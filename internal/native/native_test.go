package native

import (
	"fmt"
	"net/http"
	"net/http/httptest"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/spark"
	"github.com/xiongnemo/anima/internal/vm"
)

func TestNativeBuildAndParityWithHTTPJSONCryptoConcurrentWorkflow(t *testing.T) {
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/bad" {
			_, _ = w.Write([]byte(`{"provider":"evil","score":80,"weight":20}`))
			return
		}
		_, _ = w.Write([]byte(`{"provider":"ok","score":90,"weight":10}`))
	}))
	defer srv.Close()

	src := fmt.Sprintf(`
import std.socket as sock
import std.requests as req
import std.json as json
import std.concurrent as conc
import std.crypto as crypto
import std.bytes as bytes

entity Quote:
    provider: str
    score: int[0..100]
    weight: int[1..10]
    invariant: score * weight <= 1000

entity Account:
    balance: int[0..10_000]
    escrow: int[0..10_000]
    invariant: balance + escrow <= 10_000

def lock_funds(mut acc: Account, amt: int[1..1000]) -> bool:
    requires: acc.balance + acc.escrow <= 9000
    ensures: acc.balance + acc.escrow == old(acc.balance) + old(acc.escrow)
    if acc.balance >= amt:
        acc.balance -= amt
        acc.escrow += amt
        return True
    return False

workflow ProcessOrder(mut acc: Account, amt: int[1..1000]):
    pool arm: int[0..2] = 2
    start -> reserve:
        ok = False
        if acc.balance + acc.escrow <= 9000:
            ok = lock_funds(mut acc, amt)
    choice after reserve:
        when ok -> work
        when not ok -> reject
    fork work:
        branch b1:
            acquire arm
            step pack
            release arm
        branch b2:
            step log
    join done_work
    step finish after done_work -> done
    step reject -> done

def main() -> int:
    acc = Account(balance=500, escrow=0)
    run_workflow ProcessOrder(mut acc, 200)

    sess = req.Session(4)
    f1 = sess.get_async("%s/good", timeout_ms=2000)
    f2 = sess.get_async("%s/bad", timeout_ms=2000)
    resps = req.gather([f1, f2])
    sess.close()

    good_count: int[0..1000] = 0
    for r in resps:
        match r:
            Ok(resp) ->
                match json.decode[Quote](resp.body):
                    Ok(q) ->
                        if good_count <= 900:
                            good_count += q.score
                    Err(e) -> good_count += 0
            Err(e) -> good_count += 0

    ch = conc.Channel[int[0..100]](cap=4)
    pool = conc.ThreadPool(2, 8)
    fut = pool.submit(() => ch.send(7))
    _ = fut.await()
    ch_val = match ch.recv():
        Some(v) -> v
        None -> 0
    ch.close()
    pool.shutdown()

    bv = bytes.from_hex("0102002a")
    magic = bv.read_u16_be(2)
    sig = crypto.hmac_sha256("k", "msg")
    ok_sig = crypto.constant_time_eq(sig, crypto.hmac_sha256("k", "msg"))
    if ok_sig:
        print(f"native: bal={acc.balance} esc={acc.escrow} good={good_count} ch={ch_val} magic={magic}")
    return good_count + ch_val + magic - 139
`, srv.URL, srv.URL)

	prog, err := parser.Parse("native_test.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema error: %v", err)
	}
	rep := spark.Verify(info)
	if !rep.OK() {
		t.Fatalf("spark error: %v", rep.Errors())
	}

	tmpDir := t.TempDir()
	binPath := filepath.Join(tmpDir, "native_app")
	cPath := filepath.Join(tmpDir, "native_app.c")
	if err := BuildNative(info, binPath, cPath); err != nil {
		t.Fatalf("native build failed: %v", err)
	}

	out, err := exec.Command(binPath).CombinedOutput()
	if err != nil {
		t.Fatalf("native ELF execution failed: %v\noutput: %s", err, string(out))
	}
	if !strings.Contains(string(out), "native: bal=300 esc=200 good=90 ch=7 magic=42") {
		t.Fatalf("unexpected native ELF output: %s", string(out))
	}
}

// A division by zero, and a shift by a count that is not 0 to 63, stop a
// native program as they stop the VM: with the VM's message and exit code 1,
// not a signal or whatever the processor makes of the count. No verified
// program gets there; this builds one the kernel was not asked about.
func TestNativeDivisionByZeroIsARuntimeError(t *testing.T) {
	cases := []struct{ name, d, expr, want string }{
		{"div", "0", "10 / d", "runtime division by zero at line 4"},
		{"mod", "0", "10 % d", "runtime modulo by zero at line 4"},
		{"shl", "64", "1 << d", "runtime shift by 64 bits at line 4"},
		{"shr", "64", "8 >> d", "runtime shift by 64 bits at line 4"},
		{"shl_negative", "0 - 1", "1 << d", "runtime shift by -1 bits at line 4"},
		{"shr_negative", "0 - 1", "8 >> d", "runtime shift by -1 bits at line 4"},
	}
	for _, c := range cases {
		src := "def main() -> int:\n    d = " + c.d + "\n    print(1)\n    return " + c.expr + "\n"
		prog, err := parser.Parse(c.name+".anm", src)
		if err != nil {
			t.Fatalf("%s: parse: %v", c.name, err)
		}
		info, err := sema.Check(prog)
		if err != nil {
			t.Fatalf("%s: sema: %v", c.name, err)
		}
		// What the VM does with it: `anima run` prints "runtime error: "
		// and the error, and exits with 1.
		cp, err := vm.Compile(info, src, false)
		if err != nil {
			t.Fatalf("%s: compile: %v", c.name, err)
		}
		var vmOut strings.Builder
		_, vmErr := vm.NewVM(cp, vm.RunOptions{Stdout: &vmOut}).Run()
		if vmErr == nil || vmErr.Error() != c.want || vmOut.String() != "1\n" {
			t.Fatalf("%s: VM printed %q and ended with %v, want %q", c.name, vmOut.String(), vmErr, c.want)
		}

		bin := filepath.Join(t.TempDir(), c.name)
		if err := BuildNative(info, bin, ""); err != nil {
			t.Fatalf("%s: build: %v", c.name, err)
		}
		var stdout, stderr strings.Builder
		cmd := exec.Command(bin)
		cmd.Stdout, cmd.Stderr = &stdout, &stderr
		err = cmd.Run()
		ee, ok := err.(*exec.ExitError)
		if !ok || ee.ExitCode() != 1 {
			t.Errorf("%s: want exit code 1, got %v", c.name, err)
		}
		if stdout.String() != vmOut.String() || stderr.String() != "runtime error: "+vmErr.Error()+"\n" {
			t.Errorf("%s: stdout %q, stderr %q, want %q", c.name, stdout.String(), stderr.String(), c.want)
		}
	}
}

// The least int64 divided by -1 wraps on the VM (Go); natively it was a
// signal when the operands were not known to the C compiler, hence the
// list. This too is built without the kernel.
func TestNativeLeastIntDividedByMinusOneWraps(t *testing.T) {
	src := `def main() -> int:
    xs = [0 - 9223372036854775807 - 1, 0 - 1]
    least = xs[0]
    m = xs[1]
    print(least / m, least % m, 7 / m, 7 % m, (0 - 7) / 2, (0 - 7) % 2)
    return 0
`
	prog, err := parser.Parse("least.anm", src)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema: %v", err)
	}
	cp, err := vm.Compile(info, src, false)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	var vmOut strings.Builder
	if _, err := vm.NewVM(cp, vm.RunOptions{Stdout: &vmOut}).Run(); err != nil {
		t.Fatalf("VM: %v", err)
	}
	if want := "-9223372036854775808 0 -7 0 -3 -1\n"; vmOut.String() != want {
		t.Fatalf("VM printed %q, want %q", vmOut.String(), want)
	}
	bin := filepath.Join(t.TempDir(), "least")
	if err := BuildNative(info, bin, ""); err != nil {
		t.Fatalf("build: %v", err)
	}
	out, err := exec.Command(bin).CombinedOutput()
	if err != nil || string(out) != vmOut.String() {
		t.Errorf("native printed %q (%v), the VM %q", out, err, vmOut.String())
	}
}
