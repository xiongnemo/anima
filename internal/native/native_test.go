package native

import (
	"context"
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

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

// abs of the least int is no int64. The VM gives the least int back; the
// native program called llabs, whose result there C leaves undefined, and
// gcc took it for not negative: abs(x) < 0 was true on the VM and false in
// the native program, in a program the kernel had proved all of. The kernel
// now refuses it (TestAbsMinMaxRefused), and a program it was not asked
// about prints the same on both.
func TestNativeAbsOfTheLeastIntIsTheVMs(t *testing.T) {
	src := `def neg(x: int) -> int:
    if abs(x) < 0:
        return 1
    return 0

def main() -> int:
    xs = [0 - 9223372036854775807 - 1, 0 - 9223372036854775807, 9223372036854775807]
    print(neg(xs[0]), abs(xs[0]), neg(xs[1]), abs(xs[1]), neg(xs[2]), abs(xs[2]))
    print(min(xs[0], xs[2]), max(xs[0], xs[2]), min(xs[2], xs[0]), max(xs[2], xs[0]))
    return 0
`
	const want = "1 -9223372036854775808 0 9223372036854775807 0 9223372036854775807\n" +
		"-9223372036854775808 9223372036854775807 -9223372036854775808 9223372036854775807\n"
	prog, err := parser.Parse("abs.anm", src)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema: %v", err)
	}
	if rep := spark.Verify(info); rep.OK() {
		t.Fatal("the kernel proved a program that takes abs of the least int")
	}
	cp, err := vm.Compile(info, src, false)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	var vmOut strings.Builder
	if _, err := vm.NewVM(cp, vm.RunOptions{Stdout: &vmOut}).Run(); err != nil || vmOut.String() != want {
		t.Fatalf("VM printed %q (%v), want %q", vmOut.String(), err, want)
	}
	bin := filepath.Join(t.TempDir(), "abs")
	if err := BuildNative(info, bin, ""); err != nil {
		t.Fatalf("build: %v", err)
	}
	if out, err := exec.Command(bin).CombinedOutput(); err != nil || string(out) != want {
		t.Errorf("native printed %q (%v), want %q", out, err, want)
	}
}

// What the kernel proves of abs, min and max is what both backends compute.
func TestAbsMinMaxParity(t *testing.T) {
	src := `def clamp(x: int) -> int[0..255]:
    return min(max(x, 0), 255)

def gap(a: int[-1000..1000], b: int[-1000..1000]) -> int[0..2000]:
    return abs(a - b)

def far(x: int) -> int:
    requires: x != -9223372036854775807 - 1
    ensures: result >= 0
    return abs(x)

def main() -> int:
    xs = [0 - 9223372036854775807, 0 - 300, 0 - 1, 0, 1, 255, 256, 9223372036854775807]
    for x in xs:
        if x != -9223372036854775807 - 1:
            print(clamp(x), far(x), min(x, 0 - 1), max(x, 7), abs(min(x, 5)))
    print(gap(0 - 1000, 1000), gap(3, 3), gap(7, 0 - 2), abs(0 - 5), min(2, 3), max(2, 3))
    return 0
`
	const want = "0 9223372036854775807 -9223372036854775807 7 9223372036854775807\n" +
		"0 300 -300 7 300\n" +
		"0 1 -1 7 1\n" +
		"0 0 -1 7 0\n" +
		"1 1 -1 7 1\n" +
		"255 255 -1 255 5\n" +
		"255 256 -1 256 5\n" +
		"255 9223372036854775807 -1 9223372036854775807 5\n" +
		"2000 0 9 5 2 3\n"
	onVM, onNative := run(t, "absminmax", src)
	if onVM != want || onNative != want {
		t.Errorf("VM printed %q, native %q, want %q", onVM, onNative, want)
	}
}

// A count the machine does not have is held to one it has by both runtimes,
// the same one: no thread for each of 1 << 40 workers, no queue of 1 << 40
// places, a semaphore of no permit has one. No verified program gets there
// (TestSPARKStdResourceRanges); this builds one the kernel was not asked
// about.
func TestNativeStdArgumentsOutOfRange(t *testing.T) {
	src := `import std.concurrent as conc
import std.requests as req
import std.socket as sock
import std.time as time

def main() -> int:
    big = conc.ThreadPool(1 << 40, 1 << 40)
    f = big.submit(() => 1)
    print(f.await())
    big.shutdown()
    none = conc.ThreadPool(0 - 3, 0)
    g = none.submit(() => 2)
    print(g.await())
    none.shutdown()
    ch = conc.Channel(1 << 40)
    ch.send(3)
    print(ch.recv())
    ch.close()
    c0 = conc.Channel(0 - 1)
    c0.send(4)
    print(c0.recv())
    c0.close()
    s = conc.Semaphore(0)
    s.acquire()
    s.release()
    print(5)
    many = conc.Semaphore(1 << 62)
    many.acquire()
    many.release()
    print(6)
    sess = req.Session(1 << 40)
    sess.close()
    zero = req.Session(0)
    zero.close()
    time.sleep_ms(0 - (1 << 62))
    print(7)
    match sock.listen_tcp("127.0.0.1", 70000):
        Ok(ln) -> ln.close()
        Err(e) -> print(e)
    match sock.connect_tcp("127.0.0.1", 0 - 1):
        Ok(c) -> c.close()
        Err(e) -> print(e)
    return 0
`
	const want = "1\n2\nSome(3)\nSome(4)\n5\n6\n7\n" +
		"listen tcp: address 70000: invalid port\ndial tcp: address -1: invalid port\n"
	prog, err := parser.Parse("counts.anm", src)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema: %v", err)
	}
	if rep := spark.Verify(info); rep.OK() {
		t.Fatal("the kernel proved a program whose counts are out of range")
	}
	cp, err := vm.Compile(info, src, false)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	var vmOut strings.Builder
	done := make(chan error, 1)
	go func() {
		_, err := vm.NewVM(cp, vm.RunOptions{Stdout: &vmOut}).Run()
		done <- err
	}()
	select {
	case err := <-done:
		if err != nil || vmOut.String() != want {
			t.Errorf("VM printed %q (%v), want %q", vmOut.String(), err, want)
		}
	case <-time.After(30 * time.Second):
		t.Fatal("the VM does not end")
	}
	bin := filepath.Join(t.TempDir(), "counts")
	if err := BuildNative(info, bin, ""); err != nil {
		t.Fatalf("build: %v", err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	out, err := exec.CommandContext(ctx, bin).CombinedOutput()
	if err != nil || string(out) != want {
		t.Errorf("native printed %q (%v), want %q", out, err, want)
	}
}

// run checks src with the kernel and gives what it prints on the VM and as
// a native program built with the gcc arguments in more.
func run(t *testing.T, name, src string, more ...string) (onVM, onNative string) {
	t.Helper()
	prog, err := parser.Parse(name+".anm", src)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema: %v", err)
	}
	if rep := spark.Verify(info); !rep.OK() {
		t.Fatalf("spark: %v", rep.Errors())
	}
	cp, err := vm.Compile(info, src, false)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	var vmOut strings.Builder
	if _, err := vm.NewVM(cp, vm.RunOptions{Stdout: &vmOut}).Run(); err != nil {
		t.Fatalf("VM: %v", err)
	}
	dir := t.TempDir()
	bin, cFile := filepath.Join(dir, name), filepath.Join(dir, name+".c")
	if err := BuildNative(info, bin, cFile); err != nil {
		t.Fatalf("build: %v", err)
	}
	if len(more) > 0 {
		args := append([]string{"-std=c11", "-O2", "-w", cFile}, more...)
		args = append(args, "-lpthread", "-lssl", "-lcrypto", "-o", bin)
		if out, err := exec.Command("gcc", args...).CombinedOutput(); err != nil {
			t.Fatalf("gcc: %v\n%s", err, out)
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	out, err := exec.CommandContext(ctx, bin).CombinedOutput()
	if err != nil {
		t.Fatalf("native: %v\n%s", err, out)
	}
	return vmOut.String(), string(out)
}

// parallel_map of a list longer than there are threads to have gives f of
// every element in the order of the list, on both backends, with more than
// one call and at most sema.MaxWorkers of them going on at a time. On a
// thread for each element the native program of 131072 elements stopped
// with "cannot start a thread" where the VM went on.
func TestParallelMapOfALongListRunsAtMostMaxWorkersAtATime(t *testing.T) {
	src := fmt.Sprintf(`import std.concurrent as conc
import std.json as json
import std.time as time

entity L:
    xs: list[int[0..9]]

def up(v: int) -> int:
    if v < 100000:
        return v + 1
    return v

def down(v: int) -> int:
    if v > 0:
        return v - 1
    return v

def larger(a: int, b: int) -> int:
    if a > b:
        return a
    return b

def visit(cur: conc.Mutex[int], most: conc.Mutex[int], x: int[0..9]) -> int:
    cur.with_lock((v) => up(v))
    n = cur.get()
    most.with_lock((m) => larger(m, n))
    time.sleep_ms(50)
    cur.with_lock((v) => down(v))
    return x * 2

def head(ys: list[int]) -> str:
    if len(ys) > 3:
        return f"{ys[0]} {ys[1]} {ys[2]} {ys[3]}"
    return "short"

def main() -> int:
    s = "1,2,3"
    i = 0
    while i < 9:
        invariant: i >= 0
        decreases: 9 - i
        s = s + "," + s
        i = i + 1
    cur = conc.Mutex(0)
    most = conc.Mutex(0)
    match json.decode[L]("{\"xs\":[" + s + "]}"):
        Ok(l) ->
            ys = conc.parallel_map(l.xs, (x) => visit(cur, most, x))
            print(len(ys), head(ys), most.get() > 1, most.get() <= %d, cur.get())
            zs = conc.parallel_map(l.xs, (x) => x + 1)
            print(len(zs), head(zs))
        Err(e) -> print(e)
    return 0
`, sema.MaxWorkers)
	const want = "1536 2 4 6 2 True True 0\n1536 2 3 4 2\n"
	onVM, onNative := run(t, "parmap", src)
	if onVM != want || onNative != want {
		t.Errorf("VM printed %q, native %q, want %q", onVM, onNative, want)
	}
}

// A request begun with get_async when the system has no thread for it is
// made where it is begun, and its future has the answer. The native runtime
// did not look at what pthread_create said: the future was never done, and
// awaiting it joined a thread that was not there.
func TestNativeGetAsyncWithNoThreadToSpare(t *testing.T) {
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprint(w, "ok")
	}))
	defer srv.Close()
	src := fmt.Sprintf(`import std.requests as req

def fan(n: int[0..40]) -> int:
    decreases: n
    if n == 0:
        return 0
    sess = req.Session()
    f = sess.get_async("%s/", timeout_ms=5000)
    rest = fan(n - 1)
    r = f.await()
    sess.close()
    match r:
        Ok(x) ->
            if x.status == 200 and rest < 1000:
                return rest + 1
            return rest
        Err(e) ->
            print(e)
            return rest

def main() -> int:
    print(fan(40))
    return 0
`, srv.URL)
	wrap := filepath.Join(t.TempDir(), "wrap.c")
	// The eighth thread asked for, and every one after it, is refused.
	if err := os.WriteFile(wrap, []byte(`#include <errno.h>
#include <pthread.h>
int __real_pthread_create(pthread_t *, const pthread_attr_t *, void *(*)(void *), void *);
static int asked;
int __wrap_pthread_create(pthread_t *t, const pthread_attr_t *a, void *(*f)(void *), void *arg) {
    if (__sync_add_and_fetch(&asked, 1) > 7) return EAGAIN;
    return __real_pthread_create(t, a, f, arg);
}
`), 0o644); err != nil {
		t.Fatal(err)
	}
	onVM, onNative := run(t, "noth", src, wrap, "-Wl,--wrap=pthread_create")
	if onVM != "40\n" || onNative != "40\n" {
		t.Errorf("VM printed %q, native %q, want %q", onVM, onNative, "40\n")
	}
}
