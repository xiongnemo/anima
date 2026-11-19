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

    good_count: int = 0
    for r in resps:
        match r:
            Ok(resp) ->
                match json.decode[Quote](resp.body):
                    Ok(q) -> good_count += q.score
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
