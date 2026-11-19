package vm

import (
	"bytes"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/spark"
)

func compileAndRun(t *testing.T, src string) (Value, string, *CompiledProgram) {
	t.Helper()
	prog, err := parser.Parse("vm_test.anm", src)
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
	cp, err := Compile(info, src, true)
	if err != nil {
		t.Fatalf("compile error: %v", err)
	}
	// Test .anbc Encode/Decode roundtrip!
	bin, err := cp.Module.Encode()
	if err != nil {
		t.Fatalf("anbc encode error: %v", err)
	}
	dec, err := Decode(bin)
	if err != nil {
		t.Fatalf("anbc decode error: %v", err)
	}
	if !dec.Verified || dec.VerifyDigest != cp.Module.VerifyDigest {
		t.Fatalf("anbc digest mismatch")
	}
	cp.Module = dec

	var out bytes.Buffer
	vm := NewVM(cp, RunOptions{Stdout: &out, Seed: 7})
	val, err := vm.Run()
	if err != nil {
		t.Fatalf("vm runtime error: %v\nstdout: %s", err, out.String())
	}
	return val, out.String(), cp
}

func TestVMBytecodePipelineWorkflowAndDisasm(t *testing.T) {
	src := `
type Money = int[0..1_000_000]
type Score = int[0..100]
type FetchState = Fresh(score: Score) | Degraded

entity Account:
    balance: Money
    escrow: Money
    invariant: balance + frozen_zero == 0 or balance + escrow <= 1_000_000

entity AccountSafe:
    balance: Money
    escrow: Money
    invariant: balance + escrow <= 1_000_000

entity Quote:
    score: Score
    weight: int[1..10]
    invariant: score * weight <= 1000

monitor VaultMutex:
    writers: control int[0..1] = 0
    state Unlocked:
        invariant: writers == 0
        on acquire -> Locked:
            writers = 1
    state Locked:
        invariant: writers == 1
        on release -> Unlocked:
            writers = 0

def lock_funds(mut acc: AccountSafe, amt: int[1..10_000]) -> bool:
    requires: acc.balance + acc.escrow <= 990_000
    ensures: acc.balance + acc.escrow == old(acc.balance) + old(acc.escrow)
    if acc.balance >= amt:
        acc.balance -= amt
        acc.escrow += amt
        return True
    return False

workflow ProcessOrder(mut acc: AccountSafe, amt: int[1..10_000]) -> int:
    pool arm: int[0..2] = 2
    start -> reserve:
        ok = False
        if acc.balance + acc.escrow <= 990_000:
            ok = lock_funds(mut acc, amt)
    choice after reserve:
        when ok -> work
        when not ok -> reject
    fork work:
        branch b1:
            sync VaultMutex.acquire
            sync VaultMutex.release
        branch b2:
            acquire arm
            step pack
            release arm
    join done_work
    step finish after done_work -> done:
        return 1
    step reject -> done:
        return 0

def main() -> int:
    acc = AccountSafe(balance=500, escrow=0)
    r = run_workflow ProcessOrder(mut acc, 200)
    qs = [Quote(score=80, weight=5), Quote(score=100, weight=5), Quote(score=5, weight=2)]
    valid = qs |> filter(q => q.score >= 10)
    tot = valid |> map(q => q.score) |> fold(0, (a, b) => a + b)
    avg = 0
    if len(valid) > 0:
        avg = tot / len(valid)
    print(f"r={r} bal={acc.balance} esc={acc.escrow} avg={avg}")
    return acc.balance + acc.escrow
`
	// Remove unused buggy Account entity first in test string
	src = strings.Replace(src, `entity Account:
    balance: Money
    escrow: Money
    invariant: balance + frozen_zero == 0 or balance + escrow <= 1_000_000

`, "", 1)

	val, stdout, cp := compileAndRun(t, src)
	if val.Int != 500 {
		t.Fatalf("expected conserved total 500, got %v", val)
	}
	if !strings.Contains(stdout, "r=1 bal=300 esc=200 avg=90") {
		t.Fatalf("unexpected stdout: %q", stdout)
	}
	dis := cp.Module.Disassemble()
	if !strings.Contains(dis, "MAKE_ENTITY") || !strings.Contains(dis, "RUN_WORKFLOW") {
		t.Fatalf("unexpected disassembly:\n%s", dis)
	}
}

func TestVMStdlibSocketHTTPJSONCryptoConcurrent(t *testing.T) {
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/bad" {
			_, _ = w.Write([]byte(`{"provider":"evil","score":80,"weight":20}`)) // 80*20=1600 > 1000 invariant!
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

def main() -> int:
    # 1. HTTP Session async + gather + JSON boundary schema & invariant rejection
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

    # 2. ThreadPool & Channel concurrency
    ch = conc.Channel[int[0..100]](cap=4)
    pool = conc.ThreadPool(2, 8)
    fut = pool.submit(() => ch.send(7))
    _ = fut.await()
    ch_val = match ch.recv():
        Some(v) -> v
        None -> 0
    ch.close()
    pool.shutdown()

    # 3. ByteView + Crypto HMAC
    bv = bytes.from_hex("0102002a")
    magic = bv.read_u16_be(2)
    sig = crypto.hmac_sha256("k", "msg")
    ok_sig = crypto.constant_time_eq(sig, crypto.hmac_sha256("k", "msg"))
    if ok_sig:
        print(f"good={good_count} ch={ch_val} magic={magic}")
    return good_count + ch_val + magic
`, srv.URL, srv.URL)

	val, stdout, _ := compileAndRun(t, src)
	// good_count=90 (bad rejected by score*weight <= 1000!), ch_val=7, magic=42 => 139!
	if val.Int != 139 {
		t.Fatalf("expected 139 (90+7+42), got %d; stdout=%s", val.Int, stdout)
	}
	if !strings.Contains(stdout, "good=90 ch=7 magic=42") {
		t.Fatalf("unexpected stdout: %q", stdout)
	}
}

// A map and an entity are written in the order of their keys, not in the
// order Go walks a map, which changes from one run to the next.
func TestValueStringIsDeterministic(t *testing.T) {
	m := VMap(map[string]Value{"b\"q": VInt(1), "a\nb": VInt(2), "Z": VInt(3), "k": VStr("v")})
	want := `{"Z": 3, "a\nb": 2, "b\"q": 1, "k": v}`
	for i := 0; i < 50; i++ {
		if got := m.String(); got != want {
			t.Fatalf("map printed as %s, want %s", got, want)
		}
	}
	e := Value{Kind: ValEntity, Entity: &EntityInstance{TypeName: "Box", Fields: map[string]Value{"tag": VStr("t"), "n": VInt(1), "a": VBool(true)}}}
	for i := 0; i < 50; i++ {
		if got := e.String(); got != "Box(a=True, n=1, tag=t)" {
			t.Fatalf("entity printed as %s", got)
		}
	}
}
