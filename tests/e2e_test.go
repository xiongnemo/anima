package tests

import (
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func buildCLI(t *testing.T, tmpDir string) string {
	t.Helper()
	bin := filepath.Join(tmpDir, "anima")
	cmd := exec.Command("go", "build", "-o", bin, "../cmd/anima")
	cmd.Env = append(os.Environ(), "CGO_ENABLED=0")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("failed to build anima CLI: %v\n%s", err, string(out))
	}
	return bin
}

func TestE2EAllExamplesDualBackendParityAndExports(t *testing.T) {
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)

	examples, err := filepath.Glob("../examples/*.anm")
	if err != nil || len(examples) != 6 {
		t.Fatalf("expected 6 flagship examples, got %v (err=%v)", examples, err)
	}

	for _, ex := range examples {
		name := strings.TrimSuffix(filepath.Base(ex), ".anm")
		t.Run(name, func(t *testing.T) {
			// 1. anima check --explain
			chkOut, err := exec.Command(animaBin, "check", "--explain", ex).CombinedOutput()
			if err != nil {
				t.Fatalf("anima check failed on %s: %v\n%s", ex, err, string(chkOut))
			}
			if !strings.Contains(string(chkOut), "ALL 3 FORMAL VERIFICATION KERNELS PASSED") {
				t.Fatalf("missing pass banner on %s:\n%s", ex, string(chkOut))
			}

			// 2. anima run (Bytecode VM)
			vmOut, err := exec.Command(animaBin, "run", ex).CombinedOutput()
			if err != nil {
				t.Fatalf("anima run failed on %s: %v\n%s", ex, err, string(vmOut))
			}

			// 3. anima build -> native ELF execution
			nativeBin := filepath.Join(tmp, name+"_native")
			bldOut, err := exec.Command(animaBin, "build", "-o", nativeBin, ex).CombinedOutput()
			if err != nil {
				t.Fatalf("anima build failed on %s: %v\n%s", ex, err, string(bldOut))
			}
			natOut, err := exec.Command(nativeBin).CombinedOutput()
			if err != nil {
				t.Fatalf("native binary failed on %s: %v\n%s", ex, err, string(natOut))
			}

			// 4. Verify dual-backend stdout parity
			if strings.TrimSpace(string(vmOut)) != strings.TrimSpace(string(natOut)) {
				t.Fatalf("VM vs Native output mismatch on %s:\nVM:     %q\nNative: %q", name, string(vmOut), string(natOut))
			}

			// 5. Verify disasm, uml, export
			if dOut, err := exec.Command(animaBin, "disasm", ex).CombinedOutput(); err != nil || !strings.Contains(string(dOut), "func ") {
				t.Fatalf("disasm failed on %s: %v\n%s", ex, err, string(dOut))
			}
			if uOut, err := exec.Command(animaBin, "uml", "--format", "mermaid", ex).CombinedOutput(); err != nil || !strings.Contains(string(uOut), "classDiagram") {
				t.Fatalf("uml mermaid failed on %s: %v", ex, err)
			}
		})
	}

	// Verify export --fsp and --pnml on escrow_service.anm
	fspPath := filepath.Join(tmp, "escrow.fsp")
	pnmlPath := filepath.Join(tmp, "escrow.pnml")
	if out, err := exec.Command(animaBin, "export", "--fsp", fspPath, "--pnml", pnmlPath, "../examples/escrow_service.anm").CombinedOutput(); err != nil {
		t.Fatalf("export failed: %v\n%s", err, string(out))
	}
	fspRaw, _ := os.ReadFile(fspPath)
	pnmlRaw, _ := os.ReadFile(pnmlPath)
	if !strings.Contains(string(fspRaw), "VAULTMUTEX") || !strings.Contains(string(pnmlRaw), "<pnml") {
		t.Fatalf("invalid exported FSP/PNML")
	}
}

func TestE2ENegativeBugSuiteAndDeterministicReplay(t *testing.T) {
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)

	cases := []struct {
		file    string
		wantSub string
	}{
		{"../tests/bugs/spark_overflow.anm", "SPARK FAILED"},
		{"../tests/bugs/spark_int64_overflow.anm", "int64_overflow"},
		{"../tests/bugs/spark_divzero.anm", "div_nonzero"},
		{"../tests/bugs/spark_mut_call_stale_fact.anm", "div_nonzero"},
		{"../tests/bugs/spark_match_assignment_lost.anm", "div_nonzero"},
		{"../tests/bugs/spark_reassigned_entity.anm", "div_nonzero"},
		{"../tests/bugs/spark_entity_invariant_at_call.anm", "entity_a_invariant"},
		{"../tests/bugs/spark_alias_stale_fact.anm", "div_nonzero"},
		{"../tests/bugs/spark_readonly_param_alias.anm", "readonly_c"},
		{"../tests/bugs/spark_mut_argument_alias.anm", "call_g_mut_alias"},
		{"../tests/bugs/spark_list_literal_range.anm", "div_nonzero"},
		{"../tests/bugs/sema_list_element_range.anm", "expects list[int[1..9]], got list[int]"},
		{"../tests/bugs/spark_element_write_stale.anm", "div_nonzero"},
		{"../tests/bugs/spark_element_write_range.anm", "elem_assign_bounds"},
		{"../tests/bugs/spark_match_arm_range.anm", "div_nonzero"},
		{"../tests/bugs/spark_map_value_range.anm", "elem_assign_bounds"},
		{"../tests/bugs/sema_variable_keeps_element_type.anm", "keeps the type of its elements"},
		{"../tests/bugs/spark_variant_field_range.anm", "variant_Circle_range"},
		{"../tests/bugs/spark_map_stage_range.anm", "div_nonzero"},
		{"../tests/bugs/sema_with_field_type.anm", "expects list[int[1..9]], got list[int]"},
		{"../tests/bugs/spark_fold_not_a_sum.anm", "div_nonzero"},
		{"../tests/bugs/spark_timeout_unbounded.anm", "timeout_bounds"},
		{"../tests/bugs/sema_closure_argument_element_range.anm", "expects list[int[1..9]], got unknown"},
		{"../tests/bugs/sema_variant_fields_out_of_order.anm", "the fields of a variant are given in order"},
		{"../tests/bugs/spark_keyword_literal_range.anm", "list_elem_bounds"},
		{"../tests/bugs/sema_piped_list_element_range.anm", "expects list[int[1..9]], got list[int]"},
		{"../tests/bugs/spark_entity_kept_by_call.anm", "entity_b_invariant"},
		{"../tests/bugs/spark_requires_in_condition.anm", "call_half_requires_1"},
		{"../tests/bugs/spark_mut_call_not_alone.anm", "mut_call_alone"},
		{"../tests/bugs/spark_aliasing.anm", "anti-aliasing"},
		{"../tests/bugs/sema_fork_element_write_race.anm", "concurrent write race"},
		{"../tests/bugs/spark_match_incomplete.anm", "match_exhaustive"},
		{"../tests/bugs/spark_match_nested_literal.anm", "match_exhaustive_adt"},
		{"../tests/bugs/spark_match_str_no_default.anm", "match_exhaustive_default"},
		{"../tests/bugs/spark_choice_nonexclusive.anm", "choice_exclusive"},
		{"../tests/bugs/lts_safety_violation.anm", "ERROR=-1"},
		{"../tests/bugs/dining_philosophers_deadlock.anm", "DEADLOCK"},
		{"../tests/bugs/lts_livelock_progress.anm", "PROGRESS"},
		{"../tests/bugs/socket_leak.anm", "resource handle leak"},
		{"../tests/bugs/socket_use_after_close.anm", "use-after-close"},
		{"../tests/bugs/own_param_never_closed.anm", "resource handle leak"},
		{"../tests/bugs/own_use_after_move.anm", "after it was moved"},
		{"../tests/bugs/own_alias_use_after_close.anm", "after it was moved"},
		{"../tests/bugs/own_try_while_open.anm", "`?` may return early"},
		{"../tests/bugs/own_branch_mismatch.anm", "every path must leave it in the same state"},
		{"../tests/bugs/own_borrowed_closed.anm", "is borrowed"},
		{"../tests/bugs/own_stream_shared_with_task.anm", "cannot be shared with a task"},
		{"../tests/bugs/own_listener_closed_while_lent.anm", "while a task may still be using"},
		{"../tests/bugs/own_stored_in_entity.anm", "cannot hold"},
		{"../tests/bugs/petri_fork_merge_improper.anm", "IMPROPER COMPLETION"},
		{"../tests/bugs/petri_choice_join_deadlock.anm", "OPTION TO COMPLETE"},
		{"../tests/bugs/petri_pool_leak.anm", "IMPROPER COMPLETION"},
		{"../tests/bugs/requests_missing_timeout.anm", "timeout_ms"},
	}

	for _, tc := range cases {
		t.Run(filepath.Base(tc.file), func(t *testing.T) {
			out, err := exec.Command(animaBin, "check", tc.file).CombinedOutput()
			if err == nil {
				t.Fatalf("expected formal verification failure for %s, but check passed!\n%s", tc.file, string(out))
			}
			if !strings.Contains(string(out), tc.wantSub) {
				t.Fatalf("expected diagnostic containing %q for %s, got:\n%s", tc.wantSub, tc.file, string(out))
			}

			// Verify `anima run` refuses to run unverified program
			if _, rerr := exec.Command(animaBin, "run", tc.file).CombinedOutput(); rerr == nil {
				t.Fatalf("expected anima run to refuse unverified program %s", tc.file)
			}
		})
	}

	// Deterministic Counterexample Replay test on Dining Philosophers
	cexPath := filepath.Join(tmp, "deadlock_cex.json")
	_, _ = exec.Command(animaBin, "check", "--save-cex", cexPath, "../tests/bugs/dining_philosophers_deadlock.anm").CombinedOutput()
	repOut, err := exec.Command(animaBin, "run", "--replay", cexPath, "../tests/bugs/dining_philosophers_deadlock.anm").CombinedOutput()
	if err != nil {
		t.Fatalf("anima run --replay failed: %v\n%s", err, string(repOut))
	}
	if !strings.Contains(string(repOut), "[REPRODUCED] DEADLOCK") {
		t.Fatalf("expected deadlock replay output, got:\n%s", string(repOut))
	}
}

func TestE2ERealLoopbackHTTPParityVMVsNative(t *testing.T) {
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/bad" {
			_, _ = w.Write([]byte(`{"provider":"bad","score":90,"weight":15}`)) // invariant violated
			return
		}
		_, _ = w.Write([]byte(`{"provider":"ok","score":85,"weight":10}`))
	}))
	defer srv.Close()

	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	srcPath := filepath.Join(tmp, "http_parity.anm")
	src := fmt.Sprintf(`
import std.requests as req
import std.json as json

entity Quote:
    provider: str
    score: int[0..100]
    weight: int[1..10]
    invariant: score * weight <= 1000

def main() -> int:
    sess = req.Session(4)
    f1 = sess.get_async("%s/ok", timeout_ms=2000)
    f2 = sess.get_async("%s/bad", timeout_ms=2000)
    resps = req.gather([f1, f2])
    sess.close()
    total: int[0..1000] = 0
    for r in resps:
        match r:
            Ok(resp) ->
                match json.decode[Quote](resp.body):
                    Ok(q) ->
                        if total <= 900:
                            total += q.score
                    Err(e) -> total += 0
            Err(e) -> total += 0
    print(f"http_total={total}")
    if total == 85:
        return 0
    return 1
`, srv.URL, srv.URL)
	if err := os.WriteFile(srcPath, []byte(src), 0644); err != nil {
		t.Fatal(err)
	}

	vmOut, err := exec.Command(animaBin, "run", srcPath).CombinedOutput()
	if err != nil {
		t.Fatalf("VM HTTP parity failed: %v\n%s", err, string(vmOut))
	}
	natBin := filepath.Join(tmp, "http_parity_elf")
	if bOut, err := exec.Command(animaBin, "build", "-o", natBin, srcPath).CombinedOutput(); err != nil {
		t.Fatalf("Native HTTP build failed: %v\n%s", err, string(bOut))
	}
	natOut, err := exec.Command(natBin).CombinedOutput()
	if err != nil {
		t.Fatalf("Native HTTP ELF execution failed: %v\n%s", err, string(natOut))
	}
	if strings.TrimSpace(string(vmOut)) != "http_total=85" || strings.TrimSpace(string(natOut)) != "http_total=85" {
		t.Fatalf("HTTP parity mismatch: vm=%q native=%q", string(vmOut), string(natOut))
	}
}

// runOnBothBackends verifies src, runs it on the VM and as a native binary,
// and requires both to print want.
func runOnBothBackends(t *testing.T, name, src, want string) {
	t.Helper()
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, name+".anm")
	if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	vmOut, err := exec.Command(animaBin, "run", path).CombinedOutput()
	if err != nil || string(vmOut) != want {
		t.Fatalf("VM: err=%v, output:\n%s\nwant:\n%s", err, vmOut, want)
	}
	nativeBin := filepath.Join(tmp, name)
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	natOut, err := exec.Command(nativeBin).CombinedOutput()
	if err != nil || string(natOut) != want {
		t.Fatalf("native: err=%v, output:\n%s\nwant:\n%s", err, natOut, want)
	}
}

// A connection moved into a worker must stay open when the function that
// moved it later returns early through `?`.
func TestE2EMovedHandleSurvivesEarlyReturn(t *testing.T) {
	runOnBothBackends(t, "moved_then_try", movedThenTrySrc, "dispatch failed: boom\nreply=late\n")
}

// The native backend must evaluate calls and field reads once and in source
// order, skip the right operand of a short-circuit operator, fall through a
// failed match guard, and lower a match expression wherever it appears.
func TestE2EEvaluationOrderParity(t *testing.T) {
	runOnBothBackends(t, "evaluation_order", evaluationOrderSrc, evaluationOrderWant)
}

const evaluationOrderSrc = `import std.concurrent as conc

def a() -> int[1..1]:
    print("a")
    return 1

def b() -> int[2..2]:
    print("b")
    return 2

def add(x: int[0..5], y: int[0..5]) -> int[0..10]:
    return x + y

def yes(tag: str) -> bool:
    print(tag)
    return True

def zero(tag: str) -> int[0..0]:
    print(tag)
    return 0

def fail(tag: str) -> Result[bool, str]:
    print(tag)
    return Err(tag)

def guarded(skip: bool) -> Result[bool, str]:
    ok = skip or fail("or-rhs-try")?
    return Ok(ok)

def pick(n: int[0..9]) -> int[0..9]:
    match n:
        k if k > 5 -> return 1
        _ -> return 0
    return 9

def pick_expr(n: int[0..9]) -> int[0..9]:
    r = match n:
        k if k > 5 -> 1
        _ -> 0
    return r

def ladder(n: int[0..9]) -> str:
    if n > 5 and yes("first"):
        return "big"
    elif n > 2 and yes("second"):
        return "mid"
    elif yes("third"):
        return "small"
    return "none"

entity Box:
    v: int[0..10]

def reset(mut box: Box) -> int[1..1]:
    ensures: box.v == 0
    box.v = 0
    print("reset")
    return 1

def capacity(mut box: Box) -> int[1..4]:
    box.v = 2
    print("capacity")
    return 4

def main() -> int:
    s = add(a(), b())
    d = a() - b()
    m = min(a(), b())
    t = False and yes("and-rhs")
    u = True or yes("or-rhs")
    v = False implies yes("implies-rhs")
    print(f"s={s} d={d} m={m} t={t} u={u} v={v}")
    print(f"pick={pick(3)}{pick(7)} pick_expr={pick_expr(3)}{pick_expr(7)}")
    print(f"ladder={ladder(7)},{ladder(4)},{ladder(1)}")
    match guarded(True):
        Ok(x) -> print(f"guarded skip ok={x}")
        Err(e) -> print(f"guarded skip err={e}")
    match guarded(False):
        Ok(x) -> print(f"guarded ok={x}")
        Err(e) -> print(f"guarded err={e}")
    box = Box(v=0)
    box.v = match s:
        3 -> 7
        _ -> 8
    xs = [0, 0]
    xs[1] = match d:
        0 -> 3
        _ -> 4
    print(f"box={box.v} xs1={xs[1]}")
    one = reset(mut box)
    box.v += one
    print(f"compound={box.v}")
    box.v = 5
    total = 5 + reset(mut box)
    print(f"total={total} after={box.v}")
    ch = conc.Channel[int[0..9]](cap=capacity(mut box))
    ch.close()
    print(f"cap box={box.v}")
    ys: list[int[0..100]] = [5, 6]
    ys[0] += zero("index-rhs")
    print(f"ys0={ys[0]}")
    return 0
`

const evaluationOrderWant = `a
b
a
b
a
b
s=3 d=-1 m=1 t=False u=True v=True
pick=01 pick_expr=01
first
second
third
ladder=big,mid,small
guarded skip ok=True
or-rhs-try
guarded err=or-rhs-try
box=7 xs1=4
reset
compound=1
reset
total=6 after=0
capacity
cap box=2
index-rhs
ys0=5
`

// Element reads and writes behave the same for lists and maps on both backends.
func TestE2EElementAccessParity(t *testing.T) {
	runOnBothBackends(t, "element_access", elementAccessSrc, "a=1 b=7 xs=3,9\n")
}

const elementAccessSrc = `def zero() -> int[0..0]:
    return 0

def main() -> int:
    m: map[str, int[0..9]] = {"a": 1, "b": 2}
    m["a"] += zero()
    m["b"] = 7
    xs: list[int[0..9]] = [3, 4]
    xs[1] = 9
    a = m["a"]
    b = m["b"]
    print(f"a={a} b={b} xs={xs[0]},{xs[1]}")
    return 0
`

// A literal or range nested in a variant pattern must be compared, on both
// backends, instead of matching every value of the variant.
func TestE2ENestedPatternParity(t *testing.T) {
	runOnBothBackends(t, "nested_patterns", nestedPatternSrc,
		"zero small other 5 too big\nempty circle circle 2 flat rect 2x3 dot\nfive some 6 none\n")
}

const nestedPatternSrc = `type Shape = Circle(r: int[0..9]) | Rect(w: int[0..9], h: int[0..9]) | Dot

def get(n: int[0..9]) -> Result[int, str]:
    if n > 7:
        return Err("big")
    return Ok(n)

def classify(n: int[0..9]) -> str:
    match get(n):
        Ok(0) -> return "zero"
        Ok(1..3) -> return "small"
        Ok(k) -> return f"other {k}"
        Err("big") -> return "too big"
        Err(e) -> return e
    return "?"

def area(s: Shape) -> str:
    return match s:
        Circle(0) -> "empty circle"
        Circle(r) -> f"circle {r}"
        Rect(w, 0) -> "flat"
        Rect(w, h) -> f"rect {w}x{h}"
        Dot -> "dot"

def opt(o: Option[int]) -> str:
    match o:
        Some(5) -> return "five"
        Some(x) -> return f"some {x}"
        None -> return "none"
    return "?"

def main() -> int:
    print(f"{classify(0)} {classify(2)} {classify(5)} {classify(9)}")
    print(f"{area(Circle(r=0))} {area(Circle(r=2))} {area(Rect(w=2, h=0))} {area(Rect(w=2, h=3))} {area(Dot)}")
    print(f"{opt(Some(5))} {opt(Some(6))} {opt(None)}")
    return 0
`

// Reading from a connection the peer has closed is an error on both backends.
func TestE2ERecvAtEOFParity(t *testing.T) {
	runOnBothBackends(t, "recv_eof", recvEOFSrc, "bye / error: EOF\n")
}

const recvEOFSrc = `import std.socket as sock

def read_all(conn: sock.TcpStream) -> str:
    first = match conn.recv_text(16):
        Ok(text) -> text
        Err(e) -> "error: " + e
    second = match conn.recv_text(16):
        Ok(text) -> "data: " + text
        Err(e) -> "error: " + e
    return first + " / " + second

def main() -> int:
    match sock.listen_tcp("127.0.0.1", 0):
        Ok(ln) ->
            match sock.connect_tcp("127.0.0.1", ln.port()):
                Ok(client) ->
                    match ln.accept(timeout_ms=3000):
                        Ok(server) ->
                            sent = server.send_text("bye")
                            server.close()
                            print(read_all(client))
                        Err(e) -> print(f"accept failed: {e}")
                    client.close()
                Err(e) -> print(f"connect failed: {e}")
            ln.close()
            return 0
        Err(e) -> print(f"listen failed: {e}")
    return 1
`

const movedThenTrySrc = `import std.socket as sock
import std.concurrent as conc
import std.time as time

def late_reply(own conn: sock.TcpStream) -> bool:
    time.sleep_ms(300)
    sent = conn.send_text("late")
    conn.close()
    match sent:
        Ok(n) -> return True
        Err(e) -> return False
    return False

def fail() -> Result[int, str]:
    return Err("boom")

def dispatch(ln: sock.TcpListener, pool: conc.ThreadPool) -> Result[int, str]:
    conn = ln.accept(timeout_ms=3000)?
    fut = pool.submit(() => late_reply(own conn))
    n = fail()?
    _ = fut.await()
    return Ok(n)

def read_reply(conn: sock.TcpStream) -> str:
    match conn.recv_text(16):
        Ok(text) -> return text
        Err(e) -> return "error: " + e
    return ""

def main() -> int:
    match sock.listen_tcp("127.0.0.1", 0):
        Ok(ln) ->
            pool = conc.ThreadPool(1, 2)
            match sock.connect_tcp("127.0.0.1", ln.port()):
                Ok(client) ->
                    match dispatch(ln, pool):
                        Ok(n) -> print("dispatch ok")
                        Err(e) -> print(f"dispatch failed: {e}")
                    reply = read_reply(client)
                    client.close()
                    print(f"reply={reply}")
                Err(e) -> print(f"connect failed: {e}")
            pool.shutdown()
            ln.close()
            return 0
        Err(e) -> print(f"listen failed: {e}")
    return 1
`
