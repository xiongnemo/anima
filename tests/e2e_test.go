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
		{"../tests/bugs/spark_aliasing.anm", "anti-aliasing"},
		{"../tests/bugs/spark_match_incomplete.anm", "match_exhaustive"},
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

// A connection moved into a worker must stay open when the function that
// moved it later returns early through `?`.
func TestE2EMovedHandleSurvivesEarlyReturn(t *testing.T) {
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	src := filepath.Join(tmp, "moved_then_try.anm")
	if err := os.WriteFile(src, []byte(movedThenTrySrc), 0o644); err != nil {
		t.Fatal(err)
	}
	want := "dispatch failed: boom\nreply=late\n"

	vmOut, err := exec.Command(animaBin, "run", src).CombinedOutput()
	if err != nil || string(vmOut) != want {
		t.Fatalf("VM: err=%v, output:\n%s", err, vmOut)
	}
	nativeBin := filepath.Join(tmp, "moved_then_try")
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, src).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	natOut, err := exec.Command(nativeBin).CombinedOutput()
	if err != nil || string(natOut) != want {
		t.Fatalf("native: err=%v, output:\n%s", err, natOut)
	}
}

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
