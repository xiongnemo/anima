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
		{"../tests/bugs/spark_list_equal_to_itself.anm", "div_nonzero"},
		{"../tests/bugs/spark_bool_equality_stale.anm", "div_nonzero"},
		{"../tests/bugs/sema_compare_unlike.anm", "they are never equal"},
		{"../tests/bugs/sema_lambda_argument_missing.anm", "this function takes 2 arguments, got 1"},
		{"../tests/bugs/sema_stage_function_arity.anm", "the function of map takes 1 parameter, got one with 2"},
		{"../tests/bugs/spark_unwrap_or_default_range.anm", "div_nonzero"},
		{"../tests/bugs/sema_and_then_gives_variant.anm", "the function of and_then gives an Option, got"},
		{"../tests/bugs/sema_unwrap_or_default_elements.anm", "takes a default that is list[int], got list[int[1..9]]"},
		{"../tests/bugs/sema_fold_result_elements.anm", "the function of fold gives list[int[1..9]] as fold starts with, got list[int]"},
		{"../tests/bugs/spark_fold_result_elements.anm", "div_nonzero"},
		{"../tests/bugs/spark_take_result_length.anm", "index_bounds"},
		{"../tests/bugs/spark_sum_then_stage.anm", "div_nonzero"},
		{"../tests/bugs/own_pool_submit_after_shutdown.anm", `invalid call pool.submit() while conc.ThreadPool is in state "Shutdown"`},
		{"../tests/bugs/own_pool_shut_down_by_borrower.anm", "is borrowed"},
		{"../tests/bugs/own_pool_shut_down_on_one_path.anm", "every path must leave it in the same state"},
		{"../tests/bugs/own_pool_left_running_in_match.anm", "resource handle leak"},
		{"../tests/bugs/sema_channel_send_out_of_range.anm", "is int[1..9], got int[0..0]"},
		{"../tests/bugs/sema_mutex_holds_its_type.anm", "div_nonzero"},
		{"../tests/bugs/sema_mutex_set_other_type.anm", "is int, got str"},
		{"../tests/bugs/sema_std_call_missing_argument.anm", "std.crypto.sha256 takes 1 argument, got 0"},
		{"../tests/bugs/spark_piped_request_timeout.anm", "timeout_bounds"},
		{"../tests/bugs/spark_byteview_piped_read.anm", "byteview_bounds"},
		{"../tests/bugs/spark_byteview_from_hex_not_hex.anm", "byteview_bounds"},
		{"../tests/bugs/spark_byteview_lambda_parameter.anm", "byteview_bounds"},
		{"../tests/bugs/spark_byteview_slice_outside.anm", "byteview_bounds"},
		{"../tests/bugs/sema_nested_piped_std_call.anm", "argument 1 of set() of a conc.Mutex is int, got str"},
		{"../tests/bugs/sema_variable_changes_sort.anm", "a variable keeps its sort"},
		{"../tests/bugs/sema_loop_variable_changes_elements.anm", "a variable keeps the type of its elements"},
		{"../tests/bugs/sema_pattern_changes_elements.anm", "a variable keeps the type of its elements"},
		{"../tests/bugs/spark_pattern_name_in_loop.anm", "div_nonzero"},
		{"../tests/bugs/spark_match_expression_writes_variable.anm", "div_nonzero"},
		{"../tests/bugs/spark_index_after_forgotten_length.anm", "index_bounds"},
		{"../tests/bugs/spark_declared_range_not_proved.anm", "let_y"},
		{"../tests/bugs/sema_loop_variable_changes_range.anm", "a variable keeps its range"},
		{"../tests/bugs/sema_pattern_changes_range.anm", "a variable keeps its range"},
		{"../tests/bugs/spark_reassigned_loop_variable_range.anm", "let_x"},
		{"../tests/bugs/spark_index_through_field.anm", "index_bounds"},
		{"../tests/bugs/spark_string_index.anm", "index_bounds"},
		{"../tests/bugs/spark_map_missing_key.anm", "key_present"},
		{"../tests/bugs/spark_mut_call_through_alias.anm", "mut_call_alone"},
		{"../tests/bugs/spark_element_write_out_of_range.anm", "index_bounds"},
		{"../tests/bugs/spark_index_of_unnamed_list.anm", "give it a name first"},
		{"../tests/bugs/spark_stale_field_length.anm", "index_bounds"},
		{"../tests/bugs/sema_function_as_value.anm", "function double is not a value"},
		{"../tests/bugs/sema_unknown_method.anm", `has no member "upper"`},
		{"../tests/bugs/sema_call_non_function.anm", "cannot be called"},
		{"../tests/bugs/sema_variant_too_few_fields.anm", "Circle has 2 field(s), got 1"},
		{"../tests/bugs/sema_pattern_wrong_type.anm", "a bool pattern cannot match a value of type str"},
		{"../tests/bugs/spark_match_incomplete.anm", "match_exhaustive"},
		{"../tests/bugs/spark_match_nested_literal.anm", "match_exhaustive_adt"},
		{"../tests/bugs/spark_match_nested_variant_missing.anm", "no arm for Some(Some(_))"},
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

// Every standard function and handle method that sema accepts does the
// same on both backends. The native backend had no File.read_text,
// File.write_text, fs.write_atomic, conc.parallel_map, Mutex.with_lock or
// ByteView.slice: each gave `()`, and a match on that ran no arm.
func TestE2ENativeStandardLibraryParity(t *testing.T) {
	dir := t.TempDir()
	files := strings.ReplaceAll(`import std.fs as fs

def main() -> int:
    match fs.open("DIR/a.txt", "w"):
        Ok(f) ->
            match f.write_text("hello"):
                Ok(n) -> print(n)
                Err(e) -> print(e)
            match f.read_text():
                Ok(s) -> print("rest", s)
                Err(e) -> print(e)
            f.close()
        Err(e) -> print(e)
    match fs.open("DIR/a.txt", "r"):
        Ok(f) ->
            match f.write_text("zz"):
                Ok(n) -> print(n)
                Err(e) -> print(e)
            match f.read_text():
                Ok(s) -> print("all", s)
                Err(e) -> print(e)
            match f.read_text():
                Ok(s) -> print("rest", s)
                Err(e) -> print(e)
            f.close()
        Err(e) -> print(e)
    match fs.write_atomic("DIR/b.txt", "atom"):
        Ok(n) -> print(n)
        Err(e) -> print(e)
    match fs.read_text("DIR/b.txt"):
        Ok(s) -> print(s)
        Err(e) -> print(e)
    match fs.write_atomic("DIR/none/b.txt", "atom"):
        Ok(n) -> print(n)
        Err(e) -> print("not written")
    match fs.read_text("DIR/missing.txt"):
        Ok(s) -> print(s)
        Err(e) -> print(e)
    match fs.read_text("DIR"):
        Ok(s) -> print(s)
        Err(e) -> print(e)
    match fs.open("DIR/none/a.txt", "r"):
        Ok(f) -> f.close()
        Err(e) -> print(e)
    match fs.open("DIR", "w"):
        Ok(f) -> f.close()
        Err(e) -> print(e)
    return 0
`, "DIR", dir)
	want := strings.ReplaceAll(`5
rest 
write DIR/a.txt: bad file descriptor
all hello
rest 
4
atom
not written
open DIR/missing.txt: no such file or directory
read DIR: is a directory
open DIR/none/a.txt: no such file or directory
open DIR: is a directory
`, "DIR", dir)
	runOnBothBackends(t, "native_files", files, want)

	runOnBothBackends(t, "native_concurrent", `import std.concurrent as conc

def main() -> int:
    xs = [1, 2, 3]
    print(conc.parallel_map(xs, (x) => [x, x]))
    none: list[int] = []
    print(conc.parallel_map(none, (x) => x))
    ch = conc.Channel[int](cap=8)
    oks = conc.parallel_map(xs, (x) => ch.send(x))
    print(len(oks))
    for i in 0..3:
        match ch.recv():
            Some(v) -> print("got")
            None -> print("closed")
    m = conc.Mutex(5)
    m.with_lock((v) => 7)
    print(m.get())
    held = conc.Mutex([1])
    held.with_lock((v) => [2, 3])
    print(held.get())
    return 0
`, "[[1, 1], [2, 2], [3, 3]]\n[]\n3\ngot\ngot\ngot\n7\n[2, 3]\n")

	// A slice shares the bytes of its view. Ends outside the view are no
	// longer a program the kernel lets run (byteview_bounds); both backends
	// still bring them inside.
	runOnBothBackends(t, "native_slice", `import std.bytes as bytes

def main() -> int:
    bv = bytes.from_str("ABCDEF")
    s = bv.slice(1, 3)
    print(s.len(), bv.len(), s.read_u8(0), s.read_u8(1))
    e = bv.slice(6, 6)
    w = bv.slice(2, 6)
    t = w.slice(1, 3)
    print(e.len(), t.len(), t.read_u16_be(0))
    return 0
`, "2 6 66 67\n0 2 17477\n")
}

// A request that gets no answer is an Err on both backends, with the same
// text, and the timeout of a post given by position is the one that is
// used. The native backend gave Ok with status 200 for a request that timed
// out, after 5 s whatever the timeout.
func TestE2ERequestWithoutAnswerParity(t *testing.T) {
	runOnBothBackends(t, "request_no_answer", `import std.socket as sock
import std.requests as req
import std.time as time

def main() -> int:
    match req.get("http://127.0.0.1:1/a", timeout_ms=500):
        Ok(resp) -> print("ok", resp.status)
        Err(e) -> print(e)
    match sock.listen_tcp("127.0.0.1", 0):
        Ok(ln) ->
            url = f"http://127.0.0.1:{ln.port()}/"
            sess = req.Session(1)
            t0 = time.now_ms()
            match sess.post(url, "b", 300):
                Ok(resp) -> print("ok", resp.status)
                Err(e) -> print("post failed")
            match req.post(url, "b", 300):
                Ok(resp) -> print("ok", resp.status)
                Err(e) -> print("post failed")
            match sess.get(url, 300):
                Ok(resp) -> print("ok", resp.status)
                Err(e) -> print("get failed")
            print(time.now_ms() - t0 < 3000)
            sess.close()
            ln.close()
        Err(e) -> print("no listener")
    return 0
`, "Get \"http://127.0.0.1:1/a\": dial tcp 127.0.0.1:1: connect: connection refused\npost failed\npost failed\nget failed\nTrue\n")
}

// An answer that says how long it is (Content-Length) is whole once that
// much has come, on both backends: a server that keeps the connection open
// after it does not turn the answer into a timeout.
func TestE2EAnswerEndsAtItsLength(t *testing.T) {
	runOnBothBackends(t, "answer_then_open", `import std.socket as sock
import std.requests as req
import std.concurrent as conc
import std.time as time

def serve(ln: sock.TcpListener) -> int:
    match ln.accept(timeout_ms=3000):
        Ok(conn) ->
            match conn.recv_text(4096):
                Ok(s) -> print("asked")
                Err(e) -> print("nothing read")
            match conn.send_text("HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi"):
                Ok(n) -> print("answered")
                Err(e) -> print("not sent")
            time.sleep_ms(1500)
            conn.close()
        Err(e) -> print("no client")
    return 0

def main() -> int:
    match sock.listen_tcp("127.0.0.1", 0):
        Ok(ln) ->
            url = f"http://127.0.0.1:{ln.port()}/"
            pool = conc.ThreadPool(1, 2)
            _ = pool.submit(() => serve(ln))
            match req.get(url, 500):
                Ok(resp) -> print(resp.status, resp.body)
                Err(e) -> print("failed")
            pool.shutdown()
            ln.close()
        Err(e) -> print("no listener")
    return 0
`, "asked\nanswered\n200 hi\n")
}

// The kernel knows how long a byte view is: what it proves about reads and
// slices is what both backends do.
func TestE2EByteViewLengths(t *testing.T) {
	runOnBothBackends(t, "byteview_lengths", `import std.bytes as bytes

entity Packet:
    kind: int
    body: bytes.ByteView

def peek(bv: bytes.ByteView) -> int:
    if bv.len() > 2:
        return bv.read_u8(2)
    return 0 - 1

def head(bv: bytes.ByteView) -> int:
    requires: bv.len() >= 4
    return bv.read_u32_be(0)

def first(p: Packet) -> int:
    requires: p.body.len() >= 1
    return p.body.read_u8(0)

def at(bv: bytes.ByteView, n: int) -> int:
    if n >= 0 and n <= bv.len() - 4:
        w = bv.slice(n, n + 4)
        return w.read_u32_be(0)
    return 0 - 1

def words(s: str) -> int:
    rest = bytes.from_str(s)
    last = 0
    while rest.len() >= 2:
        last = rest.read_u16_be(0)
        rest = rest.slice(2, rest.len())
    return last

def main() -> int:
    print(peek(bytes.from_str("ABC")), peek(bytes.from_str("A")))
    bv = bytes.from_str("ABCDEF")
    h = bv.slice(0, 4)
    print(head(h), at(bv, 2), at(bv, 3), words("ABCDE"), words(""))
    p = Packet(kind=1, body=bv.slice(1, 3))
    print(first(p), p.body.len(), p.body.read_u8(1))
    hx = bytes.from_hex("0a0b0C")
    print(hx.len(), hx.read_u8(2), 1 |> hx.read_u8())
    bad = bytes.from_hex("zzzz")
    odd = bytes.from_hex("abc")
    print(bad.len(), odd.len())
    cv = bv
    bv = bytes.from_str("A")
    print(cv.read_u8(3), bv.len())
    return 0
`, "67 -1\n1094861636 1128547654 -1 17220 0\n66 2 67\n3 12 11\n0 0\n68 1\n")
}

// A `?` that returns early closes nothing, on either backend. The VM closed
// every channel a local of the returning function held, also one that was
// only another name for a channel of the caller: the caller's next send
// failed and its recv gave None, where the native build went on.
func TestE2EEarlyReturnClosesNothing(t *testing.T) {
	runOnBothBackends(t, "try_keeps_channel", `import std.concurrent as conc

def step(ch: conc.Channel[int], r: Result[int, str]) -> Result[int, str]:
    c = ch
    v = r?
    return Ok(v)

def pick(ch: conc.Channel[int], o: Option[int]) -> Option[int]:
    c = ch
    v = o?
    return Some(v)

def main() -> int:
    ch = conc.Channel[int](cap=2)
    match step(ch, Err("boom")):
        Ok(v) -> print("ok", v)
        Err(e) -> print("failed", e)
    print("sent", ch.send(1))
    match pick(ch, None):
        Some(v) -> print("some", v)
        None -> print("none")
    print("sent", ch.send(2))
    match ch.recv():
        Some(v) -> print("got", v)
        None -> print("closed")
    match ch.recv():
        Some(v) -> print("got", v)
        None -> print("closed")
    return 0
`, "failed boom\nsent True\nnone\nsent True\ngot 1\ngot 2\n")
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

// Built-in functions and pipeline stages, named with or without std.fp and
// called in a pipeline or directly, do the same on both backends; a failed
// assert reports its message.
func TestE2EBuiltinsAndStagesParity(t *testing.T) {
	runOnBothBackends(t, "builtins_and_stages", builtinsAndStagesSrc, builtinsAndStagesWant)
}

// A failed assert reports its message and exits with 1 on both backends,
// whatever the message is: one of a type sema does not know is still a value.
func TestE2EFailedAssertParity(t *testing.T) {
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	for name, tc := range map[string]struct{ args, want string }{
		"message":     {`x == 2, "boom"`, "runtime error: boom\n"},
		"no_message":  {`x == 2`, "runtime error: assertion failed\n"},
		"int_message": {`x == 2, g(123)`, "runtime error: 123\n"},
	} {
		src := "def main() -> int:\n    g = (v) => v\n    x = 1\n    print(\"before\")\n    assert(" + tc.args + ")\n    return 0\n"
		path := filepath.Join(tmp, name+".anm")
		if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
		want := "before\n" + tc.want
		vmOut, err := exec.Command(animaBin, "run", path).CombinedOutput()
		if err == nil || string(vmOut) != want {
			t.Errorf("%s: VM: err=%v, output:\n%s\nwant:\n%s", name, err, vmOut, want)
		}
		nativeBin := filepath.Join(tmp, name)
		if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
			t.Fatalf("%s: anima build failed: %v\n%s", name, err, out)
		}
		natOut, err := exec.Command(nativeBin).CombinedOutput()
		if exit, ok := err.(*exec.ExitError); !ok || exit.ExitCode() != 1 || string(natOut) != want {
			t.Errorf("%s: native: err=%v, output:\n%s\nwant:\n%s", name, err, natOut, want)
		}
	}
}

const builtinsAndStagesSrc = `import std.fp as fp

def main() -> int:
    xs: list[int[1..9]] = [1, 2, 3]
    o: Option[int] = Some(1)
    print(xs |> fp.map(x => x) |> fp.take(2), xs |> fp.sum(), xs |> drop(1))
    print(o |> fp.unwrap_or(0), o |> and_then(v => Some(v)))
    g = (v) => v > 1
    print(xs |> filter(g) |> fold(0, (a, x) => x), xs |> any(g), xs |> all(g), xs |> find(g))
    print(fp.map(xs, x => x), fp.take(xs, 2), fp.sum(xs), fp.unwrap_or(o, 0), fp.fold(xs, 0, (a, x) => x))
    print(fp.filter(xs, g), fp.any(xs, g), fp.find(xs, x => x > 5), fp.drop(xs, 2))
    h = (a, b) => b
    k = () => 7
    k2 = (v) => v
    print(h(1, 2), k(), abs(0 - 3), min(1, 2), max(1, 2), str(5), len("ab"))
    print(1 |> h(2), 1 |> k2(), 1 |> k2, 0 - 3 |> abs(), 5 |> str(), 2 |> min(1), "ab" |> len(), xs |> len)
    assert(len(xs) == 3, "three")
    assert(True)
    return 0
`

const builtinsAndStagesWant = `[1, 2] 6 [2, 3]
1 Some(1)
3 True False Some(2)
[1, 2, 3] [1, 2] 6 1 3
[2, 3] True None [3]
2 7 3 1 2 5 2
2 1 1 3 5 1 2 3
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

// An arm that is not taken binds nothing: neither a pattern that fails
// after one of its names was reached, nor one whose guard fails.
// ==, <, in, and, or mean the same on both backends: lists, maps and
// variants are equal by what they hold (a value that holds itself included),
// an entity is equal to itself only, strings are ordered byte by byte.
func TestE2EComparisonsParity(t *testing.T) {
	runOnBothBackends(t, "comparisons", comparisonsSrc, "True False False True\nTrue False\nTrue False True\nFalse True True True\nTrue False True True\nTrue False True\nTrue False\nTrue False True True False True\nTrue False True False True False True\nTrue False True True\nFalse True True False False True\n")
}

const comparisonsSrc = `type P = Pair(a: int, b: str) | Zed
type T = Node(kids: list[T]) | Leaf

entity Box:
    n: int[0..9]

def main() -> int:
    xs = [1, 2, 3]
    ys = [1, 2, 3]
    print(xs == ys, xs != ys, xs == [1, 2], xs == xs)
    print([[1], [2, 3]] == [[1], [2, 3]], [[1], [2, 3]] == [[1], [2, 4]])
    m1: map[str, int] = {"a": 1, "b": 2}
    m2: map[str, int] = {"b": 2, "a": 1}
    m3: map[str, int] = {"a": 1}
    print(m1 == m2, m1 == m3, m1 != m3)
    b1 = Box(n=1)
    b2 = Box(n=1)
    b3 = b1
    print(b1 == b2, b1 == b1, b3 == b1, b1 != b2)
    print(Pair(1, "x") == Pair(1, "x"), Pair(1, "x") == Pair(1, "y"), Zed == Zed, Zed != Pair(1, "x"))
    print(Some([1]) == Some([1]), Some([b1]) == Some([b2]), Some([b1]) == Some([b3]))
    ks = [Leaf]
    ks[0] = Node(ks)
    js = [Leaf]
    js[0] = Node(js)
    print(ks == js, ks == [Leaf])
    print("a" < "b", "b" < "a", "ab" <= "ab", "abc" > "ab", "B" >= "a", "" < "a")
    print(2 in xs, 5 in xs, "a" in m1, "z" in m1, "bc" in "abcd", "cb" in "abcd", "" in "")
    print([1] in [[2], [1]], b2 in [b1], b3 in [b1], Zed in [Pair(1, "x"), Zed])
    t = True
    f = False
    print(t and f, t or f, f implies t, t implies f, not t, t and t)
    return 0
`

// A variable that a fork branch gives another list or map holds it after the
// join on both backends: also when the new list holds what the old one held,
// and when a later branch did not touch the variable.
func TestE2EForkJoinKeepsReboundContainersParity(t *testing.T) {
	runOnBothBackends(t, "fork_equal_list", forkEqualListSrc, "[7] [1] 5\n5\n")
	runOnBothBackends(t, "fork_other_list", forkOtherListSrc, "[2, 3] {\"b\": 2} 5\n5\n")
}

const forkEqualListSrc = `workflow Tally(n: int) -> int:
    verify: sound
    start -> work:
        xs = [1]
        ys = xs
        k = 0
    fork work:
        branch a:
            xs = [1]
        branch b:
            k = 5
    join j
    step finish after j -> done:
        xs[0] = 7
        print(xs, ys, k)
        return k

def main() -> int:
    r = run_workflow Tally(1)
    print(r)
    return 0
`

const forkOtherListSrc = `workflow Tally(n: int) -> int:
    verify: sound
    start -> work:
        xs = [1]
        m: map[str, int] = {"a": 1}
        k = 0
    fork work:
        branch a:
            xs = [2, 3]
            m = {"b": 2}
        branch b:
            k = 5
    join j
    step finish after j -> done:
        print(xs, m, k)
        return k

def main() -> int:
    r = run_workflow Tally(1)
    print(r)
    return 0
`

// Both backends write a value the same way, with map entries and entity
// fields in the order of their keys, and have the same pipeline stages.
func TestE2EPrintedValuesParity(t *testing.T) {
	runOnBothBackends(t, "printed_values", printedValuesSrc, "[1, 2, 3]\n[True, False]\n[a, b]\n{\"a\": 1, \"b\": 2}\nSome(1)\nNone\nOk(x)\nCircle(2)\nDot\nBox(n=1, tag=t)\n[Some(1), None]\n[[1], [2, 3]]\n[1, 2, 3] {\"a\": 1, \"b\": 2} Box(n=1, tag=t)\n[1, 2, 3]\nTrue\nFalse\nSome(2)\n[2, 3]\n[2, 4, 6]\n[1, 2]\n[3]\n6\n3\n[1, 1, 2, 2, 3, 3]\n3 2\n1 a True\n-5\n\n")
	runOnBothBackends(t, "printed_edges", printedEdgesSrc, "\nPair(1, x) Zed\n[] [1, 2, 3] []\n[1, 2, 3] [] [1, 2, 3]\nNone False True\n[] False True None\n{}\n{\"Z\": 3, \"a\\nb\": 2, \"b\\\"q\": 1}\n{\"10\": x, \"9\": y}\nOuter(a=[1], z=Inner(k=1))\nOuter(a=[1], z=Inner(k=1)) Pair(2, y)\nTrue [2, 3]\nh o\n")
}

const printedValuesSrc = `type Shape = Circle(r: int) | Dot

entity Box:
    n: int[0..9]
    tag: str

def main() -> int:
    xs = [1, 2, 3]
    print(xs)
    print([True, False])
    print(["a", "b"])
    m: map[str, int] = {"a": 1, "b": 2}
    print(m)
    print(Some(1))
    print(None)
    print(Ok("x"))
    print(Circle(2))
    print(Dot)
    b = Box(n=1, tag="t")
    print(b)
    print([Some(1), None])
    print([[1], [2, 3]])
    print(f"{xs} {m} {b}")
    print(str(xs))
    print(xs |> any((v) => v > 1))
    print(xs |> all((v) => v > 1))
    print(xs |> find((v) => v > 1))
    print(xs |> filter((v) => v > 1))
    print(xs |> map((v) => v * 2))
    print(xs |> take(2))
    print(xs |> drop(2))
    print(xs |> sum)
    print(xs |> fold(0, (a, v) => v))
    print(xs |> flat_map((v) => [v, v]))
    print(len(xs), len(m))
    print(1, "a", True)
    print(-5)
    print("")
    return 0
`

const printedEdgesSrc = `type P = Pair(a: int, b: str) | Zed

entity Inner:
    k: int[0..9]

entity Outer:
    z: Inner
    a: list[int]

def main() -> int:
    xs = [1, 2, 3]
    print()
    print(Pair(1, "x"), Zed)
    print(xs |> take(0), xs |> take(9), xs |> take(-1))
    print(xs |> drop(0), xs |> drop(9), xs |> drop(-1))
    print(xs |> find((v) => v > 5), xs |> any((v) => v > 5), xs |> all((v) => v > 0))
    es: list[int] = []
    print(es, es |> any((v) => v > 0), es |> all((v) => v > 0), es |> find((v) => v > 0))
    m: map[str, int] = {}
    print(m)
    m["b\"q"] = 1
    m["a\nb"] = 2
    m["Z"] = 3
    print(m)
    mi: map[int, str] = {10: "x", 9: "y"}
    print(mi)
    o = Outer(z=Inner(k=1), a=[1])
    print(o)
    p = Pair(2, "y")
    print(f"{o} {p}")
    g = (v) => v > 1
    print(xs |> any(g), xs |> filter(g))
    s = "hello"
    print(s[0], s[4])
    return 0
`

func TestE2EUntakenArmBindsNothing(t *testing.T) {
	runOnBothBackends(t, "untaken_arm", untakenArmSrc, "2 2 2\n7\n5\n300\n7 5 300\n")
}

const untakenArmSrc = `type P = Pair(a: int, b: int) | Zed

def later_field(p: P) -> int:
    x = 5
    match p:
        Pair(x, 0) -> return 1
        _ -> return 10 / x

def later_field_expr(p: P) -> int:
    x = 5
    y = match p:
        Pair(x, 0) -> 1
        _ -> 10 / x
    return y

def guard(n: int) -> int:
    x = 5
    match n:
        x if x > 100 -> return 1
        _ -> return 10 / x

def taken(p: P) -> int:
    x = 5
    match p:
        Pair(x, _) -> print(x)
        Zed -> print(2)
    return x

def guarded(n: int) -> int:
    x = 5
    match n:
        x if x > 100 -> print(x)
        _ -> print(x)
    return x

def main() -> int:
    print(f"{later_field(Pair(0, 1))} {later_field_expr(Pair(0, 1))} {guard(0)}")
    print(f"{taken(Pair(7, 1))} {guarded(3)} {guarded(300)}")
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

// A pool that is made by one function, lent to another and given to a third
// to shut down runs the same on both backends; so do tasks left to the
// shutdown of their pool and a pool made and shut down in each pass of a loop.
func TestE2EThreadPoolOwnershipParity(t *testing.T) {
	const src = `import std.concurrent as conc

def make() -> conc.ThreadPool:
    return conc.ThreadPool(1, 4)

def run(pool: conc.ThreadPool) -> int:
    fut = pool.submit(() => 41)
    print(fut.await())
    return 1

def stop(own pool: conc.ThreadPool) -> int:
    pool.shutdown()
    return 0

def main() -> int:
    pool = make()
    print(run(pool))
    for i in 0..3:
        _ = pool.submit(() => print(i))
    print(stop(own pool))
    c = 0
    while c < 2:
        inner = conc.ThreadPool(1, 1)
        fut = inner.submit(() => c + 10)
        match c:
            0 -> print(f"first {fut.await()}")
            _ -> print(f"then {fut.await()}")
        inner.shutdown()
        c += 1
    return 0
`
	runOnBothBackends(t, "thread_pool_ownership", src, "41\n1\n0\n1\n2\n0\nfirst 10\nthen 11\n")
}

// Standard calls that are given what they take run the same on both
// backends: a channel and a mutex give back what they were given.
func TestE2EStandardCallsParity(t *testing.T) {
	const src = `import std.concurrent as conc
import std.crypto as crypto
import std.bytes as bytes
import std.time as time
import std.json as json
import std.requests as req

def main() -> int:
    ch = conc.Channel[int[1..9]](cap=2)
    small: int[1..9] = 4
    ok = ch.send(5)
    ok2 = ch.send(small)
    match ch.recv():
        Some(v) -> print(10 / v)
        None -> print(0)
    m = conc.Mutex(5)
    m.set(2)
    k = m.get()
    if k != 0:
        print(10 / k)
    sem = conc.Semaphore(1)
    sem.acquire()
    sem.release()
    bv = bytes.from_str("AB")
    print(bv.len(), bv.read_u8(1))
    print(crypto.constant_time_eq("a", "a"), json.encode([1, 2]))
    time.sleep_ms(ms=1)
    ok3 = 7 |> ch.send()
    match ch.recv():
        Some(v) -> print(v, 1 |> bv.read_u8())
        None -> print(0)
    pool = conc.ThreadPool(workers=1, queue_cap=2)
    f = pool.submit(() => 1)
    g = pool.submit(() => 2)
    print(req.gather([f, g]))
    pool.shutdown()
    return 0
`
	runOnBothBackends(t, "standard_calls", src, "2\n5\n2 66\nTrue [1,2]\n4 66\n[1, 2]\n")
}
