package petri

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
)

func verifyPetri(t *testing.T, src string) *Report {
	t.Helper()
	prog, err := parser.Parse("petri_test.anm", src)
	if err != nil {
		t.Fatalf("parse failed: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema failed: %v", err)
	}
	return Verify(info)
}

func TestValidFulfillWorkflowSoundnessAndShortCircuit(t *testing.T) {
	src := `
entity Account:
    balance: int[0..1000]

monitor LedgerLock:
    state Free:
        on acquire_write -> Locked
    state Locked:
        on release_write -> Free

workflow FulfillOrder(ok: bool):
    verify: sound, 1_safe
    pool robot_arm: int[0..2] = 2

    start -> check_balance
    step check_balance
    choice after check_balance:
        when ok -> fork_fulfill
        when not ok -> reject_order

    fork fork_fulfill:
        branch ledger_commit:
            sync LedgerLock.acquire_write
            sync LedgerLock.release_write
        branch warehouse_pick:
            acquire robot_arm
            step pick_and_pack
            release robot_arm
    join join_fulfill

    step ship_order after join_fulfill -> done
    step reject_order -> done
`
	rep := verifyPetri(t, src)
	if !rep.OK() {
		t.Fatalf("expected FulfillOrder to be 1-safe & van der Aalst Sound, got: %v", rep.Errors())
	}
	w := rep.Workflows[0]
	if !w.Sound || !w.OneSafe || !w.ShortCircuitL4 || !w.StructurallyWF {
		t.Fatalf("unexpected soundness result: %+v", w)
	}
	pnml := ExportPNML([]*PetriNet{w.Net})
	if !strings.Contains(pnml, "<pnml") || !strings.Contains(pnml, "pool:robot_arm") {
		t.Fatalf("invalid PNML output: %s", pnml)
	}
}

func TestCatchesForkMergeChoiceJoinAndPoolLeak(t *testing.T) {
	// 1. fork (AND-split) into merge (XOR-join) -> Improper Completion + Not 1-safe!
	repFM := verifyPetri(t, `
workflow BadForkMerge:
    verify: sound, 1_safe
    start -> split
    fork split:
        branch a:
            step do_a
        branch b:
            step do_b
    merge bad_merge
    step finish after bad_merge -> done
`)
	if repFM.OK() {
		t.Fatalf("expected Improper Completion for fork+merge")
	}
	if !strings.Contains(strings.Join(repFM.Errors(), "\n"), "IMPROPER COMPLETION") {
		t.Fatalf("expected IMPROPER COMPLETION error, got: %v", repFM.Errors())
	}

	// 2. choice (XOR-split) into join (AND-join) -> Option to Complete violated (deadlock)!
	repCJ := verifyPetri(t, `
workflow BadChoiceJoin(flag: bool):
    verify: sound, 1_safe
    start -> eval
    step eval
    choice after eval:
        when flag -> left_step
        when not flag -> right_step
    step left_step -> bad_join
    step right_step -> bad_join
    join bad_join -> done
`)
	if repCJ.OK() {
		t.Fatalf("expected Option to Complete violation for choice+join")
	}
	if !strings.Contains(strings.Join(repCJ.Errors(), "\n"), "OPTION TO COMPLETE") {
		t.Fatalf("expected OPTION TO COMPLETE error, got: %v", repCJ.Errors())
	}

	// 3. Pool resource leak: acquire without release -> Improper Completion + L4-Liveness fail!
	repLeak := verifyPetri(t, `
workflow BadPoolLeak:
    verify: sound, 1_safe
    pool arm: int[0..2] = 2
    start -> work
    fork work:
        branch a:
            acquire arm
            step grab
        branch b:
            step noop
    join j -> done
`)
	if repLeak.OK() {
		t.Fatalf("expected pool leak failure when arm not released")
	}
	if !strings.Contains(strings.Join(repLeak.Errors(), "\n"), "IMPROPER COMPLETION") {
		t.Fatalf("expected improper completion due to leaked pool token, got: %v", repLeak.Errors())
	}
}

// A task is waited for by the shutdown of its pool: its future, when it is
// given a name, is awaited or gathered somewhere in the function, whatever
// statement makes it or awaits it; `_ = pool.submit(...)` leaves it to the pool.
func TestTaskFuturesAreAwaitedOrLeftToTheirPool(t *testing.T) {
	const head = `
import std.concurrent as conc
import std.requests as req

def main() -> int:
    pool = conc.ThreadPool(2, 4)
    c = 1
`
	const tail = "    pool.shutdown()\n    return 0\n"
	leaks := map[string]string{
		"at the top":                "    f = pool.submit(() => 1)\n",
		"in a loop":                 "    for i in 0..3:\n        f = pool.submit(() => 1)\n",
		"in a while":                "    while c < 3:\n        f = pool.submit(() => 1)\n        c += 1\n",
		"in a match arm":            "    match c:\n        1 ->\n            f = pool.submit(() => 1)\n        _ -> print(0)\n",
		"in an if branch":           "    if c == 1:\n        f = pool.submit(() => 1)\n",
		"awaited in a closure only": "    f = pool.submit(() => 1)\n    g = () => f.await()\n",
	}
	for name, body := range leaks {
		rep := verifyPetri(t, head+body+tail)
		if got := strings.Join(rep.Errors(), "\n"); !strings.Contains(got, `"f" created by async call was never awaited or gathered`) {
			t.Errorf("%s: expected a future leak, got:\n%s", name, got)
		}
	}
	fine := map[string]string{
		"awaited":                   "    f = pool.submit(() => 1)\n    r = f.await()\n",
		"awaited in every arm":      "    f = pool.submit(() => 1)\n    match c:\n        1 ->\n            r = f.await()\n        _ ->\n            r = f.await()\n",
		"awaited in one branch":     "    f = pool.submit(() => 1)\n    if c == 1:\n        r = f.await()\n",
		"awaited in a loop":         "    f = pool.submit(() => 1)\n    for i in 0..2:\n        r = f.await()\n",
		"awaited in an f-string":    "    f = pool.submit(() => 1)\n    print(f\"got {f.await()}\")\n",
		"awaited in an expression":  "    f = pool.submit(() => 1)\n    xs = [f.await()]\n",
		"gathered":                  "    f = pool.submit(() => 1)\n    g = pool.submit(() => 2)\n    rs = req.gather([f, g])\n",
		"left to the pool":          "    _ = pool.submit(() => 1)\n    for i in 0..3:\n        _ = pool.submit(() => i)\n",
		"made in both branches":     "    f = pool.submit(() => 0)\n    r = f.await()\n    if c == 1:\n        f = pool.submit(() => 1)\n    else:\n        f = pool.submit(() => 2)\n    r = f.await()\n",
		"made again after an await": "    f = pool.submit(() => 1)\n    r = f.await()\n    f = pool.submit(() => 2)\n",
	}
	for name, body := range fine {
		rep := verifyPetri(t, head+body+tail)
		if got := strings.Join(rep.Errors(), "\n"); got != "" {
			t.Errorf("%s: expected no error, got:\n%s", name, got)
		}
	}
}

// Nothing waits for a request but its await: the future of get_async is
// awaited or gathered on every path, before its name is given another value.
func TestRequestFuturesAreAwaitedOnEveryPath(t *testing.T) {
	const head = `
import std.requests as req

def risky() -> Result[int, str]:
    return Err("no")

def is_err(r: Result[HttpResponse, str]) -> bool:
    match r:
        Ok(resp) -> return False
        Err(e) -> return True

def checked(r: Result[HttpResponse, str]) -> Result[int, str]:
    return Ok(1)

def first(a: int, b: bool) -> int:
    return a

def second(b: bool, a: int) -> int:
    return a

def main() -> Result[int, str]:
    sess = req.Session(4)
    c = 1
    f = sess.get_async("http://127.0.0.1:1/a", timeout_ms=100)
`
	const again = "    f = sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n"
	const tail = "    sess.close()\n    return Ok(0)\n"
	leaks := map[string]string{
		"never awaited":                                       "",
		"given another after its await":                       "    r = f.await()\n" + again,
		"given another before its await":                      again + "    r = f.await()\n",
		"awaited in a closure only":                           "    g = () => f.await()\n",
		"awaited in one branch":                               "    if c == 1:\n        r = f.await()\n",
		"awaited in one arm":                                  "    match c:\n        1 ->\n            r = f.await()\n        _ -> print(0)\n",
		"awaited in a loop only":                              "    for i in 0..2:\n        r = f.await()\n",
		"made in a loop":                                      "    r = f.await()\n    for i in 0..2:\n    " + again,
		"pending at an early return":                          "    if c == 1:\n        return Ok(1)\n    r = f.await()\n",
		"pending at a try":                                    "    v = risky()?\n    r = f.await()\n",
		"both names given another":                            "    g = f\n" + again + "    g = f\n    r = f.await()\n",
		"awaited in the guard of one arm":                     "    match c:\n        1 if is_err(f.await()) -> print(1)\n        _ -> print(0)\n",
		"awaited in a guard only":                             "    match c:\n        _ if is_err(f.await()) -> print(1)\n        _ -> print(0)\n",
		"awaited on the right of and":                         "    x = c == 2 and is_err(f.await())\n",
		"awaited in a guard that may not run":                 "    match c:\n        _ if c == 2 and is_err(f.await()) -> print(1)\n        _ -> print(0)\n",
		"second name differs by branch":                       "    h = sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n    g = f\n    if c == 1:\n        g = h\n    r = g.await()\n",
		"second name changed by a loop":                       "    h = sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n    g = f\n    for i in 0..2:\n        g = h\n    r = g.await()\n    r = h.await()\n",
		"name taken by a pattern":                             "    h = sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n    match h:\n        f if is_err(f.await()) -> print(1)\n        _ -> print(0)\n    r = h.await()\n",
		"awaited in a keyword argument that runs after a try": "    x = first(b=is_err(f.await()), a=risky()?)\n",
		"awaited beside a try in the same statement":          "    x = second(is_err(f.await()), risky()?)\n",
		"awaited after a try in the same statement":           "    x = first(risky()?, is_err(f.await()))\n",
		"started in a list":                                   "    r = f.await()\n    fs = [sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)]\n",
		"started in an argument":                              "    r = f.await()\n    b = is_err(sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100).await()) or is_err(r)\n    print(sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100))\n",
		"started in a closure":                                "    r = f.await()\n    g = () => sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n",
		"started in a match expression":                       "    r = f.await()\n    g = match c:\n        1 -> sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n        _ -> sess.get_async(\"http://127.0.0.1:1/c\", timeout_ms=100)\n    r = g.await()\n",
		"discarded":                                           "    r = f.await()\n    _ = sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n",
	}
	for name, body := range leaks {
		rep := verifyPetri(t, head+body+tail)
		if got := strings.Join(rep.Errors(), "\n"); !strings.Contains(got, "Petri Future token leak in main") {
			t.Errorf("%s: expected a future leak, got:\n%s", name, got)
		}
	}
	fine := map[string]string{
		"awaited":                                     "    r = f.await()\n",
		"awaited before a try":                        "    r = f.await()\n    v = risky()?\n",
		"awaited in every branch":                     "    if c == 1:\n        r = f.await()\n    else:\n        r = f.await()\n",
		"awaited in every arm":                        "    match c:\n        1 ->\n            r = f.await()\n        _ ->\n            r = f.await()\n",
		"awaited before each return":                  "    if c == 1:\n        r = f.await()\n        return Ok(1)\n    r = f.await()\n",
		"made in both branches":                       "    r = f.await()\n    if c == 1:\n    " + again + "    else:\n    " + again + "    r = f.await()\n",
		"each awaited in turn":                        "    r = f.await()\n" + again + "    r = f.await()\n",
		"made and awaited in a loop":                  "    r = f.await()\n    for i in 0..2:\n    " + again + "        r = f.await()\n",
		"gathered":                                    "    g = sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n    rs = req.gather([f, g])\n",
		"awaited under a second name":                 "    g = f\n    r = g.await()\n",
		"awaited under its first name":                "    g = f\n    r = f.await()\n",
		"awaited by what a try is applied to":         "    resp = f.await()?\n",
		"awaited inside what a try is applied to":     "    v = checked(f.await())?\n",
		"awaited on the left of and":                  "    x = is_err(f.await()) and c == 1\n",
		"awaited in a guard and in the arms after it": "    match c:\n        _ if is_err(f.await()) -> print(1)\n        _ ->\n            r = f.await()\n",
		"second name given another":                   "    g = f\n    g = sess.get_async(\"http://127.0.0.1:1/b\", timeout_ms=100)\n    rs = req.gather([f, g])\n",
	}
	for name, body := range fine {
		rep := verifyPetri(t, head+body+tail)
		if got := strings.Join(rep.Errors(), "\n"); got != "" {
			t.Errorf("%s: expected no error, got:\n%s", name, got)
		}
	}
}
