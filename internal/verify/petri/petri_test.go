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

// A future given a name is awaited or gathered somewhere in the function,
// whatever statement makes it or awaits it; `_ = pool.submit(...)` leaves the
// task to the shutdown of its pool.
func TestFuturesAreAwaitedOrLeftToTheirPool(t *testing.T) {
	const head = `
import std.concurrent as conc

def main() -> int:
    pool = conc.ThreadPool(2, 4)
    c = 1
`
	const tail = "    pool.shutdown()\n    return 0\n"
	leaks := map[string]string{
		"at the top":      "    f = pool.submit(() => 1)\n",
		"in a loop":       "    for i in 0..3:\n        f = pool.submit(() => 1)\n",
		"in a while":      "    while c < 3:\n        f = pool.submit(() => 1)\n        c += 1\n",
		"in a match arm":  "    match c:\n        1 ->\n            f = pool.submit(() => 1)\n        _ -> print(0)\n",
		"in an if branch": "    if c == 1:\n        f = pool.submit(() => 1)\n",
	}
	for name, body := range leaks {
		rep := verifyPetri(t, head+body+tail)
		if got := strings.Join(rep.Errors(), "\n"); !strings.Contains(got, `"f" created by async call was never awaited or gathered`) {
			t.Errorf("%s: expected a future leak, got:\n%s", name, got)
		}
	}
	fine := map[string]string{
		"awaited":                  "    f = pool.submit(() => 1)\n    r = f.await()\n",
		"awaited in every arm":     "    f = pool.submit(() => 1)\n    match c:\n        1 ->\n            r = f.await()\n        _ ->\n            r = f.await()\n",
		"awaited in a loop":        "    f = pool.submit(() => 1)\n    for i in 0..2:\n        r = f.await()\n",
		"awaited in an f-string":   "    f = pool.submit(() => 1)\n    print(f\"got {f.await()}\")\n",
		"awaited in an expression": "    f = pool.submit(() => 1)\n    xs = [f.await()]\n",
		"gathered":                 "    f = pool.submit(() => 1)\n    g = pool.submit(() => 2)\n    rs = conc.gather([f, g])\n",
		"left to the pool":         "    _ = pool.submit(() => 1)\n    for i in 0..3:\n        _ = pool.submit(() => i)\n",
	}
	for name, body := range fine {
		rep := verifyPetri(t, head+body+tail)
		if got := strings.Join(rep.Errors(), "\n"); got != "" {
			t.Errorf("%s: expected no error, got:\n%s", name, got)
		}
	}
}
