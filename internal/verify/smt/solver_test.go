package smt

import "testing"

func TestSMTEscrowProofAndCounterexample(t *testing.T) {
	bal := Var("bal")
	frz := Var("frz")
	amt := Var("amt")

	// Domain + precondition + guard
	pre := And(
		Ge(bal, Const(0)),
		Le(bal, Const(1_000_000)),
		Ge(frz, Const(0)),
		Le(frz, Const(1_000_000)),
		Le(bal.Add(frz), Const(990_000)),
		Ge(amt, Const(1)),
		Le(amt, Const(10_000)),
	)
	guard := Ge(bal, amt)

	// Postcondition: bal' = bal - amt in [0..1e6] AND frz' = frz + amt in [0..1e6] AND bal'+frz' <= 1e6
	bal2 := bal.Sub(amt)
	frz2 := frz.Add(amt)
	post := And(
		Ge(bal2, Const(0)),
		Le(bal2, Const(1_000_000)),
		Ge(frz2, Const(0)),
		Le(frz2, Const(1_000_000)),
		Le(bal2.Add(frz2), Const(1_000_000)),
	)

	// Valid VC: pre && guard && !post must be UNSAT!
	vcValid := And(pre, guard, Not(post))
	res := CheckSat(vcValid)
	if res.Status != StatusUnsat {
		t.Fatalf("expected UNSAT (valid proof), got %v model=%v (%s)", res.Status, res.IntModel, res.Explain)
	}

	// Buggy VC without guard: must be SAT with counterexample!
	vcBuggy := And(pre, Not(post))
	resBug := CheckSat(vcBuggy)
	if resBug.Status != StatusSat {
		t.Fatalf("expected SAT counterexample when guard missing, got %v", resBug.Status)
	}
	if !Eval(vcBuggy, resBug.IntModel, resBug.BoolModel) {
		t.Fatalf("returned model does not satisfy vcBuggy: %v", resBug.IntModel)
	}
	if resBug.IntModel["bal"] >= resBug.IntModel["amt"] {
		t.Fatalf("expected underflow counterexample bal < amt, got %v", resBug.IntModel)
	}
}

func TestSMTIntegerBranchAndBoundParity(t *testing.T) {
	// 2x + 2y == 1 has rational solutions (0.5, 0) but NO integer solutions!
	x := Var("x")
	y := Var("y")
	f := Eq(x.Scale(2).Add(y.Scale(2)), Const(1))
	res := CheckSat(f)
	if res.Status != StatusUnsat {
		t.Fatalf("expected integer UNSAT for 2x+2y=1, got %v model=%v", res.Status, res.IntModel)
	}
}

func TestSMTExhaustiveMatchHoleDetection(t *testing.T) {
	score := Var("score")
	dom := And(Ge(score, Const(0)), Le(score, Const(100)))
	arm1 := And(Ge(score, Const(0)), Le(score, Const(59)))
	arm2 := And(Ge(score, Const(61)), Le(score, Const(100)))

	// Uncovered: dom && !arm1 && !arm2 -> must return SAT with score == 60!
	uncovered := And(dom, Not(arm1), Not(arm2))
	res := CheckSat(uncovered)
	if res.Status != StatusSat {
		t.Fatalf("expected SAT finding gap at score=60, got %v", res.Status)
	}
	if res.IntModel["score"] != 60 {
		t.Fatalf("expected exact uncovered score=60, got %d", res.IntModel["score"])
	}

	// Now fill arm2 with >= 60: must be UNSAT!
	arm2Fixed := And(Ge(score, Const(60)), Le(score, Const(100)))
	resFixed := CheckSat(And(dom, Not(arm1), Not(arm2Fixed)))
	if resFixed.Status != StatusUnsat {
		t.Fatalf("expected UNSAT after fixing gap, got %v model=%v", resFixed.Status, resFixed.IntModel)
	}
}
