package spark

import (
	"strings"
	"testing"
)

// A workflow is verified one path at a time, as it runs: a step is checked
// with what is known on the way to it. The kernel used to run the bodies of
// all nodes one after the other in the order they are written.
func TestSPARKWorkflowIsVerifiedAlongItsPaths(t *testing.T) {
	head := "workflow W(n: int[0..100]) -> int:\n    verify: sound\n\n"
	choice := "    choice after a:\n        when n > 0 -> pos\n        else -> zero\n\n"
	cases := []struct {
		name string
		body string
		want string // a failed VC, or "" when every one is proved
	}{
		{"a step does not see what the step written above it assigned",
			"    start -> a:\n        d = 0\n\n" + choice +
				"    step pos -> done:\n        d = 5\n        return 1\n    step zero -> done:\n        return 10 / d\n",
			"workflow:W.div_nonzero"},
		{"a path that ends without a return",
			"    start -> a:\n        d = 0\n\n" + choice +
				"    step pos -> done:\n        return 1\n    step zero -> done:\n        d = 2\n",
			"workflow:W.returns"},
		{"a step with no way on ends the workflow",
			"    start -> a:\n        d = 0\n\n" + choice +
				"    step pos -> done:\n        return 1\n    step zero:\n        d = 2\n",
			"workflow:W.returns"},
		{"a branch that goes straight to done",
			"    start -> a:\n        d = 0\n\n    choice after a:\n        when n > 0 -> pos\n        else -> done\n\n" +
				"    step pos -> done:\n        return 1\n",
			"workflow:W.returns"},
		{"a merge is run by neither backend",
			"    start -> a:\n        d = 1\n\n" + choice +
				"    step pos -> m:\n        d = 2\n    step zero -> m:\n        d = 3\n\n    merge m after pos, zero -> fin\n\n" +
				"    step fin -> done:\n        return 10 / d\n",
			"workflow:W.returns"},
		{"a workflow that comes back to a step",
			"    start -> a:\n        d = 5\n\n    step a -> b:\n        d = d - 1\n    choice after b:\n        when d > 0 -> a\n        else -> fin\n\n" +
				"    step fin -> done:\n        return d\n",
			"workflow:W.acyclic"},
		{"the value of the path that is taken",
			"    start -> a:\n        d = 0\n\n" + choice +
				"    step pos -> fin:\n        d = n\n    step zero -> fin:\n        d = 1\n\n    step fin -> done:\n        return 10 / d\n",
			""},
		{"and of the other one",
			"    start -> a:\n        d = 0\n\n" + choice +
				"    step pos -> fin:\n        d = n\n    step zero -> fin:\n        d = 0\n\n    step fin -> done:\n        return 10 / d\n",
			"workflow:W.div_nonzero"},
		{"a later guard is taken after the earlier ones failed",
			"    start -> a:\n        d = 0\n\n    choice after a:\n        when n > 0 -> pos\n        when n <= 0 -> zero\n\n" +
				"    step pos -> done:\n        return 10 / n\n    step zero -> done:\n        return 10 / (1 - n)\n",
			""},
		{"a fork, its join and the step after it",
			"    start -> split:\n        x = 1\n        y = 2\n\n    fork split:\n        branch left:\n            x = n + 1\n        branch right:\n            y = n + 2\n    join both\n\n" +
				"    step fin after both -> done:\n        return 100 / x + 100 / y\n",
			""},
		{"a step that is never reached is not checked",
			"    start -> a:\n        d = 0\n\n    step a -> done:\n        return 1\n    step orphan -> done:\n        return 10 / d\n",
			""},
	}
	for _, c := range cases {
		failed := failedVCs(verifySrc(t, head+c.body))
		if c.want == "" {
			if len(failed) != 0 {
				t.Errorf("%s: expected every VC proved, failed: %v", c.name, failed)
			}
			continue
		}
		if !strings.Contains(strings.Join(failed, " "), c.want) {
			t.Errorf("%s: expected %s to fail, failed: %v", c.name, c.want, failed)
		}
	}
}

// A workflow that returns nothing may end anywhere, and the invariant of an
// entity it may change is proved where it ends.
func TestSPARKWorkflowThatReturnsNothing(t *testing.T) {
	src := func(take string) string {
		return "entity Acc:\n    bal: int\n    invariant: bal >= 0\n\n" +
			"workflow W(mut acc: Acc, n: int[0..100]):\n    verify: sound\n\n    start -> a:\n        ok = n > 50\n\n" +
			"    choice after a:\n        when ok -> take\n        when not ok -> leave\n\n" +
			"    step take -> done:\n        acc.bal = " + take + "\n    step leave -> done:\n        print(\"left\")\n"
	}
	if failed := failedVCs(verifySrc(t, src("n"))); len(failed) != 0 {
		t.Errorf("expected every VC proved, failed: %v", failed)
	}
	if failed := strings.Join(failedVCs(verifySrc(t, src("0 - 1"))), " "); !strings.Contains(failed, "W.mut_acc_invariant") {
		t.Errorf("expected W.mut_acc_invariant to fail, failed: %v", failed)
	}
}
