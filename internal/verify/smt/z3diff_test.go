package smt

import (
	"bytes"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"sort"
	"strings"
	"testing"
)

func smtInt(v int64) string {
	if v < 0 {
		// Avoid negating MinInt64.
		return fmt.Sprintf("(- %s)", strings.TrimPrefix(fmt.Sprintf("%d", v), "-"))
	}
	return fmt.Sprintf("%d", v)
}

// toSMTLIB renders a BoolExpr as an SMT-LIB 2 term over QF_LIA.
func toSMTLIB(e BoolExpr) string {
	switch x := e.(type) {
	case BoolConst:
		if x.Val {
			return "true"
		}
		return "false"
	case BoolVar:
		return x.Name
	case AtomExpr:
		keys := make([]string, 0, len(x.Atom.Coeffs))
		for k, c := range x.Atom.Coeffs {
			if c != 0 {
				keys = append(keys, k)
			}
		}
		sort.Strings(keys)
		parts := []string{"0"}
		for _, k := range keys {
			parts = append(parts, fmt.Sprintf("(* %s %s)", smtInt(x.Atom.Coeffs[k]), k))
		}
		return fmt.Sprintf("(<= (+ %s) %s)", strings.Join(parts, " "), smtInt(x.Atom.Bound))
	case NotExpr:
		return fmt.Sprintf("(not %s)", toSMTLIB(x.Inner))
	case AndExpr:
		return nary("and", x.Args)
	case OrExpr:
		return nary("or", x.Args)
	}
	panic(fmt.Sprintf("unhandled BoolExpr %T", e))
}

func nary(op string, args []BoolExpr) string {
	parts := make([]string, len(args))
	for i, a := range args {
		parts[i] = toSMTLIB(a)
	}
	return fmt.Sprintf("(%s %s)", op, strings.Join(parts, " "))
}

// z3CheckAll asks one z3 process for the satisfiability of every formula.
func z3CheckAll(t *testing.T, z3 string, intVars, boolVars []string, fs []BoolExpr) []string {
	t.Helper()
	var sb strings.Builder
	sb.WriteString("(set-logic QF_LIA)\n(set-option :timeout 10000)\n")
	for _, v := range intVars {
		fmt.Fprintf(&sb, "(declare-const %s Int)\n", v)
	}
	for _, v := range boolVars {
		fmt.Fprintf(&sb, "(declare-const %s Bool)\n", v)
	}
	for _, f := range fs {
		fmt.Fprintf(&sb, "(push)\n(assert %s)\n(check-sat)\n(pop)\n", toSMTLIB(f))
	}
	cmd := exec.Command(z3, "-in", "-smt2")
	cmd.Stdin = strings.NewReader(sb.String())
	var out, errb bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &errb
	if err := cmd.Run(); err != nil {
		t.Fatalf("z3 failed: %v\n%s\n%s", err, out.String(), errb.String())
	}
	lines := strings.Fields(out.String())
	if len(lines) != len(fs) {
		t.Fatalf("z3 returned %d answers for %d formulas:\n%s", len(lines), len(fs), out.String())
	}
	return lines
}

// TestDifferentialCheckSatAgainstZ3 compares CheckSat with Z3 on random unbounded QF_LIA formulas.
// Z3 is a test-only oracle: the anima binary never depends on it.
func TestDifferentialCheckSatAgainstZ3(t *testing.T) {
	z3, err := exec.LookPath("z3")
	if err != nil {
		if os.Getenv("ANIMA_REQUIRE_Z3") != "" {
			t.Fatal("ANIMA_REQUIRE_Z3 is set but z3 is not on PATH")
		}
		t.Skip("z3 not on PATH")
	}
	// Unbounded integer problems can exhaust the branch-and-bound budget, which costs seconds per formula,
	// so the configs with large coefficients run fewer cases.
	cfgs := []genConfig{
		{intVars: []string{"x", "y", "z"}, boolVars: []string{"p", "q"}, maxCoeff: 5, maxConst: 20, maxDepth: 3},
		{intVars: []string{"x", "y", "z", "w"}, boolVars: []string{"p", "q", "r"}, maxCoeff: 9, maxConst: 1000, maxDepth: 4},
		{intVars: []string{"x", "y", "z"}, maxCoeff: 1000, maxConst: 1_000_000, maxDepth: 3},
	}
	counts := []int{2000, 300, 100}
	for ci, cfg := range cfgs {
		n := counts[ci]
		if testing.Short() {
			n /= 10
		}
		t.Run(fmt.Sprintf("cfg%d", ci), func(t *testing.T) {
			fs := make([]BoolExpr, n)
			for i := range fs {
				fs[i] = genFormula(rand.New(rand.NewSource(int64(ci)*1_000_003+int64(i))), cfg, 0)
			}
			z3Res := z3CheckAll(t, z3, cfg.intVars, cfg.boolVars, fs)
			var unknowns, failures, skipped int
			for i, f := range fs {
				if z3Res[i] != "sat" && z3Res[i] != "unsat" {
					skipped++
					continue
				}
				res := CheckSat(f)
				var problem string
				switch res.Status {
				case StatusSat:
					if !Eval(f, res.IntModel, res.BoolModel) {
						problem = fmt.Sprintf("SAT model %v %v does not satisfy formula", res.IntModel, res.BoolModel)
					} else if z3Res[i] == "unsat" {
						problem = "solver SAT but z3 UNSAT"
					}
				case StatusUnsat:
					if z3Res[i] == "sat" {
						problem = fmt.Sprintf("UNSOUND: solver UNSAT (%s) but z3 SAT", res.Explain)
					}
				default:
					unknowns++
					if res.Explain == "" {
						problem = "UNKNOWN without an explanation"
					}
					if unknowns <= 5 {
						t.Logf("formula %d: UNKNOWN (%s), z3 %s: %s", i, res.Explain, z3Res[i], f)
					}
				}
				if problem != "" {
					failures++
					if failures <= 10 {
						t.Errorf("formula %d: %s: %s", i, problem, f)
					}
				}
			}
			t.Logf("%d formulas: %d disagreements, %d UNKNOWN, %d skipped (z3 inconclusive)", n, failures, unknowns, skipped)
		})
	}
}
