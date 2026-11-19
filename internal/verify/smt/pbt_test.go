package smt

import (
	"fmt"
	"math/rand"
	"testing"
)

// genConfig controls the shape of randomly generated formulas.
type genConfig struct {
	intVars  []string
	boolVars []string
	maxCoeff int64
	maxConst int64
	maxDepth int
}

func genTerm(rng *rand.Rand, cfg genConfig) LinearTerm {
	t := Const(rng.Int63n(2*cfg.maxConst+1) - cfg.maxConst)
	n := 1 + rng.Intn(len(cfg.intVars))
	for i := 0; i < n; i++ {
		v := cfg.intVars[rng.Intn(len(cfg.intVars))]
		c := rng.Int63n(2*cfg.maxCoeff+1) - cfg.maxCoeff
		t = t.Add(Var(v).Scale(c))
	}
	return t
}

func genAtom(rng *rand.Rand, cfg genConfig) BoolExpr {
	if len(cfg.boolVars) > 0 && rng.Intn(6) == 0 {
		return BoolVar{Name: cfg.boolVars[rng.Intn(len(cfg.boolVars))]}
	}
	a, b := genTerm(rng, cfg), genTerm(rng, cfg)
	switch rng.Intn(6) {
	case 0:
		return Le(a, b)
	case 1:
		return Lt(a, b)
	case 2:
		return Ge(a, b)
	case 3:
		return Gt(a, b)
	case 4:
		return Eq(a, b)
	default:
		return Neq(a, b)
	}
}

func genFormula(rng *rand.Rand, cfg genConfig, depth int) BoolExpr {
	if depth >= cfg.maxDepth || rng.Intn(4) == 0 {
		return genAtom(rng, cfg)
	}
	switch rng.Intn(5) {
	case 0:
		return Not(genFormula(rng, cfg, depth+1))
	case 1:
		return Implies(genFormula(rng, cfg, depth+1), genFormula(rng, cfg, depth+1))
	case 2:
		n := 2 + rng.Intn(3)
		args := make([]BoolExpr, n)
		for i := range args {
			args[i] = genFormula(rng, cfg, depth+1)
		}
		return Or(args...)
	default:
		n := 2 + rng.Intn(3)
		args := make([]BoolExpr, n)
		for i := range args {
			args[i] = genFormula(rng, cfg, depth+1)
		}
		return And(args...)
	}
}

// boxed constrains every int var to [-bound, bound] so satisfiability can be decided by enumeration.
func boxed(f BoolExpr, vars []string, bound int64) BoolExpr {
	parts := make([]BoolExpr, 0, 2*len(vars)+1)
	for _, v := range vars {
		parts = append(parts, Ge(Var(v), Const(-bound)), Le(Var(v), Const(bound)))
	}
	return And(append(parts, f)...)
}

// bruteForceSat enumerates every assignment of intVars in [-bound, bound] and boolVars in {false, true}.
func bruteForceSat(f BoolExpr, intVars, boolVars []string, bound int64) (bool, map[string]int64, map[string]bool) {
	im := make(map[string]int64, len(intVars))
	bm := make(map[string]bool, len(boolVars))
	var recBool func(i int) bool
	recBool = func(i int) bool {
		if i == len(boolVars) {
			return Eval(f, im, bm)
		}
		for _, b := range []bool{false, true} {
			bm[boolVars[i]] = b
			if recBool(i + 1) {
				return true
			}
		}
		return false
	}
	var recInt func(i int) bool
	recInt = func(i int) bool {
		if i == len(intVars) {
			return recBool(0)
		}
		for v := -bound; v <= bound; v++ {
			im[intVars[i]] = v
			if recInt(i + 1) {
				return true
			}
		}
		return false
	}
	if recInt(0) {
		return true, im, bm
	}
	return false, nil, nil
}

var boxedCfg = genConfig{
	intVars:  []string{"x", "y", "z"},
	boolVars: []string{"p", "q"},
	maxCoeff: 3,
	maxConst: 8,
	maxDepth: 3,
}

const boxBound = 4

// checkBoxedSeed returns a non-empty description when CheckSat disagrees with exhaustive enumeration.
func checkBoxedSeed(seed int64) (problem string, unknown bool) {
	rng := rand.New(rand.NewSource(seed))
	f := boxed(genFormula(rng, boxedCfg, 0), boxedCfg.intVars, boxBound)
	want, wim, wbm := bruteForceSat(f, boxedCfg.intVars, boxedCfg.boolVars, boxBound)
	res := CheckSat(f)
	switch res.Status {
	case StatusSat:
		if !Eval(f, res.IntModel, res.BoolModel) {
			return fmt.Sprintf("seed %d: SAT model %v %v does not satisfy %s", seed, res.IntModel, res.BoolModel, f), false
		}
		if !want {
			return fmt.Sprintf("seed %d: solver SAT but enumeration UNSAT for %s", seed, f), false
		}
	case StatusUnsat:
		if want {
			return fmt.Sprintf("seed %d: UNSOUND: solver UNSAT (%s) but %v %v satisfies %s", seed, res.Explain, wim, wbm, f), false
		}
	default:
		return fmt.Sprintf("seed %d: UNKNOWN (%s) on %s", seed, res.Explain, f), true
	}
	return "", false
}

// TestPBTCheckSatAgainstBruteForce compares CheckSat with exhaustive enumeration on random boxed formulas.
func TestPBTCheckSatAgainstBruteForce(t *testing.T) {
	n := int64(5000)
	if testing.Short() {
		n = 500
	}
	var unknowns, failures int
	for seed := int64(0); seed < n; seed++ {
		problem, unknown := checkBoxedSeed(seed)
		if problem == "" {
			continue
		}
		if unknown {
			unknowns++
			if unknowns <= 5 {
				t.Log(problem)
			}
			continue
		}
		failures++
		if failures <= 10 {
			t.Error(problem)
		}
	}
	if failures > 0 {
		t.Errorf("%d/%d formulas disagree with enumeration", failures, n)
	}
	if unknowns > 0 {
		t.Errorf("%d/%d decidable boxed formulas returned UNKNOWN", unknowns, n)
	}
}

func FuzzCheckSatAgainstBruteForce(f *testing.F) {
	for seed := int64(0); seed < 16; seed++ {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, seed int64) {
		if problem, _ := checkBoxedSeed(seed); problem != "" {
			t.Fatal(problem)
		}
	})
}

// An assignment the theory solver cannot decide must not hide a satisfiable alternative.
func TestUndecidedTheoryAssignmentDoesNotHideSat(t *testing.T) {
	x, y, z := Var("x"), Var("y"), Var("z")
	f := Or(
		Eq(x.Scale(3).Add(y.Scale(7)).Add(z.Scale(4)), Const(15)),
		BoolVar{Name: "p"},
		Le(y, Const(3)),
		Le(x.Scale(5).Add(y.Scale(2)).Sub(z.Scale(3)), Const(21)),
	)
	res := CheckSat(f)
	if res.Status != StatusSat {
		t.Fatalf("expected SAT, got %v (%s)", res.Status, res.Explain)
	}
	if !Eval(f, res.IntModel, res.BoolModel) {
		t.Fatalf("model %v %v does not satisfy %s", res.IntModel, res.BoolModel, f)
	}
}
