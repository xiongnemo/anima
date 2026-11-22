package spark

import (
	"math"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/verify/smt"
)

// builtinCall reports whether e calls the built-in function name with n
// arguments by position. No function, entity or variable that is called has
// the name of a built-in one (sema), so the name says which function it is.
func builtinCall(e *ast.CallExpr, name string, n int) bool {
	id, ok := e.Callee.(*ast.Ident)
	if !ok || id.Name != name || len(e.Args) != n {
		return false
	}
	for _, a := range e.Args {
		if a.Name != "" {
			return false
		}
	}
	return true
}

// absOf is abs(x): x or -x, whichever is not negative. Where x is the least
// int, -x is no int64, and checkArith has the proof that it is not. Of the
// abs of a number that could not be written down nothing is known.
func (v *verifier) absOf(x smt.LinearTerm, env *symEnv) smt.LinearTerm {
	neg := x.Scale(-1)
	if x.Overflow || neg.Overflow {
		return smt.Var(env.freshVar("abs"))
	}
	if len(x.Coeffs) == 0 {
		if x.Const < 0 {
			return neg
		}
		return x
	}
	r := smt.Var(env.freshVar("abs"))
	env.assume(smt.Ge(r, x))
	env.assume(smt.Ge(r, neg))
	env.assume(smt.Or(smt.Eq(r, x), smt.Eq(r, neg)))
	// Its range, which a product or a shift of r is read from.
	iv := v.termSides(x, env)
	lo := int64(0)
	if iv.HasLo && iv.Lo > 0 {
		lo = iv.Lo
	} else if iv.HasHi && iv.Hi < 0 && iv.Hi > math.MinInt64 {
		lo = -iv.Hi
	}
	env.assume(smt.Ge(r, smt.Const(lo)))
	if iv.HasLo && iv.HasHi && iv.Lo > math.MinInt64 && iv.Hi > math.MinInt64 {
		env.assume(smt.Le(r, smt.Const(max(iv.Hi, -iv.Lo))))
	}
	return r
}

// leastOf is min(a, b), or max(a, b) when greatest: one of the two, and
// not above (not below) either.
func (v *verifier) leastOf(a, b smt.LinearTerm, greatest bool, env *symEnv) smt.LinearTerm {
	if a.Overflow || b.Overflow {
		return smt.Var(env.freshVar("minmax"))
	}
	if len(a.Coeffs) == 0 && len(b.Coeffs) == 0 {
		if (a.Const < b.Const) != greatest {
			return a
		}
		return b
	}
	name := "min"
	if greatest {
		name = "max"
	}
	r := smt.Var(env.freshVar(name))
	if greatest {
		env.assume(smt.Ge(r, a))
		env.assume(smt.Ge(r, b))
	} else {
		env.assume(smt.Le(r, a))
		env.assume(smt.Le(r, b))
	}
	env.assume(smt.Or(smt.Eq(r, a), smt.Eq(r, b)))
	// Its range, which a product or a shift of r is read from: the side
	// it is held to by either operand, and the other side by both.
	ia, ib := v.termSides(a, env), v.termSides(b, env)
	if greatest {
		if ia.HasLo {
			env.assume(smt.Ge(r, smt.Const(ia.Lo)))
		}
		if ib.HasLo {
			env.assume(smt.Ge(r, smt.Const(ib.Lo)))
		}
		if ia.HasHi && ib.HasHi {
			env.assume(smt.Le(r, smt.Const(max(ia.Hi, ib.Hi))))
		}
	} else {
		if ia.HasHi {
			env.assume(smt.Le(r, smt.Const(ia.Hi)))
		}
		if ib.HasHi {
			env.assume(smt.Le(r, smt.Const(ib.Hi)))
		}
		if ia.HasLo && ib.HasLo {
			env.assume(smt.Ge(r, smt.Const(min(ia.Lo, ib.Lo))))
		}
	}
	return r
}

// termSides is termInterval with each end found on its own: max(n, 0) has
// a least value where n has none.
func (v *verifier) termSides(t smt.LinearTerm, env *symEnv) smt.Interval {
	if t.Overflow {
		return smt.Interval{}
	}
	lo, hi := smt.Const(t.Const), smt.Const(t.Const)
	hasLo, hasHi := true, true
	var pathBounds map[string]smt.Interval
	for k, c := range t.Coeffs {
		iv := env.intervals[k]
		if !iv.HasLo || !iv.HasHi {
			if pathBounds == nil {
				_, _, pathBounds = smt.OctagonAnalyze(env.pathAtoms())
			}
			iv = iv.Intersect(pathBounds[k])
		}
		// The end of the variable each end of the term is read from.
		least, greatest := iv.HasLo, iv.HasHi
		a, b := smt.Const(iv.Lo).Scale(c), smt.Const(iv.Hi).Scale(c)
		if c < 0 {
			a, b = b, a
			least, greatest = greatest, least
		}
		hasLo, hasHi = hasLo && least, hasHi && greatest
		lo, hi = lo.Add(a), hi.Add(b)
	}
	res := smt.Interval{}
	if hasLo && !lo.Overflow {
		res.HasLo, res.Lo = true, lo.Const
	}
	if hasHi && !hi.Overflow {
		res.HasHi, res.Hi = true, hi.Const
	}
	return res
}
