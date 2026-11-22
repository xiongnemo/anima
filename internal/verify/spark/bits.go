package spark

import (
	"math"
	"math/bits"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/verify/smt"
)

func isShift(op string) bool { return op == "<<" || op == ">>" }

func isBitOp(op string) bool {
	switch op {
	case "&", "|", "^", "<<", ">>":
		return true
	}
	return false
}

// proveShiftCount proves that a shift moves the bits by 0 to 63 places: the
// VM and the native backend stop the program on any other count.
func (v *verifier) proveShiftCount(e *ast.BinaryExpr, count smt.LinearTerm, env *symEnv, scope string) {
	v.prove(scope+".shift_count", scope, v.arithSpan(e), env,
		smt.And(smt.Ge(count, smt.Const(0)), smt.Le(count, smt.Const(63))))
}

// shiftUnbounded explains why nothing bounds x << n, or returns "" when
// evalBits has a value or a range for it. A shift by a constant count is a
// product and needs no range.
func (v *verifier) shiftUnbounded(e *ast.BinaryExpr, env *symEnv, scope string) string {
	probe := env.clone()
	l := v.evalInt(e.Left, probe, scope, false)
	r := v.evalInt(e.Right, probe, scope, false)
	if len(r.Coeffs) == 0 && !r.Overflow && r.Const >= 0 && r.Const <= 62 {
		return ""
	}
	il := v.termInterval(l, probe)
	if !il.HasLo || !il.HasHi {
		return "cannot bound a shift by a count that is not a constant; give the shifted operand a bounded type or a requires range"
	}
	if _, ok := shlInterval(il, shiftCounts(v.termInterval(r, probe))); !ok {
		return "the operand ranges allow a shift beyond 64 bits; narrow them"
	}
	return ""
}

// shiftCounts is the range of a count the runtime accepts: what is known
// of the count, inside 0..63.
func shiftCounts(iv smt.Interval) smt.Interval {
	out := smt.Interval{HasLo: true, HasHi: true, Lo: 0, Hi: 63}
	if iv.HasLo && iv.Lo > 0 {
		out.Lo = min(iv.Lo, 63)
	}
	if iv.HasHi && iv.Hi < 63 {
		out.Hi = max(iv.Hi, 0)
	}
	if out.Lo > out.Hi {
		// No count of the range is accepted: nothing is said of the result.
		out.Lo, out.Hi = 0, 63
	}
	return out
}

// shlChecked is x * 2^n, when that is an int64.
func shlChecked(x, n int64) (int64, bool) {
	if x == 0 {
		return 0, true
	}
	if n == 63 {
		return math.MinInt64, x == -1
	}
	p := int64(1) << uint(n)
	if x > math.MaxInt64/p || x < math.MinInt64/p {
		return 0, false
	}
	return x * p, true
}

// shlInterval is the range of x << n for x in a and n in counts, when
// every such shift is an int64.
func shlInterval(a, counts smt.Interval) (smt.Interval, bool) {
	out := smt.Interval{HasLo: true, HasHi: true}
	first := true
	for _, x := range []int64{a.Lo, a.Hi} {
		for _, n := range []int64{counts.Lo, counts.Hi} {
			p, ok := shlChecked(x, n)
			if !ok {
				return smt.Interval{}, false
			}
			if first || p < out.Lo {
				out.Lo = p
			}
			if first || p > out.Hi {
				out.Hi = p
			}
			first = false
		}
	}
	return out, true
}

// maskOf is the least 2^k - 1 that is at least x, for x >= 0: no bit of a
// number in 0..x is above it.
func maskOf(x int64) int64 {
	if x <= 0 {
		return 0
	}
	return int64(uint64(1)<<uint(bits.Len64(uint64(x))) - 1)
}

// evalBits is the value of an operator on the bits of l and r. Only a
// shift by a constant and ~ are linear; of the others it says what follows
// from the signs and the ranges of the operands, and no more.
func (v *verifier) evalBits(e *ast.BinaryExpr, l, r smt.LinearTerm, env *symEnv) smt.LinearTerm {
	lConst, rConst := len(l.Coeffs) == 0 && !l.Overflow, len(r.Coeffs) == 0 && !r.Overflow
	if lConst && rConst {
		switch e.Op {
		case "&":
			return smt.Const(l.Const & r.Const)
		case "|":
			return smt.Const(l.Const | r.Const)
		case "^":
			return smt.Const(l.Const ^ r.Const)
		}
	}
	if isShift(e.Op) {
		return v.evalShift(e, l, r, rConst, env)
	}

	t := smt.Var(env.freshVar("bits"))
	// Every operand is an int64, and so is what is made of their bits.
	env.assume(smt.FitsInt64(t))
	zero := smt.Const(0)
	sign := func(x smt.LinearTerm) (nonNeg, neg bool) {
		if x.Overflow {
			return false, false
		}
		if v.holds(env, smt.Ge(x, zero)) {
			return true, false
		}
		return false, v.holds(env, smt.Lt(x, zero))
	}
	lPos, lNeg := sign(l)
	rPos, rNeg := sign(r)
	// The bits of two numbers that are not negative lie under the mask of
	// the larger one.
	underMask := func() {
		il, ir := v.termInterval(l, env), v.termInterval(r, env)
		if il.HasHi && ir.HasHi {
			env.assume(smt.Le(t, smt.Const(maskOf(max(il.Hi, ir.Hi)))))
		}
	}
	switch e.Op {
	case "&":
		// Only the bits of both are left: a side that is not negative
		// bounds the result, whatever the other is.
		if lPos {
			env.assume(smt.Ge(t, zero))
			env.assume(smt.Le(t, l))
		}
		if rPos {
			env.assume(smt.Ge(t, zero))
			env.assume(smt.Le(t, r))
		}
		if lNeg && rNeg {
			env.assume(smt.Lt(t, zero))
			env.assume(smt.Le(t, l))
			env.assume(smt.Le(t, r))
		}
	case "|":
		switch {
		case lPos && rPos:
			env.assume(smt.Ge(t, l))
			env.assume(smt.Ge(t, r))
			if sum := l.Add(r); !sum.Overflow {
				env.assume(smt.Le(t, sum))
			}
			underMask()
		default:
			// A negative side keeps its sign and all its bits.
			if lNeg {
				env.assume(smt.Lt(t, zero))
				env.assume(smt.Ge(t, l))
			}
			if rNeg {
				env.assume(smt.Lt(t, zero))
				env.assume(smt.Ge(t, r))
			}
		}
	case "^":
		switch {
		case lPos && rPos:
			env.assume(smt.Ge(t, zero))
			if sum := l.Add(r); !sum.Overflow {
				env.assume(smt.Le(t, sum))
			}
			if d := l.Sub(r); !d.Overflow {
				env.assume(smt.Ge(t, d))
				env.assume(smt.Ge(t, d.Scale(-1)))
			}
			underMask()
		case lNeg && rNeg:
			env.assume(smt.Ge(t, zero))
		case (lNeg && rPos) || (lPos && rNeg):
			env.assume(smt.Lt(t, zero))
		}
	}
	return t
}

func (v *verifier) evalShift(e *ast.BinaryExpr, l, r smt.LinearTerm, rConst bool, env *symEnv) smt.LinearTerm {
	zero := smt.Const(0)
	if rConst && r.Const >= 0 && r.Const <= 62 {
		pow := int64(1) << uint(r.Const)
		if e.Op == "<<" {
			// x << n is x * 2^n: checkArith proves that it is an int64.
			return l.Scale(pow)
		}
		// x >> n is the floor of x / 2^n, for a negative x too.
		t := smt.Var(env.freshVar("shr"))
		env.assume(smt.FitsInt64(t))
		if low := t.Scale(pow); !low.Overflow && !l.Overflow {
			env.assume(smt.Le(low, l))
			if high := low.Add(smt.Const(pow - 1)); !high.Overflow {
				env.assume(smt.Le(l, high))
			}
		}
		return t
	}
	t := smt.Var(env.freshVar("shift"))
	if l.Overflow {
		return t
	}
	il := v.termInterval(l, env)
	counts := shiftCounts(v.termInterval(r, env))
	if e.Op == ">>" {
		// Whatever is shifted, the count leaves that many bits fewer.
		env.assume(smt.Ge(t, smt.Const(math.MinInt64>>uint(counts.Lo))))
		env.assume(smt.Le(t, smt.Const(math.MaxInt64>>uint(counts.Lo))))
		// The result lies between x and 0, or -1 for a negative x.
		if v.holds(env, smt.Ge(l, zero)) {
			env.assume(smt.Ge(t, zero))
			env.assume(smt.Le(t, l))
		} else if v.holds(env, smt.Lt(l, zero)) {
			env.assume(smt.Lt(t, zero))
			env.assume(smt.Ge(t, l))
		}
		// A shift keeps the order of what is shifted, and the count that
		// brings an end of the range furthest is the least or the greatest.
		lo, hi := uint(counts.Lo), uint(counts.Hi)
		if il.HasLo {
			env.assume(smt.Ge(t, smt.Const(min(il.Lo>>lo, il.Lo>>hi))))
		}
		if il.HasHi {
			env.assume(smt.Le(t, smt.Const(max(il.Hi>>lo, il.Hi>>hi))))
		}
		return t
	}
	// With no range t stays free, so nothing about the shift, not even that
	// it fits in 64 bits, can be proved.
	if il.HasLo && il.HasHi {
		if iv, ok := shlInterval(il, counts); ok {
			env.assume(smt.Ge(t, smt.Const(iv.Lo)))
			env.assume(smt.Le(t, smt.Const(iv.Hi)))
		}
	}
	return t
}
