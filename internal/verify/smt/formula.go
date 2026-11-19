package smt

import (
	"fmt"
	"math"
	"math/big"
	"sort"
	"strings"
	"sync/atomic"
)

// LinearTerm represents sum(Coeffs[v] * v) + Const.
// Overflow marks a term whose numbers could not be represented while it was built and are
// then meaningless: a coefficient outside [-MaxInt64, MaxInt64], kept symmetric so it can
// always be negated, or a constant outside [MinInt64, MaxInt64].
type LinearTerm struct {
	Coeffs   map[string]int64
	Const    int64
	Overflow bool
}

func addChecked(a, b int64) (int64, bool) {
	s := a + b
	if (a >= 0) == (b >= 0) && (s >= 0) != (a >= 0) {
		return 0, false
	}
	return s, s != math.MinInt64
}

func mulChecked(a, b int64) (int64, bool) {
	if a == 0 || b == 0 {
		return 0, true
	}
	if a == math.MinInt64 || b == math.MinInt64 {
		return 0, false
	}
	p := a * b
	if p/b != a {
		return 0, false
	}
	return p, p != math.MinInt64
}

// addExact, subExact and mulExact cover the full int64 range, MinInt64 included.
func addExact(a, b int64) (int64, bool) {
	s := a + b
	if (a >= 0) == (b >= 0) && (s >= 0) != (a >= 0) {
		return 0, false
	}
	return s, true
}

func subExact(a, b int64) (int64, bool) {
	d := a - b
	if (a >= 0) != (b >= 0) && (d >= 0) != (a >= 0) {
		return 0, false
	}
	return d, true
}

func mulExact(a, b int64) (int64, bool) {
	if a == 0 || b == 0 {
		return 0, true
	}
	if a == math.MinInt64 || b == math.MinInt64 {
		if a == 1 || b == 1 {
			return math.MinInt64, true
		}
		return 0, false
	}
	p := a * b
	if p/b != a {
		return 0, false
	}
	return p, true
}

var unknownAtomID atomic.Int64

// unknownAtom stands for a comparison the 64-bit representation cannot express.
// A fresh unconstrained variable can take either truth value, so nothing is proved from it.
func unknownAtom() BoolExpr {
	return BoolVar{Name: fmt.Sprintf("__ovf_%d", unknownAtomID.Add(1))}
}

func Var(name string) LinearTerm {
	return LinearTerm{Coeffs: map[string]int64{name: 1}}
}

func Const(v int64) LinearTerm {
	return LinearTerm{Coeffs: map[string]int64{}, Const: v}
}

func (t LinearTerm) Clone() LinearTerm {
	c := make(map[string]int64, len(t.Coeffs))
	for k, v := range t.Coeffs {
		if v != 0 {
			c[k] = v
		}
	}
	return LinearTerm{Coeffs: c, Const: t.Const, Overflow: t.Overflow}
}

func (t LinearTerm) Add(o LinearTerm) LinearTerm {
	res := t.Clone()
	var ok bool
	if res.Const, ok = addExact(res.Const, o.Const); !ok {
		res.Overflow = true
	}
	res.Overflow = res.Overflow || o.Overflow
	for k, v := range o.Coeffs {
		nv, ok := addChecked(res.Coeffs[k], v)
		if !ok {
			res.Overflow = true
		}
		if nv == 0 {
			delete(res.Coeffs, k)
		} else {
			res.Coeffs[k] = nv
		}
	}
	return res
}

func (t LinearTerm) Sub(o LinearTerm) LinearTerm {
	// The constants are subtracted directly: -o.Const is not an int64 when o.Const is MinInt64.
	res := LinearTerm{Coeffs: t.Coeffs, Overflow: t.Overflow}.Add(LinearTerm{Coeffs: o.Coeffs, Overflow: o.Overflow}.Scale(-1))
	var ok bool
	if res.Const, ok = subExact(t.Const, o.Const); !ok {
		res.Overflow = true
	}
	return res
}

func (t LinearTerm) Scale(k int64) LinearTerm {
	if k == 0 {
		return LinearTerm{Coeffs: map[string]int64{}, Overflow: t.Overflow}
	}
	res := LinearTerm{Coeffs: make(map[string]int64, len(t.Coeffs)), Overflow: t.Overflow}
	var ok bool
	if res.Const, ok = mulExact(t.Const, k); !ok {
		res.Overflow = true
	}
	for v, coef := range t.Coeffs {
		p, ok := mulChecked(coef, k)
		if !ok {
			res.Overflow = true
		}
		if p != 0 {
			res.Coeffs[v] = p
		}
	}
	return res
}

// int64Half names a solver variable that Int64Pins fixes at -2^62. An atom bound is itself
// an int64, so `t >= MinInt64` has no direct encoding once t carries a constant; writing
// MinInt64 as 2*int64Half does. '#' cannot occur in a program identifier.
const int64Half = "#int64_half"

// Int64Pins must be conjoined to any query that contains a FitsInt64 formula.
func Int64Pins() BoolExpr {
	h := map[string]int64{int64Half: 1}
	nh := map[string]int64{int64Half: -1}
	return And(
		AtomExpr{Atom: LinearAtom{Coeffs: h, Bound: -(1 << 62)}},
		AtomExpr{Atom: LinearAtom{Coeffs: nh, Bound: 1 << 62}},
	)
}

// StripInt64Pins removes the helper variable from a model.
func StripInt64Pins(model map[string]int64) {
	delete(model, int64Half)
}

// FitsInt64 states MinInt64 <= t <= MaxInt64 exactly.
func FitsInt64(t LinearTerm) BoolExpr {
	if t.Overflow {
		return BoolConst{Val: false}
	}
	if len(t.Coeffs) == 0 {
		return BoolConst{Val: true}
	}
	pos := LinearTerm{Coeffs: t.Coeffs}.Clone()
	neg := pos.Scale(-1)
	if neg.Overflow {
		return BoolConst{Val: false}
	}
	c := t.Const
	var hi, lo LinearAtom
	if c >= 0 {
		// vars <= MaxInt64 - c
		hi = LinearAtom{Coeffs: pos.Coeffs, Bound: math.MaxInt64 - c}
	} else {
		// vars + c <= -2h - 1
		pos.Coeffs[int64Half] = 2
		hi = LinearAtom{Coeffs: pos.Coeffs, Bound: -1 - c}
	}
	if c < 0 {
		// -vars <= c - MinInt64
		lo = LinearAtom{Coeffs: neg.Coeffs, Bound: (c + 1) + math.MaxInt64}
	} else {
		// 2h <= vars + c
		neg.Coeffs[int64Half] = 2
		lo = LinearAtom{Coeffs: neg.Coeffs, Bound: c}
	}
	return And(AtomExpr{Atom: hi.Normalized()}, AtomExpr{Atom: lo.Normalized()})
}

func (t LinearTerm) String() string {
	var keys []string
	for k, v := range t.Coeffs {
		if v != 0 {
			keys = append(keys, k)
		}
	}
	sort.Strings(keys)
	var parts []string
	for _, k := range keys {
		c := t.Coeffs[k]
		if c == 1 {
			parts = append(parts, k)
		} else if c == -1 {
			parts = append(parts, "-"+k)
		} else {
			parts = append(parts, fmt.Sprintf("%d*%s", c, k))
		}
	}
	if t.Const != 0 || len(parts) == 0 {
		parts = append(parts, fmt.Sprintf("%d", t.Const))
	}
	return strings.Join(parts, " + ")
}

// LinearAtom represents sum(Coeffs[v] * v) <= Bound over Z.
type LinearAtom struct {
	Coeffs map[string]int64
	Bound  int64
}

func (a LinearAtom) Negate() LinearAtom {
	// !(sum <= Bound)  <==>  sum >= Bound + 1  <==>  -sum <= -Bound - 1
	neg := make(map[string]int64, len(a.Coeffs))
	for k, v := range a.Coeffs {
		if v != 0 {
			neg[k] = -v
		}
	}
	return LinearAtom{Coeffs: neg, Bound: -a.Bound - 1}
}

func (a LinearAtom) Normalized() LinearAtom {
	c := make(map[string]int64, len(a.Coeffs))
	var g int64
	for k, v := range a.Coeffs {
		if v != 0 {
			c[k] = v
			av := v
			if av < 0 {
				av = -av
			}
			g = gcd(g, av)
		}
	}
	b := a.Bound
	if g > 1 {
		for k, v := range c {
			c[k] = v / g
		}
		b = floorDiv(b, g)
	}
	return LinearAtom{Coeffs: c, Bound: b}
}

func (a LinearAtom) Key() string {
	var keys []string
	for k, v := range a.Coeffs {
		if v != 0 {
			keys = append(keys, k)
		}
	}
	sort.Strings(keys)
	var sb strings.Builder
	for _, k := range keys {
		fmt.Fprintf(&sb, "%d*%s+", a.Coeffs[k], k)
	}
	fmt.Fprintf(&sb, "<=%d", a.Bound)
	return sb.String()
}

func (a LinearAtom) String() string {
	lt := LinearTerm{Coeffs: a.Coeffs}
	return fmt.Sprintf("%s <= %d", lt.String(), a.Bound)
}

func (a LinearAtom) Eval(model map[string]int64) bool {
	sum := new(big.Int)
	for k, c := range a.Coeffs {
		sum.Add(sum, new(big.Int).Mul(big.NewInt(c), big.NewInt(model[k])))
	}
	return sum.Cmp(big.NewInt(a.Bound)) <= 0
}

func gcd(a, b int64) int64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func floorDiv(a, b int64) int64 {
	q := a / b
	r := a % b
	if r != 0 && ((r < 0) != (b < 0)) {
		q--
	}
	return q
}

// BoolExpr is an SMT boolean formula.
type BoolExpr interface {
	isBoolExpr()
	String() string
}

type BoolConst struct{ Val bool }

func (BoolConst) isBoolExpr() {}
func (b BoolConst) String() string {
	if b.Val {
		return "true"
	}
	return "false"
}

type BoolVar struct{ Name string }

func (BoolVar) isBoolExpr()      {}
func (b BoolVar) String() string { return b.Name }

type AtomExpr struct{ Atom LinearAtom }

func (AtomExpr) isBoolExpr()      {}
func (a AtomExpr) String() string { return a.Atom.String() }

type NotExpr struct{ Inner BoolExpr }

func (NotExpr) isBoolExpr()      {}
func (n NotExpr) String() string { return fmt.Sprintf("(not %s)", n.Inner) }

type AndExpr struct{ Args []BoolExpr }

func (AndExpr) isBoolExpr() {}
func (a AndExpr) String() string {
	var s []string
	for _, x := range a.Args {
		s = append(s, x.String())
	}
	return "(" + strings.Join(s, " and ") + ")"
}

type OrExpr struct{ Args []BoolExpr }

func (OrExpr) isBoolExpr() {}
func (o OrExpr) String() string {
	var s []string
	for _, x := range o.Args {
		s = append(s, x.String())
	}
	return "(" + strings.Join(s, " or ") + ")"
}

// Helper constructors
func Le(a, b LinearTerm) BoolExpr { return less(a, b, false) }
func Lt(a, b LinearTerm) BoolExpr { return less(a, b, true) }

// less states a <= b, or a < b when strict, as vars(a) - vars(b) <= bound. The exact bound
// b.Const - a.Const (- 1) can leave int64 by up to 2^64; it is then moved back in range by
// 2^63, written 2*int64Half as in FitsInt64, so that comparisons against MinInt64 and
// MaxInt64 stay exact.
func less(a, b LinearTerm, strict bool) BoolExpr {
	vars := LinearTerm{Coeffs: a.Coeffs, Overflow: a.Overflow}.Sub(LinearTerm{Coeffs: b.Coeffs, Overflow: b.Overflow})
	if vars.Overflow {
		return unknownAtom()
	}
	if len(vars.Coeffs) == 0 {
		return BoolConst{Val: a.Const < b.Const || (!strict && a.Const == b.Const)}
	}
	bound := new(big.Int).Sub(big.NewInt(b.Const), big.NewInt(a.Const))
	if strict {
		bound.Sub(bound, big.NewInt(1))
	}
	if !bound.IsInt64() {
		// 2*int64Half is -2^63: vars <= bound <==> vars + sign*2*int64Half <= bound - sign*2^63.
		sign := int64(bound.Sign())
		if _, used := vars.Coeffs[int64Half]; used {
			return unknownAtom()
		}
		vars.Coeffs[int64Half] = 2 * sign
		bound.Add(bound, new(big.Int).Lsh(big.NewInt(-sign), 63))
		if !bound.IsInt64() {
			return unknownAtom()
		}
	}
	return AtomExpr{Atom: LinearAtom{Coeffs: vars.Coeffs, Bound: bound.Int64()}.Normalized()}
}

func Ge(a, b LinearTerm) BoolExpr { return Le(b, a) }
func Gt(a, b LinearTerm) BoolExpr { return Lt(b, a) }

func Eq(a, b LinearTerm) BoolExpr {
	return And(Le(a, b), Le(b, a))
}

func Neq(a, b LinearTerm) BoolExpr {
	return Or(Lt(a, b), Lt(b, a))
}

func Not(x BoolExpr) BoolExpr {
	if bc, ok := x.(BoolConst); ok {
		return BoolConst{Val: !bc.Val}
	}
	if nx, ok := x.(NotExpr); ok {
		return nx.Inner
	}
	return NotExpr{Inner: x}
}

func And(xs ...BoolExpr) BoolExpr {
	var flat []BoolExpr
	for _, x := range xs {
		if x == nil {
			continue
		}
		if bc, ok := x.(BoolConst); ok {
			if !bc.Val {
				return BoolConst{Val: false}
			}
			continue
		}
		if ax, ok := x.(AndExpr); ok {
			flat = append(flat, ax.Args...)
		} else {
			flat = append(flat, x)
		}
	}
	if len(flat) == 0 {
		return BoolConst{Val: true}
	}
	if len(flat) == 1 {
		return flat[0]
	}
	return AndExpr{Args: flat}
}

func Or(xs ...BoolExpr) BoolExpr {
	var flat []BoolExpr
	for _, x := range xs {
		if x == nil {
			continue
		}
		if bc, ok := x.(BoolConst); ok {
			if bc.Val {
				return BoolConst{Val: true}
			}
			continue
		}
		if ox, ok := x.(OrExpr); ok {
			flat = append(flat, ox.Args...)
		} else {
			flat = append(flat, x)
		}
	}
	if len(flat) == 0 {
		return BoolConst{Val: false}
	}
	if len(flat) == 1 {
		return flat[0]
	}
	return OrExpr{Args: flat}
}

func Implies(a, b BoolExpr) BoolExpr {
	return Or(Not(a), b)
}

// Eval evaluates a BoolExpr under a variable model (ints + bools).
func Eval(e BoolExpr, intModel map[string]int64, boolModel map[string]bool) bool {
	switch x := e.(type) {
	case BoolConst:
		return x.Val
	case BoolVar:
		return boolModel[x.Name]
	case AtomExpr:
		return x.Atom.Eval(intModel)
	case NotExpr:
		return !Eval(x.Inner, intModel, boolModel)
	case AndExpr:
		for _, a := range x.Args {
			if !Eval(a, intModel, boolModel) {
				return false
			}
		}
		return true
	case OrExpr:
		for _, a := range x.Args {
			if Eval(a, intModel, boolModel) {
				return true
			}
		}
		return false
	}
	return false
}
