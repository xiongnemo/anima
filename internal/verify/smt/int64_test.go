package smt

import (
	"math"
	"math/big"
	"math/rand"
	"testing"
)

func TestCheckedArithmeticMatchesBigInt(t *testing.T) {
	// Coefficients use a symmetric range, so every one of them can be negated; constants use
	// all of int64, because MinInt64 is a value a program can compute.
	fits := func(z *big.Int) bool {
		return z.IsInt64() && z.Int64() != math.MinInt64
	}
	exact := func(name string, a, b int64, got int64, ok bool, want *big.Int) {
		t.Helper()
		if ok != want.IsInt64() || (ok && got != want.Int64()) {
			t.Fatalf("%s(%d, %d) = %d, %v; exact %s", name, a, b, got, ok, want)
		}
	}
	edges := []int64{0, 1, -1, 2, -2, 3, math.MaxInt64, math.MinInt64, math.MaxInt64 - 1, math.MinInt64 + 1,
		1 << 31, -(1 << 31), 1 << 32, -(1 << 32), 1 << 62, -(1 << 62), 3037000499, 3037000500, -3037000500}
	rng := rand.New(rand.NewSource(1))
	pick := func() int64 {
		switch rng.Intn(3) {
		case 0:
			return edges[rng.Intn(len(edges))]
		case 1:
			return rng.Int63n(1<<33) - 1<<32
		}
		return int64(rng.Uint64())
	}
	for i := 0; i < 200_000; i++ {
		a, b := pick(), pick()
		sum := new(big.Int).Add(big.NewInt(a), big.NewInt(b))
		if got, ok := addChecked(a, b); ok != fits(sum) || (ok && got != sum.Int64()) {
			t.Fatalf("addChecked(%d, %d) = %d, %v; exact %s", a, b, got, ok, sum)
		}
		prod := new(big.Int).Mul(big.NewInt(a), big.NewInt(b))
		if got, ok := mulChecked(a, b); ok != fits(prod) || (ok && got != prod.Int64()) {
			t.Fatalf("mulChecked(%d, %d) = %d, %v; exact %s", a, b, got, ok, prod)
		}
		got, ok := addExact(a, b)
		exact("addExact", a, b, got, ok, sum)
		got, ok = subExact(a, b)
		exact("subExact", a, b, got, ok, new(big.Int).Sub(big.NewInt(a), big.NewInt(b)))
		got, ok = mulExact(a, b)
		exact("mulExact", a, b, got, ok, prod)
	}
}

// MinInt64 is an int64 like any other: a term may hold it, and only negating it overflows.
func TestMinInt64IsRepresentable(t *testing.T) {
	lowest := Const(-math.MaxInt64).Sub(Const(1))
	terms := []struct {
		name string
		term LinearTerm
		want int64
		over bool
	}{
		{"-Max - 1", lowest, math.MinInt64, false},
		{"Min + 0", Const(math.MinInt64).Add(Const(0)), math.MinInt64, false},
		{"Min * 1", Const(math.MinInt64).Scale(1), math.MinInt64, false},
		{"-2^62 * 2", Const(-(1 << 62)).Scale(2), math.MinInt64, false},
		{"-1 - Min", Const(-1).Sub(Const(math.MinInt64)), math.MaxInt64, false},
		{"Min - Min", Const(math.MinInt64).Sub(Const(math.MinInt64)), 0, false},
		{"-Min", Const(math.MinInt64).Scale(-1), 0, true},
		{"0 - Min", Const(0).Sub(Const(math.MinInt64)), 0, true},
		{"Min - 1", lowest.Sub(Const(1)), 0, true},
		{"Min + -1", lowest.Add(Const(-1)), 0, true},
		{"Min * 2", lowest.Scale(2), 0, true},
	}
	for _, tc := range terms {
		if tc.term.Overflow != tc.over || (!tc.over && tc.term.Const != tc.want) {
			t.Errorf("%s: const %d overflow %v, want %d overflow %v", tc.name, tc.term.Const, tc.term.Overflow, tc.want, tc.over)
		}
	}

	x := Var("x")
	formulas := []struct {
		name string
		f    BoolExpr
		want ResultStatus
	}{
		{"Min fits", Not(FitsInt64(lowest)), StatusUnsat},
		{"-Min does not fit", FitsInt64(lowest.Scale(-1)), StatusUnsat},
		{"Min - 1 does not fit", FitsInt64(lowest.Sub(Const(1))), StatusUnsat},
		{"Min <= Min", Not(Le(lowest, lowest)), StatusUnsat},
		{"Max <= Min is false", Le(Const(math.MaxInt64), lowest), StatusUnsat},
		{"Max < Min is false", Lt(Const(math.MaxInt64), lowest), StatusUnsat},
		{"Min < Max", Not(Lt(lowest, Const(math.MaxInt64))), StatusUnsat},
		{"x <= Min is reachable", And(FitsInt64(x), Le(x, lowest)), StatusSat},
		{"x <= Min pins x", And(FitsInt64(x), Le(x, lowest), Neq(x, lowest)), StatusUnsat},
		{"x < Min is not", And(FitsInt64(x), Lt(x, lowest)), StatusUnsat},
		{"x >= Min is all of int64", And(FitsInt64(x), Not(Ge(x, lowest))), StatusUnsat},
		{"x > Max is not", And(FitsInt64(x), Gt(x, Const(math.MaxInt64))), StatusUnsat},
		{"x + Max <= Min is not", And(FitsInt64(x), Le(x.Add(Const(math.MaxInt64)), lowest)), StatusUnsat},
		{"x - Max <= Min implies x <= -1", And(Le(x.Sub(Const(math.MaxInt64)), lowest), Gt(x, Const(-1))), StatusUnsat},
		{"x <= -1 implies x - Max <= Min", And(Le(x, Const(-1)), Not(Le(x.Sub(Const(math.MaxInt64)), lowest))), StatusUnsat},
		{"Min - x <= Max is all of int64", And(FitsInt64(x), Not(Le(lowest.Sub(x), Const(math.MaxInt64)))), StatusUnsat},
		{"x + Min <= Max is all of int64", And(FitsInt64(x), Not(Le(x.Add(lowest), Const(math.MaxInt64)))), StatusUnsat},
		{"x + Min fits for x >= 0", And(Ge(x, Const(0)), FitsInt64(x), Not(FitsInt64(x.Add(lowest)))), StatusUnsat},
		{"x + Min overflows for x < 0", And(Lt(x, Const(0)), FitsInt64(x), FitsInt64(x.Add(lowest))), StatusUnsat},
		{"x - Min overflows for x >= 0", And(Ge(x, Const(0)), FitsInt64(x), FitsInt64(x.Sub(lowest))), StatusUnsat},
	}
	for _, tc := range formulas {
		t.Run(tc.name, func(t *testing.T) {
			res := CheckSat(And(Int64Pins(), tc.f))
			if res.Status != tc.want {
				t.Fatalf("status %v, want %v (%s) model=%v", res.Status, tc.want, res.Explain, res.IntModel)
			}
			if tc.want == StatusSat && res.IntModel["x"] != math.MinInt64 {
				t.Fatalf("model x = %d, want MinInt64", res.IntModel["x"])
			}
		})
	}
}

func TestLinearTermOverflowIsStickyAndNeverProves(t *testing.T) {
	x := Var("x")
	big := x.Scale(math.MaxInt64).Scale(2)
	if !big.Overflow {
		t.Fatal("coefficient overflow not flagged")
	}
	if !big.Add(Const(1)).Sub(x).Scale(0).Overflow {
		t.Fatal("overflow flag lost")
	}
	if !Const(math.MaxInt64).Add(Const(1)).Overflow {
		t.Fatal("constant overflow not flagged")
	}
	// A comparison on an overflowed term must be provable neither way.
	for _, f := range []BoolExpr{Le(big, Const(0)), Not(Le(big, Const(0))), Eq(big, x), Not(Eq(big, x))} {
		if res := CheckSat(f); res.Status == StatusUnsat {
			t.Fatalf("%s reported UNSAT", f)
		}
	}
	if res := CheckSat(Not(FitsInt64(big))); res.Status == StatusUnsat {
		t.Fatal("an overflowed term was proved to fit in 64 bits")
	}
}

func TestFitsInt64IsExactAtBothEnds(t *testing.T) {
	x, y := Var("x"), Var("y")
	hi := Const(math.MaxInt64)
	lo := Const(-math.MaxInt64) // x >= lo - 1 is how MinInt64 is reached below
	cases := []struct {
		name string
		f    BoolExpr
		want ResultStatus
	}{
		{"x = Max fits", And(Eq(x, hi), Not(FitsInt64(x))), StatusUnsat},
		{"x = Max, x + 1 does not fit", And(Eq(x, hi), FitsInt64(x.Add(Const(1)))), StatusUnsat},
		{"x = Max - 1, x + 1 fits", And(Eq(x, hi.Sub(Const(1))), Not(FitsInt64(x.Add(Const(1))))), StatusUnsat},
		{"x = -Max, x - 1 fits (MinInt64)", And(Eq(x, lo), Not(FitsInt64(x.Sub(Const(1))))), StatusUnsat},
		{"x = -Max, x - 2 does not fit", And(Eq(x, lo), FitsInt64(x.Sub(Const(2)))), StatusUnsat},
		{"x = -Max, -x fits", And(Eq(x, lo), Not(FitsInt64(x.Scale(-1)))), StatusUnsat},
		{"x fits, x - 1 fits, -(x - 1) may not", And(FitsInt64(x), FitsInt64(x.Sub(Const(1))), Le(x, lo), Not(FitsInt64(x.Sub(Const(1)).Scale(-1)))), StatusSat},
		{"x fits does not make -x fit", And(FitsInt64(x), Not(FitsInt64(x.Scale(-1)))), StatusSat},
		{"x fits does not make x + 1 fit", And(FitsInt64(x), Not(FitsInt64(x.Add(Const(1))))), StatusSat},
		{"x fits does not make x - 1 fit", And(FitsInt64(x), Not(FitsInt64(x.Sub(Const(1))))), StatusSat},
		{"x, y fit does not make x + y fit", And(FitsInt64(x), FitsInt64(y), Not(FitsInt64(x.Add(y)))), StatusSat},
		{"x, y fit does not make x - y fit", And(FitsInt64(x), FitsInt64(y), Not(FitsInt64(x.Sub(y)))), StatusSat},
		{"halves add up", And(
			Ge(x, Const(-(1<<62))), Le(x, Const(1<<62-1)), Ge(y, Const(-(1<<62))), Le(y, Const(1<<62)),
			Not(FitsInt64(x.Add(y)))), StatusUnsat},
		{"halves plus one overflow", And(
			Ge(x, Const(0)), Le(x, Const(1<<62)), Ge(y, Const(0)), Le(y, Const(1<<62)),
			Not(FitsInt64(x.Add(y)))), StatusSat},
		{"4e9 * x for x <= 2305843009 fits", And(
			Ge(x, Const(0)), Le(x, Const(2305843009)), Not(FitsInt64(x.Scale(4_000_000_000)))), StatusUnsat},
		{"4e9 * x for x <= 2305843010 overflows", And(
			Ge(x, Const(0)), Le(x, Const(2305843010)), Not(FitsInt64(x.Scale(4_000_000_000)))), StatusSat},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			res := CheckSat(And(Int64Pins(), tc.f))
			if res.Status != tc.want {
				t.Fatalf("status %v, want %v (%s) model=%v", res.Status, tc.want, res.Explain, res.IntModel)
			}
		})
	}
}

// Leaving the pins out frees the helper variable, which relaxes the query: more formulas
// become satisfiable, so nothing extra can be proved.
func TestFitsInt64WithoutPinsIsARelaxation(t *testing.T) {
	x, y := Var("x"), Var("y")
	lo := Const(-math.MaxInt64)
	f := And(Eq(x, lo), Eq(y, lo), FitsInt64(x.Add(y)))
	if res := CheckSat(And(Int64Pins(), f)); res.Status != StatusUnsat {
		t.Fatalf("pinned: status %v, want UNSAT", res.Status)
	}
	if res := CheckSat(f); res.Status != StatusSat {
		t.Fatalf("unpinned: status %v, want SAT", res.Status)
	}
}

func TestAtomEvalDoesNotWrap(t *testing.T) {
	a := LinearAtom{Coeffs: map[string]int64{"x": 4_000_000_000}, Bound: 0}
	if a.Eval(map[string]int64{"x": 4_000_000_000}) {
		t.Fatal("4e9 * 4e9 <= 0 evaluated true")
	}
}

func TestMulIntervalOverflowIsUnbounded(t *testing.T) {
	iv := MulInterval(Interval{HasLo: true, HasHi: true, Lo: 0, Hi: 4_000_000_000}, Interval{HasLo: true, HasHi: true, Lo: 0, Hi: 4_000_000_000})
	if iv.HasLo || iv.HasHi {
		t.Fatalf("overflowing product got bounds %+v", iv)
	}
	iv = MulInterval(Interval{HasLo: true, HasHi: true, Lo: -3, Hi: 2}, Interval{HasLo: true, HasHi: true, Lo: -5, Hi: 7})
	if !iv.HasLo || !iv.HasHi || iv.Lo != -21 || iv.Hi != 15 {
		t.Fatalf("got %+v", iv)
	}
}

func TestRatFloor(t *testing.T) {
	for _, tc := range []struct{ n, d, want int64 }{{7, 2, 3}, {-7, 2, -4}, {-1, 3, -1}, {6, 3, 2}, {-6, 3, -2}, {0, 5, 0}} {
		if got, ok := ratFloor(big.NewRat(tc.n, tc.d)); !ok || got != tc.want {
			t.Fatalf("floor(%d/%d) = %d, %v; want %d", tc.n, tc.d, got, ok, tc.want)
		}
	}
	huge := new(big.Rat).SetInt(new(big.Int).Lsh(big.NewInt(1), 70))
	if _, ok := ratFloor(huge); ok {
		t.Fatal("2^70 reported as fitting")
	}
}
