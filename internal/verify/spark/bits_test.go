package spark

import (
	"fmt"
	"math"
	"math/big"
	"math/rand"
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/verify/smt"
)

// What the kernel proves of the operators on the bits of an int: the ranges
// a packet parser needs, and no more than is true.
func TestBitOperatorsProved(t *testing.T) {
	src := `
def be16(hi: int[0..255], lo: int[0..255]) -> int[0..65535]:
    return hi << 8 | lo

def low(x: int) -> int[0..255]:
    return x & 0xFF

def high(x: int[0..65535]) -> int[0..255]:
    return x >> 8

def nibble(x: int, n: int[0..15]) -> int[0..15]:
    return (x >> (n * 4)) & 0xF

def flip(x: int[0..255]) -> int[0..255]:
    return x ^ 0xFF

def turned(x: int[0..255]) -> int[-256..-1]:
    return ~x

def power(n: int[0..62]) -> int:
    return 1 << n

def spread(x: int[0..255], n: int[0..8]) -> int[0..65280]:
    return x << n

def halved(x: int) -> int:
    requires: x < 0
    ensures: result < 0 and result >= x
    return x >> 1

def exact(x: int[0..1000]) -> int:
    ensures: result * 4 <= x and x <= result * 4 + 3
    return x >> 2

def slot(xs: list[int], h: int) -> int:
    requires: len(xs) == 16
    return xs[h & 15]

def some(x: int, n: int[1..5]) -> int[-4611686018427387904..4611686018427387903]:
    return x >> n

def either(x: int[-8..5], n: int[0..3]) -> int[-8..5]:
    return x >> n

def below(x: int[-8..-2], n: int[0..3]) -> int[-8..-1]:
    return x >> n

def sign(x: int) -> int[-1..0]:
    return x >> 63

def least() -> int:
    return -1 << 63

def folded() -> int[3..3]:
    return 1 | 2 ^ 3 & 4 << 1 + 2

def greatest() -> int[9223372036854775807..9223372036854775807]:
    return ~(-9223372036854775807 - 1)

def least_again(x: int[9223372036854775807..9223372036854775807]) -> int[-1..-1]:
    return ~x + 9223372036854775807

entity Word:
    bits: int[0..64]
    v: int
    invariant: bits < 64 implies v >> bits == 0
    invariant: bits != 0 and v % bits == 0 or bits == 0
`
	if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
		t.Fatalf("not proved:\n%s", strings.Join(failed, "\n"))
	}
}

// A guard is not run, but the LTS kernel has to give it a value.
const monitorSrc = "machine Car:\n    state Off:\n        on enter -> Off\n\nmonitor Gate:\n    n: control int[0..3] = 0\n\n    state Open:\n        on enter when GUARD -> Open:\n            n = 0\n"

func TestBitOperatorsRefused(t *testing.T) {
	cases := []struct{ name, body, vc string }{
		{"a count that may be anything", "def f(x: int[0..9], n: int) -> int:\n    return x >> n\n", "def:f.shift_count"},
		{"a negative count", "def f(x: int[0..9], n: int[-1..3]) -> int:\n    return x << n\n", "def:f.shift_count"},
		{"a count of 64", "def f(x: int[0..9]) -> int:\n    return x >> 64\n", "def:f.shift_count"},
		{"a count in a condition", "def f(x: int[0..9], n: int) -> int:\n    if x >> n == 0:\n        return 1\n    return 0\n", "def:f.shift_count"},
		{"a count in a lambda", "def f(xs: list[int[0..9]], n: int) -> list[int]:\n    return xs |> map((q) => q >> n)\n", "shift_count"},
		{"bits shifted out", "def f(x: int) -> int:\n    return x << 3\n", "def:f.int64_overflow"},
		{"bits shifted out of a byte", "def f(x: int[0..255]) -> int:\n    return x << 56\n", "def:f.int64_overflow"},
		{"bits shifted out by a count in a range", "def f(x: int[0..9], n: int[0..63]) -> int:\n    return x << n\n", "def:f.int64_overflow"},
		{"a shift of anything by a count in a range", "def f(x: int, n: int[0..3]) -> int:\n    return x << n\n", "def:f.int64_overflow"},
		{"1 << 63 is not an int", "def f() -> int:\n    return 1 << 63\n", "def:f.int64_overflow"},
		{"or with a mask is not under it", "def f(x: int) -> int[0..255]:\n    return x | 0xFF\n", "def:f.return_range"},
		{"and with a mask reaches it", "def f(x: int) -> int[0..254]:\n    return x & 0xFF\n", "def:f.return_range"},
		{"and of two negatives", "def f(x: int[-9..-1], y: int[-9..-1]) -> int[-9..-1]:\n    return x & y\n", "def:f.return_range"},
		{"xor may be 0", "def f(x: int[1..9], y: int[1..9]) -> int:\n    return 10 / (x ^ y)\n", "def:f.div_nonzero"},
		{"xor of two negatives may be 0", "def f(x: int[-9..-1], y: int[-9..-1]) -> int:\n    return 10 / (x ^ y)\n", "def:f.div_nonzero"},
		{"xor of a negative and anything may be 0", "def f(x: int[-9..-1], y: int) -> int:\n    return 10 / (x ^ y)\n", "def:f.div_nonzero"},
		{"a shift by the least count of a range", "def f(x: int, n: int[1..5]) -> int[-4611686018427387904..288230376151711743]:\n    return x >> n\n", "def:f.return_range"},
		{"a negative shift by the least count of a range", "def f(x: int, n: int[1..5]) -> int[-288230376151711744..4611686018427387903]:\n    return x >> n\n", "def:f.return_range"},
		{"a negative number shifted by 0 is itself", "def f(x: int[-9..-1], n: int[0..3]) -> int:\n    return 10 / ((x >> n) - x)\n", "def:f.div_nonzero"},
		{"the low end of a range shifted by its least count", "def f(x: int[-8..5], n: int[0..3]) -> int[-1..5]:\n    return x >> n\n", "def:f.return_range"},
		{"the high end of a negative range shifted by its greatest count", "def f(x: int[-8..-2], n: int[0..3]) -> int[-8..-2]:\n    return x >> n\n", "def:f.return_range"},
		{"a negative number shifted right", "def f(x: int) -> int[0..255]:\n    return x >> 56\n", "def:f.return_range"},
		{"the turned bits of 0", "def f(x: int[0..9]) -> int[-9..-1]:\n    return ~x\n", "def:f.return_range"},
		{"a count in a monitor's guard", strings.Replace(monitorSrc, "GUARD", "1 >> (n - 1) == 0", 1), "monitor:Gate.shift_count"},
		{"a divisor in a monitor's guard", strings.Replace(monitorSrc, "GUARD", "6 / (n - 1) == 0", 1), "monitor:Gate.div_nonzero"},
		// json.decode runs an invariant on whatever fields the text holds.
		{"a count in an invariant", "entity P:\n    d: int[0..64]\n    invariant: 1 >> d == 0\n", "entity:P.shift_count"},
		{"a count of 64 in an invariant", "entity P:\n    d: int\n    invariant: d >> 64 == 0\n", "entity:P.shift_count"},
		{"a count an earlier invariant does not bound", "entity P:\n    d: int\n    invariant: d >= 0\n    invariant: 1 << d > 0\n", "entity:P.shift_count"},
		{"a divisor in an invariant", "entity P:\n    d: int[0..9]\n    invariant: (10 / d) * 0 == 0\n", "entity:P.div_nonzero"},
		{"a modulus in an invariant", "entity P:\n    d: int[0..9]\n    invariant: d == 0 or 10 % (d - 1) < 10\n", "entity:P.div_nonzero"},
	}
	for _, c := range cases {
		failed := strings.Join(failedVCs(verifySrc(t, c.body)), "\n")
		if !strings.Contains(failed, c.vc) {
			t.Errorf("%s: want %s to fail, got:\n%s", c.name, c.vc, failed)
		}
	}
}

func TestShiftRangesAgainstBigInts(t *testing.T) {
	edge := []int64{math.MinInt64, math.MinInt64 + 1, -1 << 62, -257, -2, -1, 0, 1, 2, 3, 255, 1 << 31, 1 << 62, math.MaxInt64}
	for _, x := range edge {
		for n := int64(0); n <= 63; n++ {
			want := new(big.Int).Lsh(big.NewInt(x), uint(n))
			got, ok := shlChecked(x, n)
			if ok != want.IsInt64() || (ok && got != want.Int64()) {
				t.Errorf("shlChecked(%d, %d) = %d, %v; the shift is %s", x, n, got, ok, want)
			}
		}
	}
	// The range of a shift holds every shift of its operands.
	rng := rand.New(rand.NewSource(1))
	for i := 0; i < 20000; i++ {
		a, b := edge[rng.Intn(len(edge))]>>uint(rng.Intn(64)), edge[rng.Intn(len(edge))]>>uint(rng.Intn(64))
		c, d := int64(rng.Intn(64)), int64(rng.Intn(64))
		xs := smt.Interval{HasLo: true, HasHi: true, Lo: min(a, b), Hi: max(a, b)}
		ns := smt.Interval{HasLo: true, HasHi: true, Lo: min(c, d), Hi: max(c, d)}
		iv, ok := shlInterval(xs, ns)
		x := within(rng, xs.Lo, xs.Hi)
		n := ns.Lo + int64(rng.Intn(int(ns.Hi-ns.Lo)+1))
		want := new(big.Int).Lsh(big.NewInt(x), uint(n))
		if !ok {
			continue
		}
		if !want.IsInt64() || want.Int64() < iv.Lo || want.Int64() > iv.Hi {
			t.Fatalf("shlInterval(%v, %v) = %v, but %d << %d is %s", xs, ns, iv, x, n, want)
		}
	}
	for _, c := range []struct{ in, want smt.Interval }{
		{smt.Interval{}, smt.Interval{HasLo: true, HasHi: true, Lo: 0, Hi: 63}},
		{smt.Interval{HasLo: true, HasHi: true, Lo: 2, Hi: 5}, smt.Interval{HasLo: true, HasHi: true, Lo: 2, Hi: 5}},
		{smt.Interval{HasLo: true, HasHi: true, Lo: -4, Hi: 99}, smt.Interval{HasLo: true, HasHi: true, Lo: 0, Hi: 63}},
		{smt.Interval{HasLo: true, HasHi: true, Lo: 70, Hi: 99}, smt.Interval{HasLo: true, HasHi: true, Lo: 63, Hi: 63}},
		{smt.Interval{HasLo: true, HasHi: true, Lo: -9, Hi: -1}, smt.Interval{HasLo: true, HasHi: true, Lo: 0, Hi: 0}},
	} {
		if got := shiftCounts(c.in); got != c.want {
			t.Errorf("shiftCounts(%v) = %v, want %v", c.in, got, c.want)
		}
	}
	for x, want := range map[int64]int64{0: 0, 1: 1, 2: 3, 3: 3, 4: 7, 255: 255, 256: 511, math.MaxInt64: math.MaxInt64} {
		if got := maskOf(x); got != want {
			t.Errorf("maskOf(%d) = %d, want %d", x, got, want)
		}
	}
}

// within is a number of lo..hi, a range that may be wider than an int64
// can count.
func within(rng *rand.Rand, lo, hi int64) int64 {
	span := new(big.Int).Sub(big.NewInt(hi), big.NewInt(lo))
	off := new(big.Int).Rand(rng, span.Add(span, big.NewInt(1)))
	return off.Add(off, big.NewInt(lo)).Int64()
}

// bitExpr is a random expression over a and b, with its value.
type bitExpr struct {
	text string
	eval func(a, b int64) (int64, bool)
}

func randomBitExpr(rng *rand.Rand, depth int) bitExpr {
	if depth == 0 || rng.Intn(4) == 0 {
		switch rng.Intn(3) {
		case 0:
			return bitExpr{"a", func(a, _ int64) (int64, bool) { return a, true }}
		case 1:
			return bitExpr{"b", func(_, b int64) (int64, bool) { return b, true }}
		}
		c := []int64{0, 1, 2, 3, 7, 8, 15, 16, 62, 63, 255, 256, 65535, -1, -2, -256}[rng.Intn(16)]
		return bitExpr{fmt.Sprintf("(%d)", c), func(_, _ int64) (int64, bool) { return c, true }}
	}
	if rng.Intn(8) == 0 {
		x := randomBitExpr(rng, depth-1)
		return bitExpr{"(~" + x.text + ")", func(a, b int64) (int64, bool) {
			v, ok := x.eval(a, b)
			return ^v, ok
		}}
	}
	op := []string{"&", "|", "^", "<<", ">>", "&", "|", "^", "<<", ">>", "+", "-"}[rng.Intn(12)]
	l, r := randomBitExpr(rng, depth-1), randomBitExpr(rng, depth-1)
	return bitExpr{"(" + l.text + " " + op + " " + r.text + ")", func(a, b int64) (int64, bool) {
		x, ok1 := l.eval(a, b)
		y, ok2 := r.eval(a, b)
		if !ok1 || !ok2 {
			return 0, false
		}
		var z *big.Int
		switch op {
		case "&":
			return x & y, true
		case "|":
			return x | y, true
		case "^":
			return x ^ y, true
		case "+":
			z = new(big.Int).Add(big.NewInt(x), big.NewInt(y))
		case "-":
			z = new(big.Int).Sub(big.NewInt(x), big.NewInt(y))
		default:
			if y < 0 || y > 63 {
				return 0, false
			}
			if op == ">>" {
				return x >> uint(y), true
			}
			z = new(big.Int).Lsh(big.NewInt(x), uint(y))
		}
		return z.Int64(), z.IsInt64()
	}}
}

// Whatever the kernel knows of an expression on bits, it does not rule out
// the value the expression has: for operands a0 and b0 of the parameters'
// ranges the divisor below is 0, so div_nonzero is not proved. Where the
// expression has no value for them (bits shifted out, a count that is no
// count), some condition of the function is not proved.
func TestBitFactsHoldForRandomOperands(t *testing.T) {
	rng := rand.New(rand.NewSource(20261122))
	value := func() int64 {
		v := []int64{0, 1, 2, 3, 7, 8, 15, 16, 63, 255, 256, 65535, 65536, 1<<31 - 1, 1 << 32, 1 << 62, math.MaxInt64}[rng.Intn(17)]
		if rng.Intn(2) == 0 {
			v = rng.Int63() >> uint(rng.Intn(63))
		}
		if rng.Intn(3) == 0 {
			v = ^v
		}
		return max(v, math.MinInt64+1)
	}
	type bound struct {
		ty     string
		lo, hi int64
	}
	param := func() bound {
		if rng.Intn(5) == 0 {
			return bound{"int", math.MinInt64 + 1, math.MaxInt64}
		}
		x, y := value(), value()
		if rng.Intn(3) == 0 {
			x, y = int64(rng.Intn(64)), int64(rng.Intn(64))
		}
		lo, hi := min(x, y), max(x, y)
		return bound{fmt.Sprintf("int[%d..%d]", lo, hi), lo, hi}
	}
	pick := func(p bound) int64 {
		switch rng.Intn(4) {
		case 0:
			return p.lo
		case 1:
			return p.hi
		}
		if p.ty == "int" {
			return value()
		}
		return within(rng, p.lo, p.hi)
	}
	const n = 240
	var src strings.Builder
	defined := make([]bool, n)
	desc := make([]string, n)
	for i := 0; i < n; i++ {
		e := randomBitExpr(rng, 1+rng.Intn(3))
		pa, pb := param(), param()
		a0, b0 := pick(pa), pick(pb)
		c0, ok := e.eval(a0, b0)
		defined[i] = ok
		desc[i] = fmt.Sprintf("f%d: %s with a=%d in %s, b=%d in %s is %d", i, e.text, a0, pa.ty, b0, pb.ty, c0)
		fmt.Fprintf(&src, "def f%d(a: %s, b: %s) -> int:\n", i, pa.ty, pb.ty)
		switch {
		case !defined[i]:
			fmt.Fprintf(&src, "    t = %s\n    return t\n\n", e.text)
			continue
		case rng.Intn(4) == 0:
			fmt.Fprintf(&src, "    requires: a == (%d) and b == (%d)\n", a0, b0)
		case rng.Intn(3) == 0:
			sgn := func(name string, v int64) string {
				if v >= 0 {
					return name + " >= 0"
				}
				return name + " < 0"
			}
			fmt.Fprintf(&src, "    requires: %s and %s\n", sgn("a", a0), sgn("b", b0))
		}
		// The least int is not written as a literal.
		known := fmt.Sprintf("(%d)", c0)
		if c0 == math.MinInt64 {
			known = "(-9223372036854775807 - 1)"
		}
		fmt.Fprintf(&src, "    t = %s\n    return 10 / (t - %s)\n\n", e.text, known)
	}
	rep := verifySrc(t, src.String())
	divisor := map[string]bool{}
	unproved := map[string]bool{}
	for _, vc := range rep.VCs {
		if vc.Status != VCProved {
			unproved[vc.Scope] = true
		} else if strings.HasSuffix(vc.Name, ".div_nonzero") {
			divisor[vc.Scope] = true
		}
	}
	for i := 0; i < n; i++ {
		scope := fmt.Sprintf("def:f%d", i)
		if defined[i] && divisor[scope] {
			t.Errorf("the kernel rules out the value of %s", desc[i])
		}
		if !defined[i] && !unproved[scope] {
			t.Errorf("the kernel proves all of a function whose expression has no value: %s", desc[i])
		}
	}
}
