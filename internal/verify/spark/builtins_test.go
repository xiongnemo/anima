package spark

import (
	"fmt"
	"math"
	"math/big"
	"math/rand"
	"os"
	"strconv"
	"strings"
	"testing"
)

// What the kernel knows of abs, min and max: the value, not only a range.
func TestAbsMinMaxProved(t *testing.T) {
	src := `
import std.time as time

def size(x: int[-100..100]) -> int[0..100]:
    ensures: result == x or result == 0 - x
    return abs(x)

def far(x: int) -> int:
    requires: x > -9223372036854775807 - 1
    ensures: result >= 0 and result >= x
    return abs(x)

def near(x: int) -> int[-2..2]:
    requires: x != -9223372036854775807 - 1
    if abs(x) < 3:
        return x
    return 0

def gap(a: int[0..1000], b: int[0..1000]) -> int[0..1000]:
    return abs(a - b)

def least(a: int, b: int) -> int:
    ensures: result <= a and result <= b
    ensures: result == a or result == b
    return min(a, b)

def greatest(a: int, b: int) -> int:
    ensures: result >= a and result >= b
    ensures: result == a or result == b
    return max(a, b)

def clamp(x: int) -> int[0..255]:
    return min(max(x, 0), 255)

def at(xs: list[int], i: int) -> int:
    requires: len(xs) > 0
    return xs[max(0, min(i, len(xs) - 1))]

def wait(a: int[0..1000], b: int[0..1000]) -> int:
    time.sleep_ms(max(a - b, 0))
    return 0

def area(a: int[-1000..1000], b: int[-1000..1000]) -> int[0..1000000]:
    return abs(a) * max(abs(b), 1)

def piped(x: int[-9..9]) -> int[0..9]:
    return x |> abs

def piped_at(xs: list[int], i: int) -> int:
    requires: len(xs) > 0
    return xs[i |> max(0) |> min(len(xs) - 1)]

def piped_wait(a: int[0..1000], b: int[0..1000]) -> int:
    time.sleep_ms(a - b |> max(0))
    return 10 / (a |> max(1))

def xs_len(xs: list[int]) -> int:
    ensures: result == len(xs)
    return xs |> len()

def part(a: int[-99..99], b: int[1..9]) -> int:
    return a / max(b, 3) + a / (abs(a) + 1) + a / min(0 - b, 0 - 1)

def same(a: int[-9..9]) -> int[0..0]:
    return abs(a) - max(a, 0 - a)

def of_consts() -> int[7..7]:
    return abs(0 - 3) + min(5, 2) + max(0 - 4, 2)

def greatest_int() -> int:
    return abs(-9223372036854775807)

def shifted(n: int) -> int:
    return 1 << min(max(n, 0), 62)

def shifted_by(n: int, k: int[0..62]) -> int:
    return 1 << min(max(n, 0), k)

def shifted_past(n: int, k: int[0..62]) -> int:
    return 1 << max(k, min(n, 62))

def shifted_back(n: int) -> int:
    return 1 << max(62 - max(n, 0), 0)

def of_three(n: int, i: int[0..20], j: int[0..20], k: int[0..20]) -> int:
    a = 1 << max(i + j + k, min(n, 62))
    b = 1 << min(max(n, 0), i + j + k)
    c = 1 << min(abs(i + j + k - 30), 62)
    return a - b - c

def scaled(a: int[5..10], b: int[-10..10], c: int[1..10]) -> int:
    return 10 / (max(a, b) * c) + 10 / (min(0 - a, b) * c)

entity Span:
    lo: int[-1000..1000]
    hi: int[-1000..1000]
    invariant: abs(hi - lo) <= 1000
    invariant: max(lo, hi) == hi

monitor Gate:
    n: control int[-3..3] = min(0, 1)

    state Open:
        invariant: abs(n) <= 3
        on up when abs(n + 1) <= 3 -> Open:
            n = min(n + 1, 3)
        on down when max(n, -2) == n -> Open:
            n = n - 1
`
	if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
		t.Fatalf("not proved:\n%s", strings.Join(failed, "\n"))
	}
}

// abs of the least int is the least int, on both backends, so abs(x) < 0
// held for it in a program the kernel had proved all of.
func TestAbsMinMaxRefused(t *testing.T) {
	cases := []struct{ name, body, vc string }{
		{"abs of anything", "def f(x: int) -> int:\n    return abs(x)\n", "def:f.int64_overflow"},
		{"abs of anything in a condition", "def f(x: int) -> int:\n    if abs(x) < 0:\n        return 1\n    return 0\n", "def:f.int64_overflow"},
		{"abs of the least int", "def f() -> int:\n    return abs(-9223372036854775807 - 1)\n", "def:f.int64_overflow"},
		{"abs of a difference", "def f(a: int, b: int[0..9]) -> int:\n    requires: a < 0\n    return abs(a + b)\n", "def:f.int64_overflow"},
		{"abs within abs", "def f(x: int) -> int:\n    return abs(abs(x))\n", "def:f.int64_overflow"},
		{"abs under min", "def f(x: int) -> int:\n    return min(abs(x), 3)\n", "def:f.int64_overflow"},
		{"abs after a pipe", "def f(x: int) -> int:\n    y = x |> abs()\n    if y < 0:\n        return 1\n    return 0\n", "def:f.int64_overflow"},
		{"abs after a pipe, by its name", "def f(x: int) -> int:\n    return x |> abs\n", "def:f.int64_overflow"},
		{"abs in the middle of a pipeline", "def f(x: int) -> int:\n    return x |> abs() |> min(5) |> max(-5)\n", "def:f.int64_overflow"},
		{"abs after a pipe in a lambda", "def f(xs: list[int]) -> list[int]:\n    return xs |> map((q) => (q |> abs()))\n", "int64_overflow"},
		{"max after a pipe may be 0", "def f(x: int) -> int:\n    return 100 / (x |> max(0))\n", "def:f.div_nonzero"},
		{"a divisor piped to a lambda", "def f() -> int:\n    g = (a) => 10 / a\n    return 0 |> g\n", "def:f.div_nonzero"},
		{"abs in a lambda", "def f(xs: list[int]) -> list[int]:\n    return xs |> map((q) => abs(q))\n", "int64_overflow"},
		{"abs in an invariant", "entity P:\n    d: int\n    invariant: abs(d) >= 0\n", "entity:P.int64_overflow"},
		{"abs in a monitor's guard", strings.Replace(monitorSrc, "GUARD", "abs(n - 9223372036854775807 - 1) > 0", 1), "monitor:Gate.int64_overflow"},
		{"an overflow under max", "def f(a: int, b: int) -> int:\n    return max(a + b, 0)\n", "def:f.int64_overflow"},
		{"a divisor under abs", "def f(a: int[0..9]) -> int:\n    return abs(10 / a)\n", "def:f.div_nonzero"},
		{"abs may be 0", "def f(a: int[-9..9]) -> int:\n    return 10 / abs(a)\n", "def:f.div_nonzero"},
		{"abs reaches the far end", "def f(a: int[-9..5]) -> int[0..8]:\n    return abs(a)\n", "def:f.return_range"},
		{"abs of a range away from 0", "def f(a: int[-9..-3]) -> int[4..9]:\n    return abs(a)\n", "def:f.return_range"},
		{"abs is not the number", "def f(a: int[-9..9]) -> int:\n    return 10 / (abs(a) - a + 1)\n", ""},
		{"abs may be the number", "def f(a: int[-9..9]) -> int:\n    return 10 / (abs(a) - a)\n", "def:f.div_nonzero"},
		{"abs may be the negation", "def f(a: int[-9..9]) -> int:\n    return 10 / (abs(a) + a)\n", "def:f.div_nonzero"},
		{"min may be either", "def f(a: int[0..9], b: int[0..9]) -> int:\n    return 10 / (min(a, b) - a)\n", "def:f.div_nonzero"},
		{"min may be the other", "def f(a: int[0..9], b: int[0..9]) -> int:\n    return 10 / (min(a, b) - b)\n", "def:f.div_nonzero"},
		{"max may be either", "def f(a: int[0..9], b: int[0..9]) -> int:\n    return 10 / (max(a, b) - a)\n", "def:f.div_nonzero"},
		{"max may be the other", "def f(a: int[0..9], b: int[0..9]) -> int:\n    return 10 / (max(a, b) - b)\n", "def:f.div_nonzero"},
		{"min reaches the low end", "def f(a: int[0..9], b: int[3..5]) -> int[1..5]:\n    return min(a, b)\n", "def:f.return_range"},
		{"min is not above either", "def f(a: int[0..9], b: int[3..5]) -> int[0..4]:\n    return min(a, b)\n", "def:f.return_range"},
		{"max reaches the high end", "def f(a: int[0..9], b: int[3..5]) -> int[3..8]:\n    return max(a, b)\n", "def:f.return_range"},
		{"max is not below either", "def f(a: int[0..9], b: int[3..5]) -> int[4..9]:\n    return max(a, b)\n", "def:f.return_range"},
		{"max of anything and 0 has no end", "def f(a: int) -> int[0..255]:\n    return max(a, 0)\n", "def:f.return_range"},
		{"min is not max", "def f(a: int, b: int) -> int:\n    ensures: result >= a\n    return min(a, b)\n", "f.ensures_1"},
		{"max is not min", "def f(a: int, b: int) -> int:\n    ensures: result <= a\n    return max(a, b)\n", "f.ensures_1"},
		{"an index under max alone", "def f(xs: list[int], i: int) -> int:\n    return xs[max(i, 0)]\n", "def:f.index_bounds"},
		{"the other end of a difference", "def f(n: int) -> int:\n    return 10 / abs(5 - max(n, 0))\n", "def:f.div_nonzero"},
		{"a count with no least value", "def f(n: int) -> int:\n    return 1 << min(62 - max(n, 0), 62)\n", "def:f.shift_count"},
		{"a product with one end", "def f(n: int, c: int[1..9]) -> int:\n    return max(n, 0) * c\n", "def:f.int64_overflow"},
		{"what is not written down has no abs", "def f(x: int) -> int:\n    ensures: abs(9223372036854775807 + 9223372036854775807 + x) <= 9223372036854775807\n    return 0\n", "f.ensures_1"},
		{"what is not written down has no min", "def f(x: int) -> int:\n    ensures: max(9223372036854775807 + 9223372036854775807 + x, 0) <= 9223372036854775807\n    return 0\n", "f.ensures_1"},
		{"a count under max alone", "def f(n: int) -> int:\n    return 1 << max(n, 0)\n", "def:f.shift_count"},
	}
	for _, c := range cases {
		failed := strings.Join(failedVCs(verifySrc(t, c.body)), "\n")
		if c.vc == "" {
			if failed != "" {
				t.Errorf("%s: not proved:\n%s", c.name, failed)
			}
			continue
		}
		if !strings.Contains(failed, c.vc) {
			t.Errorf("%s: want %s to fail, got:\n%s", c.name, c.vc, failed)
		}
	}
}

// numExpr is a random expression of abs, min, max, +, - and * over a and
// b, with its value where every part of it is an int64.
type numExpr struct {
	text string
	eval func(a, b *big.Int) *big.Int
}

func randomNumExpr(rng *rand.Rand, depth int) numExpr {
	if depth == 0 || rng.Intn(5) == 0 {
		switch rng.Intn(3) {
		case 0:
			return numExpr{"a", func(a, _ *big.Int) *big.Int { return a }}
		case 1:
			return numExpr{"b", func(_, b *big.Int) *big.Int { return b }}
		}
		c := []int64{0, 1, 2, 3, 7, 100, 255, -1, -2, -7, -256, math.MaxInt64, -math.MaxInt64}[rng.Intn(13)]
		return numExpr{fmt.Sprintf("(%d)", c), func(_, _ *big.Int) *big.Int { return big.NewInt(c) }}
	}
	fits := func(v *big.Int) *big.Int {
		if v == nil || !v.IsInt64() {
			return nil
		}
		return v
	}
	if rng.Intn(3) == 0 {
		x := randomNumExpr(rng, depth-1)
		return numExpr{"abs(" + x.text + ")", func(a, b *big.Int) *big.Int {
			v := x.eval(a, b)
			if v == nil {
				return nil
			}
			return fits(new(big.Int).Abs(v))
		}}
	}
	op := []string{"min", "max", "min", "max", "+", "-", "*"}[rng.Intn(7)]
	l, r := randomNumExpr(rng, depth-1), randomNumExpr(rng, depth-1)
	text := "(" + l.text + " " + op + " " + r.text + ")"
	if op == "min" || op == "max" {
		text = op + "(" + l.text + ", " + r.text + ")"
	}
	return numExpr{text, func(a, b *big.Int) *big.Int {
		x, y := l.eval(a, b), r.eval(a, b)
		if x == nil || y == nil {
			return nil
		}
		switch op {
		case "min":
			if x.Cmp(y) < 0 {
				return x
			}
			return y
		case "max":
			if x.Cmp(y) > 0 {
				return x
			}
			return y
		case "+":
			return fits(new(big.Int).Add(x, y))
		case "-":
			return fits(new(big.Int).Sub(x, y))
		}
		return fits(new(big.Int).Mul(x, y))
	}}
}

// The kernel never rules out a value an expression of abs, min and max
// takes, never proves all of one that has no value, and knows the value of
// one whose operands it knows.
func TestAbsMinMaxFactsHoldForRandomOperands(t *testing.T) {
	rng := rand.New(rand.NewSource(seedOf(20261123)))
	value := func() int64 {
		v := []int64{0, 1, 2, 3, 7, 100, 255, 256, 1 << 31, 1 << 62, math.MaxInt64}[rng.Intn(11)]
		if rng.Intn(2) == 0 {
			v = rng.Int63() >> uint(rng.Intn(63))
		}
		if rng.Intn(2) == 0 {
			v = -v
		}
		if rng.Intn(12) == 0 {
			v = math.MinInt64
		}
		return v
	}
	type bound struct {
		ty     string
		lo, hi int64
	}
	param := func() bound {
		if rng.Intn(5) == 0 {
			return bound{"int", math.MinInt64, math.MaxInt64}
		}
		x, y := value(), value()
		if rng.Intn(2) == 0 {
			x, y = int64(rng.Intn(41)-20), int64(rng.Intn(41)-20)
		}
		// The least int is not written, so no range starts at it.
		lo, hi := max(min(x, y), math.MinInt64+1), max(x, y, math.MinInt64+1)
		return bound{fmt.Sprintf("int[%d..%d]", lo, hi), lo, hi}
	}
	pick := func(p bound) int64 {
		switch rng.Intn(4) {
		case 0:
			return p.lo
		case 1:
			return p.hi
		}
		return within(rng, p.lo, p.hi)
	}
	// The least int is not written as a literal.
	lit := func(v int64) string {
		if v == math.MinInt64 {
			return "(-9223372036854775807 - 1)"
		}
		return fmt.Sprintf("(%d)", v)
	}
	n := countOf(300)
	var src strings.Builder
	defined := make([]bool, n)
	exact := make([]bool, n)
	desc := make([]string, n)
	for i := 0; i < n; i++ {
		e := randomNumExpr(rng, 1+rng.Intn(3))
		pa, pb := param(), param()
		a0, b0 := pick(pa), pick(pb)
		c0 := e.eval(big.NewInt(a0), big.NewInt(b0))
		defined[i] = c0 != nil
		desc[i] = fmt.Sprintf("f%d: %s with a=%d in %s, b=%d in %s is %v", i, e.text, a0, pa.ty, b0, pb.ty, c0)
		fmt.Fprintf(&src, "def f%d(a: %s, b: %s) -> int:\n", i, pa.ty, pb.ty)
		if !defined[i] {
			fmt.Fprintf(&src, "    t = %s\n    return t\n\n", e.text)
			continue
		}
		// A product of two operands is known only by its range, and a
		// sum whose constant part alone is no int64 is refused whatever
		// its value: 9223372036854775807 + (1 - b) with b == 11.
		exact[i] = rng.Intn(3) == 0 && !strings.Contains(e.text, "*") && !strings.Contains(e.text, "9223372036854775807")
		if exact[i] {
			fmt.Fprintf(&src, "    requires: a == %s and b == %s\n    ensures: result == %s\n    return %s\n\n", lit(a0), lit(b0), lit(c0.Int64()), e.text)
			continue
		}
		fmt.Fprintf(&src, "    t = %s\n    return 10 / (t - %s)\n\n", e.text, lit(c0.Int64()))
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
		switch {
		case !defined[i] && !unproved[scope]:
			t.Errorf("the kernel proves all of a function whose expression has no value: %s", desc[i])
		case defined[i] && exact[i] && unproved[scope]:
			t.Errorf("the kernel does not know the value of %s", desc[i])
		case defined[i] && !exact[i] && divisor[scope]:
			t.Errorf("the kernel rules out the value of %s", desc[i])
		}
	}
}

func seedOf(d int64) int64 {
	if v, err := strconv.ParseInt(os.Getenv("ANIMA_SEED"), 10, 64); err == nil {
		return v
	}
	return d
}

func countOf(d int) int {
	if v, err := strconv.Atoi(os.Getenv("ANIMA_COUNT")); err == nil {
		return v
	}
	return d
}
