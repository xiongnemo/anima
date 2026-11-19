package spark

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
)

func verifySrc(t *testing.T, src string) *Report {
	t.Helper()
	prog, err := parser.Parse("test.anm", src)
	if err != nil {
		t.Fatalf("parse failed: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema failed: %v", err)
	}
	return Verify(info)
}

func TestSPARKValidEscrowAndPipelineDivAndLoops(t *testing.T) {
	src := `
type Money = int[0..1_000_000]
type Score = int[0..100]
type FetchState = Fresh(score: Score) | Degraded

entity Account:
    balance: Money
    escrow: Money
    invariant: balance + escrow <= 1_000_000

entity UpstreamQuote:
    score: Score
    weight: int[1..10]
    invariant: score * weight <= 1000

def lock_funds(mut acc: Account, amt: int[1..10_000]) -> bool:
    requires: acc.balance + acc.escrow <= 990_000
    ensures: acc.balance + acc.escrow == old(acc.balance) + old(acc.escrow)
    if acc.balance >= amt:
        acc.balance = acc.balance - amt
        acc.escrow = acc.escrow + amt
        return True
    return False

def aggregate_quotes(quotes: list[UpstreamQuote, cap=8]) -> FetchState:
    valid = quotes |> filter(q => q.score >= 10)
    match len(valid):
        0 -> return Degraded
        n if n >= 1 ->
            total = valid |> map(q => q.score) |> fold(0, (a, b) => a + b)
            return Fresh(score=total / n)

def countdown(n: int[0..100]) -> int[0..100]:
    i: int[0..100] = n
    while i > 0:
        invariant: i >= 0 and i <= 100
        decreases: i
        i -= 1
    return i

monitor VaultMutex:
    writers: control int[0..1] = 0
    state Unlocked:
        invariant: writers == 0
        on acquire -> Locked:
            writers = 1
    state Locked:
        invariant: writers == 1
        on release -> Unlocked:
            writers = 0
`
	rep := verifySrc(t, src)
	if !rep.OK() {
		t.Fatalf("expected all SPARK VCs proved, got errors: %v", rep.Errors())
	}
	if rep.Proved < 8 {
		t.Fatalf("expected >=8 proved VCs, got %d", rep.Proved)
	}
}

func TestSPARKCatchesUnderflowOverflowDivZeroAndChoiceBugs(t *testing.T) {
	// 1. Underflow when guard missing
	rep := verifySrc(t, `
type Money = int[0..1000]
entity Account:
    balance: Money

def unsafe_withdraw(mut acc: Account, amt: int[1..100]) -> int:
    acc.balance = acc.balance - amt
    return 0
`)
	if rep.OK() {
		t.Fatalf("expected underflow failure when balance >= amt guard is missing")
	}

	// 2. Division by zero
	repDiv := verifySrc(t, `
def bad_div(a: int[0..100], b: int[0..10]) -> int:
    return a / b
`)
	if repDiv.OK() {
		t.Fatalf("expected division-by-zero counterexample b=0")
	}

	// 3. Incomplete match gap on bounded int
	repMatch := verifySrc(t, `
def grade(score: int[0..100]) -> int:
    match score:
        0..59 -> return 0
        61..100 -> return 1
    return 0
`)
	if repMatch.OK() {
		t.Fatalf("expected match exhaustiveness gap detection at score=60")
	}

	// 4. Non-exclusive choice guards in workflow
	repChoice := verifySrc(t, `
workflow BadChoice(x: int[0..100]):
    start -> eval
    step eval
    choice after eval:
        when x >= 10 -> branch_a
        when x <= 20 -> branch_b
        else -> branch_c
    step branch_a -> done
    step branch_b -> done
    step branch_c -> done
`)
	if repChoice.OK() {
		t.Fatalf("expected non-exclusive choice guard failure")
	}
}

func failedVCs(rep *Report) []string {
	var names []string
	for _, vc := range rep.VCs {
		if vc.Status != VCProved {
			names = append(names, vc.Name)
		}
	}
	return names
}

func TestSPARKCallRequiresUsesArgumentNotCallerVariable(t *testing.T) {
	cases := []struct {
		name     string
		src      string
		wantFail string
	}{
		{"int arg violates, caller has same-named int", `
def idn(x: int) -> int:
    requires: x >= 0
    return x

def main() -> int:
    x = 5
    y = 0 - 3
    r = idn(y)
    return 0
`, "call_idn_requires_1"},
		{"int literal satisfies", `
def idn(x: int) -> int:
    requires: x >= 0
    return x

def main() -> int:
    r = idn(5)
    return 0
`, ""},
		{"int arg satisfies, caller's same-named int would not", `
def idn(x: int) -> int:
    requires: x >= 0
    return x

def main() -> int:
    x = 0 - 3
    r = idn(7)
    return 0
`, ""},
		{"bool arg violates, caller has same-named bool", `
def need(flag: bool) -> int:
    requires: flag
    return 0

def main() -> int:
    flag = True
    other = False
    r = need(other)
    return 0
`, "call_need_requires_1"},
		{"bool literal satisfies", `
def need(flag: bool) -> int:
    requires: flag
    return 0

def main() -> int:
    r = need(True)
    return 0
`, ""},
		{"call in the argument is not the call in requires", `
def yes() -> bool:
    return True

def no() -> bool:
    return False

def need(flag: bool) -> int:
    requires: flag or not yes()
    return 0

def main() -> int:
    r = need(no())
    return 0
`, "call_need_requires_1"},
		{"entity arg violates, caller has same-named entity", `
type Money = int[0..1000]

entity Account:
    balance: Money

def spend(acc: Account) -> int:
    requires: acc.balance >= 100
    return 0

def main() -> int:
    acc = Account(balance=500)
    poor = Account(balance=1)
    r = spend(poor)
    return 0
`, "call_spend_requires_1"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			rep := verifySrc(t, tc.src)
			failed := failedVCs(rep)
			if tc.wantFail == "" {
				if len(failed) != 0 {
					t.Fatalf("expected all VCs proved, got: %v", rep.Errors())
				}
				return
			}
			for _, name := range failed {
				if strings.HasSuffix(name, tc.wantFail) {
					return
				}
			}
			t.Fatalf("expected a failed VC ending in %q, failed VCs: %v", tc.wantFail, failed)
		})
	}
}

// The VM and the native backend compute in int64 and wrap; the proof computes in Z. Every
// case below is a program where the two disagree unless the operation is shown to fit.
func TestSPARKInt64Overflow(t *testing.T) {
	cases := []struct {
		name string
		src  string
		// "" means everything is proved; otherwise the status the int64_overflow VC must have.
		want VCStatus
	}{
		{"constant scale of a bounded value overflows", `
type Big = int[0..4_000_000_000]

def scale(x: Big) -> int:
    ensures: result >= 0
    return x * 4_000_000_000
`, VCFailed},
		{"sum of two bounded values overflows", `
type Big = int[0..9_000_000_000_000_000_000]

def add(x: Big, y: Big) -> int:
    ensures: result >= 0
    return x + y
`, VCFailed},
		{"increment of an unconstrained int", `
def inc(x: int) -> int:
    return x + 1
`, VCFailed},
		{"negation of an unconstrained int", `
def neg(x: int) -> int:
    return -x
`, VCFailed},
		{"difference of unconstrained ints", `
def diff(a: int, b: int) -> int:
    if a >= b:
        return a - b
    return b - a
`, VCFailed},
		{"MinInt64 / -1", `
def quot(x: int, y: int) -> int:
    requires: y != 0
    return x / y
`, VCFailed},
		{"overflow in a branch condition", `
def cond(x: int) -> bool:
    if x * 2 > 10:
        return True
    return False
`, VCFailed},
		{"overflow in a compound assignment", `
def dec(x: int) -> int:
    y: int = x
    y -= 1
    return y
`, VCFailed},
		{"overflow of folded constants", `
def big() -> int:
    return 9_000_000_000_000_000_000 + 9_000_000_000_000_000_000
`, VCFailed},
		{"overflow in an entity invariant", `
entity Pair:
    a: int
    b: int
    invariant: a + b >= 0
`, VCFailed},
		{"overflow inside a lambda", `
def twice(xs: list[int, cap=8]) -> int:
    ys = xs |> map(x => x * 2)
    return 0
`, VCFailed},
		{"loop accumulator without a bound", `
def acc(n: int) -> int:
    requires: n >= 0
    i: int = 0
    total: int = 0
    while i < n:
        invariant: i >= 0 and i <= n
        decreases: n - i
        i = i + 1
        total = total + i
    return total
`, VCFailed},
		{"overflow in a variant arm of a match statement", `
def unwrap(o: Option[int]) -> int:
    match o:
        Some(v) -> return v + 1
        None -> return 0
`, VCFailed},
		{"overflow in a variant arm of a match expression", `
def unwrap(o: Option[int]) -> int:
    r = match o:
        Some(v) -> v + 1
        None -> 0
    return r
`, VCFailed},
		{"overflow in a bool arm", `
def pick(b: bool, x: int) -> int:
    match b:
        True -> return x + 1
        False -> return 0
`, VCFailed},
		{"overflow in an interpolated string", `
def show(x: int) -> int:
    print(f"next={x + 1}")
    return 0
`, VCFailed},
		{"overflow in a call argument", `
def idn(x: int) -> int:
    return x

def caller(x: int) -> int:
    return idn(x - 1)
`, VCFailed},
		{"one below MinInt64", `
def below() -> int:
    return -9_223_372_036_854_775_807 - 2
`, VCFailed},
		{"negating MinInt64", `
def flip() -> int:
    lo: int = -9_223_372_036_854_775_807 - 1
    return -lo
`, VCFailed},
		{"overflow in a with-update", `
entity Acct:
    bal: int

def credit(a: Acct, x: int) -> Acct:
    return a with { bal: x + 1 }
`, VCFailed},
		{"overflow in a run_workflow argument", `
workflow Echo(n: int) -> int:
    start -> work:
        k = n
    step finish after work -> done:
        return 0

def launch(x: int) -> int:
    return run_workflow Echo(x + 1)
`, VCFailed},
		{"overflow in the subject of a match statement", `
def classify(x: int) -> int:
    match x + 1:
        0 -> return 0
        _ -> return 1
`, VCFailed},
		{"qualified sum stage", `
import std.fp

type Huge = int[0..9_000_000_000_000_000_000]

def total(xs: list[Huge, cap=8]) -> int:
    return xs |> fp.sum()
`, VCFailed},
		{"qualified sum call", `
import std.fp

type Huge = int[0..9_000_000_000_000_000_000]

def total(xs: list[Huge, cap=8]) -> int:
    return fp.sum(xs)
`, VCFailed},
		{"qualified sum of unbounded elements", `
import std.fp

def total(xs: list[int, cap=8]) -> int:
    return fp.sum(xs)
`, VCUnknown},
		{"qualified fold call", `
import std.fp as f

type Huge = int[0..9_000_000_000_000_000_000]

def total(xs: list[Huge, cap=8]) -> int:
    return f.fold(xs, 0, (acc, x) => acc + x)
`, VCFailed},
		{"qualified map stage feeding a sum", `
import std.fp

type Half = int[0..4_000_000_000_000_000_000]

def total(xs: list[Half, cap=2]) -> int:
    return xs |> fp.map(x => x + x) |> fp.sum()
`, VCFailed},
		{"for loop accumulator", `
type Huge = int[0..9_000_000_000_000_000_000]

def total(xs: list[Huge, cap=8]) -> int:
    c: int = 0
    for x in xs:
        c += x
    return c
`, VCFailed},
		{"while loop without an invariant", `
def spin(n: int[0..9]) -> int:
    i: int = n
    while i < 10:
        i = i * 4_000_000_000
    return i
`, VCFailed},
		{"while loop nested in a for loop", `
def nested(n: int[0..3]) -> int:
    t: int = 1
    for k in 0..n:
        while t < 100:
            t = t * 4_000_000_000
    return 0
`, VCFailed},
		{"value assigned in a loop, used after it", `
def after(n: int[0..10]) -> int:
    i: int = 0
    for k in 0..n:
        i = 4_000_000_000
    return i * 4_000_000_000
`, VCFailed},
		{"product of unconstrained ints", `
def mul(x: int, y: int) -> int:
    return x * y
`, VCUnknown},
		{"product whose operand ranges exceed 64 bits", `
type Big = int[0..4_000_000_000]

def mul(x: Big, y: Big) -> int:
    return x * y
`, VCUnknown},
		{"bounded arithmetic fits", `
type Small = int[0..1_000_000]

def mix(x: Small, y: Small) -> int:
    ensures: result >= 0
    return x * y + x - y * 3 + 3_000_000
`, ""},
		{"variant arm binds a bounded field", `
def unwrap(o: Option[int[0..100]]) -> int:
    match o:
        Some(v) -> return v + 1
        None -> return 0
`, ""},
		{"string concatenation is not arithmetic", `
def greet(name: str) -> str:
    return "hello " + name + "!"
`, ""},
		{"requires range bounds a product", `
def mul(x: int, y: int) -> int:
    requires: x >= -1000 and x <= 1000 and y >= 0 and y <= 5
    return x * y
`, ""},
		{"guard bounds a sum", `
def add(a: int, b: int) -> int:
    if a > 1000 or a < -1000 or b > 1000 or b < -1000:
        return 0
    return a + b
`, ""},
		{"short circuit protects the right operand", `
def guarded(x: int) -> bool:
    requires: x >= 0
    return x <= 1000 and x * x > 30
`, ""},
		{"one-sided bound is enough when the other side cannot be reached", `
def shift(x: int) -> int:
    requires: x <= 0
    return x + 5
`, ""},
		{"the extremes themselves are representable", `
def edges(x: int) -> int:
    requires: x >= -9_223_372_036_854_775_807 and x <= 9_223_372_036_854_775_806
    lo = x - 1
    hi = x + 1
    return 0
`, ""},
		{"MinInt64 is representable", `
def lowest() -> int:
    return -9_223_372_036_854_775_807 - 1

def doubled(x: int[0..1]) -> int:
    return -4_611_686_018_427_387_904 * 2 + x

def raised() -> int:
    lo: int = -9_223_372_036_854_775_807 - 1
    return lo + 1
`, ""},
		{"qualified sum of bounded elements", `
import std.fp

type Score = int[0..100]

def total(xs: list[Score, cap=8]) -> int:
    return fp.sum(xs)

def doubled(xs: list[Score, cap=8]) -> int:
    return xs |> fp.map(x => x * 2) |> fp.sum()
`, ""},
		{"range-typed accumulator guarded in a for loop", `
type Score = int[0..100]

def total(xs: list[Score, cap=8]) -> int:
    c: int[0..1000] = 0
    for x in xs:
        if c <= 900:
            c += x
    return c * 2
`, ""},
		{"for loop over a range uses the bounds of its variable", `
def tri(n: int[0..1000]) -> int:
    last: int = 0
    for i in 0..n:
        last = i * 1000
    return 0
`, ""},
		{"division and remainder by a constant", `
def halve(x: int) -> int:
    r = x % 2
    return x / 2
`, ""},
		{"bounded loop counter", `
def count(n: int[0..1000]) -> int:
    i: int = 0
    total: int = 0
    while i < n:
        invariant: i >= 0 and i <= n and total == 2 * i
        decreases: n - i
        i = i + 1
        total = total + 2
    return total
`, ""},
		{"read_u32_be yields the whole unsigned 32-bit range", `
import std.bytes as bytes

def main() -> int:
    bv = bytes.from_hex("ffffffff")
    x = bv.read_u32_be(0) * 3_000_000_000
    return 0
`, VCFailed},
		{"read_u32_be scaled within int64", `
import std.bytes as bytes

def main() -> int:
    bv = bytes.from_hex("ffffffff")
    x = bv.read_u32_be(0) * 2_000_000_000
    return 0
`, ""},
		{"now_ms is not bounded by a billion", `
import std.time as time

def main() -> int:
    t = time.now_ms() * 9_000_000_000
    return 0
`, VCFailed},
		{"difference of two timestamps", `
import std.time as time

def main() -> int:
    t0 = time.now_ms()
    d = time.now_ms() - t0
    return 0
`, ""},
		{"constant overflow on a skipped short-circuit operand", `
def main() -> int:
    b = False and (9223372036854775807 + 1 > 0)
    return 0
`, ""},
		{"constant overflow on an evaluated short-circuit operand", `
def main() -> int:
    b = True and (9223372036854775807 + 1 > 0)
    return 0
`, VCFailed},
		{"entity with a field of its own type", `
entity Node:
    val: int[0..10]
    next: Node
    invariant: val + 1 <= 11

def get(n: Node) -> int:
    ensures: result <= 10
    return n.val
`, ""},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			rep := verifySrc(t, tc.src)
			if tc.want == "" {
				if !rep.OK() {
					t.Fatalf("expected all VCs proved, got: %v", rep.Errors())
				}
				return
			}
			for _, vc := range rep.VCs {
				if strings.HasSuffix(vc.Name, ".int64_overflow") && vc.Status == tc.want {
					return
				}
			}
			t.Fatalf("expected an int64_overflow VC with status %v, got: %v", tc.want, rep.Errors())
		})
	}
}

// A loop body runs any number of times, so what it assigns is not known after the loop
// beyond the invariants and the negated condition.
func TestSPARKLoopStateIsNotThePreLoopState(t *testing.T) {
	cases := []struct {
		name     string
		src      string
		wantFail string
	}{
		{"while loop changes a counter", `
def count(n: int[0..10]) -> int:
    ensures: result == 0
    i: int = 0
    while i < n:
        invariant: i >= 0
        decreases: n - i
        i = i + 1
    return i
`, "ensures_1"},
		{"for loop changes a flag value", `
def last(n: int[0..10]) -> int:
    ensures: result == 0
    r: int = 0
    for k in 0..n:
        r = 1
    return r
`, "ensures_1"},
		{"invariant and exit condition give the result", `
def count(n: int[0..10]) -> int:
    ensures: result == n
    i: int = 0
    while i < n:
        invariant: i >= 0 and i <= n
        decreases: n - i
        i = i + 1
    return i
`, ""},
		{"variables the loop leaves alone keep their value", `
def keep(n: int[0..10]) -> int:
    ensures: result == 7
    a: int = 7
    i: int = 0
    while i < n:
        invariant: i >= 0
        decreases: n - i
        i = i + 1
    return a
`, ""},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			rep := verifySrc(t, tc.src)
			failed := failedVCs(rep)
			if tc.wantFail == "" {
				if !rep.OK() {
					t.Fatalf("expected all VCs proved, got: %v", rep.Errors())
				}
				return
			}
			for _, name := range failed {
				if strings.HasSuffix(name, tc.wantFail) {
					return
				}
			}
			t.Fatalf("expected a failed VC ending in %q, failed VCs: %v", tc.wantFail, failed)
		})
	}
}

// The index of an assignment target is evaluated at run time, so arithmetic
// inside it needs the same proof obligations as anywhere else.
func TestSPARKChecksArithmeticInAssignmentIndex(t *testing.T) {
	for name, src := range map[string]string{
		"compound": `
def zero() -> int[0..0]:
    return 0

def f(mut xs: list[int[0..9]], n: int[0..3]) -> int:
    xs[10 / n] += zero()
    return 0
`,
		"plain": `
def f(mut xs: list[int[0..9]], n: int[0..3]) -> int:
    xs[10 / n] = 5
    return 0
`,
	} {
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
}

// A division is only checked on the paths that evaluate it: the right operand
// of and/or/implies runs only when the left one does not decide the result.
func TestSPARKDivisionUnderShortCircuitAndInElementWrites(t *testing.T) {
	cases := []struct {
		name, src string
		wantFail  bool
	}{
		{"guarded by and", `
def f(n: int[0..3]) -> bool:
    ok = n != 0 and 10 / n > 1
    return ok
`, false},
		{"guarded by or", `
def f(n: int[0..3]) -> bool:
    ok = n == 0 or 10 / n > 1
    return ok
`, false},
		{"or with the wrong guard", `
def f(n: int[0..3]) -> bool:
    bad = n != 0 or 10 / n > 1
    return bad
`, true},
		{"value written to a map", `
def f(mut m: map[str, int], n: int[0..3]) -> int:
    m["k"] = 10 / n
    return 0
`, true},
		{"value added to a list element", `
def f(mut xs: list[int[0..9]], n: int[0..3]) -> int:
    if len(xs) > 1:
        xs[0] += 9 / n
    return 0
`, true},
	}
	for _, c := range cases {
		failed := strings.Join(failedVCs(verifySrc(t, c.src)), "\n")
		if got := strings.Contains(failed, "div_nonzero"); got != c.wantFail {
			t.Errorf("%s: div_nonzero failed = %v, want %v; failed VCs:\n%s", c.name, got, c.wantFail, failed)
		}
	}
}

// A guard is not trusted across a call that may change what it tested.
func TestSPARKGuardNotKeptAcrossMutCall(t *testing.T) {
	src := `
entity S:
    n: int[0..9]

def clear(mut s: S) -> bool:
    s.n = 0
    return True

def f(mut s: S) -> bool:
    ok = s.n != 0 and clear(mut s) and 10 / s.n > 1
    return ok
`
	failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
	if !strings.Contains(failed, "div_nonzero") {
		t.Errorf("expected a failed div_nonzero, failed VCs:\n%s", failed)
	}
}
