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

const mutCallPrelude = `
entity S:
    n: int[0..9]

def clear(mut s: S) -> bool:
    ensures: s.n == 0
    s.n = 0
    return True

def five(mut s: S) -> int[0..0]:
    ensures: s.n == 5
    s.n = 5
    return 0

def bump(mut s: S) -> int[0..0]:
    requires: s.n < 9
    ensures: s.n == old(s.n) + 1
    s.n = s.n + 1
    return 0

def idn(x: int) -> int:
    requires: x >= 0
    return x
`

// mutCallVCs verifies body as the body of a function that owns a mutable S.
func mutCallVCs(t *testing.T, body string) string {
	t.Helper()
	src := mutCallPrelude + "\ndef f(mut s: S, a: bool, xs: list[int[0..9]]) -> int:\n" + body + "\n"
	return strings.Join(failedVCs(verifySrc(t, src)), "\n")
}

// A call may change its mut arguments, so nothing the caller knew about them
// before the call is kept, wherever in the statement the call is written.
func TestSPARKMutCallForgetsCallerFacts(t *testing.T) {
	cases := map[string]string{
		"statement": `
    if s.n != 0:
        y = clear(mut s)
        return 10 / s.n
    return 0`,
		"short-circuit operand": `
    if s.n != 0:
        ok = a and clear(mut s)
        return 10 / s.n
    return 0`,
		"if condition": `
    if s.n != 0:
        if clear(mut s):
            return 10 / s.n
    return 0`,
		"elif condition": `
    if s.n != 0:
        if a:
            return 1
        elif clear(mut s):
            return 2
        return 10 / s.n
    return 0`,
		"while condition": `
    i: int = 0
    if s.n != 0:
        while clear(mut s) and i < 3:
            invariant: i >= 0
            i += 1
        return 10 / s.n
    return 0`,
		"match expression arm": `
    if s.n != 0:
        y = match len(xs):
            0 -> clear(mut s)
            _ -> False
        return 10 / s.n
    return 0`,
		"match guard": `
    if s.n != 0:
        match len(xs):
            0 if clear(mut s) -> return 1
            _ -> return 10 / s.n
    return 0`,
		"lambda": `
    if s.n != 0:
        ys = xs |> map(x => clear(mut s))
        return 10 / s.n
    return 0`,
		"earlier pass of a while body": `
    i: int = 0
    if s.n != 0:
        while i < 3:
            invariant: i >= 0
            decreases: 3 - i
            x = 10 / s.n
            y = clear(mut s)
            i += 1
    return 0`,
		"earlier pass of a for body": `
    if s.n != 0:
        for x in xs:
            z = 10 / s.n
            y = clear(mut s)
    return 0`,
		"function value": `
    g = clear
    if s.n != 0:
        y = g(mut s)
        return 10 / s.n
    return 0`,
		"old value in ensures": `
    if s.n == 3:
        y = bump(mut s)
        return 10 / (s.n - 4)
    return 0`,
	}
	for name, body := range cases {
		if failed := mutCallVCs(t, body); !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
}

// After the call the caller knows the argument's type and what the callee
// ensures about it.
func TestSPARKMutCallAssumesEnsures(t *testing.T) {
	cases := map[string]string{
		"ensures": `
    y = five(mut s)
    return 10 / s.n`,
		"ensures with old": `
    if s.n == 3:
        y = bump(mut s)
        return 10 / (s.n - 3)
    return 0`,
		"calls in sequence": `
    y = five(mut s)
    z = bump(mut s)
    return 10 / (s.n - 5)`,
		"declared range": `
    y = clear(mut s)
    return 10 / (s.n + 1)`,
		"condition": `
    if not clear(mut s):
        return 1
    return 10 / (s.n + 1)`,
		"another variable keeps its facts": `
    if s.n != 0:
        t = S(n=1)
        y = clear(mut t)
        return 10 / s.n
    return 0`,
	}
	for name, body := range cases {
		if failed := mutCallVCs(t, body); failed != "" {
			t.Errorf("%s: expected every VC proved, failed VCs:\n%s", name, failed)
		}
	}
	// A requires is proved from what the previous calls ensure.
	failed := mutCallVCs(t, `
    y = five(mut s)
    z = bump(mut s)
    z = bump(mut s)
    z = bump(mut s)
    z = bump(mut s)
    z = bump(mut s)
    return 0`)
	if strings.Count(failed, "call_bump_requires_1") != 1 {
		t.Errorf("expected only the fifth bump to fail its requires, failed VCs:\n%s", failed)
	}
}

// A variable passed as mut is used nowhere else in the same statement, so
// the order of its reads and the call never decides a result.
func TestSPARKMutCallIsAloneInItsStatement(t *testing.T) {
	rejected := map[string]string{
		"read beside the call":            "    y = s.n + five(mut s)\n    return 0",
		"compound assignment":             "    s.n += five(mut s)\n    return 0",
		"two calls":                       "    y = five(mut s) + five(mut s)\n    return 0",
		"guard before the call":           "    ok = s.n != 0 and clear(mut s) and 10 / s.n > 1\n    return 0",
		"field assignment":                "    s.n = five(mut s)\n    return 0",
		"read inside a lambda":            "    ys = xs |> map(x => s.n + five(mut s))\n    return 0",
		"guard changes the match subject": "    match s.n:\n        5 if clear(mut s) -> return 1\n        5 -> return 10 / s.n\n        _ -> return 0",
		"condition of an if":              "    if s.n > 0 and clear(mut s):\n        return 1\n    return 0",
		"condition of a while":            "    while s.n > 0 and clear(mut s):\n        invariant: s.n >= 0\n        s.n = 0\n    return 0",
	}
	for name, body := range rejected {
		if failed := mutCallVCs(t, body); !strings.Contains(failed, "mut_call_alone") {
			t.Errorf("%s: expected a failed mut_call_alone, failed VCs:\n%s", name, failed)
		}
	}
	accepted := map[string]string{
		"statement":                          "    y = five(mut s)\n    return 0",
		"operand":                            "    y = 1 + five(mut s)\n    return 0",
		"condition":                          "    if clear(mut s) and a:\n        return 1\n    return 0",
		"guard of a match on something else": "    match len(xs):\n        0 if clear(mut s) -> return 1\n        _ -> return 0",
		"next statement reads":               "    y = five(mut s)\n    z = s.n + y\n    return 0",
		"while with invariant":               "    i: int = 0\n    while clear(mut s) and i < 3:\n        invariant: s.n >= 0 and i >= 0\n        i += 1\n    return 0",
		"two different variables":            "    t = S(n=1)\n    y = five(mut s) + five(mut t)\n    return 0",
	}
	for name, body := range accepted {
		if failed := mutCallVCs(t, body); strings.Contains(failed, "mut_call_alone") {
			t.Errorf("%s: expected mut_call_alone to hold, failed VCs:\n%s", name, failed)
		}
	}
}

// A callee's requires is checked wherever the call is written.
func TestSPARKCallRequiresCheckedInEveryPosition(t *testing.T) {
	forms := map[string]string{
		"assignment":      "    y = idn(%s)",
		"compound":        "    y: int = 0\n    y += idn(%s)",
		"if condition":    "    if idn(%s) > 0:\n        return 1",
		"while condition": "    i: int = 0\n    while idn(%s) > i:\n        invariant: i >= 0\n        i += 1",
		"for bound":       "    for i in 0..idn(%s):\n        print(i)",
		"negated":         "    b = not (idn(%s) > 0)",
		"list literal":    "    ys = [idn(%s)]",
		"f-string":        "    t = f\"{idn(%s)}\"",
		"match subject":   "    match idn(%s):\n        0 -> return 1\n        _ -> return 2",
		"match arm":       "    y = match len(xs):\n        0 -> idn(%s)\n        _ -> 2",
		"lambda":          "    ys = xs |> map(x => idn(%s))",
		"argument":        "    print(idn(%s))",
		"short-circuit":   "    b = a and idn(%s) > 0",
		"return":          "    return idn(%s)",
	}
	for name, form := range forms {
		bad := mutCallVCs(t, strings.Replace(form, "%s", "-3", 1)+"\n    return 0")
		if !strings.Contains(bad, "call_idn_requires_1") {
			t.Errorf("%s: expected idn(-3) to fail its requires, failed VCs:\n%s", name, bad)
		}
		good := mutCallVCs(t, strings.Replace(form, "%s", "3", 1)+"\n    return 0")
		if strings.Contains(good, "call_idn_requires_1") {
			t.Errorf("%s: expected idn(3) to meet its requires, failed VCs:\n%s", name, good)
		}
	}
}

// What a caller assumes after a call has to hold on every return, and to be
// about the caller's own variable.
func TestSPARKMutCallContractsHoldForTheCaller(t *testing.T) {
	cases := []struct{ name, src, wantFailed string }{
		{"early return through ?", `
def fail() -> Result[int, str]:
    return Err("no")

def e(mut s: S) -> Result[int, str]:
    ensures: s.n == 5
    s.n = 0
    x = fail()?
    s.n = 5
    return Ok(1)
`, "e.ensures_1"},
		{"mut parameter rebound", `
def reb(mut s: S) -> int[0..0]:
    ensures: s.n == 5
    s = S(n=5)
    return 0
`, "def:reb.mut_s_not_rebound"},
		{"ensures about a parameter the callee reassigns", `
def setk(mut s: S, k: int[0..9]) -> int[0..0]:
    ensures: s.n == k
    k = 3
    s.n = 3
    return 0

def g(mut s: S) -> int:
    y = setk(mut s, 0)
    return 10 / (s.n - 3)
`, "def:g.div_nonzero"},
		{"ensures about a local of the callee", `
def zero(mut s: S) -> int[0..0]:
    ensures: s.n == k
    k = 0
    s.n = k
    return 0

def g(mut s: S) -> int:
    k = 5
    y = zero(mut s)
    return 10 / s.n
`, "def:g.div_nonzero"},
		{"lambda kept for later", `
def g(mut s: S) -> int:
    later = () => clear(mut s)
    if s.n != 0:
        y = later()
        return 10 / s.n
    return 0
`, "def:g.mut_capture"},
	}
	for _, tc := range cases {
		failed := strings.Join(failedVCs(verifySrc(t, mutCallPrelude+tc.src)), "\n")
		if !strings.Contains(failed, tc.wantFailed) {
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", tc.name, tc.wantFailed, failed)
		}
	}
	// A `?` in a lambda leaves the lambda, so the function's contracts are
	// not due there.
	inLambda := mutCallPrelude + `
def check(x: int[0..9]) -> Result[int, str]:
    return Ok(x)

def g(mut s: S, xs: list[int[0..9]]) -> int:
    ensures: s.n == 5
    s.n = 0
    ys = xs |> map(x => check(x)?)
    s.n = 5
    return 0
`
	if failed := failedVCs(verifySrc(t, inLambda)); len(failed) != 0 {
		t.Errorf("a ? inside a lambda is not a return of the function, failed VCs: %v", failed)
	}
	stage := mutCallVCs(t, "    ys = xs |> map(x => five(mut s))\n    return 10 / (s.n + 1)")
	if stage != "" {
		t.Errorf("a pipeline stage may pass an outer variable as mut, failed VCs:\n%s", stage)
	}
}

// An entity's invariant is only known after a call that certainly ran.
func TestSPARKInvariantNotAssumedWhenCallMayNotRun(t *testing.T) {
	prelude := `
entity A:
    x: int[0..10]
    y: int[0..10]
    invariant: x + y <= 10

def keep(mut a: A) -> bool:
    return True
`
	cases := map[string]string{
		"short-circuit": `
def g(mut a: A, c: bool) -> int:
    a.x = 10
    ok = c and keep(mut a)
    z = 100 / (11 - a.x - a.y)
    a.x = 0
    return z
`,
		"loop": `
def g(mut a: A, c: bool) -> int:
    i: int = 0
    z: int = 0
    while i < 2:
        invariant: i >= 0
        decreases: 2 - i
        z = 100 / (11 - a.x - a.y)
        ok = keep(mut a)
        a.x = 10
        i += 1
    a.x = 0
    return z
`,
	}
	for name, src := range cases {
		failed := strings.Join(failedVCs(verifySrc(t, prelude+src)), "\n")
		if !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	// After a call that ran, the callee has re-established it.
	ok := `
def g(mut a: A) -> int:
    done = keep(mut a)
    return 100 / (11 - a.x - a.y)
`
	if failed := failedVCs(verifySrc(t, prelude+ok)); len(failed) != 0 {
		t.Errorf("expected every VC proved, failed VCs: %v", failed)
	}
}

// `x |> f(a)` calls f(x, a): the piped value is the first argument when the
// callee's contract is checked and applied.
func TestSPARKPipedCallBindsThePipedValueFirst(t *testing.T) {
	prelude := mutCallPrelude + `
def inv(x: int[0..9]) -> int:
    requires: x != 0
    return 10 / x

def set_to(x: int[0..9], mut s: S, other: int[0..9]) -> int[0..0]:
    ensures: s.n == x
    s.n = x
    return 0
`
	cases := []struct{ name, body, wantFailed string }{
		{"bare stage", "    z: int[0..9] = 0\n    y = z |> inv\n    return 0", "call_inv_requires_1"},
		{"stage with arguments", "    z: int[0..9] = 0\n    y = z |> inv()\n    return 0", "call_inv_requires_1"},
		{"ensures uses the piped value", "    x: int[0..9] = 0\n    y = x |> set_to(mut s, 5)\n    return 10 / s.n", "div_nonzero"},
	}
	for _, tc := range cases {
		src := prelude + "\ndef g(mut s: S) -> int:\n" + tc.body + "\n"
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, tc.wantFailed) {
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", tc.name, tc.wantFailed, failed)
		}
	}
	ok := prelude + `
def g(mut s: S) -> int:
    x: int[0..9] = 4
    y = x |> set_to(mut s, 0)
    q = 10 / s.n
    r = x |> inv
    return 0
`
	if failed := failedVCs(verifySrc(t, ok)); len(failed) != 0 {
		t.Errorf("expected every VC proved, failed VCs: %v", failed)
	}
}

// A keyword argument is bound to the parameter it names.
func TestSPARKKeywordArgumentsBindByName(t *testing.T) {
	prelude := `
def divide(a: int[0..9], b: int[0..9]) -> int:
    requires: a != 0
    return b / a
`
	cases := []struct{ name, call, wantFailed string }{
		{"reordered, safe", "divide(b=0, a=2)", ""},
		{"reordered, zero divisor", "divide(b=1, a=0)", "call_divide_requires_1"},
		{"piped and reordered", "2 |> divide(b=0)", ""},
		{"keyword first, then by position", "divide(a=2, 0)", ""},
		{"by position, then keyword", "divide(2, b=0)", ""},
		{"zero divisor by position after a keyword", "divide(b=1, 0)", "call_divide_args"},
		{"parameter given twice", "divide(4, a=6)", "call_divide_args"},
		{"unknown keyword", "divide(typo=0, 1)", "call_divide_args"},
		{"piped value with a keyword for the rest", "2 |> divide(b=1)", ""},
		{"piped value and keyword for the same parameter", "0 |> divide(b=1, a=0)", "call_divide_args"},
	}
	for _, tc := range cases {
		src := prelude + "\ndef g() -> int:\n    y = " + tc.call + "\n    return 0\n"
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if tc.wantFailed == "" && failed != "" {
			t.Errorf("%s: expected every VC proved, failed VCs:\n%s", tc.name, failed)
		}
		if tc.wantFailed != "" && !strings.Contains(failed, tc.wantFailed) {
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", tc.name, tc.wantFailed, failed)
		}
	}
}

const joinPrelude = `
entity S:
    n: int[0..9]

def make(k: int[0..9]) -> S:
    return S(n=k)

def one() -> list[int]:
    return [1]

def name_of(k: int[0..9]) -> str:
    return "a"
`

// joinVCs verifies body as a function body and returns the VCs not proved.
func joinVCs(t *testing.T, body string) string {
	t.Helper()
	src := joinPrelude + "\ndef f(o: Option[int[1..9]], n: int[0..9], c: bool, xs: list[int[0..9]]) -> int:\n" + body + "\n"
	return strings.Join(failedVCs(verifySrc(t, src)), "\n")
}

// What a branch or an arm assigns is the value after the if or the match.
func TestSPARKStateAfterIfAndMatch(t *testing.T) {
	stale := map[string]string{
		"match arms assign": `
    x = 1
    match o:
        Some(v) -> x = 0
        None -> x = 0
    return 10 / x`,
		"one match arm assigns": `
    x = 5
    match o:
        Some(v) -> x = 0
        None -> x = 7
    return 10 / x`,
		"loop inside a match arm": `
    x = 5
    match o:
        Some(v) ->
            for y in xs:
                x = 0
        None -> x = 7
    return 10 / x`,
		"match that may run no arm": `
    t = name_of(n)
    x = 0
    match t:
        "a" -> x = 2
        "b" -> x = 3
    return 10 / x`,
		"boolean assigned in both branches": `
    safe = False
    if n == 0:
        safe = True
    else:
        safe = True
    if safe:
        return 10 / n
    return 1`,
		"entity reassigned in a branch": `
    s = S(n=3)
    if c:
        s = make(0)
    return 10 / s.n`,
	}
	for name, body := range stale {
		if failed := joinVCs(t, body); !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	if failed := joinVCs(t, "    ys = [1, 2, 3]\n    if c:\n        ys = [1]\n    return ys[2]"); !strings.Contains(failed, "index_bounds") {
		t.Errorf("list reassigned in a branch: expected a failed index_bounds, failed VCs:\n%s", failed)
	}
	precise := map[string]string{
		"every arm assigns a nonzero value": `
    x = 0
    match o:
        Some(v) -> x = 5
        None -> x = 7
    return 10 / x`,
		"arm assigns the bound field": `
    x = 0
    match o:
        Some(v) -> x = v
        None -> x = 7
    return 10 / x`,
		"boolean records the test": `
    ok = False
    if n > 0:
        ok = True
    if ok:
        return 10 / n
    return 0`,
		"nested if and match": `
    x = 1
    if c:
        match o:
            Some(v) -> x = 2
            None -> x = 3
    else:
        if n > 3:
            x = 4
    return 10 / x`,
		"match that may run no arm keeps a safe value": `
    t = name_of(n)
    x = 1
    match t:
        "a" -> x = 2
        "b" -> x = 3
    return 10 / x`,
		"guarded arm with a catch-all": `
    x = 1
    match n:
        k if k > 5 -> x = 2
        _ -> x = 3
    return 10 / x`,
		"every arm returns": `
    match o:
        Some(v) -> return 10 / v
        None -> return 0`,
	}
	for name, body := range precise {
		if failed := joinVCs(t, body); failed != "" {
			t.Errorf("%s: expected every VC proved, failed VCs:\n%s", name, failed)
		}
	}
}

// An assignment replaces everything known about the variable.
func TestSPARKAssignmentForgetsTheOldValue(t *testing.T) {
	stale := map[string]string{
		"entity from a call":         "    s = S(n=5)\n    s = make(0)\n    return 10 / s.n",
		"entity from a variable":     "    s = S(n=5)\n    z = S(n=0)\n    s = z\n    return 10 / s.n",
		"positional constructor":     "    s = S(n=5)\n    s = S(0)\n    return 10 / s.n",
		"length of an earlier value": "    ys = one()\n    k = len(ys)\n    ys = one()\n    return 10 / (len(ys) - k + 1)",
	}
	for name, body := range stale {
		if failed := joinVCs(t, body); !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	if failed := joinVCs(t, "    ys = [1, 2, 3]\n    ys = one()\n    return ys[2]"); !strings.Contains(failed, "index_bounds") {
		t.Errorf("list from a call: expected a failed index_bounds, failed VCs:\n%s", failed)
	}
	loop := `
def g(xs: list[int], c: int[0..3]) -> int:
    requires: len(xs) >= 3
    i: int = 0
    while i < c:
        invariant: i >= 0
        decreases: c - i
        xs = []
        i += 1
    return 10 / len(xs)
`
	if failed := strings.Join(failedVCs(verifySrc(t, loop)), "\n"); !strings.Contains(failed, "div_nonzero") {
		t.Errorf("list parameter reassigned in a loop: expected a failed div_nonzero, failed VCs:\n%s", failed)
	}
	precise := map[string]string{
		"new value reads the old one":    "    s = S(n=3)\n    s = S(n=s.n + 1)\n    return 10 / (s.n - 3)",
		"integer reads itself":           "    k = n\n    k = k + 1\n    return 10 / k",
		"pipeline keeps the length":      "    ys = xs |> map(x => x + 1)\n    if len(xs) > 2:\n        return ys[2]\n    return 0",
		"field set after a call":         "    s = make(n)\n    s.n = 4\n    return 10 / s.n",
		"second name for a list":         "    ys = xs\n    if len(xs) > 2:\n        return ys[2]\n    return 0",
		"same unknown length read twice": "    ys = one()\n    if len(ys) > 0:\n        return 10 / len(ys)\n    return 0",
	}
	for name, body := range precise {
		if failed := joinVCs(t, body); failed != "" {
			t.Errorf("%s: expected every VC proved, failed VCs:\n%s", name, failed)
		}
	}
}

// A match on an int that a call returns must cover the negative values too:
// nothing says the result is not negative.
func TestSPARKMatchOnCallResultCoversNegatives(t *testing.T) {
	src := `
def neg() -> int:
    return 0 - 5

def g() -> int:
    match neg():
        k if k >= 0 -> return 1
    return 10 / 0
`
	failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
	if !strings.Contains(failed, "match_exhaustive") {
		t.Errorf("expected a failed match_exhaustive, failed VCs:\n%s", failed)
	}
	ok := `
def g(xs: list[int]) -> int:
    match len(xs):
        k if k >= 0 -> return 1
`
	if failed := failedVCs(verifySrc(t, ok)); len(failed) != 0 {
		t.Errorf("a length is never negative, failed VCs: %v", failed)
	}
}

const invariantPrelude = `
entity A:
    x: int[0..10]
    y: int[0..10]
    invariant: x + y <= 10

entity Box:
    inner: A
    k: int[0..9]

def use(a: A) -> int:
    return 100 / (11 - a.x - a.y)

def fresh() -> A:
    return A(x=1, y=1)

def open_box(bx: Box) -> int:
    return use(bx.inner)
`

// An entity may break its invariant between two field updates, but not at
// the point where it is handed to a call, returned, or put into another value.
func TestSPARKEntityInvariantWhereAnEntityIsHandedOn(t *testing.T) {
	body := func(b string) string {
		return invariantPrelude + "\ndef f(a: A, rows: list[A], o: Option[A]) -> int:\n" + b + "\n"
	}
	broken := "    b = A(x=5, y=5)\n    b.x = 6\n"
	rejected := map[string]string{
		"call argument":         body(broken + "    return use(b)"),
		"list element":          body(broken + "    ys = [b]\n    return 0"),
		"variant payload":       body(broken + "    p = Some(b)\n    return 0"),
		"field of an entity":    body(broken + "    bx = Box(inner=b, k=1)\n    return 0"),
		"copy with a field":     body("    b = A(x=5, y=5)\n    return use(b with {x: 6})"),
		"field of an element":   body("    rs = [A(x=5, y=5)]\n    rs[0].x = 6\n    return 0"),
		"returned":              invariantPrelude + "\ndef g() -> A:\n" + broken + "    return b\n",
		"entity inside a field": invariantPrelude + "\ndef g() -> int:\n    bx = Box(inner=A(x=5, y=5), k=1)\n    bx.inner.x = 6\n    return open_box(bx)\n",
	}
	for name, src := range rejected {
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, "_invariant_1") || !strings.Contains(failed, "entity_") {
			t.Errorf("%s: expected a failed entity invariant, failed VCs:\n%s", name, failed)
		}
	}
	accepted := map[string]string{
		"parameter":                "    return use(a)",
		"two-step update":          "    b = A(x=5, y=5)\n    b.x = 0\n    b.y = 10\n    return use(b)",
		"restored before the call": broken + "    b.y = 4\n    return use(b)",
		"second name":              "    b = A(x=5, y=5)\n    c = b\n    return use(c)",
		"copy with a field":        "    b = A(x=5, y=5)\n    c = b with {x: 2}\n    return use(c)",
		"loop element":             "    t: int = 0\n    for r in rows:\n        t = use(r)\n    return t",
		"indexed element":          "    if len(rows) > 0:\n        return use(rows[0])\n    return 0",
		"pattern payload":          "    match o:\n        Some(v) -> return use(v)\n        None -> return 0",
		"result of a call":         "    return use(fresh())",
	}
	for name, b := range accepted {
		if failed := failedVCs(verifySrc(t, body(b))); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// Replacing an entity-valued field, in a statement or in a loop, replaces
// what was known about the entity inside it.
func TestSPARKReplacedEntityFieldForgetsItsOldContents(t *testing.T) {
	prelude := `
entity P:
    x: int[0..10]

entity Holder:
    inner: P
`
	stale := map[string]string{
		"copy with a new field":     "    b.inner.x = 1\n    c = b with {inner: P(x=0)}\n    a = c.inner\n    return 10 / a.x",
		"field assigned":            "    b.inner.x = 1\n    b.inner = P(x=0)\n    a = b.inner\n    return 10 / a.x",
		"nested field in a for":     "    b.inner.x = 1\n    for i in [0]:\n        b.inner.x = 0\n    a = b.inner\n    return 10 / a.x",
		"nested field in a while":   "    b.inner.x = 1\n    i: int = 0\n    while i < 1:\n        invariant: i >= 0\n        decreases: 1 - i\n        b.inner.x = 0\n        i += 1\n    a = b.inner\n    return 10 / a.x",
		"entity assigned in a loop": "    p = P(x=1)\n    for i in [0]:\n        p = P(x=0)\n    return 10 / p.x",
	}
	for name, body := range stale {
		src := prelude + "\ndef f(mut b: Holder) -> int:\n" + body + "\n"
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	// A field of the outer entity is not mistaken for one of the new inner entity.
	outer := `
entity P:
    x: int[0..10]

entity Wide:
    inner: P
    x: int[0..10]

def make_p() -> P:
    return P(x=0)

def f(mut b: Wide) -> int:
    b.x = 5
    c = b with {inner: make_p()}
    a = c.inner
    return 10 / a.x
`
	if failed := strings.Join(failedVCs(verifySrc(t, outer)), "\n"); !strings.Contains(failed, "div_nonzero") {
		t.Errorf("outer field with the inner field's name: expected a failed div_nonzero, failed VCs:\n%s", failed)
	}
	// ...and the outer entity keeps its own fields.
	kept := strings.Replace(outer, "    a = c.inner\n    return 10 / a.x\n", "    return 10 / c.x\n", 1)
	if failed := failedVCs(verifySrc(t, kept)); len(failed) != 0 {
		t.Errorf("outer field after replacing the inner entity: expected every VC proved, failed VCs: %v", failed)
	}
	ok := prelude + "\ndef f(mut b: Holder) -> int:\n    b.inner = P(x=2)\n    a = b.inner\n    return 10 / a.x\n"
	if failed := failedVCs(verifySrc(t, ok)); len(failed) != 0 {
		t.Errorf("the new contents are known, failed VCs: %v", failed)
	}
}

// The entity a match expression yields is checked arm by arm.
func TestSPARKEntityInvariantOfMatchExpression(t *testing.T) {
	valid := invariantPrelude + `
def choose(flag: bool) -> A:
    return match flag:
        True -> A(x=1, y=1)
        False -> A(x=2, y=2)
`
	if failed := failedVCs(verifySrc(t, valid)); len(failed) != 0 {
		t.Errorf("arms that construct valid entities: expected every VC proved, failed VCs: %v", failed)
	}
	broken := invariantPrelude + `
def choose(flag: bool) -> A:
    b = A(x=5, y=5)
    b.x = 6
    return match flag:
        True -> A(x=1, y=1)
        False -> b
`
	failed := strings.Join(failedVCs(verifySrc(t, broken)), "\n")
	if !strings.Contains(failed, "entity_b_invariant_1") {
		t.Errorf("an arm that yields a broken entity: expected a failed entity_b_invariant_1, failed VCs:\n%s", failed)
	}
}

// A match expression must cover its subject wherever it is written, not
// only as the whole right-hand side of an assignment or a return.
func TestSPARKMatchExpressionCoverageInFieldAndElementAssignment(t *testing.T) {
	prelude := `
entity P:
    x: int[0..10]

entity Holder:
    inner: P
`
	partial := map[string]string{
		"field":   "    b.inner = match k:\n        0 -> P(x=1)\n    return 0",
		"element": "    rs = [P(x=1)]\n    rs[0] = match k:\n        0 -> P(x=1)\n    return 0",
	}
	for name, body := range partial {
		src := prelude + "\ndef f(mut b: Holder, k: int[0..9]) -> int:\n" + body + "\n"
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, "match_exhaustive") {
			t.Errorf("%s: expected a failed match_exhaustive, failed VCs:\n%s", name, failed)
		}
	}
	total := prelude + "\ndef f(mut b: Holder, k: int[0..9]) -> int:\n    b.inner = match k:\n        0 -> P(x=1)\n        _ -> P(x=2)\n    return 0\n"
	if failed := failedVCs(verifySrc(t, total)); len(failed) != 0 {
		t.Errorf("a total match: expected every VC proved, failed VCs: %v", failed)
	}
}

// An entity that can be reached in two ways has no private moment between
// two field updates: each write has to leave its invariants true.
func TestSPARKSharedEntityKeepsItsInvariantOnEveryWrite(t *testing.T) {
	body := func(b string) string {
		return invariantPrelude + "\ndef f(mut a: A, mut rows: list[A], mut o: Option[A]) -> int:\n" + b + "\n"
	}
	rejected := map[string]string{
		"loop variable":                 body("    for r in rows:\n        r.x = 6\n    if len(rows) > 0:\n        return use(rows[0])\n    return 0"),
		"matched payload":               body("    match o:\n        Some(v) ->\n            v.x = 6\n            return 0\n        None -> return 0"),
		"element by index":              body("    if len(rows) > 0:\n        r = rows[0]\n        r.x = 6\n    return 0"),
		"second name":                   body("    b = A(x=5, y=5)\n    c = b\n    b.x = 6\n    return use(c)"),
		"stored in a list":              body("    b = A(x=5, y=5)\n    ys = [b]\n    b.x = 6\n    b.y = 4\n    return 0"),
		"shared on a loop's next pass":  body("    c = A(x=5, y=5)\n    for i in 0..3:\n        c.x = 6\n        c.y = 4\n        if len(rows) > 0:\n            c = rows[0]\n    return 0"),
		"entity inside a loop variable": invariantPrelude + "\ndef g(bxs: list[Box]) -> int:\n    for bx in bxs:\n        bx.inner.x = 6\n    return 0\n",
		"field of another entity":       invariantPrelude + "\ndef g(mut bx: Box) -> int:\n    a = bx.inner\n    a.x = 6\n    return 0\n",
		"yielded by a lambda":           body("    b = A(x=5, y=5)\n    b.x = 6\n    ys = [1, 2] |> map(n => b)\n    return 0"),
	}
	for name, src := range rejected {
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, "_invariant_1") || !strings.Contains(failed, "entity_") {
			t.Errorf("%s: expected a failed entity invariant, failed VCs:\n%s", name, failed)
		}
	}
	accepted := map[string]string{
		"write that keeps the invariant": "    for r in rows:\n        r.x = 0\n    return 0",
		"adjusted, then stored":          "    b = A(x=5, y=5)\n    b.x = 0\n    b.y = 10\n    ys = [b]\n    return 0",
		"name given a new entity":        "    c = A(x=1, y=1)\n    for r in rows:\n        c = r\n    c = A(x=5, y=5)\n    c.x = 6\n    c.y = 4\n    return use(c)",
	}
	for name, b := range accepted {
		if failed := failedVCs(verifySrc(t, body(b))); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// A compound assignment through a field path is recorded under that path.
func TestSPARKCompoundAssignmentThroughFieldPath(t *testing.T) {
	src := `
entity P:
    x: int[0..10]

entity Holder:
    inner: P

def f(mut b: Holder) -> int:
    b.inner.x = 1
    b.inner.x -= 1
    a = b.inner
    return 10 / a.x
`
	if failed := strings.Join(failedVCs(verifySrc(t, src)), "\n"); !strings.Contains(failed, "div_nonzero") {
		t.Errorf("expected a failed div_nonzero, failed VCs:\n%s", failed)
	}
}

// What does not give a second way to reach an entity leaves its two-step
// updates alone.
func TestSPARKUnsharedEntityKeepsTwoStepUpdates(t *testing.T) {
	twoStep := "    b.x = 6\n    b.y = 4\n    return use(b)"
	accepted := map[string]string{
		"a number read out of it":           "    b = A(x=5, y=5)\n    saved = b.x\n" + twoStep,
		"replaced in every branch":          "    b = A(x=5, y=5)\n    c = b\n    if len(rows) > 0:\n        b = A(x=5, y=5)\n    else:\n        b = A(x=5, y=5)\n" + twoStep,
		"lambda parameter of the same name": "    b = A(x=5, y=5)\n    ys = rows |> map(b => [b])\n" + twoStep,
	}
	for name, body := range accepted {
		src := invariantPrelude + "\ndef f(a: A, rows: list[A], o: Option[A]) -> int:\n" + body + "\n"
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
	// Replaced in one branch only: the other still shares it.
	oneBranch := invariantPrelude + "\ndef f(a: A, rows: list[A], o: Option[A]) -> int:\n    b = A(x=5, y=5)\n    c = b\n    if len(rows) > 0:\n        b = A(x=5, y=5)\n" + twoStep + "\n"
	if failed := strings.Join(failedVCs(verifySrc(t, oneBranch)), "\n"); !strings.Contains(failed, "entity_b_invariant_1") {
		t.Errorf("replaced in one branch: expected a failed entity_b_invariant_1, failed VCs:\n%s", failed)
	}
}

// An untyped map (`m = {}`) gives its elements no type. Taking one into a
// typed variable shares it, and a field write on an untyped one is rejected.
func TestSPARKEntityInAnUntypedMap(t *testing.T) {
	body := func(b string) string {
		return invariantPrelude + "\ndef f(a: A, rows: list[A], o: Option[A]) -> int:\n    m = {}\n    m[\"k\"] = A(x=5, y=5)\n" + b + "\n    return use(m[\"k\"])\n"
	}
	rejected := map[string]string{
		"typed variable":   "entity_r_invariant_1\x00    r: A = m[\"k\"]\n    r.x = 6",
		"untyped variable": "field_x_object_type\x00    r = m[\"k\"]\n    r.x = 6",
		"in place":         "field_x_object_type\x00    m[\"k\"].x = 6",
	}
	for name, c := range rejected {
		vc, b, _ := strings.Cut(c, "\x00")
		failed := strings.Join(failedVCs(verifySrc(t, body(b))), "\n")
		if !strings.Contains(failed, vc) {
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", name, vc, failed)
		}
	}
	// With a typed map the element's other fields are known to fit the invariant.
	typed := invariantPrelude + "\ndef f(a: A, rows: list[A], o: Option[A]) -> int:\n    m: map[str, A] = {}\n    m[\"k\"] = A(x=5, y=5)\n    r = m[\"k\"]\n    r.x = 0\n    return use(m[\"k\"])\n"
	if failed := failedVCs(verifySrc(t, typed)); len(failed) != 0 {
		t.Errorf("typed map, a write that keeps the invariant: expected every VC proved, failed VCs: %v", failed)
	}
}
