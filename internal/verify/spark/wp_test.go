package spark

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
)

// semaErr is the error sema gives for src, "" if it accepts it.
func semaErr(t *testing.T, src string) string {
	t.Helper()
	prog, err := parser.Parse("test.anm", src)
	if err != nil {
		t.Fatalf("parse failed: %v", err)
	}
	if _, err := sema.Check(prog); err != nil {
		return err.Error()
	}
	return ""
}

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
		// The same entity under another name.
		"read under another name":       "    t = s\n    if s.n == 0 or clear(mut t):\n        return 1\n    return 10 / s.n",
		"another name beside the call":  "    t = s\n    y = s.n + five(mut t)\n    return 0",
		"field assignment by an alias":  "    t = s\n    s.n = five(mut t)\n    return 0",
		"another name inside a lambda":  "    t = s\n    ys = xs |> map(x => s.n + five(mut t))\n    return 0",
		"another name in a match guard": "    t = s\n    match s.n:\n        5 if clear(mut t) -> return 1\n        5 -> return 10 / s.n\n        _ -> return 0",
	}
	for name, body := range rejected {
		if failed := mutCallVCs(t, body); !strings.Contains(failed, "mut_call_alone") {
			t.Errorf("%s: expected a failed mut_call_alone, failed VCs:\n%s", name, failed)
		}
	}
	accepted := map[string]string{
		"statement":                            "    y = five(mut s)\n    return 0",
		"operand":                              "    y = 1 + five(mut s)\n    return 0",
		"condition":                            "    if clear(mut s) and a:\n        return 1\n    return 0",
		"guard of a match on something else":   "    match len(xs):\n        0 if clear(mut s) -> return 1\n        _ -> return 0",
		"next statement reads":                 "    y = five(mut s)\n    z = s.n + y\n    return 0",
		"while with invariant":                 "    i: int = 0\n    while clear(mut s) and i < 3:\n        invariant: s.n >= 0 and i >= 0\n        i += 1\n    return 0",
		"two different variables":              "    t = S(n=1)\n    y = five(mut s) + five(mut t)\n    return 0",
		"another name, a statement of its own": "    t = s\n    y = five(mut t)\n    z = s.n + y\n    return 0",
		"another name, an unrelated variable":  "    t = s\n    u = S(n=1)\n    y = u.n + five(mut t)\n    return 0",
		"another name, hidden by a lambda's":   "    t = s\n    ys = xs |> map(t => t + five(mut s))\n    return 0",
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
		{"piped value with a keyword for the rest", "2 |> divide(b=1)", ""},
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
		"match whose catch-all keeps the value": `
    t = name_of(n)
    x = 1
    match t:
        "a" -> x = 2
        "b" -> x = 3
        _ -> x = 1
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

const aliasPrelude = `
entity P:
    x: int[0..10]
    y: int[0..10]

entity Holder:
    inner: P
    k: int[0..9]

def zero(mut p: P) -> int:
    p.x = 0
    return 0

def peek(p: P) -> int:
    return p.x
`

// Entities are references. What is known about a variable does not survive
// a write made through another way to reach its entity.
func TestSPARKWriteThroughAnAliasForgetsFacts(t *testing.T) {
	stale := map[string]string{
		"second name":                 "    b = P(x=5, y=5)\n    c = b\n    b.x = 0\n    return 10 / c.x",
		"written through the copy":    "    b = P(x=5, y=5)\n    c = b\n    c.x = 0\n    return 10 / b.x",
		"loop over a list holding it": "    b = P(x=5, y=5)\n    rows = [b]\n    for r in rows:\n        r.x = 0\n    return 10 / b.x",
		"element written in place":    "    b = P(x=5, y=5)\n    rows = [b]\n    rows[0].x = 0\n    return 10 / b.x",
		"mut call on the other name":  "    b = P(x=5, y=5)\n    c = b\n    _ = zero(mut b)\n    return 10 / c.x",
		"inside another entity":       "    b = P(x=5, y=5)\n    h = Holder(inner=b, k=1)\n    h.inner.x = 0\n    return 10 / b.x",
		"alias made in one branch":    "    b = P(x=5, y=5)\n    c = P(x=5, y=5)\n    if n > 1:\n        c = b\n    b.x = 0\n    return 10 / c.x",
		"matched payload":             "    b = P(x=5, y=5)\n    o = Some(b)\n    match o:\n        Some(v) ->\n            v.x = 0\n        None ->\n            return 0\n    return 10 / b.x",
	}
	for name, body := range stale {
		src := aliasPrelude + "\ndef f(n: int[0..9]) -> int:\n" + body + "\n"
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	kept := map[string]string{
		"two separate entities":      "    b = P(x=5, y=5)\n    c = P(x=7, y=1)\n    b.x = 0\n    return 10 / c.x",
		"read by a call in between":  "    b = P(x=5, y=5)\n    c = P(x=7, y=1)\n    k = peek(b)\n    b.x = 2\n    return 10 / c.x + 10 / b.x",
		"mut call on a separate one": "    b = P(x=5, y=5)\n    c = P(x=7, y=1)\n    _ = zero(mut b)\n    return 10 / c.x",
	}
	for name, body := range kept {
		src := aliasPrelude + "\ndef f(n: int[0..9]) -> int:\n" + body + "\n"
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// What a function received without mut cannot be written through another name.
func TestSPARKReadonlyParameterThroughAnotherName(t *testing.T) {
	bodies := map[string]string{
		"second name":     "readonly_c\x00    c = a\n    c.x = 0\n    return 0",
		"loop variable":   "readonly_r\x00    for r in rows:\n        r.x = 0\n    return 0",
		"element":         "readonly_r\x00    if len(rows) > 0:\n        r = rows[0]\n        r.x = 0\n    return 0",
		"matched payload": "readonly_v\x00    match o:\n        Some(v) ->\n            v.x = 0\n            return 0\n        None -> return 0",
		"mut argument":    "readonly_c\x00    c = a\n    return zero(mut c)",
		"through a field": "readonly_c\x00    c = h.inner\n    c.x = 0\n    return 0",
	}
	for name, c := range bodies {
		vc, body, _ := strings.Cut(c, "\x00")
		src := aliasPrelude + "\ndef f(a: P, rows: list[P], o: Option[P], h: Holder) -> int:\n" + body + "\n"
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, vc) {
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", name, vc, failed)
		}
		src = aliasPrelude + "\ndef f(mut a: P, mut rows: list[P], mut o: Option[P], mut h: Holder) -> int:\n" + body + "\n"
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s with mut parameters: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// A callee is verified with its parameters taken for separate values, so a
// mut argument must not be reachable from another argument.
func TestSPARKMutArgumentAliasingAnotherArgument(t *testing.T) {
	prelude := aliasPrelude + `
def g(mut p: P, q: P) -> int:
    requires: q.x >= 1
    p.x = 0
    return 10 / q.x

def into(mut p: P, h: Holder) -> int:
    p.x = 0
    return h.k
`
	rejected := map[string]string{
		"second name":       "    b = P(x=5, y=5)\n    c = b\n    return g(mut b, c)",
		"held by an entity": "    b = P(x=5, y=5)\n    h = Holder(inner=b, k=1)\n    return into(mut b, h)",
	}
	for name, body := range rejected {
		failed := strings.Join(failedVCs(verifySrc(t, prelude+"\ndef f() -> int:\n"+body+"\n")), "\n")
		if !strings.Contains(failed, "_mut_alias") {
			t.Errorf("%s: expected a failed call_*_mut_alias, failed VCs:\n%s", name, failed)
		}
	}
	separate := prelude + "\ndef f() -> int:\n    b = P(x=5, y=5)\n    c = P(x=5, y=5)\n    k = g(mut b, c)\n    return g(mut b, c)\n"
	if failed := failedVCs(verifySrc(t, separate)); len(failed) != 0 {
		t.Errorf("separate entities, twice: expected every VC proved, failed VCs: %v", failed)
	}
}

// An entity that a call may keep (inside a mut argument) or hand back is
// shared afterwards, so a write to it has to keep its invariant.
func TestSPARKEntityKeptOrReturnedByACall(t *testing.T) {
	prelude := invariantPrelude + `
def keep(mut bx: Box, a: A) -> int:
    bx.inner = a
    return 0

def idf(a: A) -> A:
    return a
`
	rejected := map[string]string{
		"kept in a mut argument": "    b = A(x=5, y=5)\n    bx = Box(inner=A(x=1, y=1), k=1)\n    k = keep(mut bx, b)\n    b.x = 6\n    return open_box(bx)",
		"handed back":            "    b = A(x=5, y=5)\n    c = idf(b)\n    b.x = 6\n    return use(c)",
		"yielded by a lambda":    "    b = A(x=5, y=5)\n    ys = [1, 2] |> map(n => b)\n    b.x = 6\n    return 0",
	}
	for name, body := range rejected {
		failed := strings.Join(failedVCs(verifySrc(t, prelude+"\ndef f() -> int:\n"+body+"\n")), "\n")
		if !strings.Contains(failed, "entity_b_invariant_1") {
			t.Errorf("%s: expected a failed entity_b_invariant_1, failed VCs:\n%s", name, failed)
		}
	}
	// A call that only reads keeps nothing: the two-step update stays.
	read := prelude + "\ndef f() -> int:\n    b = A(x=5, y=5)\n    k = use(b)\n    b.x = 6\n    b.y = 4\n    return use(b)\n"
	if failed := failedVCs(verifySrc(t, read)); len(failed) != 0 {
		t.Errorf("after a call that only reads: expected every VC proved, failed VCs: %v", failed)
	}
}

// A forgotten alias keeps what its type says, not what an earlier binding
// of the name said, and keeps an invariant that every write preserves.
func TestSPARKForgottenAliasIsReboundFromItsType(t *testing.T) {
	stale := `
entity P1:
    x: int[1..10]

entity P2:
    x: int

def f(n: P1) -> int:
    n = P2(x=0)
    m = n
    m.x = 0
    return 10 / n.x
`
	// Sema no longer lets a name be rebound to another entity type.
	if err := semaErr(t, stale); !strings.Contains(err, "a variable keeps its sort") {
		t.Errorf("a name rebound to another entity type: expected sema to refuse it, got %q", err)
	}
	valid := invariantPrelude + "\ndef f() -> int:\n    b = A(x=5, y=5)\n    c = b\n    b.x = 0\n    return use(c)\n"
	if failed := failedVCs(verifySrc(t, valid)); len(failed) != 0 {
		t.Errorf("a write that keeps the invariant: expected every VC proved, failed VCs: %v", failed)
	}
	// c was broken before it got a second name: nothing restores it.
	broken := invariantPrelude + "\ndef f() -> int:\n    b = A(x=5, y=5)\n    d = A(x=1, y=1)\n    b.x = 6\n    c = b\n    e = d\n    d.x = 2\n    return use(c)\n"
	if failed := strings.Join(failedVCs(verifySrc(t, broken)), "\n"); !strings.Contains(failed, "entity_c_invariant_1") {
		t.Errorf("an alias that was already broken: expected a failed entity_c_invariant_1, failed VCs:\n%s", failed)
	}
}

// `with` copies one level: a flat entity's copy is separate, the copy of an
// entity that holds entities shares them.
func TestSPARKWithCopySharesNestedEntities(t *testing.T) {
	flat := aliasPrelude + "\ndef f(a: P) -> int:\n    c = a with {x: 1}\n    c.y = 2\n    return c.x + c.y\n"
	if failed := failedVCs(verifySrc(t, flat)); len(failed) != 0 {
		t.Errorf("copy of a flat read-only parameter: expected every VC proved, failed VCs: %v", failed)
	}
	nested := aliasPrelude + "\ndef f() -> int:\n    h = Holder(inner=P(x=5, y=5), k=1)\n    h.inner.x = 5\n    c = h with {k: 2}\n    h.inner.x = 0\n    g = c.inner\n    return 10 / g.x\n"
	if failed := strings.Join(failedVCs(verifySrc(t, nested)), "\n"); !strings.Contains(failed, "div_nonzero") {
		t.Errorf("copy of an entity holding an entity: expected a failed div_nonzero, failed VCs:\n%s", failed)
	}
	readonly := aliasPrelude + "\ndef f(h: Holder) -> int:\n    c = h with {k: 2}\n    c.inner.x = 0\n    return 0\n"
	if failed := strings.Join(failedVCs(verifySrc(t, readonly)), "\n"); !strings.Contains(failed, "readonly_c") {
		t.Errorf("copy of a read-only entity holding an entity: expected a failed readonly_c, failed VCs:\n%s", failed)
	}
}

// Review round 2 of the aliasing work: three ways to get a value that does
// not fit what its type promises.
func TestSPARKElementCompoundWriteWithRangeAndRelations(t *testing.T) {
	compound := `
entity A:
    x: int[0..10]
    invariant: x >= 1

def f() -> int:
    b = A(x=5)
    rows = [b]
    rows[0].x *= 0
    return 10 / b.x
`
	if failed := strings.Join(failedVCs(verifySrc(t, compound)), "\n"); !strings.Contains(failed, "entity_element_invariant_1") {
		t.Errorf("compound write on an element: expected a failed entity_element_invariant_1, failed VCs:\n%s", failed)
	}
	with := `
entity P1:
    x: int[1..10]

def inv(p: P1) -> int:
    return 10 / p.x

def f() -> int:
    b = P1(x=5)
    c = b with {x: 0}
    return inv(c)
`
	if failed := strings.Join(failedVCs(verifySrc(t, with)), "\n"); !strings.Contains(failed, "with_x_bounds") {
		t.Errorf("with outside the field's range: expected a failed with_x_bounds, failed VCs:\n%s", failed)
	}
	inRange := strings.Replace(with, "{x: 0}", "{x: 2}", 1)
	if failed := failedVCs(verifySrc(t, inRange)); len(failed) != 0 {
		t.Errorf("with inside the field's range: expected every VC proved, failed VCs: %v", failed)
	}
	relation := `
entity Acc:
    bal: int[0..10]

entity Ord:
    amount: int[0..9]
    rel buyer -> 1 Acc

def f(o: Ord) -> int:
    c = o with {amount: 1}
    c.buyer.bal = 0
    return 0
`
	if failed := strings.Join(failedVCs(verifySrc(t, relation)), "\n"); !strings.Contains(failed, "readonly_c") {
		t.Errorf("copy of a read-only entity with a relation: expected a failed readonly_c, failed VCs:\n%s", failed)
	}
}

// Review round 3 of the aliasing work: two rules that were stricter than
// they need to be.
func TestSPARKElementWriteAndCopyOfReadonlyValue(t *testing.T) {
	element := `
entity R:
    id: int[0..10]
    count: int[0..10]
    invariant: id >= 1
    invariant: count <= 10 - id + id

def f(mut rows: list[R]) -> int:
    if len(rows) > 0:
        rows[0].count = 1
    return 0
`
	if failed := failedVCs(verifySrc(t, element)); len(failed) != 0 {
		t.Errorf("an invariant on an untouched field: expected every VC proved, failed VCs: %v", failed)
	}
	touched := strings.Replace(strings.Replace(element, "count <= 10 - id + id", "count <= id", 1), "count = 1", "count = 5", 1)
	if failed := strings.Join(failedVCs(verifySrc(t, touched)), "\n"); !strings.Contains(failed, "entity_element_invariant_2") {
		t.Errorf("an invariant the write can break: expected a failed entity_element_invariant_2, failed VCs:\n%s", failed)
	}
	prelude := `
entity Acc:
    bal: int[0..10]

entity Ord:
    amount: int[0..9]
    rel buyer -> 1 Acc

def zap(mut o: Ord) -> int:
    o.buyer.bal = 0
    return 0
`
	own := prelude + "\ndef f(o: Ord) -> int:\n    c = o with {amount: 1}\n    c.amount = 3\n    return c.amount\n"
	if failed := failedVCs(verifySrc(t, own)); len(failed) != 0 {
		t.Errorf("own field of a copy: expected every VC proved, failed VCs: %v", failed)
	}
	below := map[string]string{
		"readonly_c": "    c = o with {amount: 1}\n    c.buyer.bal = 0\n    return 0",
		"readonly_h": "    c = o with {amount: 1}\n    d = c\n    h = d.buyer\n    h.bal = 0\n    return 0",
		"readonly_d": "    c = o with {amount: 1}\n    d = c\n    return zap(mut d)",
	}
	for vc, body := range below {
		failed := strings.Join(failedVCs(verifySrc(t, prelude+"\ndef f(o: Ord) -> int:\n"+body+"\n")), "\n")
		if !strings.Contains(failed, vc) {
			t.Errorf("below a copy: expected a failed %s, failed VCs:\n%s", vc, failed)
		}
	}
}

// An invariant reads the entity's fields in every form of expression, and
// sees a boolean write.
func TestSPARKInvariantReadsFieldsUnderAnyExpression(t *testing.T) {
	negated := `
entity A:
    x: int[0..10]
    invariant: -x < 0

def f(mut rows: list[A]) -> int:
    if len(rows) > 0:
        rows[0].x = 0
    return 0

def g(mut a: A) -> int:
    a.x = 0
    return 0

def h(a: A) -> int:
    x = 0
    return 10 / a.x
`
	failed := strings.Join(failedVCs(verifySrc(t, negated)), "\n")
	for _, vc := range []string{"f.entity_element_invariant_1", "g.mut_a_invariant"} {
		if !strings.Contains(failed, vc) {
			t.Errorf("invariant under a unary minus: expected a failed %s, failed VCs:\n%s", vc, failed)
		}
	}
	if strings.Contains(failed, "h.div_nonzero") {
		t.Errorf("the invariant should give h that a.x is not zero, whatever its local x is, failed VCs:\n%s", failed)
	}
	boolean := `
entity A:
    ready: bool
    x: int[0..10]
    invariant: ready

def f(mut rows: list[A]) -> int:
    if len(rows) > 0:
        rows[0].ready = False
    return 0
`
	if failed := strings.Join(failedVCs(verifySrc(t, boolean)), "\n"); !strings.Contains(failed, "entity_element_invariant_1") {
		t.Errorf("boolean field written false: expected a failed entity_element_invariant_1, failed VCs:\n%s", failed)
	}
	if failed := failedVCs(verifySrc(t, strings.Replace(boolean, "= False", "= True", 1))); len(failed) != 0 {
		t.Errorf("boolean field written true: expected every VC proved, failed VCs: %v", failed)
	}
}

// Review round 5 of the aliasing work: lengths in invariants, and fields of
// an unnamed element that are entities or lists.
func TestSPARKInvariantsOverLengthsAndElementFields(t *testing.T) {
	accepted := map[string]string{
		"untouched string length": `
entity A:
    text: str
    n: int[0..10]
    invariant: len(text) > 0

def f(mut a: A) -> int:
    a.n = 1
    return 0
`,
		"second name keeps list length": `
entity A:
    items: list[int]
    n: int[0..10]
    invariant: len(items) > 0

def f(a: A) -> A:
    c = a
    return c
`,
		"entity and list written to an element": `
entity I:
    x: int[0..10]
    invariant: x >= 1

entity O:
    inner: I
    items: list[int]
    n: int[0..10]
    invariant: len(items) > 0

def f(mut rows: list[O]) -> int:
    if len(rows) > 0:
        rows[0].inner = I(x=2)
        rows[0].items = [1, 2]
    return 0
`,
		"boolean computed from a length": `
entity A:
    ready: bool
    text: str
    invariant: ready

def f(mut rows: list[A], t: str) -> int:
    if len(rows) > 0:
        rows[0].ready = not (len(t) < 0)
    return 0
`,
	}
	for name, src := range accepted {
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
	emptied := `
entity A:
    text: str
    n: int[0..10]
    invariant: len(text) > 0

def f(mut a: A) -> int:
    a.text = ""
    return 0

def g(mut rows: list[A]) -> int:
    if len(rows) > 0:
        rows[0].text = ""
    return 0
`
	failed := strings.Join(failedVCs(verifySrc(t, emptied)), "\n")
	for _, vc := range []string{"f.mut_a_invariant", "g.entity_element_invariant_1"} {
		if !strings.Contains(failed, vc) {
			t.Errorf("string field emptied: expected a failed %s, failed VCs:\n%s", vc, failed)
		}
	}
}

// A map's length changes when a key is inserted, through any name for it.
func TestSPARKMapLengthAfterInsertion(t *testing.T) {
	stale := map[string]string{
		"same name": `
def f(mut m: map[str, int]) -> int:
    if len(m) == 0:
        m["a"] = 1
        return 10 / (1 - len(m))
    return 0
`,
		"second name": `
def f(mut m: map[str, int]) -> int:
    k = m
    if len(m) == 0:
        k["a"] = 1
        return 10 / (1 - len(m))
    return 0
`,
		"in a loop": `
def f(mut m: map[str, int]) -> int:
    if len(m) == 0:
        for i in 0..1:
            m["a"] = 1
        return 10 / (1 - len(m))
    return 0
`,
	}
	for name, src := range stale {
		if failed := strings.Join(failedVCs(verifySrc(t, src)), "\n"); !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	invariant := `
entity T:
    tbl: map[str, int]
    n: int[0..10]
    invariant: len(tbl) == 0

def insert(mut t: T) -> int:
    t.tbl["a"] = 1
    return 0

def untouched(mut t: T) -> int:
    t.n = 2
    return 0

def read(m: map[str, int]) -> int:
    if len(m) > 0:
        return 10 / len(m)
    return 0
`
	failed := failedVCs(verifySrc(t, invariant))
	if len(failed) != 1 || failed[0] != "insert.mut_t_invariant" {
		t.Errorf("expected only insert.mut_t_invariant to fail, failed VCs: %v", failed)
	}
	kept := map[string]string{
		"insertion into a separate new map": `
def f(m: map[str, int]) -> int:
    if len(m) > 0:
        acc: map[str, int] = {}
        acc["a"] = 1
        return 10 / len(m)
    return 0
`,
		"invariant guaranteed by a mut call": `
entity T:
    tbl: map[str, int]
    n: int[0..10]
    invariant: len(tbl) > 0

def touch(mut t: T) -> int:
    t.n = 1
    return 0

def f(mut t: T) -> int:
    return touch(mut t)
`,
		"insertion in one branch": `
def f(mut m: map[str, int], c: bool) -> int:
    ensures: result >= 0
    if c:
        m["a"] = 1
    return len(m)
`,
		"two lists passed twice": `
def fill(mut dst: list[int], src: list[int]) -> int:
    return len(src)

def f() -> int:
    a = [1, 2]
    b = [3, 4]
    k = fill(mut a, b)
    return fill(mut a, b)
`,
	}
	for name, src := range kept {
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
	rejected := map[string]string{
		"div_nonzero": `
entity T:
    tbl: map[str, int]
    n: int[0..10]

def f() -> int:
    e: map[str, int] = {}
    t = T(tbl=e, n=1)
    if len(e) == 0:
        t.tbl["a"] = 1
        return 10 / (1 - len(e))
    return 0
`,
		"call_g_mut_alias": `
def g(mut m: map[str, int], k: map[str, int]) -> int:
    if len(k) == 0:
        m["a"] = 1
        return 10 / (1 - len(k))
    return 0

def f() -> int:
    m: map[str, int] = {}
    k = m
    return g(mut m, k)
`,
	}
	for vc, src := range rejected {
		if failed := strings.Join(failedVCs(verifySrc(t, src)), "\n"); !strings.Contains(failed, vc) {
			t.Errorf("expected a failed %s, failed VCs:\n%s", vc, failed)
		}
	}
	// A map variable given a list is refused by sema.
	rebound := `
def f(c: bool) -> int:
    x = {"a": 1}
    k = len(x)
    if c:
        x = [1, 2]
    return x[5]
`
	if err := semaErr(t, rebound); !strings.Contains(err, "a variable keeps its sort") {
		t.Errorf("a map variable given a list: expected sema to refuse it, got %q", err)
	}
}

// Review round 8 of the aliasing work.
func TestSPARKMatchAliasNestedInvariantAndResultShape(t *testing.T) {
	matchAlias := `
def f(mut m: map[str, int], mut other: map[str, int], c: bool) -> int:
    k = match c:
        True -> m
        False -> other
    if len(k) == 0:
        m["a"] = 1
        return 10 / (1 - len(k))
    return 0
`
	if failed := strings.Join(failedVCs(verifySrc(t, matchAlias)), "\n"); !strings.Contains(failed, "div_nonzero") {
		t.Errorf("alias through a match expression: expected a failed div_nonzero, failed VCs:\n%s", failed)
	}
	nested := `
entity Inner:
    x: int[0..10]
    y: int[0..10]
    invariant: x + y <= 10

entity Outer:
    inner: Inner
    k: int[0..9]

def brk(mut o: Outer) -> int:
    o.inner.x = 6
    return 0

def keep(mut o: Outer) -> int:
    o.inner.x = 0
    o.k = 2
    return 0
`
	failed := failedVCs(verifySrc(t, nested))
	if len(failed) != 1 || failed[0] != "brk.mut_o.inner_invariant" {
		t.Errorf("nested entity of a mut parameter: expected only brk.mut_o.inner_invariant to fail, failed VCs: %v", failed)
	}
	prelude := invariantPrelude + `
def codes(a: A) -> list[int]:
    return [a.x, a.y]

def idf(a: A) -> A:
    return a
`
	numbers := prelude + "\ndef f() -> int:\n    b = A(x=5, y=5)\n    k = codes(b)\n    b.x = 6\n    b.y = 4\n    return use(b)\n"
	if failed := failedVCs(verifySrc(t, numbers)); len(failed) != 0 {
		t.Errorf("a call returning numbers keeps no entity: expected every VC proved, failed VCs: %v", failed)
	}
	taken := prelude + "\ndef first(rows: list[A]) -> A:\n    requires: len(rows) > 0\n    return rows[0]\n\ndef f() -> int:\n    b = A(x=5, y=5)\n    rows = [b]\n    c = first(rows)\n    c.x = 6\n    return use(b)\n"
	if failed := strings.Join(failedVCs(verifySrc(t, taken)), "\n"); !strings.Contains(failed, "entity_c_invariant_1") {
		t.Errorf("an entity taken out of a list by a call: expected a failed entity_c_invariant_1, failed VCs:\n%s", failed)
	}
	piped := prelude + "\ndef f() -> int:\n    b = A(x=5, y=5)\n    c = b |> idf\n    b.x = 6\n    return use(c)\n"
	if failed := strings.Join(failedVCs(verifySrc(t, piped)), "\n"); !strings.Contains(failed, "entity_b_invariant_1") {
		t.Errorf("an entity handed back by a piped call: expected a failed entity_b_invariant_1, failed VCs:\n%s", failed)
	}
}

// Review round 9 of the aliasing work.
func TestSPARKClosureResultBareOptionAndNestedAliasWrite(t *testing.T) {
	nested := invariantPrelude + `
entity Outer:
    inner: A
    k: int[0..9]
`
	rejected := map[string]struct{ src, vc string }{
		"entity handed back by a closure": {invariantPrelude + `
def f() -> int:
    b = A(x=5, y=5)
    g = n => b
    c = g(1)
    if c.x != 0:
        b.x = 0
        return 10 / c.x
    return 0
`, "div_nonzero"},
		"map handed back by a closure": {`
def f() -> int:
    m: map[str, int] = {}
    g = n => m
    k = g(1)
    if len(m) == 0:
        k["a"] = 1
        return 10 / (1 - len(m))
    return 0
`, "div_nonzero"},
		"bare Option next to its mut payload": {invariantPrelude + `
def wrap(a: A) -> Option:
    return Some(a)

def g(mut p: A, q: Option[A]) -> int:
    return 0

def f() -> int:
    b = A(x=5, y=5)
    o = wrap(b)
    return g(mut b, o)
`, "call_g_mut_alias"},
		"nested invariant broken through a second name": {nested + `
def f(mut o: Outer) -> int:
    h = o.inner
    h.x = 6
    return 0
`, "entity_h_invariant_1"},
		"nested invariant broken before the second name": {nested + `
def f(mut o: Outer, mut rows: list[A]) -> int:
    o.inner.x = 6
    h = o.inner
    if len(rows) > 0:
        rows[0].x = 0
    return 0
`, "f.mut_o.inner_invariant"},
		"a ? that can return": {invariantPrelude + `
def half(n: int) -> Option[int]:
    if n > 0:
        return Some(n / 2)
    return None

def f(mut o: A, n: int) -> Option[int]:
    o.x = 6
    v = half(n)?
    o.y = 4
    return Some(v)
`, "f.mut_o_invariant"},
	}
	for name, c := range rejected {
		if failed := strings.Join(failedVCs(verifySrc(t, c.src)), "\n"); !strings.Contains(failed, c.vc) {
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", name, c.vc, failed)
		}
	}
	proved := map[string]string{
		"nested entity written through a second name": nested + `
def f(mut o: Outer) -> int:
    h = o.inner
    h.x = 0
    return 0
`,
		"lambda parameter with the name of a function": invariantPrelude + `
def mk(n: int) -> A:
    return A(x=5, y=5)

def f() -> int:
    ys = [1, 2] |> map(mk => mk + 1)
    b = mk(1)
    b.x = 6
    b.y = 4
    return use(b)
`,
		"a ? that cannot return": nested + `
def f(mut o: Outer) -> Option[int]:
    o.inner.x = 6
    v = Some(1)?
    o.inner.y = 4
    return Some(v)
`,
	}
	for name, src := range proved {
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// The range of the elements of a list, of the values of a map and of the
// fields of a variant is proved where they are made or written.
func TestSPARKElementRanges(t *testing.T) {
	rejected := map[string]struct{ src, vc string }{
		"literal for a keyword argument": {`
def f(a: list[int[1..9]], b: list[int[0..20]]) -> int:
    if len(a) > 0:
        return 100 / a[0]
    return 0

def main() -> int:
    print(f(b=[5], a=[0]))
    return 0
`, "list_elem_bounds"},
		"piped literal": {`
def first(xs: list[int[1..9]]) -> int:
    if len(xs) > 0:
        return 10 / xs[0]
    return 0

def main() -> int:
    print([0] |> first)
    return 0
`, "list_elem_bounds"},
		"literal after a piped value": {`
def add(a: int[1..9], ys: list[int[1..9]]) -> int:
    if len(ys) > 0:
        return 10 / ys[0]
    return a

def main() -> int:
    print(5 |> add([0]))
    return 0
`, "list_elem_bounds"},
		"r11/a1": {`
def main() -> int:
    xs = [5, 0]
    print(10 / xs[1])
    return 0
`, "div_nonzero"},
		"r11/a2": {`
def main() -> int:
    m = {"a": 5, "b": 0}
    print(10 / m["b"])
    return 0
`, "div_nonzero"},
		"r11/a4": {`
def main() -> int:
    xs = [5, 6]
    xs[0] = 0
    print(10 / xs[0])
    return 0
`, "div_nonzero"},
		"r11/a5": {`
def main() -> int:
    xs: list[int[1..9]] = [5, 6]
    xs[0] = 0
    print(10 / xs[0])
    return 0
`, "elem_assign_bounds"},
		"r11/a9": {`
def main() -> int:
    xs: list[int[1..9]] = [0, 6]
    print(10 / xs[0])
    return 0
`, "list_elem_bounds"},
		"r11/a11": {`
def main() -> int:
    m: map[str, int[1..9]] = {"a": 1}
    m["a"] = 0
    print(10 / m["a"])
    return 0
`, "elem_assign_bounds"},
		"r11/a13": {`
def main() -> int:
    xs = [5, 6]
    for i in 0..2:
        xs[i] = xs[i] - 5
    print(10 / xs[0])
    return 0
`, "div_nonzero"},
		"r11b/n6": {`
def get(c: bool) -> Option[int[1..9]]:
    x = 0
    if c:
        return Some(x)
    return None

def main() -> int:
    match get(True):
        Some(v) -> print(10 / v)
        None -> print(0)
    return 0
`, "variant_Some_range"},
		"r11b/n17": {`
type Shape = Circle(r: int[1..9]) | Dot

def main() -> int:
    s = Circle(0)
    match s:
        Circle(r) -> print(10 / r)
        Dot -> print(0)
    return 0
`, "variant_Circle_range"},
		"r11b/n13": {`
def main() -> int:
    m: map[str, int[1..9]] = {"a": 0}
    print(10 / m["a"])
    return 0
`, "map_value_bounds"},
		"r11b/n24": {`
def main() -> int:
    y: int[1..9] = 0
    ys = [1] |> map(v => y)
    print(10 / ys[0])
    return 0
`, "div_nonzero"},
		"r11b/n31": {`
def main() -> int:
    xs: list[int[1..9]] = [5, 6]
    ys: list[int[1..9]] = xs |> map(x => x - 5)
    zs = xs |> map(x => x - 5)
    for v in zs:
        print(10 / v)
    return 0
`, "list_elem_bounds"},
		"r11b/h2": {`
def f(xs: list[int[1..9]]) -> int:
    s = xs |> fold(0, (a, v) => 0)
    if len(xs) == 2:
        return 10 / s
    return 0

def main() -> int:
    xs: list[int[1..9]] = [1, 1]
    print(f(xs))
    return 0
`, "div_nonzero"},
		"r11b/n1": {`
def main() -> int:
    xs = [5, 6]
    ys = xs
    ys[0] = 0
    print(10 / xs[0])
    return 0
`, "div_nonzero"},
		"r11b/n2": {`
def zero(mut ys: list[int]) -> int:
    ys[0] = 0
    return 0

def main() -> int:
    xs = [5, 6]
    r = zero(mut xs)
    print(10 / xs[0])
    return 0
`, "div_nonzero"},
	}
	for name, tc := range rejected {
		failed := failedVCs(verifySrc(t, tc.src))
		found := false
		for _, f := range failed {
			if strings.Contains(f, tc.vc) {
				found = true
			}
		}
		if !found {
			t.Errorf("%s: expected a failed %s VC, failed VCs: %v", name, tc.vc, failed)
		}
	}
	proved := map[string]string{
		"literals for reordered keyword arguments": `
def f(a: list[int[1..9]], b: list[int[10..20]]) -> int:
    if len(a) > 0:
        return 100 / (a[0] - 10)
    return 0

def main() -> int:
    print(f(b=[15], a=[5]))
    return 0
`,
		"r11b/p1": `
def main() -> int:
    xs: list[int[1..9]] = [5, 6]
    xs[0] = 7
    print(10 / xs[0])
    return 0
`,
		"r11b/p2": `
def main() -> int:
    xs = [5, 6]
    print(10 / xs[0])
    for v in xs:
        print(10 / v)
    return 0
`,
		"r11b/p3": `
def f(ys: list[int[1..9]]) -> int:
    if len(ys) > 0:
        return 10 / ys[0]
    return 0

def main() -> int:
    print(f([5, 6]))
    xs: list[int[1..9]] = [3, 4]
    print(f(xs))
    return 0
`,
		"r11b/p5": `
def mk() -> list[int[1..9]]:
    return [1, 2, 3]

def main() -> int:
    xs = mk()
    if len(xs) > 1:
        print(10 / xs[1])
    m: map[str, int[1..9]] = {"a": 1}
    m["b"] = 2
    print(10 / m["a"])
    return 0
`,
		"r11b/p6": `
def main() -> int:
    xs: list[int[1..9]] = [5, 6]
    ys: list[int[2..10]] = xs |> map(x => x + 1)
    zs = xs |> map(x => x - 5)
    for v in ys:
        print(10 / v)
    return 0
`,
	}
	for name, src := range proved {
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// A call that blocks on the network is given a timeout in 1..300_000,
// whatever the type of the expression.
func TestSPARKTimeoutBounds(t *testing.T) {
	wait := func(decl, arg string) string {
		return `
import std.socket as sock

def wait(t: int) -> int:
` + decl + `
    match sock.listen_tcp("127.0.0.1", 0):
        Ok(ln) ->
            match ln.accept(timeout_ms=` + arg + `):
                Ok(c) -> c.close()
                Err(e) -> print(e)
            ln.close()
        Err(e) -> print(e)
    return 0
`
	}
	rejected := map[string]string{
		"variable assigned zero": wait("    timeout = 0", "timeout"),
		"unbounded parameter":    wait("    timeout = 1", "t"),
		"computed zero":          wait("    timeout = 1 - 1", "timeout"),
		"too long":               wait("    timeout = 300_000", "timeout + 1"),
	}
	for name, src := range rejected {
		failed := strings.Join(failedVCs(verifySrc(t, src)), "\n")
		if !strings.Contains(failed, "timeout_bounds") {
			t.Errorf("%s: expected a failed timeout_bounds, failed VCs:\n%s", name, failed)
		}
	}
	proved := map[string]string{
		"variable":         wait("    timeout = 20", "timeout * 2"),
		"guarded argument": wait("    if t < 1 or t > 5000:\n        return 0", "t"),
	}
	for name, src := range proved {
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// A literal nested in a variant pattern matches only that value, so it does
// not cover the variant; a match on a string needs a catch-all arm.
func TestSPARKMatchExhaustivenessWithNestedAndStringPatterns(t *testing.T) {
	cases := []struct {
		name, src, wantFailed string
	}{
		{"nested literal does not cover Ok", `
def f(r: Result[int, str]) -> int:
    match r:
        Ok(0) -> return 0
        Err(e) -> return 1
    return 2
`, "match_exhaustive_adt"},
		{"nested literal plus a binding arm covers Ok", `
def f(r: Result[int, str]) -> int:
    match r:
        Ok(0) -> return 0
        Ok(n) -> return 1
        Err(e) -> return 2
    return 3
`, ""},
		{"nested literal in Some", `
def f(o: Option[int]) -> int:
    match o:
        Some(5) -> return 0
        None -> return 1
    return 2
`, "match_exhaustive_adt"},
		{"string match without a catch-all", `
def f(cmd: str) -> int:
    match cmd:
        "get" -> return 0
        "set" -> return 1
    return 2
`, "match_exhaustive_default"},
		{"string match with a catch-all", `
def f(cmd: str) -> int:
    match cmd:
        "get" -> return 0
        _ -> return 1
    return 2
`, ""},
		{"guarded catch-all is not a catch-all", `
def f(cmd: str, n: int) -> int:
    match cmd:
        "get" -> return 0
        other if n > 0 -> return 1
    return 2
`, "match_exhaustive_default"},
		{"nested variants cover between them", `
def f(o: Option[Option[int]]) -> int:
    match o:
        Some(Some(1)) -> return 1
        Some(Some(v)) -> return 2
        Some(None) -> return 3
        None -> return 4
`, ""},
		{"a nested variant is missing", `
def f(o: Option[Option[int]]) -> int:
    match o:
        Some(Some(1)) -> return 1
        Some(None) -> return 3
        None -> return 4
    return 5
`, "match_exhaustive_adt"},
		{"two fields cover between them", `
type Tree = Leaf(v: int) | Node(l: Option[int], r: Option[int])

def f(t: Tree) -> int:
    match t:
        Leaf(0) -> return 0
        Leaf(v) -> return 1
        Node(Some(a), Some(b)) -> return 2
        Node(Some(a), None) -> return 3
        Node(None, _) -> return 4
`, ""},
		{"one combination of two fields is missing", `
type Cmd = Get(key: str) | Set(key: str, on: bool) | Quit

def f(c: Cmd) -> int:
    match c:
        Get(k) -> return 2
        Set(_, False) -> return 4
        Set("a", True) -> return 3
        Quit -> return 6
    return 7
`, "match_exhaustive_adt"},
		{"nested bools cover between them", `
def f(a: Option[bool]) -> int:
    match a:
        Some(True) -> return 1
        Some(False) -> return 2
        None -> return 3
`, ""},
		{"a guarded nested arm does not cover", `
def f(r: Result[Option[int], str]) -> int:
    match r:
        Ok(Some(v)) if v > 0 -> return v
        Ok(None) -> return -1
        Err(_) -> return -2
    return 0
`, "match_exhaustive_adt"},
		{"result of a future, nested patterns cover", `
import std.concurrent as conc

def work(n: int) -> Result[Option[int], str]:
    if n > 0:
        return Ok(Some(n))
    return Err("neg")

def f() -> int:
    pool = conc.ThreadPool(2, 4)
    fut = pool.submit(() => work(3))
    r = fut.await()
    x = 0
    match r:
        Ok(Some(3)) -> x = 1
        Ok(Some(_)) -> x = 2
        Ok(None) -> x = 3
        Err(e) -> x = 4
    pool.shutdown()
    return x
`, ""},
		{"result of a future, a nested variant is missing", `
import std.concurrent as conc

def work(n: int) -> Result[Option[int], str]:
    if n > 0:
        return Ok(Some(n))
    return Err("neg")

def f() -> int:
    pool = conc.ThreadPool(2, 4)
    fut = pool.submit(() => work(3))
    r = fut.await()
    x = 0
    match r:
        Ok(Some(3)) -> x = 1
        Ok(Some(_)) -> x = 2
        Err(e) -> x = 4
    pool.shutdown()
    return x
`, "match_exhaustive_adt"},
		{"a bare None inside Some is a value too", `
def f() -> int:
    o = Some(None)
    x = 0
    match o:
        Some(Some(_)) -> x = 1
        None -> x = 2
    return x
`, "match_exhaustive_adt"},
		{"a bare None is a value of Option", `
def f() -> int:
    o = None
    x = 0
    match o:
        Some(v) -> x = 1
    return x
`, "match_exhaustive_adt"},
		{"bool result of a future, both values", `
import std.concurrent as conc

def work(n: int) -> bool:
    return n > 0

def f() -> int:
    pool = conc.ThreadPool(2, 4)
    fut = pool.submit(() => work(3))
    r = fut.await()
    x = 0
    match r:
        True -> x = 1
        False -> x = 2
    pool.shutdown()
    return x
`, ""},
		{"bool result of a future, one value", `
import std.concurrent as conc

def work(n: int) -> bool:
    return n > 0

def f() -> int:
    pool = conc.ThreadPool(2, 4)
    fut = pool.submit(() => work(3))
    r = fut.await()
    x = 0
    match r:
        True -> x = 1
    pool.shutdown()
    return x
`, "match_exhaustive_bool"},
		{"bool inside the result of a future, one value", `
import std.concurrent as conc

def work(n: int) -> Option[bool]:
    return Some(n > 0)

def f() -> int:
    pool = conc.ThreadPool(2, 4)
    fut = pool.submit(() => work(3))
    r = fut.await()
    x = 0
    match r:
        Some(True) -> x = 1
        None -> x = 2
    pool.shutdown()
    return x
`, "match_exhaustive_adt"},
		{"recursive type, covered", `
type Tree = Leaf(v: int) | Node(l: Tree, r: Tree)

def f(t: Tree) -> int:
    match t:
        Leaf(_) -> return 0
        Node(Leaf(_), Leaf(_)) -> return 1
        Node(Node(_, _), _) -> return 2
        Node(_, Node(_, _)) -> return 2
`, ""},
		{"recursive type, one shape missing", `
type Tree = Leaf(v: int) | Node(l: Tree, r: Tree)

def f(t: Tree) -> int:
    match t:
        Leaf(_) -> return 0
        Node(Leaf(_), Leaf(_)) -> return 1
        Node(Node(_, _), Leaf(_)) -> return 2
    return 3
`, "match_exhaustive_adt"},
	}
	for _, c := range cases {
		failed := strings.Join(failedVCs(verifySrc(t, c.src)), "\n")
		switch {
		case c.wantFailed == "" && failed != "":
			t.Errorf("%s: expected every VC to be proved, failed:\n%s", c.name, failed)
		case c.wantFailed != "" && !strings.Contains(failed, c.wantFailed):
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", c.name, c.wantFailed, failed)
		}
	}
}

// `==` between two booleans says that one holds when the other does. Between
// lists, maps, entities and variants it says nothing the kernel can keep: they
// change in place.
func TestSPARKEqualityOfValuesThatAreNotIntegers(t *testing.T) {
	rejected := map[string]string{
		"boolean changed after the comparison": `
def f(b: bool, c: bool) -> int:
    d = b
    if d == c:
        d = not d
        if d != c:
            return 10 / 0
    return 0
`,
		"list written after the comparison": `
def f(mut xs: list[int], ys: list[int]) -> int:
    if xs == ys:
        if len(xs) > 0:
            xs[0] = 9
        if xs != ys:
            return 10 / 0
    return 0
`,
		"map written after the comparison": `
def f(mut m: map[str, int], k: map[str, int]) -> int:
    if m == k:
        m["a"] = 9
        if m != k:
            return 10 / 0
    return 0
`,
		"variant that holds a list": `
def f(mut xs: list[int], o: Option[list[int]]) -> int:
    p = Some(xs)
    if p == o:
        if len(xs) > 0:
            xs[0] = 9
        if p != o:
            return 10 / 0
    return 0
`,
		"boolean handed back by a call": `
def flip(b: bool) -> bool:
    ensures: result != b
    return not b

def f(b: bool) -> int:
    c = flip(b)
    if c != b:
        return 10 / 0
    return 0
`,
		"two lists that are not the same list": `
def f(xs: list[int], ys: list[int]) -> int:
    if xs == ys:
        return 1
    return 10 / 0
`,
	}
	for name, src := range rejected {
		if failed := strings.Join(failedVCs(verifySrc(t, src)), "\n"); !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	wrong := `
def bad(b: bool) -> bool:
    ensures: result == b
    return not b
`
	if failed := strings.Join(failedVCs(verifySrc(t, wrong)), "\n"); !strings.Contains(failed, "bad.ensures_1") {
		t.Errorf("boolean result that is not what ensures says: expected a failed bad.ensures_1, failed VCs:\n%s", failed)
	}
	proved := map[string]string{
		"boolean equal to a constant": `
def f(b: bool) -> int:
    c = True
    if b == c:
        if not b:
            return 10 / 0
    return 0
`,
		"boolean known to hold": `
def f(b: bool) -> int:
    if b:
        if b == False:
            return 10 / 0
        if b != True:
            return 10 / 0
    return 0
`,
		"two booleans that differ": `
def f(b: bool, c: bool) -> int:
    if b != c:
        if b:
            if c:
                return 10 / 0
    return 0
`,
		"strings": `
def f(s: str, t: str) -> int:
    if s == t:
        if s != t:
            return 10 / 0
    return 0
`,
		"integers": `
def f(n: int, k: int) -> int:
    if n == k:
        return 10 / (n - k + 1)
    return 0
`,
		"boolean result in an ensures clause": `
def same(b: bool) -> bool:
    ensures: result == b
    return b

def flip(b: bool) -> bool:
    ensures: result != b
    return not b

def pos(n: int) -> bool:
    ensures: result == (n > 0)
    return n > 0
`,
		"boolean in a requires clause": `
def g(b: bool, c: bool) -> int:
    requires: b == c
    if b:
        if not c:
            return 10 / 0
    return 0

def f() -> int:
    return g(True, True)
`,
	}
	for name, src := range proved {
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// A name in a pattern is written by the arm that matches: in a loop, and
// after a match expression, the kernel forgets what the variable held.
func TestSPARKPatternNameWritesAVariable(t *testing.T) {
	rejected := map[string]string{
		"match statement in a for": `
def f(os: list[Option[int]]) -> int:
    x = 5
    for o in os:
        match o:
            Some(x) -> print(x)
            None -> print("none")
    return 10 / x
`,
		"match expression in a for": `
def f(os: list[Option[int]]) -> int:
    x = 5
    for o in os:
        r = match o:
            Some(x) -> x
            None -> 0
        print(r)
    return 10 / x
`,
		"match statement in a while": `
def f(o: Option[int], n: int[0..5]) -> int:
    x = 5
    i: int[0..5] = 0
    while i < n:
        match o:
            Some(x) -> print(x)
            None -> print("none")
        i += 1
    return 10 / x
`,
		"match expression, no loop": `
def f(o: Option[int]) -> int:
    x = 5
    r = match o:
        Some(x) -> x
        None -> 0
    return 10 / x
`,
		"match expression written into an element": `
def f(o: Option[int]) -> int:
    x = 5
    xs = [1, 2]
    xs[0] = match o:
        Some(x) -> x
        None -> 0
    return 10 / x
`,
		"a boolean": `
def f(os: list[Option[bool]]) -> int:
    b = True
    for o in os:
        match o:
            Some(b) -> print(b)
            None -> print("none")
    if b:
        return 1
    return 10 / 0
`,
	}
	for name, src := range rejected {
		if failed := strings.Join(failedVCs(verifySrc(t, src)), "\n"); !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	proved := `
def f(os: list[Option[int]]) -> int:
    x = 5
    for o in os:
        match o:
            Some(v) -> print(v)
            None -> print("none")
    return 10 / x
`
	if failed := failedVCs(verifySrc(t, proved)); len(failed) != 0 {
		t.Errorf("a pattern name of its own: expected every VC proved, failed VCs: %v", failed)
	}
	own := `
def f(o: Option[int]) -> int:
    x = 5
    r = match o:
        Some(v) -> v
        None -> 0
    return 10 / x
`
	if failed := failedVCs(verifySrc(t, own)); len(failed) != 0 {
		t.Errorf("a match expression with a name of its own: expected every VC proved, failed VCs: %v", failed)
	}
}

// A list whose length the kernel forgot, in a loop that assigns it or by a
// pattern that names it, is still a list: an index into it is checked
// against a length of which nothing is known.
func TestSPARKIndexIntoAListOfForgottenLength(t *testing.T) {
	rejected := map[string]string{
		"assigned in a loop": `
def f(xs: list[int]) -> int:
    ys = [1, 2]
    for x in xs:
        ys = [1]
    return ys[1]
`,
		"named by a pattern of a match expression": `
def f(o: Option[list[int]]) -> int:
    ys = [1, 2]
    r = match o:
        Some(ys) -> 0
        None -> 0
    return ys[1]
`,
		"named by a pattern in a loop": `
def f(os: list[Option[list[int]]]) -> int:
    ys = [1, 2]
    for o in os:
        match o:
            Some(ys) -> print(1)
            None -> print(0)
    return ys[1]
`,
		"a loop variable": `
def f(xss: list[list[int]]) -> int:
    ys = [1, 2]
    for ys in xss:
        print(1)
    return ys[1]
`,
	}
	for name, src := range rejected {
		if failed := strings.Join(failedVCs(verifySrc(t, src)), "\n"); !strings.Contains(failed, "index_bounds") {
			t.Errorf("%s: expected a failed index_bounds, failed VCs:\n%s", name, failed)
		}
	}
	proved := map[string]string{
		"length tested after the loop": `
def f(xs: list[int]) -> int:
    ys = [1, 2]
    for x in xs:
        ys = [1]
    if len(ys) > 1:
        return ys[1]
    return 0
`,
		"length tested after the match": `
def f(o: Option[list[int]]) -> int:
    ys = [1, 2]
    r = match o:
        Some(ys) -> 0
        None -> 0
    if len(ys) > 1:
        return ys[1]
    return 0
`,
	}
	for name, src := range proved {
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
}

// A variable with a range is taken to be in it at the head of a loop, so
// every value it is given is proved in the range: where it is declared,
// and in each later assignment, to a parameter and a loop variable too.
func TestSPARKVariableKeepsItsRange(t *testing.T) {
	rejected := map[string]string{
		"declared with a value out of range": `
def f(n: int) -> int:
    y: int[1..9] = 0
    i = 0
    while i < n:
        y += 0
        i += 1
    return 10 / y
`,
		"declared with any int": `
def f(n: int) -> int:
    y: int[1..9] = n
    return y
`,
		"assigned out of range": `
def f() -> int:
    y: int[1..9] = 5
    y = 0
    return y
`,
		"a parameter": `
def f(n: int[1..9]) -> int:
    n = 0
    return n
`,
		"a quotient of the variable": `
def f() -> int:
    y: int[1..9] = 1
    y = y / 2
    return y
`,
		"a loop variable, after a loop that assumes its range": `
def f(xs: list[int[1..9]], k: int, m: int) -> int:
    t = 0
    for x in xs:
        a = 0
        while a < k:
            b = 0
            while b < m:
                x += 0
                b += 1
            t = 10 / x
            x = 0
            a += 1
    return t
`,
	}
	for name, src := range rejected {
		if failed := strings.Join(failedVCs(verifySrc(t, src)), "\n"); !strings.Contains(failed, ".let_") {
			t.Errorf("%s: expected a failed let_ VC, failed VCs:\n%s", name, failed)
		}
	}
	proved := map[string]string{
		"a counter": `
def f() -> int:
    i: int[0..10] = 0
    while i < 10:
        i = i + 1
    return 100 / (i + 1)
`,
		"a maximum": `
def f(xs: list[int[0..9]]) -> int:
    m: int[0..9] = 0
    for x in xs:
        if x > m:
            m = x
    return 100 / (m + 1)
`,
		"values in range": `
def one() -> int[1..9]:
    return 4

def f(p: int[2..9], xs: list[int[1..9]]) -> int:
    y: int[1..9] = p
    y = y / 2
    y = one()
    if len(xs) > 0:
        y = xs[0]
    for x in xs:
        y = x
    return 10 / y
`,
	}
	for name, src := range proved {
		if failed := failedVCs(verifySrc(t, src)); len(failed) != 0 {
			t.Errorf("%s: expected every VC proved, failed VCs: %v", name, failed)
		}
	}
	// A quotient is in range by what is known of it, or by the rule for
	// operands that are not negative; the largest int is no upper bound
	// to wrap around.
	quotients := `
def f(n: int[0..100]) -> int:
    a: int[-9..-1] = -4 / 2
    b: int[0..9223372036854775807] = 4 / 1
    c: int[0..9223372036854775807] = n / 1
    d: int[1..9] = 8 / 2
    return a + b + c + d
`
	if failed := failedVCs(verifySrc(t, quotients)); len(failed) != 0 {
		t.Errorf("quotients in range: expected every VC proved, failed VCs: %v", failed)
	}
	for name, src := range map[string]string{
		"a quotient below the range":                     "\ndef f(n: int[0..9]) -> int:\n    y: int[1..9] = 5\n    y = n / 2\n    return y\n",
		"a quotient below a range up to the largest int": "\ndef f(n: int[0..100]) -> int:\n    z: int[5..9223372036854775807] = n / 1\n    return z\n",
	} {
		if failed := strings.Join(failedVCs(verifySrc(t, src)), "\n"); !strings.Contains(failed, ".let_") {
			t.Errorf("%s: expected a failed let_ VC, failed VCs:\n%s", name, failed)
		}
	}
	// A plain assignment in a loop of a variable without a range tells
	// nothing about it at the head.
	plain := `
def f(n: int) -> int:
    y = 5
    i = 0
    while i < n:
        y = 0
        i += 1
    return 10 / y
`
	if failed := strings.Join(failedVCs(verifySrc(t, plain)), "\n"); !strings.Contains(failed, "div_nonzero") {
		t.Errorf("a variable without a range: expected a failed div_nonzero, failed VCs:\n%s", failed)
	}
}

// Out of range a read gives None and a write is dropped, so every index
// into a list or a string is proved inside it: through a field, of a
// string, of a list no variable holds, and where an element is written.
func TestSPARKEveryIndexIsProved(t *testing.T) {
	prelude := `
entity Bag:
    items: list[int]
    name: str

entity Shelf:
    bag: Bag
    n: int[0..9]

def keep(b: Bag) -> Bag:
    return b

def shrink(mut b: Bag) -> int:
    b.items = [1]
    return 0

def one() -> list[int]:
    return [1]
`
	rejected := map[string]string{
		"a field":                  "def f(b: Bag) -> int:\n    return b.items[3]\n",
		"a string":                 "def f(s: str) -> str:\n    return s[5]\n",
		"a string in a field":      "def f(b: Bag) -> str:\n    return b.name[0]\n",
		"a call result":            "def f() -> int:\n    return one()[4]\n",
		"an element of an element": "def f(xss: list[list[int]]) -> int:\n    if len(xss) > 0:\n        return xss[0][2]\n    return 0\n",
		"a write":                  "def f(mut ys: list[int], i: int) -> int:\n    ys[i] = 7\n    return 0\n",
		"a compound write":         "def f(mut ys: list[int[0..9]], i: int) -> int:\n    ys[i] *= 0\n    return 0\n",
		"a write through a field":  "def f(mut b: Bag) -> int:\n    b.items[7] = 1\n    return 0\n",
		"a literal":                "def f() -> int:\n    return [1, 2][2]\n",
		"a string literal":         "def f() -> str:\n    s = \"ab\"\n    return s[2]\n",
		"a constructed field":      "def f() -> int:\n    b = Bag(items=[1, 2], name=\"ab\")\n    return b.items[2]\n",
		"a lambda parameter":       "def f(ws: list[str]) -> list[str]:\n    s = \"hello\"\n    return ws |> map(s => s[4])\n",
		// The length a guard learnt is the length of the value it measured.
		"a field assigned":            "def f(mut b: Bag) -> int:\n    if len(b.items) > 3:\n        b.items = [1]\n        return b.items[3]\n    return 0\n",
		"a field assigned by a name":  "def f(mut b: Bag) -> int:\n    c = b\n    if len(b.items) > 3:\n        c.items = [1]\n        return b.items[3]\n    return 0\n",
		"a field assigned by a call":  "def f(mut b: Bag) -> int:\n    if len(b.items) > 3:\n        z = shrink(mut b)\n        return b.items[3]\n    return 0\n",
		"a field assigned in a loop":  "def f(mut b: Bag, n: int) -> int:\n    if len(b.items) > 3:\n        for i in 0..n:\n            b.items = [1]\n        return b.items[3]\n    return 0\n",
		"a string field assigned":     "def f(mut b: Bag) -> str:\n    b.name = \"ab\"\n    return b.name[2]\n",
		"a string field by a name":    "def f() -> str:\n    b = Bag(items=[1, 2], name=\"ab\")\n    d = b\n    d.name = \"a\"\n    return b.name[1]\n",
		"a field of a kept entity":    "def f() -> str:\n    b = Bag(items=[1, 2], name=\"ab\")\n    d = keep(b)\n    if len(d.name) > 1:\n        b.name = \"a\"\n        return d.name[1]\n    return \"\"\n",
		"a string assigned in an if":  "def f(c: bool) -> str:\n    s = \"hello\"\n    if c:\n        s = \"a\"\n    return s[4]\n",
		"a string assigned in a loop": "def f(xs: list[int]) -> str:\n    s = \"hello\"\n    for x in xs:\n        s = \"a\"\n    return s[4]\n",
		"a loop variable":             "def f(ws: list[str]) -> int:\n    w = \"hello\"\n    for w in ws:\n        print(w[4])\n    return 0\n",
		"a pattern name":              "def f(o: Option[str]) -> str:\n    s = \"hello\"\n    match o:\n        Some(s) -> print(s[4])\n        None -> print(0)\n    return s[4]\n",
		"an entity assigned":          "def f() -> int:\n    b = Bag(items=[1, 2], name=\"ab\")\n    b = keep(Bag(items=[], name=\"\"))\n    return b.items[1]\n",
		"a callee's requires":         "def g(b: Bag) -> int:\n    requires: len(b.items) > 3\n    return b.items[3]\n\ndef f() -> int:\n    b = Bag(items=[1], name=\"n\")\n    return g(b)\n",
	}
	for name, src := range rejected {
		want := "index_bounds"
		if name == "a callee's requires" {
			want = "f.call_g_requires_1"
		}
		if failed := strings.Join(failedVCs(verifySrc(t, prelude+"\n"+src)), "\n"); !strings.Contains(failed, want) {
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", name, want, failed)
		}
	}
	proved := `
def f(b: Bag, s: str, xs: list[int], sh: Shelf) -> int:
    requires: len(xs) > 2
    t = 0
    if len(b.items) > 3:
        t = b.items[3]
    if len(s) > 5:
        print(s[5])
    if len(b.name) > 0:
        print(b.name[0])
    if len(sh.bag.items) > 1:
        t = sh.bag.items[1]
    row = b.items
    if len(row) > 1:
        t = row[1]
    for i in 0..len(xs):
        t = xs[i]
    for i in 0..len(b.items):
        t = b.items[i]
    return xs[2]

def g(mut b: Bag, mut ys: list[int], zs: list[int[0..9]], i: int) -> int:
    if i >= 0 and i < len(ys):
        ys[i] = 7
    if len(b.items) > 7:
        b.items[7] = 1
    o = Bag(items=[1, 2], name="ab")
    print(o.items[1], o.name[1])
    p = o with {items: [1, 2, 3]}
    print(p.items[2], p.name[1])
    s = "hello"
    u = s
    print(s[0], u[4], "abc"[2], [1, 2][1])
    # A string field is as long as the value it is given.
    b.name = "ab"
    print(b.name[1])
    q = b with {name: "xyz"}
    print(q.name[2])
    if len(o.name) > 1:
        b.name = o.name
        print(b.name[1])
    # The list a name was given keeps its length when the field gets another.
    old = b.items
    if len(old) > 3:
        b.items = [1]
        print(old[3])
    return f(o, "abcdef", [1, 2, 3], Shelf(bag=o, n=1))

def h(xss: list[list[int]], o: Option[str], ws: list[str], m: map[str, int]) -> int:
    t = 0
    if len(xss) > 0:
        row = xss[0]
        if len(row) > 2:
            t = row[2]
    match o:
        Some(v) if len(v) > 0 -> print(v[0])
        _ -> print(0)
    for w in ws:
        if len(w) > 0:
            print(w[0])
    # A map is keyed.
    if "a" in m:
        t = m["a"]
        m2: map[str, int] = {}
        m2["b"] = 1
    return t
`
	if failed := failedVCs(verifySrc(t, prelude+proved)); len(failed) != 0 {
		t.Errorf("expected every VC proved, failed VCs: %v", failed)
	}
}

// A map read at a key that is not there gives None, whatever the value
// type says, so every read is proved to find its key: under `k in m`, after
// `m[k] = v`, or a key of the literal. What is known of a key holds for the
// map and the key it was learnt of, and a map only gains keys.
func TestSPARKMapKeyIsPresent(t *testing.T) {
	prelude := `
entity T:
    tbl: map[str, int[1..9]]

def other() -> map[str, int[1..9]]:
    m: map[str, int[1..9]] = {"b": 1}
    return m

def put(mut m: map[str, int[1..9]]) -> int:
    m["a"] = 1
    return 0

def swap(mut b: T) -> int:
    e: map[str, int[1..9]] = {}
    b.tbl = e
    return 0

def g(m: map[str, int[1..9]], k: str) -> int:
    requires: k in m
    return 10 / m[k]

def ga(m: map[str, int[1..9]]) -> int:
    requires: "a" in m
    return 10 / m["a"]

def gt(b: T, c: T) -> int:
    requires: "a" in c.tbl
    return 10 / c.tbl["a"]
`
	rejected := map[string]string{
		"no guard":               "def f(m: map[str, int[1..9]]) -> int:\n    return 10 / m[\"zz\"]\n",
		"another key":            "def f(m: map[str, int[1..9]]) -> int:\n    if \"a\" in m:\n        return 10 / m[\"b\"]\n    return 0\n",
		"a key not in a literal": "def f() -> int:\n    m: map[str, int[1..9]] = {\"a\": 1}\n    return 10 / m[\"b\"]\n",
		"a compound write":       "def f(mut m: map[str, int]) -> int:\n    m[\"zz\"] += 1\n    return 0\n",
		"a guard in one branch":  "def f(m: map[str, int[1..9]], c: bool) -> int:\n    t = 0\n    if c:\n        if \"a\" in m:\n            t = 1\n    return 10 / m[\"a\"]\n",
		"the else branch":        "def f(m: map[str, int[1..9]]) -> int:\n    if \"a\" in m:\n        return 1\n    else:\n        return 10 / m[\"a\"]\n",
		"an int key":             "def f(mi: map[int, int[1..9]], i: int) -> int:\n    requires: i > 0 and i < 100\n    j = i\n    if j in mi:\n        j += 1\n        return 10 / mi[j]\n    return 0\n",
		"a field":                "def f(b: T) -> int:\n    return 10 / b.tbl[\"a\"]\n",
		"a lambda":               "def f(ms: list[map[str, int[1..9]]]) -> list[int]:\n    return ms |> map(m => 10 / m[\"a\"])\n",
		// The map the name holds is another one.
		"the map assigned":          "def f() -> int:\n    m: map[str, int[1..9]] = {\"a\": 1}\n    if \"a\" in m:\n        m = other()\n        return 10 / m[\"a\"]\n    return 0\n",
		"the map assigned in an if": "def f(m: map[str, int[1..9]], n: map[str, int[1..9]], c: bool) -> int:\n    x = m\n    if \"a\" in x:\n        if c:\n            x = n\n        return 10 / x[\"a\"]\n    return 0\n",
		"the map a loop variable":   "def f(ms: list[map[str, int[1..9]]]) -> int:\n    m: map[str, int[1..9]] = {\"a\": 1}\n    for m in ms:\n        print(1)\n    return 10 / m[\"a\"]\n",
		"the field assigned":        "def f(mut b: T) -> int:\n    if \"a\" in b.tbl:\n        e: map[str, int[1..9]] = {}\n        b.tbl = e\n        return 10 / b.tbl[\"a\"]\n    return 0\n",
		"the field by another name": "def f(mut b: T) -> int:\n    c = b\n    if \"a\" in b.tbl:\n        e: map[str, int[1..9]] = {}\n        c.tbl = e\n        return 10 / b.tbl[\"a\"]\n    return 0\n",
		"the field by a callee":     "def f(mut b: T) -> int:\n    if \"a\" in b.tbl:\n        z = swap(mut b)\n        return 10 / b.tbl[\"a\"]\n    return 0\n",
		// The key the name holds is another one.
		"the key assigned":           "def f(m: map[str, int[1..9]]) -> int:\n    k = \"a\"\n    if k in m:\n        k = \"zz\"\n        return 10 / m[k]\n    return 0\n",
		"the key a loop variable":    "def f(m: map[str, int[1..9]], ks: list[str]) -> int:\n    k = \"a\"\n    if k in m:\n        for k in ks:\n            print(k)\n        return 10 / m[k]\n    return 0\n",
		"the key a pattern name":     "def f(m: map[str, int[1..9]], o: Option[str]) -> int:\n    k = \"a\"\n    if k in m:\n        match o:\n            Some(k) -> print(k)\n            None -> print(0)\n        return 10 / m[k]\n    return 0\n",
		"the key a lambda parameter": "def f(m: map[str, int[1..9]], ks: list[str]) -> list[int]:\n    k = \"a\"\n    if k in m:\n        return ks |> map(k => 10 / m[k])\n    return []\n",
		"a key of the loop":          "def f(m: map[str, int[1..9]], ks: list[str]) -> int:\n    t = 0\n    for k in ks:\n        if \"a\" in m:\n            t = 10 / m[k]\n    return t\n",
		// A callee's requires is proved of the map and the key it is given.
		"requires, another map":   "def f(m: map[str, int[1..9]], n: map[str, int[1..9]]) -> int:\n    if \"a\" in m:\n        return ga(n)\n    return 0\n",
		"requires, another key":   "def f(m: map[str, int[1..9]], k: str, w: str) -> int:\n    if k in m:\n        return g(m, w)\n    return 0\n",
		"requires, another field": "def f(b: T, c: T) -> int:\n    if \"a\" in b.tbl:\n        return gt(b, c)\n    return 0\n",
	}
	for name, src := range rejected {
		want := "key_present"
		if strings.HasPrefix(name, "requires") {
			want = "_requires_1"
		}
		if failed := strings.Join(failedVCs(verifySrc(t, prelude+"\n"+src)), "\n"); !strings.Contains(failed, want) {
			t.Errorf("%s: expected a failed %s, failed VCs:\n%s", name, want, failed)
		}
	}
	// A key that was not in the map may be in it after an insertion, by
	// this name, another one, a callee or a loop: the branch is checked.
	reached := map[string]string{
		"this name":    "def f(mut m: map[str, int[1..9]], k: str) -> int:\n    if not (\"z\" in m):\n        m[k] = 1\n        if \"z\" in m:\n            return 10 / 0\n    return 0\n",
		"another name": "def f(mut m: map[str, int[1..9]]) -> int:\n    m2 = m\n    if not (\"a\" in m):\n        m2[\"a\"] = 1\n        if \"a\" in m:\n            return 10 / 0\n    return 0\n",
		"a callee":     "def f(mut m: map[str, int[1..9]]) -> int:\n    if not (\"a\" in m):\n        z = put(mut m)\n        if \"a\" in m:\n            return 10 / 0\n    return 0\n",
		"a loop":       "def f(mut m: map[str, int[1..9]], ks: list[str]) -> int:\n    if not (\"z\" in m):\n        for k in ks:\n            m[k] = 1\n        if \"z\" in m:\n            return 10 / 0\n    return 0\n",
		"a field":      "def f() -> int:\n    m: map[str, int[1..9]] = {\"b\": 1}\n    b = T(tbl=m)\n    if not (\"z\" in b.tbl):\n        m[\"z\"] = 1\n        if \"z\" in b.tbl:\n            return 10 / 0\n    return 0\n",
		"an int key":   "def f(mut mi: map[int, int[1..9]], i: int, j: int) -> int:\n    if not (i in mi):\n        mi[j] = 1\n        if i in mi:\n            return 10 / 0\n    return 0\n",
	}
	// A callee that is given the entity under another name may put another
	// map in the field, or a key in the map, while the statement is read.
	alone := map[string]string{
		"an insertion into the field it replaces": "def one(mut b: T) -> int[1..9]:\n    e: map[str, int[1..9]] = {}\n    b.tbl = e\n    return 1\n\ndef f(mut b: T) -> int:\n    c = b\n    b.tbl[\"a\"] = one(mut c)\n    return 10 / b.tbl[\"a\"]\n",
		"a condition before an insertion":         "def no(mut m: map[str, int[1..9]]) -> bool:\n    m[\"a\"] = 1\n    return False\n\ndef f(mut m: map[str, int[1..9]]) -> int:\n    m2 = m\n    c = \"a\" in m or no(mut m2)\n    if not c:\n        if \"a\" in m:\n            return 10 / 0\n    return 1\n",
	}
	for name, src := range alone {
		if failed := strings.Join(failedVCs(verifySrc(t, prelude+"\n"+src)), "\n"); !strings.Contains(failed, "mut_call_alone") {
			t.Errorf("%s: expected a failed mut_call_alone, failed VCs:\n%s", name, failed)
		}
	}
	for name, src := range reached {
		if failed := strings.Join(failedVCs(verifySrc(t, prelude+"\n"+src)), "\n"); !strings.Contains(failed, "div_nonzero") {
			t.Errorf("%s: expected a failed div_nonzero, failed VCs:\n%s", name, failed)
		}
	}
	proved := `
def f(mut m: map[str, int[1..9]], ks: list[str], mi: map[int, int], i: int, b: T) -> int:
    t = 0
    for k in ks:
        if k in m:
            t = 10 / m[k]
    m["q"] = 3
    t = 10 / m["q"]
    k2 = "w"
    m[k2] = 4
    t = m[k2] + m["q"]
    if "a" in m:
        # What was found stays found when the map gains a key.
        m["b"] = 2
        z = put(mut m)
        m["a"] += 1 - 1
        t = m["a"] + m["b"]
        t = ga(m)
        t = g(m, k2)
    if i in mi:
        t = mi[i]
        j = i
        t = mi[j]
    if "a" in b.tbl and "b" in b.tbl:
        t = b.tbl["a"] + b.tbl["b"]
        t = gt(b, b)
    lit: map[str, int] = {"x": 1, "y": 2}
    lit["z"] = 3
    al = lit
    al["u"] = 4
    print(lit["x"], lit["y"], lit["z"], al["u"])
    mn: map[int, int] = {1: 5}
    print(mn[1])
    # A closure reads the map and the key it was made with.
    x = m
    if k2 in x:
        h = () => 10 / x[k2]
        x = other()
        t = h()
    return t
`
	if failed := failedVCs(verifySrc(t, prelude+proved)); len(failed) != 0 {
		t.Errorf("expected every VC proved, failed VCs: %v", failed)
	}
}
