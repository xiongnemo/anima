package spark

import (
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
