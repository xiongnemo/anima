package lts

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
)

func verifyLTS(t *testing.T, src string) *Report {
	t.Helper()
	prog, err := parser.Parse("lts_test.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema error: %v", err)
	}
	return Verify(info)
}

func TestSingleLaneBridgeValid(t *testing.T) {
	src := `
machine RedCar:
    state OffBridge:
        on red_enter -> OnBridge
    state OnBridge:
        on red_exit -> OffBridge

machine BlueCar:
    state OffBridge:
        on blue_enter -> OnBridge
    state OnBridge:
        on blue_exit -> OffBridge

monitor BridgeController:
    n_red: control int[0..1] = 0
    n_blue: control int[0..1] = 0

    state Empty:
        invariant: n_red == 0 and n_blue == 0
        on red_enter when n_blue == 0 -> RedCrossing:
            n_red = 1
        on blue_enter when n_red == 0 -> BlueCrossing:
            n_blue = 1

    state RedCrossing:
        invariant: n_red == 1 and n_blue == 0
        on red_exit -> Empty:
            n_red = 0

    state BlueCrossing:
        invariant: n_blue == 1 and n_red == 0
        on blue_exit -> Empty:
            n_blue = 0

property OneWaySafety:
    state Empty:
        on red_enter -> RedBusy
        on blue_enter -> BlueBusy
    state RedBusy:
        on red_exit -> Empty
    state BlueBusy:
        on blue_exit -> Empty

progress RedCrosses = {red_enter}
progress BlueCrosses = {blue_enter}

system BridgeSystem:
    compose:
        red: RedCar
        blue: BlueCar
        ctrl: BridgeController
    check:
        deadlock_free
        satisfies OneWaySafety
        satisfies RedCrosses
        satisfies BlueCrosses
        ltl: always (red_enter -> eventually red_exit)
`
	rep := verifyLTS(t, src)
	if !rep.OK() {
		t.Fatalf("expected SingleLaneBridge to pass all checks, got: %v", rep.Errors())
	}
	if len(rep.Systems) != 1 || rep.Systems[0].NumStates == 0 {
		t.Fatalf("unexpected system stats: %+v", rep.Systems)
	}
}

func TestCatchesSafetyErrorAndDiningPhilosophersDeadlock(t *testing.T) {
	// 1. Safety ERROR(-1) violation: controller allows blue while red still on bridge
	repSafety := verifyLTS(t, `
machine RedCar:
    state Off:
        on red_enter -> On
    state On:
        on red_exit -> Off

machine BlueCar:
    state Off:
        on blue_enter -> On
    state On:
        on blue_exit -> Off

monitor BrokenBridge:
    state Any:
        on red_enter -> Any
        on blue_enter -> Any
        on red_exit -> Any
        on blue_exit -> Any

property OneWaySafety:
    state Empty:
        on red_enter -> RedBusy
        on blue_enter -> BlueBusy
    state RedBusy:
        on red_exit -> Empty
    state BlueBusy:
        on blue_exit -> Empty

system BrokenSys:
    compose:
        red: RedCar
        blue: BlueCar
        ctrl: BrokenBridge
    check:
        satisfies OneWaySafety
`)
	if repSafety.OK() {
		t.Fatalf("expected OneWaySafety violation")
	}
	if !strings.Contains(strings.Join(repSafety.Errors(), "\n"), "ERROR=-1") {
		t.Fatalf("expected ERROR=-1 diagnostic, got: %v", repSafety.Errors())
	}

	// 2. Classic Dining Philosophers Deadlock
	repDead := verifyLTS(t, `
machine Fork:
    state Free:
        on get -> Taken
    state Taken:
        on put -> Free

machine Philosopher:
    state Thinking:
        on left.get -> HoldLeft
    state HoldLeft:
        on right.get -> Eating
    state Eating:
        on left.put -> PutRight
    state PutRight:
        on right.put -> Thinking

system Diners:
    compose:
        f0: Fork
        f1: Fork
        p0: Philosopher(left=f0, right=f1)
        p1: Philosopher(left=f1, right=f0)
    check:
        deadlock_free
`)
	if repDead.OK() {
		t.Fatalf("expected Dining Philosophers deadlock!")
	}
	if !strings.Contains(strings.Join(repDead.Errors(), "\n"), "DEADLOCK") {
		t.Fatalf("expected DEADLOCK error, got: %v", repDead.Errors())
	}
}

func TestCatchesProgressStarvationAndLTLAndTypestateLeaks(t *testing.T) {
	// 1. Progress violation under priority_low starvation
	repProg := verifyLTS(t, `
machine Worker:
    state Ready:
        on busy_spin -> Ready
        on serve -> Ready

progress MustServe = {serve}

system StarveSys:
    compose:
        w: Worker
    priority_low: [serve]
    check:
        satisfies MustServe
        ltl: always (busy_spin -> eventually serve)
`)
	if repProg.OK() {
		t.Fatalf("expected progress & LTL starvation failure")
	}
	if len(repProg.Systems[0].Failures) < 2 {
		t.Fatalf("expected both Progress and LTL failures, got %+v", repProg.Systems[0].Failures)
	}

	// 2. Socket handle leak on early return branch
	repLeak := verifyLTS(t, `
import std.socket as sock

def bad_server(flag: bool) -> Result[int, str]:
    listener = sock.listen_tcp("127.0.0.1", 8080)?
    if flag:
        return Ok(1)
    listener.close()
    return Ok(0)
`)
	if repLeak.OK() {
		t.Fatalf("expected socket handle leak on flag=true branch")
	}
	if !strings.Contains(strings.Join(repLeak.Errors(), "\n"), "resource handle leak") {
		t.Fatalf("expected resource handle leak diagnostic, got: %v", repLeak.Errors())
	}

	// 3. Socket use-after-close
	repUAF := verifyLTS(t, `
import std.socket as sock

def bad_uaf() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 8080)?
    conn.close()
    conn.send_text("hello")?
    return Ok(0)
`)
	if repUAF.OK() {
		t.Fatalf("expected socket use-after-close error")
	}
	if !strings.Contains(strings.Join(repUAF.Errors(), "\n"), "use-after-close") {
		t.Fatalf("expected use-after-close diagnostic, got: %v", repUAF.Errors())
	}
}

// abs, min and max in a monitor are what they are in a function. The model
// read each as 0: `abs(n - 3) == 2` was never true and `abs(n - 3) == 0`
// always, so a transition the monitor takes was left out of the model and
// one it never takes was in it.
func TestAbsMinMaxInAMonitor(t *testing.T) {
	// With n == 1, the car stops for good after one `go` exactly where
	// the guard holds; where it does not, it goes on for ever.
	const guarded = `
machine Car:
    state A:
        on go -> A

monitor Gate:
    n: control int[0..3] = INIT

    state S:
        on go when GUARD -> T
        on go when not (GUARD) -> S
    state T:
        on stop -> T

system Sys:
    compose:
        car: Car
        gate: Gate
    check:
        deadlock_free
`
	// The gate counts with ASSIGN while n < 3, and then lets no `go` by.
	const counted = `
machine Car:
    state A:
        on go -> A

monitor Gate:
    n: control int[0..3] = 0

    state S:
        on go when n < 3 -> S:
            n = ASSIGN

system Sys:
    compose:
        car: Car
        gate: Gate
    check:
        deadlock_free
`
	for _, c := range []struct {
		src, hole, expr string
		stops           bool
	}{
		{guarded, "GUARD", "abs(n - 3) == 2", true},
		{guarded, "GUARD", "abs(n - 3) == 0", false},
		{guarded, "GUARD", "abs(n) == n and abs(0 - n) == n", true},
		{guarded, "GUARD", "min(n, 5) == 1", true},
		{guarded, "GUARD", "min(n, 0 - 5) == 1", false},
		{guarded, "GUARD", "min(n, 0) == 0", true},
		{guarded, "GUARD", "max(n, 2) == 2", true},
		{guarded, "GUARD", "max(n, 0) == 0", false},
		{guarded, "GUARD", "max(2, n) > min(2, n)", true},
		{guarded, "GUARD", "min(max(n, 2), 3) - abs(n - 2) == 1", true},
		{guarded, "INIT", "min(3, 5)", false},
		{guarded, "INIT", "max(0, 1)", true},
		{guarded, "INIT", "abs(0 - 1)", true},
		{counted, "ASSIGN", "min(n + 1, 3)", true},
		{counted, "ASSIGN", "max(n + 1, abs(0 - 3))", true},
		{counted, "ASSIGN", "min(n, 2)", false},
		{counted, "ASSIGN", "abs(n - 1) - 1", false},
	} {
		src := strings.Replace(c.src, c.hole, c.expr, -1)
		src = strings.Replace(strings.Replace(src, "INIT", "1", 1), "GUARD", "n == 1", -1)
		rep := verifyLTS(t, src)
		if len(rep.Systems) != 1 {
			t.Fatalf("%s: %d systems", c.expr, len(rep.Systems))
		}
		if stopped := !rep.OK(); stopped != c.stops {
			t.Errorf("%s as %s: deadlock %v, want %v: %v", c.expr, c.hole, stopped, c.stops, rep.Errors())
		}
	}
}
