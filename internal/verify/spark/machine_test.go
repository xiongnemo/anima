package spark

import (
	"strings"
	"testing"
)

// An invariant of a state is worked out by the LTS kernel wherever a machine
// arrives in the state, so it is proved to have a value there: no division
// by zero, no shift by a count outside 0..63, no overflow.
func TestSPARKMachineInvariantHasAValue(t *testing.T) {
	const src = `monitor Gate:
    n: control int[0..3] = INIT

    state S:
        INV
        on go when n < 2 -> S:
            n = n + 1
        on go when n >= 2 -> S
`
	for _, c := range []struct{ init, inv, fails string }{
		{"0", "invariant: n < 3\n        invariant: 1 << (2 - n) >= 1", ""},
		{"0", "invariant: n < 3 and 1 << (2 - n) >= 1", ""},
		{"0", "invariant: n >= 3 or 8 >> (2 - n) >= 0", ""},
		// The invariants of S hold where a transition leaves it, so in either
		// order n is at most 2 where one arrives.
		{"0", "invariant: 1 << (2 - n) >= 1\n        invariant: n < 3", ""},
		// With nothing known of n in S, it arrives with n = 3.
		{"0", "invariant: 1 << (2 - n) >= 1", "monitor:Gate.shift_count"},
		{"0", "invariant: n < 3 or 1 << (2 - n) >= 1", "monitor:Gate.shift_count"},
		{"0", "invariant: 10 / (n - 3) <= 10", "monitor:Gate.div_nonzero"},
		{"0", "invariant: 10 % (n - 3) <= 10", "monitor:Gate.div_nonzero"},
		{"0", "invariant: n * 9223372036854775807 >= 0", "monitor:Gate.int64_overflow"},
		{"0", "invariant: abs(n - 9223372036854775807 - 4) >= 0", "monitor:Gate.int64_overflow"},
		// The first state, with the first values.
		{"3", "invariant: 10 / (n - 3) <= 10", "monitor:Gate.div_nonzero"},
	} {
		rep := verifySrc(t, strings.NewReplacer("INIT", c.init, "INV", c.inv).Replace(src))
		failed := strings.Join(failedVCs(rep), " ")
		if c.fails == "" && failed != "" {
			t.Errorf("init %s, %q: %v", c.init, c.inv, rep.Errors())
		}
		if c.fails != "" && !strings.Contains(failed, c.fails) {
			t.Errorf("init %s, %q: want %s to fail, got %q", c.init, c.inv, c.fails, failed)
		}
	}
}

// A control variable with no first value written starts at the least of its
// range, which is where the LTS kernel starts it, and the invariants of the
// first state are proved of that value and of no other.
func TestSPARKMachineFirstValueNotWritten(t *testing.T) {
	const src = `monitor Gate:
    n: control int[LO..3]

    state S:
        INV
        on go -> S
`
	for _, c := range []struct{ lo, inv, fails string }{
		{"0", "invariant: n + 1 > n", ""},
		{"1", "invariant: 6 / n <= 6", ""},
		{"2", "invariant: n == 2\n        invariant: 1 << (2 - n) == 1", ""},
		{"0", "invariant: 6 / n <= 6", "monitor:Gate.div_nonzero"},
		{"1", "invariant: n == 2", "Gate.init.S_invariant"},
		{"3", "invariant: n == 2\n        invariant: 1 << (2 - n) == 1", "Gate.init.S_invariant"},
	} {
		rep := verifySrc(t, strings.NewReplacer("LO", c.lo, "INV", c.inv).Replace(src))
		failed := strings.Join(failedVCs(rep), " ")
		if c.fails == "" && failed != "" {
			t.Errorf("from %s, %q: %v", c.lo, c.inv, rep.Errors())
		}
		if c.fails != "" && !strings.Contains(failed, c.fails) {
			t.Errorf("from %s, %q: want %s to fail, got %q", c.lo, c.inv, c.fails, failed)
		}
	}
}
