package lts

import (
	"math"
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
)

// machineOf compiles the machine or monitor name of src.
func machineOf(t *testing.T, src, name string) *ComponentLTS {
	t.Helper()
	prog, err := parser.Parse("lts_test.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema error: %v", err)
	}
	comp, err := CompileMachine(info.Machines[name], info)
	if err != nil {
		t.Fatalf("CompileMachine(%s): %v", name, err)
	}
	return comp
}

// An action a part names is one it takes part in, where it can make it or
// not. A guard that never holds and a state that is never reached took the
// action out of the alphabet, and the rest of the system then did it alone.
func TestAnActionThatIsNeverOfferedIsStillInTheAlphabet(t *testing.T) {
	const car = `machine Car:
    state A:
        on go -> A

`
	const sys = `
system Sys:
    compose:
        car: Car
        gate: Gate
    check:
        CHECK
`
	gates := map[string]string{
		"a guard that holds nowhere": `monitor Gate:
    n: control int[0..3] = 0
    state S:
        on go when n > 5 -> S
`,
		"a guard that is False": `monitor Gate:
    state S:
        on go when False -> S
`,
		"a state that is not reached": `monitor Gate:
    state S:
        on other -> S
    state U:
        on go -> U
`,
		"a machine and no monitor": `machine Gate:
    state S:
        on other -> S
    state U:
        on go -> U
`,
	}
	const noGo = `
property NoGo:
    state P:
        on go -> ERROR
`
	for name, gate := range gates {
		src := car + gate + noGo + sys
		comp := machineOf(t, strings.Replace(src, "CHECK", "deadlock_free", 1), "Gate")
		if !comp.Alphabet["go"] || !comp.BaseAlpha["go"] {
			t.Errorf("%s: go is not in the alphabet %v", name, comp.Alphabet)
		}
		for _, es := range comp.Edges {
			for _, e := range es {
				if e.Action == "go" {
					t.Errorf("%s: the gate has an edge on go", name)
				}
			}
		}

		// A monitor does nothing by itself, so nothing happens at all; a
		// machine goes on with what else it does.
		rep := verifyLTS(t, strings.Replace(src, "CHECK", "deadlock_free", 1))
		if got := strings.Join(rep.Errors(), "\n"); strings.Contains(got, "DEADLOCK") != strings.HasPrefix(gate, "monitor") {
			t.Errorf("%s: deadlock_free gives %q", name, got)
		}
		rep = verifyLTS(t, strings.Replace(src, "CHECK", "satisfies NoGo", 1))
		if !rep.OK() {
			t.Errorf("%s: go is said to happen: %v", name, rep.Errors())
		}
		for _, es := range rep.Systems[0].SysLTS.Edges {
			for _, e := range es {
				if strings.Contains(e.Action, "go") {
					t.Errorf("%s: the system has an edge on %s", name, e.Action)
				}
			}
		}
	}

	// One that is offered somewhere is made there and nowhere else.
	rep := verifyLTS(t, car+`monitor Gate:
    n: control int[0..2] = 0
    state S:
        on go when n < 2 -> S:
            n += 1
`+strings.Replace(sys, "CHECK", "deadlock_free", 1))
	if got := strings.Join(rep.Errors(), "\n"); !strings.Contains(got, "DEADLOCK at state 2 [car=A, gate=S[n=2]]") {
		t.Errorf("want a deadlock after two go, got %q", got)
	}
}

// A part bound to another (`left=f0`) and a workflow that syncs with a
// monitor are held back in the same way.
func TestAnActionThatIsNeverOfferedHoldsBackWhatIsBoundToIt(t *testing.T) {
	for name, c := range map[string]struct{ src, want string }{
		"bound part, unreachable state": {`machine Fork:
    state Free:
        on put -> Free
    state Taken:
        on get -> Taken

machine Phil:
    state T:
        on left.get -> T

system Sys:
    compose:
        f0: Fork
        p0: Phil(left=f0)
    check:
        deadlock_free
`, "DEADLOCK at state 0 [f0=Free, p0=T]"},
		"bound part, the action under another name": {`machine Fork:
    state Free:
        on get -> Free

machine Phil:
    state T:
        on left.get -> T

system Sys:
    compose:
        f0: Fork / {get -> grab}
        p0: Phil(left=f0)
    check:
        deadlock_free
`, "DEADLOCK at state 0 [f0=Free, p0=T]"},
		"workflow sync": {`monitor Gate:
    n: control int[0..1] = 0
    state S:
        on go when n > 5 -> S

workflow W() -> bool:
    start -> a:
        ok = True
    fork a:
        branch b1:
            sync Gate.go
        branch b2:
            sync Gate.go
    join j
    step fin after j -> done:
        return True

system Sys:
    compose:
        w: W
        gate: Gate
    check:
        deadlock_free
`, "DEADLOCK"},
	} {
		rep := verifyLTS(t, c.src)
		if got := strings.Join(rep.Errors(), "\n"); !strings.Contains(got, c.want) {
			t.Errorf("%s: want %q, got %q", name, c.want, got)
		}
	}
}

// An instance has the actions of its machine under the names it gives them:
// one relabelled away is no longer shared, and the new name is.
func TestRelabelledAlphabet(t *testing.T) {
	const src = `machine A:
    state S:
        on a -> S

machine B:
    state S:
        on a when False -> S

property NoA:
    state P:
        on a -> ERROR

system Sys:
    compose:
        x: A
        y: B RELABEL
    check:
        satisfies NoA
`
	// y names a and never offers it: x cannot do a.
	if rep := verifyLTS(t, strings.Replace(src, " RELABEL", "", 1)); !rep.OK() {
		t.Errorf("no relabel: %v", rep.Errors())
	}
	// y names b now, and x does a alone.
	rep := verifyLTS(t, strings.Replace(src, "RELABEL", "/ {a -> b}", 1))
	if got := strings.Join(rep.Errors(), "\n"); !strings.Contains(got, `PROPERTY NoA VIOLATED (ERROR=-1): action "a" illegal`) {
		t.Errorf("a -> b: want a violation of NoA, got %q", got)
	}

	// The other way: y's b becomes a, which it never offers.
	other := strings.Replace(strings.Replace(src, "on a when False", "on b when False", 1), "RELABEL", "/ {b -> a}", 1)
	if rep := verifyLTS(t, other); !rep.OK() {
		t.Errorf("b -> a: %v", rep.Errors())
	}
}

// What an action is done with is in the name the instance gives it, and not
// in the name its machine is written with.
func TestRelabelledActionIsDoneWithWhatItsNewNameNames(t *testing.T) {
	const gate = `monitor Gate:
    state S:
        on go when False -> S

`
	for name, c := range map[string]struct{ src, want string }{
		// Gate.go is go now, and no Gate is asked for.
		"a monitor's action to a plain one, no monitor": {gate + `machine Car:
    state A:
        on Gate.go -> A

system Sys:
    compose:
        car: Car / {Gate.go -> go}
    check:
        deadlock_free
`, ""},
		"a monitor's action to another plain one, the monitor there": {gate + `machine Car:
    state A:
        on Gate.go -> A

system Sys:
    compose:
        car: Car / {Gate.go -> other}
        gate: Gate
    check:
        deadlock_free
`, ""},
		"a monitor's action to the plain one the monitor has": {gate + `machine Car:
    state A:
        on Gate.go -> A

system Sys:
    compose:
        car: Car / {Gate.go -> go}
        gate: Gate
    check:
        deadlock_free
`, "DEADLOCK at state 0 [car=A, gate=S]"},
		"a part that is not there, to a plain one": {`machine Car:
    state A:
        on missing.go -> A

system Sys:
    compose:
        car: Car / {missing.go -> go}
    check:
        deadlock_free
`, ""},
		// go is Gate.go now, and is done with the monitor.
		"a plain action to a monitor's": {gate + `machine Car:
    state A:
        on go -> A

system Sys:
    compose:
        car: Car / {go -> Gate.go}
        gate: Gate / {go -> run}
    check:
        deadlock_free
`, "DEADLOCK at state 0 [car=A, gate=S]"},
		"a plain action to a monitor's, no monitor": {gate + `machine Car:
    state A:
        on go -> A

system Sys:
    compose:
        car: Car / {go -> Gate.go}
    check:
        deadlock_free
`, "car of system Sys does Gate.go with Gate, which is a monitor the system has no part of"},
	} {
		rep := verifyLTS(t, c.src)
		got := strings.Join(rep.Errors(), "\n")
		if c.want == "" && !rep.OK() {
			t.Errorf("%s: %v", name, got)
		}
		if c.want != "" && !strings.Contains(got, c.want) {
			t.Errorf("%s: want %q, got %q", name, c.want, got)
		}
	}
}

// A `sync Gate.go` of a workflow has the name Gate.go, and stays an action
// done with a part: what a workflow does alone no other part holds back.
func TestRelabelledWorkflow(t *testing.T) {
	const src = `monitor Gate:
    state S:
        on go when False -> S
        on run -> S

workflow W() -> bool:
    start -> a:
        ok = True
    fork a:
        branch b1:
            sync Gate.go
        branch b2:
            sync Gate.go
    join j
    step fin after j -> done:
        return True

workflow P() -> bool:
    start -> fin:
        ok = True
    step fin -> done:
        return True

system Sys:
    compose:
        w: PART
        gate: Gate
    check:
        deadlock_free
`
	for part, want := range map[string]string{
		"W":                         "DEADLOCK at state 1 [w=a, gate=S]",
		"W / {Gate.go -> Gate.run}": "",
		"W / {go -> run}":           "w of system Sys relabels go, which is no action of W",
		"W / {nope -> run}":         "w of system Sys relabels nope, which is no action of W",
		"W / {Gate.go -> go}":       "w of system Sys relabels Gate.go to go: a workflow does with a part what it is written to do with one",
		"W / {Gate.go -> Door.go}":  "w of system Sys does Door.go with Door, which is bound to no part of the system",
		"P":                         "",
		"P / {fin -> Gate.run}":     "",
		"P / {fin -> Gate.go}":      "DEADLOCK",
	} {
		rep := verifyLTS(t, strings.Replace(src, "PART", part, 1))
		got := strings.Join(rep.Errors(), "\n")
		if want == "" && !rep.OK() {
			t.Errorf("%s: %v", part, got)
		}
		if want != "" && !strings.Contains(got, want) {
			t.Errorf("%s: want %q, got %q", part, want, got)
		}
	}
}

// What an action is done with is a part of the system. An action of a part
// that is not there was done alone, as often as its doer liked.
func TestSystemNamesOnlyItsParts(t *testing.T) {
	const gate = `monitor Gate:
    state S:
        on go when False -> S

`
	for name, c := range map[string]struct{ src, want string }{
		"machine, monitor not in the system": {gate + `machine Car:
    state A:
        on Gate.go -> A

system Sys:
    compose:
        car: Car
    check:
        deadlock_free
`, "car of system Sys does Gate.go with Gate, which is a monitor the system has no part of"},
		"workflow, monitor not in the system": {gate + `workflow W() -> bool:
    start -> a:
        ok = True
    fork a:
        branch b1:
            sync Gate.go
        branch b2:
            sync Gate.go
    join j
    step fin after j -> done:
        return True

system Sys:
    compose:
        w: W
    check:
        deadlock_free
`, "w of system Sys does Gate.go with Gate, which is a monitor the system has no part of"},
		"workflow, a machine and no monitor": {`machine Gate:
    state S:
        on go -> S

workflow W() -> bool:
    start -> a:
        ok = True
    fork a:
        branch b1:
            sync Gate.go
        branch b2:
            sync Gate.go
    join j
    step fin after j -> done:
        return True

system Sys:
    compose:
        w: W
        gate: Gate
    check:
        deadlock_free
`, "w of system Sys does Gate.go with Gate, which is a machine and no monitor"},
		"a name that is bound to nothing": {`machine Fork:
    state Free:
        on get -> Free

machine Phil:
    state T:
        on left.get -> U
    state U:
        on right.get -> T

system Sys:
    compose:
        f0: Fork
        p0: Phil(left=f0)
    check:
        deadlock_free
`, "p0 of system Sys does right.get with right, which is bound to no part of the system"},
		"bound to a part that is not there": {`machine Fork:
    state Free:
        on get -> Free

machine Phil:
    state T:
        on left.get -> T

system Sys:
    compose:
        f0: Fork
        p0: Phil(left=f9)
    check:
        deadlock_free
`, "p0 of system Sys is bound to f9, which is no other part of the system"},
		"bound to itself": {`machine Phil:
    state T:
        on left.get -> T

system Sys:
    compose:
        p0: Phil(left=p0)
    check:
        deadlock_free
`, "p0 of system Sys is bound to p0, which is no other part of the system"},
		"a part others call calls a part": {`machine Fork:
    state Free:
        on get -> Taken
    state Taken:
        on b.put -> Free

machine Phil:
    state T:
        on left.get -> H
    state H:
        on left.put -> T

machine B:
    state S:
        on put when False -> S

system Sys:
    compose:
        f0: Fork
        b: B
        p0: Phil(left=f0)
    check:
        deadlock_free
`, "f0 of system Sys does b.put, and other parts do their actions with it: it moves only with the part that calls it, and calls none"},
		"a monitor calls a part": {`monitor Gate:
    state S:
        on car.go -> S

machine Car:
    state A:
        on go -> A

system Sys:
    compose:
        car: Car
        gate: Gate
    check:
        deadlock_free
`, "gate of system Sys does car.go, and it is a monitor: it moves only with the part that calls it, and calls none"},
		"two monitors of the type an action names": {`monitor Gate:
    state S:
        on go -> T
    state T:
        on stop -> T

machine Car:
    state A:
        on Gate.go -> A

system Sys:
    compose:
        car: Car
        g1: Gate / {go -> stop}
        g2: Gate
    check:
        deadlock_free
`, "car of system Sys does Gate.go with the monitor Gate, and the system has two: g1 and g2"},
		"an action with itself": {`machine A:
    state S:
        on a.go -> S
        on go -> S

system Sys:
    compose:
        a: A
    check:
        deadlock_free
`, "a of system Sys does a.go with itself"},
		// The forks are named and not bound: they are taken and put down by
		// the philosophers and by no one else, so the two are found stuck.
		"a part named in an action moves only with its caller": {`machine Fork:
    state Free:
        on get -> Taken
    state Taken:
        on put -> Free

machine PhilA:
    state T:
        on f0.get -> H
    state H:
        on f1.get -> E
    state E:
        on f0.put -> P
    state P:
        on f1.put -> T

machine PhilB:
    state T:
        on f1.get -> H
    state H:
        on f0.get -> E
    state E:
        on f1.put -> P
    state P:
        on f0.put -> T

system Sys:
    compose:
        f0: Fork
        f1: Fork
        a: PhilA
        b: PhilB
    check:
        deadlock_free
`, "DEADLOCK at state 4 [f0=Taken, f1=Taken, a=H, b=H]"},
	} {
		rep := verifyLTS(t, c.src)
		if got := strings.Join(rep.Errors(), "\n"); !strings.Contains(got, c.want) {
			t.Errorf("%s: want %q, got %q", name, c.want, got)
		}
	}

	// A workflow calls methods of its values, which are no parts.
	rep := verifyLTS(t, `import std.concurrent as conc

workflow W() -> int:
    start -> a:
        ch = conc.Channel(cap=2)
    step a -> fin:
        ch.send(1)
    step fin -> done:
        return 0

system Sys:
    compose:
        w: W
    check:
        deadlock_free
`)
	if !rep.OK() {
		t.Errorf("a method call in a workflow: %v", rep.Errors())
	}
}

// guardOf is the guard `when EXPR` as the parser reads it, with no check by
// sema: the kernel is asked what it makes of every form.
func guardOf(t *testing.T, expr string) ast.Expr {
	t.Helper()
	prog, err := parser.Parse("lts_test.anm", "monitor M:\n    state S:\n        on go when "+expr+" -> S\n")
	if err != nil {
		t.Fatalf("%s: parse error: %v", expr, err)
	}
	return prog.Decls[0].(*ast.MachineDecl).States[0].Transitions[0].Guard
}

func TestModelValues(t *testing.T) {
	env := map[string]int64{"n": 3, "z": 0, "neg": -7, "big": math.MaxInt64, "least": math.MinInt64}
	for _, c := range []struct {
		expr string
		want int64
	}{
		{"7", 7}, {"n", 3}, {"-n", -3}, {"~n", -4}, {"~least", math.MaxInt64},
		{"n + 4", 7}, {"n - 4", -1}, {"n * neg", -21}, {"neg * neg", 49},
		{"neg / 2", -3}, {"neg % 2", -1}, {"7 / n", 2}, {"7 % n", 1},
		{"big + z", math.MaxInt64}, {"least - z", math.MinInt64}, {"big + least", -1},
		{"least + big", -1}, {"z - big", -math.MaxInt64}, {"neg - least", math.MaxInt64 - 6},
		{"least / 1", math.MinInt64}, {"least % 1", 0},
		{"4611686018427387904 * -2", math.MinInt64}, {"least * 1", math.MinInt64}, {"big * -1", -math.MaxInt64},
		{"n & 6", 2}, {"n | 4", 7}, {"n ^ 1", 2}, {"neg & 255", 249},
		{"n << 2", 12}, {"neg >> 1", -4}, {"1 << 62", 1 << 62}, {"-1 << 63", math.MinInt64}, {"least >> 63", -1},
		{"n << 0", 3}, {"big >> 0", math.MaxInt64},
		{"abs(neg)", 7}, {"abs(n)", 3}, {"abs(-big)", math.MaxInt64},
		{"min(n, neg)", -7}, {"max(n, neg)", 3}, {"min(max(n, 0), 2)", 2},
	} {
		// The guard is `EXPR == 0`, and its left side the int.
		e := guardOf(t, "("+c.expr+") == 0").(*ast.BinaryExpr).Left
		got, err := evalInt(e, env)
		if err != nil || got != c.want {
			t.Errorf("%s = %d, %v; want %d", c.expr, got, err, c.want)
		}
	}

	for _, c := range []struct {
		expr string
		want bool
	}{
		{"True", true}, {"False", false}, {"not False", true},
		{"n == 3", true}, {"n != 3", false}, {"n < 3", false}, {"n <= 3", true}, {"n > neg", true}, {"n >= 4", false},
		{"n == 3 and neg < 0", true}, {"n == 3 and neg > 0", false},
		{"n == 4 or neg < 0", true}, {"n == 4 or neg > 0", false},
		{"n == 3 implies neg > 0", false}, {"n == 4 implies neg > 0", true}, {"n == 3 implies neg < 0", true},
		{"(n == 3) == True", true}, {"(n == 3) == (neg > 0)", false}, {"(n == 4) != (neg < 0)", true},
		{"True == (n == 3)", true}, {"not (n == 3) == False", true}, {"(not (n == 3)) == False", true},
		// The right side is worked out only where it is run.
		{"z == 0 or 1 / z > 0", true}, {"z != 0 and 1 / z > 0", false}, {"z != 0 implies 1 / z > 0", true},
		{"not (z != 0 and 1 << 64 > 0)", true},
	} {
		got, err := evalBool(guardOf(t, c.expr), env)
		if err != nil || got != c.want {
			t.Errorf("%s = %v, %v; want %v", c.expr, got, err, c.want)
		}
	}
}

// What has no value, and what the kernel does not work out, is an error.
// Each of these was the int 0 or the bool False.
func TestModelHasNoValueForWhatItDoesNotWorkOut(t *testing.T) {
	env := map[string]int64{"n": 3, "z": 0, "big": math.MaxInt64, "least": math.MinInt64}
	for _, c := range []struct{ expr, want string }{
		{"1 / z == 0", "a division by zero"},
		{"1 % z == 0", "a division by zero"},
		{"least / -1 == 0", "/ overflows"},
		{"least % -1 == 0", "% overflows"},
		{"big + 1 == 0", "+ overflows"},
		{"least + -1 == 0", "+ overflows"},
		{"least - 1 == 0", "- overflows"},
		{"z - least == 0", "- overflows"},
		{"big * 2 == 0", "* overflows"},
		{"least * -1 == 0", "* overflows"},
		{"4611686018427387904 * 2 == 0", "* overflows"},
		{"-least == 0", "the negation of the least int overflows"},
		{"abs(least) == 0", "abs of the least int overflows"},
		{"1 << 64 == 0", "a shift by 64, which is outside 0..63,"},
		{"1 >> 64 == 0", "a shift by 64, which is outside 0..63,"},
		{"1 << -1 == 0", "a shift by -1, which is outside 0..63,"},
		{"1 << 63 == 0", "<< overflows"},
		{"n << 62 == 0", "<< overflows"},
		{"z == 0 and 1 / z > 0", "a division by zero"},
		{"z != 0 or 1 / z > 0", "a division by zero"},
		{"z == 0 implies 1 / z > 0", "a division by zero"},

		{"other == 0", "other, which is no control variable, is not worked out"},
		{"f(n) == 0", "a call other than abs, min and max is not worked out"},
		{"len([1, 2]) == 2", "a call other than abs, min and max is not worked out"},
		{"n.abs() == 3", "a call other than abs, min and max is not worked out"},
		{"abs(n, n) == 3", "abs of 2 arguments is not worked out"},
		{"min(n) == 3", "min of 1 arguments is not worked out"},
		{"[1, 2][0] == 1", "this is not worked out"},
		{"n in [1, 2, 3]", "this, where a bool is, is not worked out"},
		{"\"a\" == \"a\"", "this is not worked out"},
		{"Some(n) == None", "a call other than abs, min and max is not worked out"},
		{"n", "this, where a bool is, is not worked out"},
		{"n + 1", "this, where a bool is, is not worked out"},
		{"f(n)", "this, where a bool is, is not worked out"},
		{"(n == 3) + 1 == 1", "a bool where an int is is not worked out"},
		{"(n == 3) < 1", "a bool where an int is is not worked out"},
		{"(n == 3) == 1", "this, where a bool is, is not worked out"},
		{"not n == 3 == 3", "this, where a bool is, is not worked out"},
	} {
		got, err := evalBool(guardOf(t, c.expr), env)
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Errorf("%s = %v, %v; want an error with %q", c.expr, got, err, c.want)
		}
	}
}

// bodyOf is the body of a transition as the parser reads it.
func bodyOf(t *testing.T, body string) []ast.Stmt {
	t.Helper()
	src := "monitor M:\n    state S:\n        on go -> S:\n"
	for _, l := range strings.Split(body, "\n") {
		src += "            " + l + "\n"
	}
	prog, err := parser.Parse("lts_test.anm", src)
	if err != nil {
		t.Fatalf("%s: parse error: %v", body, err)
	}
	return prog.Decls[0].(*ast.MachineDecl).States[0].Transitions[0].Body
}

func TestModelStatements(t *testing.T) {
	run := func(body string) (map[string]int64, error) {
		env := map[string]int64{"n": 3, "m": 10}
		for _, s := range bodyOf(t, body) {
			if err := execStmt(s, env); err != nil {
				return env, err
			}
		}
		return env, nil
	}
	for _, c := range []struct {
		body string
		n, m int64
	}{
		{"n = n + 1", 4, 10},
		{"n += m", 13, 10},
		{"n -= m", -7, 10},
		{"n = m\nm = n + 1", 10, 11},
		{"if n == 3:\n    n = 0\nelse:\n    m = 0", 0, 10},
		{"if n == 4:\n    n = 0\nelse:\n    m = 0", 3, 0},
		{"if n == 4:\n    n = 0\nelif m == 10:\n    n = 1\nelse:\n    n = 2", 1, 10},
		{"if n == 4:\n    n = 0", 3, 10},
		// A branch that is not taken is not worked out.
		{"if n == 4:\n    n = 1 / 0\nelse:\n    m = 1", 3, 1},
	} {
		env, err := run(c.body)
		if err != nil || env["n"] != c.n || env["m"] != c.m {
			t.Errorf("%q: n=%d m=%d, %v; want n=%d m=%d", c.body, env["n"], env["m"], err, c.n, c.m)
		}
	}
	for _, c := range []struct{ body, want string }{
		{"t = 1", "t is no control variable, and a transition assigns to nothing else"},
		{"n: int = 1", "a transition declares no variable"},
		{"t += 1", "t is no control variable, and a transition assigns to nothing else"},
		{"n = f(n)", "a call other than abs, min and max is not worked out"},
		{"n = 1 / (n - 3)", "a division by zero"},
		{"n += 9223372036854775807", "+ overflows"},
		{"if n:\n    n = 1", "this, where a bool is, is not worked out"},
		{"if n == 3:\n    print(n)", "a transition holds assignments to control variables and ifs, and this is neither"},
		{"while n > 0:\n    n -= 1", "a transition holds assignments to control variables and ifs, and this is neither"},
		{"return 1", "a transition holds assignments to control variables and ifs, and this is neither"},
		{"print(n)", "a transition holds assignments to control variables and ifs, and this is neither"},
	} {
		env, err := run(c.body)
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Errorf("%q: %v, %v; want an error with %q", c.body, env, err, c.want)
		}
	}
}

// The first value of a control variable is worked out with those before it,
// and with none written it is the least of the range.
func TestControlVariableFirstValues(t *testing.T) {
	const src = `machine Car:
    state A:
        on go -> A

monitor Gate:
VARS
    state S:
        on go when n < 3 -> S:
            n += 1

system Sys:
    compose:
        car: Car
        gate: Gate
    check:
        deadlock_free
`
	for vars, want := range map[string]string{
		"    n: control int[0..3] = 1":                                   "S[n=1]",
		"    n: control int[1..3]":                                       "S[n=1]",
		"    n: control int[-2..3]":                                      "S[n=-2]",
		"    a: control int[0..3] = 2\n    n: control int[0..3] = a + 1": "S[a=2,n=3]",
		"    a: control int[2..3]\n    n: control int[0..3] = min(a, 9)": "S[a=2,n=2]",
	} {
		comp := machineOf(t, strings.Replace(src, "VARS", vars, 1), "Gate")
		if got := comp.States[comp.Init]; got != want {
			t.Errorf("%q: the first state is %s, want %s", vars, got, want)
		}
	}
}

// The contract kernel proves that a control variable stays in its range and
// that an invariant holds where a transition arrives. Of a program it has
// refused, the model is not built: a transition into a state whose invariant
// does not hold was dropped without a word, and one out of the range went on.
func TestModelIsNotBuiltOfWhatTheContractKernelRefuses(t *testing.T) {
	const src = `machine Car:
    state A:
        on go -> A

monitor Gate:
    n: control int[0..3] = INIT
    state S:
        INV
        on go -> S:
            n = n + 1

system Sys:
    compose:
        car: Car
        gate: Gate
    check:
        deadlock_free
`
	for _, c := range []struct{ init, inv, want string }{
		{"0", "invariant: n >= 0", "control variable n of Gate is 4 after go from S[n=3], outside its range 0..3"},
		{"4", "invariant: n >= 0", "control variable n of Gate is 4 at first, outside its range 0..3"},
		{"0", "invariant: n < 2", "Gate arrives in S[n=2] where the invariant of S at"},
		{"2", "invariant: n < 2", "Gate arrives in S[n=2] where the invariant of S at"},
		{"0", "invariant: 4 / (n - 1) != 9", "a division by zero"},
	} {
		rep := verifyLTS(t, strings.NewReplacer("INIT", c.init, "INV", c.inv).Replace(src))
		if got := strings.Join(rep.BuildErrors, "\n"); !strings.Contains(got, c.want) {
			t.Errorf("init %s, %s: want %q, got %q", c.init, c.inv, c.want, got)
		}
		if len(rep.Systems) != 0 {
			t.Errorf("init %s, %s: a system was checked", c.init, c.inv)
		}
	}
}

// LTSA reads the alphabet of a process off its actions, so one that is
// never made is written as an extension of the alphabet.
func TestFSPExportKeepsAnActionThatIsNeverOffered(t *testing.T) {
	prog, err := parser.Parse("lts_test.anm", `machine Car:
    state A:
        on go -> A

monitor Gate:
    n: control int[0..1] = 0
    state S:
        on go when n > 5 -> S
        on stop when n > 5 -> S
        on other -> S

system Sys:
    compose:
        car: Car
        gate: Gate
    check:
        deadlock_free
`)
	if err != nil {
		t.Fatal(err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatal(err)
	}
	out := ExportFSP(info)
	if !strings.Contains(out, "+ {go, stop}.") {
		t.Errorf("want the alphabet extended by {go, stop}:\n%s", out)
	}
	if strings.Contains(out, "+ {go, other") || strings.Contains(out, "go ->") && strings.Contains(out, "GATE = (go") {
		t.Errorf("an action that is made is in the extension, or go is made:\n%s", out)
	}
}
