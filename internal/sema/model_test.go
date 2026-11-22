package sema

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
)

func modelErr(t *testing.T, src string) string {
	t.Helper()
	prog, err := parser.Parse("model_test.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v\n%s", err, src)
	}
	if _, err := Check(prog); err != nil {
		return err.Error()
	}
	return ""
}

const modelSrc = `type Small = int[0..3]
type Wide = int[0..33]

def f(x: int) -> int:
    return x

def yes() -> bool:
    return True

monitor Gate:
    n: control int[0..3] = 0
    m: control Small = INIT

    state S:
        invariant: INV
        on go when GUARD -> S:
            BODY
        on stop -> T

    state T:
        on go -> S
`

func modelOf(init, inv, guard, body string) string {
	return strings.NewReplacer("INIT", init, "INV", inv, "GUARD", guard, "BODY", strings.Replace(body, "\n", "\n            ", -1)).Replace(modelSrc)
}

// A model is written with what the LTS kernel works out. Each of these was
// read by sema, and was the int 0 or the bool False in the model.
func TestModelRefusesWhatTheKernelDoesNotWorkOut(t *testing.T) {
	const notWorkedOut = "is not worked out in a model: a model is written with int literals, control variables, the operators of ints, abs, min, max, comparisons, and not, and, or, implies"
	for _, c := range []struct{ expr, want string }{
		{"f(n) == 0", "a call other than abs, min and max " + notWorkedOut},
		{"yes()", "this, where a bool is, " + notWorkedOut},
		{"len([1, 2]) == 2", "a call other than abs, min and max " + notWorkedOut},
		{"[1, 2, 3][n] == 2", "this " + notWorkedOut},
		{"n in [1, 2]", "the operator in " + notWorkedOut},
		{`"a" == "a"`, "this " + notWorkedOut},
		{`"a" < "b"`, "this " + notWorkedOut},
		{`f"{n}" == "1"`, "this " + notWorkedOut},
		{"Some(n) == None", "a call other than abs, min and max " + notWorkedOut},
		{"Some(n) != Some(1)", "a call other than abs, min and max " + notWorkedOut},
		{"(n |> f) == 0", "this " + notWorkedOut},
		{"(n == 1) == yes()", "this, where a bool is, " + notWorkedOut},
	} {
		for hole, src := range map[string]string{
			"guard":     modelOf("0", "True", c.expr, "n = 0"),
			"invariant": modelOf("0", c.expr, "True", "n = 0"),
			"if":        modelOf("0", "True", "True", "if "+c.expr+":\n    n = 0"),
		} {
			if got := modelErr(t, src); !strings.Contains(got, c.want) {
				t.Errorf("%s as %s: want %q, got %q", c.expr, hole, c.want, got)
			}
		}
	}

	for _, c := range []struct{ expr, want string }{
		{"f(1)", "a call other than abs, min and max " + notWorkedOut},
		{"len([1, 2])", "a call other than abs, min and max " + notWorkedOut},
		{"[1, 2, 3][0]", "this " + notWorkedOut},
	} {
		if got := modelErr(t, modelOf(c.expr, "True", "True", "n = 0")); !strings.Contains(got, c.want) {
			t.Errorf("%s as a first value: want %q, got %q", c.expr, c.want, got)
		}
		if got := modelErr(t, modelOf("0", "True", "True", "n = "+c.expr)); !strings.Contains(got, c.want) {
			t.Errorf("n = %s: want %q, got %q", c.expr, c.want, got)
		}
		if got := modelErr(t, modelOf("0", "True", "True", "n += "+c.expr)); !strings.Contains(got, c.want) {
			t.Errorf("n += %s: want %q, got %q", c.expr, c.want, got)
		}
	}

	const only = "a transition holds assignments to control variables and ifs, and nothing else is in the model"
	for _, c := range []struct{ body, want string }{
		{"t = 1", "t is no control variable: " + only},
		{"n: int[0..3] = 1", "a transition declares no variable: " + only},
		{"print(n)", only},
		{"while n > 0:\n    n -= 1", only},
		{"for i in [1, 2]:\n    n = i", only},
		{"return 1", only},
		{"if n > 0:\n    print(n)", only},
		{"if n > 0:\n    n = 0\nelse:\n    t = 2", "t is no control variable: " + only},
	} {
		if got := modelErr(t, modelOf("0", "True", "True", c.body)); !strings.Contains(got, c.want) {
			t.Errorf("%q: want %q, got %q", c.body, c.want, got)
		}
	}
}

func TestModelAcceptsWhatTheKernelWorksOut(t *testing.T) {
	for _, c := range []struct{ init, inv, guard, body string }{
		{"0", "True", "True", "n = 0"},
		{"n", "n >= 0 and m <= 3", "n < 3 or m == 0", "n += 1\nm -= 0"},
		{"min(n + 1, 3)", "abs(n - m) <= 3", "max(n, m) < 3 implies not (n == 3)", "n = min(n + 1, 3)"},
		{"3 & 1", "n | m >= 0", "(n ^ m) << 1 >= 0 and n >> 1 <= 1 and ~n < 0", "n = (n * 2) % 4 / 1 - 0"},
		{"-(0 - 1)", "(n == 0) == (n < 1)", "(n > 0) != False", "if n == 0:\n    n = 1\nelif m == 0:\n    m = 1\nelse:\n    n = 0"},
		{"0", "not False", "True == (n == n)", "n = n"},
		// A pipe into a built-in is the call it runs.
		{"0", "(n - 3 |> abs()) >= 0", "(n |> min(m)) <= 3", "n = n |> max(0)"},
	} {
		if got := modelErr(t, modelOf(c.init, c.inv, c.guard, c.body)); got != "" {
			t.Errorf("%+v: %s", c, got)
		}
	}
}

// A control variable is an int of a small range: the model holds a state for
// each of its values. A bool was read as False wherever it was named, and a
// range of 2^63 values was a model that was never done being built.
func TestControlVariableIsAnIntOfASmallRange(t *testing.T) {
	const src = `type Small = int[0..3]
type Wide = int[0..33]
type Name = str

monitor Gate:
    n: control TYPE
    state S:
        on go -> S
`
	for ty, ok := range map[string]bool{
		"int[0..3]":    true,
		"int[0..32]":   true,
		"int[-16..16]": true,
		"int[5..5]":    true,
		"Small":        true,
		"int[0..33]":   false,
		"Wide":         false,
		"int":          false,
		"bool":         false,
		"str":          false,
		"Name":         false,
		"list[int]":    false,
		"int[-9223372036854775807..9223372036854775807]":  false,
		"int[-9223372036854775807..-9223372036854775800]": true,
	} {
		got := modelErr(t, strings.Replace(src, "TYPE", ty, 1))
		want := "control variable n has type " + ty + ": a control variable is an int of a range, int[lo..hi], of at most 33 values"
		if ok && got != "" {
			t.Errorf("%s: %s", ty, got)
		}
		if !ok && !strings.Contains(got, want) {
			t.Errorf("%s: want %q, got %q", ty, want, got)
		}
	}
}

// A property is the actions it allows in each state. A guard, an invariant
// and a body were read and dropped; of two transitions on one action the
// last was kept; a target that is no state was ERROR.
func TestPropertyHoldsOnlyActions(t *testing.T) {
	const src = `property P:
    state A:
        ON
    state B:
        on b -> A
`
	for on, want := range map[string]string{
		"on a -> B":                        "",
		"on a -> ERROR":                    "",
		"on a -> A\n        on b -> B":     "",
		"on a when False -> B":             "transition a of property P has a guard or a body",
		"on a -> B:\n            n = 1":    "transition a of property P has a guard or a body",
		"invariant: 1 == 1":                "state A of property P has an invariant",
		"on a -> Nowhere":                  `transition a targets unknown state "Nowhere" in property P`,
		"on a -> END":                      `transition a targets unknown state "END" in property P`,
		"on a -> B\n        on a -> A":     "state A of property P has two transitions on a",
		"on a -> B\n        on a -> ERROR": "state A of property P has two transitions on a",
	} {
		got := modelErr(t, strings.Replace(src, "ON", on, 1))
		if (want == "") != (got == "") || !strings.Contains(got, want) {
			t.Errorf("%q: want %q, got %q", on, want, got)
		}
	}
}

// An instance gives another name to an action its machine has, and to each
// once.
func TestRelabelNamesAnActionOfTheMachine(t *testing.T) {
	const src = `machine A:
    state S:
        on a -> S
        on left.get when False -> S

system Sys:
    compose:
        x: A RELABEL
    check:
        deadlock_free
`
	for relabel, want := range map[string]string{
		"":                          "",
		"/ {a -> b}":                "",
		"/ {a -> b, left.get -> c}": "",
		"/ {zzz -> a}":              "instance x of system Sys relabels zzz, which is no action of A",
		"/ {get -> a}":              "instance x of system Sys relabels get, which is no action of A",
		"/ {a -> b, a -> c}":        "instance x of system Sys relabels a twice",
	} {
		got := modelErr(t, strings.Replace(src, "RELABEL", relabel, 1))
		if (want == "") != (got == "") || !strings.Contains(got, want) {
			t.Errorf("%q: want %q, got %q", relabel, want, got)
		}
	}
}
