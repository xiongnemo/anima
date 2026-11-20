package sema

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
)

// The branches of a fork run at the same time: the VM gives each a copy of
// the variables, the native backend runs them as threads on the variables
// themselves. A branch that names a variable another branch writes sees one
// thing on one backend and another on the other.
func TestSemaForkBranchesShareOnlyWhatNoneWrites(t *testing.T) {
	head := `import std.concurrent as conc

entity Acc:
    bal: int

def set_zero(mut a: Acc):
    a.bal = 0

def zeroed(mut a: Acc) -> int:
    a.bal = 0
    return 0

def read(a: Acc) -> int:
    return a.bal

workflow W(n: int[0..100], o: Option[int], ch: conc.Channel[int]) -> int:
    verify: sound

    start -> split:
        acc = Acc(bal=5)
        xs = [5, 6]
        m = {"a": 1}
        a = 0
        b = 0

    fork split:
        branch left:
`
	tail := `    join both

    step fin after both -> done:
        return a + b
`
	const uses = "which branch"
	const inPlace = "in place"
	cases := []struct {
		name        string
		left, right []string
		want        string // part of the error, or "" when it is accepted
	}{
		{"a variable one branch assigns", []string{"a = 1"}, []string{"b = a + 1"}, uses},
		{"the same, the reader first", []string{"b = a + 1"}, []string{"a = 1"}, uses},
		{"an in-place update of a variable", []string{"b = a"}, []string{"a += 1"}, uses},
		{"a loop variable", []string{"b = a"}, []string{"for a in xs:\n                print(a)"}, uses},
		{"a name in a pattern", []string{"b = a"}, []string{"match o:\n                Some(a) -> print(a)\n                None -> print(0)"}, uses},
		{"a variable first bound in a branch", []string{"c = 1"}, []string{"b = c"}, uses},
		{"an assignment under an if", []string{"b = a"}, []string{"if n > 0:\n                a = 1"}, uses},
		{"two branches assign one variable", []string{"a = 1"}, []string{"a = 2"}, "concurrent write race"},

		{"a field write", []string{"b = 1"}, []string{"acc.bal = 0"}, inPlace},
		{"a field update", []string{"b = 1"}, []string{"acc.bal += 1"}, inPlace},
		{"an element write", []string{"b = 1"}, []string{"xs[0] = 0"}, inPlace},
		{"an element update", []string{"b = 1"}, []string{"xs[0] += 1"}, inPlace},
		{"a map insert", []string{"b = 1"}, []string{"m[\"k\"] = 1"}, inPlace},
		{"a mut argument", []string{"b = 1"}, []string{"set_zero(mut acc)"}, inPlace},
		{"a mut argument in an expression", []string{"b = 1"}, []string{"a = zeroed(mut acc) + 1"}, inPlace},
		{"a mut argument in a lambda", []string{"b = 1"}, []string{"a = xs |> map(v => zeroed(mut acc)) |> sum()"}, inPlace},
		{"a write under a loop", []string{"b = 1"}, []string{"for v in xs:\n                acc.bal = v"}, inPlace},

		{"a return in a branch", []string{"return 7"}, []string{"b = 1"}, "return in branch"},
		{"a return under an if", []string{"if n > 0:\n                return 7"}, []string{"b = 1"}, "return in branch"},

		{"two branches read one variable", []string{"a = n + xs[0] + acc.bal"}, []string{"b = n + xs[1] + acc.bal"}, ""},
		{"each branch assigns its own", []string{"a = 1", "a += 1"}, []string{"b = 2", "c = b + n"}, ""},
		{"a branch assigns what a function returns", []string{"a = read(acc)"}, []string{"b = read(acc) + 1"}, ""},
		{"a lambda parameter is not the variable", []string{"a = 1"}, []string{"b = xs |> map(a => a + 1) |> sum()"}, ""},
		{"a channel is what branches share", []string{"ch.send(1)"}, []string{"ch.send(2)"}, ""},
	}
	for _, c := range cases {
		src := head
		for _, l := range c.left {
			src += "            " + l + "\n"
		}
		src += "        branch right:\n"
		for _, l := range c.right {
			src += "            " + l + "\n"
		}
		src += tail
		prog, err := parser.Parse("fork.anm", src)
		if err != nil {
			t.Fatalf("%s: parse error: %v", c.name, err)
		}
		_, err = Check(prog)
		switch {
		case c.want == "" && err != nil:
			t.Errorf("%s: expected it to be accepted, got %v", c.name, err)
		case c.want != "" && (err == nil || !strings.Contains(err.Error(), c.want)):
			t.Errorf("%s: expected an error with %q, got %v", c.name, c.want, err)
		}
	}
}
