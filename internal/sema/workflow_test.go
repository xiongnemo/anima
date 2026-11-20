package sema

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
)

// A workflow variable is read only where every path to the read has
// assigned it: on a path that has not, it is () on both backends.
func TestSemaWorkflowVariableIsAssignedOnEveryPath(t *testing.T) {
	const head = `workflow W(n: int) -> int:
    verify: sound

    start -> a:
        ok = n > 0
`
	const choice = `
    choice after a:
        when ok -> yes
        when not ok -> no
`
	const missing = "is not assigned on every path"
	cases := []struct {
		name, body string
		want       string // part of the error, or "" when it is accepted
	}{
		{"assigned on one path, read where the paths meet", choice + `
    step yes -> fin:
        d = 5
    step no -> fin:
        print("no")
    step fin -> done:
        return d
`, `"d" ` + missing + ` to step fin`},
		{"the same through a merge", choice + `
    step yes -> m:
        d = 5
    step no -> m:
        print("no")
    merge m after yes, no -> fin
    step fin -> done:
        return d
`, `"d" ` + missing},
		{"read in the guard of a later choice", choice + `
    step yes -> fin:
        d = 5
    step no -> fin:
        print("no")
    step fin:
        print("fin")
    choice after fin:
        when d > 3 -> big
        else -> small
    step big -> done:
        return 1
    step small -> done:
        return 2
`, `"d" ` + missing + ` to this choice`},
		{"read in a fork branch", choice + `
    step yes -> split:
        d = 5
    step no -> split:
        print("no")
    fork split:
        branch left:
            x = d + 1
        branch right:
            y = 2
    join both
    step fin after both -> done:
        return y
`, `"d" ` + missing + ` to branch left`},
		{"updated in place where it may not be assigned", choice + `
    step yes -> fin:
        d = 5
    step no -> fin:
        print("no")
    step fin -> done:
        d += 1
        return 1
`, `"d" ` + missing},
		{"assigned in a step the path does not run", `
    step a -> fin:
        print("a")
    step other -> fin:
        d = 5
    step fin -> done:
        return d
`, `"d" ` + missing},

		{"assigned on both paths", choice + `
    step yes -> fin:
        d = 5
    step no -> fin:
        d = 6
    step fin -> done:
        return d
`, ""},
		{"assigned in the start", `
    step a -> fin:
        d = n
    step fin -> done:
        return d
`, ""},
		{"read on the path that assigned it only", choice + `
    step yes -> done:
        d = 5
        return d
    step no -> done:
        return 2
`, ""},
		{"assigned in a fork branch, read after the join", `
    step a -> split:
        print("a")
    fork split:
        branch left:
            x = 1
        branch right:
            y = 2
    join both
    step fin after both -> done:
        return x + y
`, ""},
		{"a lambda parameter named like a variable of another path", choice + `
    step yes -> fin:
        d = 5
    step no -> fin:
        print("no")
    step fin -> done:
        return [1, 2] |> map(d => d + 1) |> sum()
`, ""},
		{"assigned again where the paths meet, then read", choice + `
    step yes -> fin:
        d = 5
    step no -> fin:
        print("no")
    step fin -> done:
        d = 7
        return d
`, ""},
	}
	for _, c := range cases {
		prog, err := parser.Parse("wf.anm", head+c.body+"\ndef main() -> int:\n    return 0\n")
		if err != nil {
			t.Fatalf("%s: parse: %v", c.name, err)
		}
		_, err = Check(prog)
		switch {
		case c.want == "" && err != nil:
			t.Errorf("%s: expected it accepted, got %v", c.name, err)
		case c.want != "" && (err == nil || !strings.Contains(err.Error(), c.want)):
			t.Errorf("%s: expected an error containing %q, got %v", c.name, c.want, err)
		}
	}
}
