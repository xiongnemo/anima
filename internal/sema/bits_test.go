package sema

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
)

// The operators on bits, and unary - with them, take ints: both backends
// run them on whatever they are given as if it were one.
func TestSemaBitOperatorsTakeInts(t *testing.T) {
	const head = `import std.concurrent as conc

def main() -> int:
    n: int[0..9] = 3
`
	cases := []struct{ name, body, want string }{
		{"ints", "    x = (n & 1 | 2 ^ 3) << 2 >> 1\n    y: int = ~x", ""},
		{"in a lambda", "    xs = [1, 2] |> map((q) => q << 1 & 6)", ""},
		{"a named lambda", "    g = (q) => ~q | 1\n    y: int = g(4)", ""},
		{"bools", "    x = True & False", "& works on the bits of two ints, got bool and bool"},
		{"strs", `    x = "a" | "b"`, "| works on the bits of two ints, got str and str"},
		{"lists", "    x = [1] ^ [2]", "^ works on the bits of two ints"},
		{"a count that is a str", `    x = 1 << "a"`, "<< works on the bits of two ints"},
		{"an Option", "    x = None >> 1", ">> works on the bits of two ints"},
		{"~ of a bool", "    x = ~True", "~ needs an int, got bool"},
		{"~ of a str", `    x = ~"s"`, "~ needs an int, got str"},
		{"- of a str", `    x = -"s"`, "- needs an int, got str"},
		{"- of a bool", "    x = -True", "- needs an int, got bool"},
		{"- of a list", "    x = -[1]", "- needs an int"},
		{"a str in a lambda", `    xs = ["a"] |> map((q) => q << 1)`, "<< works on the bits of two ints, got str"},
		{"a named lambda given a str", "    g = (q) => q & 1\n    y = g(\"a\")", "& works on the bits of two ints, got str"},
		{"a value of unknown type", "    ch = conc.Channel(cap=1)\n    sent = ch.send(1)\n    match ch.recv():\n        None -> print(0)\n        Some(v) -> print(v & 1)", "& works on the bits of two ints, got unknown"},
		{"a range of the result is left to the contract kernel", "    x: int[0..1] = n & 1", ""},
	}
	for _, c := range cases {
		prog, err := parser.Parse("bits.anm", head+c.body+"\n    return 0\n")
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
