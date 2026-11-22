package tests

import (
	"os/exec"
	"strings"
	"testing"
)

// A program is given the same arguments by `anima run f.anm -- ...` as its
// native executable is run with. The `--` was given to it as the first of
// them, so a program that reads its arguments read other ones on the VM.
func TestE2EProgramArguments(t *testing.T) {
	vm, native := bothBackends(t, "args", `import std.cli as cli

def main() -> int:
    args = cli.args()
    for i in 1..len(args):
        print(f"[{args[i]}]")
    return len(args) - 1
`)
	run := func(argv []string, args ...string) string {
		out, err := exec.Command(argv[0], append(argv[1:], args...)...).CombinedOutput()
		code := 0
		if e, ok := err.(*exec.ExitError); ok {
			code = e.ExitCode()
		} else if err != nil {
			t.Fatal(err)
		}
		if n := strings.Count(string(out), "\n"); n != code {
			t.Fatalf("%q: %d arguments counted, %d printed:\n%s", args, code, n, out)
		}
		return string(out)
	}
	for _, args := range [][]string{
		{}, {"a"}, {"a", "b c", ""}, {"-x", "--seed", "3"}, {"a", "--", "b"}, {"--", "--"}, {"--"},
	} {
		want := run(native, args...)
		if got := run(vm, append([]string{"--"}, args...)...); got != want {
			t.Errorf("anima run f.anm -- %q gives\n%s, the executable\n%s", args, got, want)
		}
		// Without the `--`, the same, but for a first argument that is one.
		if len(args) > 0 && args[0] == "--" {
			continue
		}
		if got := run(vm, args...); got != want {
			t.Errorf("anima run f.anm %q gives\n%s, the executable\n%s", args, got, want)
		}
	}
}
