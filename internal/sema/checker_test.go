package sema

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/parser"
)

func TestSemaValidPipelineAndFrameInference(t *testing.T) {
	src := `
import std.socket as sock
import std.requests as req
import std.json as json

type Money = int[0..1_000_000]
type FetchState = Cached(score: int[0..100]) | Fresh(score: int[0..100]) | Degraded

entity Account:
    balance: Money
    frozen: Money
    invariant: balance + frozen <= 1_000_000

def lock_funds(mut acc: Account, amt: int[1..10_000]) -> bool:
    if acc.balance >= amt:
        acc.balance -= amt
        acc.frozen += amt
        return True
    return False

def call_net(url: str) -> Result[req.HttpResponse, str]:
    resp = req.get(url, timeout_ms=2000)?
    return Ok(resp)
`
	prog, err := parser.Parse("valid.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	info, err := Check(prog)
	if err != nil {
		t.Fatalf("sema failed: %v", err)
	}
	fi := info.Funcs["lock_funds"]
	if fi == nil || len(fi.Frame.Writes) == 0 {
		t.Fatalf("expected inferred writes frame for lock_funds, got %+v", fi)
	}
	cni := info.Funcs["call_net"]
	if len(cni.Frame.PortEffects) == 0 {
		t.Fatalf("expected inferred port effects on call_net")
	}
}

func TestSemaRejectsAliasing(t *testing.T) {
	src := `
entity Account:
    balance: int[0..1000]

def transfer(mut src: Account, mut dst: Account, amt: int[1..100]) -> int:
    src.balance -= amt
    dst.balance += amt
    return 0

def main() -> int:
    acc = Account(balance=500)
    return transfer(mut acc, mut acc, 10)
`
	prog, err := parser.Parse("alias.anm", src)
	if err != nil {
		t.Fatal(err)
	}
	_, err = Check(prog)
	if err == nil || !strings.Contains(err.Error(), "anti-aliasing") {
		t.Fatalf("expected SPARK anti-aliasing violation, got: %v", err)
	}
}

func TestSemaRejectsMissingTimeoutOnRequests(t *testing.T) {
	src := `
import std.requests as req

def fetch() -> Result[req.HttpResponse, str]:
    return req.get("https://example.com")
`
	prog, err := parser.Parse("timeout.anm", src)
	if err != nil {
		t.Fatal(err)
	}
	_, err = Check(prog)
	if err == nil || !strings.Contains(err.Error(), "timeout_ms") {
		t.Fatalf("expected timeout_ms liveness contract error, got: %v", err)
	}
}

// Writing an element of a list parameter needs `mut`, like writing a field.
func TestSemaRejectsElementWriteToReadOnlyList(t *testing.T) {
	for name, body := range map[string]string{
		"assignment":          "    xs[0] = 1\n",
		"compound assignment": "    xs[0] += 0\n",
	} {
		ro := "def f(xs: list[int[0..9]]) -> int:\n" + body + "    return 0\n"
		prog, err := parser.Parse("ro.anm", ro)
		if err != nil {
			t.Fatalf("%s: parse error: %v", name, err)
		}
		if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "read-only parameter") {
			t.Errorf("%s: expected a read-only parameter error, got %v", name, err)
		}
		prog, err = parser.Parse("mut.anm", strings.Replace(ro, "def f(xs:", "def f(mut xs:", 1))
		if err != nil {
			t.Fatalf("%s: parse error: %v", name, err)
		}
		if _, err := Check(prog); err != nil {
			t.Errorf("%s: a mut list parameter should be writable, got %v", name, err)
		}
	}
}

// Reading an element is not a write: it may be passed next to a mut list,
// and a map only accepts values of its value type.
func TestSemaElementReadsAndMapValueTypes(t *testing.T) {
	ok := `
def set_first(mut xs: list[int[0..9]], v: int[0..9]) -> int:
    xs[0] = v
    return 0

def f(mut xs: list[int[0..9]]) -> int:
    return set_first(mut xs, xs[1])
`
	prog, err := parser.Parse("ok.anm", ok)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	if _, err := Check(prog); err != nil {
		t.Errorf("an element passed by value is not an alias, got %v", err)
	}
	bad := `
def f() -> int:
    m: map[str, int[0..9]] = {"count": 1}
    m["count"] = "unknown"
    return 0
`
	prog, err = parser.Parse("bad.anm", bad)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "map value expects") {
		t.Errorf("expected a map value type error, got %v", err)
	}
}

// A fork branch writes nothing in place: two branches that write elements
// of one map race, and so does one that writes what another reads.
func TestSemaRejectsElementWriteRaceInFork(t *testing.T) {
	src := `
workflow Tally(mut m: map[str, int[0..9]]) -> bool:
    verify: sound
    start -> work
    fork work:
        branch a:
            m["a"] = 1
        branch b:
            m["b"] = 2
    join j
    step finish after j -> done:
        return True
`
	prog, err := parser.Parse("race.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "writes m in place") {
		t.Errorf("expected an error about a write in place, got %v", err)
	}
}

// The runtimes compare map keys by their printed form, which only tells
// str, int and bool keys apart.
func TestSemaRejectsCompositeMapKeys(t *testing.T) {
	for name, src := range map[string]string{
		"annotation": "def f(m: map[list[int], int]) -> int:\n    return 0\n",
		"literal":    "def f() -> int:\n    m = {[1]: 1, [2]: 2}\n    return 0\n",
	} {
		prog, err := parser.Parse("key.anm", src)
		if err != nil {
			t.Fatalf("%s: parse error: %v", name, err)
		}
		if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "a map key must be") {
			t.Errorf("%s: expected a map key error, got %v", name, err)
		}
	}
}

// `{}` takes its key type from its use; a composite key stays rejected.
func TestSemaEmptyMapLiteralKeyType(t *testing.T) {
	ok := `
def f() -> int:
    a: map[int, int[0..9]] = {}
    a[1] = 2
    b: map[bool, int[0..9]] = {}
    b[True] = 3
    c = {}
    c["k"] = 4
    a = {}
    a[2] = 3
    return 0
`
	prog, err := parser.Parse("ok.anm", ok)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	if _, err := Check(prog); err != nil {
		t.Errorf("int, bool and str keys into an empty map should be accepted, got %v", err)
	}
	// Without a declared type the keys are str, in every branch alike.
	branches := `
def f(flag: bool) -> int:
    m = {}
    if flag:
        m = {}
        m["a"] = 1
    else:
        m["b"] = 2
    return 0
`
	prog, err = parser.Parse("branches.anm", branches)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	if _, err := Check(prog); err != nil {
		t.Errorf("str keys in both branches should be accepted, got %v", err)
	}
	bad := "def f() -> int:\n    c = {}\n    c[1] = 4\n    return 0\n"
	prog, err = parser.Parse("bad.anm", bad)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "map key expects") {
		t.Errorf("expected a map key error, got %v", err)
	}
}

// An entity read out of a list is the object the list holds, so it cannot be
// passed next to the same list as a mut argument.
func TestSemaRejectsElementAliasOfMutContainer(t *testing.T) {
	head := `
entity Inner:
    v: int[0..9]

entity Row:
    n: int[0..9]
    inner: Inner

def bump(mut rows: list[Row], r: Row) -> int:
    return 0

def poke(mut rows: list[Row], i: Inner) -> int:
    return 0

def f(mut rows: list[Row]) -> int:
    if len(rows) > 0:
`
	for name, call := range map[string]string{
		"element":          "        return bump(mut rows, rows[0])\n",
		"field of element": "        return poke(mut rows, rows[0].inner)\n",
	} {
		prog, err := parser.Parse("alias.anm", head+call+"    return 0\n")
		if err != nil {
			t.Fatalf("%s: parse error: %v", name, err)
		}
		if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "anti-aliasing") {
			t.Errorf("%s: expected an anti-aliasing error, got %v", name, err)
		}
	}
}

// Keys are stored by their printed form, so one map cannot mix key types.
func TestSemaRejectsMixedMapKeyTypes(t *testing.T) {
	for name, body := range map[string]string{
		"writes to an empty map": "    m = {}\n    m[1] = 1\n    m[\"1\"] = 2\n",
		"literal":                "    m = {1: 1, \"1\": 2}\n",
		"map inside a list":      "    maps = [{}]\n    m = maps[0]\n    m[\"1\"] = 1\n    m[1] = 2\n",
	} {
		prog, err := parser.Parse("mixed.anm", "def f() -> int:\n"+body+"    return 0\n")
		if err != nil {
			t.Fatalf("%s: parse error: %v", name, err)
		}
		if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "map key") {
			t.Errorf("%s: expected a map key error, got %v", name, err)
		}
	}
}

// A function is not a value, so no call can go around the element-alias
// rule through one.
func TestSemaRejectsElementAliasThroughFunctionValue(t *testing.T) {
	src := `
entity Row:
    n: int[0..9]

def bump(mut rs: list[Row], r: Row) -> int:
    return 0

def f(mut rows: list[Row]) -> int:
    g = bump
    if len(rows) > 0:
        return g(mut rows, rows[0])
    return 0
`
	prog, err := parser.Parse("fnval.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "function bump is not a value") {
		t.Errorf("expected bump to be rejected as a value, got %v", err)
	}
}

// The element range of a list or map is part of its type, and a variable
// keeps the type of its lists, maps and variants.
func TestSemaElementRanges(t *testing.T) {
	rejected := map[string]string{
		"lambda parameter given to a bounded list": `
def first(xs: list[int[1..9]]) -> int:
    if len(xs) > 0:
        return 10 / xs[0]
    return 0

def main() -> int:
    ys: list[int] = [0]
    h = (v) => first(v)
    print(h(ys))
    return 0
`,
		"list of unknown elements": `
def first(xs: list[int[1..9]]) -> int:
    if len(xs) > 0:
        return 10 / xs[0]
    return 0

def main() -> int:
    g = (v) => v - 1
    ys = [1, 2] |> map(g)
    print(first(ys))
    return 0
`,
		"r11/a3": `
def f(ys: list[int[1..9]]) -> int:
    if len(ys) > 0:
        return 10 / ys[0]
    return 0

def main() -> int:
    xs: list[int] = [0, 6]
    print(f(xs))
    return 0
`,
		"r11/a7": `
def f() -> list[int[1..9]]:
    xs: list[int] = [0, 6]
    return xs

def main() -> int:
    ys = f()
    if len(ys) > 0:
        print(10 / ys[0])
    return 0
`,
		"r11/a8": `
entity B:
    vals: list[int[1..9]]

def main() -> int:
    xs: list[int] = [0, 6]
    b = B(vals=xs)
    if len(b.vals) > 0:
        print(10 / b.vals[0])
    return 0
`,
		"r11/a10": `
def f(m: map[str, int[1..9]]) -> int:
    return 10 / m["a"]

def main() -> int:
    m: map[str, int] = {"a": 0}
    print(f(m))
    return 0
`,
		"r11b/n5": `
def mk() -> list[int[1..9]]:
    return [1, 2, 3]

def main() -> int:
    xs = [0, 0]
    if len(xs) > 5:
        xs = mk()
    print(10 / xs[0])
    return 0
`,
		"r11b/g5": `
entity Box:
    vals: list[int[1..9]]
    n: int

def main() -> int:
    b = Box(vals=[1, 2], n=1)
    ys: list[int] = [0]
    c = b with {vals: ys}
    print(10 / c.vals[0])
    return 0
`,
		"r11b/k2": `
def bump(mut ys: list[int[1..9]]) -> int:
    ys[0] = 9
    return 0

def main() -> int:
    xs = [0, 1]
    r = bump(mut xs)
    return 0
`,
		"r11b/n18": `
def f(o: Option[int[1..9]]) -> int:
    match o:
        Some(v) -> return 10 / v
        None -> return 0

def main() -> int:
    print(f(Some(0)))
    x = 0
    o = Some(x)
    print(f(o))
    return 0
`,
	}
	for name, src := range rejected {
		prog, err := parser.Parse("t.anm", src)
		if err != nil {
			t.Fatalf("%s: parse failed: %v", name, err)
		}
		if _, err := Check(prog); err == nil {
			t.Errorf("%s: expected a type error", name)
		}
	}
	accepted := map[string]string{
		"empty values": `
def first(xs: list[int[1..9]]) -> int:
    if len(xs) > 0:
        return 10 / xs[0]
    return 0

def main() -> int:
    es: list[int[1..9]] = []
    print(first([]))
    print(first(es))
    o: Option[int[1..9]] = None
    r: Result[int[1..9], str] = Err("x")
    m: map[str, int[1..9]] = {}
    return 0
`,
		"r11b/p1": `
def main() -> int:
    xs: list[int[1..9]] = [5, 6]
    xs[0] = 7
    print(10 / xs[0])
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
		"narrower variant, same list, counter": `
def f(o: Option[int]) -> int:
    return 0

def main() -> int:
    o: Option[int[1..9]] = Some(1)
    print(f(o))
    xs: list[int[1..9]] = [1]
    xs = [2]
    i = 0
    i += 1
    return 0
`,
	}
	for name, src := range accepted {
		prog, err := parser.Parse("t.anm", src)
		if err != nil {
			t.Fatalf("%s: parse failed: %v", name, err)
		}
		if _, err := Check(prog); err != nil {
			t.Errorf("%s: unexpected error: %v", name, err)
		}
	}
}

// The arguments of a call are checked against the parameters they are
// bound to: a keyword argument by its name, a piped value first.
func TestSemaCallArgumentsBindToTheirParameters(t *testing.T) {
	prelude := `
def divide(a: int[0..9], b: int[0..9]) -> int:
    requires: a != 0
    return b / a

def pick(s: str, xs: list[int[1..9]], ys: list[int[10..20]]) -> int:
    return 0

def g() -> int:
    zs: list[int] = [0]
`
	rejected := map[string]string{
		"unknown keyword":               "divide(typo=0, 1)",
		"too many piped arguments":      "0 |> divide(b=1, a=0)",
		"too few piped arguments":       "2 |> divide",
		"piped value of another type":   `zs |> pick(xs=[1], s="a")`,
		"piped list of another range":   `"a" |> pick(zs, [10])`,
		"keyword list of another range": `pick(ys=[10], xs=zs, s="a")`,
		"keyword of another type":       `pick(ys=[10], xs=[1], s=1)`,
	}
	for name, call := range rejected {
		prog, err := parser.Parse("t.anm", prelude+"    y = "+call+"\n    return 0\n")
		if err != nil {
			t.Fatalf("%s: parse failed: %v", name, err)
		}
		if _, err := Check(prog); err == nil {
			t.Errorf("%s: expected a type error", name)
		}
	}
	accepted := map[string]string{
		"reordered keywords":        `pick(ys=[10], xs=[1], s="a")`,
		"piped, then keywords":      `"a" |> pick(ys=[10], xs=[1])`,
		"piped, then by position":   `"a" |> pick([1], [10])`,
		"keyword, then by position": `divide(a=2, 0)`,
	}
	for name, call := range accepted {
		prog, err := parser.Parse("t.anm", prelude+"    y = "+call+"\n    return 0\n")
		if err != nil {
			t.Fatalf("%s: parse failed: %v", name, err)
		}
		if _, err := Check(prog); err != nil {
			t.Errorf("%s: unexpected error: %v", name, err)
		}
	}
}

// The backends fill the fields of a variant by position, so a keyword
// argument has to name the field at its place.
func TestSemaVariantFieldsInOrder(t *testing.T) {
	prelude := `
type Shape = Circle(r: int[1..9], k: int) | Dot

def g() -> int:
`
	cases := map[string]bool{
		"Circle(5, 0)":     true,
		"Circle(r=5, k=0)": true,
		"Circle(5, k=0)":   true,
		"Circle(k=0, r=5)": false,
		"Circle(5, r=0)":   false,
		"Circle(5, 0, 1)":  false,
		"Circle(5, zz=0)":  false,
		`Circle("a", k=0)`: false,
	}
	for call, ok := range cases {
		prog, err := parser.Parse("t.anm", prelude+"    s = "+call+"\n    return 0\n")
		if err != nil {
			t.Fatalf("%s: parse failed: %v", call, err)
		}
		if _, err := Check(prog); (err == nil) != ok {
			t.Errorf("%s: accepted = %v, want %v (%v)", call, err == nil, ok, err)
		}
	}
}

// What a program calls, reads a member of, or matches against has to be
// there at run time: sema is the only check of it.
func TestSemaCallsMembersAndPatternsExist(t *testing.T) {
	prelude := `
import std.concurrent as conc

type Shape = Circle(r: int, k: int) | Dot
type Other = Left(n: int) | Right

entity Box:
    n: int[0..9]

def first(n: int) -> int:
    return n

def work(n: int) -> Result[bool, str]:
    return Ok(n > 0)

def f(s: str, n: int, b: bool, xs: list[int], m: map[str, int], sh: Shape, o: Option[int], bx: Box) -> int:
`
	cases := []struct {
		body string
		want string // "" when the body is accepted
	}{
		// A function is called, not held.
		{"g = first\n    return 0", "function first is not a value"},
		{"ys = [first]\n    return 0", "function first is not a value"},
		{"ys = xs |> map(first)\n    return 0", "function first is not a value"},
		{"ys = xs |> filter(first)\n    return 0", "function first is not a value"},
		{"t = xs |> fold(0, first)\n    return 0", "function first is not a value"},
		{"ys = xs |> filter(5)\n    return 0", "filter takes a function"},
		{"return first(n)", ""},
		{"return n |> first", ""},
		{"ys = xs |> map((v) => first(v))\n    return 0", ""},
		{"g = (v) => first(v)\n    return g(1)", ""},
		{"g = (v) => v > 1\n    ys = xs |> filter(g)\n    return 0", ""},
		{"first = 3\n    return first", ""},
		// A call by a name that is a variable and a function at once: the
		// backends call the variable, the kernels would check the function.
		{"first = 3\n    return first(1)", "both a variable and a function"},
		{"first = (v) => 0\n    return first(1)", "both a variable and a function"},
		{"first = (v) => 0\n    return n |> first", "both a variable and a function"},
		{"len = 5\n    return len(xs)", "both a variable and a function"},
		{"filter = 5\n    ys = xs |> filter((v) => v > 1)\n    return 0", "both a variable and a function"},
		{"sum = 0\n    for v in xs:\n        sum = v\n    return sum", ""},
		{"ys = xs |> map(first => first)\n    return first(n)", ""},
		// Only a function is called.
		{"return n(1)", "cannot be called"},
		{"return s(1)", "cannot be called"},
		{"return bx.n(1)", "cannot be called"},
		{"return sh()", "cannot be called"},
		// Members.
		{"x = s.upper()\n    return 0", `has no member "upper"`},
		{"x = xs.nope()\n    return 0", `has no member "nope"`},
		{"x = m.len()\n    return 0", `has no member "len"`},
		{"x = n.foo\n    return 0", `has no member "foo"`},
		{"x = b.foo\n    return 0", `has no member "foo"`},
		{"x = o.is_some()\n    return 0", "match on it to reach what it holds"},
		{"x = first(n).foo\n    return 0", `has no member "foo"`},
		{"x = bx.missing\n    return 0", `has no field "missing"`},
		{"return xs.len() + s.len() + len(m) + bx.n", ""},
		// A variant is made with all of its fields.
		{"x = Circle(5)\n    return 0", "Circle has 2 field(s), got 1"},
		{"x = Circle()\n    return 0", "Circle has 2 field(s), got 0"},
		{"x = Circle(5, 6)\n    y = Dot\n    return 0", ""},
		// A pattern names every field and has the type of its subject.
		{"match sh:\n        Circle(r) -> return 1\n        _ -> return 0", "variant Circle has 2 field(s), pattern has 1"},
		{"match sh:\n        Circle -> return 1\n        _ -> return 0", "variant Circle has 2 field(s), pattern has 0"},
		{"match sh:\n        Left(v) -> return 1\n        _ -> return 0", "variant Left of Other cannot match"},
		{"match sh:\n        1 -> return 1\n        _ -> return 0", "an int pattern cannot match"},
		{"match s:\n        True -> return 1\n        _ -> return 0", "a bool pattern cannot match"},
		{"match s:\n        1..5 -> return 1\n        _ -> return 0", "an int range pattern cannot match"},
		{"match n:\n        \"a\" -> return 1\n        _ -> return 0", "a string pattern cannot match"},
		{"match b:\n        Some(v) -> return 1\n        _ -> return 0", "a variant pattern cannot match"},
		{"match o:\n        Some(True) -> return 1\n        _ -> return 0", "a bool pattern cannot match"},
		{"match sh:\n        Circle(1, \"a\") -> return 1\n        _ -> return 0", "a string pattern cannot match"},
		{"match sh:\n        Circle(1, k) -> return k\n        Circle(_, _) -> return 2\n        Dot -> return 0", ""},
		{"match o:\n        Some(1..5) -> return 1\n        Some(v) -> return v\n        None -> return 0", ""},
		{"match s:\n        \"a\" -> return 1\n        _ -> return 0", ""},
		// The result of a future has no type for sema: its patterns say.
		{"pool = conc.ThreadPool(2, 4)\n    fut = pool.submit(() => work(3))\n    r = fut.await()\n    match r:\n        Ok(True) -> print(1)\n        Ok(False) -> print(2)\n        Err(e) -> print(e)\n    pool.shutdown()\n    return 0", ""},
	}
	for _, tc := range cases {
		prog, err := parser.Parse("t.anm", prelude+"    "+tc.body+"\n")
		if err != nil {
			t.Fatalf("%q: parse failed: %v", tc.body, err)
		}
		_, err = Check(prog)
		switch {
		case tc.want == "" && err != nil:
			t.Errorf("%q: rejected: %v", tc.body, err)
		case tc.want != "" && (err == nil || !strings.Contains(err.Error(), tc.want)):
			t.Errorf("%q: want an error with %q, got %v", tc.body, tc.want, err)
		}
	}
}

// Both backends call a function of the program that is named like a
// pipeline stage, so `xs |> filter(2)` is checked as `filter(xs, 2)`.
func TestSemaUserFunctionNamedLikeAStage(t *testing.T) {
	prelude := `
def filter(xs: list[int], n: int[0..9]) -> int:
    return n

def fold(xs: list[int], s: str) -> str:
    return s

def f(xs: list[int]) -> int:
`
	cases := map[string]bool{
		"n = xs |> filter(2)\n    return n":                 true,
		"s = xs |> fold(\"a\")\n    return len(s)":          true,
		"n = xs |> filter(\"a\")\n    return n":             false, // not an int
		"n = xs |> filter((v) => v > 1)\n    return 0":      false, // not an int
		"ys = xs |> map((v) => v) |> take(1)\n    return 0": true,  // stages no function shadows
	}
	for body, ok := range cases {
		prog, err := parser.Parse("t.anm", prelude+"    "+body+"\n")
		if err != nil {
			t.Fatalf("%q: parse failed: %v", body, err)
		}
		if _, err := Check(prog); (err == nil) != ok {
			t.Errorf("%q: accepted = %v, want %v (%v)", body, err == nil, ok, err)
		}
	}
}

// The backends give a workflow its arguments by position, so a keyword
// argument has to name the parameter at its place.
func TestSemaWorkflowArgumentsInOrder(t *testing.T) {
	prelude := `
workflow Sub(a: int[0..9], b: int[0..9]) -> int:
    verify: sound
    start -> work
    step work -> done:
        return a - b

def g() -> int:
`
	cases := map[string]bool{
		"Sub(1, 0)":     true,
		"Sub(a=1, b=0)": true,
		"Sub(1, b=0)":   true,
		"Sub(b=1, a=0)": false,
		"Sub(1, a=0)":   false,
		"Sub(1, zz=0)":  false,
	}
	for call, ok := range cases {
		prog, err := parser.Parse("t.anm", prelude+"    r = run_workflow "+call+"\n    return 0\n")
		if err != nil {
			t.Fatalf("%s: parse failed: %v", call, err)
		}
		if _, err := Check(prog); (err == nil) != ok {
			t.Errorf("%s: accepted = %v, want %v (%v)", call, err == nil, ok, err)
		}
	}
}

// A comparison and a logical operator take operands they are for: both
// backends run them on anything, and do not agree on the answer.
func TestSemaOperandsOfComparisons(t *testing.T) {
	prelude := `
type Shape = Circle(r: int) | Dot
type Other = Left(n: int) | Right

entity Box:
    n: int[0..9]

entity Crate:
    n: int[0..9]

def f(s: str, n: int, b: bool, xs: list[int], m: map[str, int], sh: Shape, o: Option[int], bx: Box, cr: Crate, ot: Other) -> int:
`
	cases := []struct {
		body string
		want string // "" when the body is accepted
	}{
		// == and != between values of one sort.
		{"if n == 1:\n        return 1\n    return 0", ""},
		{"if s == \"a\" and b == True:\n        return 1\n    return 0", ""},
		{"if xs == [1, 2] or m != m:\n        return 1\n    return 0", ""},
		{"if o == None or o == Some(1) or sh == Dot or sh != Circle(2):\n        return 1\n    return 0", ""},
		{"c = bx\n    if c == bx:\n        return 1\n    return 0", ""},
		{"g = (v) => v == 1\n    return 0", ""},
		{"if xs == 5:\n        return 1\n    return 0", "they are never equal"},
		{"if n == \"5\":\n        return 1\n    return 0", "they are never equal"},
		{"if b == 1:\n        return 1\n    return 0", "they are never equal"},
		{"if s != n:\n        return 1\n    return 0", "they are never equal"},
		{"if bx == cr:\n        return 1\n    return 0", "they are never equal"},
		{"if sh == ot:\n        return 1\n    return 0", "they are never equal"},
		{"if sh == Right:\n        return 1\n    return 0", "they are never equal"},
		{"if xs == m:\n        return 1\n    return 0", "they are never equal"},
		// < and its kin order integers, or strings.
		{"if n < 2 and s <= \"b\" and n >= len(xs):\n        return 1\n    return 0", ""},
		{"g = (v) => v > n\n    return 0", ""},
		{"if s < n:\n        return 1\n    return 0", "both sides must be integers, or both strings"},
		{"if xs < xs:\n        return 1\n    return 0", "orders integers or strings"},
		{"if b > False:\n        return 1\n    return 0", "orders integers or strings"},
		{"if bx >= bx:\n        return 1\n    return 0", "orders integers or strings"},
		// and, or, implies and not take booleans.
		{"if b and not b or (n > 0 implies b):\n        return 1\n    return 0", ""},
		{"g = (v) => v and b\n    return 0", ""},
		{"if n and b:\n        return 1\n    return 0", "and needs a bool"},
		{"if b or xs:\n        return 1\n    return 0", "or needs a bool"},
		{"if s implies b:\n        return 1\n    return 0", "implies needs a bool"},
		{"if not n:\n        return 1\n    return 0", "not needs a bool"},
		// in looks into a list, a map or a string.
		{"if n in xs or s in m or s in \"abc\" or 1 in [1, 2]:\n        return 1\n    return 0", ""},
		{"g = (v) => v in xs\n    return 0", ""},
		{"if n in 5:\n        return 1\n    return 0", "in looks into a list, a map or a string"},
		{"if n in bx:\n        return 1\n    return 0", "in looks into a list, a map or a string"},
		{"if s in xs:\n        return 1\n    return 0", "in looks for"},
		{"if n in m:\n        return 1\n    return 0", "in looks for"},
		{"if n in s:\n        return 1\n    return 0", "in looks for"},
	}
	for _, tc := range cases {
		prog, err := parser.Parse("t.anm", prelude+"    "+tc.body+"\n")
		if err != nil {
			t.Fatalf("%q: parse failed: %v", tc.body, err)
		}
		_, err = Check(prog)
		switch {
		case tc.want == "" && err != nil:
			t.Errorf("%q: rejected: %v", tc.body, err)
		case tc.want != "" && (err == nil || !strings.Contains(err.Error(), tc.want)):
			t.Errorf("%q: want an error with %q, got %v", tc.body, tc.want, err)
		}
	}
}

// A variable holds values of one sort from its first assignment on: a later
// assignment, a loop variable and a name in a pattern all write it, and what
// it holds after an if, a loop or a match is read with one type.
func TestSemaVariableKeepsItsSort(t *testing.T) {
	prelude := `
type Shape = Circle(r: int) | Dot

entity Box:
    n: int[0..9]

entity Crate:
    n: int[0..9]

def f(c: bool, n: int, s: str, xs: list[int], ss: list[str], o: Option[int], os: Option[str], xss: list[list[int]], ol: Option[list[int]], bx: Box) -> int:
`
	const sort = "a variable keeps its sort"
	const elems = "a variable keeps the type of its elements"
	cases := []struct {
		body string
		want string // "" when the body is accepted
	}{
		// Assignments.
		{"x = 5\n    x = 7\n    if c:\n        x = n\n    return x", ""},
		{"t = \"a\"\n    t = s\n    b = True\n    b = not c\n    return 0", ""},
		{"q = None\n    q = Some(3)\n    q = o\n    return 0", ""},
		{"e = bx\n    e = Box(n=1)\n    return 0", ""},
		// What a named lambda hands back has the type its first use gives.
		{"g = (v) => v\n    r = g(1)\n    r = \"s\"\n    return 0", "keeps its sort"},
		{"x = 5\n    x = \"five\"\n    return 0", sort},
		{"x = 0\n    if c:\n        x = True\n    return 0", sort},
		{"x = 7\n    if c:\n        x = Some(3)\n    return 0", sort},
		{"ys = [0]\n    if c:\n        ys = 5\n    return 0", sort},
		{"ys = [0]\n    ys = {\"a\": 1}\n    return 0", sort},
		{"e = bx\n    e = Crate(n=1)\n    return 0", sort},
		{"q = Some(1)\n    q = Dot\n    return 0", elems},
		{"k = n\n    while k > 0:\n        k = \"s\"\n    return 0", sort},
		// A parameter is a variable too.
		{"n = 3\n    return n", ""},
		{"n = \"s\"\n    return 0", sort},
		{"s = 1\n    return 0", sort},
		// Loop variables.
		{"for i in 0..3:\n        print(i)\n    for i in xs:\n        print(i)\n    return 0", ""},
		{"x = 5\n    for x in xs:\n        print(x)\n    return x", ""},
		{"x = 5\n    for x in ss:\n        print(x)\n    return 0", sort},
		{"x = \"a\"\n    for x in 0..3:\n        print(x)\n    return 0", sort},
		{"ys: list[int] = [5]\n    for ys in xss:\n        print(ys)\n    return 0", ""},
		{"ys: list[int[1..9]] = [5]\n    for ys in xss:\n        print(ys)\n    return 0", elems},
		// Names in patterns.
		{"v = 4\n    match o:\n        Some(v) -> print(v)\n        None -> print(0)\n    return v", ""},
		{"v = 4\n    match os:\n        Some(v) -> print(v)\n        None -> print(0)\n    return 0", sort},
		{"v = \"a\"\n    r = match o:\n        Some(v) -> v\n        None -> 0\n    return r", sort},
		{"ys: list[int[1..9]] = [5]\n    match ol:\n        Some(ys) -> print(ys)\n        None -> print(0)\n    return 0", elems},
		{"q: Option[int[1..9]] = Some(1)\n    match Some(o):\n        Some(q) -> print(q)\n        None -> print(0)\n    return 0", elems},
		// A lambda parameter is a variable of its own.
		{"x = \"a\"\n    ys = xs |> filter(x => x > 0)\n    return len(x)", ""},
		// A name first assigned in a branch ends with the branch.
		{"if c:\n        x = 5\n        print(x)\n    else:\n        x = \"s\"\n        print(x)\n    return 0", ""},
	}
	for _, tc := range cases {
		prog, err := parser.Parse("t.anm", prelude+"    "+tc.body+"\n")
		if err != nil {
			t.Fatalf("%q: parse failed: %v", tc.body, err)
		}
		_, err = Check(prog)
		switch {
		case tc.want == "" && err != nil:
			t.Errorf("%q: rejected: %v", tc.body, err)
		case tc.want != "" && (err == nil || !strings.Contains(err.Error(), tc.want)):
			t.Errorf("%q: want an error with %q, got %v", tc.body, tc.want, err)
		}
	}
}

// A variable with a range keeps it: a second declaration, a loop variable
// and a name in a pattern must have the very range, and every assignment
// is recorded for the kernel to prove the value in it.
func TestSemaVariableKeepsItsRange(t *testing.T) {
	prelude := `
type Small = int[1..9]

def f(n: int, p: int[1..9], xs: list[int], rs: list[int[1..9]], o: Option[int], ro: Option[int[1..9]]) -> int:
`
	const keeps = "a variable keeps its range"
	cases := []struct {
		body string
		want string
	}{
		{"y: int[1..9] = 5\n    y = n\n    y += 1\n    return y", ""},
		{"y: int[1..9] = 5\n    y: int[1..9] = n\n    return y", ""},
		{"y: Small = 5\n    y: int[1..9] = n\n    return y", ""},
		{"y = 5\n    y: int = n\n    return y", ""},
		{"y: int[1..9] = 5\n    for y in rs:\n        print(y)\n    return y", ""},
		{"y: int[1..9] = 5\n    match ro:\n        Some(y) -> print(y)\n        None -> print(0)\n    return y", ""},
		// A variable without a range may be shadowed by one with a range.
		{"y = 5\n    for y in rs:\n        print(y)\n    return y", ""},
		{"y = 5\n    y: int[1..9] = n\n    return y", keeps},
		{"y: int[1..9] = 5\n    y: int = n\n    return y", keeps},
		{"y: int[1..9] = 5\n    y: int[0..9] = n\n    return y", keeps},
		{"p: int[0..9] = n\n    return p", keeps},
		{"y: int[1..9] = 5\n    for y in xs:\n        print(y)\n    return y", keeps},
		{"y: int[1..9] = 5\n    for y in 0..n:\n        print(y)\n    return y", keeps},
		{"for p in xs:\n        print(p)\n    return p", keeps},
		{"y: int[1..9] = 5\n    match o:\n        Some(y) -> print(y)\n        None -> print(0)\n    return y", keeps},
		{"y: int[1..9] = 5\n    match n:\n        y -> print(y)\n    return y", keeps},
		{"y: int[1..9] = 5\n    r = match o:\n        Some(y) -> y\n        None -> 0\n    return r", keeps},
		{"for x in rs:\n        match o:\n            Some(x) -> print(x)\n            None -> print(0)\n    return 0", keeps},
	}
	for _, tc := range cases {
		prog, err := parser.Parse("t.anm", prelude+"    "+tc.body+"\n")
		if err != nil {
			t.Fatalf("%q: parse failed: %v", tc.body, err)
		}
		_, err = Check(prog)
		switch {
		case tc.want == "" && err != nil:
			t.Errorf("%q: rejected: %v", tc.body, err)
		case tc.want != "" && (err == nil || !strings.Contains(err.Error(), tc.want)):
			t.Errorf("%q: want an error with %q, got %v", tc.body, tc.want, err)
		}
	}

	// Every assignment to a ranged variable is recorded, annotated or not,
	// to a parameter and a loop variable as well; none to a plain int.
	src := prelude + "    y: int[1..9] = 5\n    y = n\n    p = n\n    z = n\n    z = 3\n    for x in rs:\n        x = n\n    return y\n"
	prog, err := parser.Parse("t.anm", src)
	if err != nil {
		t.Fatalf("parse failed: %v", err)
	}
	info, err := Check(prog)
	if err != nil {
		t.Fatalf("rejected: %v", err)
	}
	got := map[string]int{}
	for let, rng := range info.LetRanges {
		if rng.Lo != 1 || rng.Hi != 9 {
			t.Errorf("%s: recorded range %s", let.Name, rng)
		}
		got[let.Name]++
	}
	if got["y"] != 2 || got["p"] != 1 || got["x"] != 1 || got["z"] != 0 || len(got) != 3 {
		t.Errorf("recorded assignments per variable: %v", got)
	}
}

// A lambda, a built-in function and a pipeline stage are called with what
// they take: both backends read arguments by position without counting
// them, and an argument that is not given is None when the program runs.
func TestSemaCallsAreGivenWhatTheyTake(t *testing.T) {
	const head = "import std.fp as fp\n\ntype Shape = Circle(r: int[1..9]) | Dot\n\nentity Box:\n    n: int[1..9]\n\ndef main() -> int:\n    xs: list[int[1..9]] = [1, 2, 3]\n    ss: list[str] = [\"a\"]\n    o: Option[int] = Some(1)\n    r: Result[int, str] = Ok(1)\n    w: Option[int[1..9]] = Some(1)\n    ol: Option[list[int]] = None\n    on: Option[Option[int[1..9]]] = None\n    ow: Option[list[int[1..9]]] = None\n    rl: Result[int, list[int[1..9]]] = Err(xs)\n"
	rejected := map[string]string{
		"g = (a, b) => b\n    n = g(1)":          "this function takes 2 arguments, got 1",
		"g = (a) => a\n    n = g(1, 2)":          "this function takes 1 argument, got 2",
		"g = () => 5\n    n = g(1)":              "this function takes 0 arguments, got 1",
		"g = (a) => a\n    n = g(a=1)":           "a lambda takes its arguments by position",
		"ys = xs |> map((a, b) => b)":            "the function of map takes 1 parameter, got one with 2",
		"ys = xs |> filter(() => True)":          "the function of filter takes 1 parameter, got one with 0",
		"n = xs |> fold(5, (a, x, z) => z)":      "the function of fold takes 2 parameters, got one with 3",
		"n = xs |> fold(5, (a) => a)":            "the function of fold takes 2 parameters, got one with 1",
		"ys = xs |> flat_map((a, b) => [b])":     "the function of flat_map takes 1 parameter",
		"b = xs |> any((a, b) => a > 1)":         "the function of any takes 1 parameter",
		"g = (a, b) => b\n    ys = xs |> map(g)": "the function of map takes 1 parameter, got one with 2",
		"ys = xs |> take()":                      "take takes 1 argument after the value it works on, got 0",
		"ys = xs |> drop()":                      "drop takes 1 argument",
		"ys = xs |> map()":                       "map takes 1 argument",
		"b = xs |> any()":                        "any takes 1 argument",
		"n = xs |> sum(1)":                       "sum takes 0 arguments",
		"ys = xs |> filter_ok(1)":                "filter_ok takes 0 arguments",
		"ys = xs |> filter(x => x > 1, 2)":       "filter takes 1 argument",
		"n = xs |> fold((a, x) => a)":            "fold takes 2 arguments",
		"n = o |> unwrap_or()":                   "unwrap_or takes 1 argument",
		"ys = 5 |> take(1)":                      "take takes a list, got",
		"n = xs |> unwrap_or(0)":                 "unwrap_or takes an Option or a Result, got",
		"ys = o |> map(x => x)":                  "map takes a list, got",
		"ys = xs |> and_then(x => x)":            "and_then takes an Option or a Result, got",
		"ys = xs |> take(\"a\")":                 "take takes an int, got str",
		"n = ss |> sum()":                        "sum takes a list of int, got",
		"ys = xs |> map(5)":                      "map takes a function, got",
		"ys = xs |> fp.take()":                   "take takes 1 argument",
		"ys = fp.take(xs)":                       "take takes 1 argument",
		"ys = fp.take()":                         "take takes the value it works on as its first argument",
		"ys = fp.map(xs, (a, b) => b)":           "the function of map takes 1 parameter",
		"ys = fp.nope(xs)":                       "module std.fp has no member",
		"n = abs()":                              "abs() takes 1 argument, got 0",
		"n = min(1)":                             "min() takes 2 arguments, got 1",
		"n = max(1, 2, 3)":                       "max() takes 2 arguments, got 3",
		"s = str()":                              "str() takes 1 argument, got 0",
		"assert()":                               "assert() takes 1 argument, got 0",
		"assert(5)":                              "argument 1 of assert() is a bool, got",
		"assert(1 == 2, 3)":                      "argument 2 of assert() is a str, got",
		"n = abs(\"a\")":                         "argument 1 of abs() is an int, got str",
		"n = min(\"a\", \"b\")":                  "argument 1 of min() is an int, got str",
		"n = len(5)":                             "len() takes a list, a map or a string, got",
		"oz: Option[int] = Some(0)\n    a = on |> unwrap_or(oz)":     "takes a default that is Option[int[1..9]], got Option[int]",
		"zs: list[int] = [0]\n    ys = zs |> fold(xs, (a, x) => zs)": "the function of fold gives list[int[1..9]] as fold starts with, got list[int]",
		"n = xs |> fold(0, (a, x) => \"s\")":                         "the function of fold gives int[0..0] as fold starts with, got str",
		"ys = ol |> unwrap_or(xs)":                                   "unwrap_or on Option[list[int]] takes a default that is list[int], got list[int[1..9]]",
		"ys = fp.unwrap_or(ol, xs)":                                  "takes a default that is list[int], got list[int[1..9]]",
		"g = (v) => [v]\n    d = g(0)\n    ys = ow |> unwrap_or(d)":  "takes a default that is list[int[1..9]], got list[int]",
		"zs: list[int] = [0]\n    q = rl |> and_then(v => Err(zs))":  "gives a Result with the error of Result[int, list[int[1..9]]], got",
		"g = (v) => v\n    n = 1 |> g(2)":                            "this function takes 1 argument, got 2",
		"g = (a, b) => b\n    n = 1 |> g":                            "this function takes 2 arguments, got 1",
		"n = \"a\" |> abs()":                                         "argument 1 of abs() is an int, got str",
		"n = 1 |> min()":                                             "min() takes 2 arguments, got 1",
		"p = 1 |> Some()":                                            "Some makes a value and is not a pipeline stage",
		"p = 1 |> Some":                                              "Some makes a value and is not a pipeline stage",
		"p = 1 |> Ok()":                                              "Ok makes a value and is not a pipeline stage",
		"b = 1 |> Box()":                                             "Box makes a value and is not a pipeline stage",
		"c = 1 |> Circle()":                                          "Circle makes a value and is not a pipeline stage",
		"n = o |> unwrap_or(\"x\")":                                  "unwrap_or on Option[int] takes a default that is int, got str",
		"p = o |> and_then(v => 1)":                                  "the function of and_then gives an Option, got",
		"p = o |> and_then(v => Ok(v))":                              "the function of and_then gives an Option, got",
		"p = fp.and_then(o, v => 1)":                                 "the function of and_then gives an Option, got",
		"p = r |> and_then(v => Some(v))":                            "the function of and_then gives a Result, got",
		"p = r |> and_then(v => Err(5))":                             "gives a Result with the error of Result[int, str], got",
	}
	for body, want := range rejected {
		prog, err := parser.Parse("call.anm", head+"    "+body+"\n    return 0\n")
		if err != nil {
			t.Fatalf("%q: parse error: %v", body, err)
		}
		if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%q: expected %q, got %v", body, want, err)
		}
	}
	accepted := []string{
		"g = (a, b) => b\n    n = g(1, 2)",
		"k = () => 7\n    n = k()",
		"g = (v) => v > 1\n    ys = xs |> filter(g)\n    b = xs |> any(g)",
		"ys = xs |> map(x => x) |> take(2) |> drop(1)",
		"n = xs |> fold(0, (a, x) => x)",
		"ys = xs |> fold(xs, (a, x) => a)\n    s = ss |> fold(\"\", (a, w) => w)\n    b = xs |> fold(True, (a, x) => x > 1)",
		"n = xs |> sum()",
		"n = o |> unwrap_or(0)\n    p = o |> and_then(v => Some(v))",
		"f = xs |> find(x => x > 1)\n    b = xs |> all(x => x > 0)",
		"ys = xs |> fp.map(x => x)\n    n = xs |> fp.sum()",
		"ys = fp.map(xs, x => x)\n    n = fp.fold(xs, 0, (a, x) => x)\n    m = fp.sum(xs)\n    zs = fp.take(xs, 2)",
		"n = abs(0 - 3) + min(1, 2) + max(1, 2) + len(xs) + len(\"ab\")\n    s = str(5)",
		"assert(1 == 1)\n    assert(1 == 1, \"ok\")",
		"g = (v) => v\n    h = (a, b) => b\n    n = 1 |> g()\n    m = 1 |> g\n    k = 1 |> h(2)",
		"n = (0 - 3 |> abs()) + (2 |> min(1)) + (\"ab\" |> len()) + (xs |> len)\n    s = 5 |> str()\n    7 |> print()",
		"p = o |> and_then(v => Some(v))\n    q = o |> and_then(v => None)",
		"u = r |> and_then(v => Ok(\"s\"))\n    e = r |> and_then(v => Err(\"bad\"))\n    n = r |> unwrap_or(0)",
		"k: int[0..9] = w |> unwrap_or(0)\n    j: int[0..9] = fp.unwrap_or(w, 0)",
		"a = on |> unwrap_or(Some(1))\n    b = on |> unwrap_or(None)\n    c = on |> unwrap_or(w)",
		"ys = ow |> unwrap_or(xs)\n    zs = ow |> unwrap_or([])\n    ws = ow |> unwrap_or([1, 2])\n    q = rl |> and_then(v => Err(xs))",
		"oo: Option[Option[int]] = None\n    om: Option[map[str, int]] = None\n    a = oo |> unwrap_or(None)\n    b = oo |> unwrap_or(Some(1))\n    c = om |> unwrap_or({})",
	}
	for _, body := range accepted {
		prog, err := parser.Parse("call.anm", head+"    "+body+"\n    return 0\n")
		if err != nil {
			t.Fatalf("%q: parse error: %v", body, err)
		}
		if _, err := Check(prog); err != nil {
			t.Errorf("%q: expected no error, got %v", body, err)
		}
	}
}

// A standard function or handle method takes its arguments by position and
// reads them as what it expects: the call is checked against that.
func TestSemaStandardCallsAreGivenWhatTheyTake(t *testing.T) {
	const head = `import std.socket as sock
import std.concurrent as conc
import std.time as time
import std.crypto as crypto
import std.bytes as bytes
import std.fs as fs
import std.cli as cli
import std.json as json
import std.requests as req

def use(conn: sock.TcpStream, ln: sock.TcpListener, file: fs.File, pool: conc.ThreadPool) -> int:
    sess = req.Session(4)
    bv = bytes.from_str("abcd")
    ch = conc.Channel[int[1..9]](cap=2)
    lists = conc.Channel[list[int[1..9]]](cap=2)
    m = conc.Mutex(5)
    held = conc.Mutex([1])
    sem = conc.Semaphore(1)
    n: int = 3
    small: int[1..9] = 3
    zs: list[int] = [0]
`
	rejected := map[string]string{
		// How many.
		"time.sleep_ms()":                          "std.time.sleep_ms takes 1 argument, got 0",
		"time.sleep_ms(1, 2)":                      "std.time.sleep_ms takes 1 argument, got 2",
		"t = time.now_ms(1)":                       "std.time.now_ms takes 0 arguments, got 1",
		"s = crypto.sha256()":                      "std.crypto.sha256 takes 1 argument, got 0",
		"s = crypto.hmac_sha256(\"k\")":            "std.crypto.hmac_sha256 takes 2 arguments, got 1",
		"s = json.encode()":                        "std.json.encode takes 1 argument, got 0",
		"r = fs.read_text()":                       "std.fs.read_text takes 1 argument, got 0",
		"r = fs.open()":                            "std.fs.open takes 1 to 2 arguments, got 0",
		"r = fs.open(\"p\", \"w\", \"x\")":         "std.fs.open takes 1 to 2 arguments, got 3",
		"r = sock.connect_tcp(\"h\")":              "std.socket.connect_tcp takes 2 arguments, got 1",
		"p = conc.ThreadPool(2)":                   "std.concurrent.ThreadPool takes 2 arguments, got 1",
		"s = conc.Semaphore()":                     "std.concurrent.Semaphore takes 1 argument, got 0",
		"x = conc.Mutex()":                         "std.concurrent.Mutex takes 1 argument, got 0",
		"r = conn.send_text()":                     "send_text() of a sock.TcpStream takes 1 argument, got 0",
		"r = conn.recv_text(1, 2)":                 "recv_text() of a sock.TcpStream takes 0 to 1 argument, got 2",
		"p = ln.port(1)":                           "port() of a sock.TcpListener takes 0 arguments, got 1",
		"r = file.write_text()":                    "write_text() of a fs.File takes 1 argument, got 0",
		"b = bv.read_u8()":                         "read_u8() of a bytes.ByteView takes 1 argument, got 0",
		"ok = ch.send()":                           "send() of a conc.Channel takes 1 argument, got 0",
		"v = ch.recv(1)":                           "recv() of a conc.Channel takes 0 arguments, got 1",
		"m.set()":                                  "set() of a conc.Mutex takes 1 argument, got 0",
		"sem.acquire(1)":                           "acquire() of a conc.Semaphore takes 0 arguments, got 1",
		"r = sess.post(\"u\", timeout_ms=5)":       "post() of a req.Session takes 2 arguments and timeout_ms, got 2",
		"r = sess.get(\"u\", \"b\", timeout_ms=5)": "get() of a req.Session takes 1 argument and timeout_ms, got 3",
		// What kind.
		"time.sleep_ms(\"a\")":                "argument 1 of std.time.sleep_ms is an int, got str",
		"s = crypto.sha256(5)":                "argument 1 of std.crypto.sha256 is a str, got int",
		"o = cli.env_get(5)":                  "argument 1 of std.cli.env_get is a str, got int",
		"r = sock.listen_tcp(80, \"h\")":      "argument 1 of std.socket.listen_tcp is a str, got int",
		"r = conn.send_text(5)":               "argument 1 of send_text() of a sock.TcpStream is a str, got int",
		"r = conn.recv_text(\"a\")":           "argument 1 of recv_text() of a sock.TcpStream is an int, got str",
		"b = bv.read_u8(\"a\")":               "argument 1 of read_u8() of a bytes.ByteView is an int, got str",
		"xs = conc.parallel_map(5, (x) => x)": "argument 1 of std.concurrent.parallel_map is a list, got int",
		"xs = conc.parallel_map(zs, 5)":       "argument 2 of std.concurrent.parallel_map is a function of 1 argument, got int",
		"xs = conc.parallel_map(zs, () => 1)": "argument 2 of std.concurrent.parallel_map is a function of 1 argument",
		"f = pool.submit(5)":                  "argument 1 of submit() of a conc.ThreadPool is a function of 0 arguments, got int",
		"f = pool.submit((a) => a)":           "argument 1 of submit() of a conc.ThreadPool is a function of 0 arguments",
		"rs = req.gather(5)":                  "argument 1 of std.requests.gather is a list, got int",
		"rs = req.gather([1, 2])":             "gather takes futures, got int",
		// By position.
		"p = conc.ThreadPool(queue_cap=4, workers=2)": "argument 1 of std.concurrent.ThreadPool is \"workers\"",
		"time.sleep_ms(millis=5)":                     "argument 1 of std.time.sleep_ms is \"ms\"",
		"time.sleep_ms(mut n)":                        "no `mut` or `own`",
		// What a channel or a mutex keeps.
		"ok = ch.send(0)":              "argument 1 of send() of a conc.Channel is int[1..9], got int[0..0]",
		"ok = ch.send(n)":              "argument 1 of send() of a conc.Channel is int[1..9], got int",
		"ok = ch.send(\"s\")":          "argument 1 of send() of a conc.Channel is int[1..9], got str",
		"ok = lists.send(zs)":          "argument 1 of send() of a conc.Channel is list[int[1..9]], got list[int]",
		"m.set(\"s\")":                 "argument 1 of set() of a conc.Mutex is int, got str",
		"held.set(5)":                  "argument 1 of set() of a conc.Mutex is list[int], got int",
		"held.with_lock((v) => \"s\")": "the function of with_lock gives what the mutex holds, list[int], got str",
		"m.with_lock(5)":               "argument 1 of with_lock() of a conc.Mutex is a function of 1 argument, got int",
		"rs: list[int[1..9]] = [1]\n    ranged = conc.Mutex(rs)\n    ranged.with_lock((v) => [0])": "the function of with_lock gives what the mutex holds, list[int[1..9]], got list[int]",
		"r = json.decode()": "std.json.decode takes 1 argument, got 0",
		// Only to be called.
		"g = time.sleep_ms":             "std.time.sleep_ms is not a value",
		"g = conn.send_text":            "send_text() of a sock.TcpStream is not a value",
		"xs = zs |> map(crypto.sha256)": "std.crypto.sha256 is not a value",
		// Piped: `x |> o.f(a)` is o.f(x, a).
		"ok = 0 |> ch.send()":                "argument 1 of send() of a conc.Channel is int[1..9], got int[0..0]",
		"s = 5 |> crypto.sha256()":           "argument 1 of std.crypto.sha256 is a str, got int",
		"s = \"a\" |> crypto.sha256(\"b\")":  "std.crypto.sha256 takes 1 argument, got 2",
		"((v) => \"s\") |> held.with_lock()": "the function of with_lock gives what the mutex holds, list[int], got str",
		"rs = [1, 2] |> req.gather()":        "gather takes futures, got int",
		"x = conc.Mutex() |> print()":        "std.concurrent.Mutex takes 1 argument, got 0",
		// A piped call inside the arguments of a piped call.
		"\"s\" |> m.set(0 |> bv.read_u8())":                     "argument 1 of set() of a conc.Mutex is int, got str",
		"7 |> m.set(0 |> bv.read_u8())":                         "set() of a conc.Mutex takes 1 argument, got 2",
		"(\"s\" |> bv.read_u8()) |> m.set()":                    "argument 1 of read_u8() of a bytes.ByteView is an int, got str",
		"s = 5 |> crypto.hmac_sha256(\"a\" |> crypto.sha256())": "argument 1 of std.crypto.hmac_sha256 is a str, got int",
		"s = \"k\" |> crypto.hmac_sha256(5 |> crypto.sha256())": "argument 1 of std.crypto.sha256 is a str, got int",
		// The timeout of a piped request is where the call has it.
		"r = \"u\" |> sess.get()":      "'get' requires explicit bounded 'timeout_ms: int[1..300_000]'",
		"r = \"u\" |> req.post(\"b\")": "'post' requires explicit bounded 'timeout_ms: int[1..300_000]'",
		"r = \"u\" |> sess.get(\"v\")": "timeout_ms must be int[1..300_000], got str",
		"r = \"u\" |> req.get(0)":      "timeout_ms range [0..0] exceeds legal contract int[1..300_000]",
		// What is not there.
		"x = conc.nope()":                      "module std.concurrent has no member \"nope\"",
		"rs = conc.gather([1])":                "module std.concurrent has no member \"gather\"",
		"sem.nope()":                           "handle conc.Semaphore has no method \"nope\"",
		"m.nope()":                             "handle conc.Mutex has no method \"nope\"",
		"r = conn.send_bytes(\"x\")":           "handle sock.TcpStream has no method \"send_bytes\"",
		"xs = pool.map_parallel(zs, (x) => x)": "handle conc.ThreadPool has no method \"map_parallel\"",
		"r = req.serve_once(80)":               "module std.requests has no member \"serve_once\"",
	}
	for body, want := range rejected {
		prog, err := parser.Parse("std.anm", head+"    "+body+"\n    return 0\n")
		if err != nil {
			t.Fatalf("%q: parse error: %v", body, err)
		}
		if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%q: expected %q, got %v", body, want, err)
		}
	}
	accepted := []string{
		"time.sleep_ms(5)\n    time.sleep_ms(ms=n)\n    t = time.now_ms()",
		"s = crypto.sha256(\"a\")\n    h = crypto.hmac_sha256(\"k\", \"a\")\n    b = crypto.constant_time_eq(s, h)",
		"r = fs.open(\"p\")\n    w = fs.open(\"p\", \"w\")\n    t = fs.read_text(\"p\")\n    a = fs.write_atomic(\"p\", \"x\")",
		"args = cli.args()\n    o = cli.env_get(\"HOME\")\n    s = json.encode(zs)",
		"p = conc.ThreadPool(workers=2, queue_cap=4)\n    c2 = conc.Channel[int](cap=n)\n    c3 = conc.Channel[int]()\n    s2 = req.Session()",
		"r = conn.send_text(\"x\")\n    a = conn.recv_text()\n    b = conn.recv_text(16)\n    p = ln.port()",
		"r = ln.accept(timeout_ms=10)\n    q = ln.accept(10)",
		"r = sess.get(\"u\", timeout_ms=5)\n    q = sess.get(\"u\", 5)\n    p = sess.post(\"u\", \"b\", timeout_ms=5)\n    f = sess.get_async(\"u\", timeout_ms=5)\n    rs = req.gather([f])",
		"r = req.get(\"u\", timeout_ms=5)\n    p = req.post(\"u\", \"b\", 5)",
		"r = file.read_text()\n    w = file.write_text(\"x\")",
		"b = bv.read_u8(0)\n    l = bv.len()\n    s = bv.slice(1, 2)",
		"ok = ch.send(5)\n    ok2 = ch.send(small)\n    v = ch.recv()\n    ok3 = lists.send([1, 2])",
		"m.set(0)\n    m.set(n)\n    held.set(zs)\n    held.with_lock((v) => zs)\n    m.with_lock((v) => 7)\n    k = m.get()",
		"sem.acquire()\n    sem.release()",
		"(0 |> bv.read_u8()) |> m.set()\n    s = \"k\" |> crypto.hmac_sha256(\"a\" |> crypto.sha256())\n    h = (\"a\" |> crypto.sha256()) |> crypto.sha256()",
		"r = \"u\" |> req.get(5)\n    p = \"u\" |> req.post(\"b\", 5)\n    q = \"u\" |> sess.get(small)",
		"m2 = 5 |> conc.Mutex()\n    m2.set(0)\n    ((v) => zs) |> held.with_lock()\n    r = \"u\" |> sess.get(timeout_ms=5)",
		"s = \"abc\" |> crypto.sha256()\n    h = \"k\" |> crypto.hmac_sha256(\"abc\")\n    ok = 5 |> ch.send()\n    b = 1 |> bv.read_u8()\n    n |> time.sleep_ms()",
		"k = bytes.from_str(\"ab\").len()\n    g = (ms) => time.sleep_ms(ms)\n    g(1)",
		"rs: list[int[1..9]] = [1]\n    ranged = conc.Mutex(rs)\n    ranged.with_lock((v) => rs)\n    ranged.set([2, 3])",
		"f = pool.submit(() => 1)\n    g = pool.submit(() => \"s\")\n    rs = req.gather([f, g])\n    xs = conc.parallel_map(zs, (x) => x)",
	}
	for _, body := range accepted {
		prog, err := parser.Parse("std.anm", head+"    "+body+"\n    return 0\n")
		if err != nil {
			t.Fatalf("%q: parse error: %v", body, err)
		}
		if _, err := Check(prog); err != nil {
			t.Errorf("%q: expected no error, got %v", body, err)
		}
	}
	// A mutex holds values of the type of its first one, not of its range.
	prog, err := parser.Parse("std.anm", head+"    k = m.get()\n    return 0\n")
	if err != nil {
		t.Fatal(err)
	}
	info, err := Check(prog)
	if err != nil {
		t.Fatal(err)
	}
	for e, ty := range info.ExprTypes {
		if call, ok := e.(*ast.CallExpr); ok {
			if fe, ok := call.Callee.(*ast.FieldExpr); ok && fe.Field == "get" {
				if it, ok := ty.(*IntType); !ok || it.IsBounded {
					t.Errorf("m.get() of conc.Mutex(5): expected int, got %s", ty)
				}
			}
		}
	}
}

// A function that returns a value returns one on every path: where it ended
// without a return it gave (), and its caller was told the declared type.
func TestSemaEveryPathReturns(t *testing.T) {
	rejected := map[string]string{
		"def f(n: int) -> int:\n    if n > 0:\n        return 1\n":                                             "function f can end without a return",
		"def f(n: int) -> int:\n    if n > 0:\n        return 1\n    elif n < 0:\n        return 2\n":          "can end without a return",
		"def f(n: int) -> int:\n    if n > 0:\n        return 1\n    else:\n        print(n)\n":                "can end without a return",
		"def f(n: int) -> str:\n    print(n)\n":                                                                "it returns str",
		"def f(o: Option[int]) -> int:\n    match o:\n        Some(v) -> return v\n        None -> print(1)\n": "can end without a return",
		"def f(xs: list[int]) -> int:\n    for x in xs:\n        return x\n":                                   "can end without a return",
		"def f(n: int) -> int:\n    while n > 0:\n        return 1\n":                                          "can end without a return",
		"def f(n: int) -> int:\n    while False:\n        return 1\n":                                          "can end without a return",
		"def f(r: Result[int, str]) -> Result[int, str]:\n    v = r?\n":                                        "can end without a return",
		"def f(n: int) -> int:\n    if n > 0:\n        return 1\n    return\n":                                 "return needs a value of type int",
		"def f(n: int) -> list[int]:\n    return\n":                                                            "return needs a value of type list[int]",
	}
	for src, want := range rejected {
		prog, err := parser.Parse("ret.anm", src)
		if err != nil {
			t.Fatalf("%q: parse error: %v", src, err)
		}
		if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%q: expected an error with %q, got %v", src, want, err)
		}
	}
	accepted := []string{
		"def f(n: int) -> int:\n    if n > 0:\n        return 1\n    return 2\n",
		"def f(n: int) -> int:\n    if n > 0:\n        return 1\n    elif n < 0:\n        return 2\n    else:\n        return 3\n",
		"def f(o: Option[int]) -> int:\n    match o:\n        Some(v) -> return v\n        None -> return 0\n",
		"def f(o: Option[int]) -> int:\n    match o:\n        Some(v) ->\n            if v > 0:\n                return v\n            else:\n                return 0\n        None -> return 0\n",
		"def f(n: int) -> int:\n    while True:\n        if n > 0:\n            return 1\n",
		"def f(n: int) -> int:\n    return 1\n    print(n)\n",
		// A function that returns nothing may end anywhere.
		"def f(n: int):\n    if n > 0:\n        return\n    print(n)\n",
	}
	for _, src := range accepted {
		prog, err := parser.Parse("ret.anm", src)
		if err != nil {
			t.Fatalf("%q: parse error: %v", src, err)
		}
		if _, err := Check(prog); err != nil {
			t.Errorf("%q: expected no error, got %v", src, err)
		}
	}
}

// A workflow has one start: the backends run the last one written and the
// kernel walks from one of them.
func TestSemaWorkflowHasOneStart(t *testing.T) {
	src := "workflow W(n: int) -> int:\n    verify: sound\n\n    start -> done:\n        return 1\n\n    start -> done:\n        return 10 / n\n"
	prog, err := parser.Parse("wf.anm", src)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "more than one start") {
		t.Errorf("expected an error about a second start, got %v", err)
	}
}
