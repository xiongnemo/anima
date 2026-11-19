package sema

import (
	"strings"
	"testing"

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

// Two fork branches that write elements of the same map race, like two
// branches assigning the same variable.
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
	if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "concurrent write race") {
		t.Errorf("expected a concurrent write race error, got %v", err)
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

// The element-alias rule also holds for a call through a function value.
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
	if _, err := Check(prog); err == nil || !strings.Contains(err.Error(), "anti-aliasing") {
		t.Errorf("expected an anti-aliasing error, got %v", err)
	}
}
