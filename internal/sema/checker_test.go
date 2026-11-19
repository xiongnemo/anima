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
