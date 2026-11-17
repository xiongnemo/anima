package parser

import (
	"testing"

	"github.com/xiongnemo/anima/internal/ast"
)

func TestParseGatewayAndEscrowFullSyntax(t *testing.T) {
	src := `
import std.socket as sock
import std.requests as req
import std.concurrent as conc
import std.json as json

type PortNum   = int[1024..65535]
type Score     = int[0..100]
type FetchState = Cached(score: Score) | Fresh(score: Score) | Degraded

type MultiLineADT =
    | Alpha(x: int)
    | Beta

entity UpstreamQuote:
    provider: str
    score: Score
    weight: int[1..10]
    rel owner -> 1 Account
    invariant: score * weight <= 1000

port AuditLog:
    protocol:
        state Closed:
            on open_log -> Open
        state Open:
            on write_entry -> Open
            on close_log -> Closed
    extern def write_entry(amt: int[1..10_000], ok: bool)

def aggregate_quotes(quotes: list[UpstreamQuote, cap=8]) -> FetchState:
    requires: len(quotes) >= 0
    valid = quotes |> filter(q => q.score >= 10)
    match len(valid):
        0 -> return Degraded
        n if n >= 1 ->
            total = valid |> map(q => q.score) |> fold(0, (a, b) => a + b)
            return Fresh(score=total / n)

monitor RateLimiter:
    active: control int[0..2] = 0
    state Ready:
        invariant: active < 2
        on enter_req when active == 0 -> Ready:
            active = 1
        on enter_req when active == 1 -> Full:
            active = 2
    state Full:
        invariant: active == 2
        on leave_req -> Ready:
            active = 1

property ExclusiveWrite:
    state Idle:
        on enter_req -> Busy
    state Busy:
        on leave_req -> Idle

progress RequestMustFinish = {leave_req}

workflow FetchAllUpstreams(urls: list[str, cap=4], timeout: int[100..10_000]) -> FetchState:
    verify: sound, 1_safe
    pool http_conn: int[0..4] = 4

    start -> fanout_requests
    fork fanout_requests:
        branch node_a:
            acquire http_conn
            r1 = req.get("https://api-a.example.com/q", timeout_ms=timeout)
            release http_conn
        branch node_b:
            acquire http_conn
            r2 = req.get("https://api-b.example.com/q", timeout_ms=timeout)
            release http_conn
    join collect_responses

    step merge_result after collect_responses -> done:
        parsed = [r1, r2]
            |> filter_ok()
            |> map(resp => json.decode[UpstreamQuote](resp.body))
            |> filter_ok()
        return aggregate_quotes(parsed)

def serve_once(port: PortNum) -> Result[int, str]:
    listener = sock.listen_tcp("127.0.0.1", port)?
    conn = listener.accept(timeout_ms=5000)?
    state = run_workflow FetchAllUpstreams([], 2000)
    payload = match state:
        Fresh(s) -> json.encode({"status": "ok", "score": s})
        Cached(s) -> json.encode({"status": "cached", "score": s})
        Degraded -> json.encode({"status": "degraded", "score": 0})
    conn.send_text(payload)?
    conn.close()
    listener.close()
    return Ok(0)

system GatewaySys:
    compose:
        w1: FetchAllUpstreams
        lim: RateLimiter
    hide: {internal_step}
    check:
        deadlock_free
        satisfies ExclusiveWrite
        satisfies RequestMustFinish
        ltl: always (w1.enter_req -> eventually w1.leave_req)
`
	prog, err := Parse("gateway.anm", src)
	if err != nil {
		t.Fatalf("parse failed: %v", err)
	}
	if len(prog.Decls) != 17 {
		t.Fatalf("expected 17 top-level decls, got %d", len(prog.Decls))
	}
	sys, ok := prog.Decls[len(prog.Decls)-1].(*ast.SystemDecl)
	if !ok || sys.Name != "GatewaySys" || len(sys.Checks) != 4 {
		t.Fatalf("unexpected system decl: %+v", prog.Decls[len(prog.Decls)-1])
	}
}

func TestParseProceduralAndWithAndLoops(t *testing.T) {
	src := `
entity Acc:
    balance: int[0..100]

def loop_demo(mut a: Acc, n: int[0..10]) -> int:
    total = 0
    for i in 0..n:
        total += i
    i = n
    while i > 0:
        invariant: i >= 0
        decreases: i
        i -= 1
    b = a with { balance: 42 }
    s = f"bal={b.balance}"
    return total
`
	prog, err := Parse("loop.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	if len(prog.Decls) != 2 {
		t.Fatalf("expected 2 decls, got %d", len(prog.Decls))
	}
}
