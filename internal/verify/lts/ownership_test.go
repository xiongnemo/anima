package lts

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
)

const ownPrelude = `
import std.socket as sock
import std.concurrent as conc
import std.fs as fs

def close_it(own conn: sock.TcpStream) -> int:
    conn.close()
    return 0

def peek(conn: sock.TcpStream) -> Result[str, str]:
    return conn.recv_text(16)

def accept_one(ln: sock.TcpListener) -> int:
    match ln.accept(timeout_ms=10):
        Ok(c) -> c.close()
        Err(e) -> print(e)
    return 0

def fallible() -> Result[int, str]:
    return Err("no")

port AuditLog:
    protocol:
        state Closed:
            on open_log -> Open
        state Open:
            on close_log -> Closed
    extern def open_log()
    extern def close_log()
`

// ownershipErrors returns the front-end error or the typestate errors of src.
func ownershipErrors(t *testing.T, src string) string {
	t.Helper()
	prog, err := parser.Parse("own_test.anm", ownPrelude+src)
	if err != nil {
		return "parse: " + err.Error()
	}
	info, err := sema.Check(prog)
	if err != nil {
		return "sema: " + err.Error()
	}
	var msgs []string
	for _, e := range Verify(info).TypestateErrors {
		msgs = append(msgs, e.Message)
	}
	return strings.Join(msgs, "\n")
}

func TestOwnershipAccepts(t *testing.T) {
	cases := map[string]string{
		"borrowed parameter left open": `
def f(conn: sock.TcpStream) -> Result[int, str]:
    _ = conn.send_text("x")?
    s = conn.recv_text(8)?
    return Ok(len(s))
`,
		"owned parameter closed": `
def f(own conn: sock.TcpStream) -> int:
    conn.close()
    return 0
`,
		"owned parameter passed on": `
def f(own conn: sock.TcpStream) -> int:
    return close_it(own conn)
`,
		"owned parameter returned": `
def f(own conn: sock.TcpStream) -> sock.TcpStream:
    return conn
`,
		"borrow then close": `
def f() -> Result[str, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    r = peek(conn)
    conn.close()
    return r
`,
		"both branches close": `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    if b:
        conn.close()
    else:
        conn.close()
    return Ok(1)
`,
		"one branch closes, the other gives it away": `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    match b:
        True -> conn.close()
        False -> _ = close_it(own conn)
    return Ok(1)
`,
		"closing branch returns": `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    if b:
        conn.close()
        return Ok(0)
    conn.close()
    return Ok(1)
`,
		"failure handled by match": `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    match conn.send_text("x"):
        Ok(n) -> print(n)
        Err(e) ->
            conn.close()
            return Err(e)
    conn.close()
    return Ok(1)
`,
		"factory returns the handle": `
def dial() -> Result[sock.TcpStream, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    return Ok(conn)

def f() -> Result[int, str]:
    conn = dial()?
    conn.close()
    return Ok(1)
`,
		"factory result forwarded": `
def dial() -> Result[sock.TcpStream, str]:
    return sock.connect_tcp("127.0.0.1", 1)
`,
		"unmatched result matched later": `
def f() -> int:
    r = sock.connect_tcp("127.0.0.1", 1)
    match r:
        Ok(conn) -> conn.close()
        Err(e) -> print(e)
    return 0
`,
		"alias then close the alias": `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    c2 = conn
    c2.close()
    return Ok(1)
`,
		"handle opened and closed per iteration": `
def f(ln: sock.TcpListener) -> int:
    n: int[0..3] = 0
    while n < 3:
        decreases: 3 - n
        match ln.accept(timeout_ms=10):
            Ok(c) -> c.close()
            Err(e) -> print(e)
        n += 1
    return 0
`,
		"connection moved into a task": `
def f() -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    pool = conc.ThreadPool(2, 4)
    match ln.accept(timeout_ms=10):
        Ok(conn) -> _ = pool.submit(() => close_it(own conn))
        Err(e) -> print(e)
    pool.shutdown()
    ln.close()
    return Ok(0)
`,
		"listener lent to tasks until shutdown": `
def f() -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    pool = conc.ThreadPool(2, 4)
    a = pool.submit(() => accept_one(ln))
    b = pool.submit(() => accept_one(ln))
    _ = a.await()
    _ = b.await()
    pool.shutdown()
    ln.close()
    return Ok(0)
`,
		"listener lent until await": `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    a = pool.submit(() => accept_one(ln))
    _ = a.await()
    ln.close()
    return Ok(0)
`,
		"file": `
def f() -> Result[str, str]:
    h = fs.open("/tmp/x", "r")?
    r = h.read_text()
    h.close()
    return r
`,
		"one concurrent branch uses the stream": `
workflow W(conn: sock.TcpStream, ln: sock.TcpListener) -> int:
    start -> go:
        n = 1
    fork go:
        branch a:
            call conn.send_text("a")
            call ln.port()
        branch b:
            call ln.port()
    join joined
    step fin after joined -> done:
        return 0
`,
		"stream lent to a workflow": `
workflow W(conn: sock.TcpStream) -> int:
    start -> fin:
        n = 1
    step fin -> done:
        return 0

def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    n = run_workflow W(conn)
    conn.close()
    return Ok(n)
`,
		"every arm of a match expression moves the handle": `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    n = match b:
        True -> close_it(own conn)
        False -> close_it(own conn) + 1
    return Ok(n)
`,
		"fallible argument evaluated before the handle is opened": `
def keep(conn: sock.TcpStream, n: int) -> int:
    return n

def f() -> Result[int, str]:
    n = fallible()?
    conn = sock.connect_tcp("127.0.0.1", 1)?
    m = keep(conn, n)
    conn.close()
    return Ok(m)
`,
		"port opened and closed in a loop body": `
def f(xs: list[int]) -> int:
    for x in xs:
        AuditLog.open_log()
        AuditLog.close_log()
    return 0
`,
		"task fails only after the callee took the handle": `
def try_close(own conn: sock.TcpStream) -> Result[int, str]:
    conn.close()
    return Err("closed")

def f(pool: conc.ThreadPool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    a = pool.submit(() => try_close(own conn)?)
    _ = a.await()
    return Ok(0)
`,
		"own is still an ordinary name": `
def f(own: int) -> int:
    return own
`,
	}
	for name, src := range cases {
		if got := ownershipErrors(t, src); got != "" {
			t.Errorf("%s: expected no error, got:\n%s", name, got)
		}
	}
}

func TestOwnershipRejects(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"owned parameter never closed", `
def f(own conn: sock.TcpStream) -> int:
    return 0
`, "resource handle leak"},
		{"borrowed parameter closed", `
def f(conn: sock.TcpStream) -> int:
    conn.close()
    return 0
`, "is borrowed"},
		{"borrowed parameter given away", `
def f(conn: sock.TcpStream) -> int:
    return close_it(own conn)
`, "cannot give away borrowed"},
		{"borrowed parameter returned", `
def f(conn: sock.TcpStream) -> sock.TcpStream:
    return conn
`, "cannot return borrowed"},
		{"missing own at the call", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    return Ok(close_it(conn))
`, "requires 'own'"},
		{"own on a borrowed parameter", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    r = peek(own conn)
    conn.close()
    return Ok(1)
`, "unexpected 'own'"},
		{"own parameter that is not a handle", `
def f(own n: int) -> int:
    return n
`, "must be a linear handle"},
		{"use after close", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    conn.close()
    r = conn.recv_text(8)
    return Ok(1)
`, "use-after-close"},
		{"use after move", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    _ = close_it(own conn)
    r = conn.recv_text(8)
    return Ok(1)
`, "after it was moved"},
		{"moved twice", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    _ = close_it(own conn)
    _ = close_it(own conn)
    return Ok(1)
`, "after it was moved"},
		{"borrow after close", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    conn.close()
    r = peek(conn)
    return Ok(1)
`, "use-after-close"},
		{"alias, close one, use the other", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    c2 = conn
    c2.close()
    r = conn.recv_text(8)
    return Ok(1)
`, "after it was moved"},
		{"double close", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    conn.close()
    conn.close()
    return Ok(1)
`, "use-after-close"},
		{"closed in a loop", `
def f(xs: list[int]) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    for x in xs:
        conn.close()
    return Ok(1)
`, "the loop body changes"},
		{"moved in a loop", `
def f(xs: list[int]) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    for x in xs:
        _ = close_it(own conn)
    return Ok(1)
`, "the loop body changes"},
		{"opened in a loop and never closed", `
def f(xs: list[int]) -> int:
    for x in xs:
        match sock.connect_tcp("127.0.0.1", 1):
            Ok(c) -> print(x)
            Err(e) -> print(e)
    return 0
`, "resource handle leak"},
		{"closed on one branch only", `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    if b:
        conn.close()
    return Ok(1)
`, "every path must leave it in the same state"},
		{"early return leaks", `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    if b:
        return Ok(0)
    conn.close()
    return Ok(1)
`, "resource handle leak"},
		{"try while owning an open handle", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    _ = conn.send_text("x")?
    conn.close()
    return Ok(1)
`, "`?` may return early"},
		{"second open may fail while the first is open", `
def f() -> Result[int, str]:
    a = sock.connect_tcp("127.0.0.1", 1)?
    b = sock.connect_tcp("127.0.0.1", 2)?
    a.close()
    b.close()
    return Ok(1)
`, "`?` may return early"},
		{"returned handle never closed by the caller", `
def dial() -> Result[sock.TcpStream, str]:
    return sock.connect_tcp("127.0.0.1", 1)

def f() -> Result[int, str]:
    conn = dial()?
    return Ok(1)
`, "resource handle leak"},
		{"returned result never matched", `
def f() -> int:
    r = sock.connect_tcp("127.0.0.1", 1)
    return 0
`, "resource handle leak"},
		{"result discarded", `
def f() -> int:
    _ = sock.connect_tcp("127.0.0.1", 1)
    return 0
`, "is discarded"},
		{"result dropped as a statement", `
def f(ln: sock.TcpListener) -> int:
    ln.accept(timeout_ms=1)
    return 0
`, "resource handle leak"},
		{"match arm ignores the handle", `
def f() -> int:
    match sock.connect_tcp("127.0.0.1", 1):
        Ok(_) -> print("up")
        Err(e) -> print(e)
    return 0
`, "must bind"},
		{"wildcard arm swallows the handle", `
def f() -> int:
    match sock.connect_tcp("127.0.0.1", 1):
        _ -> print("?")
    return 0
`, "without binding it"},
		{"method on an unmatched result", `
def f() -> int:
    r = sock.connect_tcp("127.0.0.1", 1)
    r.close()
    return 0
`, "match on it before calling"},
		{"overwritten while open", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    match sock.connect_tcp("127.0.0.1", 2):
        Ok(c) ->
            conn = c
        Err(e) -> print(e)
    conn.close()
    return Ok(1)
`, "overwritten"},
		{"stored in an entity", `
entity Peer:
    conn: sock.TcpStream
`, "cannot hold"},
		{"stored in a nested entity field", `
entity Node:
    next: Option[Node]
    conns: list[sock.TcpStream]
`, "cannot hold"},
		{"list of handles as a parameter", `
def f(xs: list[sock.TcpStream]) -> int:
    return 0
`, "can only be passed or returned directly"},
		{"doubly wrapped return", `
def f() -> Result[Option[sock.TcpStream], str]:
    return Ok(None)
`, "can only be passed or returned directly"},
		{"own argument to a workflow", `
workflow W(conn: sock.TcpStream) -> int:
    start -> fin:
        n = 1
    step fin -> done:
        return 0

def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    n = run_workflow W(own conn)
    conn.close()
    return Ok(n)
`, "a workflow cannot take ownership"},
		{"formatted into a string", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    print(f"{conn}")
    conn.close()
    return Ok(1)
`, "cannot be stored"},
		{"borrowing call returned while still open", `
def f() -> Result[str, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    return peek(conn)
`, "resource handle leak"},
		{"moved in an elif condition", `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    if b:
        print("a")
    elif close_it(own conn) == 0:
        print("b")
    else:
        print("c")
    return Ok(1)
`, "every path must leave it in the same state"},
		{"closed in a loop condition", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    n: int[0..3] = 0
    while close_it(own conn) == n:
        decreases: 3 - n
        n += 1
    return Ok(1)
`, "after it was moved"},
		{"future reassigned before await", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    a = pool.submit(() => accept_one(ln))
    a = pool.submit(() => 1)
    _ = a.await()
    ln.close()
    return Ok(0)
`, "while a task may still be using"},
		{"awaited on one branch only", `
def f(pool: conc.ThreadPool, b: bool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    a = pool.submit(() => accept_one(ln))
    if b:
        _ = a.await()
    ln.close()
    return Ok(0)
`, "while a task may still be using"},
		{"pattern shadows an open handle", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    match sock.connect_tcp("127.0.0.1", 2):
        Ok(conn) -> conn.close()
        Err(e) -> print(e)
    conn.close()
    return Ok(1)
`, "overwritten"},
		{"fallible argument after an own argument", `
def consume(own conn: sock.TcpStream, n: int) -> int:
    conn.close()
    return n

def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    return Ok(consume(own conn, fallible()?))
`, "`?` may return early"},
		{"later argument closes a borrowed argument", `
def keep(conn: sock.TcpStream, n: int) -> int:
    return n

def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    return Ok(keep(conn, close_it(own conn)))
`, "after it was moved"},
		{"await inside an unused closure", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    a = pool.submit(() => accept_one(ln))
    wait = () => a.await()
    ln.close()
    _ = a.await()
    return Ok(0)
`, "while a task may still be using"},
		{"await inside another task", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    a = pool.submit(() => accept_one(ln))
    w = pool.submit(() => a.await())
    ln.close()
    _ = a.await()
    _ = w.await()
    return Ok(0)
`, "while a task may still be using"},
		{"shutdown inside a closure", `
def f() -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    pool = conc.ThreadPool(2, 4)
    a = pool.submit(() => accept_one(ln))
    stop = () => pool.shutdown()
    ln.close()
    pool.shutdown()
    return Ok(0)
`, "while a task may still be using"},
		{"match expression moves the handle in one arm", `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    n = match b:
        True -> close_it(own conn)
        False -> 0
    return Ok(n)
`, "every path must leave it in the same state"},
		{"port left open by a loop body", `
def f(xs: list[int]) -> int:
    for x in xs:
        AuditLog.open_log()
    return 0
`, "resource handle leak in inner block"},
		{"port left open by a match arm", `
def f(b: bool) -> int:
    match b:
        True -> AuditLog.open_log()
        False -> print("skip")
    return 0
`, "resource handle leak in inner block"},
		{"task may fail before taking the handle it captured", `
def consume(own conn: sock.TcpStream, n: int) -> int:
    conn.close()
    return n

def f(pool: conc.ThreadPool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    a = pool.submit(() => consume(own conn, fallible()?))
    _ = a.await()
    return Ok(0)
`, "may end it before"},
		{"stored in a list", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    xs = [conn]
    conn.close()
    return Ok(1)
`, "cannot be stored"},
		{"passed to a builtin", `
def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    print(conn)
    conn.close()
    return Ok(1)
`, "cannot be stored"},
		{"same handle passed twice", `
def two(a: sock.TcpStream, own b: sock.TcpStream) -> int:
    b.close()
    return 0

def f() -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    return Ok(two(conn, own conn))
`, "more than once"},
		{"stream shared with a task", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    a = pool.submit(() => peek(conn))
    _ = a.await()
    conn.close()
    return Ok(0)
`, "cannot be shared with a task"},
		{"stream used directly by a task", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    a = pool.submit(() => conn.recv_text(8))
    _ = a.await()
    conn.close()
    return Ok(0)
`, "cannot be shared with a task"},
		{"used after being moved into a task", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    a = pool.submit(() => close_it(own conn))
    r = conn.recv_text(8)
    _ = a.await()
    return Ok(0)
`, "after it was moved"},
		{"listener closed while a task uses it", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    a = pool.submit(() => accept_one(ln))
    ln.close()
    _ = a.await()
    return Ok(0)
`, "while a task may still be using"},
		{"closed listener given to a task", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    ln.close()
    a = pool.submit(() => accept_one(ln))
    _ = a.await()
    return Ok(0)
`, "use-after-close"},
		{"listener closed after tasks started in a loop", `
def f(pool: conc.ThreadPool, xs: list[int]) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    for x in xs:
        a = pool.submit(() => accept_one(ln))
        print(x)
    ln.close()
    return Ok(0)
`, "while a task may still be using"},
		{"borrowed listener escapes into a task", `
def f(ln: sock.TcpListener, pool: conc.ThreadPool) -> int:
    _ = pool.submit(() => accept_one(ln))
    return 0
`, "may still be used by a task"},
		{"task closes a captured handle", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    a = pool.submit(() => ln.close())
    _ = a.await()
    return Ok(0)
`, "a task closure cannot call"},
		{"task accepts without owning the connection", `
def f(pool: conc.ThreadPool) -> Result[int, str]:
    ln = sock.listen_tcp("127.0.0.1", 0)?
    a = pool.submit(() => ln.accept(timeout_ms=1))
    _ = a.await()
    ln.close()
    return Ok(0)
`, "resource handle leak"},
		{"captured by an ordinary closure", `
def f(xs: list[int]) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    ys = xs |> map(x => close_it(own conn))
    return Ok(0)
`, "cannot be captured by this closure"},
		{"closed in a short-circuit operand", `
def f(b: bool) -> Result[int, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    ok = b and close_it(own conn) == 0
    return Ok(0)
`, "conditionally evaluated"},
		{"returned after close", `
def f() -> Result[sock.TcpStream, str]:
    conn = sock.connect_tcp("127.0.0.1", 1)?
    conn.close()
    return Ok(conn)
`, "cannot return"},
		{"own parameter in a workflow", `
workflow W(own conn: sock.TcpStream) -> int:
    start -> fin:
        conn.close()
    step fin -> done:
        return 0
`, "sema: "},
		{"stream shared by concurrent branches", `
workflow W(conn: sock.TcpStream) -> int:
    start -> go:
        n = 1
    fork go:
        branch a:
            call conn.send_text("a")
        branch b:
            call conn.send_text("b")
    join joined
    step fin after joined -> done:
        return 0
`, "cannot be shared between threads"},
		{"workflow leaks a connection", `
workflow W() -> int:
    start -> fin:
        match sock.connect_tcp("127.0.0.1", 1):
            Ok(c) -> print("up")
            Err(e) -> print(e)
    step fin -> done:
        return 0
`, "resource handle leak"},
	}
	for _, c := range cases {
		got := ownershipErrors(t, c.src)
		if got == "" {
			t.Errorf("%s: expected an error, but the program was accepted", c.name)
		} else if !strings.Contains(got, c.want) {
			t.Errorf("%s: expected error containing %q, got:\n%s", c.name, c.want, got)
		}
	}
}
