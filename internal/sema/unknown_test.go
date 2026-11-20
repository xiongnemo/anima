package sema

import (
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
)

const unknownHead = `import std.concurrent as conc
import std.json as json
import std.requests as req

def work(x: int[0..100]) -> int[0..100]:
    return x

def nothing():
    print("n")

def inRange() -> Option[int[1..9]]:
    return Some(1)

def outOfRange() -> Option[int[0..0]]:
    return Some(0)

def some() -> Option:
    return Some([1])

def inv(q: Option[int[1..9]]) -> int:
    return 0

def drain(c: conc.Channel[int[1..9]]) -> int:
    return 0

def fill(c: conc.Channel[int]) -> int:
    return 0

def locked(m: conc.Mutex[int[1..9]]) -> int:
    return 0

def main() -> int:
    xs: list[int[0..9]] = [1, 2, 3]
    ch = conc.Channel(cap=1)
    sent = ch.send([1])
`

func checkUnknownCases(t *testing.T, cases []struct{ name, body, want string }) {
	t.Helper()
	for _, c := range cases {
		prog, err := parser.Parse("unk.anm", unknownHead+c.body+"\n    return 0\n")
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

// A value sema cannot tell the type of is bound, passed on, printed and
// matched. Anything else reads it as a type it may not have: both backends
// run the operation on whatever the value is.
func TestSemaUnknownValueIsOnlyPassedOn(t *testing.T) {
	const recv = `    match ch.recv():
        None -> print("none")
        Some(v) ->
`
	const unknown = "a value of unknown type"
	checkUnknownCases(t, []struct{ name, body, want string }{
		{"printed, formatted and wrapped", recv + `            print(v, f"got {v}")
            o = Some(v)
            ys = [v]
            w = v
            print(o, ys, w)`, ""},
		{"compared", recv + `            if v != 0:
                print(1)`, "!= on " + unknown},
		{"a condition", recv + `            if v:
                print(1)`, "if condition must be bool, got unknown"},
		{"negated", recv + `            print(not v)`, "not needs a bool, got unknown"},
		{"arithmetic", recv + `            print(v + 1)`, "arithmetic + requires int, got unknown"},
		{"a divisor", recv + `            print(10 / v)`, "requires int"},
		{"indexed", recv + `            print(v[0])`, "an index into " + unknown},
		{"a member", recv + `            print(v.nope)`, `member "nope" of ` + unknown},
		{"a method", recv + `            print(v.nope())`, `member "nope" of ` + unknown},
		{"called", recv + `            print(v(1))`, unknown},
		{"looped over", recv + `            for x in v:
                print(x)`, unknown},
		{"measured", recv + `            print(len(v))`, "len() takes a list, a map or a string, got unknown"},
		{"given to a function", recv + `            print(work(v))`, "arg 1 of work expects int[0..100], got unknown"},
		{"declared as a type", recv + `            n: int = v
            print(n)`, "cannot assign unknown to n (int)"},
		{"inside a variant declared as a type", recv + `            o = Some(v)
            t: Option[int] = o
            print(t)`, "cannot assign Option[unknown] to t (Option[int])"},
		{"inside a list declared as a type", recv + `            ys = [v]
            zs: list[int[1..9]] = ys
            print(zs)`, "cannot assign list[unknown] to zs"},
		{"an arm of a match on it", recv + `            d = match v:
                0 -> 1
                n -> 10 / n
            print(d)`, "requires int"},
		{"a variable that held one", recv + `            x = v
            x = 5
            print(10 / x)`, "x holds a value of unknown type and cannot be given a int"},
		{"given to a variable that has a type", recv + `            n = 5
            n = v
            print(n)`, "n is a int and cannot be given a value of unknown type"},
		{"bound by a pattern to a variable that has a type", `    x = 5
    match ch.recv():
        Some(x) -> print(x)
        None -> print("none")
    if x != 0:
        print(10 / x)`, "x is a int and cannot be given a value of unknown type"},
		{"bound by a loop to a variable that has a type", `    x = 5
` + recv + `            ys = [v]
            for x in ys:
                print(x)
    if x != 0:
        print(10 / x)`, "x is a int and cannot be given a value of unknown type"},
		{"piped into a stage that takes a list", recv + `            d = v |> map((q) => 1)
            print(d)`, "the stage map on " + unknown},
		{"piped into take", recv + `            print(v |> take(1))`, "the stage take on " + unknown},
		{"piped into a stage that takes a variant", recv + `            print(v |> unwrap_or(1))`, "the stage unwrap_or on " + unknown},
		{"put into a mutex of ints", recv + `            m = conc.Mutex(5)
            m.set(v)`, "argument 1 of set() of a conc.Mutex is int, got unknown"},
		{"written into a list of ints", recv + `            ns = [1, 2]
            ns[0] = v`, "list element expects int, got unknown"},
		{"what json.decode gives without a type", `    match json.decode("5"):
        Ok(v) -> print(v + 1)
        Err(e) -> print(e)`, "arithmetic + requires int, got unknown"},
		{"the parameter of a lambda that is not named", `    fs = [(v) => v + 1]
    print(fs)`, "arithmetic + requires int, got unknown"},
		// What an Option written without its type holds is of unknown type.
		{"held by a bare Option, declared as a type", `    match some():
        Some(n) ->
            k: int = n
            print(k)
        None -> print("none")`, "cannot assign unknown to k (int)"},
		{"held by a bare Option, bound to a variable that has a type", `    x = 5
    match some():
        Some(x) -> print(x)
        None -> print("none")`, "x is a int and cannot be given a value of unknown type"},
		{"a bare Option given as an Option of ints", `    print(inv(some()))`, "arg 1 of inv expects Option[int[1..9]], got Option[unknown]"},
		{"a bare Option passed on and printed", `    o = some()
    print(o)`, ""},
		// What a function with no return type gives is not of a type either.
		{"a variable of no type given an int on one path", `    x = nothing()
    if sent:
        x = 5
    print(10 / x)`, "x holds what a function with no return type gives and cannot be given a int"},
		{"a variable that has a type given no type", `    x = 5
    x = nothing()`, "x is a int and cannot be given what a function with no return type gives"},
		{"a loop variable that has a type given no type", `    x = 5
    for x in [nothing()]:
        print(x)`, "x is a int and cannot be given what a function with no return type gives"},
		{"an arm of a match expression of no type", `    o: Option[int] = None
    d = match o:
        Some(n) -> 5
        None -> nothing()
    print(10 / d)`, "arithmetic / requires int"},
		// A handle is a reference: it is passed as a handle of what it holds.
		{"a channel of anything given as a channel of ints", `    print(drain(ch))`, "arg 1 of drain expects conc.Channel[int[1..9]], got conc.Channel[unknown]"},
		{"a channel of a range given as a channel of ints", `    c = conc.Channel[int[1..9]](cap=1)
    print(fill(c))`, "arg 1 of fill expects conc.Channel[int], got conc.Channel[int[1..9]]"},
		{"a mutex of ints given as a mutex of a range", `    m = conc.Mutex(5)
    print(locked(m))`, "arg 1 of locked expects conc.Mutex[int[1..9]], got conc.Mutex[int]"},
		{"a channel given as what it is", `    c = conc.Channel[int[1..9]](cap=1)
    d = conc.Channel[int](cap=1)
    print(drain(c), fill(d))`, ""},
		// A variable keeps the type of what its handle holds, whichever path
		// gave it the handle.
		{"a future of an int given one of a str on one path", `    pool = conc.ThreadPool(1, 2)
    f = pool.submit(() => 5)
    if sent:
        f = pool.submit(() => "s")
    print(f.await())
    pool.shutdown()`, "f is a Future[int] and cannot be given a Future[str]: a variable keeps the type of what its handle holds"},
		{"a future given one of the same type", `    pool = conc.ThreadPool(1, 2)
    f = pool.submit(() => 5)
    if sent:
        f = pool.submit(() => 6)
    print(f.await() + 1)
    pool.shutdown()`, ""},
		{"a channel of anything given one of ints", `    c = conc.Channel(cap=1)
    c = conc.Channel[int](cap=1)
    print(c.recv())`, "c is a conc.Channel[unknown] and cannot be given a conc.Channel[int]"},
		// Futures gathered into one list give one type, ranges included.
		{"futures of two ranges gathered", `    pool = conc.ThreadPool(2, 2)
    f1 = pool.submit(() => inRange())
    f2 = pool.submit(() => outOfRange())
    rs = req.gather([f1, f2])
    pool.shutdown()
    for r in rs:
        match r:
            Some(n) -> print(10 / n)
            None -> print("none")`, "arithmetic / requires int, got int[10..10] and unknown"},
		{"futures of one range gathered", `    pool = conc.ThreadPool(2, 2)
    f1 = pool.submit(() => inRange())
    f2 = pool.submit(() => inRange())
    rs = req.gather([f1, f2])
    pool.shutdown()
    for r in rs:
        match r:
            Some(n) -> print(10 / n)
            None -> print("none")`, ""},
		// What has no value yet takes the type of what it is given.
		{"an empty list, None and Ok", `    ys: list[int] = []
    o: Option[int] = None
    r: Result[int, str] = Ok(1)
    zs = []
    zs = [1]
    print(ys, o, r, zs[0])`, ""},
	})
}

// A lambda with parameters that is given a name takes the types of its
// first use, and is used by its name only.
func TestSemaNamedLambdaTakesTheTypesOfItsFirstUse(t *testing.T) {
	const same = "a lambda takes the same types at every use"
	const byName = "is a lambda with parameters and is used by its name only"
	checkUnknownCases(t, []struct{ name, body, want string }{
		{"called, piped and given to stages", `    g = (v) => v > 1
    k = (v) => [v]
    h = (w) => g(w)
    print(g(2), h(0), xs |> filter(g), xs |> any(g), xs |> find(g), 5 |> g(), k(7))`, ""},
		{"its parameter is piped in its body", `    a = (v) => (v |> map((q) => q > 1))
    b = (o) => (o |> unwrap_or(1))
    e = (v) => (v |> filter((q) => q > 1) |> any((q) => q > 5))
    k = (o) => (o |> and_then((q) => Some(q > 1)))
    o: Option[int[0..9]] = Some(2)
    print(a(xs), b(o), len(xs), e(xs), k(o))`, ""},
		{"first used in a loop", `    g = (v) => v > 1
    i = 0
    while i < 2:
        print(g(i))
        i += 1`, ""},
		{"what it gives has a type", `    g = (v) => v
    y = g(xs)
    print(y.nope())`, `a value of type list[int[0..9]] has no member "nope"`},
		{"its body is checked with what it is given", `    g = (v) => v.nope()
    print(g(3))`, "nope"},
		{"an int and then a str", `    g = (v) => v
    print(g(1))
    print(g("s"))`, "g takes int where it is first used, got str: " + same},
		{"a list and then an int, as a stage", `    g = (v) => v
    print(g(xs))
    print(xs |> map(g))`, same},
		{"too many arguments", `    g = (v) => v
    print(g(1, 2))`, "takes 1 argument, got 2"},
		// The types of the first use are those of every later one, so it
		// has to say them whole: None would let Some(0) in afterwards.
		{"first used with None", `    g = (v) => v
    a = g(None)
    o: Option[int[1..9]] = g(Some(0))
    print(a, o)`, "g is first used with Option, which does not say the type of all it holds"},
		{"first used with an empty list", `    g = (v) => v
    a = g([])
    print(a)`, "g is first used with list[unknown], which does not say the type of all it holds"},
		{"None after a whole type", `    g = (v) => v
    o: Option[int[1..9]] = Some(1)
    print(g(o), g(None))`, ""},
		{"an Option of a range and then one of any int", `    g = (v) => v
    o: Option[int[1..9]] = Some(1)
    print(g(o))
    p: Option[int[1..9]] = g(Some(0))
    print(p)`, "g takes Option[int[1..9]] where it is first used, got Option[int]: " + same},
		// A lambda keeps the handle its variable had where it was written.
		{"the mutex it names is one of another type by its first use", `    m = conc.Mutex(5)
    g = (v) => m.get()
    m = conc.Mutex("s")
    print(g(1) + "t")`, "m is a conc.Mutex[int] and cannot be given a conc.Mutex[str]: a variable keeps the type of what its handle holds"},
		{"given another name", `    g = (v) => v
    h = g
    print(1)`, "g " + byName},
		{"stored", `    g = (v) => v
    fs = [g]
    print(1)`, "g " + byName},
		{"printed", `    g = (v) => v
    print(g)`, "g " + byName},
		{"assigned again", `    g = (v) => v
    g = (v) => [v]
    print(1)`, "g names a lambda and is not assigned again"},
		{"given the name of a variable", `    g = 5
    g = (v) => v
    print(1)`, "a lambda with parameters is given a name of its own"},
		// A function a standard call is given is called with what the call
		// has for it.
		{"the function of with_lock", `    m = conc.Mutex(5)
    m.with_lock((v) => v + 1)
    print(m.get() + 1)`, ""},
		{"the function of parallel_map", `    rs = conc.parallel_map(xs, (x) => work(x))
    ps = xs |> conc.parallel_map((x) => x > 0)
    if len(rs) > 0 and len(ps) > 0:
        print(rs[0] + 1, not ps[0])`, ""},
		{"the future of a task", `    pool = conc.ThreadPool(1, 2)
    f = pool.submit(() => work(4))
    p = (() => 4) |> pool.submit()
    r = f.await() + p.await()
    pool.shutdown()
    print(r)`, ""},
		{"the future of a task that gives a str", `    pool = conc.ThreadPool(1, 2)
    f = pool.submit(() => "s")
    r = f.await()
    pool.shutdown()
    print(10 / r)`, "arithmetic / requires int"},
	})
}
