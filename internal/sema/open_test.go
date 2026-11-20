package sema

import "testing"

// `None`, `[]`, `{}` and `Ok(1)` leave a part of their type open: no value
// has typed it. An open part is any type where it is read, so a variable
// that has one is not given a value that types it, and nothing that can be
// written to is held by a variable with an open part inside.
func TestSemaOpenTypePartsStayOpen(t *testing.T) {
	const assigned = "declare the type of o where it is first assigned"
	const written = "which can be written to and does not say the type of all it holds: declare the type of"
	checkUnknownCases(t, []struct{ name, body, want string }{
		// A variable with an open part keeps it.
		{"None then Some in a branch", `    o = None
    if sent:
        o = Some(0)
    p: Option[int[1..9]] = o
    print(p)`, assigned},
		{"None read before it is typed in a loop", `    o = None
    for i in [1, 2]:
        p: Option[int[1..9]] = o
        print(p)
        o = Some(0)`, assigned},
		{"an empty list typed in a loop", `    ys = []
    for i in [1, 2]:
        zs: list[str] = ys
        print(zs)
        ys = [1]`, "declare the type of ys where it is first assigned"},
		{"None as a loop variable", `    o = None
    for o in [Some(0)]:
        print(o)
    p: Option[int[1..9]] = o
    print(p)`, assigned},
		{"None as a name in a pattern", `    o = None
    match Some(Some(0)):
        Some(o) -> print(o)
        None -> print("x")
    p: Option[int[1..9]] = o
    print(p)`, assigned},
		{"None declared again", `    o = None
    o: Option[int] = Some(0)
    print(o)`, assigned},
		{"Ok then Err", `    r = Ok(1)
    r = Err("s")
    print(r)`, "declare the type of r where it is first assigned"},
		{"a future of None then of Some", `    pool = conc.ThreadPool(1, 2)
    f = pool.submit(() => None)
    for i in [1, 2]:
        p: Option[int[1..9]] = f.await()
        print(p)
        f = pool.submit(() => Some(0))
    pool.shutdown()`, "declare the type of f where it is first assigned"},
		// What is written to says the type of all it holds.
		{"a list of None", `    os = [None]
    os[0] = Some(0)
    print(os)`, written},
		{"a list of empty lists", `    ls = [[]]
    print(ls)`, written},
		{"a map of None", `    d = {"a": None}
    d["a"] = Some(0)
    print(d)`, written},
		{"an empty map", `    d = {}
    d["a"] = 1
    print(d)`, written},
		{"a mutex of None", `    m = conc.Mutex(None)
    m.set(Some(0))
    print(m.get())`, written},
		{"a mutex of an empty list", `    m = conc.Mutex([])
    print(m.get())`, written},
		{"two Oks gathered into a list", `    pool = conc.ThreadPool(2, 2)
    f1 = pool.submit(() => Ok(1))
    f2 = pool.submit(() => Ok(2))
    rs = req.gather([f1, f2])
    pool.shutdown()
    print(rs)`, written},
		{"a list of None as a loop variable", `    for os in [[None]]:
        print(os)`, written},
		{"a list of None as a name in a pattern", `    match Some([None]):
        Some(os) -> print(os)
        None -> print("x")`, written},
		// With a declared type all of them are what they were.
		{"declared", `    o: Option[int] = None
    o = Some(6)
    ys: list[int] = []
    ys = [1]
    os: list[Option[int]] = [None]
    os[0] = Some(4)
    d: map[str, int] = {}
    d["a"] = 5
    m: conc.Mutex[Option[int]] = conc.Mutex(None)
    m.set(Some(3))
    r: Result[int, str] = Ok(1)
    r = Err("s")
    pool = conc.ThreadPool(2, 2)
    f: conc.Future[Option[int]] = pool.submit(() => None)
    f = pool.submit(() => Some(0))
    f1 = pool.submit(() => Ok(1))
    f2 = pool.submit(() => Ok(2))
    rs: list[Result[int, str]] = req.gather([f1, f2])
    pool.shutdown()
    print(o, ys, os, d, m.get(), r, f.await(), rs)`, ""},
		// An open part that stays open is no harm: nothing is in it.
		{"None and an empty list kept as they are", `    o = None
    o = None
    ys = []
    ys = []
    p: Option[int[1..9]] = o
    zs: list[str] = ys
    w = Some([])
    print(o, ys, p, zs, w)`, ""},
	})
}
