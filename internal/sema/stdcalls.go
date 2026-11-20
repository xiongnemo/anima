package sema

import (
	"fmt"

	"github.com/xiongnemo/anima/internal/ast"
)

// Both backends take the arguments of a standard function or handle method
// by position, in the order they are written, and read them without looking
// at how many there are or what they are: a missing one stops the VM with a
// Go panic and the native build with it, and one of another kind is read as
// an empty string or as 0. So the call is checked here against what the
// function takes.

// stdArg is what a parameter of a standard function takes.
type stdArg int

const (
	argAny  stdArg = iota
	argInt         // an int
	argStr         // a str
	argList        // a list
	argFn0         // a function of no argument
	argFn1         // a function of one argument
	argElem        // what the handle keeps: the T of a Channel[T] or of a Mutex
)

type stdParam struct {
	name string
	kind stdArg
	opt  bool // may be left out; only at the end
}

// stdSig is what a standard function takes. One with timeout also takes
// `timeout_ms`, by keyword after the others or by position in their place.
type stdSig struct {
	params  []stdParam
	timeout bool
}

func sig(params ...stdParam) stdSig { return stdSig{params: params} }

func (s stdSig) withTimeout() stdSig { s.timeout = true; return s }

func intP(name string) stdParam    { return stdParam{name: name, kind: argInt} }
func strP(name string) stdParam    { return stdParam{name: name, kind: argStr} }
func anyP(name string) stdParam    { return stdParam{name: name, kind: argAny} }
func (p stdParam) maybe() stdParam { p.opt = true; return p }

// stdSigs is keyed by `std.module.function` and by `handle.method`.
var stdSigs = map[string]stdSig{
	"std.socket.listen_tcp":  sig(strP("host"), intP("port")),
	"std.socket.connect_tcp": sig(strP("host"), intP("port")),

	"std.requests.get":     sig(strP("url")).withTimeout(),
	"std.requests.post":    sig(strP("url"), strP("body")).withTimeout(),
	"std.requests.Session": sig(intP("pool_size").maybe()),
	"std.requests.gather":  sig(stdParam{name: "futures", kind: argList}),

	"std.concurrent.ThreadPool":   sig(intP("workers"), intP("queue_cap")),
	"std.concurrent.Channel":      sig(intP("cap").maybe()),
	"std.concurrent.Mutex":        sig(anyP("value")),
	"std.concurrent.Semaphore":    sig(intP("permits")),
	"std.concurrent.parallel_map": sig(stdParam{name: "xs", kind: argList}, stdParam{name: "f", kind: argFn1}),

	"std.json.encode": sig(anyP("value")),
	"std.json.decode": sig(strP("text")),

	"std.bytes.from_str": sig(strP("text")),
	"std.bytes.from_hex": sig(strP("hex")),

	"std.crypto.sha256":           sig(strP("text")),
	"std.crypto.hmac_sha256":      sig(strP("key"), strP("text")),
	"std.crypto.constant_time_eq": sig(strP("a"), strP("b")),

	"std.fs.open":         sig(strP("path"), strP("mode").maybe()),
	"std.fs.read_text":    sig(strP("path")),
	"std.fs.write_atomic": sig(strP("path"), strP("text")),

	"std.cli.args":    sig(),
	"std.cli.env_get": sig(strP("name")),

	"std.time.now_ms":   sig(),
	"std.time.sleep_ms": sig(intP("ms")),

	"sock.TcpListener.port":   sig(),
	"sock.TcpListener.accept": sig().withTimeout(),
	"sock.TcpListener.close":  sig(),

	"sock.TcpStream.send_text": sig(strP("text")),
	"sock.TcpStream.recv_text": sig(intP("max_bytes").maybe()),
	"sock.TcpStream.close":     sig(),

	"fs.File.read_text":  sig(),
	"fs.File.write_text": sig(strP("text")),
	"fs.File.close":      sig(),

	"req.Session.get":       sig(strP("url")).withTimeout(),
	"req.Session.post":      sig(strP("url"), strP("body")).withTimeout(),
	"req.Session.get_async": sig(strP("url")).withTimeout(),
	"req.Session.close":     sig(),

	"Future.await": sig(),

	"conc.ThreadPool.submit":   sig(stdParam{name: "task", kind: argFn0}),
	"conc.ThreadPool.shutdown": sig(),

	"conc.Channel.send":  sig(stdParam{name: "value", kind: argElem}),
	"conc.Channel.recv":  sig(),
	"conc.Channel.close": sig(),

	"conc.Mutex.get":       sig(),
	"conc.Mutex.set":       sig(stdParam{name: "value", kind: argElem}),
	"conc.Mutex.with_lock": sig(stdParam{name: "f", kind: argFn1}),

	"conc.Semaphore.acquire": sig(),
	"conc.Semaphore.release": sig(),

	"bytes.ByteView.len":         sig(),
	"bytes.ByteView.read_u8":     sig(intP("offset")),
	"bytes.ByteView.read_u16_be": sig(intP("offset")),
	"bytes.ByteView.read_u32_be": sig(intP("offset")),
	"bytes.ByteView.slice":       sig(intP("lo"), intP("hi")),
}

// gatherType is what req.gather(futures) gives: the results of the futures,
// in order. They are known when the futures are written out and all give
// the same type.
func (c *checker) gatherType(e *ast.CallExpr) (Type, error) {
	var elem Type = UnknownType{}
	if lit, ok := c.stdArgs(e)[0].Value.(*ast.ListLit); ok {
		for i, x := range lit.Elems {
			ht, ok := c.info.ExprTypes[x].(*HandleType)
			if !ok || ht.Name != "Future" {
				if t := c.info.ExprTypes[x]; t != nil && t.Kind() != KindUnknown {
					return nil, fmt.Errorf("%s: gather takes futures, got %s", x.GetSpan(), t)
				}
				ht = &HandleType{Name: "Future", Elem: UnknownType{}}
			}
			switch {
			case i == 0:
				elem = ht.Elem
			case !knownType(elem) || !knownType(ht.Elem) || !elem.Equals(ht.Elem) || !ht.Elem.Equals(elem):
				elem = UnknownType{}
			}
		}
	}
	if elem == nil {
		elem = UnknownType{}
	}
	return &ListType{Elem: elem}, nil
}

// stdArgs are the arguments a standard call is given: those written, after
// the piped value when the call is a pipeline stage (`x |> o.f(a)` is
// o.f(x, a)).
func (c *checker) stdArgs(e *ast.CallExpr) []ast.CallArg {
	x := c.piped[e]
	if x == nil {
		return e.Args
	}
	return append([]ast.CallArg{{Value: x, Span: x.GetSpan()}}, e.Args...)
}

// checkStdCall checks the arguments of a call to a standard function or to a
// method of a standard handle. The arguments have been type-checked.
func (c *checker) checkStdCall(e *ast.CallExpr, fe *ast.FieldExpr) error {
	var key, what string
	var elem Type
	switch t := c.info.ExprTypes[fe.Object].(type) {
	case *ModuleType:
		key = t.Path + "." + fe.Field
		what = key
	case *HandleType:
		key = t.Name + "." + fe.Field
		what = fe.Field + "() of a " + t.Name
		elem = t.Elem
	default:
		return nil
	}
	s, ok := stdSigs[key]
	if !ok {
		return nil
	}
	args := c.stdArgs(e)
	named := false // timeout_ms is given by keyword
	for _, a := range args {
		named = named || (s.timeout && a.Name == "timeout_ms")
	}
	given := 0
	for i, a := range args {
		at := c.info.ExprTypes[a.Value]
		if a.Mut || a.Own {
			return fmt.Errorf("%s: %s takes its arguments as they are: no `mut` or `own`", a.Span, what)
		}
		if a.Name == "timeout_ms" && s.timeout {
			if i != len(args)-1 {
				return fmt.Errorf("%s: timeout_ms is the last argument of %s", a.Span, what)
			}
			continue
		}
		if i >= len(s.params) {
			if s.timeout && !named && i == len(s.params) && a.Name == "" {
				// The timeout, by position.
				continue
			}
			return fmt.Errorf("%s: %s takes %s, got %d", e.Span, what, s.takes(), len(args))
		}
		p := s.params[i]
		if a.Name != "" && a.Name != p.name {
			return fmt.Errorf("%s: argument %d of %s is %q: arguments are taken in order, so it cannot be given as %q here", a.Span, i+1, what, p.name, a.Name)
		}
		given++
		if err := c.checkStdArg(a, at, p, what, i+1, elem); err != nil {
			return err
		}
	}
	for _, p := range s.params[given:] {
		if !p.opt {
			return fmt.Errorf("%s: %s takes %s, got %d", e.Span, what, s.takes(), len(args))
		}
	}
	// What the function of with_lock gives is what the mutex then holds.
	if key == "conc.Mutex.with_lock" && len(args) == 1 {
		if ft, ok := c.info.ExprTypes[args[0].Value].(*FuncType); ok && knownType(elem) {
			if !c.kept(elem, ft.Return, nil) {
				return fmt.Errorf("%s: the function of with_lock gives what the mutex holds, %s, got %s", args[0].Value.GetSpan(), elem, ft.Return)
			}
		}
	}
	return nil
}

func (c *checker) checkStdArg(a ast.CallArg, at Type, p stdParam, what string, n int, elem Type) error {
	bad := func(want string) error {
		return fmt.Errorf("%s: argument %d of %s is %s, got %s", a.Value.GetSpan(), n, what, want, at)
	}
	if at == nil {
		return nil
	}
	unknown := generic(at)
	switch p.kind {
	case argInt:
		if at.Kind() != KindInt && !unknown {
			return bad("an int")
		}
	case argStr:
		if at.Kind() != KindStr && !unknown {
			return bad("a str")
		}
	case argList:
		if at.Kind() != KindList && !unknown {
			return bad("a list")
		}
	case argFn0, argFn1:
		arity := 0
		if p.kind == argFn1 {
			arity = 1
		}
		ft, ok := at.(*FuncType)
		if (!ok && !unknown) || (ok && len(ft.Params) != arity) {
			return bad("a function of " + plural(arity, "argument"))
		}
	case argElem:
		if knownType(elem) && !c.kept(elem, at, a.Value) {
			return bad(elem.String())
		}
	}
	return nil
}

// kept reports whether a value of type actual can be handed to a handle that
// keeps values of type expected and gives them back as such. The kernel does
// not follow a value through a channel or a mutex, so a range is checked
// here, on the types: a variable or a literal has the range of its type.
func (c *checker) kept(expected, actual Type, expr ast.Expr) bool {
	if want, ok := expected.(*IntType); ok && want.IsBounded {
		got, ok := actual.(*IntType)
		return ok && got.IsBounded && want.Lo <= got.Lo && got.Hi <= want.Hi
	}
	if expected.Kind() != actual.Kind() && actual.Kind() != KindUnknown {
		return false
	}
	return c.assignable(expected, actual, expr)
}

// takes describes the number of arguments of s.
func (s stdSig) takes() string {
	min := 0
	for _, p := range s.params {
		if !p.opt {
			min++
		}
	}
	out := plural(len(s.params), "argument")
	if min != len(s.params) {
		out = fmt.Sprintf("%d to %s", min, out)
	}
	if s.timeout {
		out += " and timeout_ms"
	}
	return out
}
