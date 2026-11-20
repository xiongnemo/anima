package spark

import (
	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/smt"
)

// A byte view never changes: its length is that of the value it was made
// from, kept in listLens under its name like the length of a list.

// viewReads are the reads of a byte view, with the number of bytes each
// takes at its offset.
var viewReads = map[string]int64{"read_u8": 1, "read_u16_be": 2, "read_u32_be": 4}

func isByteView(t sema.Type) bool {
	ht, ok := t.(*sema.HandleType)
	return ok && ht.Name == "bytes.ByteView"
}

// viewLen is the length of the view e evaluates to: the one known for a
// variable or a field of one, an arbitrary one for anything else.
func (v *verifier) viewLen(e ast.Expr, env *symEnv) smt.LinearTerm {
	if path, ok := mutArgPath(e); ok && isByteView(v.info.ExprTypes[e]) {
		return env.lenOf(path)
	}
	return env.freshLen("bytes")
}

// isHexLit reports whether from_hex decodes s: both backends give an empty
// view for anything else.
func isHexLit(s string) bool {
	if len(s)%2 != 0 {
		return false
	}
	for i := 0; i < len(s); i++ {
		c := s[i]
		if !(c >= '0' && c <= '9' || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F') {
			return false
		}
	}
	return true
}

// newViewLen is the length of the view that rhs makes, when rhs says it:
// from_str and from_hex of a literal, from_str of a string whose length is
// known, a slice (proved inside its view where it is called), or another
// name for a view.
func (v *verifier) newViewLen(rhs ast.Expr, env *symEnv, scope string) (smt.LinearTerm, bool) {
	if !isByteView(v.info.ExprTypes[rhs]) {
		return smt.LinearTerm{}, false
	}
	if path, ok := mutArgPath(rhs); ok {
		return env.lenOf(path), true
	}
	call, ok := rhs.(*ast.CallExpr)
	if !ok {
		return smt.LinearTerm{}, false
	}
	fe, ok := call.Callee.(*ast.FieldExpr)
	if !ok {
		return smt.LinearTerm{}, false
	}
	if id, ok := fe.Object.(*ast.Ident); ok && v.info.Imports[id.Name] == "std.bytes" && len(call.Args) == 1 {
		arg := call.Args[0].Value
		switch fe.Field {
		case "from_hex":
			if sl, ok := arg.(*ast.StrLit); ok {
				if !isHexLit(sl.Value) {
					return smt.Const(0), true
				}
				return smt.Const(int64(len(sl.Value) / 2)), true
			}
		case "from_str":
			return v.lenOfValue(arg, env)
		}
		return smt.LinearTerm{}, false
	}
	if fe.Field == "slice" && len(call.Args) == 2 && isByteView(v.info.ExprTypes[fe.Object]) {
		lo := v.evalInt(call.Args[0].Value, env, scope, false)
		hi := v.evalInt(call.Args[1].Value, env, scope, false)
		return hi.Sub(lo), true
	}
	return smt.LinearTerm{}, false
}

// checkViewCall proves that a read or a slice of a byte view stays inside
// it. piped is the value the call is given by a pipeline, its first
// argument, or nil. A value sema has no type for (the parameter of a
// lambda) is read as a view of unknown length: nothing else has these
// methods.
func (v *verifier) checkViewCall(call *ast.CallExpr, piped ast.Expr, env *symEnv, scope string) {
	fe, ok := call.Callee.(*ast.FieldExpr)
	if !ok {
		return
	}
	width, isRead := viewReads[fe.Field]
	if !isRead && fe.Field != "slice" {
		return
	}
	switch t := v.info.ExprTypes[fe.Object].(type) {
	case nil, sema.UnknownType:
		if id, ok := fe.Object.(*ast.Ident); ok && v.info.Imports[id.Name] != "" {
			return
		}
	default:
		if !isByteView(t) {
			return
		}
	}
	var args []ast.Expr
	if piped != nil {
		args = append(args, piped)
	}
	for _, a := range call.Args {
		args = append(args, a.Value)
	}
	length := v.viewLen(fe.Object, env)
	var inside smt.BoolExpr
	switch {
	case isRead && len(args) == 1:
		off := v.evalInt(args[0], env, scope, true)
		inside = smt.And(smt.Ge(off, smt.Const(0)), smt.Le(off.Add(smt.Const(width)), length))
	case !isRead && len(args) == 2:
		lo := v.evalInt(args[0], env, scope, true)
		hi := v.evalInt(args[1], env, scope, true)
		inside = smt.And(smt.Ge(lo, smt.Const(0)), smt.Le(lo, hi), smt.Le(hi, length))
	default:
		return
	}
	v.prove(scope+".byteview_bounds", scope, call.Span, env, inside)
}
