package spark

import (
	"fmt"
	"reflect"
	"strconv"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/smt"
)

// The range of the elements of a list, or of the values of a map, is part of
// its type, and it is the same under every name the list has (sema). So it
// holds as long as it is proved where an element is made: in a literal and
// in an assignment to an element.
//
// symEnv.listElems is narrower knowledge about what a list holds right now,
// such as the smallest range around the elements of a literal. A list is a
// reference, so it lasts until an element of any list is written.

// elemRange is the declared range of the ints directly in a list or map of
// type t.
func elemRange(t sema.Type) *sema.IntType {
	var elem sema.Type
	switch x := t.(type) {
	case *sema.ListType:
		elem = x.Elem
	case *sema.MapType:
		elem = x.Val
	}
	if it, ok := elem.(*sema.IntType); ok && it.IsBounded {
		return it
	}
	return nil
}

// proveLiteralElems proves the elements of a list or map literal in the
// range of the type it was given to.
func (v *verifier) proveLiteralElems(lit ast.Expr, env *symEnv, scope string) {
	it := elemRange(v.info.LiteralTargets[lit])
	if it == nil {
		return
	}
	switch x := lit.(type) {
	case *ast.ListLit:
		for _, el := range x.Elems {
			v.checkIntRange(v.evalInt(el, env, scope, false), el, env, it, scope+".list_elem_bounds", scope, el.GetSpan())
		}
	case *ast.MapLit:
		for _, en := range x.Entries {
			v.checkIntRange(v.evalInt(en.Value, env, scope, false), en.Value, env, it, scope+".map_value_bounds", scope, en.Value.GetSpan())
		}
	}
}

// proveElemAssign proves the value written to an element of list in the
// element range of the list's type.
func (v *verifier) proveElemAssign(list, value ast.Expr, env *symEnv, scope string, span ast.Span) {
	if it := elemRange(v.info.ExprTypes[list]); it != nil {
		v.checkIntRange(v.evalInt(value, env, scope, false), value, env, it, scope+".elem_assign_bounds", scope, span)
	}
}

// forgetElemHulls is called when an element of some list may have been
// written: by an assignment, or by a callee given a mut argument.
func (e *symEnv) forgetElemHulls() {
	for k := range e.listElems {
		delete(e.listElems, k)
	}
}

// writesElems reports whether a statement under node assigns to an element.
func writesElems(node any) bool {
	found := false
	visitNodes(reflect.ValueOf(node), func(n any) {
		switch x := n.(type) {
		case *ast.IndexAssignStmt:
			found = true
		case *ast.CompoundAssignStmt:
			if _, ok := x.Target.(*ast.IndexExpr); ok {
				found = true
			}
		}
	})
	return found
}

// elemHull is what is known about the int read by ix beyond its type.
func (v *verifier) elemHull(ix *ast.IndexExpr, env *symEnv) (smt.Interval, bool) {
	id, ok := ix.List.(*ast.Ident)
	if !ok {
		return smt.Interval{}, false
	}
	if _, ok := v.info.ExprTypes[id].(*sema.ListType); !ok {
		return smt.Interval{}, false
	}
	iv, ok := env.listElems[id.Name]
	return iv, ok && iv.HasLo && iv.HasHi
}

// proveIndex proves idx inside the list or string that indexed evaluates
// to: out of it a read gives None, whatever the element type says, and a
// write is dropped. The length is known of a literal and of what a
// variable or a field of one holds; any other list or string has to be
// given a name first. A map is keyed, and takes any key.
func (v *verifier) proveIndex(indexed, key ast.Expr, idx smt.LinearTerm, write bool, env *symEnv, scope string, span ast.Span) {
	name := scope + ".index_bounds"
	path, named := mutArgPath(indexed)
	var length smt.LinearTerm
	switch v.info.ExprTypes[indexed].(type) {
	case *sema.ListType, sema.StrType:
		lt, known := v.lenOfValue(indexed, env)
		if !known {
			if smt.CheckSat(smt.And(smt.Int64Pins(), env.pathCond())).Status == smt.StatusUnsat {
				v.record(name, scope, span, "index < len", VCProved, "unreachable", nil)
				return
			}
			v.record(name, scope, span, "index < len", VCFailed,
				"the length of what is indexed is not known here: give it a name first, as in `row = rows[i]`", nil)
			return
		}
		length = lt
	case *sema.MapType:
		// A write makes the key; a read of a key that is not there gives
		// None, whatever the value type says.
		if !write {
			v.prove(scope+".key_present", scope, span, env, v.memberOf(indexed, key, env))
		}
		return
	default:
		// A value sema has no type for is checked when its length is known.
		lt, known := env.listLens[path]
		if !named || !known || env.mapLens[path] {
			return
		}
		length = lt
	}
	v.prove(name, scope, span, env, smt.And(smt.Ge(idx, smt.Const(0)), smt.Lt(idx, length)))
}

// lenOfValue is the length of the list or string e evaluates to, when e is
// a literal, a variable or a field of one.
func (v *verifier) lenOfValue(e ast.Expr, env *symEnv) (smt.LinearTerm, bool) {
	switch v.info.ExprTypes[e].(type) {
	case *sema.ListType, sema.StrType:
	default:
		return smt.LinearTerm{}, false
	}
	switch x := e.(type) {
	case *ast.ListLit:
		return smt.Const(int64(len(x.Elems))), true
	case *ast.StrLit:
		return smt.Const(int64(len(x.Value))), true
	}
	if path, ok := mutArgPath(e); ok {
		return env.lenOf(path), true
	}
	return smt.LinearTerm{}, false
}

// inMark is in the name of a bool that says whether a key is in a map:
// <map path>.in:<key>. Under the path of its map, it is forgotten with it.
const inMark = ".in:"

// keyFact names the bool for key in the map that indexed evaluates to. A
// key is known by its value: a literal, the integer it is, or the string
// variable that holds it, until that variable is assigned.
func (v *verifier) keyFact(indexed, key ast.Expr, env *symEnv) (string, bool) {
	path, named := mutArgPath(indexed)
	if _, isMap := v.info.ExprTypes[indexed].(*sema.MapType); !isMap || !named {
		return "", false
	}
	switch k := key.(type) {
	case *ast.StrLit:
		return path + inMark + strconv.Quote(k.Value), true
	case *ast.Ident:
		if _, isStr := v.info.ExprTypes[key].(sema.StrType); isStr {
			return path + inMark + "$" + k.Name, true
		}
	}
	if _, isInt := v.info.ExprTypes[key].(*sema.IntType); isInt {
		if t := v.tryEvalInt(key, env); t != nil {
			return path + inMark + fmt.Sprint(*t), true
		}
	}
	return "", false
}

// memberOf is whether key is in the map that indexed evaluates to.
func (v *verifier) memberOf(indexed, key ast.Expr, env *symEnv) smt.BoolExpr {
	fact, ok := v.keyFact(indexed, key, env)
	if !ok {
		return smt.BoolVar{Name: env.freshVar("in")}
	}
	if b, known := env.boolTerms[fact]; known {
		return b
	}
	b := smt.BoolVar{Name: env.freshVar("in")}
	env.boolTerms[fact] = b
	return b
}

// keyWritten records that key is in the map after `m[key] = v`.
func (v *verifier) keyWritten(indexed, key ast.Expr, env *symEnv) {
	if fact, ok := v.keyFact(indexed, key, env); ok {
		env.boolTerms[fact] = smt.BoolConst{Val: true}
	}
}

// forgetKeysOf forgets which keys were looked up by the string variable name.
func (e *symEnv) forgetKeysOf(name string) {
	for _, k := range sortedKeys(e.boolTerms) {
		if strings.HasSuffix(k, inMark+"$"+name) {
			delete(e.boolTerms, k)
		}
	}
}

// literalKey is how keyFact writes a key that is a literal.
func (v *verifier) literalKey(key ast.Expr) string {
	switch k := key.(type) {
	case *ast.StrLit:
		return strconv.Quote(k.Value)
	case *ast.IntLit:
		return fmt.Sprint(smt.Const(k.Value))
	}
	return ""
}

// keyBinds gives the map a callee names param the keys the caller knows of
// the map it passes, held under arg. A key looked up by a string variable
// is known to the callee when that variable is an argument too.
func keyBinds(env *symEnv, arg, param string, strParams map[string][]string) []func(*symEnv) {
	var binds []func(*symEnv)
	for _, k := range sortedKeys(env.boolTerms) {
		key, ok := strings.CutPrefix(k, arg+inMark)
		if !ok {
			continue
		}
		b := env.boolTerms[k]
		names := []string{key}
		if v, byVar := strings.CutPrefix(key, "$"); byVar {
			names = nil
			for _, p := range strParams[v] {
				names = append(names, "$"+p)
			}
		}
		for _, n := range names {
			binds = append(binds, func(c *symEnv) { c.boolTerms[param+inMark+n] = b })
		}
	}
	return binds
}
