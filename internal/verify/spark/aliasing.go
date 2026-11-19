package spark

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/smt"
)

// Entities are references: two variables, or a variable and an element of a
// list, can be one object. What is known about a variable is therefore only
// kept across a write made some other way while the variable is the one way
// to reach its entity (it is not in symEnv.shared).

// forgetEntity keeps of the entity under name only what its fields' types say.
func (e *symEnv) forgetEntity(name string) {
	for _, k := range sortedKeys(e.intTerms) {
		if !strings.HasPrefix(k, name+".") {
			continue
		}
		t := smt.Var(e.freshVar(k))
		e.intTerms[k] = t
		if iv, ok := e.intervals[k]; ok && iv.HasLo && iv.HasHi {
			e.assume(smt.Ge(t, smt.Const(iv.Lo)))
			e.assume(smt.Le(t, smt.Const(iv.Hi)))
		} else {
			e.assume(smt.FitsInt64(t))
		}
	}
	for _, k := range sortedKeys(e.boolTerms) {
		if strings.HasPrefix(k, name+".") {
			e.boolTerms[k] = smt.BoolVar{Name: e.freshVar(k)}
		}
	}
	for _, k := range sortedKeys(e.listLens) {
		if strings.HasPrefix(k, name+".") {
			delete(e.listLens, k)
			delete(e.listElems, k)
			delete(e.sumInfos, k)
		}
	}
}

// forgetAliases is called when the entity obj evaluates to has been written.
// A shared variable other than the one written through may be that entity.
func (v *verifier) forgetAliases(obj ast.Expr, env *symEnv) {
	written := ""
	root := obj
	for {
		fe, ok := root.(*ast.FieldExpr)
		if !ok {
			break
		}
		root = fe.Object
	}
	if id, ok := root.(*ast.Ident); ok {
		if !env.shared[id.Name] {
			return
		}
		written = id.Name
	}
	for _, name := range sortedKeys(env.shared) {
		if name != written {
			env.forgetEntity(name)
		}
	}
}

// forgetWrittenAliases applies forgetAliases for every entity that the code
// under node may write: a field assignment or a mut argument.
func (v *verifier) forgetWrittenAliases(node any, env *symEnv) {
	visitNodes(reflect.ValueOf(node), func(n any) {
		switch x := n.(type) {
		case *ast.FieldAssignStmt:
			v.forgetAliases(x.Object, env)
		case *ast.CompoundAssignStmt:
			if fe, ok := x.Target.(*ast.FieldExpr); ok {
				v.forgetAliases(fe.Object, env)
			}
		}
	})
	visitExprs(reflect.ValueOf(node), func(e ast.Expr) bool {
		args, _ := callArgs(e)
		for _, a := range args {
			if a.Mut {
				v.forgetAliases(a.Value, env)
			}
		}
		return true
	})
}

// isScalar reports whether a value of type t is a number, a boolean or a
// string: something that cannot be written in place.
func isScalar(t sema.Type) bool {
	switch t.(type) {
	case *sema.IntType, sema.BoolType, sema.StrType:
		return true
	}
	return false
}

// readonlyNames lists the variables of a function that may hold (part of)
// what a parameter that is not mut was given: the parameter itself, and
// what is taken out of it by an assignment, a loop or a match.
func (v *verifier) readonlyNames(params []sema.FuncParamInfo, body any) map[string]bool {
	ro := map[string]bool{}
	for _, p := range params {
		if !p.Mut && !p.Own && !isScalar(p.Type) {
			ro[p.Name] = true
		}
	}
	var derived func(e ast.Expr) bool
	derived = func(e ast.Expr) bool {
		if e == nil || isScalar(v.info.ExprTypes[e]) {
			return false
		}
		if root := mutRoot(e); root != nil {
			return ro[root.Name]
		}
		switch x := e.(type) {
		case *ast.TryExpr:
			return derived(x.Inner)
		case *ast.WithExpr:
			// The copy shares the entities inside the original.
			return derived(x.Base)
		case *ast.PipeExpr:
			return derived(x.Left) || derived(x.Right)
		case *ast.MatchExpr:
			for _, arm := range x.Arms {
				if derived(arm.Value) {
					return true
				}
			}
		case *ast.ListLit:
			for _, el := range x.Elems {
				if derived(el) {
					return true
				}
			}
		case *ast.MapLit:
			for _, en := range x.Entries {
				if derived(en.Value) {
					return true
				}
			}
		default:
			// A call may hand back what it was given.
			args, _ := callArgs(e)
			for _, a := range args {
				if derived(a.Value) {
					return true
				}
			}
		}
		return false
	}
	bindPatterns := func(pat ast.Pattern) bool {
		changed := false
		visitNodes(reflect.ValueOf(pat), func(n any) {
			if vp, ok := n.(*ast.VarPat); ok && !ro[vp.Name] {
				ro[vp.Name] = true
				changed = true
			}
		})
		return changed
	}
	for changed := true; changed; {
		changed = false
		add := func(name string) {
			if !ro[name] {
				ro[name] = true
				changed = true
			}
		}
		visitNodes(reflect.ValueOf(body), func(n any) {
			switch x := n.(type) {
			case *ast.LetAssignStmt:
				if derived(x.Value) {
					add(x.Name)
				}
			case *ast.ForStmt:
				if derived(x.Iterable) {
					add(x.Var)
				}
			case *ast.MatchStmt:
				if derived(x.Subject) {
					for _, arm := range x.Arms {
						changed = bindPatterns(arm.Pattern) || changed
					}
				}
			case *ast.MatchExpr:
				if derived(x.Subject) {
					for _, arm := range x.Arms {
						changed = bindPatterns(arm.Pattern) || changed
					}
				}
			}
		})
	}
	return ro
}

// checkReadonlyWrites rejects a write made through a variable that may hold
// what a parameter that is not mut was given. The caller keeps what it
// knows about such an argument across the call.
func (v *verifier) checkReadonlyWrites(params []sema.FuncParamInfo, body any, scope string) {
	ro := v.readonlyNames(params, body)
	reject := func(target ast.Expr, span ast.Span) {
		root := mutRoot(target)
		if root == nil || !ro[root.Name] {
			return
		}
		v.record(fmt.Sprintf("%s.readonly_%s", scope, root.Name), scope, span, "a value received without mut is not written", VCFailed,
			fmt.Sprintf("%s may hold a value this function received through a parameter that is not `mut`, so it cannot be written here", root.Name), nil)
	}
	visitNodes(reflect.ValueOf(body), func(n any) {
		switch x := n.(type) {
		case *ast.FieldAssignStmt:
			reject(x.Object, x.Span)
		case *ast.IndexAssignStmt:
			reject(x.List, x.Span)
		case *ast.CompoundAssignStmt:
			if _, plain := x.Target.(*ast.Ident); !plain {
				reject(x.Target, x.Span)
			}
		}
	})
	visitExprs(reflect.ValueOf(body), func(e ast.Expr) bool {
		args, _ := callArgs(e)
		for _, a := range args {
			if a.Mut {
				reject(a.Value, e.GetSpan())
			}
		}
		return true
	})
}
