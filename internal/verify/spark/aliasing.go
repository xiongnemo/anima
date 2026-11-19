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

// holds reports whether goal is known to be true in env.
func (v *verifier) holds(env *symEnv, goal smt.BoolExpr) bool {
	if bc, ok := goal.(smt.BoolConst); ok {
		return bc.Val
	}
	return smt.CheckSat(smt.And(smt.Int64Pins(), env.pathCond(), smt.Not(goal))).Status == smt.StatusUnsat
}

// forgetEntity keeps of the entity variable name only what its type says:
// the ranges of its fields. Its invariants are kept too when they are known
// to hold now and the entity is flat: every write that could have reached
// it has proved them again (proveSharedEntity, a callee's exit).
func (v *verifier) forgetEntity(env *symEnv, name string) {
	et := env.entTypes[name]
	if et == nil {
		// Not an entity the kernel has bound: a list, or a value whose
		// type is not known.
		for _, k := range sortedKeys(env.intTerms) {
			if strings.HasPrefix(k, name+".") {
				t := smt.Var(env.freshVar(k))
				env.intTerms[k] = t
				env.assume(smt.FitsInt64(t))
			}
		}
		for _, k := range sortedKeys(env.boolTerms) {
			if strings.HasPrefix(k, name+".") {
				env.boolTerms[k] = smt.BoolVar{Name: env.freshVar(k)}
			}
		}
		return
	}
	valid := v.isFlatEntity(et)
	for _, inv := range et.Invariants {
		valid = valid && v.holds(env, v.evalBoolWithPrefix(inv, env, name+"."))
	}
	saved := v.noInvariants
	v.noInvariants = !valid
	v.bindFresh(env, name, et)
	v.noInvariants = saved
}

// forgetAliases is called when the entity obj evaluates to has been written,
// or handed to a callee as mut. A shared variable other than the one written
// through may be that entity, or one inside it.
func (v *verifier) forgetAliases(obj ast.Expr, env *symEnv) {
	written := ""
	if id, ok := obj.(*ast.Ident); ok {
		// Written through a variable that is the one way to reach its
		// entity, which holds nothing another variable could be.
		if !env.shared[id.Name] && v.isFlatEntity(v.info.ExprTypes[id]) {
			return
		}
		written = id.Name
	} else if root := mutRoot(obj); root != nil {
		// box.inner, rows[i]: the object may be one a shared variable names.
		written = root.Name
	}
	for _, name := range sortedKeys(env.shared) {
		if name != written {
			v.forgetEntity(env, name)
		}
	}
}

// isFlatEntity reports whether t is an entity whose fields are all numbers,
// booleans and strings: nothing reachable from it can be shared on its own.
func (v *verifier) isFlatEntity(t sema.Type) bool {
	et, ok := t.(*sema.EntityType)
	if !ok {
		return false
	}
	for _, f := range et.Fields {
		if !isScalar(f.Type) {
			return false
		}
	}
	return true
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

// checkMutAliases rejects a call that passes as mut something another of
// its arguments may reach too. The callee is verified with its parameters
// taken for separate values, which the caller therefore has to guarantee:
// of a mut argument and any other argument that can hold an entity, one at
// least is rooted in a variable that is not shared.
func (v *verifier) checkMutAliases(groups [][]ast.Expr, env *symEnv, scope string) {
	unshared := func(e ast.Expr) bool {
		r := mutRoot(e)
		return r != nil && !env.shared[r.Name]
	}
	visitExprs(reflect.ValueOf(groups), func(e ast.Expr) bool {
		if _, ok := e.(*ast.LambdaExpr); ok {
			// Its parameters are not this function's variables.
			return false
		}
		var args []ast.CallArg
		name := "call"
		switch x := e.(type) {
		case *ast.PipeExpr:
			if c := v.pipedCall(x); c != nil {
				args = c.Args
				if id, ok := c.Callee.(*ast.Ident); ok {
					name = id.Name
				}
			}
		case *ast.CallExpr:
			args = x.Args
			if id, ok := x.Callee.(*ast.Ident); ok {
				name = id.Name
			}
		case *ast.RunWorkflowExpr:
			args, name = x.Args, x.Name
		}
		for i, m := range args {
			if !m.Mut || !mayHoldEntity(v.info.ExprTypes[m.Value]) || unshared(m.Value) {
				continue
			}
			for j, o := range args {
				if i == j || !mayHoldEntity(v.info.ExprTypes[o.Value]) || v.isFreshValue(o.Value) || unshared(o.Value) {
					continue
				}
				v.record(fmt.Sprintf("%s.call_%s_mut_alias", scope, name), scope, e.GetSpan(), "a mut argument is not reachable from another argument", VCFailed,
					fmt.Sprintf("in the call of %s, the mut argument %d and argument %d may be, or hold, the same entity", name, i+1, j+1), nil)
				return true
			}
		}
		return true
	})
}
