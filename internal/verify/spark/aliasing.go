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
// booleans and strings, and that has no relation to another entity: nothing
// reachable from it can be shared on its own.
func (v *verifier) isFlatEntity(t sema.Type) bool {
	et, ok := t.(*sema.EntityType)
	if !ok || len(et.Relations) > 0 {
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

// How much of a variable may be what a parameter that is not mut was given.
const (
	roNone = iota
	// roBelow: a `with` copy. Its own fields are new, the entities it holds
	// are the original's.
	roBelow
	// roAll: the value itself, or part of it.
	roAll
)

// readonlyNames lists the variables of a function that may hold (part of)
// what a parameter that is not mut was given: the parameter itself, and
// what is taken out of it by an assignment, a loop or a match.
func (v *verifier) readonlyNames(params []sema.FuncParamInfo, body any) map[string]int {
	ro := map[string]int{}
	for _, p := range params {
		if !p.Mut && !p.Own && !isScalar(p.Type) {
			ro[p.Name] = roAll
		}
	}
	var derived func(e ast.Expr) int
	anyDerived := func(es ...ast.Expr) int {
		for _, e := range es {
			if derived(e) != roNone {
				return roAll
			}
		}
		return roNone
	}
	derived = func(e ast.Expr) int {
		if e == nil || isScalar(v.info.ExprTypes[e]) {
			return roNone
		}
		if root := mutRoot(e); root != nil {
			level := ro[root.Name]
			if _, bare := e.(*ast.Ident); level == roBelow && !bare {
				// Something inside the copy.
				return roAll
			}
			return level
		}
		switch x := e.(type) {
		case *ast.TryExpr:
			return derived(x.Inner)
		case *ast.WithExpr:
			// The copy shares the entities inside the original, if any.
			if v.isFlatEntity(v.info.ExprTypes[x.Base]) || derived(x.Base) == roNone {
				return roNone
			}
			return roBelow
		case *ast.PipeExpr:
			return anyDerived(x.Left, x.Right)
		case *ast.MatchExpr:
			level := roNone
			for _, arm := range x.Arms {
				level = max(level, derived(arm.Value))
			}
			return level
		case *ast.ListLit:
			return anyDerived(x.Elems...)
		case *ast.MapLit:
			for _, en := range x.Entries {
				if derived(en.Value) != roNone {
					return roAll
				}
			}
		default:
			// A call may hand back what it was given.
			args, _ := callArgs(e)
			for _, a := range args {
				if derived(a.Value) != roNone {
					return roAll
				}
			}
		}
		return roNone
	}
	for changed := true; changed; {
		changed = false
		add := func(name string, level int) {
			if ro[name] < level {
				ro[name] = level
				changed = true
			}
		}
		bindPatterns := func(subject ast.Expr, pats ...ast.Pattern) {
			if derived(subject) == roNone {
				return
			}
			for _, pat := range pats {
				visitNodes(reflect.ValueOf(pat), func(n any) {
					if vp, ok := n.(*ast.VarPat); ok {
						add(vp.Name, roAll)
					}
				})
			}
		}
		visitNodes(reflect.ValueOf(body), func(n any) {
			switch x := n.(type) {
			case *ast.LetAssignStmt:
				add(x.Name, derived(x.Value))
			case *ast.ForStmt:
				if derived(x.Iterable) != roNone {
					add(x.Var, roAll)
				}
			case *ast.MatchStmt:
				for _, arm := range x.Arms {
					bindPatterns(x.Subject, arm.Pattern)
				}
			case *ast.MatchExpr:
				for _, arm := range x.Arms {
					bindPatterns(x.Subject, arm.Pattern)
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
	// reject is given the object that is written; whole says that anything
	// reachable from it may be (it is passed as mut).
	reject := func(obj ast.Expr, whole bool, span ast.Span) {
		root := mutRoot(obj)
		if root == nil || ro[root.Name] == roNone {
			return
		}
		if _, bare := obj.(*ast.Ident); ro[root.Name] == roBelow && bare && !whole {
			// A field of the copy itself.
			return
		}
		v.record(fmt.Sprintf("%s.readonly_%s", scope, root.Name), scope, span, "a value received without mut is not written", VCFailed,
			fmt.Sprintf("%s may hold a value this function received through a parameter that is not `mut`, so it cannot be written here", root.Name), nil)
	}
	visitNodes(reflect.ValueOf(body), func(n any) {
		switch x := n.(type) {
		case *ast.FieldAssignStmt:
			reject(x.Object, false, x.Span)
		case *ast.IndexAssignStmt:
			reject(x.List, false, x.Span)
		case *ast.CompoundAssignStmt:
			switch t := x.Target.(type) {
			case *ast.FieldExpr:
				reject(t.Object, false, x.Span)
			case *ast.IndexExpr:
				reject(t.List, false, x.Span)
			}
		}
	})
	visitExprs(reflect.ValueOf(body), func(e ast.Expr) bool {
		args, _ := callArgs(e)
		for _, a := range args {
			if a.Mut {
				reject(a.Value, true, e.GetSpan())
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

// A list, a string and a byte view never change their length. A map does,
// when a key is inserted, and so may a value whose type is not known.
func hasFixedLen(t sema.Type) bool {
	switch t.(type) {
	case *sema.ListType, sema.StrType, *sema.HandleType:
		return true
	}
	return false
}

// forgetMapLens drops every map length: a map may have been inserted into,
// and maps are references, so which one is not known.
func (e *symEnv) forgetMapLens() {
	for k := range e.mapLens {
		delete(e.listLens, k)
		delete(e.mapLens, k)
	}
}

// mayInsert reports whether the code under node can insert into a map:
// an element assignment on something that is not a list, or a mut argument.
func (v *verifier) mayInsert(node any) bool {
	found := false
	visitNodes(reflect.ValueOf(node), func(n any) {
		switch x := n.(type) {
		case *ast.IndexAssignStmt:
			found = found || !hasFixedLen(v.info.ExprTypes[x.List])
		case *ast.CompoundAssignStmt:
			if ix, ok := x.Target.(*ast.IndexExpr); ok {
				found = found || !hasFixedLen(v.info.ExprTypes[ix.List])
			}
		}
	})
	visitExprs(reflect.ValueOf(node), func(e ast.Expr) bool {
		args, _ := callArgs(e)
		for _, a := range args {
			found = found || a.Mut
		}
		return true
	})
	return found
}
