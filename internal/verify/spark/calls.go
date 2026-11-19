package spark

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/smt"
)

// A call may change the variables it receives as `mut`. The kernel handles
// that in two parts:
//
//   - A variable passed as mut is used nowhere else in the expressions of
//     the same statement (checkMutCalls). The order in which the statement
//     reads the variable and the call changes it then never matters.
//   - After the call the variable holds an arbitrary value of its declared
//     type, of which the callee's `ensures` clauses are assumed.

// visitExprs calls fn on every expression under n, outermost first. When fn
// returns false the expression's own children are skipped.
func visitExprs(n reflect.Value, fn func(ast.Expr) bool) {
	switch n.Kind() {
	case reflect.Interface:
		if !n.IsNil() {
			visitExprs(n.Elem(), fn)
		}
	case reflect.Pointer:
		if n.IsNil() {
			return
		}
		if n.CanInterface() {
			if e, ok := n.Interface().(ast.Expr); ok && !fn(e) {
				return
			}
		}
		visitExprs(n.Elem(), fn)
	case reflect.Slice:
		for i := 0; i < n.Len(); i++ {
			visitExprs(n.Index(i), fn)
		}
	case reflect.Struct:
		for i := 0; i < n.NumField(); i++ {
			visitExprs(n.Field(i), fn)
		}
	}
}

// callArgs returns the arguments of a call or run_workflow expression.
func callArgs(e ast.Expr) ([]ast.CallArg, bool) {
	switch c := e.(type) {
	case *ast.CallExpr:
		return c.Args, true
	case *ast.RunWorkflowExpr:
		return c.Args, true
	}
	return nil, false
}

// mutArgPath is the variable path a mut argument names: s, or box.inner.
func mutArgPath(e ast.Expr) (string, bool) {
	switch x := e.(type) {
	case *ast.Ident:
		return x.Name, true
	case *ast.FieldExpr:
		base, ok := mutArgPath(x.Object)
		return base + "." + x.Field, ok
	}
	return "", false
}

// mutRoot is the variable a mut argument belongs to: rows for rows[0].inner.
func mutRoot(e ast.Expr) *ast.Ident {
	for {
		switch x := e.(type) {
		case *ast.Ident:
			return x
		case *ast.FieldExpr:
			e = x.Object
		case *ast.IndexExpr:
			e = x.List
		default:
			return nil
		}
	}
}

// havocMutArg forgets what env knows about a mut argument, keeping its type.
func (v *verifier) havocMutArg(a ast.CallArg, env *symEnv) {
	if path, ok := mutArgPath(a.Value); ok {
		v.bindFresh(env, path, v.info.ExprTypes[a.Value])
	} else if root := mutRoot(a.Value); root != nil {
		v.bindFresh(env, root.Name, v.info.ExprTypes[root])
	}
}

// havocMutArgs forgets every variable passed as mut anywhere under node,
// which is an expression, a statement or a list of either.
func (v *verifier) havocMutArgs(node any, env *symEnv) {
	visitExprs(reflect.ValueOf(node), func(e ast.Expr) bool {
		args, _ := callArgs(e)
		for _, a := range args {
			if a.Mut {
				v.havocMutArg(a, env)
			}
		}
		return true
	})
}

// havocLambdaMutArgs forgets the variables that lambdas under node pass as
// mut. A lambda body runs once per element, so it is checked from a state in
// which earlier runs have already happened.
func (v *verifier) havocLambdaMutArgs(node any, env *symEnv) {
	visitExprs(reflect.ValueOf(node), func(e ast.Expr) bool {
		if lam, ok := e.(*ast.LambdaExpr); ok {
			v.havocMutArgs(lam, env)
			return false
		}
		return true
	})
}

// stmtExprGroups returns the expressions a statement evaluates itself, not
// those of nested statements. Each group is evaluated as one unit; the
// conditions of an if and the guards of a match are units of their own.
func stmtExprGroups(stmt ast.Stmt) [][]ast.Expr {
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		return [][]ast.Expr{{s.Value}}
	case *ast.CompoundAssignStmt:
		return [][]ast.Expr{{s.Target, s.Value}}
	case *ast.FieldAssignStmt:
		return [][]ast.Expr{{s.Object, s.Value}}
	case *ast.IndexAssignStmt:
		return [][]ast.Expr{{s.List, s.Index, s.Value}}
	case *ast.IfStmt:
		var groups [][]ast.Expr
		for _, br := range s.Branches {
			groups = append(groups, []ast.Expr{br.Cond})
		}
		return groups
	case *ast.MatchStmt:
		groups := [][]ast.Expr{{s.Subject}}
		for _, arm := range s.Arms {
			if arm.Guard != nil {
				groups = append(groups, []ast.Expr{arm.Guard})
			}
		}
		return groups
	case *ast.ForStmt:
		return [][]ast.Expr{{s.Iterable}}
	case *ast.WhileStmt:
		return [][]ast.Expr{{s.Cond}}
	case *ast.ReturnStmt:
		return [][]ast.Expr{{s.Value}}
	case *ast.ExprStmt:
		return [][]ast.Expr{{s.Expr}}
	case *ast.CallStmt:
		if s.Call == nil {
			return nil
		}
		return [][]ast.Expr{{s.Call}}
	}
	// A statement kind not listed above: every expression in it is one unit.
	var all []ast.Expr
	visitExprs(reflect.ValueOf(stmt), func(e ast.Expr) bool {
		all = append(all, e)
		return false
	})
	return [][]ast.Expr{all}
}

// checkMutCalls requires that a variable passed as mut in exprs, the
// expressions of one statement, is passed by a single call and appears
// nowhere else in them except among that call's own arguments.
func (v *verifier) checkMutCalls(exprs []ast.Expr, scope string, span ast.Span) {
	owner := map[string]ast.Expr{}
	var roots []string
	clash := ""
	for _, x := range exprs {
		visitExprs(reflect.ValueOf(x), func(e ast.Expr) bool {
			args, _ := callArgs(e)
			for _, a := range args {
				root := mutRoot(a.Value)
				if !a.Mut || root == nil {
					continue
				}
				if c, seen := owner[root.Name]; !seen {
					owner[root.Name] = e
					roots = append(roots, root.Name)
				} else if c != e && clash == "" {
					clash = root.Name
				}
			}
			return true
		})
	}
	for _, root := range roots {
		if clash != "" {
			break
		}
		for _, x := range exprs {
			if mentionsOutside(reflect.ValueOf(x), root, owner[root]) {
				clash = root
				break
			}
		}
	}
	if len(roots) == 0 {
		return
	}
	name := scope + ".mut_call_alone"
	formula := "a variable passed as mut is not used elsewhere in the statement"
	if clash != "" {
		v.record(name, scope, span, formula, VCFailed, fmt.Sprintf(
			"%q is passed as mut and also used elsewhere in this statement; "+
				"put the call in a statement of its own", clash), nil)
		return
	}
	v.record(name, scope, span, formula, VCProved, strings.Join(roots, ", "), nil)
}

// mentionsOutside reports whether the variable root appears under n anywhere
// but among the arguments of the call owner.
func mentionsOutside(n reflect.Value, root string, owner ast.Expr) bool {
	found := false
	visitExprs(n, func(e ast.Expr) bool {
		if found {
			return false
		}
		if e == owner {
			if c, ok := e.(*ast.CallExpr); ok {
				found = mentionsOutside(reflect.ValueOf(c.Callee), root, nil)
			}
			return false
		}
		if id, ok := e.(*ast.Ident); ok && id.Name == root {
			found = true
		}
		return true
	})
	return found
}

// applyCallEffects models what calling fi does to the caller's variables:
// every mut argument is rebound to an arbitrary value of its type, and the
// ensures clauses of fi that only speak about its parameters are assumed.
// callEnv is the caller's state before the call with the parameters bound.
func (v *verifier) applyCallEffects(fi *sema.FuncInfo, args []ast.CallArg, env, callEnv *symEnv, scope string) {
	changed := false
	for _, a := range args {
		if a.Mut {
			v.havocMutArg(a, env)
			changed = true
		}
	}
	if !changed || fi.Decl == nil || len(fi.Decl.Ensures) == 0 {
		return
	}
	// post is the state after the call as the callee names it.
	post := env.clone()
	params := map[string]bool{}
	ints := map[string]smt.LinearTerm{}
	bools := map[string]smt.BoolExpr{}
	lens := map[string]smt.LinearTerm{}
	elems := map[string]smt.Interval{}
	for i, p := range fi.Type.Params {
		params[p.Name] = true
		from, src := p.Name, callEnv
		if i < len(args) && args[i].Mut {
			path, ok := mutArgPath(args[i].Value)
			if !ok {
				continue
			}
			from, src = path, env
		}
		under := func(k string) (string, bool) {
			if k == from || strings.HasPrefix(k, from+".") {
				return p.Name + k[len(from):], true
			}
			return "", false
		}
		for k, t := range src.intTerms {
			if nk, ok := under(k); ok {
				ints[nk] = t
			}
		}
		for k, b := range src.boolTerms {
			if nk, ok := under(k); ok {
				bools[nk] = b
			}
		}
		for k, t := range src.listLens {
			if nk, ok := under(k); ok {
				lens[nk] = t
			}
		}
		for k, iv := range src.listElems {
			if nk, ok := under(k); ok {
				elems[nk] = iv
			}
		}
	}
	for name := range params {
		post.unbind(name)
	}
	for k, t := range ints {
		post.intTerms[k] = t
	}
	for k, b := range bools {
		post.boolTerms[k] = b
	}
	for k, t := range lens {
		post.listLens[k] = t
	}
	for k, iv := range elems {
		post.listElems[k] = iv
	}
	// old(p.f) is the value the parameter had when the call started.
	post.entryTerms = map[string]smt.LinearTerm{}
	for k, t := range callEnv.intTerms {
		if params[strings.SplitN(k, ".", 2)[0]] {
			post.entryTerms[k] = t
		}
	}
	var facts []smt.BoolExpr
	for _, ens := range fi.Decl.Ensures {
		if ensuresUsable(ens, post, false) {
			facts = append(facts, v.evalBool(ens, post, scope))
		}
	}
	// Evaluating a clause may have named new symbols and bounded them.
	env.pc = append(env.pc, post.pc[len(env.pc):]...)
	for _, f := range facts {
		env.assume(f)
	}
}

// ensuresUsable reports whether an ensures clause can be assumed at a call
// site: it is built from comparisons and arithmetic over integers that post
// has a value for. Anything else (the result, a call, an unbound name) is
// left out, which only makes the caller know less.
func ensuresUsable(e ast.Expr, post *symEnv, old bool) bool {
	bound := func(path string) bool {
		if old {
			_, ok := post.entryTerms[path]
			return ok
		}
		_, ok := post.intTerms[path]
		return ok
	}
	switch x := e.(type) {
	case *ast.IntLit, *ast.BoolLit:
		return true
	case *ast.Ident:
		return x.Name != "result" && bound(x.Name)
	case *ast.FieldExpr:
		id, ok := x.Object.(*ast.Ident)
		return ok && bound(id.Name+"."+x.Field)
	case *ast.OldExpr:
		switch x.Inner.(type) {
		case *ast.Ident, *ast.FieldExpr:
			return !old && ensuresUsable(x.Inner, post, true)
		}
	case *ast.UnaryExpr:
		return ensuresUsable(x.Expr, post, old)
	case *ast.BinaryExpr:
		switch x.Op {
		case "and", "or", "implies", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*":
			return ensuresUsable(x.Left, post, old) && ensuresUsable(x.Right, post, old)
		}
	}
	return false
}
