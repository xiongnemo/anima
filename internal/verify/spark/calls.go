package spark

import (
	"fmt"
	"reflect"
	"slices"
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
//     type, of which the callee's `ensures` clauses are assumed. For that to
//     be true of every return, a `?` proves them too (checkTryExit), and a
//     mut parameter is never rebound to another value (checkParamsNotRebound).
//   - A lambda only passes a variable of the enclosing function as mut when
//     it is a pipeline stage, which runs before the statement is over
//     (checkMutCaptures).

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

// visitNodes calls fn on every syntax node under n: each pointer to a struct.
func visitNodes(n reflect.Value, fn func(any)) {
	visitNodesUntil(n, func(node any) bool {
		fn(node)
		return true
	})
}

// visitNodesUntil is visitNodes, except that the nodes under one for which
// fn returns false are skipped.
func visitNodesUntil(n reflect.Value, fn func(any) bool) {
	switch n.Kind() {
	case reflect.Interface:
		if !n.IsNil() {
			visitNodesUntil(n.Elem(), fn)
		}
	case reflect.Pointer:
		if n.IsNil() {
			return
		}
		if n.Elem().Kind() == reflect.Struct && n.CanInterface() && !fn(n.Interface()) {
			return
		}
		visitNodesUntil(n.Elem(), fn)
	case reflect.Slice:
		for i := 0; i < n.Len(); i++ {
			visitNodesUntil(n.Index(i), fn)
		}
	case reflect.Struct:
		for i := 0; i < n.NumField(); i++ {
			visitNodesUntil(n.Field(i), fn)
		}
	}
}

// reboundNames lists the names that code under node binds to a new value:
// assignments, loop variables and pattern variables.
func reboundNames(node any) map[string]bool {
	names := map[string]bool{}
	visitNodes(reflect.ValueOf(node), func(n any) {
		switch x := n.(type) {
		case *ast.LetAssignStmt:
			names[x.Name] = true
		case *ast.CompoundAssignStmt:
			if id, ok := x.Target.(*ast.Ident); ok {
				names[id.Name] = true
			}
		case *ast.ForStmt:
			names[x.Var] = true
		case *ast.VarPat:
			names[x.Name] = true
		}
	})
	return names
}

// checkParamsNotRebound requires that body, the code of a function or
// workflow, never rebinds a mut parameter: the caller would keep the old
// value while the contracts speak about the new one.
func (v *verifier) checkParamsNotRebound(params []sema.FuncParamInfo, body any, scope string, span ast.Span) {
	rebound := reboundNames(body)
	for _, p := range params {
		if !p.Mut {
			continue
		}
		name := fmt.Sprintf("%s.mut_%s_not_rebound", scope, p.Name)
		formula := "a mut parameter always names the caller's value"
		if rebound[p.Name] {
			v.record(name, scope, span, formula, VCFailed, fmt.Sprintf(
				"mut parameter %q is assigned a new value, which the caller never sees; change its fields or elements instead", p.Name), nil)
		} else {
			v.record(name, scope, span, formula, VCProved, p.Name, nil)
		}
	}
}

// neverFails reports whether e is written as the success variant of an
// Option or a Result, on which `?` cannot return.
func (v *verifier) neverFails(e ast.Expr) bool {
	call, ok := e.(*ast.CallExpr)
	if !ok {
		return false
	}
	id, ok := call.Callee.(*ast.Ident)
	return ok && (id.Name == "Some" || id.Name == "Ok") && !v.callsClosure(call)
}

// checkTryExit proves what a caller may rely on when a `?` returns from the
// current function: the invariants of its mut entities and the ensures
// clauses that do not speak about the result.
func (v *verifier) checkTryExit(env *symEnv, scope string, span ast.Span) {
	v.proveMutInvariants(env, scope, span)
	for idx, ens := range v.curEnsures {
		if mentionsOutside(reflect.ValueOf(ens), "result", nil) {
			continue
		}
		v.prove(fmt.Sprintf("%s.ensures_%d", v.curFuncName, idx+1), scope, span, env, v.evalBool(ens, env, scope))
	}
}

// checkMutCaptures requires that a lambda in exprs which passes a variable
// of the enclosing function as mut is a pipeline stage. Any other lambda may
// run later, when nothing tells the kernel that the variable changed.
func (v *verifier) checkMutCaptures(exprs []ast.Expr, scope string, span ast.Span) {
	stage := map[*ast.LambdaExpr]bool{}
	for _, x := range exprs {
		visitExprs(reflect.ValueOf(x), func(e ast.Expr) bool {
			switch n := e.(type) {
			case *ast.PipeExpr:
				if call, ok := n.Right.(*ast.CallExpr); ok {
					for _, a := range call.Args {
						if lam, ok := a.Value.(*ast.LambdaExpr); ok {
							stage[lam] = true
						}
					}
				}
			case *ast.LambdaExpr:
				if stage[n] {
					return true
				}
				own := map[string]bool{}
				visitNodes(reflect.ValueOf(n), func(sub any) {
					if l, ok := sub.(*ast.LambdaExpr); ok {
						for _, p := range l.Params {
							own[p] = true
						}
					}
				})
				captured := ""
				visitExprs(reflect.ValueOf(n.Body), func(sub ast.Expr) bool {
					args, _ := callArgs(sub)
					for _, a := range args {
						if root := mutRoot(a.Value); a.Mut && root != nil && !own[root.Name] && captured == "" {
							captured = root.Name
						}
					}
					return true
				})
				if captured != "" {
					v.record(scope+".mut_capture", scope, span, "a lambda that changes an outer variable is a pipeline stage", VCFailed,
						fmt.Sprintf("this lambda passes the outer variable %q as mut and may run later; only a pipeline stage (xs |> map(...)) may do that", captured), nil)
				}
				return false
			}
			return true
		})
	}
}

// pipedCall returns the call `x |> f(a)` or `x |> f` makes when f is a
// function of the program: f(x, a). It is nil for any other stage.
func (v *verifier) pipedCall(pe *ast.PipeExpr) *ast.CallExpr {
	first := ast.CallArg{Span: pe.Left.GetSpan(), Value: pe.Left}
	switch rhs := pe.Right.(type) {
	case *ast.CallExpr:
		if id, ok := rhs.Callee.(*ast.Ident); ok && v.info.Funcs[id.Name] != nil {
			return &ast.CallExpr{Span: rhs.Span, Callee: rhs.Callee, TypeArgs: rhs.TypeArgs,
				Args: append([]ast.CallArg{first}, rhs.Args...)}
		}
	case *ast.Ident:
		if v.info.Funcs[rhs.Name] != nil {
			return &ast.CallExpr{Span: pe.Span, Callee: rhs, Args: []ast.CallArg{first}}
		}
	}
	return nil
}

// argParams maps each argument of a call to the index of the parameter it
// is bound to, as both backends do: a keyword argument to the parameter it
// names, any other to the parameter at its own position. problem says why
// the arguments do not give every parameter exactly one value; the backends
// disagree on such a call, so it is not verified.
func argParams(params []sema.FuncParamInfo, args []ast.CallArg) (idx []int, problem string) {
	note := func(format string, a ...any) {
		if problem == "" {
			problem = fmt.Sprintf(format, a...)
		}
	}
	given := make([]bool, len(params))
	keywords := false
	for i, a := range args {
		pi := -1
		if a.Name == "" {
			if i < len(params) {
				pi = i
			}
		} else {
			keywords = true
			for k, p := range params {
				if p.Name == a.Name {
					pi = k
				}
			}
			if pi < 0 {
				note("there is no parameter %q", a.Name)
			}
		}
		if pi >= 0 {
			if given[pi] {
				note("parameter %q is given more than once", params[pi].Name)
			}
			given[pi] = true
		}
		idx = append(idx, pi)
	}
	if keywords {
		for k, p := range params {
			if !given[k] {
				note("parameter %q is not given", p.Name)
			}
		}
	}
	return idx, problem
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
// An entity's invariant is only kept when returned says that a function or
// workflow of this program has just returned it: each proves the invariants
// of its mut entities on the way out. Elsewhere the call may not have run,
// and the entity may be in the middle of an update by the caller.
func (v *verifier) havocMutArg(a ast.CallArg, env *symEnv, returned bool) {
	// The callee may have inserted into a map it reaches. What it
	// guarantees about the argument is bound after that.
	env.forgetMapLens(a.Value)
	env.forgetElemHulls()
	saved := v.noInvariants
	v.noInvariants = !returned
	if path, ok := mutArgPath(a.Value); ok {
		// A callee given a map cannot make the name hold another one: the
		// keys that were in it still are (forgetMapLens).
		kept := map[string]smt.BoolExpr{}
		if _, isMap := v.info.ExprTypes[a.Value].(*sema.MapType); isMap {
			for k, b := range env.boolTerms {
				if strings.HasPrefix(k, path+inMark) {
					kept[k] = b
				}
			}
		}
		v.bindFresh(env, path, v.info.ExprTypes[a.Value])
		for k, b := range kept {
			env.boolTerms[k] = b
		}
	} else if root := mutRoot(a.Value); root != nil {
		v.bindFresh(env, root.Name, v.info.ExprTypes[root])
	}
	v.noInvariants = saved
	// The callee may have written the entity, which another name may share.
	v.forgetAliases(a.Value, env)
}

// havocMutArgs forgets every variable passed as mut anywhere under node,
// which is an expression, a statement or a list of either.
func (v *verifier) havocMutArgs(node any, env *symEnv) {
	visitExprs(reflect.ValueOf(node), func(e ast.Expr) bool {
		args, _ := callArgs(e)
		for _, a := range args {
			if a.Mut {
				v.havocMutArg(a, env, false)
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
// conditions of an if are units of their own.
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
		// The subject is evaluated once and then compared in every arm, so
		// a guard must not change what it was read from.
		unit := []ast.Expr{s.Subject}
		for _, arm := range s.Arms {
			if arm.Guard != nil {
				unit = append(unit, arm.Guard)
			}
		}
		return [][]ast.Expr{unit}
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
//
// The kernel reads the statement in the state its calls leave. So what a
// callee may write is not read elsewhere in the statement under another
// name either: when the variable passed as mut may be reached through
// another name, no other such variable appears outside that call.
func (v *verifier) checkMutCalls(exprs []ast.Expr, env *symEnv, scope string, span ast.Span) {
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
	if clash == "" {
		for _, root := range roots {
			if !env.shared[root] {
				continue
			}
			for _, other := range sortedKeys(env.shared) {
				if other == root {
					continue
				}
				if outerMentioned(exprs, other, owner[root]) {
					v.record(name, scope, span, formula, VCFailed, fmt.Sprintf(
						"%q is passed as mut and may be reached through %q, which is used elsewhere in this statement; "+
							"put the call in a statement of its own", root, other), nil)
					return
				}
			}
		}
	}
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
		// A parameter of that name is another variable in a lambda's body,
		// unless owner is in that body: then it is the one owner speaks of.
		if lam, ok := e.(*ast.LambdaExpr); ok && slices.Contains(lam.Params, root) {
			return owner != nil && containsExpr(lam.Body, owner)
		}
		return true
	})
	return found
}

// containsExpr reports whether target is n or a part of it.
func containsExpr(n ast.Expr, target ast.Expr) bool {
	found := false
	visitExprs(reflect.ValueOf(n), func(e ast.Expr) bool {
		if e == target {
			found = true
		}
		return !found
	})
	return found
}

// outerMentioned reports whether the outer variable name appears in exprs
// anywhere but among the arguments of the call owner. A lambda's parameter
// of that name is another variable, and hides it in the lambda's body.
func outerMentioned(exprs []ast.Expr, name string, owner ast.Expr) bool {
	found := false
	for _, x := range exprs {
		visitExprs(reflect.ValueOf(x), func(e ast.Expr) bool {
			if found || e == owner {
				return false
			}
			if lam, ok := e.(*ast.LambdaExpr); ok && slices.Contains(lam.Params, name) {
				return false
			}
			if id, ok := e.(*ast.Ident); ok && id.Name == name {
				found = true
			}
			return true
		})
	}
	return found
}

// applyCallEffects models what calling fi does to the caller's variables:
// every mut argument is rebound to an arbitrary value of its type, and the
// ensures clauses of fi that only speak about its parameters are assumed.
// callEnv is the caller's state before the call with the parameters bound.
func (v *verifier) applyCallEffects(fi *sema.FuncInfo, args []ast.CallArg, argParam []int, env, callEnv *symEnv, scope string) {
	changed := false
	for _, a := range args {
		if a.Mut {
			v.havocMutArg(a, env, true)
			changed = true
		}
	}
	if !changed || fi.Decl == nil || len(fi.Decl.Ensures) == 0 {
		return
	}
	// post is the state after the call as the callee names it. A parameter
	// the callee rebinds no longer names the argument when it returns, so
	// clauses about it are not used.
	post := env.clone()
	rebound := reboundNames(fi.Decl.Body)
	argOf := map[int]ast.CallArg{}
	for i, pi := range argParam {
		if pi >= 0 {
			argOf[pi] = args[i]
		}
	}
	params := map[string]bool{}
	ints := map[string]smt.LinearTerm{}
	bools := map[string]smt.BoolExpr{}
	lens := map[string]smt.LinearTerm{}
	elems := map[string]smt.Interval{}
	for i, p := range fi.Type.Params {
		params[p.Name] = true
		if rebound[p.Name] {
			continue
		}
		from, src := p.Name, callEnv
		if a, given := argOf[i]; given && a.Mut {
			path, ok := mutArgPath(a.Value)
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
		if ensuresUsable(ens, post, params, false) {
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
// site: it is built from comparisons and arithmetic over integer parameters
// that post has a value for. Anything else (the result, a call, a local of
// the callee) is left out, which only makes the caller know less.
func ensuresUsable(e ast.Expr, post *symEnv, params map[string]bool, old bool) bool {
	bound := func(path string) bool {
		if !params[strings.SplitN(path, ".", 2)[0]] {
			return false
		}
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
			return !old && ensuresUsable(x.Inner, post, params, true)
		}
	case *ast.UnaryExpr:
		return ensuresUsable(x.Expr, post, params, old)
	case *ast.BinaryExpr:
		switch x.Op {
		case "and", "or", "implies", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*":
			return ensuresUsable(x.Left, post, params, old) && ensuresUsable(x.Right, post, params, old)
		}
	}
	return false
}
