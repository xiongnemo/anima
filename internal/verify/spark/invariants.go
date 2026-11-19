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

// An entity's invariant may be broken while a function updates its fields
// one by one. Wherever the entity leaves that function's hands (a call
// argument, a returned value, an element or field of another value) it has
// to hold again, which is what lets the receiver assume it.

// entityProbe names an entity value that has no name of its own while its
// invariants are proved.
const entityProbe = "\x00entity"

// hasInvariants reports whether an entity of type t, or one in its fields,
// declares an invariant.
func hasInvariants(t sema.Type, seen map[*sema.EntityType]bool) bool {
	et, ok := t.(*sema.EntityType)
	if !ok || seen[et] {
		return false
	}
	if len(et.Invariants) > 0 {
		return true
	}
	if seen == nil {
		seen = map[*sema.EntityType]bool{}
	}
	seen[et] = true
	for _, f := range et.Fields {
		if hasInvariants(f.Type, seen) {
			return true
		}
	}
	return false
}

// entityHolds reports whether the entity e evaluates to is known to satisfy
// its invariants because of where it comes from: a constructor, a function
// or workflow of the program (each proves it for what it returns), or an
// element of a list or map (proved when it was put there).
func (v *verifier) entityHolds(e ast.Expr) bool {
	switch x := e.(type) {
	case *ast.TryExpr:
		return v.entityHolds(x.Inner)
	case *ast.IndexExpr:
		return true
	case *ast.RunWorkflowExpr:
		return v.info.Workflows[x.Name] != nil
	case *ast.PipeExpr:
		return v.pipedCall(x) != nil
	case *ast.CallExpr:
		if id, ok := x.Callee.(*ast.Ident); ok {
			return v.info.Entities[id.Name] != nil || v.info.Funcs[id.Name] != nil
		}
	}
	return false
}

// proveEntityValue proves the invariants of the entity e evaluates to, at a
// point where it is handed to something else. Nothing is proved for a value
// that is not an entity with invariants, or that entityHolds vouches for.
func (v *verifier) proveEntityValue(e ast.Expr, env *symEnv, scope string) {
	if e == nil {
		return
	}
	et, ok := v.info.ExprTypes[e].(*sema.EntityType)
	if !ok || !hasInvariants(et, nil) || v.entityHolds(e) {
		return
	}
	if me, ok := e.(*ast.MatchExpr); ok {
		// The value is that of one arm, in the state that arm runs in.
		for _, arm := range me.Arms {
			armEnv := env.clone()
			v.assumePattern(arm.Pattern, me.Subject, armEnv, scope)
			if arm.Guard != nil {
				armEnv.assume(v.evalBool(arm.Guard, armEnv, scope))
			}
			v.proveEntityValue(arm.Value, armEnv, scope)
		}
		return
	}
	path, isPath := mutArgPath(e)
	label := path
	if !isPath {
		// A value with no name: work it out as an assignment would.
		path, label = entityProbe, "value"
		probe := env.clone()
		v.effectsDone = true
		v.assignSymbolic(path, e, probe, scope, e.GetSpan())
		env = probe
	}
	v.proveInvariants(et, path, label, e.GetSpan(), env, scope, map[*sema.EntityType]bool{})
}

// proveInvariants proves the invariants of the entity bound under path, and
// of the entities in its fields.
func (v *verifier) proveInvariants(et *sema.EntityType, path, label string, span ast.Span, env *symEnv, scope string, seen map[*sema.EntityType]bool) {
	if seen[et] {
		return
	}
	seen[et] = true
	for i, inv := range et.Invariants {
		v.prove(fmt.Sprintf("%s.entity_%s_invariant_%d", scope, label, i+1), scope, span, env,
			v.evalBoolWithPrefix(inv, env, path+"."))
	}
	for _, f := range et.Fields {
		if ft, ok := f.Type.(*sema.EntityType); ok {
			v.proveInvariants(ft, path+"."+f.Name, label+"."+f.Name, span, env, scope, seen)
		}
	}
	delete(seen, et)
}

// isVariantConstructor reports whether call builds a value of a variant type.
func (v *verifier) isVariantConstructor(call *ast.CallExpr) bool {
	id, ok := call.Callee.(*ast.Ident)
	if !ok {
		return false
	}
	switch id.Name {
	case "Ok", "Err", "Some":
		return true
	}
	return v.info.Variants[id.Name] != nil
}

// copyEntityFacts gives the entity under to what is known of the one under from.
func (e *symEnv) copyEntityFacts(from, to string) {
	under := func(k string) (string, bool) {
		if strings.HasPrefix(k, from+".") {
			return to + k[len(from):], true
		}
		return "", false
	}
	for k, t := range e.intTerms {
		if nk, ok := under(k); ok {
			e.intTerms[nk] = t
		}
	}
	for k, b := range e.boolTerms {
		if nk, ok := under(k); ok {
			e.boolTerms[nk] = b
		}
	}
	for k, t := range e.listLens {
		if nk, ok := under(k); ok {
			e.listLens[nk] = t
		}
	}
	for k, iv := range e.listElems {
		if nk, ok := under(k); ok {
			e.listElems[nk] = iv
		}
	}
	for k, si := range e.sumInfos {
		if nk, ok := under(k); ok {
			e.sumInfos[nk] = si
		}
	}
}

// An entity that can be reached in two ways (two names, or a name and the
// list, map, variant or entity it sits in) is seen through the other way
// while a field of it is being written. Such an entity has no private
// moment between two updates: every write has to leave its invariants true.

// pathRoot is the variable a field path starts from.
func pathRoot(path string) string {
	if i := strings.IndexByte(path, '.'); i >= 0 {
		return path[:i]
	}
	return path
}

// sharingOf lists the variables that node, on its own, makes shared, and
// whether it gives the variable `fresh` a value nothing else can reach.
// After it, two variables that can reach one entity are both shared.
func (v *verifier) sharingOf(node any) (names []string, fresh string) {
	root := func(e ast.Expr) {
		if r := mutRoot(e); r != nil {
			names = append(names, r.Name)
		}
	}
	// stored: the value of e stays reachable from somewhere else.
	stored := func(e ast.Expr) bool {
		if !mayHoldEntity(v.info.ExprTypes[e]) {
			return false
		}
		roots := v.valueRoots(e)
		names = append(names, roots...)
		return len(roots) > 0
	}
	bindsVar := func(pats ...ast.Pattern) bool {
		found := false
		for _, p := range pats {
			visitNodes(reflect.ValueOf(p), func(n any) {
				if _, ok := n.(*ast.VarPat); ok {
					found = true
				}
			})
		}
		return found
	}
	switch x := node.(type) {
	case *ast.ForStmt:
		if _, isRange := x.Iterable.(*ast.RangeExpr); !isRange {
			names = append(names, x.Var)
			root(x.Iterable)
		}
	case *ast.VarPat:
		names = append(names, x.Name)
	case *ast.MatchStmt:
		for _, arm := range x.Arms {
			if bindsVar(arm.Pattern) {
				root(x.Subject)
			}
		}
	case *ast.MatchExpr:
		for _, arm := range x.Arms {
			if bindsVar(arm.Pattern) {
				root(x.Subject)
			}
		}
	case *ast.LetAssignStmt:
		if isScalar(v.info.ExprTypes[x.Value]) {
			// A number read out of an entity is not a way to reach it.
			// A value of any other type may be one, an element of an
			// untyped map for instance.
			return nil, x.Name
		}
		src := x.Value
		for {
			t, ok := src.(*ast.TryExpr)
			if !ok {
				break
			}
			src = t.Inner
		}
		if roots := v.valueRoots(src); len(roots) > 0 {
			// A second name, or a name for something inside another value.
			names = append(append(names, x.Name), roots...)
		} else if v.isFreshValue(src) && len(v.sharedIn(x.Value)) == 0 {
			fresh = x.Name
		} else {
			// What a call hands back may be one of its arguments, and a
			// new value may hold a variable's entity.
			names = append(names, x.Name)
		}
	case *ast.IndexAssignStmt:
		if stored(x.Value) {
			root(x.List)
		}
	case *ast.FieldAssignStmt:
		if stored(x.Value) {
			root(x.Object)
		}
	case *ast.ListLit:
		for _, el := range x.Elems {
			stored(el)
		}
	case *ast.MapLit:
		for _, en := range x.Entries {
			stored(en.Value)
		}
	case *ast.CallExpr:
		keeps := false
		switch c := x.Callee.(type) {
		case *ast.Ident:
			if fi := v.info.Funcs[c.Name]; fi != nil {
				for _, a := range x.Args {
					if v.mayKeepArgument(fi.Type.Params, fi.Type.Return, v.info.ExprTypes[a.Value]) {
						stored(a.Value)
					}
				}
			} else {
				keeps = v.info.Entities[c.Name] != nil || v.isVariantConstructor(x)
			}
		default:
			// A method: a channel keeps what is sent, a pool what is submitted.
			keeps = true
		}
		if keeps {
			for _, a := range x.Args {
				stored(a.Value)
			}
		}
	case *ast.RunWorkflowExpr:
		if wi := v.info.Workflows[x.Name]; wi != nil {
			for _, a := range x.Args {
				if v.mayKeepArgument(wi.Params, wi.Return, v.info.ExprTypes[a.Value]) {
					stored(a.Value)
				}
			}
		}
	case *ast.PipeExpr:
		if c := v.pipedCall(x); c != nil {
			return v.sharingOf(c)
		}
	}
	return names, fresh
}

// valueRoots lists the variables whose value, or something inside it, e may
// evaluate to: a path, an arm of a match, the base of a `with` copy that
// shares what the original holds.
func (v *verifier) valueRoots(e ast.Expr) []string {
	if r := mutRoot(e); r != nil {
		return []string{r.Name}
	}
	switch x := e.(type) {
	case *ast.TryExpr:
		return v.valueRoots(x.Inner)
	case *ast.WithExpr:
		if !v.isFlatEntity(v.info.ExprTypes[x.Base]) {
			return v.valueRoots(x.Base)
		}
	case *ast.MatchExpr:
		var out []string
		for _, arm := range x.Arms {
			out = append(out, v.valueRoots(arm.Value)...)
		}
		return out
	}
	return nil
}

// mayHoldEntity reports whether a value of type t is, or contains, something
// held by reference: an entity, a list or a map. A type that is not known
// is taken to.
func mayHoldEntity(t sema.Type) bool {
	return mayHoldEntityIn(t, 0)
}

func mayHoldEntityIn(t sema.Type, depth int) bool {
	if depth > 8 {
		return true
	}
	switch x := t.(type) {
	case *sema.IntType, sema.BoolType, sema.StrType, *sema.HandleType, *sema.FuncType:
		return false
	case *sema.ListType, *sema.MapType:
		// References themselves: an element written, or a key inserted,
		// through one name is seen through every other.
		return true
	case *sema.ADTType:
		for _, a := range x.TypeArgs {
			if mayHoldEntityIn(a, depth+1) {
				return true
			}
		}
		for _, vi := range x.Variants {
			for _, f := range vi.Fields {
				if _, isVar := f.Type.(sema.TypeVar); !isVar && mayHoldEntityIn(f.Type, depth+1) {
					return true
				}
			}
		}
		return false
	}
	return true
}

// mayKeepArgument reports whether a function with these parameters and
// result can leave an argument of type arg reachable after it returns:
// inside a mut argument that has room for a reference, through a handle (a
// channel, a pool), or as, or inside, its result.
func (v *verifier) mayKeepArgument(params []sema.FuncParamInfo, ret sema.Type, arg sema.Type) bool {
	if v.resultMayBe(ret, arg) {
		return true
	}
	for _, p := range params {
		if p.Mut && v.hasRoom(p.Type) {
			return true
		}
		switch p.Type.(type) {
		case *sema.HandleType, *sema.FuncType:
			return true
		}
	}
	return false
}

// resultMayBe reports whether a result of type ret can be a value of type
// arg, hold one, or come out of one: a list of numbers is not a flat
// entity, holds none and is not inside one.
func (v *verifier) resultMayBe(ret, arg sema.Type) bool {
	if ret == nil || !mayHoldEntity(ret) || !mayHoldEntity(arg) {
		return false
	}
	// The result holds the argument, or was taken out of it.
	if v.hasRoom(ret) || v.hasRoom(arg) {
		return true
	}
	switch ret.(type) {
	case *sema.ListType:
		_, same := arg.(*sema.ListType)
		return same
	case *sema.MapType:
		_, same := arg.(*sema.MapType)
		return same
	case *sema.EntityType:
		return ret.Equals(arg)
	}
	return true
}

// hasRoom reports whether a value of type t has a place to put a reference
// to another value: a list or map of numbers, or a flat entity, has none.
func (v *verifier) hasRoom(t sema.Type) bool {
	switch x := t.(type) {
	case *sema.ListType:
		return mayHoldEntity(x.Elem)
	case *sema.MapType:
		return mayHoldEntity(x.Val)
	case *sema.EntityType:
		return !v.isFlatEntity(x)
	}
	return mayHoldEntity(t)
}

// isFreshValue reports whether e evaluates to a value nothing else can
// reach: a literal, a new entity, or the result of a call that was given
// nothing it could hand back.
func (v *verifier) isFreshValue(e ast.Expr) bool {
	// No argument can be, or be inside, a result of type ret.
	keepsNone := func(ret sema.Type, args []ast.CallArg) bool {
		for _, a := range args {
			if ret == nil || v.resultMayBe(ret, v.info.ExprTypes[a.Value]) {
				return false
			}
		}
		return true
	}
	switch x := e.(type) {
	case *ast.ListLit, *ast.MapLit, *ast.LambdaExpr:
		return true
	case *ast.WithExpr:
		return v.isFlatEntity(v.info.ExprTypes[x.Base])
	case *ast.TryExpr:
		return v.isFreshValue(x.Inner)
	case *ast.MatchExpr:
		for _, arm := range x.Arms {
			if !v.isFreshValue(arm.Value) {
				return false
			}
		}
		return true
	case *ast.RunWorkflowExpr:
		return keepsNone(v.info.ExprTypes[x], x.Args)
	case *ast.PipeExpr:
		if c := v.pipedCall(x); c != nil {
			return keepsNone(v.info.ExprTypes[x], c.Args)
		}
	case *ast.CallExpr:
		id, ok := x.Callee.(*ast.Ident)
		if !ok {
			return false
		}
		if v.info.Entities[id.Name] != nil || v.isVariantConstructor(x) {
			return true
		}
		return keepsNone(v.info.ExprTypes[x], x.Args)
	}
	return false
}

// sharedIn lists the variables that the code under node can make shared.
func (v *verifier) sharedIn(node any) []string {
	var out []string
	visitNodesUntil(reflect.ValueOf(node), func(n any) bool {
		if lam, ok := n.(*ast.LambdaExpr); ok {
			// A lambda's parameter is not the outer variable of that name.
			inner := v.sharedIn(lam.Body)
			// What the lambda yields ends up where its caller puts it.
			if _, ok := v.info.ExprTypes[lam.Body].(*sema.EntityType); ok {
				if p, ok := mutArgPath(lam.Body); ok {
					inner = append(inner, pathRoot(p))
				}
			}
			for _, name := range inner {
				if !slices.Contains(lam.Params, name) {
					out = append(out, name)
				}
			}
			return false
		}
		names, _ := v.sharingOf(n)
		out = append(out, names...)
		return true
	})
	return out
}

// noteShared records what stmt itself, not the statements inside it, shares.
func (v *verifier) noteShared(stmt ast.Stmt, groups [][]ast.Expr, env *symEnv) {
	names, fresh := v.sharingOf(stmt)
	if fresh != "" {
		delete(env.shared, fresh)
	}
	for _, g := range groups {
		names = append(names, v.sharedIn(g)...)
	}
	if m, ok := stmt.(*ast.MatchStmt); ok {
		for _, arm := range m.Arms {
			names = append(names, v.sharedIn(arm.Pattern)...)
		}
	}
	for _, name := range names {
		env.shared[name] = true
	}
}

// proveSharedEntity is called after a field of obj was written: when obj
// belongs to a shared variable, that variable's invariants must hold now.
func (v *verifier) proveSharedEntity(obj ast.Expr, env *symEnv, scope string, span ast.Span) {
	root := obj
	for {
		fe, ok := root.(*ast.FieldExpr)
		if !ok {
			break
		}
		root = fe.Object
	}
	id, ok := root.(*ast.Ident)
	if !ok || !env.shared[id.Name] {
		return
	}
	if et, ok := v.info.ExprTypes[id].(*sema.EntityType); ok && hasInvariants(et, nil) {
		v.proveInvariants(et, id.Name, id.Name, span, env, scope, map[*sema.EntityType]bool{})
	}
}

// checkWrittenObject rejects a field write on an object whose entity type
// is not known (an element of an untyped map): which invariants the write
// has to keep cannot be told.
func (v *verifier) checkWrittenObject(obj ast.Expr, field string, scope string, span ast.Span) {
	if _, ok := v.info.ExprTypes[obj].(*sema.EntityType); ok {
		return
	}
	v.record(fmt.Sprintf("%s.field_%s_object_type", scope, field), scope, span, "the written object has a known entity type", VCFailed,
		fmt.Sprintf("the type of the object whose field %s is written is not known, so its invariants cannot be checked; give the map or variable it comes from a type", field), nil)
}

// proveElementWrite is called for a field write on an object that has no
// name (rows[i].x = v, rows[i].x += v). The object stays inside its
// container, so its invariants must hold again right away. They held before
// the write, as they do for everything a container holds; of the object's
// other fields nothing else is known.
// value is the expression written, nil for a compound assignment, whose
// result is term.
func (v *verifier) proveElementWrite(obj ast.Expr, field string, value ast.Expr, term smt.LinearTerm, env *symEnv, scope string, span ast.Span) {
	et, ok := v.info.ExprTypes[obj].(*sema.EntityType)
	if !ok || !hasInvariants(et, nil) {
		return
	}
	probe := env.clone()
	saved := v.noInvariants
	v.noInvariants = false
	v.bindFresh(probe, entityProbe, et)
	v.noInvariants = saved
	// The written field is what the write makes it; what it was, and what
	// was inside it, is gone.
	path := entityProbe + "." + field
	if value != nil {
		// As for a field of a variable: an entity or a list is assigned
		// with what is known of it, a boolean is evaluated.
		v.setField(path, value, term, probe, scope, span)
	} else {
		probe.unbind(path)
		probe.intTerms[path] = term
	}
	v.proveInvariants(et, entityProbe, "element", span, probe, scope, map[*sema.EntityType]bool{})
}

// proveMutInvariants proves, where the function gives its mut entities back
// to its caller, their invariants and those of the entities in their
// fields: the caller assumes all of them.
func (v *verifier) proveMutInvariants(env *symEnv, scope string, span ast.Span) {
	var walk func(et *sema.EntityType, path string, seen map[*sema.EntityType]bool)
	walk = func(et *sema.EntityType, path string, seen map[*sema.EntityType]bool) {
		if seen[et] {
			return
		}
		seen[et] = true
		for _, inv := range et.Invariants {
			v.prove(fmt.Sprintf("%s.mut_%s_invariant", v.curFuncName, path), scope, span, env,
				v.evalBoolWithPrefix(inv, env, path+"."))
		}
		for _, f := range et.Fields {
			if ft, ok := f.Type.(*sema.EntityType); ok {
				walk(ft, path+"."+f.Name, seen)
			}
		}
		delete(seen, et)
	}
	for _, me := range v.curMutEnts {
		walk(me.ent, me.varName, map[*sema.EntityType]bool{})
	}
}
