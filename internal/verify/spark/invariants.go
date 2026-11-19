package spark

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
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
	for k, t := range e.intTerms {
		if len(k) > len(from) && k[:len(from)+1] == from+"." {
			e.intTerms[to+k[len(from):]] = t
		}
	}
	for k, b := range e.boolTerms {
		if len(k) > len(from) && k[:len(from)+1] == from+"." {
			e.boolTerms[to+k[len(from):]] = b
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
// whether it gives the variable `fresh` an entity nothing else can reach.
func (v *verifier) sharingOf(node any) (names []string, fresh string) {
	stored := func(e ast.Expr) {
		if _, ok := v.info.ExprTypes[e].(*sema.EntityType); !ok {
			return
		}
		if p, ok := mutArgPath(e); ok {
			names = append(names, pathRoot(p))
		}
	}
	switch x := node.(type) {
	case *ast.ForStmt:
		if _, isRange := x.Iterable.(*ast.RangeExpr); !isRange {
			names = append(names, x.Var)
		}
	case *ast.VarPat:
		names = append(names, x.Name)
	case *ast.LetAssignStmt:
		if _, ok := v.info.ExprTypes[x.Value].(*sema.EntityType); !ok {
			// A number read out of an entity is not a way to reach it.
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
		if _, ok := src.(*ast.IndexExpr); ok {
			names = append(names, x.Name)
		} else if p, ok := mutArgPath(src); ok {
			names = append(names, x.Name, pathRoot(p))
		} else {
			fresh = x.Name
		}
	case *ast.IndexAssignStmt:
		stored(x.Value)
	case *ast.FieldAssignStmt:
		stored(x.Value)
	case *ast.ListLit:
		for _, el := range x.Elems {
			stored(el)
		}
	case *ast.MapLit:
		for _, en := range x.Entries {
			stored(en.Value)
		}
	case *ast.CallExpr:
		if id, ok := x.Callee.(*ast.Ident); ok && (v.info.Entities[id.Name] != nil || v.isVariantConstructor(x)) {
			for _, a := range x.Args {
				stored(a.Value)
			}
		}
	}
	return names, fresh
}

// sharedIn lists the variables that the code under node can make shared.
func (v *verifier) sharedIn(node any) []string {
	var out []string
	visitNodes(reflect.ValueOf(node), func(n any) {
		names, _ := v.sharingOf(n)
		out = append(out, names...)
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
