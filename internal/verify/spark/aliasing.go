package spark

import (
	"reflect"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
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
