package sema

import (
	"fmt"
	"reflect"
	"sort"

	"github.com/xiongnemo/anima/internal/ast"
)

// The branches of a fork run at the same time: on the VM each on its own
// copy of the variables, natively as threads on the variables themselves.
// What a branch reads of something another branch writes is therefore not
// one thing. So a branch only assigns variables, which no other branch
// names; it writes nothing in place (a field, an element, a mut argument),
// because the entity or list written may be reached by a name that another
// branch reads, and what is known of it would have to be dropped at every
// read. Handles (channels, mutexes) are what branches share.

// branchVars is what the statements of one fork branch do with variables:
// the ones they write and the ones they name at all.
type branchVars struct {
	writes, uses map[string]bool
	returns      *ast.ReturnStmt
	// inPlace is the first variable written in place, "" when there is none.
	inPlace     string
	inPlaceSpan ast.Span
}

func newBranchVars() *branchVars {
	return &branchVars{writes: map[string]bool{}, uses: map[string]bool{}}
}

// rootIdent is the variable an assignment target or a mut argument reaches:
// box for box.rows[i].
func rootIdent(e ast.Expr) string {
	for {
		switch x := e.(type) {
		case *ast.Ident:
			return x.Name
		case *ast.FieldExpr:
			e = x.Object
		case *ast.IndexExpr:
			e = x.List
		default:
			return ""
		}
	}
}

func (b *branchVars) write(name string) {
	if name != "" {
		b.writes[name] = true
		b.uses[name] = true
	}
}

// writeInPlace records a write to a field or an element of what target
// reaches, or its use as a mut argument.
func (b *branchVars) writeInPlace(target ast.Expr, span ast.Span) {
	if b.inPlace == "" {
		b.inPlace, b.inPlaceSpan = rootIdent(target), span
		if b.inPlace == "" {
			b.inPlace = "a value"
		}
	}
}

var callArgType = reflect.TypeOf(ast.CallArg{})

// visit records what the code under n does. A variable is written by an
// assignment to it and by a loop or a pattern that binds it.
func (b *branchVars) visit(n reflect.Value) {
	switch n.Kind() {
	case reflect.Interface:
		if !n.IsNil() {
			b.visit(n.Elem())
		}
	case reflect.Pointer:
		if n.IsNil() {
			return
		}
		if n.Elem().Kind() == reflect.Struct && n.CanInterface() {
			switch x := n.Interface().(type) {
			case *ast.Ident:
				b.uses[x.Name] = true
			case *ast.LetAssignStmt:
				b.write(x.Name)
			case *ast.CompoundAssignStmt:
				if id, ok := x.Target.(*ast.Ident); ok {
					b.write(id.Name)
				} else {
					b.writeInPlace(x.Target, x.Span)
				}
			case *ast.FieldAssignStmt:
				b.writeInPlace(x.Object, x.Span)
			case *ast.IndexAssignStmt:
				b.writeInPlace(x.List, x.Span)
			case *ast.ForStmt:
				b.write(x.Var)
			case *ast.VarPat:
				b.write(x.Name)
			case *ast.ReturnStmt:
				if b.returns == nil {
					b.returns = x
				}
			case *ast.LambdaExpr:
				// A parameter of a lambda is not the variable of that name.
				inner := newBranchVars()
				inner.visit(reflect.ValueOf(x.Body))
				for _, p := range x.Params {
					delete(inner.writes, p)
					delete(inner.uses, p)
				}
				for name := range inner.writes {
					b.writes[name] = true
				}
				for name := range inner.uses {
					b.uses[name] = true
				}
				if b.inPlace == "" {
					b.inPlace, b.inPlaceSpan = inner.inPlace, inner.inPlaceSpan
				}
				return
			}
		}
		b.visit(n.Elem())
	case reflect.Slice:
		for i := 0; i < n.Len(); i++ {
			b.visit(n.Index(i))
		}
	case reflect.Struct:
		if n.Type() == callArgType {
			if arg := n.Interface().(ast.CallArg); arg.Mut {
				b.writeInPlace(arg.Value, arg.Span)
			}
		}
		for i := 0; i < n.NumField(); i++ {
			b.visit(n.Field(i))
		}
	}
}

// checkForkBranches refuses a fork whose branches do not run the same in
// every order: one that returns, one that writes in place, and one that
// names a variable another assigns.
func checkForkBranches(fk *ast.ForkNode) error {
	vars := make([]*branchVars, len(fk.Branches))
	for i, br := range fk.Branches {
		vars[i] = newBranchVars()
		for _, op := range br.Ops {
			if op.Kind == ast.BranchStmt && op.Stmt != nil {
				vars[i].visit(reflect.ValueOf(op.Stmt))
			}
		}
		if ret := vars[i].returns; ret != nil {
			return fmt.Errorf("%s: return in branch %q of fork %s: the workflow returns from a step, after the join", ret.Span, br.Name, fk.Name)
		}
		if name := vars[i].inPlace; name != "" {
			return fmt.Errorf("%s: branch %q of fork %s writes %s in place: a branch only assigns variables, as another branch may reach what is written; write it in a step, or assign what a function returns", vars[i].inPlaceSpan, br.Name, fk.Name, name)
		}
	}
	for i, br := range fk.Branches {
		names := make([]string, 0, len(vars[i].writes))
		for name := range vars[i].writes {
			names = append(names, name)
		}
		sort.Strings(names)
		for _, name := range names {
			for j, other := range fk.Branches {
				if j == i {
					continue
				}
				if vars[j].writes[name] {
					if j < i {
						continue // reported from the earlier branch
					}
					return fmt.Errorf("%s: concurrent write race on variable %q in fork branches %q and %q", other.Span, name, br.Name, other.Name)
				}
				if vars[j].uses[name] {
					return fmt.Errorf("%s: branch %q of fork %s uses %q, which branch %q assigns: the branches run at the same time", other.Span, other.Name, fk.Name, name, br.Name)
				}
			}
		}
	}
	return nil
}
