package sema

import (
	"fmt"

	"github.com/xiongnemo/anima/internal/ast"
)

// A machine, a monitor and a property are not run by a backend. The LTS
// kernel works out the guards, invariants and assignments of a machine over
// the values of its control variables, and what it does not work out it
// would have to give a value the program does not have. So a model is
// written only with what the kernel works out, and the rest is refused here.

// MaxControlSpan is the most hi-lo of a control variable int[lo..hi]: the
// model holds a state for each value.
const MaxControlSpan = 32

// ControlRange is the range of the type of a control variable, if it is an
// int of a range of at most MaxControlSpan+1 values.
func ControlRange(cv ast.ControlVarDecl, types map[string]Type) (lo, hi int64, err error) {
	bounded := false
	switch t := cv.Type.(type) {
	case *ast.IntRangeType:
		lo, hi, bounded = t.Lo, t.Hi, true
	case *ast.SimpleType:
		if it, ok := types[t.Name].(*IntType); ok && it.IsBounded {
			lo, hi, bounded = it.Lo, it.Hi, true
		}
	}
	// hi-lo may be more than an int64 holds.
	if !bounded || lo > hi || uint64(hi)-uint64(lo) > MaxControlSpan {
		return 0, 0, fmt.Errorf("%s: control variable %s has type %s: a control variable is an int of a range, int[lo..hi], of at most %d values, since the model holds a state for each value", cv.Span, cv.Name, cv.Type, MaxControlSpan+1)
	}
	return lo, hi, nil
}

const modelForms = "a model is written with int literals, control variables, the operators of ints, abs, min, max, comparisons, and not, and, or, implies"

func notModelled(e ast.Expr, what string) error {
	return fmt.Errorf("%s: %s is not worked out in a model: %s", e.GetSpan(), what, modelForms)
}

// modelBoolForm reports whether e is a bool by its form. A model has no bool
// variable, so every bool is one of these.
func modelBoolForm(e ast.Expr) bool {
	switch x := e.(type) {
	case *ast.BoolLit:
		return true
	case *ast.UnaryExpr:
		return x.Op == "not"
	case *ast.BinaryExpr:
		switch x.Op {
		case "and", "or", "implies", "==", "!=", "<", "<=", ">", ">=":
			return true
		}
	}
	return false
}

// modelInt is an error unless the LTS kernel works out the int e over the
// control variables vars.
func modelInt(e ast.Expr, vars map[string]bool) error {
	switch x := e.(type) {
	case *ast.IntLit:
		return nil
	case *ast.Ident:
		if !vars[x.Name] {
			return notModelled(e, x.Name+", which is no control variable written before it,")
		}
		return nil
	case *ast.UnaryExpr:
		if x.Op == "-" || x.Op == "~" {
			return modelInt(x.Expr, vars)
		}
	case *ast.CallExpr:
		id, ok := x.Callee.(*ast.Ident)
		if !ok || vars[id.Name] || (id.Name != "abs" && id.Name != "min" && id.Name != "max") {
			return notModelled(e, "a call other than abs, min and max")
		}
		for _, a := range x.Args {
			if a.Name != "" || a.Mut || a.Own {
				return notModelled(e, "a named, mut or own argument")
			}
			if err := modelInt(a.Value, vars); err != nil {
				return err
			}
		}
		return nil
	case *ast.BinaryExpr:
		switch x.Op {
		case "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>":
			if err := modelInt(x.Left, vars); err != nil {
				return err
			}
			return modelInt(x.Right, vars)
		}
	}
	if modelBoolForm(e) {
		return notModelled(e, "a bool where an int is")
	}
	return notModelled(e, "this")
}

// modelBool is modelInt of a bool.
func modelBool(e ast.Expr, vars map[string]bool) error {
	switch x := e.(type) {
	case *ast.BoolLit:
		return nil
	case *ast.UnaryExpr:
		if x.Op == "not" {
			return modelBool(x.Expr, vars)
		}
	case *ast.BinaryExpr:
		operands := modelInt
		switch x.Op {
		case "and", "or", "implies":
			operands = modelBool
		case "==", "!=":
			if modelBoolForm(x.Left) || modelBoolForm(x.Right) {
				operands = modelBool
			}
		case "<", "<=", ">", ">=":
		case "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>":
			return notModelled(e, "an int where a bool is")
		default:
			return notModelled(e, "the operator "+x.Op)
		}
		if err := operands(x.Left, vars); err != nil {
			return err
		}
		return operands(x.Right, vars)
	}
	return notModelled(e, "this, where a bool is,")
}

// modelStmt is an error unless s is an assignment to a control variable or
// an if of such.
func modelStmt(s ast.Stmt, vars map[string]bool) error {
	const only = "a transition holds assignments to control variables and ifs, and nothing else is in the model"
	switch x := s.(type) {
	case *ast.LetAssignStmt:
		if x.TypeAnno != nil {
			return fmt.Errorf("%s: a transition declares no variable: %s", x.Span, only)
		}
		if !vars[x.Name] {
			return fmt.Errorf("%s: %s is no control variable: %s", x.Span, x.Name, only)
		}
		return modelInt(x.Value, vars)
	case *ast.CompoundAssignStmt:
		id, ok := x.Target.(*ast.Ident)
		if !ok || !vars[id.Name] {
			return fmt.Errorf("%s: this assigns to no control variable: %s", x.Span, only)
		}
		return modelInt(x.Value, vars)
	case *ast.IfStmt:
		for _, br := range x.Branches {
			if err := modelBool(br.Cond, vars); err != nil {
				return err
			}
			for _, bs := range br.Body {
				if err := modelStmt(bs, vars); err != nil {
					return err
				}
			}
		}
		for _, es := range x.Else {
			if err := modelStmt(es, vars); err != nil {
				return err
			}
		}
		return nil
	}
	return fmt.Errorf("%s: %s", s.GetSpan(), only)
}

// checkModels refuses what the LTS kernel does not work out of a machine,
// a monitor, a property and a system. It is run after callAllPiped, so that
// `n |> abs()` is the call the kernel is given.
func (c *checker) checkModels() error {
	for _, d := range c.info.Program.Decls {
		var err error
		switch node := d.(type) {
		case *ast.MachineDecl:
			err = c.checkMachineModel(node)
		case *ast.PropertyDecl:
			err = checkPropertyModel(node)
		case *ast.SystemDecl:
			err = c.checkSystemModel(node)
		}
		if err != nil {
			return err
		}
	}
	return nil
}

func (c *checker) checkMachineModel(m *ast.MachineDecl) error {
	vars := map[string]bool{}
	for _, cv := range m.ControlVars {
		if _, _, err := ControlRange(cv, c.info.Types); err != nil {
			return err
		}
		// A first value is worked out with the variables before it.
		if cv.Init != nil {
			if err := modelInt(cv.Init, vars); err != nil {
				return err
			}
		}
		vars[cv.Name] = true
	}
	for _, st := range m.States {
		for _, inv := range st.Invariants {
			if err := modelBool(inv, vars); err != nil {
				return err
			}
		}
		for _, tr := range st.Transitions {
			if tr.Guard != nil {
				if err := modelBool(tr.Guard, vars); err != nil {
					return err
				}
			}
			for _, bs := range tr.Body {
				if err := modelStmt(bs, vars); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

// checkPropertyModel: a property is the actions it allows in each state and
// nothing else. A guard, an invariant and a body were read and dropped, so
// `on a when False -> P` allowed a; of two transitions of one state on one
// action the last was kept; a target that is no state was ERROR.
func checkPropertyModel(p *ast.PropertyDecl) error {
	states := map[string]bool{}
	for _, st := range p.States {
		states[st.Name] = true
	}
	for _, st := range p.States {
		if len(st.Invariants) > 0 {
			return fmt.Errorf("%s: state %s of property %s has an invariant: a property has no variables, and says only which actions each state allows", st.Invariants[0].GetSpan(), st.Name, p.Name)
		}
		seen := map[string]bool{}
		for _, tr := range st.Transitions {
			if tr.Guard != nil || len(tr.Body) > 0 {
				return fmt.Errorf("%s: transition %s of property %s has a guard or a body: a property has no variables, and says only which actions each state allows", tr.Span, tr.Action, p.Name)
			}
			if tr.TargetState != "ERROR" && !states[tr.TargetState] {
				return fmt.Errorf("%s: transition %s targets unknown state %q in property %s", tr.Span, tr.Action, tr.TargetState, p.Name)
			}
			if seen[tr.Action] {
				return fmt.Errorf("%s: state %s of property %s has two transitions on %s: a property goes one way on an action", tr.Span, st.Name, p.Name, tr.Action)
			}
			seen[tr.Action] = true
		}
	}
	return nil
}

// checkSystemModel: an instance gives another name only to an action its
// machine has. `y: B / {zzz -> a}` of a B with no zzz put a in the alphabet
// of y, and no other part of the system could then do a.
func (c *checker) checkSystemModel(sys *ast.SystemDecl) error {
	for _, inst := range sys.Instances {
		m, ok := c.info.Machines[inst.TypeName]
		if !ok || len(inst.Relabels) == 0 {
			continue
		}
		actions := map[string]bool{}
		for _, st := range m.States {
			for _, tr := range st.Transitions {
				actions[tr.Action] = true
			}
		}
		from := map[string]bool{}
		for _, r := range inst.Relabels {
			if !actions[r.From] {
				return fmt.Errorf("%s: instance %s of system %s relabels %s, which is no action of %s", r.Span, inst.Name, sys.Name, r.From, inst.TypeName)
			}
			if from[r.From] {
				return fmt.Errorf("%s: instance %s of system %s relabels %s twice", r.Span, inst.Name, sys.Name, r.From)
			}
			from[r.From] = true
		}
	}
	return nil
}
