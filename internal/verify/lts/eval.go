package lts

import (
	"fmt"
	"math"
	"math/bits"

	"github.com/xiongnemo/anima/internal/ast"
)

// A machine is not run by a backend: its guards, invariants and assignments
// are worked out here, over the values of its control variables. Nothing is
// given a value it does not have: what is outside the forms below, or has no
// value (a division by zero, a result outside 64 bits), is an error and not
// 0 or false. sema refuses the same forms (checkModels), so an error here is
// of a program that was not checked.

func notModelled(e ast.Expr, what string) error {
	return fmt.Errorf("%s: %s is not worked out in a model", e.GetSpan(), what)
}

func noValue(e ast.Expr, why string) error {
	return fmt.Errorf("%s: %s in a model", e.GetSpan(), why)
}

// isBoolForm reports whether e is a bool by its form. A model has no bool
// variable, so every bool is one of these.
func isBoolForm(e ast.Expr) bool {
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

func evalInt(expr ast.Expr, env map[string]int64) (int64, error) {
	switch e := expr.(type) {
	case *ast.IntLit:
		return e.Value, nil
	case *ast.Ident:
		v, ok := env[e.Name]
		if !ok {
			return 0, notModelled(e, e.Name+", which is no control variable,")
		}
		return v, nil
	case *ast.UnaryExpr:
		x, err := evalInt(e.Expr, env)
		if err != nil {
			return 0, err
		}
		switch e.Op {
		case "-":
			if x == math.MinInt64 {
				return 0, noValue(e, "the negation of the least int overflows")
			}
			return -x, nil
		case "~":
			return ^x, nil
		}
		return 0, notModelled(e, e.Op+" of an int")
	case *ast.CallExpr:
		id, ok := e.Callee.(*ast.Ident)
		if !ok || (id.Name != "abs" && id.Name != "min" && id.Name != "max") {
			return 0, notModelled(e, "a call other than abs, min and max")
		}
		if _, shadowed := env[id.Name]; shadowed {
			return 0, notModelled(e, "a call of the control variable "+id.Name)
		}
		var xs []int64
		for _, a := range e.Args {
			if a.Name != "" || a.Mut || a.Own {
				return 0, notModelled(e, "a named, mut or own argument")
			}
			x, err := evalInt(a.Value, env)
			if err != nil {
				return 0, err
			}
			xs = append(xs, x)
		}
		switch {
		case id.Name == "abs" && len(xs) == 1:
			if xs[0] == math.MinInt64 {
				return 0, noValue(e, "abs of the least int overflows")
			}
			if xs[0] < 0 {
				return -xs[0], nil
			}
			return xs[0], nil
		case id.Name == "min" && len(xs) == 2:
			return min(xs[0], xs[1]), nil
		case id.Name == "max" && len(xs) == 2:
			return max(xs[0], xs[1]), nil
		}
		return 0, notModelled(e, fmt.Sprintf("%s of %d arguments", id.Name, len(xs)))
	case *ast.BinaryExpr:
		if isBoolForm(e) {
			return 0, notModelled(e, "a bool where an int is")
		}
		l, err := evalInt(e.Left, env)
		if err != nil {
			return 0, err
		}
		r, err := evalInt(e.Right, env)
		if err != nil {
			return 0, err
		}
		overflow := noValue(e, e.Op+" overflows")
		switch e.Op {
		case "+":
			s := l + r
			if (s > l) != (r > 0) {
				return 0, overflow
			}
			return s, nil
		case "-":
			d := l - r
			if (d < l) != (r > 0) {
				return 0, overflow
			}
			return d, nil
		case "*":
			return mulInt(l, r, overflow)
		case "/", "%":
			if r == 0 {
				return 0, noValue(e, "a division by zero")
			}
			if l == math.MinInt64 && r == -1 {
				return 0, overflow
			}
			if e.Op == "/" {
				return l / r, nil
			}
			return l % r, nil
		case "&":
			return l & r, nil
		case "|":
			return l | r, nil
		case "^":
			return l ^ r, nil
		case "<<", ">>":
			if r < 0 || r > 63 {
				return 0, noValue(e, fmt.Sprintf("a shift by %d, which is outside 0..63,", r))
			}
			if e.Op == ">>" {
				return l >> uint(r), nil
			}
			if s := l << uint(r); s>>uint(r) == l {
				return s, nil
			}
			return 0, overflow
		}
		return 0, notModelled(e, e.Op)
	}
	return 0, notModelled(expr, "this")
}

func mulInt(l, r int64, overflow error) (int64, error) {
	if l == 0 || r == 0 {
		return 0, nil
	}
	neg := (l < 0) != (r < 0)
	abs := func(x int64) uint64 {
		if x < 0 {
			return uint64(-(x + 1)) + 1
		}
		return uint64(x)
	}
	hi, lo := bits.Mul64(abs(l), abs(r))
	switch {
	case hi != 0, !neg && lo > math.MaxInt64, neg && lo > 1<<63:
		return 0, overflow
	case neg:
		return int64(-lo), nil
	}
	return int64(lo), nil
}

func evalBool(expr ast.Expr, env map[string]int64) (bool, error) {
	switch e := expr.(type) {
	case *ast.BoolLit:
		return e.Value, nil
	case *ast.UnaryExpr:
		if e.Op == "not" {
			x, err := evalBool(e.Expr, env)
			return !x, err
		}
	case *ast.BinaryExpr:
		switch e.Op {
		case "and", "or", "implies":
			// The right operand is worked out only where it is run.
			l, err := evalBool(e.Left, env)
			if err != nil {
				return false, err
			}
			if e.Op == "implies" {
				l = !l
			}
			if l == (e.Op != "and") {
				return l, nil
			}
			return evalBool(e.Right, env)
		case "==", "!=":
			if isBoolForm(e.Left) || isBoolForm(e.Right) {
				l, err := evalBool(e.Left, env)
				if err != nil {
					return false, err
				}
				r, err := evalBool(e.Right, env)
				if err != nil {
					return false, err
				}
				return (l == r) == (e.Op == "=="), nil
			}
			fallthrough
		case "<", "<=", ">", ">=":
			l, err := evalInt(e.Left, env)
			if err != nil {
				return false, err
			}
			r, err := evalInt(e.Right, env)
			if err != nil {
				return false, err
			}
			switch e.Op {
			case "==":
				return l == r, nil
			case "!=":
				return l != r, nil
			case "<":
				return l < r, nil
			case "<=":
				return l <= r, nil
			case ">":
				return l > r, nil
			}
			return l >= r, nil
		}
	}
	return false, notModelled(expr, "this, where a bool is,")
}

// execStmt runs one statement of a transition on env.
func execStmt(stmt ast.Stmt, env map[string]int64) error {
	assign := func(span ast.Span, name string, e ast.Expr, op string) error {
		old, ok := env[name]
		if !ok {
			return fmt.Errorf("%s: %s is no control variable, and a transition assigns to nothing else", span, name)
		}
		v, err := evalInt(e, env)
		if err != nil {
			return err
		}
		if op != "" {
			lhs := &ast.IntLit{Span: span, Value: old}
			rhs := &ast.IntLit{Span: span, Value: v}
			if v, err = evalInt(&ast.BinaryExpr{Span: span, Op: op, Left: lhs, Right: rhs}, env); err != nil {
				return err
			}
		}
		env[name] = v
		return nil
	}
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		if s.TypeAnno != nil {
			return fmt.Errorf("%s: a transition declares no variable", s.Span)
		}
		return assign(s.Span, s.Name, s.Value, "")
	case *ast.CompoundAssignStmt:
		id, ok := s.Target.(*ast.Ident)
		if !ok || len(s.Op) != 2 {
			return fmt.Errorf("%s: a transition assigns to a control variable and to nothing else", s.Span)
		}
		return assign(s.Span, id.Name, s.Value, s.Op[:1])
	case *ast.IfStmt:
		body := s.Else
		for _, br := range s.Branches {
			c, err := evalBool(br.Cond, env)
			if err != nil {
				return err
			}
			if c {
				body = br.Body
				break
			}
		}
		for _, bs := range body {
			if err := execStmt(bs, env); err != nil {
				return err
			}
		}
		return nil
	}
	return fmt.Errorf("%s: a transition holds assignments to control variables and ifs, and this is neither", stmt.GetSpan())
}
