package sema

import (
	"fmt"
	"reflect"
	"sort"

	"github.com/xiongnemo/anima/internal/ast"
)

// The variables of a workflow are bound by the assignments at the top of
// its start, its steps and its fork branches, and the types above are
// checked down the page. The workflow runs along its paths, though: a step
// may be reached by a way that never ran the assignment written above it,
// and the variable is then () on both backends. So a variable is read only
// where every path to the read has assigned it.

// wfAssigned follows the paths of a workflow with the variables assigned
// so far on each.
type wfAssigned struct {
	wf   *ast.WorkflowDecl
	flow *ast.Flow
	vars map[string]bool // the variables of the workflow
}

// checkWorkflowAssigned refuses a read of a workflow variable that some
// path to it has not assigned.
func checkWorkflowAssigned(wf *ast.WorkflowDecl) error {
	w := &wfAssigned{wf: wf, flow: ast.NewFlow(wf), vars: map[string]bool{}}
	if w.flow.Start == nil {
		return nil
	}
	bind := func(stmts []ast.Stmt) {
		for _, st := range stmts {
			if la, ok := st.(*ast.LetAssignStmt); ok {
				w.vars[la.Name] = true
			}
		}
	}
	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.StartNode:
			bind(x.Body)
		case *ast.StepNode:
			bind(x.Body)
		case *ast.ForkNode:
			for _, br := range x.Branches {
				bind(branchStmts(br))
			}
		}
	}
	bound := map[string]bool{}
	for _, p := range wf.Params {
		bound[p.Name] = true
	}
	if err := w.body(w.flow.Start.Body, bound, "the start"); err != nil {
		return err
	}
	if alwaysReturns(w.flow.Start.Body) {
		return nil
	}
	return w.walk(w.flow.Start.Target, bound, map[string]bool{})
}

func branchStmts(br ast.ForkBranch) []ast.Stmt {
	var out []ast.Stmt
	for _, op := range br.Ops {
		if op.Kind == ast.BranchStmt && op.Stmt != nil {
			out = append(out, op.Stmt)
		}
	}
	return out
}

func copyNames(m map[string]bool) map[string]bool {
	out := make(map[string]bool, len(m))
	for k := range m {
		out[k] = true
	}
	return out
}

// reads refuses what n names of the workflow's variables that is not in
// bound.
func (w *wfAssigned) reads(n any, span ast.Span, bound map[string]bool, where string) error {
	b := newBranchVars()
	b.visit(reflect.ValueOf(n))
	for _, name := range sortedNames(b.uses) {
		if w.vars[name] && !bound[name] {
			return fmt.Errorf("%s: %q is not assigned on every path to %s of workflow %s: assign it in the start, or on each path", span, name, where, w.wf.Name)
		}
	}
	return nil
}

// body runs the statements of a node in order: an assignment at the top
// binds its variable for what follows.
func (w *wfAssigned) body(stmts []ast.Stmt, bound map[string]bool, where string) error {
	for _, st := range stmts {
		if la, ok := st.(*ast.LetAssignStmt); ok {
			if err := w.reads(la.Value, la.Span, bound, where); err != nil {
				return err
			}
			bound[la.Name] = true
			continue
		}
		if err := w.reads(st, st.GetSpan(), bound, where); err != nil {
			return err
		}
	}
	return nil
}

func (w *wfAssigned) walk(cur string, bound map[string]bool, onPath map[string]bool) error {
	for {
		if w.flow.Ends(cur) || onPath[cur] {
			return nil
		}
		onPath[cur] = true
		choice := w.flow.Choice(cur)
		if st := w.flow.Step(cur); st != nil {
			if err := w.body(st.Body, bound, "step "+st.Name); err != nil {
				return err
			}
			if alwaysReturns(st.Body) {
				return nil
			}
			if cur, choice = w.flow.AfterStep(st); choice == nil {
				continue
			}
		}
		if choice != nil {
			return w.choice(choice, bound, onPath)
		}
		if fk := w.flow.Fork(cur); fk != nil {
			// Every branch runs, and none reads what another assigns
			// (checkForkBranches): what they bind is bound after the fork.
			after := copyNames(bound)
			for _, br := range fk.Branches {
				in := copyNames(bound)
				if err := w.body(branchStmts(br), in, "branch "+br.Name); err != nil {
					return err
				}
				for name := range in {
					after[name] = true
				}
			}
			bound, cur = after, w.flow.AfterFork()
			continue
		}
		if jn := w.flow.Join(cur); jn != nil {
			cur, choice = w.flow.AfterJoin(jn)
		} else {
			cur, choice = w.flow.AfterMerge(w.flow.Merge(cur))
		}
		if choice != nil {
			return w.choice(choice, bound, onPath)
		}
	}
}

// choice walks each branch of a choice with what is bound before it.
func (w *wfAssigned) choice(choice *ast.ChoiceNode, bound map[string]bool, onPath map[string]bool) error {
	for _, br := range choice.Branches {
		if br.Guard != nil {
			if err := w.reads(br.Guard, br.Span, bound, "this choice"); err != nil {
				return err
			}
		}
		if err := w.walk(br.Target, copyNames(bound), copyNames(onPath)); err != nil {
			return err
		}
	}
	return nil
}

func sortedNames(m map[string]bool) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}
