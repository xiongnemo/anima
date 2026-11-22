package tests

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/lts"
	"github.com/xiongnemo/anima/internal/verify/petri"
)

// The net and the LTS of a workflow are two readings of one flow. A step the
// net lets run is one the LTS does the action of, and when the net has no
// path that stops short of done, the steps and joins of the two are the same. The
// programs are those of the repository, and those of the directory
// ANIMA_WORKFLOW_CORPUS names.
func TestWorkflowNetAndLTSHoldTheSameSteps(t *testing.T) {
	files, _ := filepath.Glob("../examples/*.anm")
	bugs, _ := filepath.Glob("bugs/*.anm")
	files = append(files, bugs...)
	if dir := os.Getenv("ANIMA_WORKFLOW_CORPUS"); dir != "" {
		more, _ := filepath.Glob(filepath.Join(dir, "*.anm"))
		files = append(files, more...)
	}
	workflows := 0
	for _, file := range files {
		src, err := os.ReadFile(file)
		if err != nil {
			t.Fatal(err)
		}
		prog, err := parser.Parse(file, string(src))
		if err != nil {
			continue
		}
		info, err := sema.Check(prog)
		if err != nil {
			continue
		}
		byName := map[string]petri.WorkflowResult{}
		for _, wr := range petri.Verify(info).Workflows {
			byName[wr.Name] = wr
		}
		for _, d := range prog.Decls {
			wf, ok := d.(*ast.WorkflowDecl)
			if !ok {
				continue
			}
			wr := byName[wf.Name]
			if wr.Net == nil || !wr.Bounded {
				continue
			}
			workflows++
			dead := map[string]bool{}
			for _, name := range wr.Dead {
				dead[name] = true
			}
			model := lts.CompileWorkflowLTS(wf)
			done := map[string]bool{}
			seen := map[int]bool{model.Init: true}
			for todo := []int{model.Init}; len(todo) > 0; todo = todo[1:] {
				for _, e := range model.Edges[todo[0]] {
					done[e.Action] = true
					if !seen[e.Target] {
						seen[e.Target] = true
						todo = append(todo, e.Target)
					}
				}
			}
			inBranch := map[string]bool{}
			for _, n := range wf.Nodes {
				if fk, ok := n.(*ast.ForkNode); ok {
					for _, br := range fk.Branches {
						for _, op := range br.Ops {
							inBranch[op.Target] = true
						}
					}
				}
			}
			flow := ast.NewFlow(wf)
			whole := wr.OptionToComplete && wr.ProperCompletion
			same := func(what, name, trans, action string) {
				runs := !dead[trans]
				if runs && !done[action] {
					t.Errorf("%s: workflow %s: the net runs %s %s, the LTS never does %s", file, wf.Name, what, name, action)
				}
				if whole && !runs && done[action] {
					t.Errorf("%s: workflow %s: the LTS does %s, the net never runs %s %s", file, wf.Name, action, what, name)
				}
			}
			for _, n := range wf.Nodes {
				switch x := n.(type) {
				case *ast.StepNode:
					if flow.Step(x.Name) == x && !inBranch[x.Name] {
						same("step", x.Name, "t_"+x.Name, x.Name)
					}
				case *ast.JoinNode:
					if flow.Join(x.Name) == x {
						same("join", x.Name, "t_join_"+x.Name, "join_"+x.Name)
					}
				}
			}
		}
	}
	if workflows < 10 {
		t.Fatalf("only %d workflows were read", workflows)
	}
}
