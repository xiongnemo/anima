package ast

// Flow is the control flow of a workflow as the backends run it: the node a
// name stands for and where the workflow goes after it. Where two nodes
// could both come next, the first in the source does.
type Flow struct {
	Start       *StartNode
	steps       map[string]*StepNode
	choices     map[string]*ChoiceNode // a `choice c:` by its name
	forks       map[string]*ForkNode
	joins       map[string]*JoinNode
	merges      map[string]*MergeNode
	choiceAfter map[string]*ChoiceNode // a `choice after n:` by n
	forkAfter   map[string]string
	stepAfter   map[string]string
	firstJoin   string
}

func NewFlow(wf *WorkflowDecl) *Flow {
	f := &Flow{
		steps:       map[string]*StepNode{},
		choices:     map[string]*ChoiceNode{},
		forks:       map[string]*ForkNode{},
		joins:       map[string]*JoinNode{},
		merges:      map[string]*MergeNode{},
		choiceAfter: map[string]*ChoiceNode{},
		forkAfter:   map[string]string{},
		stepAfter:   map[string]string{},
	}
	first := func(m map[string]string, after, name string) {
		if _, taken := m[after]; after != "" && !taken {
			m[after] = name
		}
	}
	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *StartNode:
			// Sema refuses a second start; the backends would run the last.
			f.Start = x
		case *StepNode:
			f.steps[x.Name] = x
			first(f.stepAfter, x.After, x.Name)
		case *ChoiceNode:
			if x.After != "" {
				f.choiceAfter[x.After] = x
			} else {
				f.choices[x.Name] = x
			}
		case *ForkNode:
			f.forks[x.Name] = x
			first(f.forkAfter, x.After, x.Name)
		case *JoinNode:
			f.joins[x.Name] = x
			if f.firstJoin == "" {
				f.firstJoin = x.Name
			}
		case *MergeNode:
			f.merges[x.Name] = x
		}
	}
	return f
}

// Ends reports whether the workflow is over at name: done, or a name that
// stands for no node.
func (f *Flow) Ends(name string) bool {
	if name == "" || name == "done" || name == "END" {
		return true
	}
	return f.steps[name] == nil && f.forks[name] == nil && f.joins[name] == nil && f.merges[name] == nil && f.Choice(name) == nil
}

// Step, Choice, Fork, Join and Merge give the node a name stands for. A name is
// looked up in that order, so each is nil when an earlier one is not.
func (f *Flow) Step(name string) *StepNode { return f.steps[name] }

// Choice is the choice of that name, or the one written after a name that no
// node has: the choice after a node is where the node goes, not what its
// name stands for.
func (f *Flow) Choice(name string) *ChoiceNode {
	if f.steps[name] != nil {
		return nil
	}
	if ch := f.choices[name]; ch != nil {
		return ch
	}
	if f.forks[name] != nil || f.joins[name] != nil || f.merges[name] != nil {
		return nil
	}
	return f.choiceAfter[name]
}

func (f *Flow) Fork(name string) *ForkNode {
	if f.steps[name] != nil || f.choices[name] != nil {
		return nil
	}
	return f.forks[name]
}

func (f *Flow) Join(name string) *JoinNode {
	if f.steps[name] != nil || f.choices[name] != nil || f.forks[name] != nil {
		return nil
	}
	return f.joins[name]
}

func (f *Flow) Merge(name string) *MergeNode {
	if f.steps[name] != nil || f.choices[name] != nil || f.forks[name] != nil || f.joins[name] != nil {
		return nil
	}
	return f.merges[name]
}

// after is where the workflow goes from a step, a join or a merge: to its
// target, or to the choice, the fork or the step declared after it. With
// none of them it is over (next is "").
func (f *Flow) after(name, target string, fork bool) (next string, choice *ChoiceNode) {
	if target != "" {
		return target, nil
	}
	if ch := f.choiceAfter[name]; ch != nil {
		return "", ch
	}
	if fk, ok := f.forkAfter[name]; ok && fork {
		return fk, nil
	}
	return f.stepAfter[name], nil
}

// AfterStep is where the workflow goes once the body of a step has run
// without a return.
func (f *Flow) AfterStep(st *StepNode) (next string, choice *ChoiceNode) {
	return f.after(st.Name, st.Target, true)
}

// AfterFork is the join the branches of a fork meet at.
func (f *Flow) AfterFork() string { return f.firstJoin }

// AfterJoin is where the workflow goes from a join.
func (f *Flow) AfterJoin(jn *JoinNode) (next string, choice *ChoiceNode) {
	return f.after(jn.Name, jn.Target, false)
}

// AfterMerge is where the workflow goes from a merge, the node the branches
// of a choice come together at: it does nothing itself.
func (f *Flow) AfterMerge(mn *MergeNode) (next string, choice *ChoiceNode) {
	return f.after(mn.Name, mn.Target, false)
}
