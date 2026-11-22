package petri

import (
	"fmt"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
)

type PlaceKind int

const (
	PlaceStart PlaceKind = iota
	PlaceDone
	PlaceControl
	PlacePool
)

type Place struct {
	ID         int
	Name       string
	Kind       PlaceKind
	InitTokens int
}

type TransKind int

const (
	TransStep TransKind = iota
	TransFork
	TransJoin
	TransChoice
	TransMerge
	TransOp
	TransShortCircuit
)

type Transition struct {
	ID   int
	Name string
	Kind TransKind
	Pre  map[int]int
	Post map[int]int
}

type PetriNet struct {
	Name        string
	VerifyFlags []string
	Places      []Place
	Transitions []Transition
	PlaceByName map[string]int
	StartPlace  int
	DonePlace   int
	PoolPlaces  []int
	InitMarking []int
	TargetMark  []int
}

func (n *PetriNet) ensurePlace(name string, kind PlaceKind, initTok int) int {
	if id, ok := n.PlaceByName[name]; ok {
		return id
	}
	id := len(n.Places)
	n.Places = append(n.Places, Place{ID: id, Name: name, Kind: kind, InitTokens: initTok})
	n.PlaceByName[name] = id
	if kind == PlacePool {
		n.PoolPlaces = append(n.PoolPlaces, id)
	}
	return id
}

func (n *PetriNet) addTrans(name string, kind TransKind, pre, post map[int]int) int {
	id := len(n.Transitions)
	n.Transitions = append(n.Transitions, Transition{
		ID: id, Name: name, Kind: kind, Pre: pre, Post: post,
	})
	return id
}

// CompileWorkflow is the workflow as a place / transition net: the control
// the backends run (ast.Flow), with a place for each name the control stands
// at, the pools as places, a fork as an AND-split and its join an AND-join.
//
//   - A step moves the control where the flow goes after it; one whose body
//     always returns moves it to done. With nowhere to go it leaves the
//     control at a place of its own, and the net does not complete.
//   - A choice has a transition for each branch, from the place of its own
//     name or from the place its step leaves the control at.
//   - The branches of a fork end in the first join of the workflow, the only
//     one the backends go to. With no join each branch ends the workflow.
//   - A join waits for the branches and for each node written to go to it.
//
// A node the flow does not come to has a transition that never fires.
func CompileWorkflow(wf *ast.WorkflowDecl) (*PetriNet, error) {
	net := &PetriNet{
		Name:        wf.Name,
		VerifyFlags: append([]string{}, wf.VerifyFlags...),
		PlaceByName: map[string]int{},
	}

	net.StartPlace = net.ensurePlace("start", PlaceStart, 1)
	net.DonePlace = net.ensurePlace("done", PlaceDone, 0)

	poolIDs := map[string]int{}
	for _, pl := range wf.Pools {
		pid := net.ensurePlace("pool:"+pl.Name, PlacePool, int(pl.Capacity))
		poolIDs[pl.Name] = pid
	}

	flow := ast.NewFlow(wf)
	joinInputs := map[string][]int{}
	// at is the place of the control standing at a name. A name with no node
	// has a place nothing takes the control from.
	at := func(name string) int {
		if name == "done" || name == "END" {
			return net.DonePlace
		}
		return net.ensurePlace("p:"+name, PlaceControl, 0)
	}
	// into is where who (a kind and a name, so no two are one) sends the
	// control when it goes to name: a join waits for it as it waits for a
	// branch.
	into := func(name, who string) int {
		if flow.Join(name) == nil {
			return at(name)
		}
		pid := net.ensurePlace("join_in:"+name+":"+who, PlaceControl, 0)
		joinInputs[name] = append(joinInputs[name], pid)
		return pid
	}
	// leave is the place a step, a join or a merge leaves the control at:
	// the one the choice written after it takes it from, or the place of
	// the node it goes to. A join that goes nowhere ends the workflow; a
	// step or a merge that does ends it on the backends, and the net asks
	// for the `-> done` to be written.
	chosenAt := map[*ast.ChoiceNode]int{}
	leave := func(name, who, next string, choice *ast.ChoiceNode) int {
		switch {
		case choice != nil:
			chosenAt[choice] = net.ensurePlace("after:"+name, PlaceControl, 0)
			return chosenAt[choice]
		case next != "":
			return into(next, who)
		case flow.Join(name) != nil:
			return net.DonePlace
		}
		return net.ensurePlace("no_successor:"+name, PlaceControl, 0)
	}
	leaves := map[ast.WorkflowNode]int{}
	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.StepNode:
			if sema.AlwaysReturns(x.Body) {
				leaves[x] = net.DonePlace
				continue
			}
			next, choice := flow.AfterStep(x)
			leaves[x] = leave(x.Name, "step:"+x.Name, next, choice)
		case *ast.MergeNode:
			next, choice := flow.AfterMerge(x)
			leaves[x] = leave(x.Name, "merge:"+x.Name, next, choice)
		case *ast.JoinNode:
			next, choice := flow.AfterJoin(x)
			leaves[x] = leave(x.Name, "join:"+x.Name, next, choice)
		}
	}

	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.StartNode:
			to := net.DonePlace
			if !sema.AlwaysReturns(x.Body) {
				to = into(x.Target, "start")
			}
			net.addTrans("t_start", TransStep, map[int]int{net.StartPlace: 1}, map[int]int{to: 1})

		case *ast.StepNode:
			net.addTrans("t_"+x.Name, TransStep, map[int]int{at(x.Name): 1}, map[int]int{leaves[x]: 1})

		case *ast.MergeNode:
			net.addTrans("t_after_merge_"+x.Name, TransStep, map[int]int{at(x.Name): 1}, map[int]int{leaves[x]: 1})

		case *ast.ChoiceNode:
			// A choice is taken where the flow comes to it: after the
			// node that goes on to it, or at the name it stands for.
			key := x.After
			if key == "" {
				key = x.Name
			}
			from, reached := chosenAt[x]
			switch {
			case reached:
			case flow.Choice(key) == x:
				from = at(key)
			default:
				from = net.ensurePlace("unreached:after:"+key, PlaceControl, 0)
			}
			for idx, br := range x.Branches {
				to := into(br.Target, fmt.Sprintf("choice:%s:%d", key, idx))
				net.addTrans(fmt.Sprintf("t_choice_%s_%d_%s", key, idx+1, br.Target), TransChoice,
					map[int]int{from: 1}, map[int]int{to: 1})
			}

		case *ast.ForkNode:
			postFork := map[int]int{}
			join := flow.AfterFork()
			for _, br := range x.Branches {
				cur := net.ensurePlace(fmt.Sprintf("p:%s:%s:0", x.Name, br.Name), PlaceControl, 0)
				postFork[cur] = 1
				if len(br.Ops) == 0 {
					end := net.ensurePlace(fmt.Sprintf("p:%s:%s:end", x.Name, br.Name), PlaceControl, 0)
					net.addTrans(fmt.Sprintf("t_%s_%s_noop", x.Name, br.Name), TransOp, map[int]int{cur: 1}, map[int]int{end: 1})
					cur = end
				}
				for opIdx, op := range br.Ops {
					nextP := net.ensurePlace(fmt.Sprintf("p:%s:%s:%d", x.Name, br.Name, opIdx+1), PlaceControl, 0)
					pre := map[int]int{cur: 1}
					post := map[int]int{nextP: 1}
					opLabel := fmt.Sprintf("t_%s_%s_%d", x.Name, br.Name, opIdx+1)
					switch op.Kind {
					case ast.BranchAcquire:
						pid, ok := poolIDs[op.Target]
						if !ok {
							return nil, fmt.Errorf("%s: unknown pool %q", op.Span, op.Target)
						}
						pre[pid] += 1
						opLabel = fmt.Sprintf("t_acq_%s_%s", br.Name, op.Target)
					case ast.BranchRelease:
						pid, ok := poolIDs[op.Target]
						if !ok {
							return nil, fmt.Errorf("%s: unknown pool %q", op.Span, op.Target)
						}
						post[pid] += 1
						opLabel = fmt.Sprintf("t_rel_%s_%s", br.Name, op.Target)
					case ast.BranchSync:
						opLabel = fmt.Sprintf("t_sync_%s_%s", br.Name, op.Target)
					case ast.BranchStepRef:
						opLabel = fmt.Sprintf("t_step_%s_%s", br.Name, op.Target)
					}
					net.addTrans(opLabel, TransOp, pre, post)
					cur = nextP
				}
				if join != "" {
					joinInputs[join] = append(joinInputs[join], cur)
				} else {
					// With no join the workflow is over after the fork:
					// once for each branch.
					net.addTrans(fmt.Sprintf("t_%s_%s_to_done", x.Name, br.Name), TransStep,
						map[int]int{cur: 1}, map[int]int{net.DonePlace: 1})
				}
			}
			net.addTrans("t_fork_"+x.Name, TransFork, map[int]int{at(x.Name): 1}, postFork)
		}
	}

	// A join comes last: it waits for every place written above, and
	// for the joins that go to it.
	for _, n := range wf.Nodes {
		jn, ok := n.(*ast.JoinNode)
		if !ok {
			continue
		}
		pre := map[int]int{}
		for _, pid := range joinInputs[jn.Name] {
			pre[pid] += 1
		}
		if len(pre) == 0 {
			pre[net.ensurePlace("in:"+jn.Name, PlaceControl, 0)] = 1
		}
		net.addTrans("t_join_"+jn.Name, TransJoin, pre, map[int]int{leaves[jn]: 1})
	}

	// Build initial and clean final markings
	net.InitMarking = make([]int, len(net.Places))
	net.TargetMark = make([]int, len(net.Places))
	for i, pl := range net.Places {
		net.InitMarking[i] = pl.InitTokens
		if pl.Kind == PlaceDone {
			net.TargetMark[i] = 1
		} else if pl.Kind == PlacePool {
			net.TargetMark[i] = pl.InitTokens
		}
	}
	return net, nil
}
