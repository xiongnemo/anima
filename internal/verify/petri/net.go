package petri

import (
	"fmt"

	"github.com/xiongnemo/anima/internal/ast"
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

// CompileWorkflow builds a SWEN90004 Place/Transition Workflow Net (WF-Net)
// with explicit pool resource places, AND-split/join (fork/join), and XOR-split/join (choice/merge).
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

	// Index named nodes for cross-referencing
	var startNode *ast.StartNode
	stepNodes := map[string]*ast.StepNode{}
	choiceNodes := map[string]*ast.ChoiceNode{}
	choiceAfter := map[string]*ast.ChoiceNode{}
	forkNodes := map[string]*ast.ForkNode{}
	forkAfter := map[string]*ast.ForkNode{}
	joinNodes := map[string]*ast.JoinNode{}
	mergeNodes := map[string]*ast.MergeNode{}
	stepAfter := map[string][]*ast.StepNode{}

	var joinOrder []*ast.JoinNode
	var mergeOrder []*ast.MergeNode

	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.StartNode:
			startNode = x
		case *ast.StepNode:
			stepNodes[x.Name] = x
			if x.After != "" {
				stepAfter[x.After] = append(stepAfter[x.After], x)
			}
		case *ast.ChoiceNode:
			if x.Name != "" {
				choiceNodes[x.Name] = x
			}
			if x.After != "" {
				choiceAfter[x.After] = x
			}
		case *ast.ForkNode:
			forkNodes[x.Name] = x
			if x.After != "" {
				forkAfter[x.After] = x
			}
		case *ast.JoinNode:
			joinNodes[x.Name] = x
			joinOrder = append(joinOrder, x)
		case *ast.MergeNode:
			mergeNodes[x.Name] = x
			mergeOrder = append(mergeOrder, x)
		}
	}

	// Helper: entry place for a named target node
	targetEntryPlace := func(name string) int {
		if name == "done" || name == "END" {
			return net.DonePlace
		}
		if _, isJoin := joinNodes[name]; isJoin {
			// Join collects branch end places separately; direct reference creates a join input place
			return net.ensurePlace("in:"+name, PlaceControl, 0)
		}
		if _, isMerge := mergeNodes[name]; isMerge {
			return net.ensurePlace("p:"+name, PlaceControl, 0)
		}
		return net.ensurePlace("p:"+name, PlaceControl, 0)
	}

	// 1. Start node transition
	if startNode != nil {
		net.addTrans("t_start", TransStep,
			map[int]int{net.StartPlace: 1},
			map[int]int{targetEntryPlace(startNode.Target): 1},
		)
	}

	// 2. Step nodes
	for _, st := range stepNodes {
		inPlace := net.ensurePlace("p:"+st.Name, PlaceControl, 0)
		var outPlace int
		switch {
		case st.Target != "":
			if _, isJoin := joinNodes[st.Target]; isJoin {
				// Step feeds an explicit join branch input place
				outPlace = net.ensurePlace("join_in:"+st.Target+":"+st.Name, PlaceControl, 0)
			} else {
				outPlace = targetEntryPlace(st.Target)
			}
			net.addTrans("t_"+st.Name, TransStep, map[int]int{inPlace: 1}, map[int]int{outPlace: 1})
		case choiceAfter[st.Name] != nil || forkAfter[st.Name] != nil:
			// Step executes then feeds choice/fork place
			outPlace = net.ensurePlace("after:"+st.Name, PlaceControl, 0)
			net.addTrans("t_"+st.Name, TransStep, map[int]int{inPlace: 1}, map[int]int{outPlace: 1})
		default:
			// Step itself might directly be `p:st.Name` consumed by `choice after st.Name` if no explicit action
		}
	}

	// 3. Choice nodes (XOR-split: one shared input place, one transition per branch)
	for _, n := range wf.Nodes {
		cn, ok := n.(*ast.ChoiceNode)
		if !ok {
			continue
		}
		var splitPlace int
		if cn.After != "" {
			if st, exists := stepNodes[cn.After]; exists && st.Target == "" && len(st.Body) >= 0 {
				// Check if t_step produced after:cn.After
				if ap, has := net.PlaceByName["after:"+cn.After]; has {
					splitPlace = ap
				} else {
					splitPlace = net.ensurePlace("p:"+cn.After, PlaceControl, 0)
				}
			} else {
				splitPlace = net.ensurePlace("p:"+cn.After, PlaceControl, 0)
			}
		} else if cn.Name != "" {
			splitPlace = net.ensurePlace("p:"+cn.Name, PlaceControl, 0)
		} else {
			splitPlace = net.ensurePlace("p:choice", PlaceControl, 0)
		}

		for idx, br := range cn.Branches {
			var dst int
			if _, isJoin := joinNodes[br.Target]; isJoin {
				dst = net.ensurePlace(fmt.Sprintf("join_in:%s:choice_%d", br.Target, idx), PlaceControl, 0)
			} else {
				dst = targetEntryPlace(br.Target)
			}
			tname := fmt.Sprintf("t_choice_%d_%s", idx+1, br.Target)
			net.addTrans(tname, TransChoice, map[int]int{splitPlace: 1}, map[int]int{dst: 1})
		}
	}

	// Track branch end places feeding joins or merges
	joinInputs := map[string][]int{}
	mergeInputs := map[string][]int{}

	// Collect step->join explicit inputs
	for _, st := range stepNodes {
		if st.Target != "" {
			if _, isJoin := joinNodes[st.Target]; isJoin {
				pName := "join_in:" + st.Target + ":" + st.Name
				if pid, ok := net.PlaceByName[pName]; ok {
					joinInputs[st.Target] = append(joinInputs[st.Target], pid)
				}
			}
		}
	}
	for _, n := range wf.Nodes {
		if cn, ok := n.(*ast.ChoiceNode); ok {
			for idx, br := range cn.Branches {
				if _, isJoin := joinNodes[br.Target]; isJoin {
					pName := fmt.Sprintf("join_in:%s:choice_%d", br.Target, idx)
					if pid, ok := net.PlaceByName[pName]; ok {
						joinInputs[br.Target] = append(joinInputs[br.Target], pid)
					}
				}
			}
		}
	}

	// 4. Fork nodes (AND-split) -> Branches -> Join or Merge
	// Match each ForkNode to its succeeding JoinNode or MergeNode if not explicitly referenced
	for _, fk := range forkNodes {
		inPlace := net.ensurePlace("p:"+fk.Name, PlaceControl, 0)
		if fk.After != "" {
			if ap, has := net.PlaceByName["after:"+fk.After]; has {
				inPlace = ap
			}
		}

		postFork := map[int]int{}
		// Determine whether this fork is closed by a Join or a Merge (buggy XOR-join!)
		targetJoin := ""
		targetMerge := ""
		if len(joinOrder) > 0 {
			targetJoin = joinOrder[0].Name
		}
		for _, m := range mergeOrder {
			if len(m.Afters) == 0 && targetJoin == "" {
				targetMerge = m.Name
				break
			}
			for _, af := range m.Afters {
				if af == fk.Name {
					targetMerge = m.Name
					break
				}
			}
		}

		for _, br := range fk.Branches {
			brStart := net.ensurePlace(fmt.Sprintf("p:%s:%s:0", fk.Name, br.Name), PlaceControl, 0)
			postFork[brStart] = 1
			curPlace := brStart

			if len(br.Ops) == 0 {
				nextP := net.ensurePlace(fmt.Sprintf("p:%s:%s:end", fk.Name, br.Name), PlaceControl, 0)
				net.addTrans(fmt.Sprintf("t_%s_%s_noop", fk.Name, br.Name), TransOp, map[int]int{curPlace: 1}, map[int]int{nextP: 1})
				curPlace = nextP
			} else {
				for opIdx, op := range br.Ops {
					nextP := net.ensurePlace(fmt.Sprintf("p:%s:%s:%d", fk.Name, br.Name, opIdx+1), PlaceControl, 0)
					pre := map[int]int{curPlace: 1}
					post := map[int]int{nextP: 1}
					opLabel := fmt.Sprintf("t_%s_%s_%d", fk.Name, br.Name, opIdx+1)
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
					curPlace = nextP
				}
			}

			if targetMerge != "" {
				mergeInputs[targetMerge] = append(mergeInputs[targetMerge], curPlace)
			} else if targetJoin != "" {
				joinInputs[targetJoin] = append(joinInputs[targetJoin], curPlace)
			} else {
				// No join or merge specified -> sends straight to done (improper completion if >1 branches!)
				net.addTrans(fmt.Sprintf("t_%s_%s_to_done", fk.Name, br.Name), TransStep,
					map[int]int{curPlace: 1}, map[int]int{net.DonePlace: 1})
			}
		}

		net.addTrans("t_fork_"+fk.Name, TransFork, map[int]int{inPlace: 1}, postFork)
	}

	// 5. Join nodes (AND-join: SINGLE transition consuming ALL branch end places!)
	for _, jn := range joinNodes {
		pre := map[int]int{}
		for _, pid := range joinInputs[jn.Name] {
			pre[pid] += 1
		}
		if len(pre) == 0 {
			pre[net.ensurePlace("in:"+jn.Name, PlaceControl, 0)] = 1
		}
		var outPlace int
		if jn.Target != "" {
			outPlace = targetEntryPlace(jn.Target)
		} else if afters := stepAfter[jn.Name]; len(afters) > 0 {
			outPlace = targetEntryPlace(afters[0].Name)
		} else {
			outPlace = net.DonePlace
		}
		net.addTrans("t_join_"+jn.Name, TransJoin, pre, map[int]int{outPlace: 1})
	}

	// 6. Merge nodes (XOR-join: SEPARATE transitions from each incoming branch to shared merge place -> out)
	for _, mn := range mergeNodes {
		mergePlace := net.ensurePlace("p:"+mn.Name, PlaceControl, 0)
		for idx, pid := range mergeInputs[mn.Name] {
			net.addTrans(fmt.Sprintf("t_merge_%s_%d", mn.Name, idx+1), TransMerge,
				map[int]int{pid: 1}, map[int]int{mergePlace: 1})
		}
		var outPlace int
		if mn.Target != "" {
			outPlace = targetEntryPlace(mn.Target)
		} else if afters := stepAfter[mn.Name]; len(afters) > 0 {
			outPlace = targetEntryPlace(afters[0].Name)
		} else {
			outPlace = net.DonePlace
		}
		if len(mergeInputs[mn.Name]) > 0 || mn.Target != "" || len(stepAfter[mn.Name]) > 0 {
			net.addTrans("t_after_merge_"+mn.Name, TransStep,
				map[int]int{mergePlace: 1}, map[int]int{outPlace: 1})
		}
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
