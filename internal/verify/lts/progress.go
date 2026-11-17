package lts

import (
	"fmt"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
)

// TarjanSCC computes strongly connected components on SystemLTS (each SCC as a slice of state IDs).
// Tarjan's algorithm emits SCCs in reverse topological order (terminal SCCs first).
func TarjanSCC(sys *SystemLTS) [][]int {
	n := len(sys.States)
	index := make([]int, n)
	low := make([]int, n)
	onStack := make([]bool, n)
	for i := range index {
		index[i] = -1
	}
	curIdx := 0
	var stack []int
	var sccs [][]int

	var strongConnect func(v int)
	strongConnect = func(v int) {
		index[v] = curIdx
		low[v] = curIdx
		curIdx++
		stack = append(stack, v)
		onStack[v] = true

		for _, e := range sys.Edges[v] {
			w := e.Target
			if index[w] == -1 {
				strongConnect(w)
				if low[w] < low[v] {
					low[v] = low[w]
				}
			} else if onStack[w] {
				if index[w] < low[v] {
					low[v] = index[w]
				}
			}
		}

		if low[v] == index[v] {
			var comp []int
			for {
				w := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				onStack[w] = false
				comp = append(comp, w)
				if w == v {
					break
				}
			}
			sccs = append(sccs, comp)
		}
	}

	if n > 0 {
		strongConnect(sys.Init)
	}
	return sccs
}

// CheckProgress implements Magee & Kramer LTSA Terminal-SCC Progress checking under Fair Choice.
// Every Terminal SCC (no outgoing edge to another SCC) that is not a clean Terminal sink
// must contain at least one action from the progress set.
func CheckProgress(sys *SystemLTS, prog *ast.ProgressDecl) (sccCount int, cex *SequenceTrace) {
	sccs := TarjanSCC(sys)
	sccCount = len(sccs)

	compID := make([]int, len(sys.States))
	for i := range compID {
		compID[i] = -1
	}
	for cid, comp := range sccs {
		for _, v := range comp {
			compID[v] = cid
		}
	}

	progSet := map[string]bool{}
	for _, a := range prog.Actions {
		progSet[a] = true
	}

	for cid, comp := range sccs {
		inComp := make(map[int]bool, len(comp))
		for _, v := range comp {
			inComp[v] = true
		}

		// Determine if this SCC is Terminal (no edge leaving to another SCC)
		hasOutEdge := false
		internalEdges := 0
		hasProgressAction := false
		allCleanTerm := true
		for _, u := range comp {
			if !sys.States[u].Terminal {
				allCleanTerm = false
			}
			for _, e := range sys.Edges[u] {
				if compID[e.Target] != cid {
					hasOutEdge = true
				} else {
					internalEdges++
					if !e.Hidden && (progSet[e.Action] || progSet[e.BaseAction]) {
						hasProgressAction = true
					}
				}
			}
		}
		if hasOutEdge {
			continue
		}
		if allCleanTerm && internalEdges == 0 {
			continue
		}
		// Either a non-clean deadlock sink or an infinite terminal cycle missing progress action!
		if !hasProgressAction {
			stem := shortestPath(sys, sys.Init, comp[0])
			var lasso []TraceStep
			if internalEdges > 0 {
				lasso = findCycleInSCC(sys, comp[0], inComp)
			}
			cycleIdx := -1
			if len(lasso) > 0 {
				cycleIdx = len(stem)
				stem = append(stem, lasso...)
			}
			return sccCount, &SequenceTrace{
				Title:         fmt.Sprintf("Progress Violation (%s) in %s", prog.Name, sys.SystemName),
				Participants:  append([]string{}, sys.Instances...),
				Steps:         stem,
				CycleStartIdx: cycleIdx,
				Violation:     fmt.Sprintf("PROGRESS %s VIOLATED: terminal SCC (%d states) starves {%s}", prog.Name, len(comp), strings.Join(prog.Actions, ", ")),
			}
		}
	}
	return sccCount, nil
}

// CheckLTL verifies bounded FLTL properties on SystemLTS.
func CheckLTL(sys *SystemLTS, chk ast.SystemCheck) *SequenceTrace {
	switch f := chk.LTL.(type) {
	case *ast.LTLNever:
		// Never A: BFS for any edge matching A
		type node struct {
			st    int
			trace []TraceStep
		}
		vis := map[int]bool{sys.Init: true}
		q := []node{{st: sys.Init}}
		for len(q) > 0 {
			cur := q[0]
			q = q[1:]
			for _, e := range sys.Edges[cur.st] {
				step := TraceStep{Action: e.Action, Actor: e.Actor, Receiver: e.Receiver, FromID: cur.st, ToID: e.Target, StateStr: strings.Join(sys.States[e.Target].Labels, ", ")}
				tr := append(append([]TraceStep{}, cur.trace...), step)
				if e.Action == f.Action || e.BaseAction == f.Action {
					return &SequenceTrace{
						Title:         fmt.Sprintf("LTL Violation (never %s)", f.Action),
						Participants:  append([]string{}, sys.Instances...),
						Steps:         tr,
						CycleStartIdx: -1,
						Violation:     fmt.Sprintf("LTL VIOLATED: forbidden action %q occurred", f.Action),
					}
				}
				if !vis[e.Target] {
					vis[e.Target] = true
					q = append(q, node{st: e.Target, trace: tr})
				}
			}
		}

	case *ast.LTLAlwaysEventually:
		// Product with 2-state response monitor:
		// m=0: ok / waiting for trigger
		// m=1: triggered, awaiting response
		// Violation if: (a) m=1 reaches a state with 0 outgoing edges, OR (b) m=1 participates in a cycle staying strictly in m=1!
		type pState struct {
			sysSt int
			mon   int
		}
		start := pState{sysSt: sys.Init, mon: 0}
		prodEdges := map[pState][]struct {
			dst  pState
			edge CompositeEdge
		}{}
		vis := map[pState]bool{start: true}
		q := []pState{start}

		for len(q) > 0 {
			cur := q[0]
			q = q[1:]
			for _, e := range sys.Edges[cur.sysSt] {
				nextMon := cur.mon
				isTrig := e.Action == f.Trigger || e.BaseAction == f.Trigger
				isResp := e.Action == f.Response || e.BaseAction == f.Response
				if cur.mon == 0 {
					if isTrig && !isResp {
						nextMon = 1
					}
				} else {
					if isResp {
						nextMon = 0
					} else {
						nextMon = 1
					}
				}
				dst := pState{sysSt: e.Target, mon: nextMon}
				prodEdges[cur] = append(prodEdges[cur], struct {
					dst  pState
					edge CompositeEdge
				}{dst: dst, edge: e})
				if !vis[dst] {
					vis[dst] = true
					q = append(q, dst)
				}
			}
		}

		// (a) Check deadlock / termination in mon == 1
		for ps := range vis {
			if ps.mon == 1 && len(sys.Edges[ps.sysSt]) == 0 {
				return &SequenceTrace{
					Title:         fmt.Sprintf("LTL Violation (%s)", chk.RawText),
					Participants:  append([]string{}, sys.Instances...),
					Steps:         shortestPath(sys, sys.Init, ps.sysSt),
					CycleStartIdx: -1,
					Violation:     fmt.Sprintf("LTL VIOLATED: %q occurred but system ended without %q", f.Trigger, f.Response),
				}
			}
		}

		// (b) Check any cycle strictly inside {ps | ps.mon == 1}
		for ps := range vis {
			if ps.mon != 1 {
				continue
			}
			// BFS from ps staying inside mon==1 to see if ps can reach itself in >=1 step
			type cNode struct {
				p     pState
				steps []TraceStep
			}
			seenCycle := map[pState]bool{}
			cq := []cNode{}
			for _, pe := range prodEdges[ps] {
				if pe.dst.mon == 1 {
					step := TraceStep{Action: pe.edge.Action, Actor: pe.edge.Actor, Receiver: pe.edge.Receiver, FromID: ps.sysSt, ToID: pe.dst.sysSt, StateStr: strings.Join(sys.States[pe.dst.sysSt].Labels, ", ")}
					if pe.dst == ps {
						stem := shortestPathToTrigger(sys, f.Trigger, ps.sysSt)
						idx := len(stem)
						return &SequenceTrace{
							Title:         fmt.Sprintf("LTL Violation (%s)", chk.RawText),
							Participants:  append([]string{}, sys.Instances...),
							Steps:         append(stem, step),
							CycleStartIdx: idx,
							Violation:     fmt.Sprintf("LTL VIOLATED: infinite cycle avoiding %q after %q", f.Response, f.Trigger),
						}
					}
					seenCycle[pe.dst] = true
					cq = append(cq, cNode{p: pe.dst, steps: []TraceStep{step}})
				}
			}
			for len(cq) > 0 {
				cn := cq[0]
				cq = cq[1:]
				for _, pe := range prodEdges[cn.p] {
					if pe.dst.mon != 1 {
						continue
					}
					step := TraceStep{Action: pe.edge.Action, Actor: pe.edge.Actor, Receiver: pe.edge.Receiver, FromID: cn.p.sysSt, ToID: pe.dst.sysSt, StateStr: strings.Join(sys.States[pe.dst.sysSt].Labels, ", ")}
					if pe.dst == ps {
						stem := shortestPathToTrigger(sys, f.Trigger, ps.sysSt)
						idx := len(stem)
						return &SequenceTrace{
							Title:         fmt.Sprintf("LTL Violation (%s)", chk.RawText),
							Participants:  append([]string{}, sys.Instances...),
							Steps:         append(stem, append(cn.steps, step)...),
							CycleStartIdx: idx,
							Violation:     fmt.Sprintf("LTL VIOLATED: infinite cycle avoiding %q after %q", f.Response, f.Trigger),
						}
					}
					if !seenCycle[pe.dst] {
						seenCycle[pe.dst] = true
						cq = append(cq, cNode{p: pe.dst, steps: append(append([]TraceStep{}, cn.steps...), step)})
					}
				}
			}
		}
	}
	return nil
}

func shortestPath(sys *SystemLTS, from, target int) []TraceStep {
	if from == target {
		return nil
	}
	type node struct {
		st    int
		steps []TraceStep
	}
	vis := map[int]bool{from: true}
	q := []node{{st: from}}
	for len(q) > 0 {
		cur := q[0]
		q = q[1:]
		for _, e := range sys.Edges[cur.st] {
			step := TraceStep{
				Action: e.Action, Actor: e.Actor, Receiver: e.Receiver,
				FromID: cur.st, ToID: e.Target, StateStr: strings.Join(sys.States[e.Target].Labels, ", "),
			}
			tr := append(append([]TraceStep{}, cur.steps...), step)
			if e.Target == target {
				return tr
			}
			if !vis[e.Target] {
				vis[e.Target] = true
				q = append(q, node{st: e.Target, steps: tr})
			}
		}
	}
	return nil
}

func shortestPathToTrigger(sys *SystemLTS, trigger string, targetSys int) []TraceStep {
	type pState struct {
		st  int
		hit bool
	}
	type node struct {
		p     pState
		steps []TraceStep
	}
	start := pState{st: sys.Init, hit: false}
	vis := map[pState]bool{start: true}
	q := []node{{p: start}}
	for len(q) > 0 {
		cur := q[0]
		q = q[1:]
		for _, e := range sys.Edges[cur.p.st] {
			hit := cur.p.hit || e.Action == trigger || e.BaseAction == trigger
			step := TraceStep{
				Action: e.Action, Actor: e.Actor, Receiver: e.Receiver,
				FromID: cur.p.st, ToID: e.Target, StateStr: strings.Join(sys.States[e.Target].Labels, ", "),
			}
			tr := append(append([]TraceStep{}, cur.steps...), step)
			if e.Target == targetSys && hit {
				return tr
			}
			np := pState{st: e.Target, hit: hit}
			if !vis[np] {
				vis[np] = true
				q = append(q, node{p: np, steps: tr})
			}
		}
	}
	return shortestPath(sys, sys.Init, targetSys)
}

func findCycleInSCC(sys *SystemLTS, start int, inComp map[int]bool) []TraceStep {
	type node struct {
		st    int
		steps []TraceStep
	}
	vis := map[int]bool{}
	var q []node
	for _, e := range sys.Edges[start] {
		if !inComp[e.Target] {
			continue
		}
		step := TraceStep{
			Action: e.Action, Actor: e.Actor, Receiver: e.Receiver,
			FromID: start, ToID: e.Target, StateStr: strings.Join(sys.States[e.Target].Labels, ", "),
		}
		if e.Target == start {
			return []TraceStep{step}
		}
		vis[e.Target] = true
		q = append(q, node{st: e.Target, steps: []TraceStep{step}})
	}
	for len(q) > 0 {
		cur := q[0]
		q = q[1:]
		for _, e := range sys.Edges[cur.st] {
			if !inComp[e.Target] {
				continue
			}
			step := TraceStep{
				Action: e.Action, Actor: e.Actor, Receiver: e.Receiver,
				FromID: cur.st, ToID: e.Target, StateStr: strings.Join(sys.States[e.Target].Labels, ", "),
			}
			tr := append(append([]TraceStep{}, cur.steps...), step)
			if e.Target == start {
				return tr
			}
			if !vis[e.Target] {
				vis[e.Target] = true
				q = append(q, node{st: e.Target, steps: tr})
			}
		}
	}
	return nil
}
