package lts

import (
	"fmt"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
)

type TraceStep struct {
	Action   string `json:"action"`
	Actor    string `json:"actor"`
	Receiver string `json:"receiver,omitempty"`
	FromID   int    `json:"from_id"`
	ToID     int    `json:"to_id"`
	StateStr string `json:"state"`
}

type SequenceTrace struct {
	Title         string      `json:"title"`
	Participants  []string    `json:"participants"`
	Steps         []TraceStep `json:"steps"`
	CycleStartIdx int         `json:"cycle_start_idx"` // -1 if finite path
	Violation     string      `json:"violation"`
}

type PropertyLTS struct {
	Name     string
	States   []string
	StateMap map[string]int
	Alphabet map[string]bool
	Trans    map[int]map[string]int // state -> action -> nextState
}

func CompileProperty(prop *ast.PropertyDecl) *PropertyLTS {
	pl := &PropertyLTS{
		Name:     prop.Name,
		StateMap: map[string]int{},
		Alphabet: map[string]bool{},
		Trans:    map[int]map[string]int{},
	}
	for i, st := range prop.States {
		pl.States = append(pl.States, st.Name)
		pl.StateMap[st.Name] = i
		pl.Trans[i] = map[string]int{}
	}
	for i, st := range prop.States {
		for _, tr := range st.Transitions {
			pl.Alphabet[tr.Action] = true
			if dst, ok := pl.StateMap[tr.TargetState]; ok {
				pl.Trans[i][tr.Action] = dst
			} else if tr.TargetState == "ERROR" {
				pl.Trans[i][tr.Action] = ErrorState
			}
		}
	}
	return pl
}

// CheckDeadlock runs BFS on SystemLTS to find any reachable state with 0 outgoing
// transitions that is not cleanly terminated.
func CheckDeadlock(sys *SystemLTS) *SequenceTrace {
	type node struct {
		state int
		trace []TraceStep
	}
	visited := map[int]bool{sys.Init: true}
	queue := []node{{state: sys.Init}}

	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		edges := sys.Edges[cur.state]
		if len(edges) == 0 && !sys.States[cur.state].Terminal {
			return &SequenceTrace{
				Title:         fmt.Sprintf("Deadlock in %s", sys.SystemName),
				Participants:  append([]string{}, sys.Instances...),
				Steps:         cur.trace,
				CycleStartIdx: -1,
				Violation:     fmt.Sprintf("DEADLOCK at state %d [%s]", cur.state, strings.Join(sys.States[cur.state].Labels, ", ")),
			}
		}
		for _, e := range edges {
			if !visited[e.Target] {
				visited[e.Target] = true
				step := TraceStep{
					Action:   e.Action,
					Actor:    e.Actor,
					Receiver: e.Receiver,
					FromID:   cur.state,
					ToID:     e.Target,
					StateStr: strings.Join(sys.States[e.Target].Labels, ", "),
				}
				tr := make([]TraceStep, len(cur.trace)+1)
				copy(tr, cur.trace)
				tr[len(cur.trace)] = step
				queue = append(queue, node{state: e.Target, trace: tr})
			}
		}
	}
	return nil
}

// CheckSafety composes SystemLTS with deterministic PropertyLTS (with implicit ERROR=-1 trap)
// and searches via BFS for shortest trace reaching ERROR.
func CheckSafety(sys *SystemLTS, prop *PropertyLTS) *SequenceTrace {
	if len(prop.States) == 0 {
		return nil
	}
	type pair struct {
		sysSt  int
		propSt int
	}
	type node struct {
		p     pair
		trace []TraceStep
	}
	start := pair{sysSt: sys.Init, propSt: 0}
	visited := map[pair]bool{start: true}
	queue := []node{{p: start}}

	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		for _, e := range sys.Edges[cur.p.sysSt] {
			nextProp := cur.p.propSt
			// Match either exact action name or base action name against property alphabet
			matchedAct := ""
			if prop.Alphabet[e.Action] {
				matchedAct = e.Action
			} else if prop.Alphabet[e.BaseAction] {
				matchedAct = e.BaseAction
			}
			if matchedAct != "" {
				dst, ok := prop.Trans[cur.p.propSt][matchedAct]
				if !ok || dst == ErrorState {
					// ERROR(-1) reached!
					step := TraceStep{
						Action:   e.Action,
						Actor:    e.Actor,
						Receiver: e.Receiver,
						FromID:   cur.p.sysSt,
						ToID:     e.Target,
						StateStr: strings.Join(sys.States[e.Target].Labels, ", "),
					}
					tr := append(append([]TraceStep{}, cur.trace...), step)
					return &SequenceTrace{
						Title:         fmt.Sprintf("Safety Violation (%s) in %s", prop.Name, sys.SystemName),
						Participants:  append([]string{}, sys.Instances...),
						Steps:         tr,
						CycleStartIdx: -1,
						Violation: fmt.Sprintf("PROPERTY %s VIOLATED (ERROR=-1): action %q illegal in property state %q",
							prop.Name, matchedAct, prop.States[cur.p.propSt]),
					}
				}
				nextProp = dst
			}
			np := pair{sysSt: e.Target, propSt: nextProp}
			if !visited[np] {
				visited[np] = true
				step := TraceStep{
					Action:   e.Action,
					Actor:    e.Actor,
					Receiver: e.Receiver,
					FromID:   cur.p.sysSt,
					ToID:     e.Target,
					StateStr: strings.Join(sys.States[e.Target].Labels, ", "),
				}
				tr := append(append([]TraceStep{}, cur.trace...), step)
				queue = append(queue, node{p: np, trace: tr})
			}
		}
	}
	return nil
}
