package petri

import "math"

const Omega = math.MaxInt32

type CoverNode struct {
	ID       int
	Marking  []int
	Parent   int
	ViaTrans int
}

type CoverResult struct {
	Nodes           []CoverNode
	Bounded         bool
	OneSafe         bool
	UnboundedPlaces []string
	MaxTokens       map[string]int
}

// ComputeCoverability runs the Karp-Miller Coverability Tree algorithm with omega acceleration.
func ComputeCoverability(net *PetriNet) *CoverResult {
	res := &CoverResult{
		Bounded:   true,
		OneSafe:   true,
		MaxTokens: map[string]int{},
	}
	root := CoverNode{
		ID:      0,
		Marking: append([]int{}, net.InitMarking...),
		Parent:  -1,
	}
	res.Nodes = append(res.Nodes, root)
	queue := []int{0}

	const maxCoverNodes = 20_000
	for len(queue) > 0 && len(res.Nodes) < maxCoverNodes {
		nid := queue[0]
		queue = queue[1:]
		cur := res.Nodes[nid]

		// Check if identical marking exists on ancestor path (duplicate stop condition)
		isDuplicate := false
		for anc := cur.Parent; anc != -1; anc = res.Nodes[anc].Parent {
			if equalMarkings(cur.Marking, res.Nodes[anc].Marking) {
				isDuplicate = true
				break
			}
		}
		if isDuplicate {
			continue
		}

		// Fire every enabled transition
		for _, tr := range net.Transitions {
			if !isEnabled(cur.Marking, tr) {
				continue
			}
			next := fireMarking(cur.Marking, tr)

			// Karp-Miller omega acceleration along ancestors
			for anc := nid; anc != -1; anc = res.Nodes[anc].Parent {
				am := res.Nodes[anc].Marking
				if coversStrictly(next, am) {
					for p := range next {
						if next[p] > am[p] {
							next[p] = Omega
						}
					}
				}
			}

			childID := len(res.Nodes)
			res.Nodes = append(res.Nodes, CoverNode{
				ID:       childID,
				Marking:  next,
				Parent:   nid,
				ViaTrans: tr.ID,
			})
			queue = append(queue, childID)
		}
	}

	seenUnbounded := map[string]bool{}
	for _, node := range res.Nodes {
		for p, tok := range node.Marking {
			pl := net.Places[p]
			if tok == Omega {
				res.Bounded = false
				res.OneSafe = false
				res.MaxTokens[pl.Name] = Omega
				if !seenUnbounded[pl.Name] {
					seenUnbounded[pl.Name] = true
					res.UnboundedPlaces = append(res.UnboundedPlaces, pl.Name)
				}
				continue
			}
			if tok > res.MaxTokens[pl.Name] {
				res.MaxTokens[pl.Name] = tok
			}
			if pl.Kind != PlacePool && tok > 1 {
				res.OneSafe = false
			}
		}
	}
	return res
}

func isEnabled(m []int, tr Transition) bool {
	for p, req := range tr.Pre {
		if m[p] != Omega && m[p] < req {
			return false
		}
	}
	return true
}

func fireMarking(m []int, tr Transition) []int {
	next := append([]int{}, m...)
	for p, req := range tr.Pre {
		if next[p] != Omega {
			next[p] -= req
		}
	}
	for p, prod := range tr.Post {
		if next[p] != Omega {
			next[p] += prod
		}
	}
	return next
}

func equalMarkings(a, b []int) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func coversStrictly(a, b []int) bool {
	strict := false
	for i := range a {
		if a[i] < b[i] {
			return false
		}
		if a[i] > b[i] {
			strict = true
		}
	}
	return strict
}
