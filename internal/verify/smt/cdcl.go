package smt

import "sort"

// cdclSolver implements a DPLL/CDCL SAT solver with 2-watched literals and 1-UIP clause learning.
type cdclSolver struct {
	numVars   int
	clauses   [][]int // literal: +v or -v (1-indexed)
	watches   [][]int // indexed by litIdx(lit) -> list of clause indices
	assigns   []int8  // 0: undef, 1: true, -1: false (1-indexed)
	level     []int
	reason    []int // clause index that propagated var, -1 if decision
	trail     []int // assigned literals in order
	trailLim  []int // stack of trail indices starting each decision level
	qhead     int
	activity  []float64
	varInc    float64
	learntNum int
}

func newCDCL(numVars int) *cdclSolver {
	s := &cdclSolver{
		numVars:  numVars,
		watches:  make([][]int, 2*(numVars+1)),
		assigns:  make([]int8, numVars+1),
		level:    make([]int, numVars+1),
		reason:   make([]int, numVars+1),
		activity: make([]float64, numVars+1),
		varInc:   1.0,
	}
	for i := range s.reason {
		s.reason[i] = -1
	}
	return s
}

func litVar(lit int) int {
	if lit < 0 {
		return -lit
	}
	return lit
}

func litIdx(lit int) int {
	if lit > 0 {
		return 2 * lit
	}
	return 2*(-lit) + 1
}

func (s *cdclSolver) valLit(lit int) int8 {
	v := s.assigns[litVar(lit)]
	if lit < 0 {
		return -v
	}
	return v
}

func (s *cdclSolver) decisionLevel() int {
	return len(s.trailLim)
}

func (s *cdclSolver) enqueue(lit int, reasonClause int) bool {
	val := s.valLit(lit)
	if val != 0 {
		return val == 1
	}
	v := litVar(lit)
	if lit > 0 {
		s.assigns[v] = 1
	} else {
		s.assigns[v] = -1
	}
	s.level[v] = s.decisionLevel()
	s.reason[v] = reasonClause
	s.trail = append(s.trail, lit)
	return true
}

func (s *cdclSolver) addClause(lits []int) bool {
	// Deduplicate and check tautology
	seen := make(map[int]bool, len(lits))
	var clean []int
	for _, l := range lits {
		if seen[-l] {
			return true // tautology
		}
		if !seen[l] {
			seen[l] = true
			clean = append(clean, l)
		}
	}
	if len(clean) == 0 {
		return false
	}
	if len(clean) == 1 {
		return s.enqueue(clean[0], -1)
	}
	cid := len(s.clauses)
	s.clauses = append(s.clauses, clean)
	s.watches[litIdx(-clean[0])] = append(s.watches[litIdx(-clean[0])], cid)
	s.watches[litIdx(-clean[1])] = append(s.watches[litIdx(-clean[1])], cid)
	return true
}

func (s *cdclSolver) cancelUntil(lvl int) {
	if s.decisionLevel() <= lvl {
		return
	}
	targetTrail := s.trailLim[lvl]
	for i := len(s.trail) - 1; i >= targetTrail; i-- {
		v := litVar(s.trail[i])
		s.assigns[v] = 0
		s.reason[v] = -1
	}
	s.trail = s.trail[:targetTrail]
	s.trailLim = s.trailLim[:lvl]
	if s.qhead > len(s.trail) {
		s.qhead = len(s.trail)
	}
}

// propagate performs BCP using 2-watched literals. Returns conflicting clause index or -1.
func (s *cdclSolver) propagate() int {
	for s.qhead < len(s.trail) {
		p := s.trail[s.qhead]
		s.qhead++
		wIdx := litIdx(p)
		wList := s.watches[wIdx]
		newW := wList[:0]
		confl := -1

		for i := 0; i < len(wList); i++ {
			cid := wList[i]
			c := s.clauses[cid]
			falseLit := -p
			if c[0] == falseLit {
				c[0], c[1] = c[1], c[0]
			}
			// Now c[1] == falseLit
			if s.valLit(c[0]) == 1 {
				newW = append(newW, cid)
				continue
			}
			// Search for a new watch among c[2..]
			found := false
			for k := 2; k < len(c); k++ {
				if s.valLit(c[k]) != -1 {
					c[1], c[k] = c[k], c[1]
					s.watches[litIdx(-c[1])] = append(s.watches[litIdx(-c[1])], cid)
					found = true
					break
				}
			}
			if found {
				continue
			}
			// Could not find replacement watch -> unit or conflict
			newW = append(newW, cid)
			if s.valLit(c[0]) == -1 {
				confl = cid
				// Keep remaining watches untouched
				newW = append(newW, wList[i+1:]...)
				break
			}
			s.enqueue(c[0], cid)
		}
		s.watches[wIdx] = newW
		if confl != -1 {
			return confl
		}
	}
	return -1
}

// analyze performs 1-UIP conflict analysis.
func (s *cdclSolver) analyze(confl int) (learnt []int, backLevel int) {
	seen := make([]bool, s.numVars+1)
	learnt = append(learnt, 0) // slot 0 reserved for asserting literal
	pathC := 0
	p := 0
	idx := len(s.trail) - 1

	c := s.clauses[confl]
	for {
		start := 0
		if p != 0 {
			start = 1
		}
		for j := start; j < len(c); j++ {
			q := c[j]
			qv := litVar(q)
			if !seen[qv] && s.level[qv] > 0 {
				seen[qv] = true
				s.bumpActivity(qv)
				if s.level[qv] == s.decisionLevel() {
					pathC++
				} else {
					learnt = append(learnt, q)
				}
			}
		}

		// Find next seen literal on trail
		for idx >= 0 && !seen[litVar(s.trail[idx])] {
			idx--
		}
		if idx < 0 {
			break
		}
		p = s.trail[idx]
		idx--
		pv := litVar(p)
		seen[pv] = false
		pathC--
		if pathC <= 0 {
			break
		}
		rc := s.reason[pv]
		if rc == -1 {
			break
		}
		c = s.clauses[rc]
	}
	learnt[0] = -p

	// Compute backtrack level & put highest-level non-UIP literal at index 1 for 2-watched invariants
	if len(learnt) == 1 {
		return learnt, 0
	}
	maxI := 1
	maxLvl := s.level[litVar(learnt[1])]
	for i := 2; i < len(learnt); i++ {
		if l := s.level[litVar(learnt[i])]; l > maxLvl {
			maxLvl = l
			maxI = i
		}
	}
	learnt[1], learnt[maxI] = learnt[maxI], learnt[1]
	return learnt, maxLvl
}

func (s *cdclSolver) bumpActivity(v int) {
	s.activity[v] += s.varInc
	if s.activity[v] > 1e100 {
		for i := range s.activity {
			s.activity[i] *= 1e-100
		}
		s.varInc *= 1e-100
	}
}

func (s *cdclSolver) pickBranchVar() int {
	best := 0
	bestAct := -1.0
	for v := 1; v <= s.numVars; v++ {
		if s.assigns[v] == 0 && s.activity[v] >= bestAct {
			best = v
			bestAct = s.activity[v]
		}
	}
	return best
}

// addLearnedTheoryClause adds a blocking clause obtained from the LIA theory solver.
func (s *cdclSolver) addLearnedTheoryClause(lits []int) bool {
	s.cancelUntil(0)
	seen := make(map[int]bool, len(lits))
	var rem []int
	for _, l := range lits {
		if seen[-l] {
			return true
		}
		if seen[l] {
			continue
		}
		seen[l] = true
		v := s.valLit(l)
		if v == 1 {
			return true // already satisfied at level 0
		}
		if v == 0 {
			rem = append(rem, l)
		}
	}
	if len(rem) == 0 {
		return false
	}
	if len(rem) == 1 {
		return s.enqueue(rem[0], -1)
	}
	sort.Ints(rem)
	cid := len(s.clauses)
	s.clauses = append(s.clauses, rem)
	s.watches[litIdx(-rem[0])] = append(s.watches[litIdx(-rem[0])], cid)
	s.watches[litIdx(-rem[1])] = append(s.watches[litIdx(-rem[1])], cid)
	return true
}

// solveSAT runs CDCL until either SAT (returns true) or UNSAT (returns false).
func (s *cdclSolver) solveSAT() bool {
	for {
		confl := s.propagate()
		if confl != -1 {
			if s.decisionLevel() == 0 {
				return false
			}
			learnt, backLvl := s.analyze(confl)
			s.cancelUntil(backLvl)
			s.varInc *= 1.05
			if len(learnt) == 1 {
				if !s.enqueue(learnt[0], -1) {
					return false
				}
			} else {
				cid := len(s.clauses)
				s.clauses = append(s.clauses, learnt)
				s.watches[litIdx(-learnt[0])] = append(s.watches[litIdx(-learnt[0])], cid)
				s.watches[litIdx(-learnt[1])] = append(s.watches[litIdx(-learnt[1])], cid)
				s.enqueue(learnt[0], cid)
			}
			s.learntNum++
		} else {
			v := s.pickBranchVar()
			if v == 0 {
				return true // All variables assigned consistently
			}
			s.trailLim = append(s.trailLim, len(s.trail))
			// Branch polarity: prefer false on inequalities/gates or true on vars
			s.enqueue(-v, -1)
		}
	}
}
