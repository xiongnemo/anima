package smt

import (
	"fmt"
	"sort"
)

type ResultStatus int

const (
	StatusSat ResultStatus = iota
	StatusUnsat
	StatusUnknown
)

type SolveResult struct {
	Status      ResultStatus
	IntModel    map[string]int64
	BoolModel   map[string]bool
	Explain     string
	TheoryHits  int
	SATRestarts int
}

// CheckSat decides satisfiability of formula f using:
// 1. Top-level conjunct flattening + Octagon/Interval fast proof
// 2. Tseitin CNF + CDCL(LIA) with Dutertre-de Moura Simplex & Integer BnB
func CheckSat(f BoolExpr) SolveResult {
	// Flatten top-level And conjuncts for immediate Octagon check
	conjuncts := flattenAnd(f)
	var topAtoms []LinearAtom
	for _, c := range conjuncts {
		if bc, ok := c.(BoolConst); ok && !bc.Val {
			return SolveResult{Status: StatusUnsat, Explain: "boolean constant false"}
		}
		if ae, ok := c.(AtomExpr); ok {
			topAtoms = append(topAtoms, ae.Atom.Normalized())
		}
	}
	if len(topAtoms) > 0 {
		if unsat, expl, _ := OctagonAnalyze(topAtoms); unsat {
			return SolveResult{Status: StatusUnsat, Explain: expl}
		}
	}

	// Build Tseitin CNF encoding
	enc := &tseitinEncoder{
		boolVars: map[string]int{},
		atomVars: map[string]atomMapping{},
	}
	rootLit := enc.encode(f)
	enc.clauses = append(enc.clauses, []int{rootLit})

	solver := newCDCL(enc.nextVar)
	for _, cl := range enc.clauses {
		if !solver.addClause(cl) {
			return SolveResult{Status: StatusUnsat, Explain: "CDCL level-0 contradiction"}
		}
	}

	const maxTheoryLoops = 2000
	for loop := 0; loop < maxTheoryLoops; loop++ {
		sat := solver.solveSAT()
		if !sat {
			return SolveResult{
				Status:      StatusUnsat,
				Explain:     fmt.Sprintf("proved UNSAT via CDCL(LIA) in %d theory refinements", loop),
				TheoryHits:  loop,
				SATRestarts: loop,
			}
		}

		// Extract active linear inequalities from SAT assignment
		var tagged []TaggedAtom
		boolModel := make(map[string]bool, len(enc.boolVars))
		for name, vid := range enc.boolVars {
			boolModel[name] = solver.assigns[vid] == 1
		}
		for _, am := range enc.atomList {
			val := solver.assigns[am.varID]
			if val == 1 {
				tagged = append(tagged, TaggedAtom{LitID: am.varID, Atom: am.posAtom})
			} else if val == -1 {
				tagged = append(tagged, TaggedAtom{LitID: -am.varID, Atom: am.posAtom.Negate()})
			}
		}

		liaRes := CheckLIA(tagged)
		switch liaRes.Status {
		case LIASat:
			// Verify original formula evaluates to true under concrete model
			if Eval(f, liaRes.Model, boolModel) {
				return SolveResult{
					Status:      StatusSat,
					IntModel:    liaRes.Model,
					BoolModel:   boolModel,
					Explain:     "counterexample found by CDCL(LIA)",
					TheoryHits:  loop + 1,
					SATRestarts: loop,
				}
			}
			return SolveResult{Status: StatusUnknown, Explain: "model validation mismatch"}

		case LIAUnsat:
			core := liaRes.Core
			if len(core) == 0 {
				for _, ta := range tagged {
					if ta.LitID != 0 {
						core = append(core, ta.LitID)
					}
				}
			}
			if len(core) == 0 {
				return SolveResult{Status: StatusUnsat, Explain: liaRes.Explain}
			}
			block := make([]int, len(core))
			for i, lit := range core {
				block[i] = -lit
			}
			if !solver.addLearnedTheoryClause(block) {
				return SolveResult{
					Status:      StatusUnsat,
					Explain:     fmt.Sprintf("CDCL+LIA UNSAT after %d theory conflicts (%s)", loop+1, liaRes.Explain),
					TheoryHits:  loop + 1,
					SATRestarts: loop,
				}
			}

		case LIAUnknown:
			return SolveResult{Status: StatusUnknown, Explain: liaRes.Explain}
		}
	}
	return SolveResult{Status: StatusUnknown, Explain: "DPLL(T) loop limit reached"}
}

func flattenAnd(e BoolExpr) []BoolExpr {
	if ax, ok := e.(AndExpr); ok {
		var out []BoolExpr
		for _, a := range ax.Args {
			out = append(out, flattenAnd(a)...)
		}
		return out
	}
	return []BoolExpr{e}
}

type atomMapping struct {
	varID   int
	flipped bool // true if input atom was the Negate() of posAtom
	posAtom LinearAtom
}

type atomEntry struct {
	varID   int
	posAtom LinearAtom
}

type tseitinEncoder struct {
	nextVar  int
	clauses  [][]int
	boolVars map[string]int
	atomVars map[string]atomMapping
	atomList []atomEntry
}

func (e *tseitinEncoder) freshVar() int {
	e.nextVar++
	return e.nextVar
}

func (e *tseitinEncoder) getBoolVar(name string) int {
	if v, ok := e.boolVars[name]; ok {
		return v
	}
	v := e.freshVar()
	e.boolVars[name] = v
	return v
}

func (e *tseitinEncoder) getAtomLit(raw LinearAtom) int {
	norm := raw.Normalized()
	neg := norm.Negate().Normalized()

	// Choose canonical polarity so A and !A share the exact same SAT variable!
	if canFlipToPos(norm) {
		key := norm.Key()
		if am, ok := e.atomVars[key]; ok {
			return am.varID
		}
		v := e.freshVar()
		am := atomMapping{varID: v, flipped: false, posAtom: norm}
		e.atomVars[key] = am
		e.atomVars[neg.Key()] = atomMapping{varID: v, flipped: true, posAtom: norm}
		e.atomList = append(e.atomList, atomEntry{varID: v, posAtom: norm})
		return v
	}

	posKey := neg.Key()
	if am, ok := e.atomVars[posKey]; ok {
		if am.flipped {
			return am.varID
		}
		return -am.varID
	}
	v := e.freshVar()
	e.atomVars[posKey] = atomMapping{varID: v, flipped: false, posAtom: neg}
	e.atomVars[norm.Key()] = atomMapping{varID: v, flipped: true, posAtom: neg}
	e.atomList = append(e.atomList, atomEntry{varID: v, posAtom: neg})
	return -v
}

// canFlipToPos picks a deterministic canonical orientation based on first non-zero sorted var coeff > 0.
func canFlipToPos(a LinearAtom) bool {
	var keys []string
	for k, c := range a.Coeffs {
		if c != 0 {
			keys = append(keys, k)
		}
	}
	sort.Strings(keys)
	if len(keys) == 0 {
		return true
	}
	return a.Coeffs[keys[0]] > 0
}

func (e *tseitinEncoder) encode(expr BoolExpr) int {
	switch x := expr.(type) {
	case BoolConst:
		v := e.freshVar()
		if x.Val {
			e.clauses = append(e.clauses, []int{v})
		} else {
			e.clauses = append(e.clauses, []int{-v})
		}
		return v
	case BoolVar:
		return e.getBoolVar(x.Name)
	case AtomExpr:
		if len(x.Atom.Coeffs) == 0 {
			return e.encode(BoolConst{Val: x.Atom.Bound >= 0})
		}
		return e.getAtomLit(x.Atom)
	case NotExpr:
		inner := e.encode(x.Inner)
		return -inner
	case AndExpr:
		if len(x.Args) == 0 {
			return e.encode(BoolConst{Val: true})
		}
		if len(x.Args) == 1 {
			return e.encode(x.Args[0])
		}
		g := e.freshVar()
		bigCl := []int{g}
		for _, a := range x.Args {
			sl := e.encode(a)
			e.clauses = append(e.clauses, []int{-g, sl})
			bigCl = append(bigCl, -sl)
		}
		e.clauses = append(e.clauses, bigCl)
		return g
	case OrExpr:
		if len(x.Args) == 0 {
			return e.encode(BoolConst{Val: false})
		}
		if len(x.Args) == 1 {
			return e.encode(x.Args[0])
		}
		g := e.freshVar()
		bigCl := []int{-g}
		for _, a := range x.Args {
			sl := e.encode(a)
			e.clauses = append(e.clauses, []int{g, -sl})
			bigCl = append(bigCl, sl)
		}
		e.clauses = append(e.clauses, bigCl)
		return g
	}
	return e.encode(BoolConst{Val: true})
}
