package smt

import (
	"math"
	"math/big"
	"sort"
)

// TaggedAtom is a linear constraint tagged with its boolean literal ID for unsat-core extraction.
type TaggedAtom struct {
	LitID int
	Atom  LinearAtom
}

type LIAStatus int

const (
	LIASat LIAStatus = iota
	LIAUnsat
	LIAUnknown
)

type LIAResult struct {
	Status  LIAStatus
	Model   map[string]int64
	Core    []int // LitIDs participating in conflict
	Explain string
}

// CheckLIA decides feasibility over Z of a conjunction of TaggedAtoms
// using Octagon pre-filtering + Exact Rational Simplex (big.Rat) + Integer Branch-and-Bound.
func CheckLIA(tagged []TaggedAtom) LIAResult {
	// Fast check: 0-var atoms and Octagon closure
	rawAtoms := make([]LinearAtom, 0, len(tagged))
	for _, ta := range tagged {
		a := ta.Atom.Normalized()
		if len(a.Coeffs) == 0 {
			if a.Bound < 0 {
				var core []int
				if ta.LitID != 0 {
					core = []int{ta.LitID}
				}
				return LIAResult{Status: LIAUnsat, Core: core, Explain: "constant inequality false"}
			}
			continue
		}
		rawAtoms = append(rawAtoms, a)
	}

	if unsat, expl, _ := OctagonAnalyze(rawAtoms); unsat {
		// Fall through to Simplex ONLY if we need minimal LitID core, or run Simplex to get exact core!
		res := solveSimplexWithCore(tagged)
		if res.Status == LIAUnsat {
			if res.Explain == "" {
				res.Explain = expl
			}
			return res
		}
		// Octagon caught an integer parity contradiction (e.g. 2x <= 1 and -2x <= -1 -> x<=0 and x>=1)
		// Run BnB to get full integer proof & core!
		_ = expl
	}

	budget := 2000
	return solveLIA_BnB(tagged, &budget)
}

func solveLIA_BnB(tagged []TaggedAtom, budget *int) LIAResult {
	if *budget <= 0 {
		return LIAResult{Status: LIAUnknown, Explain: "BnB node budget exceeded"}
	}
	*budget--

	qRes, qModel := solveSimplexModel(tagged)
	if qRes.Status == LIAUnsat {
		return qRes
	}
	if qRes.Status != LIASat {
		return qRes
	}

	// Check integrality of all problem variables
	var fracVar string
	var fracVal *big.Rat
	var keys []string
	for k := range qModel {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		if !qModel[k].IsInt() {
			fracVar = k
			fracVal = qModel[k]
			break
		}
	}

	if fracVar == "" {
		intModel := make(map[string]int64, len(qModel))
		for k, r := range qModel {
			if !r.Num().IsInt64() {
				return LIAResult{Status: LIAUnknown, Explain: "model value exceeds 64 bits"}
			}
			intModel[k] = r.Num().Int64()
		}
		return LIAResult{Status: LIASat, Model: intModel}
	}

	// Branch on fracVar <= floor(val) OR fracVar >= ceil(val)
	fl, ok := ratFloor(fracVal)
	if !ok || fl == math.MaxInt64 {
		return LIAResult{Status: LIAUnknown, Explain: "branch bound exceeds 64 bits"}
	}
	ce := fl + 1

	left := make([]TaggedAtom, len(tagged)+1)
	copy(left, tagged)
	left[len(tagged)] = TaggedAtom{
		LitID: 0, // synthetic branch bound
		Atom:  LinearAtom{Coeffs: map[string]int64{fracVar: 1}, Bound: fl},
	}
	lRes := solveLIA_BnB(left, budget)
	if lRes.Status == LIASat {
		return lRes
	}

	right := make([]TaggedAtom, len(tagged)+1)
	copy(right, tagged)
	right[len(tagged)] = TaggedAtom{
		LitID: 0,
		Atom:  LinearAtom{Coeffs: map[string]int64{fracVar: -1}, Bound: -ce},
	}
	rRes := solveLIA_BnB(right, budget)
	if rRes.Status == LIASat {
		return rRes
	}

	if lRes.Status == LIAUnsat && rRes.Status == LIAUnsat {
		core := mergeCore(lRes.Core, rRes.Core)
		return LIAResult{Status: LIAUnsat, Core: core, Explain: "integer branch-and-bound infeasible"}
	}
	return LIAResult{Status: LIAUnknown}
}

func ratFloor(r *big.Rat) (int64, bool) {
	q := new(big.Int).Div(r.Num(), r.Denom())
	return q.Int64(), q.IsInt64()
}

func mergeCore(a, b []int) []int {
	seen := map[int]bool{}
	var out []int
	for _, x := range a {
		if x != 0 && !seen[x] {
			seen[x] = true
			out = append(out, x)
		}
	}
	for _, x := range b {
		if x != 0 && !seen[x] {
			seen[x] = true
			out = append(out, x)
		}
	}
	return out
}

func solveSimplexWithCore(tagged []TaggedAtom) LIAResult {
	r, _ := solveSimplexModel(tagged)
	return r
}

// solveSimplexModel runs exact Dutertre-de Moura General Simplex over big.Rat.
func solveSimplexModel(tagged []TaggedAtom) (LIAResult, map[string]*big.Rat) {
	varSet := map[string]bool{}
	var multi []TaggedAtom
	var single []TaggedAtom

	for _, ta := range tagged {
		a := ta.Atom.Normalized()
		nz := 0
		for _, c := range a.Coeffs {
			if c != 0 {
				nz++
			}
		}
		if nz == 0 {
			if a.Bound < 0 {
				var core []int
				if ta.LitID != 0 {
					core = []int{ta.LitID}
				}
				return LIAResult{Status: LIAUnsat, Core: core}, nil
			}
			continue
		}
		for k, c := range a.Coeffs {
			if c != 0 {
				varSet[k] = true
			}
		}
		if nz == 1 {
			single = append(single, TaggedAtom{LitID: ta.LitID, Atom: a})
		} else {
			multi = append(multi, TaggedAtom{LitID: ta.LitID, Atom: a})
		}
	}

	var probVars []string
	for v := range varSet {
		probVars = append(probVars, v)
	}
	sort.Strings(probVars)

	numProb := len(probVars)
	numSlack := len(multi)
	totalVars := numProb + numSlack
	if totalVars == 0 {
		return LIAResult{Status: LIASat, Model: map[string]int64{}}, map[string]*big.Rat{}
	}

	varIdx := make(map[string]int, numProb)
	for i, v := range probVars {
		varIdx[v] = i
	}

	hasL := make([]bool, totalVars)
	hasU := make([]bool, totalVars)
	lo := make([]*big.Rat, totalVars)
	hi := make([]*big.Rat, totalVars)
	reasonL := make([]int, totalVars)
	reasonU := make([]int, totalVars)
	val := make([]*big.Rat, totalVars)
	for i := 0; i < totalVars; i++ {
		val[i] = new(big.Rat)
	}

	// Process unary bounds on problem variables
	for _, ta := range single {
		for vname, coef := range ta.Atom.Coeffs {
			if coef == 0 {
				continue
			}
			vi := varIdx[vname]
			if coef > 0 {
				ub := floorDiv(ta.Atom.Bound, coef)
				r := big.NewRat(ub, 1)
				if !hasU[vi] || r.Cmp(hi[vi]) < 0 {
					hasU[vi] = true
					hi[vi] = r
					reasonU[vi] = ta.LitID
				}
			} else {
				r := new(big.Rat).SetInt(new(big.Int).Neg(big.NewInt(floorDiv(ta.Atom.Bound, -coef))))
				if !hasL[vi] || r.Cmp(lo[vi]) > 0 {
					hasL[vi] = true
					lo[vi] = r
					reasonL[vi] = ta.LitID
				}
			}
		}
	}

	// Check trivial unary contradiction
	for i := 0; i < numProb; i++ {
		if hasL[i] && hasU[i] && lo[i].Cmp(hi[i]) > 0 {
			core := mergeCore([]int{reasonL[i]}, []int{reasonU[i]})
			return LIAResult{Status: LIAUnsat, Core: core}, nil
		}
		if hasL[i] {
			val[i].Set(lo[i])
		} else if hasU[i] {
			val[i].Set(hi[i])
		} else {
			val[i].SetInt64(0)
		}
	}

	if numSlack == 0 {
		outModel := make(map[string]*big.Rat, numProb)
		intModel := make(map[string]int64, numProb)
		for i, name := range probVars {
			outModel[name] = new(big.Rat).Set(val[i])
			if !val[i].Num().IsInt64() {
				return LIAResult{Status: LIAUnknown, Explain: "model value exceeds 64 bits"}, nil
			}
			intModel[name] = val[i].Num().Int64()
		}
		return LIAResult{Status: LIASat, Model: intModel}, outModel
	}

	// Build Simplex tableau:
	// Non-basic initially = 0..numProb-1
	// Basic initially = numProb..totalVars-1 (one slack s_r per multi-var inequality)
	isBasic := make([]bool, totalVars)
	basicRow := make([]int, totalVars) // var -> row index in tableau if isBasic
	rowVar := make([]int, numSlack)    // row index -> var ID
	for i := 0; i < totalVars; i++ {
		basicRow[i] = -1
	}

	tab := make([][]*big.Rat, numSlack)
	for r := 0; r < numSlack; r++ {
		sID := numProb + r
		isBasic[sID] = true
		basicRow[sID] = r
		rowVar[r] = sID
		hasU[sID] = true
		hi[sID] = big.NewRat(multi[r].Atom.Bound, 1)
		reasonU[sID] = multi[r].LitID

		tab[r] = make([]*big.Rat, totalVars)
		for j := 0; j < totalVars; j++ {
			tab[r][j] = new(big.Rat)
		}
		sum := new(big.Rat)
		for vname, coef := range multi[r].Atom.Coeffs {
			if coef == 0 {
				continue
			}
			j := varIdx[vname]
			tab[r][j].SetInt64(coef)
			prod := new(big.Rat).Mul(tab[r][j], val[j])
			sum.Add(sum, prod)
		}
		val[sID].Set(sum)
	}

	// General Simplex Loop with Bland's Rule
	const maxPivots = 5000
	for iter := 0; iter < maxPivots; iter++ {
		// Pick lowest-index basic variable violating its bounds
		pivotVar := -1
		needIncrease := false
		for v := 0; v < totalVars; v++ {
			if !isBasic[v] {
				continue
			}
			if hasL[v] && val[v].Cmp(lo[v]) < 0 {
				pivotVar = v
				needIncrease = true
				break
			}
			if hasU[v] && val[v].Cmp(hi[v]) > 0 {
				pivotVar = v
				needIncrease = false
				break
			}
		}
		if pivotVar == -1 {
			// Feasible solution over Q!
			outModel := make(map[string]*big.Rat, numProb)
			for i, name := range probVars {
				outModel[name] = new(big.Rat).Set(val[i])
			}
			return LIAResult{Status: LIASat}, outModel
		}

		r := basicRow[pivotVar]
		// Pick lowest-index non-basic variable col that can move pivotVar toward bound
		pivotCol := -1
		for col := 0; col < totalVars; col++ {
			if isBasic[col] {
				continue
			}
			aij := tab[r][col]
			sgn := aij.Sign()
			if sgn == 0 {
				continue
			}
			if needIncrease {
				if (sgn > 0 && (!hasU[col] || val[col].Cmp(hi[col]) < 0)) ||
					(sgn < 0 && (!hasL[col] || val[col].Cmp(lo[col]) > 0)) {
					pivotCol = col
					break
				}
			} else {
				if (sgn > 0 && (!hasL[col] || val[col].Cmp(lo[col]) > 0)) ||
					(sgn < 0 && (!hasU[col] || val[col].Cmp(hi[col]) < 0)) {
					pivotCol = col
					break
				}
			}
		}

		if pivotCol == -1 {
			// Infeasible over Q: extract Farkas unsat core
			var core []int
			if needIncrease && reasonL[pivotVar] != 0 {
				core = append(core, reasonL[pivotVar])
			} else if !needIncrease && reasonU[pivotVar] != 0 {
				core = append(core, reasonU[pivotVar])
			}
			for col := 0; col < totalVars; col++ {
				if isBasic[col] {
					continue
				}
				sgn := tab[r][col].Sign()
				if sgn == 0 {
					continue
				}
				if needIncrease {
					if sgn > 0 && reasonU[col] != 0 {
						core = append(core, reasonU[col])
					} else if sgn < 0 && reasonL[col] != 0 {
						core = append(core, reasonL[col])
					}
				} else {
					if sgn > 0 && reasonL[col] != 0 {
						core = append(core, reasonL[col])
					} else if sgn < 0 && reasonU[col] != 0 {
						core = append(core, reasonU[col])
					}
				}
			}
			return LIAResult{Status: LIAUnsat, Core: mergeCore(core, nil)}, nil
		}

		// PivotAndUpdate(r, pivotVar, pivotCol, targetBound)
		var target *big.Rat
		if needIncrease {
			target = lo[pivotVar]
		} else {
			target = hi[pivotVar]
		}

		// theta = (target - val[pivotVar]) / tab[r][pivotCol]
		theta := new(big.Rat).Sub(target, val[pivotVar])
		theta.Quo(theta, tab[r][pivotCol])

		val[pivotVar].Set(target)
		val[pivotCol].Add(val[pivotCol], theta)
		for k := 0; k < numSlack; k++ {
			if k == r {
				continue
			}
			bk := rowVar[k]
			if tab[k][pivotCol].Sign() != 0 {
				delta := new(big.Rat).Mul(tab[k][pivotCol], theta)
				val[bk].Add(val[bk], delta)
			}
		}

		// Update tableau: solve row r for pivotCol in terms of pivotVar & other non-basics
		// Before: pivotVar = sum_{j != pivotCol} a_{rj} x_j + a_{rc} pivotCol
		// After:  pivotCol = (1/a_{rc}) * pivotVar + sum_{j != pivotCol} (-a_{rj}/a_{rc}) x_j
		a_rc := new(big.Rat).Set(tab[r][pivotCol])
		inv_arc := new(big.Rat).Inv(a_rc)
		negInv := new(big.Rat).Neg(inv_arc)

		tab[r][pivotCol].SetInt64(0)
		for j := 0; j < totalVars; j++ {
			if j == pivotVar || j == pivotCol || isBasic[j] {
				continue
			}
			tab[r][j].Mul(tab[r][j], negInv)
		}
		tab[r][pivotVar].Set(inv_arc)

		// Substitute pivotCol out of all other rows k != r
		for k := 0; k < numSlack; k++ {
			if k == r {
				continue
			}
			coeff := new(big.Rat).Set(tab[k][pivotCol])
			if coeff.Sign() == 0 {
				continue
			}
			tab[k][pivotCol].SetInt64(0)
			for j := 0; j < totalVars; j++ {
				if j == pivotCol {
					continue
				}
				if tab[r][j].Sign() != 0 {
					term := new(big.Rat).Mul(coeff, tab[r][j])
					tab[k][j].Add(tab[k][j], term)
				}
			}
		}

		// Swap basic/non-basic metadata
		isBasic[pivotVar] = false
		basicRow[pivotVar] = -1
		isBasic[pivotCol] = true
		basicRow[pivotCol] = r
		rowVar[r] = pivotCol
	}

	return LIAResult{Status: LIAUnknown, Explain: "simplex pivot limit reached"}, nil
}
