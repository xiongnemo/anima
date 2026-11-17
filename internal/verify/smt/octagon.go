package smt

import (
	"fmt"
	"math"
	"sort"
)

const octInf int64 = math.MaxInt64 / 4

type Interval struct {
	HasLo bool
	HasHi bool
	Lo    int64
	Hi    int64
}

func (iv Interval) Intersect(o Interval) Interval {
	res := iv
	if o.HasLo && (!res.HasLo || o.Lo > res.Lo) {
		res.HasLo = true
		res.Lo = o.Lo
	}
	if o.HasHi && (!res.HasHi || o.Hi < res.Hi) {
		res.HasHi = true
		res.Hi = o.Hi
	}
	return res
}

func (iv Interval) Empty() bool {
	return iv.HasLo && iv.HasHi && iv.Lo > iv.Hi
}

func MulInterval(a, b Interval) Interval {
	if !a.HasLo || !a.HasHi || !b.HasLo || !b.HasHi {
		return Interval{}
	}
	prods := []int64{a.Lo * b.Lo, a.Lo * b.Hi, a.Hi * b.Lo, a.Hi * b.Hi}
	lo, hi := prods[0], prods[0]
	for _, p := range prods[1:] {
		if p < lo {
			lo = p
		}
		if p > hi {
			hi = p
		}
	}
	return Interval{HasLo: true, HasHi: true, Lo: lo, Hi: hi}
}

func DivInterval(a, b Interval) (Interval, bool) {
	if !a.HasLo || !a.HasHi || !b.HasLo || !b.HasHi {
		return Interval{}, false
	}
	if b.Lo <= 0 && b.Hi >= 0 {
		return Interval{}, false // may divide by zero
	}
	quots := []int64{a.Lo / b.Lo, a.Lo / b.Hi, a.Hi / b.Lo, a.Hi / b.Hi}
	lo, hi := quots[0], quots[0]
	for _, q := range quots[1:] {
		if q < lo {
			lo = q
		}
		if q > hi {
			hi = q
		}
	}
	return Interval{HasLo: true, HasHi: true, Lo: lo, Hi: hi}, true
}

// OctagonAnalyze runs Mine's Integer Octagon Abstract Domain (Floyd-Warshall + integer strong closure)
// on all unary and 2-variable +-x +- y <= c constraints among atoms.
func OctagonAnalyze(atoms []LinearAtom) (unsat bool, explain string, bounds map[string]Interval) {
	varSet := map[string]bool{}
	for _, a := range atoms {
		for k, c := range a.Coeffs {
			if c != 0 {
				varSet[k] = true
			}
		}
	}
	var vars []string
	for v := range varSet {
		vars = append(vars, v)
	}
	sort.Strings(vars)
	n := len(vars)
	bounds = make(map[string]Interval, n)
	if n == 0 {
		for _, a := range atoms {
			if a.Bound < 0 {
				return true, fmt.Sprintf("Octagon trivial contradiction: 0 <= %d", a.Bound), bounds
			}
		}
		return false, "", bounds
	}
	// If too many variables for O(n^3) DBM, skip octagon and let Simplex handle it.
	if n > 80 {
		return false, "", bounds
	}

	idx := make(map[string]int, n)
	for i, v := range vars {
		idx[v] = i
	}

	dim := 2 * n
	d := make([][]int64, dim)
	for i := 0; i < dim; i++ {
		d[i] = make([]int64, dim)
		for j := 0; j < dim; j++ {
			if i == j {
				d[i][j] = 0
			} else {
				d[i][j] = octInf
			}
		}
	}
	setMin := func(u, v int, w int64) {
		if w < d[u][v] {
			d[u][v] = w
		}
	}

	usedOct := 0
	for _, a := range atoms {
		var nz []string
		for k, c := range a.Coeffs {
			if c != 0 {
				nz = append(nz, k)
			}
		}
		if len(nz) == 0 {
			if a.Bound < 0 {
				return true, fmt.Sprintf("constant contradiction 0 <= %d", a.Bound), bounds
			}
			continue
		}
		if len(nz) == 1 {
			v := nz[0]
			c := a.Coeffs[v]
			i := idx[v]
			if c > 0 {
				// c * x <= b  ==>  x <= floor(b / c)
				ub := floorDiv(a.Bound, c)
				if ub < octInf/2 {
					setMin(2*i+1, 2*i, 2*ub)
					usedOct++
				}
			} else {
				// (-|c|) * x <= b  ==>  -x <= floor(b / |c|)  ==>  x >= -floor(b / |c|)
				negUb := floorDiv(a.Bound, -c)
				if negUb < octInf/2 {
					setMin(2*i, 2*i+1, 2*negUb)
					usedOct++
				}
			}
			continue
		}
		if len(nz) == 2 {
			v1, v2 := nz[0], nz[1]
			c1, c2 := a.Coeffs[v1], a.Coeffs[v2]
			if (c1 == 1 || c1 == -1) && (c2 == 1 || c2 == -1) {
				i1, i2 := idx[v1], idx[v2]
				b := a.Bound
				switch {
				case c1 == 1 && c2 == -1: // x1 - x2 <= b
					setMin(2*i2, 2*i1, b)
					setMin(2*i1+1, 2*i2+1, b)
				case c1 == -1 && c2 == 1: // x2 - x1 <= b
					setMin(2*i1, 2*i2, b)
					setMin(2*i2+1, 2*i1+1, b)
				case c1 == 1 && c2 == 1: // x1 + x2 <= b
					setMin(2*i2+1, 2*i1, b)
					setMin(2*i1+1, 2*i2, b)
				case c1 == -1 && c2 == -1: // -x1 - x2 <= b
					setMin(2*i2, 2*i1+1, b)
					setMin(2*i1, 2*i2+1, b)
				}
				usedOct++
			}
		}
	}

	if usedOct == 0 {
		return false, "", bounds
	}

	// Floyd-Warshall + integer strong closure
	for k := 0; k < dim; k++ {
		for i := 0; i < dim; i++ {
			if d[i][k] >= octInf {
				continue
			}
			for j := 0; j < dim; j++ {
				if d[k][j] >= octInf {
					continue
				}
				sum := octSafeAdd(d[i][k], d[k][j])
				if sum < d[i][j] {
					d[i][j] = sum
				}
			}
		}
		for i := 0; i < dim; i++ {
			if d[i][i] < 0 {
				varName := vars[i/2]
				return true, fmt.Sprintf("Octagon Floyd-Warshall negative cycle on %q (diagonal weight=%d < 0)", varName, d[i][i]), bounds
			}
		}
	}

	// Integer tightening on unary bounds & closure
	for i := 0; i < n; i++ {
		if d[2*i+1][2*i] < octInf {
			d[2*i+1][2*i] = 2 * floorDiv(d[2*i+1][2*i], 2)
		}
		if d[2*i][2*i+1] < octInf {
			d[2*i][2*i+1] = 2 * floorDiv(d[2*i][2*i+1], 2)
		}
		lo := -octInf
		hi := octInf
		var iv Interval
		if d[2*i+1][2*i] < octInf {
			hi = d[2*i+1][2*i] / 2
			iv.HasHi = true
			iv.Hi = hi
		}
		if d[2*i][2*i+1] < octInf {
			lo = -(d[2*i][2*i+1] / 2)
			iv.HasLo = true
			iv.Lo = lo
		}
		if iv.Empty() {
			return true, fmt.Sprintf("Octagon interval emptiness on %q: [%d..%d]", vars[i], iv.Lo, iv.Hi), bounds
		}
		bounds[vars[i]] = iv
	}
	return false, "", bounds
}

func octSafeAdd(a, b int64) int64 {
	if a >= octInf || b >= octInf {
		return octInf
	}
	if a > 0 && b > octInf-a {
		return octInf
	}
	return a + b
}
