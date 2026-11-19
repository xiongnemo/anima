package spark

import (
	"sort"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/smt"
)

// joinBranches makes env the state after a statement whose alternative
// paths ended in outs. Each out descends from env, so its path condition
// starts with env's.
//
// Which path ran is named by a fresh boolean per path rather than by the
// path conditions themselves: the arms of a match are not modelled as
// mutually exclusive, and equating a variable with the value of every arm
// whose condition holds would make the state contradictory.
func (v *verifier) joinBranches(env *symEnv, outs []*symEnv) {
	if len(outs) == 0 {
		return
	}
	if len(outs) == 1 {
		*env = *outs[0]
		return
	}
	base := len(env.pc)
	sel := make([]smt.BoolExpr, len(outs))
	for i, o := range outs {
		sel[i] = smt.BoolVar{Name: env.freshVar("path")}
		learned := o.pc
		if len(learned) >= base {
			learned = learned[base:]
		}
		env.assume(smt.Implies(sel[i], smt.And(learned...)))
	}
	env.assume(smt.Or(sel...))

	ints := map[string]smt.LinearTerm{}
	for _, k := range joinKeys(outs, func(o *symEnv) map[string]smt.LinearTerm { return o.intTerms }) {
		ints[k] = v.joinTerm(env, outs, sel, k, func(o *symEnv) map[string]smt.LinearTerm { return o.intTerms })
	}
	lens := map[string]smt.LinearTerm{}
	for _, k := range joinKeys(outs, func(o *symEnv) map[string]smt.LinearTerm { return o.listLens }) {
		lens[k] = v.joinTerm(env, outs, sel, k, func(o *symEnv) map[string]smt.LinearTerm { return o.listLens })
	}
	bools := map[string]smt.BoolExpr{}
	for _, k := range joinKeys(outs, func(o *symEnv) map[string]smt.BoolExpr { return o.boolTerms }) {
		same := true
		for _, o := range outs {
			b, ok := o.boolTerms[k]
			if first, ok0 := outs[0].boolTerms[k]; !ok || !ok0 || b.String() != first.String() {
				same = false
			}
		}
		if same {
			bools[k] = outs[0].boolTerms[k]
			continue
		}
		phi := smt.BoolVar{Name: env.freshVar("phi_" + k)}
		for i, o := range outs {
			if b, ok := o.boolTerms[k]; ok {
				env.assume(smt.Implies(sel[i], smt.And(smt.Implies(phi, b), smt.Implies(b, phi))))
			}
		}
		bools[k] = phi
	}
	// An element range or a sum bound holds after the join when every path
	// has one; the range is widened to cover them all.
	elems := map[string]smt.Interval{}
	for k, first := range outs[0].listElems {
		hull, all := first, true
		for _, o := range outs[1:] {
			iv, ok := o.listElems[k]
			if !ok {
				all = false
				break
			}
			hull.HasLo = hull.HasLo && iv.HasLo
			hull.HasHi = hull.HasHi && iv.HasHi
			if iv.Lo < hull.Lo {
				hull.Lo = iv.Lo
			}
			if iv.Hi > hull.Hi {
				hull.Hi = iv.Hi
			}
		}
		if all {
			elems[k] = hull
		}
	}
	sums := map[string]listSumInfo{}
	for k, first := range outs[0].sumInfos {
		all := true
		for _, o := range outs[1:] {
			s, ok := o.sumInfos[k]
			if !ok || s.lenTerm.String() != first.lenTerm.String() || s.elemLo != first.elemLo ||
				s.elemHi != first.elemHi || s.hasElem != first.hasElem {
				all = false
			}
		}
		if all {
			sums[k] = first
		}
	}
	for _, o := range outs {
		for k, iv := range o.intervals {
			env.intervals[k] = iv
		}
	}
	// Shared after the join: what some branch left shared.
	env.shared = map[string]bool{}
	for _, o := range outs {
		for k := range o.shared {
			env.shared[k] = true
		}
	}
	// A map length after the join: what some branch left as one.
	env.mapLens = map[string]bool{}
	for _, o := range outs {
		for k := range o.mapLens {
			env.mapLens[k] = true
		}
	}
	// An entity type is kept for a name that has it on every path.
	types := map[string]*sema.EntityType{}
	for k, t := range outs[0].entTypes {
		same := true
		for _, o := range outs[1:] {
			if o.entTypes[k] != t {
				same = false
			}
		}
		if same {
			types[k] = t
		}
	}
	env.entTypes = types
	env.intTerms, env.listLens, env.boolTerms = ints, lens, bools
	env.listElems, env.sumInfos = elems, sums
}

// joinKeys lists, in a fixed order, the names bound on at least one path.
func joinKeys[T any](outs []*symEnv, m func(*symEnv) map[string]T) []string {
	seen := map[string]bool{}
	var keys []string
	for _, o := range outs {
		for k := range m(o) {
			if !seen[k] {
				seen[k] = true
				keys = append(keys, k)
			}
		}
	}
	sort.Strings(keys)
	return keys
}

// joinTerm is the value of k after the join: the common term when every path
// agrees, else a fresh symbol equal to each path's term when that path ran.
// A path that does not bind k says nothing about it.
func (v *verifier) joinTerm(env *symEnv, outs []*symEnv, sel []smt.BoolExpr, k string, m func(*symEnv) map[string]smt.LinearTerm) smt.LinearTerm {
	first, ok0 := m(outs[0])[k]
	same := ok0
	for _, o := range outs[1:] {
		if t, ok := m(o)[k]; !ok || !ok0 || t.String() != first.String() {
			same = false
		}
	}
	if same {
		return first
	}
	phi := smt.Var(env.freshVar("phi_" + k))
	for i, o := range outs {
		if t, ok := m(o)[k]; ok {
			env.assume(smt.Implies(sel[i], smt.Eq(phi, t)))
		}
	}
	return phi
}

// matchIsTotal reports whether some arm of a match on subj always runs, so
// that no path skips the match. That is so when an arm takes anything, or
// when the subject's type is one whose exhaustiveness is a proof obligation
// of its own (verifyMatchExhaustive).
func (v *verifier) matchIsTotal(subj ast.Expr, arms []matchArmDesc) bool {
	for _, arm := range arms {
		if arm.guard != nil {
			continue
		}
		switch arm.pat.(type) {
		case *ast.WildcardPat, *ast.VarPat:
			return true
		}
	}
	switch v.info.ExprTypes[subj].(type) {
	case *sema.IntType, *sema.ADTType, sema.BoolType:
		return true
	}
	return false
}

// sortedKeys lists the keys of m in a fixed order.
func sortedKeys[T any](m map[string]T) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}
