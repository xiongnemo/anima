package spark

import (
	"fmt"
	"math"
	"reflect"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/smt"
)

type VCStatus string

const (
	VCProved  VCStatus = "PROVED"
	VCFailed  VCStatus = "FAILED"
	VCUnknown VCStatus = "UNKNOWN"
)

type VCRecord struct {
	Name           string
	Scope          string
	Span           ast.Span
	Formula        string
	Status         VCStatus
	Explain        string
	Counterexample map[string]int64
}

type Report struct {
	VCs     []VCRecord
	Proved  int
	Failed  int
	Unknown int
}

func (r *Report) OK() bool {
	return r.Failed == 0 && r.Unknown == 0
}

func (r *Report) Errors() []string {
	var errs []string
	for _, vc := range r.VCs {
		if vc.Status != VCProved {
			cex := ""
			if len(vc.Counterexample) > 0 {
				var parts []string
				for k, v := range vc.Counterexample {
					if !strings.HasPrefix(k, "__") {
						parts = append(parts, fmt.Sprintf("%s=%d", k, v))
					}
				}
				if len(parts) > 0 {
					cex = " (counterexample: " + strings.Join(parts, ", ") + ")"
				}
			}
			errs = append(errs, fmt.Sprintf("%s: SPARK %s [%s]: %s%s", vc.Span, vc.Status, vc.Name, vc.Explain, cex))
		}
	}
	return errs
}

// Verify runs Hoare WP / symbolic SSA verification across all entities, functions,
// monitors/machines, and workflow guards using AnimaSMT.
func Verify(info *sema.ProgramInfo) *Report {
	v := &verifier{
		info:   info,
		report: &Report{},
	}
	v.verifyAll()
	return v.report
}

type listSumInfo struct {
	lenTerm smt.LinearTerm
	elemLo  int64
	elemHi  int64
	hasElem bool
}

type symEnv struct {
	intTerms   map[string]smt.LinearTerm
	boolTerms  map[string]smt.BoolExpr
	intervals  map[string]smt.Interval
	listLens   map[string]smt.LinearTerm
	listElems  map[string]smt.Interval
	sumInfos   map[string]listSumInfo
	entryTerms map[string]smt.LinearTerm
	pc         []smt.BoolExpr
	// mapLens marks the entries of listLens that are the length of a map,
	// which an insertion changes.
	mapLens map[string]bool
	// entTypes gives the entity type of each variable, and field path,
	// that is bound to an entity.
	entTypes map[string]*sema.EntityType
	// shared holds the variables whose entity can also be reached another
	// way: through a second name, or inside a list, map, variant or entity.
	shared map[string]bool
	// fresh numbers the symbols this env and every clone of it invent, so
	// that two branches never use one name for two values.
	fresh *int
}

func newSymEnv() *symEnv {
	return &symEnv{
		intTerms:   map[string]smt.LinearTerm{},
		boolTerms:  map[string]smt.BoolExpr{},
		intervals:  map[string]smt.Interval{},
		listLens:   map[string]smt.LinearTerm{},
		listElems:  map[string]smt.Interval{},
		sumInfos:   map[string]listSumInfo{},
		entryTerms: map[string]smt.LinearTerm{},
		shared:     map[string]bool{},
		entTypes:   map[string]*sema.EntityType{},
		mapLens:    map[string]bool{},
		fresh:      new(int),
	}
}

func (e *symEnv) clone() *symEnv {
	c := &symEnv{
		intTerms:   make(map[string]smt.LinearTerm, len(e.intTerms)),
		boolTerms:  make(map[string]smt.BoolExpr, len(e.boolTerms)),
		intervals:  make(map[string]smt.Interval, len(e.intervals)),
		listLens:   make(map[string]smt.LinearTerm, len(e.listLens)),
		listElems:  make(map[string]smt.Interval, len(e.listElems)),
		sumInfos:   make(map[string]listSumInfo, len(e.sumInfos)),
		entryTerms: e.entryTerms,
		shared:     make(map[string]bool, len(e.shared)),
		pc:         append([]smt.BoolExpr{}, e.pc...),
		fresh:      e.fresh,
	}
	for k := range e.shared {
		c.shared[k] = true
	}
	c.mapLens = make(map[string]bool, len(e.mapLens))
	for k := range e.mapLens {
		c.mapLens[k] = true
	}
	c.entTypes = make(map[string]*sema.EntityType, len(e.entTypes))
	for k, t := range e.entTypes {
		c.entTypes[k] = t
	}
	for k, v := range e.intTerms {
		c.intTerms[k] = v.Clone()
	}
	for k, v := range e.boolTerms {
		c.boolTerms[k] = v
	}
	for k, v := range e.intervals {
		c.intervals[k] = v
	}
	for k, v := range e.listLens {
		c.listLens[k] = v.Clone()
	}
	for k, v := range e.listElems {
		c.listElems[k] = v
	}
	for k, v := range e.sumInfos {
		c.sumInfos[k] = v
	}
	return c
}

func (e *symEnv) freshVar(prefix string) string {
	*e.fresh++
	return fmt.Sprintf("__%s_%d", prefix, *e.fresh)
}

// unbind drops every binding of name, so a callee parameter cannot resolve to a caller variable of the same name.
func (e *symEnv) unbind(name string) {
	under := func(k string) bool { return k == name || strings.HasPrefix(k, name+".") }
	e.forgetKeysOf(name)
	for k := range e.intTerms {
		if under(k) {
			delete(e.intTerms, k)
		}
	}
	for k := range e.boolTerms {
		if under(k) {
			delete(e.boolTerms, k)
		}
	}
	for k := range e.listLens {
		if under(k) {
			delete(e.listLens, k)
		}
	}
	for k := range e.listElems {
		if under(k) {
			delete(e.listElems, k)
		}
	}
	for k := range e.sumInfos {
		if under(k) {
			delete(e.sumInfos, k)
		}
	}
	for k := range e.entTypes {
		if under(k) {
			delete(e.entTypes, k)
		}
	}
	for k := range e.mapLens {
		if under(k) {
			delete(e.mapLens, k)
		}
	}
}

// rename moves what is bound under one program name to another, keeping the symbols.
func (e *symEnv) rename(from, to string) {
	move := func(k string) (string, bool) {
		if k == from || strings.HasPrefix(k, from+".") {
			return to + k[len(from):], true
		}
		return "", false
	}
	for k, t := range e.intTerms {
		if nk, ok := move(k); ok {
			delete(e.intTerms, k)
			e.intTerms[nk] = t
		}
	}
	for k, b := range e.boolTerms {
		if nk, ok := move(k); ok {
			delete(e.boolTerms, k)
			e.boolTerms[nk] = b
		}
	}
	for k, t := range e.listLens {
		if nk, ok := move(k); ok {
			delete(e.listLens, k)
			e.listLens[nk] = t
		}
	}
	for k, iv := range e.listElems {
		if nk, ok := move(k); ok {
			delete(e.listElems, k)
			e.listElems[nk] = iv
		}
	}
	for k, si := range e.sumInfos {
		if nk, ok := move(k); ok {
			delete(e.sumInfos, k)
			e.sumInfos[nk] = si
		}
	}
	for k, t := range e.entTypes {
		if nk, ok := move(k); ok {
			delete(e.entTypes, k)
			e.entTypes[nk] = t
		}
	}
	for k := range e.mapLens {
		if nk, ok := move(k); ok {
			delete(e.mapLens, k)
			e.mapLens[nk] = true
		}
	}
}

// freshLen is a length nothing is known about.
func (e *symEnv) freshLen(of string) smt.LinearTerm {
	t := smt.Var(e.freshVar("len(" + of + ")"))
	// A length is counted in an int64: without the upper end, arithmetic on
	// it (len(xs) - 1) could not be shown to stay inside one.
	e.assume(smt.Ge(t, smt.Const(0)))
	e.assume(smt.FitsInt64(t))
	return t
}

// lenOf is the length of the list, string or byte view held by name. An
// unknown length gets a symbol of its own, kept until name is assigned
// again, so that it is never mistaken for the length of an earlier value.
func (e *symEnv) lenOf(name string) smt.LinearTerm {
	if t, ok := e.listLens[name]; ok {
		return t
	}
	t := e.freshLen(name)
	e.listLens[name] = t
	return t
}

func (e *symEnv) assume(b smt.BoolExpr) {
	if b != nil {
		e.pc = append(e.pc, b)
	}
}

// assumeRange records that t holds a value of the bounded type ty. The fact is attached to
// the term, not to a variable name, so it stays true after the variable is reassigned.
func (e *symEnv) assumeRange(t smt.LinearTerm, ty *sema.IntType) {
	e.assume(smt.Ge(t, smt.Const(ty.Lo)))
	e.assume(smt.Le(t, smt.Const(ty.Hi)))
}

// pathAtoms returns the linear atoms the path condition asserts unconditionally.
func (e *symEnv) pathAtoms() []smt.LinearAtom {
	var out []smt.LinearAtom
	var walk func(b smt.BoolExpr)
	walk = func(b smt.BoolExpr) {
		switch x := b.(type) {
		case smt.AtomExpr:
			out = append(out, x.Atom)
		case smt.AndExpr:
			for _, a := range x.Args {
				walk(a)
			}
		}
	}
	for _, b := range e.pc {
		walk(b)
	}
	return out
}

// fieldView is a copy of e in which every name n that expr mentions is what
// e has under prefix+n, and nothing else: a variable of e with the name of
// a field is not seen. names lists them.
func (e *symEnv) fieldView(expr ast.Expr, prefix string) (view *symEnv, names []string) {
	view = e.clone()
	seen := map[string]bool{}
	visitExprs(reflect.ValueOf(expr), func(x ast.Expr) bool {
		id, ok := x.(*ast.Ident)
		if !ok || seen[id.Name] {
			return true
		}
		seen[id.Name] = true
		names = append(names, id.Name)
		n, from := id.Name, prefix+id.Name
		view.unbind(n)
		under := func(k string) (string, bool) {
			if k == from || strings.HasPrefix(k, from+".") {
				return n + k[len(from):], true
			}
			return "", false
		}
		for k, t := range e.intTerms {
			if nk, ok := under(k); ok {
				view.intTerms[nk] = t.Clone()
			}
		}
		for k, b := range e.boolTerms {
			if nk, ok := under(k); ok {
				view.boolTerms[nk] = b
			}
		}
		for k, t := range e.listLens {
			if nk, ok := under(k); ok {
				view.listLens[nk] = t.Clone()
			}
		}
		for k, iv := range e.listElems {
			if nk, ok := under(k); ok {
				view.listElems[nk] = iv
			}
		}
		// A field with no value yet is its own symbol, the same one each time.
		if _, ok := view.intTerms[n]; !ok {
			view.intTerms[n] = smt.Var(from)
		}
		if _, ok := view.boolTerms[n]; !ok {
			view.boolTerms[n] = smt.BoolVar{Name: from}
		}
		return true
	})
	return view, names
}

func (e *symEnv) pathCond() smt.BoolExpr {
	return smt.And(e.pc...)
}

type verifier struct {
	info        *sema.ProgramInfo
	report      *Report
	curFuncName string
	// curCalls tells, for a call in the current function, whether it calls
	// a closure held in a variable; curLocals lists every name the function
	// binds (closureCalls).
	curCalls   map[*ast.CallExpr]bool
	curLocals  map[string]bool
	curDecExpr ast.Expr
	curDecTerm smt.LinearTerm
	curMutEnts []struct {
		varName string
		ent     *sema.EntityType
	}
	curEnsures []ast.Expr
	curRetType sema.Type
	fstrSpan   *ast.Span
	strParams  map[string]bool
	// assignDepth counts the assignSymbolic calls in progress.
	assignDepth int
	// effectsDone tells the next assignSymbolic that the right-hand side
	// has been checked and its effects applied already.
	effectsDone bool
	// lambdaDepth counts the lambda bodies being checked.
	lambdaDepth int
	// noInvariants makes bindVarType bind an entity without assuming its invariants.
	noInvariants bool
	// bindingEnts holds the entity types bindVarType is currently expanding.
	bindingEnts map[*sema.EntityType]bool
}

func (v *verifier) prove(name, scope string, span ast.Span, env *symEnv, goal smt.BoolExpr) {
	if bc, ok := goal.(smt.BoolConst); ok {
		if bc.Val {
			v.record(name, scope, span, goal.String(), VCProved, "tautology", nil)
			return
		}
		// A false goal still holds on a path that is never taken, as any other goal does.
		if smt.CheckSat(smt.And(smt.Int64Pins(), env.pathCond())).Status == smt.StatusUnsat {
			v.record(name, scope, span, goal.String(), VCProved, "unreachable", nil)
			return
		}
		v.record(name, scope, span, goal.String(), VCFailed, "condition is statically false", nil)
		return
	}

	query := smt.And(smt.Int64Pins(), env.pathCond(), smt.Not(goal))
	res := smt.CheckSat(query)
	smt.StripInt64Pins(res.IntModel)
	switch res.Status {
	case smt.StatusUnsat:
		v.record(name, scope, span, goal.String(), VCProved, res.Explain, nil)
	case smt.StatusSat:
		v.record(name, scope, span, goal.String(), VCFailed, "counterexample violates verification condition", res.IntModel)
	default:
		v.record(name, scope, span, goal.String(), VCUnknown, res.Explain, nil)
	}
}

func (v *verifier) record(name, scope string, span ast.Span, formula string, st VCStatus, explain string, cex map[string]int64) {
	v.report.VCs = append(v.report.VCs, VCRecord{
		Name: name, Scope: scope, Span: span, Formula: formula, Status: st, Explain: explain, Counterexample: cex,
	})
	switch st {
	case VCProved:
		v.report.Proved++
	case VCFailed:
		v.report.Failed++
	case VCUnknown:
		v.report.Unknown++
	}
}

func (v *verifier) verifyAll() {
	// 0. Entity invariants are evaluated at run time when an entity crosses a JSON boundary
	for _, d := range v.info.Program.Decls {
		if ent, ok := d.(*ast.EntityDecl); ok {
			v.verifyEntityInvariantArith(ent)
		}
	}
	// 1. Verify monitor / machine state invariants & transitions
	for _, d := range v.info.Program.Decls {
		if m, ok := d.(*ast.MachineDecl); ok {
			v.verifyMachine(m)
		}
	}
	// 2. Verify functions (AoRTE, requires/ensures, entity invariants, match exhaustiveness, loop/recursion termination)
	for _, d := range v.info.Program.Decls {
		if fn, ok := d.(*ast.FuncDecl); ok {
			v.verifyFunc(fn)
		}
	}
	// 3. Verify workflow steps & choice exhaustiveness + mutual exclusivity
	for _, d := range v.info.Program.Decls {
		if wf, ok := d.(*ast.WorkflowDecl); ok {
			v.verifyWorkflow(wf)
		}
	}
}

func (v *verifier) bindVarType(env *symEnv, name string, ty sema.Type) {
	switch t := ty.(type) {
	case *sema.IntType:
		term := smt.Var(name)
		env.intTerms[name] = term
		env.entryTerms[name] = term
		if t.IsBounded {
			env.intervals[name] = smt.Interval{HasLo: true, HasHi: true, Lo: t.Lo, Hi: t.Hi}
			env.assume(smt.Ge(term, smt.Const(t.Lo)))
			env.assume(smt.Le(term, smt.Const(t.Hi)))
		} else {
			env.assume(smt.FitsInt64(term))
		}
	case sema.BoolType:
		env.boolTerms[name] = smt.BoolVar{Name: name}
	case *sema.ListType:
		lenName := "len(" + name + ")"
		lt := smt.Var(lenName)
		env.listLens[name] = lt
		env.assume(smt.Ge(lt, smt.Const(0)))
		env.assume(smt.FitsInt64(lt))
		if t.HasCap {
			env.assume(smt.Le(lt, smt.Const(t.Cap)))
		}
		if elemInt, ok := t.Elem.(*sema.IntType); ok && elemInt.IsBounded {
			env.listElems[name] = smt.Interval{HasLo: true, HasHi: true, Lo: elemInt.Lo, Hi: elemInt.Hi}
		}
	case *sema.EntityType:
		// A field of the entity's own type is left unbound: nothing is assumed about it.
		if v.bindingEnts[t] {
			return
		}
		env.entTypes[name] = t
		if v.bindingEnts == nil {
			v.bindingEnts = map[*sema.EntityType]bool{}
		}
		v.bindingEnts[t] = true
		defer delete(v.bindingEnts, t)
		for _, f := range t.Fields {
			fPath := name + "." + f.Name
			v.bindVarType(env, fPath, f.Type)
		}
		// Assume entity invariants at entry
		if v.noInvariants {
			return
		}
		for _, inv := range t.Invariants {
			b := v.evalBoolWithPrefix(inv, env, name+".")
			env.assume(b)
		}
	}
}

// verifyEntityInvariantArith checks the arithmetic of each invariant under the field types
// and the invariants before it, which is the order the runtime short-circuits them in.
func (v *verifier) verifyEntityInvariantArith(ent *ast.EntityDecl) {
	et := v.info.Entities[ent.Name]
	if et == nil {
		return
	}
	scope := "entity:" + ent.Name
	env := newSymEnv()
	for _, f := range et.Fields {
		v.bindVarType(env, f.Name, f.Type)
	}
	for _, inv := range et.Invariants {
		v.checkArith(inv, env, scope)
		env.assume(v.evalBool(inv, env, scope))
	}
}

func (v *verifier) verifyMachine(m *ast.MachineDecl) {
	scope := m.Kind + ":" + m.Name
	baseEnv := newSymEnv()
	var cvInfo []struct {
		name string
		ty   *sema.IntType
	}
	for _, cv := range m.ControlVars {
		if ty, err := v.resolveSimpleRange(cv.Type); err == nil && ty != nil {
			cvInfo = append(cvInfo, struct {
				name string
				ty   *sema.IntType
			}{cv.Name, ty})
			v.bindVarType(baseEnv, cv.Name, ty)
		}
	}

	// Verify initial control var values satisfy initial state's invariants
	if len(m.States) > 0 {
		initEnv := newSymEnv()
		for _, cv := range m.ControlVars {
			if cv.Init != nil {
				v.checkArith(cv.Init, initEnv, scope)
				term := v.evalInt(cv.Init, initEnv, scope, true)
				initEnv.intTerms[cv.Name] = term
				if ty, err := v.resolveSimpleRange(cv.Type); err == nil && ty != nil && ty.IsBounded {
					v.prove(fmt.Sprintf("%s.init.%s_range", m.Name, cv.Name), scope, cv.Span, initEnv,
						smt.And(smt.Ge(term, smt.Const(ty.Lo)), smt.Le(term, smt.Const(ty.Hi))))
				}
			}
		}
		for _, inv := range m.States[0].Invariants {
			b := v.evalBool(inv, initEnv, scope)
			v.prove(fmt.Sprintf("%s.init.%s_invariant", m.Name, m.States[0].Name), scope, inv.GetSpan(), initEnv, b)
		}
	}

	stateInvMap := map[string][]ast.Expr{}
	for _, st := range m.States {
		stateInvMap[st.Name] = st.Invariants
	}

	for _, st := range m.States {
		for _, tr := range st.Transitions {
			tEnv := newSymEnv()
			for _, cv := range cvInfo {
				v.bindVarType(tEnv, cv.name, cv.ty)
			}
			for _, inv := range st.Invariants {
				tEnv.assume(v.evalBool(inv, tEnv, scope))
			}
			if tr.Guard != nil {
				v.checkArith(tr.Guard, tEnv, scope)
				tEnv.assume(v.evalBool(tr.Guard, tEnv, scope))
			}
			for _, bs := range tr.Body {
				v.execStmt(bs, tEnv, scope)
			}
			// Check control var bounds after transition
			for _, cv := range cvInfo {
				if cv.ty.IsBounded {
					val := tEnv.intTerms[cv.name]
					v.prove(fmt.Sprintf("%s.%s->%s.%s_bounds", m.Name, tr.Action, tr.TargetState, cv.name),
						scope, tr.Span, tEnv,
						smt.And(smt.Ge(val, smt.Const(cv.ty.Lo)), smt.Le(val, smt.Const(cv.ty.Hi))))
				}
			}
			// Check target state invariants
			for _, dstInv := range stateInvMap[tr.TargetState] {
				b := v.evalBool(dstInv, tEnv, scope)
				v.prove(fmt.Sprintf("%s.%s->%s.target_invariant", m.Name, tr.Action, tr.TargetState),
					scope, tr.Span, tEnv, b)
			}
		}
	}
}

func (v *verifier) resolveSimpleRange(te ast.TypeExpr) (*sema.IntType, error) {
	if ir, ok := te.(*ast.IntRangeType); ok {
		return sema.NewIntRange(ir.Lo, ir.Hi, ""), nil
	}
	if st, ok := te.(*ast.SimpleType); ok {
		if ty, exists := v.info.Types[st.Name]; exists {
			if it, ok := ty.(*sema.IntType); ok {
				return it, nil
			}
		}
	}
	return nil, nil
}

func (v *verifier) verifyFunc(fn *ast.FuncDecl) {
	fi := v.info.Funcs[fn.Name]
	if fi == nil {
		return
	}
	scope := "def:" + fn.Name
	env := newSymEnv()
	v.curFuncName = fn.Name
	v.curDecExpr = fn.Decreases
	v.curEnsures = fn.Ensures
	v.curRetType = fi.Type.Return
	v.curMutEnts = nil
	v.curCalls, v.curLocals = closureCalls(fi.Type.Params, fn.Body)
	v.checkParamsNotRebound(fi.Type.Params, fn.Body, scope, fn.Span)
	v.checkReadonlyWrites(fi.Type.Params, fn.Body, scope)

	for _, p := range fi.Type.Params {
		v.bindVarType(env, p.Name, p.Type)
		if p.Mut {
			if et, ok := p.Type.(*sema.EntityType); ok {
				v.curMutEnts = append(v.curMutEnts, struct {
					varName string
					ent     *sema.EntityType
				}{p.Name, et})
			}
		}
	}
	for _, req := range fn.Requires {
		env.assume(v.evalBool(req, env, scope))
	}
	if fn.Decreases != nil {
		v.curDecTerm = v.evalInt(fn.Decreases, env, scope, false)
	}

	terminated := v.execBlock(fn.Body, env, scope)
	if !terminated {
		v.checkFunctionExitContracts(env, scope, fn.Span, nil)
	}
}

func (v *verifier) checkFunctionExitContracts(env *symEnv, scope string, span ast.Span, retVal ast.Expr) {
	// 1. Return refinement range
	if retVal != nil && v.curRetType != nil {
		if it, ok := v.curRetType.(*sema.IntType); ok && it.IsBounded {
			rt := v.evalInt(retVal, env, scope, true)
			v.checkIntRange(rt, retVal, env, it, scope+".return_range", scope, span)
		}
		if adt, ok := v.curRetType.(*sema.ADTType); ok && !v.makesVariant(retVal) {
			v.checkADTConstructionRange(retVal, env, adt, scope, span)
		}
	}
	// 2. Mutable entity invariants preserved
	v.proveMutInvariants(env, scope, span)
	// 3. Ensures postconditions
	for idx, ens := range v.curEnsures {
		b := v.evalBool(ens, env, scope)
		v.prove(fmt.Sprintf("%s.ensures_%d", v.curFuncName, idx+1), scope, ens.GetSpan(), env, b)
	}
}

func (v *verifier) verifyWorkflow(wf *ast.WorkflowDecl) {
	wi := v.info.Workflows[wf.Name]
	if wi == nil {
		return
	}
	scope := "workflow:" + wf.Name
	env := newSymEnv()
	v.curFuncName = wf.Name
	v.curDecExpr = nil
	v.curEnsures = nil
	v.curRetType = wi.Return
	v.curMutEnts = nil
	v.curCalls, v.curLocals = closureCalls(wi.Params, wf.Nodes)
	v.checkParamsNotRebound(wi.Params, wf.Nodes, scope, wf.Span)
	v.checkReadonlyWrites(wi.Params, wf.Nodes, scope)

	for _, p := range wi.Params {
		v.bindVarType(env, p.Name, p.Type)
		if p.Mut {
			if et, ok := p.Type.(*sema.EntityType); ok {
				v.curMutEnts = append(v.curMutEnts, struct {
					varName string
					ent     *sema.EntityType
				}{p.Name, et})
			}
		}
	}

	flow := ast.NewFlow(wf)
	if flow.Start == nil {
		v.workflowEnds(env, scope, wf.Span)
		return
	}
	if v.execBlock(flow.Start.Body, env, scope) {
		return
	}
	v.walkWorkflow(flow, flow.Start.Target, env, scope, flow.Start.Span, map[string]bool{})
}

// walkWorkflow runs the workflow from the node called cur as the backends
// do, one path at a time: the body of a step is checked with what is known
// on the way to it, not with what the step written above it left behind. A
// choice is followed down each branch with its guard taken to hold.
func (v *verifier) walkWorkflow(flow *ast.Flow, cur string, env *symEnv, scope string, at ast.Span, onPath map[string]bool) {
	for {
		if flow.Ends(cur) {
			v.workflowEnds(env, scope, at)
			return
		}
		if onPath[cur] {
			// A loop would need an invariant, and a workflow has nowhere to state one.
			v.record(scope+".acyclic", scope, at, "false", VCFailed,
				fmt.Sprintf("the workflow comes back to %s: a loop is not verified in a workflow, write it in a function", cur), nil)
			return
		}
		onPath[cur] = true
		if st := flow.Step(cur); st != nil {
			if v.execBlock(st.Body, env, scope) {
				return
			}
			next, choice := flow.AfterStep(st)
			if choice != nil {
				v.walkChoice(flow, choice, env, scope, onPath)
				return
			}
			cur, at = next, st.Span
			continue
		}
		if cn := flow.Choice(cur); cn != nil {
			v.walkChoice(flow, cn, env, scope, onPath)
			return
		}
		if fk := flow.Fork(cur); fk != nil {
			v.execFork(fk, env, scope)
			cur, at = flow.AfterFork(), fk.Span
			continue
		}
		jn := flow.Join(cur)
		cur, at = flow.AfterJoin(jn), jn.Span
	}
}

// execFork runs the statements of the branches of a fork one branch after
// the other. Sema keeps a branch from naming a variable another one assigns
// and from writing anything in place (checkForkBranches), so every order
// in which the branches run gives what this one does.
func (v *verifier) execFork(fk *ast.ForkNode, env *symEnv, scope string) {
	for _, br := range fk.Branches {
		for _, op := range br.Ops {
			if op.Kind == ast.BranchStmt && op.Stmt != nil {
				v.execStmt(op.Stmt, env, scope)
			}
		}
	}
}

// walkChoice follows each branch of a choice. The backends take the first
// branch whose guard holds, so a branch is walked with its own guard and
// the negation of those before it.
func (v *verifier) walkChoice(flow *ast.Flow, cn *ast.ChoiceNode, env *symEnv, scope string, onPath map[string]bool) {
	guards := v.verifyChoiceNode(cn, env, scope)
	var earlier []smt.BoolExpr
	for i, br := range cn.Branches {
		benv := env.clone()
		for _, g := range earlier {
			benv.assume(smt.Not(g))
		}
		if !br.IsElse {
			benv.assume(guards[i])
			earlier = append(earlier, guards[i])
		}
		path := make(map[string]bool, len(onPath))
		for k := range onPath {
			path[k] = true
		}
		v.walkWorkflow(flow, br.Target, benv, scope, br.Span, path)
		if br.IsElse {
			return
		}
	}
	// With no else and no guard that holds the workflow is over:
	// choice_complete proves that this is never so.
}

// workflowEnds is the end of a path that did not return. A workflow that
// returns a value gives () there, which is of no type.
func (v *verifier) workflowEnds(env *symEnv, scope string, at ast.Span) {
	if v.curRetType != nil && v.curRetType.Kind() != sema.KindVoid {
		if smt.CheckSat(smt.And(smt.Int64Pins(), env.pathCond())).Status == smt.StatusUnsat {
			v.record(scope+".returns", scope, at, "false", VCProved, "unreachable", nil)
		} else {
			v.record(scope+".returns", scope, at, "false", VCFailed,
				fmt.Sprintf("the workflow can end here without a return, and it returns %s", v.curRetType), nil)
		}
	}
	v.checkFunctionExitContracts(env, scope, at, nil)
}

// verifyChoiceNode proves that the guards of a choice leave exactly one
// branch to take, and gives the guard of each branch (nil for else).
func (v *verifier) verifyChoiceNode(cn *ast.ChoiceNode, env *symEnv, scope string) []smt.BoolExpr {
	var guards []smt.BoolExpr
	byBranch := make([]smt.BoolExpr, len(cn.Branches))
	hasElse := false
	for i, br := range cn.Branches {
		if br.IsElse {
			hasElse = true
			continue
		}
		v.checkMutCalls([]ast.Expr{br.Guard}, env, scope, cn.Span)
		v.checkMutCaptures([]ast.Expr{br.Guard}, scope, cn.Span)
		v.checkArith(br.Guard, env, scope)
		v.evalSideEffects(br.Guard, env, scope)
		g := v.evalBool(br.Guard, env, scope)
		guards = append(guards, g)
		byBranch[i] = g
	}

	// 1. Exhaustiveness: unless `else` present, union of guards must hold
	if !hasElse && len(guards) > 0 {
		v.prove(fmt.Sprintf("%s.choice_complete", scope), scope, cn.Span, env, smt.Or(guards...))
	}

	// 2. Mutual Exclusivity: no two guards can be simultaneously true (XOR-split safety!)
	for i := 0; i < len(guards); i++ {
		for j := i + 1; j < len(guards); j++ {
			notBoth := smt.Not(smt.And(guards[i], guards[j]))
			v.prove(fmt.Sprintf("%s.choice_exclusive_%d_%d", scope, i+1, j+1), scope, cn.Span, env, notBoth)
		}
	}
	return byBranch
}

// ---------------------------------------------------------------------------
// Symbolic SSA Execution
// ---------------------------------------------------------------------------

func (v *verifier) execBlock(stmts []ast.Stmt, env *symEnv, scope string) bool {
	for _, s := range stmts {
		if v.execStmt(s, env, scope) {
			return true
		}
	}
	return false
}

func (v *verifier) execStmt(stmt ast.Stmt, env *symEnv, scope string) bool {
	groups := stmtExprGroups(stmt)
	for _, g := range groups {
		v.checkMutCalls(g, env, scope, stmt.GetSpan())
		v.checkMutCaptures(g, scope, stmt.GetSpan())
	}
	v.havocLambdaMutArgs(groups, env)
	v.checkMutAliases(groups, env, scope)
	v.noteShared(stmt, groups, env)
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		v.checkArith(s.Value, env, scope)
		// A variable with a range is taken to be in it wherever it is
		// read, so every value it is given is proved in it. A quotient
		// is proved from its operands, as they are before the assignment.
		rng := v.info.LetRanges[s]
		var before *symEnv
		if be, ok := s.Value.(*ast.BinaryExpr); ok && be.Op == "/" && rng != nil {
			before = env.clone()
		}
		v.assignSymbolic(s.Name, s.Value, env, scope, s.Span)
		if rng != nil {
			vc := scope + ".let_" + s.Name
			t, ok := env.intTerms[s.Name]
			inRange := smt.And(smt.Ge(t, smt.Const(rng.Lo)), smt.Le(t, smt.Const(rng.Hi)))
			switch {
			case !ok:
				v.prove(vc, scope, s.Span, env, smt.BoolConst{Val: false})
			case before != nil && !v.holds(env, inRange):
				v.checkIntRange(t, s.Value, before, rng, vc, scope, s.Span)
			default:
				v.prove(vc, scope, s.Span, env, inRange)
			}
		}

	case *ast.CompoundAssignStmt:
		var rhsAst ast.Expr
		op := "+"
		switch s.Op {
		case "+=":
			op = "+"
		case "-=":
			op = "-"
		case "*=":
			op = "*"
		}
		rhsAst = &ast.BinaryExpr{Span: s.Span, Op: op, Left: s.Target, Right: s.Value}
		// The target is evaluated too (`xs[10 / n] += 1`).
		v.checkArith(s.Target, env, scope)
		if ix, ok := s.Target.(*ast.IndexExpr); ok {
			v.evalSideEffects(ix.List, env, scope)
			v.evalSideEffects(ix.Index, env, scope)
			v.proveIndex(ix.List, ix.Index, v.evalInt(ix.Index, env, scope, false), false, env, scope, s.Span)
		} else if fe, ok := s.Target.(*ast.FieldExpr); ok {
			v.evalSideEffects(fe.Object, env, scope)
		}
		v.checkArith(s.Value, env, scope)
		v.evalSideEffects(s.Value, env, scope)
		if _, isInt := v.info.ExprTypes[s.Target].(*sema.IntType); isInt {
			v.proveFitsInt64(rhsAst, env, scope)
		}
		rhsTerm := v.evalInt(rhsAst, env, scope, true)
		if targetTy, ok := v.info.ExprTypes[s.Target]; ok {
			if it, ok := targetTy.(*sema.IntType); ok && it.IsBounded {
				v.checkIntRange(rhsTerm, rhsAst, env, it, scope+".assign_bounds", scope, s.Span)
			}
		}
		if id, ok := s.Target.(*ast.Ident); ok {
			env.intTerms[id.Name] = rhsTerm
		} else if _, ok := s.Target.(*ast.IndexExpr); ok {
			env.forgetElemHulls()
		} else if fe, ok := s.Target.(*ast.FieldExpr); ok {
			v.checkWrittenObject(fe.Object, fe.Field, scope, s.Span)
			if path, ok := mutArgPath(fe); ok {
				env.intTerms[path] = rhsTerm
				v.proveSharedEntity(fe.Object, env, scope, s.Span)
			} else {
				v.proveElementWrite(fe.Object, fe.Field, nil, rhsTerm, env, scope, s.Span)
			}
			v.forgetAliases(fe.Object, env)
		}

	case *ast.IndexAssignStmt:
		v.checkArith(s.List, env, scope)
		v.evalSideEffects(s.List, env, scope)
		v.checkArith(s.Index, env, scope)
		v.evalSideEffects(s.Index, env, scope)
		v.checkArith(s.Value, env, scope)
		v.evalSideEffects(s.Value, env, scope)
		// The index is evaluated before the value, the write comes last.
		v.proveIndex(s.List, s.Index, v.evalInt(s.Index, env, scope, false), true, env, scope, s.Span)
		v.proveEntityValue(s.Value, env, scope)
		v.proveElemAssign(s.List, s.Value, env, scope, s.Span)
		env.forgetElemHulls()
		if !hasFixedLen(v.info.ExprTypes[s.List]) {
			env.forgetMapLens(s.List)
			v.keyWritten(s.List, s.Index, env)
		}

	case *ast.CallStmt:
		if s.Call != nil {
			v.checkArith(s.Call, env, scope)
			v.evalSideEffects(s.Call, env, scope)
		}

	case *ast.FieldAssignStmt:
		v.checkArith(s.Object, env, scope)
		v.evalSideEffects(s.Object, env, scope)
		v.checkArith(s.Value, env, scope)
		v.evalSideEffects(s.Value, env, scope)
		v.proveEntityValue(s.Value, env, scope)
		v.checkWrittenObject(s.Object, s.Field, scope, s.Span)
		path := ""
		if obj, ok := mutArgPath(s.Object); ok {
			path = obj + "." + s.Field
		}
		rhsTerm := v.evalInt(s.Value, env, scope, true)
		if path == "" {
			v.proveElementWrite(s.Object, s.Field, s.Value, rhsTerm, env, scope, s.Span)
		}
		if objTy, ok := v.info.ExprTypes[s.Object]; ok {
			if et, ok := objTy.(*sema.EntityType); ok {
				if ft, ok := et.FieldMap[s.Field]; ok {
					if it, ok := ft.(*sema.IntType); ok && it.IsBounded {
						v.checkIntRange(rhsTerm, s.Value, env, it, scope+".field_"+path+"_bounds", scope, s.Span)
					}
				}
			}
		}
		if path != "" {
			// Nothing known about the old value of the field, or of what
			// was inside it, is true of the new one.
			v.setField(path, s.Value, rhsTerm, env, scope, s.Span)
			v.proveSharedEntity(s.Object, env, scope, s.Span)
		}
		v.forgetAliases(s.Object, env)

	case *ast.IfStmt:
		curEnv := env.clone()
		var outs []*symEnv
		for _, br := range s.Branches {
			v.checkArith(br.Cond, curEnv, scope)
			v.evalSideEffects(br.Cond, curEnv, scope)
			cond := v.evalBool(br.Cond, curEnv, scope)
			thenEnv := curEnv.clone()
			thenEnv.assume(cond)
			if !v.execBlock(br.Body, thenEnv, scope) {
				outs = append(outs, thenEnv)
			}
			curEnv.assume(smt.Not(cond))
		}
		// curEnv is now the path on which no condition held.
		if len(s.Else) == 0 || !v.execBlock(s.Else, curEnv, scope) {
			outs = append(outs, curEnv)
		}
		if len(outs) == 0 {
			return true
		}
		v.joinBranches(env, outs)

	case *ast.MatchStmt:
		v.checkArith(s.Subject, env, scope)
		v.evalSideEffects(s.Subject, env, scope)
		arms := extractMatchArmsFromStmt(s.Arms)
		v.verifyMatchExhaustive(s.Subject, arms, env, scope, s.Span)
		// A guard may run, and change what it is given as mut, without its arm.
		for _, arm := range s.Arms {
			v.havocMutArgs(arm.Guard, env)
		}
		var outs []*symEnv
		for _, arm := range s.Arms {
			armEnv := env.clone()
			v.assumePattern(arm.Pattern, s.Subject, armEnv, scope)
			if arm.Guard != nil {
				v.checkArith(arm.Guard, armEnv, scope)
				v.evalSideEffects(arm.Guard, armEnv, scope)
				armEnv.assume(v.evalBool(arm.Guard, armEnv, scope))
			}
			if !v.execBlock(arm.Body, armEnv, scope) {
				outs = append(outs, armEnv)
			}
		}
		if !v.matchIsTotal(s.Subject, arms) {
			outs = append(outs, env.clone())
		}
		if len(outs) == 0 {
			return true
		}
		v.joinBranches(env, outs)

	case *ast.WhileStmt:
		// 1. Prove invariant holds at entry
		for i, inv := range s.Invariants {
			v.prove(fmt.Sprintf("%s.loop_inv_entry_%d", scope, i+1), scope, inv.GetSpan(), env, v.evalBool(inv, env, scope))
		}
		// 2. Inductive step from an arbitrary iteration: only the invariants are known there.
		stepEnv := env.clone()
		v.havocAssigned(s.Body, stepEnv)
		v.havocMutArgs(s.Cond, stepEnv)
		for _, inv := range s.Invariants {
			stepEnv.assume(v.evalBool(inv, stepEnv, scope))
		}
		v.checkArith(s.Cond, stepEnv, scope)
		v.evalSideEffects(s.Cond, stepEnv, scope)
		exitEnv := stepEnv.clone()
		stepEnv.assume(v.evalBool(s.Cond, stepEnv, scope))

		var decBefore smt.LinearTerm
		if s.Decreases != nil {
			decBefore = v.evalInt(s.Decreases, stepEnv, scope, false)
			v.prove(scope+".loop_decreases_nonneg", scope, s.Decreases.GetSpan(), stepEnv, smt.Ge(decBefore, smt.Const(0)))
		}
		if !v.execBlock(s.Body, stepEnv, scope) {
			for i, inv := range s.Invariants {
				v.prove(fmt.Sprintf("%s.loop_inv_step_%d", scope, i+1), scope, inv.GetSpan(), stepEnv, v.evalBool(inv, stepEnv, scope))
			}
			if s.Decreases != nil {
				decAfter := v.evalInt(s.Decreases, stepEnv, scope, false)
				v.prove(scope+".loop_decreases_strict", scope, s.Decreases.GetSpan(), stepEnv, smt.Lt(decAfter, decBefore))
			}
		}
		// 3. After the loop: invariants and the negated condition, on the same arbitrary state.
		exitEnv.assume(smt.Not(v.evalBool(s.Cond, exitEnv, scope)))
		*env = *exitEnv

	case *ast.ForStmt:
		v.checkArith(s.Iterable, env, scope)
		v.evalSideEffects(s.Iterable, env, scope)
		var lo, hi *smt.LinearTerm
		if r, ok := s.Iterable.(*ast.RangeExpr); ok {
			l, h := v.evalInt(r.Lo, env, scope, true), v.evalInt(r.Hi, env, scope, true)
			lo, hi = &l, &h
		}
		// The body is checked from an arbitrary iteration, and nothing the loop assigns, its
		// variable included, is known once it is over.
		v.havocAssigned([]ast.Stmt{s}, env)
		loopEnv := env.clone()
		if lo != nil {
			loopEnv.unbind(s.Var)
			iv := smt.Var(loopEnv.freshVar(s.Var))
			loopEnv.intTerms[s.Var] = iv
			loopEnv.assume(smt.Ge(iv, *lo))
			loopEnv.assume(smt.Lt(iv, *hi))
		} else {
			var elem sema.Type
			if lt, ok := v.info.ExprTypes[s.Iterable].(*sema.ListType); ok {
				elem = lt.Elem
			}
			v.bindFresh(loopEnv, s.Var, elem)
			// What is known of the elements is known of each one.
			if _, isInt := elem.(*sema.IntType); isInt {
				if iv := v.pipeElemInterval(s.Iterable, loopEnv, scope); iv.HasLo && iv.HasHi {
					t := loopEnv.intTerms[s.Var]
					loopEnv.assume(smt.Ge(t, smt.Const(iv.Lo)))
					loopEnv.assume(smt.Le(t, smt.Const(iv.Hi)))
				}
			}
		}
		v.execBlock(s.Body, loopEnv, scope)

	case *ast.ReturnStmt:
		if s.Value != nil {
			v.checkArith(s.Value, env, scope)
			v.evalSideEffects(s.Value, env, scope)
			v.proveEntityValue(s.Value, env, scope)
			if rTerm := v.tryEvalInt(s.Value, env); rTerm != nil {
				env.intTerms["result"] = *rTerm
			}
			// A boolean result is read as a boolean by an ensures clause
			// that compares it (evalEquality).
			if t := v.info.ExprTypes[s.Value]; t != nil && t.Kind() == sema.KindBool {
				env.boolTerms["result"] = v.evalBool(s.Value, env, scope)
			} else {
				delete(env.boolTerms, "result")
			}
		}
		v.checkFunctionExitContracts(env, scope, s.Span, s.Value)
		return true

	case *ast.ExprStmt:
		v.checkArith(s.Expr, env, scope)
		v.evalSideEffects(s.Expr, env, scope)
	}
	return false
}

// assignTarget stands for the assigned variable while the new value is
// worked out, so that the right-hand side still reads the old one.
const assignTarget = "\x00assigned"

// assignSymbolic makes name hold the value of rhs. Nothing known about the
// old value survives: what the kernel cannot work out about the new one is
// an arbitrary value of its type.
func (v *verifier) assignSymbolic(name string, rhs ast.Expr, env *symEnv, scope string, span ast.Span) {
	// A value being worked out may itself assign an entity to one of its
	// fields, so each level has a temporary of its own.
	target := fmt.Sprintf("%s%d", assignTarget, v.assignDepth)
	v.assignDepth++
	v.assignValue(target, rhs, env, scope, span)
	v.assignDepth--
	env.unbind(name)
	ty := v.info.ExprTypes[rhs]
	switch ty.(type) {
	case *sema.EntityType, *sema.ListType:
		// The invariants are assumed for a value whose producer proved
		// them; another variable's entity may be in the middle of an update.
		saved := v.noInvariants
		v.noInvariants = !v.entityHolds(rhs)
		v.bindFresh(env, name, ty)
		v.noInvariants = saved
	}
	env.rename(target, name)
	_, isInt := env.intTerms[name]
	_, isBool := env.boolTerms[name]
	if _, isList := env.listLens[name]; !isInt && !isBool && !isList {
		v.bindFresh(env, name, ty)
	}
}

// setField makes the field at path hold value, whose integer reading is
// term. An entity or list is assigned as a variable would be, so that what
// was known under the old value is gone.
func (v *verifier) setField(path string, value ast.Expr, term smt.LinearTerm, env *symEnv, scope string, span ast.Span) {
	switch v.info.ExprTypes[value].(type) {
	case *sema.EntityType, *sema.ListType:
		v.effectsDone = true
		v.assignSymbolic(path, value, env, scope, span)
	case sema.BoolType:
		env.unbind(path)
		env.boolTerms[path] = v.evalBool(value, env, scope)
	default:
		// A string or a byte view is as long as the value it is given.
		lt, known := v.lenOfValue(value, env)
		if !known {
			lt, known = v.newViewLen(value, env, scope)
		}
		env.unbind(path)
		env.intTerms[path] = term
		if known {
			env.listLens[path] = lt
		}
	}
}

// isConstructorCall reports whether e builds a new entity.
func (v *verifier) isConstructorCall(e ast.Expr) bool {
	call, ok := e.(*ast.CallExpr)
	if !ok {
		return false
	}
	id, ok := call.Callee.(*ast.Ident)
	return ok && v.info.Entities[id.Name] != nil
}

func (v *verifier) assignValue(name string, rhs ast.Expr, env *symEnv, scope string, span ast.Span) {
	if !v.effectsDone {
		v.evalSideEffects(rhs, env, scope)
	}
	v.effectsDone = false

	// Propagate pipe list lengths & element intervals
	if pe, ok := rhs.(*ast.PipeExpr); ok {
		v.propagatePipeMeta(name, pe, env, scope)
		if _, has := env.intTerms[name]; has {
			if rhsTy, ok := v.info.ExprTypes[rhs]; ok {
				if rt, ok := rhsTy.(*sema.IntType); ok && rt.IsBounded {
					env.assumeRange(env.intTerms[name], rt)
				}
			}
			return
		}
		if _, has := env.listLens[name]; has {
			return
		}
	}

	if rhsTy, ok := v.info.ExprTypes[rhs]; ok {
		switch rt := rhsTy.(type) {
		case *sema.IntType:
			t := v.evalInt(rhs, env, scope, false)
			env.intTerms[name] = t
			if rt.IsBounded {
				env.assumeRange(t, rt)
			}
			return
		case sema.BoolType:
			env.boolTerms[name] = v.evalBool(rhs, env, scope)
			return
		case *sema.EntityType:
			// A second name for an entity, or a copy with some fields
			// replaced, starts from what is known of the original.
			src := rhs
			with, isWith := rhs.(*ast.WithExpr)
			if isWith {
				src = with.Base
			}
			if from, ok := mutArgPath(src); ok {
				env.copyEntityFacts(from, name)
			}
			if isWith {
				for _, f := range with.Fields {
					env.unbind(name + "." + f.Name)
					if t := v.tryEvalInt(f.Value, env); t != nil {
						v.setField(name+"."+f.Name, f.Value, *t, env, scope, span)
					} else {
						v.setField(name+"."+f.Name, f.Value, smt.Var(env.freshVar("field")), env, scope, span)
					}
				}
			}
			if ce, ok := rhs.(*ast.CallExpr); ok && v.isConstructorCall(rhs) {
				for i, arg := range ce.Args {
					field := arg.Name
					if field == "" && i < len(rt.Fields) {
						field = rt.Fields[i].Name
					}
					if field != "" {
						if t := v.tryEvalInt(arg.Value, env); t != nil {
							env.intTerms[name+"."+field] = *t
						}
						if lt, ok := v.lenOfValue(arg.Value, env); ok {
							env.listLens[name+"."+field] = lt
						} else if lt, ok := v.newViewLen(arg.Value, env, scope); ok {
							env.listLens[name+"."+field] = lt
						}
					}
				}
			}
			return
		case *sema.ListType:
			if ll, ok := rhs.(*ast.ListLit); ok {
				lt := smt.Const(int64(len(ll.Elems)))
				env.listLens[name] = lt
				if iv := v.literalHull(ll, env, scope); iv.HasLo && iv.HasHi {
					env.listElems[name] = iv
				}
			} else if from, ok := mutArgPath(rhs); ok {
				// A list never changes its length, so a second name for it has the same one.
				env.listLens[name] = env.lenOf(from)
				if iv, ok := env.listElems[from]; ok {
					env.listElems[name] = iv
				}
			}
		case sema.StrType:
			if lt, ok := v.lenOfValue(rhs, env); ok {
				env.listLens[name] = lt
			}
		case *sema.MapType:
			// The keys a literal is written with are in it.
			if ml, ok := rhs.(*ast.MapLit); ok {
				for _, en := range ml.Entries {
					switch en.Key.(type) {
					case *ast.StrLit, *ast.IntLit:
						env.boolTerms[name+inMark+v.literalKey(en.Key)] = smt.BoolConst{Val: true}
					}
				}
			}
		case *sema.HandleType:
			if lt, ok := v.newViewLen(rhs, env, scope); ok {
				env.listLens[name] = lt
			}
		}
	}
	if t := v.tryEvalInt(rhs, env); t != nil {
		env.intTerms[name] = *t
	}
}

func (v *verifier) propagatePipeMeta(targetVar string, pe *ast.PipeExpr, env *symEnv, scope string) {
	// Collect chain left-to-right: base |> step1 |> step2 ...
	var chain []ast.Expr
	stageOf := map[ast.Expr]*ast.PipeExpr{}
	cur := ast.Expr(pe)
	for {
		if p, ok := cur.(*ast.PipeExpr); ok {
			chain = append([]ast.Expr{p.Right}, chain...)
			stageOf[p.Right] = p
			cur = p.Left
		} else {
			break
		}
	}
	var baseTermLen smt.LinearTerm
	if id, ok := cur.(*ast.Ident); ok {
		baseTermLen = env.lenOf(id.Name)
	} else if ll, ok := cur.(*ast.ListLit); ok {
		baseTermLen = smt.Const(int64(len(ll.Elems)))
	} else {
		baseTermLen = env.freshLen("pipe")
	}

	curLen := baseTermLen
	var curElem smt.Interval
	if id, ok := cur.(*ast.Ident); ok {
		curElem = env.listElems[id.Name]
	} else if ll, ok := cur.(*ast.ListLit); ok {
		curElem = v.literalHull(ll, env, scope)
	}
	if curTy, ok := v.info.ExprTypes[cur]; ok {
		if lt, ok := curTy.(*sema.ListType); ok {
			if it, ok := lt.Elem.(*sema.IntType); ok && it.IsBounded {
				curElem = smt.Interval{HasLo: true, HasHi: true, Lo: it.Lo, Hi: it.Hi}
			}
		}
	}

	for _, step := range chain {
		// What an earlier stage gave is not what the pipeline gives.
		delete(env.intTerms, targetVar)
		delete(env.sumInfos, targetVar)
		ce, ok := step.(*ast.CallExpr)
		if !ok {
			// `xs |> f`: whatever f gives.
			curLen, curElem = env.freshLen("pipe"), smt.Interval{}
			continue
		}
		fname := v.stageName(ce)
		switch fname {
		case "filter", "take", "drop":
			// Some of the elements it is given.
			fv := smt.Var(env.freshVar("flen"))
			env.assume(smt.Ge(fv, smt.Const(0)))
			env.assume(smt.Le(fv, curLen))
			curLen = fv
		case "map", "fold", "sum":
			// Read the list they are given below.
		default:
			// Any other stage gives a value of its own: nothing is known
			// of its length or of its elements from the list it is given.
			curLen, curElem = env.freshLen("pipe"), smt.Interval{}
		}
		switch fname {
		case "map":
			// The elements are what the lambda yields: nothing is known
			// of them when that cannot be bounded.
			curElem = v.pipeElemInterval(stageOf[step], env, scope)
		case "fold":
			if isSumFold(ce) && curElem.HasLo && curElem.HasHi {
				initT := v.evalInt(ce.Args[0].Value, env, scope, true)
				fv := smt.Var(env.freshVar("fold"))
				env.intTerms[targetVar] = fv
				env.sumInfos[targetVar] = listSumInfo{
					lenTerm: curLen,
					elemLo:  curElem.Lo,
					elemHi:  curElem.Hi,
					hasElem: true,
				}
				// Add exact linear sum bounds: init + elemLo*len <= fv <= init + elemHi*len
				env.assume(smt.Ge(fv, initT.Add(curLen.Scale(curElem.Lo))))
				env.assume(smt.Le(fv, initT.Add(curLen.Scale(curElem.Hi))))
			}
		case "sum":
			if curElem.HasLo && curElem.HasHi {
				fv := smt.Var(env.freshVar("sum"))
				env.intTerms[targetVar] = fv
				env.sumInfos[targetVar] = listSumInfo{
					lenTerm: curLen,
					elemLo:  curElem.Lo,
					elemHi:  curElem.Hi,
					hasElem: true,
				}
				env.assume(smt.Ge(fv, curLen.Scale(curElem.Lo)))
				env.assume(smt.Le(fv, curLen.Scale(curElem.Hi)))
			}
		}
		if fname == "fold" || fname == "sum" {
			// What a fold gives is not the list it is given either.
			curLen, curElem = env.freshLen("pipe"), smt.Interval{}
		}
	}
	env.listLens[targetVar] = curLen
	if curElem.HasLo && curElem.HasHi {
		env.listElems[targetVar] = curElem
	}
}

// isSumFold reports whether call is fold(init, (a, x) => a + x): the one
// fold whose result is init plus the sum of the elements.
func isSumFold(call *ast.CallExpr) bool {
	if len(call.Args) != 2 {
		return false
	}
	lam, ok := call.Args[1].Value.(*ast.LambdaExpr)
	if !ok || len(lam.Params) != 2 || lam.Params[0] == lam.Params[1] {
		return false
	}
	be, ok := lam.Body.(*ast.BinaryExpr)
	if !ok || be.Op != "+" {
		return false
	}
	l, ok := be.Left.(*ast.Ident)
	r, ok2 := be.Right.(*ast.Ident)
	if !ok || !ok2 {
		return false
	}
	return (l.Name == lam.Params[0] && r.Name == lam.Params[1]) || (l.Name == lam.Params[1] && r.Name == lam.Params[0])
}

// literalHull bounds the int elements of a list literal: the smallest
// interval that holds each of them, none when one is not bounded.
func (v *verifier) literalHull(ll *ast.ListLit, env *symEnv, scope string) smt.Interval {
	var hull smt.Interval
	for i, el := range ll.Elems {
		if _, ok := v.info.ExprTypes[el].(*sema.IntType); !ok {
			return smt.Interval{}
		}
		iv := v.termInterval(v.evalInt(el, env, scope, false), env)
		if !iv.HasLo || !iv.HasHi {
			return smt.Interval{}
		}
		if i == 0 {
			hull = iv
			continue
		}
		hull.Lo, hull.Hi = min(hull.Lo, iv.Lo), max(hull.Hi, iv.Hi)
	}
	return hull
}

func (v *verifier) evalSideEffects(expr ast.Expr, env *symEnv, scope string) {
	if expr == nil {
		return
	}
	switch e := expr.(type) {
	case *ast.BinaryExpr:
		v.evalSideEffects(e.Left, env, scope)
		switch e.Op {
		case "and", "implies", "or":
			// The right operand only runs when the left one does not decide the result.
			rEnv := env.clone()
			left := v.evalBool(e.Left, rEnv, scope)
			if e.Op == "or" {
				left = smt.Not(left)
			}
			rEnv.assume(left)
			v.evalSideEffects(e.Right, rEnv, scope)
			// Whether the right operand ran is not known afterwards.
			v.havocMutArgs(e.Right, env)
			return
		}
		v.evalSideEffects(e.Right, env, scope)
		if e.Op == "/" || e.Op == "%" {
			den := v.evalInt(e.Right, env, scope, true)
			v.prove(scope+".div_nonzero", scope, e.Span, env, smt.Neq(den, smt.Const(0)))
		}
	case *ast.IndexExpr:
		v.evalSideEffects(e.List, env, scope)
		v.evalSideEffects(e.Index, env, scope)
		v.proveIndex(e.List, e.Index, v.evalInt(e.Index, env, scope, true), false, env, scope, e.Span)
	case *ast.CallExpr:
		v.evalSideEffects(e.Callee, env, scope)
		for _, a := range e.Args {
			v.evalSideEffects(a.Value, env, scope)
		}
		// A call that blocks on the network is given a timeout it will honour.
		if te := v.info.TimeoutArgs[e]; te != nil {
			v.checkIntRange(v.evalInt(te, env, scope, false), te, env, sema.NewIntRange(1, 300_000, ""), scope+".timeout_bounds", scope, te.GetSpan())
		}
		// A variant is made with its fields in their declared ranges.
		if v.isVariantConstructor(e) {
			ty := v.info.LiteralTargets[e]
			if ty == nil {
				ty = v.info.ExprTypes[e]
			}
			if adt, ok := ty.(*sema.ADTType); ok {
				v.checkADTConstructionRange(e, env, adt, scope, e.Span)
			}
		}
		// A callee the kernel has no contract for may do anything to its
		// mut arguments.
		modelled := false
		defer func() {
			if !modelled {
				for _, a := range e.Args {
					if a.Mut {
						v.havocMutArg(a, env, false)
					}
				}
			}
		}()
		// An entity handed to a function of the program, or put into a new
		// entity or variant value, satisfies its invariants.
		if id, ok := e.Callee.(*ast.Ident); ok && (v.info.Funcs[id.Name] != nil || v.info.Entities[id.Name] != nil || v.isVariantConstructor(e)) {
			for _, a := range e.Args {
				v.proveEntityValue(a.Value, env, scope)
			}
		}
		// Check entity constructor bounds & invariants
		if id, ok := e.Callee.(*ast.Ident); ok {
			if et, isEnt := v.info.Entities[id.Name]; isEnt {
				entEnv := env.clone()
				for i, a := range e.Args {
					fname := a.Name
					if fname == "" && i < len(et.Fields) {
						fname = et.Fields[i].Name
					}
					if ft, ok := et.FieldMap[fname]; ok {
						if it, ok := ft.(*sema.IntType); ok && it.IsBounded {
							valT := v.evalInt(a.Value, env, scope, true)
							v.checkIntRange(valT, a.Value, env, it, fmt.Sprintf("%s.construct_%s.%s", scope, et.Name, fname), scope, a.Span)
							entEnv.intTerms[fname] = valT
						}
					}
				}
				for idx, inv := range et.Invariants {
					v.prove(fmt.Sprintf("%s.construct_%s_inv_%d", scope, et.Name, idx+1), scope, e.Span, entEnv, v.evalBool(inv, entEnv, scope))
				}
			}
			// Check user callee requires & parameter range bounds
			if fi, isFn := v.info.Funcs[id.Name]; isFn {
				// Arguments are evaluated in the caller's env before it is cloned, so the call env
				// inherits their assumptions and never reuses one of their fresh names.
				var binds []func(*symEnv)
				argParam, problem := argParams(fi.Type.Params, e.Args)
				if problem != "" {
					v.record(fmt.Sprintf("%s.call_%s_args", scope, id.Name), scope, e.Span, "each parameter is given once", VCFailed,
						fmt.Sprintf("in the call of %s, %s", id.Name, problem), nil)
				}
				for _, p := range fi.Type.Params {
					binds = append(binds, func(c *symEnv) { c.unbind(p.Name) })
				}
				// The string variables given for string parameters: a key the
				// caller looked up by one is the key the callee names by the other.
				strParams := map[string][]string{}
				for i, a := range e.Args {
					if argParam[i] < 0 {
						continue
					}
					p := fi.Type.Params[argParam[i]]
					if _, isStr := p.Type.(sema.StrType); !isStr {
						continue
					}
					if id, ok := a.Value.(*ast.Ident); ok {
						strParams[id.Name] = append(strParams[id.Name], p.Name)
					}
				}
				for i, a := range e.Args {
					if argParam[i] < 0 {
						continue
					}
					p := fi.Type.Params[argParam[i]]
					switch pt := p.Type.(type) {
					case *sema.MapType:
						if path, ok := mutArgPath(a.Value); ok {
							binds = append(binds, keyBinds(env, path, p.Name, strParams)...)
						}
					case *sema.IntType:
						valT := v.evalInt(a.Value, env, scope, pt.IsBounded)
						if pt.IsBounded {
							v.checkIntRange(valT, a.Value, env, pt, fmt.Sprintf("%s.call_%s_arg_%s", scope, id.Name, p.Name), scope, a.Span)
						}
						binds = append(binds, func(c *symEnv) { c.intTerms[p.Name] = valT })
					case sema.BoolType:
						valB := v.evalBool(a.Value, env, scope)
						binds = append(binds, func(c *symEnv) { c.boolTerms[p.Name] = valB })
					case sema.StrType:
						lt, known := v.lenOfValue(a.Value, env)
						if !known {
							lt = env.freshLen("arg")
						}
						binds = append(binds, func(c *symEnv) { c.listLens[p.Name] = lt })
					case *sema.HandleType:
						// A byte view is as long as the caller knows it to be.
						if isByteView(pt) {
							lt, known := v.newViewLen(a.Value, env, scope)
							if !known {
								lt = env.freshLen("arg")
							}
							binds = append(binds, func(c *symEnv) { c.listLens[p.Name] = lt })
						}
					case *sema.ListType:
						argID, _ := a.Value.(*ast.Ident)
						lt, known := v.lenOfValue(a.Value, env)
						if !known {
							lt = smt.Var(env.freshVar("arglen"))
						}
						binds = append(binds, func(c *symEnv) { c.listLens[p.Name] = lt })
						if argID != nil {
							if iv, ok := env.listElems[argID.Name]; ok {
								binds = append(binds, func(c *symEnv) { c.listElems[p.Name] = iv })
							}
						}
					case *sema.EntityType:
						argID, _ := a.Value.(*ast.Ident)
						for _, f := range pt.Fields {
							// The lists, strings and byte views in the fields are as
							// long as the caller knows.
							switch f.Type.(type) {
							case *sema.ListType, sema.StrType, *sema.HandleType:
								if argID != nil && (isByteView(f.Type) || f.Type.Kind() != sema.KindHandle) {
									lt := env.lenOf(argID.Name + "." + f.Name)
									path := p.Name + "." + f.Name
									binds = append(binds, func(c *symEnv) { c.listLens[path] = lt })
								}
							case *sema.MapType:
								if argID != nil {
									binds = append(binds, keyBinds(env, argID.Name+"."+f.Name, p.Name+"."+f.Name, strParams)...)
								}
							}
							if _, isInt := f.Type.(*sema.IntType); !isInt {
								continue
							}
							t, known := smt.LinearTerm{}, false
							if argID != nil {
								t, known = env.intTerms[argID.Name+"."+f.Name]
							}
							if !known {
								t = smt.Var(env.freshVar("argfield"))
							}
							path := p.Name + "." + f.Name
							binds = append(binds, func(c *symEnv) { c.intTerms[path] = t })
						}
					}
				}
				callEnv := env.clone()
				for _, bind := range binds {
					bind(callEnv)
				}
				for idx, req := range fi.Decl.Requires {
					v.prove(fmt.Sprintf("%s.call_%s_requires_%d", scope, id.Name, idx+1), scope, e.Span, callEnv, v.evalBool(req, callEnv, scope))
				}
				// Check recursive termination if calling self!
				if id.Name == v.curFuncName && v.curDecExpr != nil {
					v.prove(scope+".rec_decreases_nonneg", scope, e.Span, env, smt.Ge(v.curDecTerm, smt.Const(0)))
					recDec := v.evalInt(v.curDecExpr, callEnv, scope, false)
					v.prove(scope+".rec_decreases_strict", scope, e.Span, callEnv, smt.Lt(recDec, v.curDecTerm))
				}
				v.applyCallEffects(fi, e.Args, argParam, env, callEnv, scope)
				modelled = true
			}
		}
		v.checkViewCall(e, nil, env, scope)
	case *ast.PipeExpr:
		if call := v.pipedCall(e); call != nil {
			v.evalSideEffects(call, env, scope)
			return
		}
		v.evalSideEffects(e.Left, env, scope)
		v.evalSideEffects(e.Right, env, scope)
		// `off |> bv.read_u8()` is bv.read_u8(off).
		if call, ok := e.Right.(*ast.CallExpr); ok {
			v.checkViewCall(call, e.Left, env, scope)
		}
		// A map stage given to a list[int[1..9]]: what the lambda yields.
		if it := elemRange(v.info.LiteralTargets[e]); it != nil {
			iv := v.pipeElemInterval(e, env, scope)
			ok := iv.HasLo && iv.HasHi && it.Lo <= iv.Lo && iv.Hi <= it.Hi
			v.prove(scope+".list_elem_bounds", scope, e.Span, env, smt.BoolConst{Val: ok})
		}
	case *ast.RunWorkflowExpr:
		for _, a := range e.Args {
			v.evalSideEffects(a.Value, env, scope)
		}
		for _, a := range e.Args {
			v.proveEntityValue(a.Value, env, scope)
		}
		for _, a := range e.Args {
			if a.Mut {
				v.havocMutArg(a, env, v.info.Workflows[e.Name] != nil)
			}
		}
	case *ast.MatchExpr:
		v.evalSideEffects(e.Subject, env, scope)
		// Checked here so that it holds wherever the match is written.
		v.verifyMatchExhaustive(e.Subject, extractMatchArmsFromExpr(e.Arms), env, scope, e.Span)
		// Only one arm runs, and a guard may run without its arm.
		for _, arm := range e.Arms {
			v.havocMutArgs(arm.Guard, env)
		}
		for _, arm := range e.Arms {
			armEnv := env.clone()
			v.assumePattern(arm.Pattern, e.Subject, armEnv, scope)
			if arm.Guard != nil {
				v.evalSideEffects(arm.Guard, armEnv, scope)
				armEnv.assume(v.evalBool(arm.Guard, armEnv, scope))
			}
			v.evalSideEffects(arm.Value, armEnv, scope)
		}
		for _, arm := range e.Arms {
			v.havocMutArgs(arm.Value, env)
		}
		v.forgetPatternNames(e, env)
	case *ast.LambdaExpr:
		// The body is checked where its parameters are known: checkLambdaArith.
	case *ast.UnaryExpr:
		v.evalSideEffects(e.Expr, env, scope)
	case *ast.FieldExpr:
		v.evalSideEffects(e.Object, env, scope)
	case *ast.TryExpr:
		v.evalSideEffects(e.Inner, env, scope)
		// Inside a lambda `?` returns from the lambda, not from the function,
		// and `Some(x)?` or `Ok(x)?` never returns.
		if v.lambdaDepth == 0 && !v.neverFails(e.Inner) {
			v.checkTryExit(env, scope, e.Span)
		}
	case *ast.RangeExpr:
		v.evalSideEffects(e.Lo, env, scope)
		v.evalSideEffects(e.Hi, env, scope)
	case *ast.ListLit:
		for _, el := range e.Elems {
			v.evalSideEffects(el, env, scope)
			v.proveEntityValue(el, env, scope)
		}
		v.proveLiteralElems(e, env, scope)
	case *ast.MapLit:
		for _, en := range e.Entries {
			v.evalSideEffects(en.Key, env, scope)
			v.evalSideEffects(en.Value, env, scope)
			v.proveEntityValue(en.Value, env, scope)
		}
		v.proveLiteralElems(e, env, scope)
	case *ast.FStrExpr:
		for _, part := range e.Parts {
			if part.IsExpr {
				v.evalSideEffects(part.Expr, env, scope)
			}
		}
	case *ast.WithExpr:
		v.evalSideEffects(e.Base, env, scope)
		et, _ := v.info.ExprTypes[e.Base].(*sema.EntityType)
		for _, f := range e.Fields {
			v.evalSideEffects(f.Value, env, scope)
			// The copy's fields have the declared types, as a constructor's do.
			v.proveEntityValue(f.Value, env, scope)
			if et == nil {
				continue
			}
			if it, ok := et.FieldMap[f.Name].(*sema.IntType); ok && it.IsBounded {
				t := v.evalInt(f.Value, env, scope, true)
				v.checkIntRange(t, f.Value, env, it, scope+".with_"+f.Name+"_bounds", scope, e.Span)
			}
		}
	case *ast.IntLit, *ast.BoolLit, *ast.StrLit, *ast.NoneLit, *ast.Ident, *ast.OldExpr:
	default:
		// An expression kind with no case of its own: its parts are checked
		// from a copy of the state, and what they pass as mut is forgotten.
		rv := reflect.ValueOf(expr)
		if rv.Kind() == reflect.Pointer && !rv.IsNil() {
			visitExprs(rv.Elem(), func(sub ast.Expr) bool {
				v.evalSideEffects(sub, env.clone(), scope)
				return false
			})
		}
		v.havocMutArgs(expr, env)
	}
}

// checkArith proves that no integer operation the runtime performs while evaluating expr
// leaves the int64 range. Inside that range the unbounded integers of the proof and the
// 64-bit integers of the VM and native backends agree, so every other VC stays meaningful.
func (v *verifier) checkArith(expr ast.Expr, env *symEnv, scope string) {
	switch e := expr.(type) {
	case *ast.UnaryExpr:
		v.checkArith(e.Expr, env, scope)
		if _, lit := e.Expr.(*ast.IntLit); e.Op == "-" && !lit {
			v.proveFitsInt64(e, env, scope)
		}
	case *ast.BinaryExpr:
		v.checkArith(e.Left, env, scope)
		switch e.Op {
		case "and", "implies", "or":
			// The right operand only runs when the left one does not decide the result.
			rEnv := env.clone()
			left := v.evalBool(e.Left, rEnv, scope)
			if e.Op == "or" {
				left = smt.Not(left)
			}
			rEnv.assume(left)
			v.checkArith(e.Right, rEnv, scope)
		case "+", "-", "*":
			v.checkArith(e.Right, env, scope)
			if !v.isIntArith(e) {
				break
			}
			if why := v.productUnbounded(e, env, scope); e.Op == "*" && why != "" {
				v.record(scope+".int64_overflow", scope, v.arithSpan(e), "product fits in 64 bits", VCUnknown, why, nil)
				break
			}
			v.proveFitsInt64(e, env, scope)
		case "/", "%":
			v.checkArith(e.Right, env, scope)
			// The only overflowing quotient is MinInt64 / -1.
			num := v.evalInt(e.Left, env, scope, false)
			den := v.evalInt(e.Right, env, scope, false)
			v.proveArith(e, env, scope, smt.Or(smt.FitsInt64(num.Scale(-1)), smt.Neq(den, smt.Const(-1))))
		default:
			v.checkArith(e.Right, env, scope)
		}
	case *ast.FStrExpr:
		// Interpolated expressions are parsed on their own and carry no position in the file.
		outer := v.fstrSpan
		if outer == nil {
			v.fstrSpan = &e.Span
		}
		for _, part := range e.Parts {
			if part.IsExpr {
				v.checkArith(part.Expr, env, scope)
			}
		}
		v.fstrSpan = outer
	case *ast.FieldExpr:
		v.checkArith(e.Object, env, scope)
	case *ast.IndexExpr:
		v.checkArith(e.List, env, scope)
		v.checkArith(e.Index, env, scope)
	case *ast.CallExpr:
		if name := v.stageName(e); name != "" && len(e.Args) > 0 {
			if _, qualified := e.Callee.(*ast.FieldExpr); qualified {
				// fp.sum(xs) runs the same code as xs |> sum().
				stage := &ast.CallExpr{Span: e.Span, Callee: &ast.Ident{Span: e.Span, Name: name}, Args: e.Args[1:]}
				v.checkArith(&ast.PipeExpr{Span: e.Span, Left: e.Args[0].Value, Right: stage}, env, scope)
				break
			}
		}
		v.checkArith(e.Callee, env, scope)
		for _, a := range e.Args {
			v.checkArith(a.Value, env, scope)
		}
	case *ast.WithExpr:
		v.checkArith(e.Base, env, scope)
		for _, f := range e.Fields {
			v.checkArith(f.Value, env, scope)
		}
	case *ast.RunWorkflowExpr:
		for _, a := range e.Args {
			v.checkArith(a.Value, env, scope)
		}
	case *ast.LambdaExpr:
		var types []sema.Type
		if ft, ok := v.info.ExprTypes[e].(*sema.FuncType); ok {
			for _, p := range ft.Params {
				types = append(types, p.Type)
			}
		}
		v.checkLambdaArith(e, types, v.lambdaEnv(e, types, env), scope)
	case *ast.PipeExpr:
		v.checkArith(e.Left, env, scope)
		v.checkPipeStepArith(e, env, scope)
	case *ast.TryExpr:
		v.checkArith(e.Inner, env, scope)
	case *ast.RangeExpr:
		v.checkArith(e.Lo, env, scope)
		v.checkArith(e.Hi, env, scope)
	case *ast.ListLit:
		for _, el := range e.Elems {
			v.checkArith(el, env, scope)
		}
	case *ast.MapLit:
		for _, en := range e.Entries {
			v.checkArith(en.Key, env, scope)
			v.checkArith(en.Value, env, scope)
		}
	case *ast.MatchExpr:
		v.checkArith(e.Subject, env, scope)
		for _, arm := range e.Arms {
			armEnv := env.clone()
			v.assumePattern(arm.Pattern, e.Subject, armEnv, scope)
			if arm.Guard != nil {
				v.checkArith(arm.Guard, armEnv, scope)
				armEnv.assume(v.evalBool(arm.Guard, armEnv, scope))
			}
			v.checkArith(arm.Value, armEnv, scope)
		}
	}
}

// lambdaEnv binds each parameter to an arbitrary value of its type: the body runs once per
// element, on values the enclosing env knows nothing about.
func (v *verifier) lambdaEnv(lam *ast.LambdaExpr, types []sema.Type, env *symEnv) *symEnv {
	bodyEnv := env.clone()
	for i, p := range lam.Params {
		var ty sema.Type
		if i < len(types) {
			ty = types[i]
		}
		v.bindFresh(bodyEnv, p, ty)
	}
	return bodyEnv
}

// bindFresh rebinds name to an arbitrary value of type ty, or of unknown type when ty is nil.
func (v *verifier) bindFresh(env *symEnv, name string, ty sema.Type) {
	env.unbind(name)
	sym := env.freshVar(name)
	if ty != nil {
		v.bindVarType(env, sym, ty)
		env.rename(sym, name)
	}
	if _, ok := env.intTerms[name]; !ok {
		env.intTerms[name] = smt.Var(sym)
	}
	if _, ok := env.boolTerms[name]; !ok {
		env.boolTerms[name] = smt.BoolVar{Name: sym}
	}
}

// havocAssigned forgets the value of everything stmts may assign. A loop body runs an
// unknown number of times, so at the start of an iteration and after the loop such a
// variable is only known to hold some 64-bit integer. A range type narrows that when every
// assignment in stmts is a compound one, which is proved to stay inside the range.
func (v *verifier) havocAssigned(stmts []ast.Stmt, env *symEnv) {
	// An entity the loop shares on one pass is shared on the next.
	for _, name := range v.sharedIn(stmts) {
		env.shared[name] = true
	}
	v.forgetWrittenAliases(stmts, env)
	v.forgetInsertedMapLens(stmts, env)
	names, compound, lets := collectAssignedVars(stmts)
	for _, name := range names {
		if _, ok := env.intTerms[name]; ok {
			t := smt.Var(env.freshVar(name))
			env.intTerms[name] = t
			// The range each write of the variable was proved in, when
			// they all were and it is the one range.
			var rng *sema.IntType
			same := true
			proved := func(it *sema.IntType) {
				if it == nil || !it.IsBounded || (rng != nil && (it.Lo != rng.Lo || it.Hi != rng.Hi)) {
					same = false
				}
				rng = it
			}
			for _, target := range compound[name] {
				it, _ := v.info.ExprTypes[target].(*sema.IntType)
				proved(it)
			}
			for _, let := range lets[name] {
				proved(v.info.LetRanges[let])
			}
			if same && rng != nil {
				env.assumeRange(t, rng)
			} else {
				env.assume(smt.FitsInt64(t))
			}
		}
		v.forgetRest(name, env)
	}
	if writesElems(stmts) {
		env.forgetElemHulls()
	}
	// What the statements pass as mut may change on every pass too.
	v.havocMutArgs(stmts, env)
}

// forgetRest forgets what is known of the variable name beyond its integer
// value: its truth, its length and elements, the fields of the entity it is.
func (v *verifier) forgetRest(name string, env *symEnv) {
	if _, ok := env.boolTerms[name]; ok {
		env.boolTerms[name] = smt.BoolVar{Name: env.freshVar(name)}
	}
	delete(env.listLens, name)
	delete(env.listElems, name)
	delete(env.sumInfos, name)
	env.forgetKeysOf(name)
	// An entity that is assigned as a whole: everything inside it.
	for _, k := range sortedKeys(env.intTerms) {
		if strings.HasPrefix(k, name+".") {
			t := smt.Var(env.freshVar(k))
			env.intTerms[k] = t
			env.assume(smt.FitsInt64(t))
		}
	}
	for _, k := range sortedKeys(env.boolTerms) {
		if strings.HasPrefix(k, name+".") {
			env.boolTerms[k] = smt.BoolVar{Name: env.freshVar(k)}
		}
	}
	for _, k := range sortedKeys(env.listLens) {
		if strings.HasPrefix(k, name+".") {
			delete(env.listLens, k)
			delete(env.listElems, k)
		}
	}
}

// forgetPatternNames forgets the variables that the patterns of a match
// expression name: the arm that matches writes them, and the arms were run
// on copies of env.
func (v *verifier) forgetPatternNames(e *ast.MatchExpr, env *symEnv) {
	for _, arm := range e.Arms {
		visitNodes(reflect.ValueOf(arm.Pattern), func(n any) {
			vp, ok := n.(*ast.VarPat)
			if !ok {
				return
			}
			if _, ok := env.intTerms[vp.Name]; ok {
				t := smt.Var(env.freshVar(vp.Name))
				env.intTerms[vp.Name] = t
				env.assume(smt.FitsInt64(t))
			}
			v.forgetRest(vp.Name, env)
		})
	}
}

// stageName is the combinator a call names, written bare (`sum`) or through the std.fp
// module (`fp.sum`); it is empty for a method call on a value.
func (v *verifier) stageName(call *ast.CallExpr) string {
	switch c := call.Callee.(type) {
	case *ast.Ident:
		return c.Name
	case *ast.FieldExpr:
		// Sema does not type the callee of a pipeline stage, so fall back to the import table.
		switch t := v.info.ExprTypes[c.Object].(type) {
		case *sema.ModuleType:
			if t.Path == "std.fp" {
				return c.Field
			}
		case nil:
			if id, ok := c.Object.(*ast.Ident); ok && v.info.Imports[id.Name] == "std.fp" {
				return c.Field
			}
		}
	}
	return ""
}

// checkPipeStepArith covers the arithmetic a pipeline stage runs per element of pe.Left.
func (v *verifier) checkPipeStepArith(pe *ast.PipeExpr, env *symEnv, scope string) {
	var name string
	var args []ast.CallArg
	switch rhs := pe.Right.(type) {
	case *ast.CallExpr:
		args = rhs.Args
		name = v.stageName(rhs)
	case *ast.Ident:
		name = rhs.Name
	}
	list, _ := v.info.ExprTypes[pe.Left].(*sema.ListType)
	elem := v.pipeElemInterval(pe.Left, env, scope)
	maxLen, hasLen := v.pipeMaxLen(pe.Left, env)
	sumBounded := hasLen && elem.HasLo && elem.HasHi

	switch {
	case name == "sum" && len(args) == 0:
		if sumBounded {
			n := smt.Const(maxLen)
			v.proveArith(pe, env, scope, smt.And(smt.FitsInt64(n.Scale(elem.Lo)), smt.FitsInt64(n.Scale(elem.Hi))))
		} else {
			v.record(scope+".int64_overflow", scope, pe.Span, "sum fits in 64 bits", VCUnknown,
				"sum needs a list of known maximum length with bounded int elements", nil)
		}
		return
	case name == "fold" && len(args) == 2 && sumBounded:
		lam, ok := args[1].Value.(*ast.LambdaExpr)
		if !ok || !isSumLambda(lam) {
			break
		}
		// Before adding an element the accumulator is init plus the sum of k earlier ones.
		v.checkArith(args[0].Value, env, scope)
		bodyEnv := v.lambdaEnv(lam, nil, env)
		k := smt.Var(bodyEnv.freshVar("k"))
		partial := smt.Var(bodyEnv.freshVar("partial"))
		x := smt.Var(bodyEnv.freshVar(lam.Params[1]))
		bodyEnv.assume(smt.Ge(k, smt.Const(0)))
		bodyEnv.assume(smt.Lt(k, smt.Const(maxLen)))
		bodyEnv.assume(smt.Ge(partial, k.Scale(elem.Lo)))
		bodyEnv.assume(smt.Le(partial, k.Scale(elem.Hi)))
		bodyEnv.assume(smt.Ge(x, smt.Const(elem.Lo)))
		bodyEnv.assume(smt.Le(x, smt.Const(elem.Hi)))
		bodyEnv.intTerms[lam.Params[0]] = v.evalInt(args[0].Value, env, scope, false).Add(partial)
		bodyEnv.intTerms[lam.Params[1]] = x
		v.checkArith(lam.Body, bodyEnv, scope)
		v.lambdaDepth++
		v.evalSideEffects(lam.Body, bodyEnv, scope)
		v.lambdaDepth--
		return
	}

	for i, a := range args {
		lam, ok := a.Value.(*ast.LambdaExpr)
		if !ok || list == nil {
			v.checkArith(a.Value, env, scope)
			continue
		}
		switch {
		case len(lam.Params) == 1:
			v.checkLambdaArith(lam, []sema.Type{list.Elem}, v.elemLambdaEnv(lam, pe.Left, env, scope), scope)
		case name == "fold" && i == 1 && len(lam.Params) == 2:
			// The accumulator is only known to have the type of the initial value.
			types := []sema.Type{v.info.ExprTypes[args[0].Value], list.Elem}
			if it, ok := types[0].(*sema.IntType); ok && it.IsBounded {
				types[0] = sema.NewUnboundedInt()
			}
			v.checkLambdaArith(lam, types, v.lambdaEnv(lam, types, env), scope)
		default:
			v.checkArith(a.Value, env, scope)
		}
	}
}

// checkLambdaArith checks a lambda body in bodyEnv. Sema leaves the parameters of an inline
// lambda untyped, so the ones known to be strings are noted for isIntArith.
func (v *verifier) checkLambdaArith(lam *ast.LambdaExpr, types []sema.Type, bodyEnv *symEnv, scope string) {
	saved := v.strParams
	v.strParams = map[string]bool{}
	for k, b := range saved {
		v.strParams[k] = b
	}
	for i, p := range lam.Params {
		isStr := false
		if i < len(types) {
			_, isStr = types[i].(sema.StrType)
		}
		v.strParams[p] = isStr
	}
	v.checkArith(lam.Body, bodyEnv, scope)
	v.lambdaDepth++
	v.evalSideEffects(lam.Body, bodyEnv, scope)
	v.lambdaDepth--
	// What the lambda yields ends up in a list or in the caller's hands.
	v.proveEntityValue(lam.Body, bodyEnv, scope)
	v.strParams = saved
}

// isIntArith tells integer +, -, * from string concatenation, the only other use of `+`.
func (v *verifier) isIntArith(e *ast.BinaryExpr) bool {
	if e.Op != "+" {
		return true
	}
	for _, x := range []ast.Expr{e, e.Left, e.Right} {
		switch t := x.(type) {
		case *ast.StrLit, *ast.FStrExpr:
			return false
		case *ast.Ident:
			if v.strParams[t.Name] {
				return false
			}
		case *ast.BinaryExpr:
			if t != e && t.Op == "+" && !v.isIntArith(t) {
				return false
			}
		}
		if _, isStr := v.info.ExprTypes[x].(sema.StrType); isStr {
			return false
		}
	}
	return true
}

// elemLambdaEnv is lambdaEnv for a one-parameter stage lambda, with the parameter narrowed
// to the element range the earlier stages of the pipeline produce.
func (v *verifier) elemLambdaEnv(lam *ast.LambdaExpr, left ast.Expr, env *symEnv, scope string) *symEnv {
	var types []sema.Type
	if lt, ok := v.info.ExprTypes[left].(*sema.ListType); ok {
		types = []sema.Type{lt.Elem}
	}
	bodyEnv := v.lambdaEnv(lam, types, env)
	iv := v.pipeElemInterval(left, env, scope)
	t := bodyEnv.intTerms[lam.Params[0]]
	if iv.HasLo && iv.HasHi && len(t.Coeffs) == 1 && t.Const == 0 {
		for sym, c := range t.Coeffs {
			if c == 1 {
				bodyEnv.intervals[sym] = iv
				bodyEnv.assume(smt.Ge(t, smt.Const(iv.Lo)))
				bodyEnv.assume(smt.Le(t, smt.Const(iv.Hi)))
			}
		}
	}
	return bodyEnv
}

// pipeMaxLen is the largest length the list e evaluates to can have, when that is known.
func (v *verifier) pipeMaxLen(e ast.Expr, env *symEnv) (int64, bool) {
	if lt, ok := v.info.ExprTypes[e].(*sema.ListType); ok && lt.HasCap && lt.Cap >= 0 {
		return lt.Cap, true
	}
	switch x := e.(type) {
	case *ast.ListLit:
		return int64(len(x.Elems)), true
	case *ast.Ident:
		if n, ok := env.listLens[x.Name]; ok {
			if iv := v.termInterval(n, env); iv.HasHi && iv.Hi >= 0 {
				return iv.Hi, true
			}
		}
	case *ast.PipeExpr:
		call, ok := x.Right.(*ast.CallExpr)
		if !ok {
			break
		}
		if name := v.stageName(call); name == "filter" || name == "map" {
			return v.pipeMaxLen(x.Left, env)
		}
	}
	return 0, false
}

// pipeElemInterval bounds the int elements of the list e evaluates to, when it can.
func (v *verifier) pipeElemInterval(e ast.Expr, env *symEnv, scope string) smt.Interval {
	// The declared range, unless e is a new list that was given it: that
	// one is what has to be proved.
	if it := elemRange(v.info.ExprTypes[e]); it != nil && v.info.LiteralTargets[e] == nil {
		return smt.Interval{HasLo: true, HasHi: true, Lo: it.Lo, Hi: it.Hi}
	}
	switch x := e.(type) {
	case *ast.Ident:
		return env.listElems[x.Name]
	case *ast.ListLit:
		return v.literalHull(x, env, scope)
	case *ast.PipeExpr:
		call, ok := x.Right.(*ast.CallExpr)
		if !ok || len(call.Args) != 1 {
			break
		}
		lam, _ := call.Args[0].Value.(*ast.LambdaExpr)
		if lam == nil || len(lam.Params) != 1 {
			break
		}
		switch v.stageName(call) {
		case "filter":
			return v.pipeElemInterval(x.Left, env, scope)
		case "map":
			bodyEnv := v.elemLambdaEnv(lam, x.Left, env, scope)
			return v.termInterval(v.evalInt(lam.Body, bodyEnv, scope, false), bodyEnv)
		}
	}
	return smt.Interval{}
}

// isSumLambda reports whether lam is (a, b) => a + b, in either operand order.
func isSumLambda(lam *ast.LambdaExpr) bool {
	be, ok := lam.Body.(*ast.BinaryExpr)
	if !ok || be.Op != "+" || len(lam.Params) != 2 || lam.Params[0] == lam.Params[1] {
		return false
	}
	l, lok := be.Left.(*ast.Ident)
	r, rok := be.Right.(*ast.Ident)
	if !lok || !rok {
		return false
	}
	return (l.Name == lam.Params[0] && r.Name == lam.Params[1]) || (l.Name == lam.Params[1] && r.Name == lam.Params[0])
}

// productUnbounded explains why the interval approximation used for x * y cannot show the
// product fits, or returns "" when it has bounds to work with. A product with a constant
// side is linear and needs none.
func (v *verifier) productUnbounded(e *ast.BinaryExpr, env *symEnv, scope string) string {
	probe := env.clone()
	l := v.evalInt(e.Left, probe, scope, false)
	r := v.evalInt(e.Right, probe, scope, false)
	if len(l.Coeffs) == 0 || len(r.Coeffs) == 0 {
		return ""
	}
	il, ir := v.termInterval(l, probe), v.termInterval(r, probe)
	if !il.HasLo || !il.HasHi || !ir.HasLo || !ir.HasHi {
		return "cannot bound a product of two non-constant operands; give both a bounded type or a requires range"
	}
	if p := smt.MulInterval(il, ir); !p.HasLo || !p.HasHi {
		return "the operand ranges allow a product beyond 64 bits; narrow them"
	}
	return ""
}

func (v *verifier) arithSpan(e ast.Expr) ast.Span {
	if v.fstrSpan != nil {
		return *v.fstrSpan
	}
	return e.GetSpan()
}

func (v *verifier) proveFitsInt64(e ast.Expr, env *symEnv, scope string) {
	v.proveArith(e, env, scope, smt.FitsInt64(v.evalInt(e, env, scope, false)))
}

func (v *verifier) proveArith(e ast.Expr, env *symEnv, scope string, goal smt.BoolExpr) {
	if bc, ok := goal.(smt.BoolConst); ok && bc.Val {
		return
	}
	v.prove(scope+".int64_overflow", scope, v.arithSpan(e), env, goal)
}

// checkIntRange verifies lo <= expr <= hi, using exact Presburger characterization for div!
func (v *verifier) checkIntRange(term smt.LinearTerm, expr ast.Expr, env *symEnv, target *sema.IntType, vcName, scope string, span ast.Span) {
	inRange := smt.And(smt.Ge(term, smt.Const(target.Lo)), smt.Le(term, smt.Const(target.Hi)))
	// The rule below is for operands that are not negative; what is known
	// of the quotient itself may do, as for `-4 / 2`.
	if be, ok := expr.(*ast.BinaryExpr); ok && be.Op == "/" && !v.holds(env, inRange) {
		num := v.evalInt(be.Left, env, scope, false)
		den := v.evalInt(be.Right, env, scope, false)
		// Exact theorem for den >= 1 and num >= 0:
		// target.Lo <= floor(num / den) <= target.Hi  <==>  target.Lo * den <= num && num <= (target.Hi + 1) * den - 1
		parts := []smt.BoolExpr{
			smt.Ge(den, smt.Const(1)),
			smt.Ge(num, smt.Const(0)),
			smt.Le(den.Scale(target.Lo), num),
		}
		// No quotient is above the largest int, and Hi + 1 would wrap.
		if target.Hi != math.MaxInt64 {
			parts = append(parts, smt.Lt(num, den.Scale(target.Hi+1)))
		}
		v.prove(vcName, scope, span, env, smt.And(parts...))
		return
	}
	v.prove(vcName, scope, span, env, inRange)
}

// makesVariant reports whether e makes a variant, whose fields
// evalSideEffects proves in range.
func (v *verifier) makesVariant(e ast.Expr) bool {
	call, ok := e.(*ast.CallExpr)
	return ok && v.isVariantConstructor(call)
}

func (v *verifier) checkADTConstructionRange(expr ast.Expr, env *symEnv, adt *sema.ADTType, scope string, span ast.Span) {
	ce, ok := expr.(*ast.CallExpr)
	if !ok {
		return
	}
	id, ok := ce.Callee.(*ast.Ident)
	if !ok {
		return
	}
	vi, ok := adt.VariantMap[id.Name]
	if !ok {
		return
	}
	for i, arg := range ce.Args {
		var fty sema.Type
		if arg.Name != "" {
			for _, vf := range vi.Fields {
				if vf.Name == arg.Name {
					fty = vf.Type
					break
				}
			}
		} else if i < len(vi.Fields) {
			fty = vi.Fields[i].Type
		}
		// Some(x) given to an Option[int[1..9]]: the field is the type argument.
		if tv, ok := fty.(sema.TypeVar); ok {
			for j, tp := range adt.TypeParams {
				if tp == tv.Name && j < len(adt.TypeArgs) {
					fty = adt.TypeArgs[j]
				}
			}
		}
		if it, ok := fty.(*sema.IntType); ok && it.IsBounded {
			t := v.evalInt(arg.Value, env, scope, true)
			v.checkIntRange(t, arg.Value, env, it, fmt.Sprintf("%s.variant_%s_range", scope, vi.Name), scope, arg.Span)
		}
	}
}

func (v *verifier) tryEvalInt(expr ast.Expr, env *symEnv) *smt.LinearTerm {
	if expr == nil {
		return nil
	}
	t := v.evalInt(expr, env, "", false)
	return &t
}

func (v *verifier) evalInt(expr ast.Expr, env *symEnv, scope string, emitVCs bool) smt.LinearTerm {
	switch e := expr.(type) {
	case *ast.IntLit:
		return smt.Const(e.Value)
	case *ast.Ident:
		if t, ok := env.intTerms[e.Name]; ok {
			return t
		}
		return smt.Var(e.Name)
	case *ast.FieldExpr:
		if id, ok := e.Object.(*ast.Ident); ok {
			path := id.Name + "." + e.Field
			if t, ok := env.intTerms[path]; ok {
				return t
			}
			return smt.Var(path)
		}
	case *ast.OldExpr:
		if id, ok := e.Inner.(*ast.Ident); ok {
			if t, ok := env.entryTerms[id.Name]; ok {
				return t
			}
			return smt.Var("old_" + id.Name)
		}
		if fe, ok := e.Inner.(*ast.FieldExpr); ok {
			if id, ok := fe.Object.(*ast.Ident); ok {
				path := id.Name + "." + fe.Field
				if t, ok := env.entryTerms[path]; ok {
					return t
				}
				return smt.Var("old_" + path)
			}
		}
	case *ast.UnaryExpr:
		if e.Op == "-" {
			return v.evalInt(e.Expr, env, scope, emitVCs).Scale(-1)
		}
	case *ast.BinaryExpr:
		l := v.evalInt(e.Left, env, scope, emitVCs)
		r := v.evalInt(e.Right, env, scope, emitVCs)
		switch e.Op {
		case "+":
			return l.Add(r)
		case "-":
			return l.Sub(r)
		case "*":
			if len(r.Coeffs) == 0 {
				return l.Scale(r.Const)
			}
			if len(l.Coeffs) == 0 {
				return r.Scale(l.Const)
			}
			// Bounded nonlinear multiplication approximation via Interval arithmetic
			ivL := v.termInterval(l, env)
			ivR := v.termInterval(r, env)
			mv := smt.Var(env.freshVar("mul"))
			// With no bound mv stays free, so nothing about the product, not even that it
			// fits in 64 bits, can be proved.
			if prod := smt.MulInterval(ivL, ivR); prod.HasLo && prod.HasHi {
				env.assume(smt.Ge(mv, smt.Const(prod.Lo)))
				env.assume(smt.Le(mv, smt.Const(prod.Hi)))
			}
			return mv
		case "/":
			if emitVCs {
				v.prove(scope+".div_nonzero", scope, e.Span, env, smt.Neq(r, smt.Const(0)))
			}
			dv := smt.Var(env.freshVar("div"))
			env.assume(smt.FitsInt64(dv))
			ivL := v.termInterval(l, env)
			ivR := v.termInterval(r, env)
			if qiv, ok := smt.DivInterval(ivL, ivR); ok {
				env.assume(smt.Ge(dv, smt.Const(qiv.Lo)))
				env.assume(smt.Le(dv, smt.Const(qiv.Hi)))
			}
			return dv
		}
	case *ast.CallExpr:
		// bv.len() is the length of the view.
		if fe, ok := e.Callee.(*ast.FieldExpr); ok && fe.Field == "len" && len(e.Args) == 0 && isByteView(v.info.ExprTypes[fe.Object]) {
			return v.viewLen(fe.Object, env)
		}
		if id, ok := e.Callee.(*ast.Ident); ok && id.Name == "len" && len(e.Args) == 1 {
			// The length of what a variable holds, or a field of one.
			if path, ok := mutArgPath(e.Args[0].Value); ok {
				if !hasFixedLen(v.info.ExprTypes[e.Args[0].Value]) {
					env.mapLens[path] = true
				}
				return env.lenOf(path)
			}
		}
	}
	// Anything else is a value the runtime holds in an int64.
	term := smt.Var(env.freshVar("term"))
	if it, ok := v.info.ExprTypes[expr].(*sema.IntType); ok && it.IsBounded {
		env.assumeRange(term, it)
	} else {
		env.assume(smt.FitsInt64(term))
	}
	if ix, ok := expr.(*ast.IndexExpr); ok {
		if iv, ok := v.elemHull(ix, env); ok {
			env.assume(smt.Ge(term, smt.Const(iv.Lo)))
			env.assume(smt.Le(term, smt.Const(iv.Hi)))
		}
	}
	return term
}

// termInterval bounds t from the declared ranges of its variables and from the
// single-variable facts on the path (a requires clause, a branch condition).
func (v *verifier) termInterval(t smt.LinearTerm, env *symEnv) smt.Interval {
	if t.Overflow {
		return smt.Interval{}
	}
	lo, hi := smt.Const(t.Const), smt.Const(t.Const)
	if len(t.Coeffs) == 0 {
		return smt.Interval{HasLo: true, HasHi: true, Lo: t.Const, Hi: t.Const}
	}
	var pathBounds map[string]smt.Interval
	for k, c := range t.Coeffs {
		iv := env.intervals[k]
		if !iv.HasLo || !iv.HasHi {
			if pathBounds == nil {
				_, _, pathBounds = smt.OctagonAnalyze(env.pathAtoms())
			}
			iv = iv.Intersect(pathBounds[k])
		}
		if !iv.HasLo || !iv.HasHi {
			return smt.Interval{}
		}
		a, b := smt.Const(iv.Lo).Scale(c), smt.Const(iv.Hi).Scale(c)
		if c < 0 {
			a, b = b, a
		}
		lo, hi = lo.Add(a), hi.Add(b)
	}
	if lo.Overflow || hi.Overflow {
		return smt.Interval{}
	}
	return smt.Interval{HasLo: true, HasHi: true, Lo: lo.Const, Hi: hi.Const}
}

func (v *verifier) evalBool(expr ast.Expr, env *symEnv, scope string) smt.BoolExpr {
	return v.evalBoolWithPrefix(expr, env, "")
}

// evalBoolWithPrefix evaluates expr with each name n in it standing for the
// variable prefix+n: an entity's invariant, written over its fields, for
// the entity bound under a path.
func (v *verifier) evalBoolWithPrefix(expr ast.Expr, env *symEnv, prefix string) smt.BoolExpr {
	if prefix != "" {
		// Evaluate in a view where the names are bound to the fields, so
		// that every form of expression reads them, and nothing else.
		view, names := env.fieldView(expr, prefix)
		b := v.evalBoolWithPrefix(expr, view, "")
		// What was learned about the symbols the evaluation made, and the
		// lengths it named: the same field has the same length next time.
		env.pc = append(env.pc, view.pc[len(env.pc):]...)
		for _, n := range names {
			for k, t := range view.listLens {
				if k != n && !strings.HasPrefix(k, n+".") {
					continue
				}
				if _, known := env.listLens[prefix+k]; !known {
					env.listLens[prefix+k] = t
				}
				if view.mapLens[k] {
					env.mapLens[prefix+k] = true
				}
			}
		}
		return b
	}
	switch e := expr.(type) {
	case *ast.BoolLit:
		return smt.BoolConst{Val: e.Value}
	case *ast.Ident:
		name := prefix + e.Name
		if b, ok := env.boolTerms[name]; ok {
			return b
		}
		return smt.BoolVar{Name: name}
	case *ast.UnaryExpr:
		if e.Op == "not" {
			return smt.Not(v.evalBoolWithPrefix(e.Expr, env, prefix))
		}
	case *ast.BinaryExpr:
		switch e.Op {
		case "and":
			return smt.And(v.evalBoolWithPrefix(e.Left, env, prefix), v.evalBoolWithPrefix(e.Right, env, prefix))
		case "or":
			return smt.Or(v.evalBoolWithPrefix(e.Left, env, prefix), v.evalBoolWithPrefix(e.Right, env, prefix))
		case "implies":
			return smt.Implies(v.evalBoolWithPrefix(e.Left, env, prefix), v.evalBoolWithPrefix(e.Right, env, prefix))
		case "in":
			if _, isMap := v.info.ExprTypes[e.Right].(*sema.MapType); isMap {
				return v.memberOf(e.Right, e.Left, env)
			}
		case "==", "!=", "<", "<=", ">", ">=":
			if e.Op == "==" || e.Op == "!=" {
				if b, ok := v.evalEquality(e, env); ok {
					return b
				}
			}
			l := v.evalInt(e.Left, env, "", false)
			r := v.evalInt(e.Right, env, "", false)
			switch e.Op {
			case "==":
				return smt.Eq(l, r)
			case "!=":
				return smt.Neq(l, r)
			case "<":
				return smt.Lt(l, r)
			case "<=":
				return smt.Le(l, r)
			case ">":
				return smt.Gt(l, r)
			case ">=":
				return smt.Ge(l, r)
			}
		}
	}
	return smt.BoolVar{Name: env.freshVar("bool")}
}

// evalEquality is `==` and `!=` between values that are not integers. Two
// booleans are equal when one holds exactly when the other does. A list, a
// map, an entity and a variant change in place or hold what does, so that
// nothing said of two names once stays true: the comparison is unknown.
// Integers and strings are left to the caller.
func (v *verifier) evalEquality(e *ast.BinaryExpr, env *symEnv) (smt.BoolExpr, bool) {
	lt, rt := v.info.ExprTypes[e.Left], v.info.ExprTypes[e.Right]
	known := func(t sema.Type) bool { return t != nil && t.Kind() != sema.KindUnknown }
	isBool := func(t sema.Type) bool { return t != nil && t.Kind() == sema.KindBool }
	var eq smt.BoolExpr
	switch {
	case isBool(lt) && isBool(rt):
		l := v.evalBoolWithPrefix(e.Left, env, "")
		r := v.evalBoolWithPrefix(e.Right, env, "")
		eq = smt.And(smt.Implies(l, r), smt.Implies(r, l))
	case isBool(lt) || isBool(rt):
		// The other side has no type (a lambda parameter): it may hold
		// something that is not a boolean and equal to none.
		eq = smt.BoolVar{Name: env.freshVar("bool")}
	case (known(lt) && !isScalar(lt)) || (known(rt) && !isScalar(rt)):
		eq = smt.BoolVar{Name: env.freshVar("bool")}
	default:
		return nil, false
	}
	if e.Op == "!=" {
		return smt.Not(eq), true
	}
	return eq, true
}

// ---------------------------------------------------------------------------
// Exhaustive Match Verification (via AnimaSMT for ints + structural ADT check)
// ---------------------------------------------------------------------------

type matchArmDesc struct {
	pat   ast.Pattern
	guard ast.Expr
}

func extractMatchArmsFromStmt(arms []ast.MatchArm) []matchArmDesc {
	out := make([]matchArmDesc, len(arms))
	for i, a := range arms {
		out[i] = matchArmDesc{pat: a.Pattern, guard: a.Guard}
	}
	return out
}

func extractMatchArmsFromExpr(arms []ast.MatchExprArm) []matchArmDesc {
	out := make([]matchArmDesc, len(arms))
	for i, a := range arms {
		out[i] = matchArmDesc{pat: a.Pattern, guard: a.Guard}
	}
	return out
}

func (v *verifier) verifyMatchExhaustive(subj ast.Expr, arms []matchArmDesc, env *symEnv, scope string, span ast.Span) {
	subjTy := v.info.ExprTypes[subj]
	if subjTy == nil {
		subjTy = sema.UnknownType{}
	}
	switch t := subjTy.(type) {
	case *sema.IntType:
		st := v.evalInt(subj, env, scope, false)
		// The subject is known to lie in its range type; a length is not
		// negative; any other int can be any value.
		var dom smt.BoolExpr = smt.BoolConst{Val: true}
		if t.IsBounded {
			dom = smt.And(smt.Ge(st, smt.Const(t.Lo)), smt.Le(st, smt.Const(t.Hi)))
		} else if call, ok := subj.(*ast.CallExpr); ok {
			if id, ok := call.Callee.(*ast.Ident); ok && id.Name == "len" {
				dom = smt.Ge(st, smt.Const(0))
			}
		}

		var covered []smt.BoolExpr
		for _, arm := range arms {
			armEnv := env.clone()
			cond := v.patternCond(arm.pat, st, armEnv)
			if arm.guard != nil {
				g := v.evalBool(arm.guard, armEnv, scope)
				cond = smt.And(cond, g)
			}
			covered = append(covered, cond)
		}
		mEnv := env.clone()
		mEnv.assume(dom)
		v.prove(scope+".match_exhaustive", scope, span, mEnv, smt.Or(covered...))

	default:
		// A variant, a bool, a string, or a type sema does not know such
		// as the result of a future, which the patterns then name.
		var rows [][]ast.Pattern
		vc, what := "match_exhaustive_default", subjTy.String()
		_, unknown := subjTy.(sema.UnknownType)
		for _, arm := range arms {
			if arm.guard == nil { // a guarded arm may not run
				rows = append(rows, []ast.Pattern{arm.pat})
			}
			if !unknown || vc != "match_exhaustive_default" {
				continue
			}
			switch p := arm.pat.(type) {
			case *ast.VariantPat:
				if adt := v.info.Variants[p.Name]; adt != nil {
					vc, what = "match_exhaustive_adt", adt.Name
				}
			case *ast.BoolPat:
				vc, what = "match_exhaustive_bool", "bool"
			}
		}
		switch t := subjTy.(type) {
		case *sema.ADTType:
			vc, what = "match_exhaustive_adt", t.Name
		case sema.BoolType:
			vc, what = "match_exhaustive_bool", "bool"
		}
		if missing, ok := v.unmatched(rows, []sema.Type{subjTy}); ok {
			hint := "no arm for " + missing[0]
			if missing[0] == "_" {
				hint = "add a `_` arm"
			}
			v.record(scope+"."+vc, scope, span, what, VCFailed, fmt.Sprintf("non-exhaustive match on %s: %s", what, hint), nil)
		} else {
			v.record(scope+"."+vc, scope, span, what, VCProved, fmt.Sprintf("every value of %s is matched", what), nil)
		}
	}
}

// unmatched looks for a tuple of values of types that no row of patterns
// matches, and describes one. A column is split by variant or by bool
// value where some row tells them apart; an int or a string in a nested
// pattern is matched for certain only by a wildcard or a name.
func (v *verifier) unmatched(rows [][]ast.Pattern, types []sema.Type) ([]string, bool) {
	if len(types) == 0 {
		return nil, len(rows) == 0
	}
	catchAll := func(p ast.Pattern) bool {
		switch p.(type) {
		case *ast.WildcardPat, *ast.VarPat:
			return true
		}
		return false
	}
	rest := types[1:]
	split := false
	for _, r := range rows {
		switch r[0].(type) {
		case *ast.VariantPat, *ast.BoolPat:
			split = true
		}
	}
	adt, isADT := types[0].(*sema.ADTType)
	_, isBool := types[0].(sema.BoolType)
	typeKnown := types[0] != nil
	switch types[0].(type) {
	case sema.UnknownType, sema.TypeVar:
		typeKnown = false
	}
	if !typeKnown && split {
		// A type sema does not know, such as the result of a future or a
		// field that is a type parameter: the patterns name the type. A
		// pattern of another type than the one sema knows matches nothing.
		for _, r := range rows {
			if vp, ok := r[0].(*ast.VariantPat); ok && v.info.Variants[vp.Name] != nil {
				adt, isADT = v.info.Variants[vp.Name], true
				break
			}
			if _, ok := r[0].(*ast.BoolPat); ok {
				isBool = true
				break
			}
		}
	}
	// The type of a bare `None` lists no variants: its declaration does.
	var variants []sema.VariantInfo
	if isADT {
		variants = adt.Variants
		if decl := v.info.ADTs[adt.Name]; decl != nil && len(variants) == 0 {
			variants = decl.Variants
		}
	}
	switch {
	case split && isADT && len(variants) > 0:
		for _, vr := range variants {
			fields := v.variantFieldTypes(adt, vr.Name)
			var sub [][]ast.Pattern
			for _, r := range rows {
				head := make([]ast.Pattern, len(fields))
				for i := range head {
					head[i] = &ast.WildcardPat{}
				}
				if vp, ok := r[0].(*ast.VariantPat); ok {
					if vp.Name != vr.Name || len(vp.Fields) > len(fields) {
						continue
					}
					copy(head, vp.Fields)
				} else if !catchAll(r[0]) {
					continue
				}
				sub = append(sub, append(head, r[1:]...))
			}
			if w, ok := v.unmatched(sub, append(append([]sema.Type{}, fields...), rest...)); ok {
				name := vr.Name
				if len(fields) > 0 {
					name += "(" + strings.Join(w[:len(fields)], ", ") + ")"
				}
				return append([]string{name}, w[len(fields):]...), true
			}
		}
		return nil, false
	case split && isBool:
		for _, val := range []bool{true, false} {
			var sub [][]ast.Pattern
			for _, r := range rows {
				if bp, ok := r[0].(*ast.BoolPat); (ok && bp.Value == val) || catchAll(r[0]) {
					sub = append(sub, r[1:])
				}
			}
			if w, ok := v.unmatched(sub, rest); ok {
				name := "False"
				if val {
					name = "True"
				}
				return append([]string{name}, w...), true
			}
		}
		return nil, false
	}
	var sub [][]ast.Pattern
	for _, r := range rows {
		if catchAll(r[0]) {
			sub = append(sub, r[1:])
		}
	}
	if w, ok := v.unmatched(sub, rest); ok {
		return append([]string{"_"}, w...), true
	}
	return nil, false
}

// variantFieldTypes gives the types of the fields of a variant of adt, with
// its type parameters replaced by the arguments of adt.
func (v *verifier) variantFieldTypes(adt *sema.ADTType, name string) []sema.Type {
	decl := v.info.Variants[name]
	if decl == nil || decl.Name != adt.Name {
		decl = adt
	}
	var out []sema.Type
	for _, f := range adt.VariantMap[name].Fields {
		fty := f.Type
		if tv, ok := fty.(sema.TypeVar); ok {
			fty = nil
			for i, tp := range decl.TypeParams {
				if tp == tv.Name && i < len(adt.TypeArgs) {
					fty = adt.TypeArgs[i]
				}
			}
		}
		out = append(out, fty)
	}
	return out
}

func (v *verifier) patternCond(pat ast.Pattern, st smt.LinearTerm, env *symEnv) smt.BoolExpr {
	switch p := pat.(type) {
	case *ast.WildcardPat:
		return smt.BoolConst{Val: true}
	case *ast.VarPat:
		env.intTerms[p.Name] = st
		return smt.BoolConst{Val: true}
	case *ast.IntPat:
		return smt.Eq(st, smt.Const(p.Value))
	case *ast.RangePat:
		return smt.And(smt.Ge(st, smt.Const(p.Lo)), smt.Le(st, smt.Const(p.Hi)))
	}
	return smt.BoolConst{Val: false}
}

func (v *verifier) assumePattern(pat ast.Pattern, subj ast.Expr, env *symEnv, scope string) {
	switch p := pat.(type) {
	case *ast.VariantPat:
		v.bindVariantPat(p, v.info.ExprTypes[subj], env)
		return
	case *ast.BoolPat:
		b := v.evalBool(subj, env, scope)
		if !p.Value {
			b = smt.Not(b)
		}
		env.assume(b)
		return
	case *ast.StrPat:
		return
	}
	st := v.evalInt(subj, env, scope, false)
	env.assume(v.patternCond(pat, st, env))
}

// bindVariantPat makes the arm reachable with each bound field an arbitrary value of its
// declared type. Which variant the subject holds is not modelled.
func (v *verifier) bindVariantPat(p *ast.VariantPat, subjTy sema.Type, env *symEnv) {
	subjADT, _ := subjTy.(*sema.ADTType)
	adt := v.info.Variants[p.Name]
	if adt == nil {
		adt = subjADT
	}
	var fields []sema.EntityFieldInfo
	subst := map[string]sema.Type{}
	if adt != nil {
		fields = adt.VariantMap[p.Name].Fields
		if subjADT != nil && subjADT.Name == adt.Name {
			for i, tp := range adt.TypeParams {
				if i < len(subjADT.TypeArgs) {
					subst[tp] = subjADT.TypeArgs[i]
				}
			}
		}
	}
	for i, sub := range p.Fields {
		var fty sema.Type
		if i < len(fields) {
			fty = fields[i].Type
			if tv, ok := fty.(sema.TypeVar); ok {
				fty = subst[tv.Name]
			}
		}
		switch sp := sub.(type) {
		case *ast.VarPat:
			v.bindFresh(env, sp.Name, fty)
		case *ast.VariantPat:
			v.bindVariantPat(sp, fty, env)
		}
	}
}

// collectAssignedVars lists what stmts may assign. compound and lets hold, for the names
// that are only ever written by a compound assignment or an assignment to the variable
// itself, those targets and those assignments.
func collectAssignedVars(stmts []ast.Stmt) (out []string, compound map[string][]ast.Expr, lets map[string][]*ast.LetAssignStmt) {
	seen := map[string]bool{}
	plain := map[string]bool{}
	compound = map[string][]ast.Expr{}
	lets = map[string][]*ast.LetAssignStmt{}
	add := func(name string) {
		if name != "" && !seen[name] {
			seen[name] = true
			out = append(out, name)
		}
		plain[name] = true
	}
	// path names what an assignment target denotes in a symEnv: `x` or `obj.field`.
	path := func(e ast.Expr) string {
		p, _ := mutArgPath(e)
		return p
	}
	var walk func([]ast.Stmt)
	walk = func(ss []ast.Stmt) {
		for _, s := range ss {
			switch x := s.(type) {
			case *ast.LetAssignStmt:
				was := plain[x.Name]
				add(x.Name)
				plain[x.Name] = was
				lets[x.Name] = append(lets[x.Name], x)
			case *ast.CompoundAssignStmt:
				name := path(x.Target)
				was := plain[name]
				add(name)
				plain[name] = was
				compound[name] = append(compound[name], x.Target)
			case *ast.FieldAssignStmt:
				add(path(&ast.FieldExpr{Object: x.Object, Field: x.Field}))
			case *ast.IfStmt:
				for _, br := range x.Branches {
					walk(br.Body)
				}
				walk(x.Else)
			case *ast.MatchStmt:
				for _, arm := range x.Arms {
					walk(arm.Body)
				}
			case *ast.WhileStmt:
				walk(x.Body)
			case *ast.ForStmt:
				add(x.Var)
				walk(x.Body)
			}
		}
	}
	walk(stmts)
	// A name in a pattern is written by the arm that matches, in a match
	// statement and in a match expression alike.
	visitNodes(reflect.ValueOf(stmts), func(n any) {
		if vp, ok := n.(*ast.VarPat); ok {
			add(vp.Name)
		}
	})
	for name := range plain {
		if plain[name] {
			delete(compound, name)
			delete(lets, name)
		}
	}
	return out, compound, lets
}
