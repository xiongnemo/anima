package spark

import (
	"fmt"
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
	freshID    int
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
		pc:         append([]smt.BoolExpr{}, e.pc...),
		freshID:    e.freshID,
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
	e.freshID++
	return fmt.Sprintf("__%s_%d", prefix, e.freshID)
}

// unbind drops every binding of name, so a callee parameter cannot resolve to a caller variable of the same name.
func (e *symEnv) unbind(name string) {
	delete(e.intTerms, name)
	delete(e.boolTerms, name)
	delete(e.listLens, name)
	delete(e.listElems, name)
	delete(e.sumInfos, name)
	for k := range e.intTerms {
		if strings.HasPrefix(k, name+".") {
			delete(e.intTerms, k)
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
	if t, ok := e.listLens[from]; ok {
		delete(e.listLens, from)
		e.listLens[to] = t
	}
	if iv, ok := e.listElems[from]; ok {
		delete(e.listElems, from)
		e.listElems[to] = iv
	}
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

func (e *symEnv) pathCond() smt.BoolExpr {
	return smt.And(e.pc...)
}

type verifier struct {
	info        *sema.ProgramInfo
	report      *Report
	curFuncName string
	curDecExpr  ast.Expr
	curDecTerm  smt.LinearTerm
	curMutEnts  []struct {
		varName string
		ent     *sema.EntityType
	}
	curEnsures []ast.Expr
	curRetType sema.Type
	fstrSpan   *ast.Span
	strParams  map[string]bool
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
		if adt, ok := v.curRetType.(*sema.ADTType); ok {
			v.checkADTConstructionRange(retVal, env, adt, scope, span)
		}
	}
	// 2. Mutable entity invariants preserved
	for _, me := range v.curMutEnts {
		for _, inv := range me.ent.Invariants {
			b := v.evalBoolWithPrefix(inv, env, me.varName+".")
			v.prove(fmt.Sprintf("%s.mut_%s_invariant", v.curFuncName, me.varName), scope, span, env, b)
		}
	}
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

	for _, n := range wf.Nodes {
		switch node := n.(type) {
		case *ast.StartNode:
			v.execBlock(node.Body, env, scope)
		case *ast.ForkNode:
			for _, br := range node.Branches {
				for _, op := range br.Ops {
					if op.Kind == ast.BranchStmt && op.Stmt != nil {
						v.execStmt(op.Stmt, env, scope)
					}
				}
			}
		case *ast.ChoiceNode:
			v.verifyChoiceNode(node, env, scope)
		case *ast.StepNode:
			v.execBlock(node.Body, env, scope)
		}
	}
}

func (v *verifier) verifyChoiceNode(cn *ast.ChoiceNode, env *symEnv, scope string) {
	var guards []smt.BoolExpr
	hasElse := false
	for _, br := range cn.Branches {
		if br.IsElse {
			hasElse = true
			continue
		}
		v.checkArith(br.Guard, env, scope)
		g := v.evalBool(br.Guard, env, scope)
		guards = append(guards, g)
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
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		v.checkArith(s.Value, env, scope)
		v.assignSymbolic(s.Name, s.Value, env, scope, s.Span)
		if s.TypeAnno != nil {
			if ty, ok := v.info.ExprTypes[s.Value]; ok {
				if it, ok := ty.(*sema.IntType); ok && it.IsBounded {
					t := v.evalInt(s.Value, env, scope, true)
					v.checkIntRange(t, s.Value, env, it, scope+".let_"+s.Name, scope, s.Span)
				}
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
			v.evalSideEffects(ix.Index, env, scope)
		}
		v.checkArith(s.Value, env, scope)
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
		} else if fe, ok := s.Target.(*ast.FieldExpr); ok {
			if objID, ok := fe.Object.(*ast.Ident); ok {
				env.intTerms[objID.Name+"."+fe.Field] = rhsTerm
			}
		}

	case *ast.IndexAssignStmt:
		v.checkArith(s.Index, env, scope)
		v.evalSideEffects(s.Index, env, scope)
		v.checkArith(s.Value, env, scope)

	case *ast.CallStmt:
		if s.Call != nil {
			v.checkArith(s.Call, env, scope)
		}

	case *ast.FieldAssignStmt:
		v.checkArith(s.Value, env, scope)
		v.evalSideEffects(s.Value, env, scope)
		path := ""
		if objID, ok := s.Object.(*ast.Ident); ok {
			path = objID.Name + "." + s.Field
		}
		rhsTerm := v.evalInt(s.Value, env, scope, true)
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
			env.intTerms[path] = rhsTerm
		}

	case *ast.IfStmt:
		curEnv := env.clone()
		allTerm := true
		type branchOut struct {
			cond  smt.BoolExpr
			terms map[string]smt.LinearTerm
			bools map[string]smt.BoolExpr
		}
		var outs []branchOut

		for _, br := range s.Branches {
			v.checkArith(br.Cond, curEnv, scope)
			cond := v.evalBool(br.Cond, curEnv, scope)
			thenEnv := curEnv.clone()
			thenEnv.assume(cond)
			term := v.execBlock(br.Body, thenEnv, scope)
			if !term {
				allTerm = false
				outs = append(outs, branchOut{
					cond:  smt.And(curEnv.pathCond(), cond),
					terms: thenEnv.intTerms,
					bools: thenEnv.boolTerms,
				})
			}
			curEnv.assume(smt.Not(cond))
		}
		if len(s.Else) > 0 {
			term := v.execBlock(s.Else, curEnv, scope)
			if !term {
				allTerm = false
				outs = append(outs, branchOut{
					cond:  curEnv.pathCond(),
					terms: curEnv.intTerms,
					bools: curEnv.boolTerms,
				})
			}
		} else {
			allTerm = false
			outs = append(outs, branchOut{
				cond:  curEnv.pathCond(),
				terms: curEnv.intTerms,
				bools: curEnv.boolTerms,
			})
		}
		if allTerm {
			return true
		}
		if len(outs) == 1 {
			env.intTerms = outs[0].terms
			env.boolTerms = outs[0].bools
			env.pc = []smt.BoolExpr{outs[0].cond}
		} else if len(outs) > 1 {
			var branchDisj []smt.BoolExpr
			allKeys := map[string]bool{}
			for _, o := range outs {
				branchDisj = append(branchDisj, o.cond)
				for k := range o.terms {
					allKeys[k] = true
				}
			}
			for k := range allKeys {
				same := true
				var firstStr string
				for idx, o := range outs {
					t, ok := o.terms[k]
					if !ok {
						same = false
						break
					}
					if idx == 0 {
						firstStr = t.String()
					} else if t.String() != firstStr {
						same = false
						break
					}
				}
				if same {
					env.intTerms[k] = outs[0].terms[k]
					continue
				}
				mv := smt.Var(env.freshVar("phi_" + k))
				env.intTerms[k] = mv
				for _, o := range outs {
					if t, ok := o.terms[k]; ok {
						env.assume(smt.Implies(o.cond, smt.Eq(mv, t)))
					}
				}
			}
			env.assume(smt.Or(branchDisj...))
		}

	case *ast.MatchStmt:
		v.checkArith(s.Subject, env, scope)
		v.verifyMatchExhaustive(s.Subject, extractMatchArmsFromStmt(s.Arms), env, scope, s.Span)
		for _, arm := range s.Arms {
			armEnv := env.clone()
			v.assumePattern(arm.Pattern, s.Subject, armEnv, scope)
			if arm.Guard != nil {
				v.checkArith(arm.Guard, armEnv, scope)
				armEnv.assume(v.evalBool(arm.Guard, armEnv, scope))
			}
			v.execBlock(arm.Body, armEnv, scope)
		}

	case *ast.WhileStmt:
		// 1. Prove invariant holds at entry
		for i, inv := range s.Invariants {
			v.prove(fmt.Sprintf("%s.loop_inv_entry_%d", scope, i+1), scope, inv.GetSpan(), env, v.evalBool(inv, env, scope))
		}
		// 2. Inductive step from an arbitrary iteration: only the invariants are known there.
		stepEnv := env.clone()
		v.havocAssigned(s.Body, stepEnv)
		for _, inv := range s.Invariants {
			stepEnv.assume(v.evalBool(inv, stepEnv, scope))
		}
		v.checkArith(s.Cond, stepEnv, scope)
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
		}
		v.execBlock(s.Body, loopEnv, scope)

	case *ast.ReturnStmt:
		if s.Value != nil {
			if me, ok := s.Value.(*ast.MatchExpr); ok {
				v.verifyMatchExhaustive(me.Subject, extractMatchArmsFromExpr(me.Arms), env, scope, s.Span)
			}
			v.checkArith(s.Value, env, scope)
			v.evalSideEffects(s.Value, env, scope)
			if rTerm := v.tryEvalInt(s.Value, env); rTerm != nil {
				env.intTerms["result"] = *rTerm
			}
		}
		v.checkFunctionExitContracts(env, scope, s.Span, s.Value)
		return true

	case *ast.ExprStmt:
		if me, ok := s.Expr.(*ast.MatchExpr); ok {
			v.verifyMatchExhaustive(me.Subject, extractMatchArmsFromExpr(me.Arms), env, scope, s.Span)
		}
		v.checkArith(s.Expr, env, scope)
		v.evalSideEffects(s.Expr, env, scope)
	}
	return false
}

func (v *verifier) assignSymbolic(name string, rhs ast.Expr, env *symEnv, scope string, span ast.Span) {
	if me, ok := rhs.(*ast.MatchExpr); ok {
		v.verifyMatchExhaustive(me.Subject, extractMatchArmsFromExpr(me.Arms), env, scope, span)
	}
	v.evalSideEffects(rhs, env, scope)

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
			if ce, ok := rhs.(*ast.CallExpr); ok {
				for _, arg := range ce.Args {
					if arg.Name != "" {
						if t := v.tryEvalInt(arg.Value, env); t != nil {
							env.intTerms[name+"."+arg.Name] = *t
						}
					}
				}
			}
			return
		case *sema.ListType:
			if ll, ok := rhs.(*ast.ListLit); ok {
				lt := smt.Const(int64(len(ll.Elems)))
				env.listLens[name] = lt
			}
		case *sema.HandleType:
			if rt.Name == "bytes.ByteView" {
				if ce, ok := rhs.(*ast.CallExpr); ok && len(ce.Args) >= 1 {
					if fe, ok := ce.Callee.(*ast.FieldExpr); ok {
						if sl, ok := ce.Args[0].Value.(*ast.StrLit); ok {
							if fe.Field == "from_hex" {
								env.listLens[name] = smt.Const(int64(len(sl.Value) / 2))
							} else if fe.Field == "from_str" {
								env.listLens[name] = smt.Const(int64(len(sl.Value)))
							}
						}
					}
				}
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
	cur := ast.Expr(pe)
	for {
		if p, ok := cur.(*ast.PipeExpr); ok {
			chain = append([]ast.Expr{p.Right}, chain...)
			cur = p.Left
		} else {
			break
		}
	}
	baseTermLen := smt.Var("len(" + targetVar + ")")
	if id, ok := cur.(*ast.Ident); ok {
		if lt, exists := env.listLens[id.Name]; exists {
			baseTermLen = lt
		}
	} else if ll, ok := cur.(*ast.ListLit); ok {
		baseTermLen = smt.Const(int64(len(ll.Elems)))
	}

	curLen := baseTermLen
	var curElem smt.Interval
	if id, ok := cur.(*ast.Ident); ok {
		curElem = env.listElems[id.Name]
	}
	if curTy, ok := v.info.ExprTypes[cur]; ok {
		if lt, ok := curTy.(*sema.ListType); ok {
			if it, ok := lt.Elem.(*sema.IntType); ok && it.IsBounded {
				curElem = smt.Interval{HasLo: true, HasHi: true, Lo: it.Lo, Hi: it.Hi}
			}
		}
	}

	for _, step := range chain {
		ce, ok := step.(*ast.CallExpr)
		if !ok {
			continue
		}
		fname := ""
		if id, ok := ce.Callee.(*ast.Ident); ok {
			fname = id.Name
		}
		switch fname {
		case "filter", "filter_ok":
			fv := smt.Var(env.freshVar("flen"))
			env.assume(smt.Ge(fv, smt.Const(0)))
			env.assume(smt.Le(fv, curLen))
			curLen = fv
		case "map":
			if len(ce.Args) == 1 {
				if lam, ok := ce.Args[0].Value.(*ast.LambdaExpr); ok {
					// Check if lambda accesses a bounded field like q.score
					if fe, ok := lam.Body.(*ast.FieldExpr); ok {
						if ft, ok := v.info.ExprTypes[fe]; ok {
							if it, ok := ft.(*sema.IntType); ok && it.IsBounded {
								curElem = smt.Interval{HasLo: true, HasHi: true, Lo: it.Lo, Hi: it.Hi}
							}
						}
					} else if bt, ok := v.info.ExprTypes[lam.Body]; ok {
						if it, ok := bt.(*sema.IntType); ok && it.IsBounded {
							curElem = smt.Interval{HasLo: true, HasHi: true, Lo: it.Lo, Hi: it.Hi}
						}
					}
				}
			}
		case "fold":
			if len(ce.Args) >= 1 && curElem.HasLo && curElem.HasHi {
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
	}
	env.listLens[targetVar] = curLen
	if curElem.HasLo && curElem.HasHi {
		env.listElems[targetVar] = curElem
	}
}

func (v *verifier) evalSideEffects(expr ast.Expr, env *symEnv, scope string) {
	if expr == nil {
		return
	}
	switch e := expr.(type) {
	case *ast.BinaryExpr:
		v.evalSideEffects(e.Left, env, scope)
		v.evalSideEffects(e.Right, env, scope)
		if e.Op == "/" || e.Op == "%" {
			den := v.evalInt(e.Right, env, scope, true)
			v.prove(scope+".div_nonzero", scope, e.Span, env, smt.Neq(den, smt.Const(0)))
		}
	case *ast.IndexExpr:
		v.evalSideEffects(e.List, env, scope)
		v.evalSideEffects(e.Index, env, scope)
		idx := v.evalInt(e.Index, env, scope, true)
		if id, ok := e.List.(*ast.Ident); ok {
			if lt, exists := env.listLens[id.Name]; exists {
				v.prove(scope+".index_bounds", scope, e.Span, env,
					smt.And(smt.Ge(idx, smt.Const(0)), smt.Lt(idx, lt)))
			}
		}
	case *ast.CallExpr:
		for _, a := range e.Args {
			v.evalSideEffects(a.Value, env, scope)
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
				for i, a := range e.Args {
					if i >= len(fi.Type.Params) {
						break
					}
					p := fi.Type.Params[i]
					binds = append(binds, func(c *symEnv) { c.unbind(p.Name) })
					switch pt := p.Type.(type) {
					case *sema.IntType:
						valT := v.evalInt(a.Value, env, scope, pt.IsBounded)
						if pt.IsBounded {
							v.checkIntRange(valT, a.Value, env, pt, fmt.Sprintf("%s.call_%s_arg_%s", scope, id.Name, p.Name), scope, a.Span)
						}
						binds = append(binds, func(c *symEnv) { c.intTerms[p.Name] = valT })
					case sema.BoolType:
						valB := v.evalBool(a.Value, env, scope)
						binds = append(binds, func(c *symEnv) { c.boolTerms[p.Name] = valB })
					case *sema.ListType:
						argID, _ := a.Value.(*ast.Ident)
						lt, known := smt.LinearTerm{}, false
						if argID != nil {
							lt, known = env.listLens[argID.Name]
						}
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
			}
		}
		// Check ByteView bounds (std.bytes)
		if fe, ok := e.Callee.(*ast.FieldExpr); ok {
			if objTy, ok := v.info.ExprTypes[fe.Object]; ok {
				if ht, ok := objTy.(*sema.HandleType); ok && ht.Name == "bytes.ByteView" && len(e.Args) >= 1 {
					width := int64(0)
					switch fe.Field {
					case "read_u8":
						width = 1
					case "read_u16_be":
						width = 2
					case "read_u32_be":
						width = 4
					}
					if width > 0 {
						off := v.evalInt(e.Args[0].Value, env, scope, true)
						bvLen := smt.Var("len(bytes)")
						if id, ok := fe.Object.(*ast.Ident); ok {
							if l, exists := env.listLens[id.Name]; exists {
								bvLen = l
							} else {
								bvLen = smt.Var("len(" + id.Name + ")")
							}
						}
						v.prove(scope+".byteview_bounds", scope, e.Span, env,
							smt.And(smt.Ge(off, smt.Const(0)), smt.Le(off.Add(smt.Const(width)), bvLen)))
					}
				}
			}
		}
	case *ast.PipeExpr:
		v.evalSideEffects(e.Left, env, scope)
		v.evalSideEffects(e.Right, env, scope)
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
	names, compound := collectAssignedVars(stmts)
	for _, name := range names {
		if _, ok := env.intTerms[name]; ok {
			t := smt.Var(env.freshVar(name))
			env.intTerms[name] = t
			var rng *sema.IntType
			for i, target := range compound[name] {
				it, _ := v.info.ExprTypes[target].(*sema.IntType)
				if it == nil || !it.IsBounded || (i > 0 && (rng == nil || it.Lo != rng.Lo || it.Hi != rng.Hi)) {
					rng = nil
					break
				}
				rng = it
			}
			if rng != nil {
				env.assumeRange(t, rng)
			} else {
				env.assume(smt.FitsInt64(t))
			}
		}
		if _, ok := env.boolTerms[name]; ok {
			env.boolTerms[name] = smt.BoolVar{Name: env.freshVar(name)}
		}
		delete(env.listLens, name)
		delete(env.listElems, name)
		delete(env.sumInfos, name)
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
	if lt, ok := v.info.ExprTypes[e].(*sema.ListType); ok {
		if it, ok := lt.Elem.(*sema.IntType); ok && it.IsBounded {
			return smt.Interval{HasLo: true, HasHi: true, Lo: it.Lo, Hi: it.Hi}
		}
	}
	switch x := e.(type) {
	case *ast.Ident:
		return env.listElems[x.Name]
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
	if be, ok := expr.(*ast.BinaryExpr); ok && be.Op == "/" {
		num := v.evalInt(be.Left, env, scope, false)
		den := v.evalInt(be.Right, env, scope, false)
		// Exact theorem for den >= 1 and num >= 0:
		// target.Lo <= floor(num / den) <= target.Hi  <==>  target.Lo * den <= num && num <= (target.Hi + 1) * den - 1
		cond := smt.And(
			smt.Ge(den, smt.Const(1)),
			smt.Ge(num, smt.Const(0)),
			smt.Le(den.Scale(target.Lo), num),
			smt.Lt(num, den.Scale(target.Hi+1)),
		)
		v.prove(vcName, scope, span, env, cond)
		return
	}
	v.prove(vcName, scope, span, env, smt.And(smt.Ge(term, smt.Const(target.Lo)), smt.Le(term, smt.Const(target.Hi))))
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
		if id, ok := e.Callee.(*ast.Ident); ok && id.Name == "len" && len(e.Args) == 1 {
			if argID, ok := e.Args[0].Value.(*ast.Ident); ok {
				if lt, exists := env.listLens[argID.Name]; exists {
					return lt
				}
				return smt.Var("len(" + argID.Name + ")")
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

func (v *verifier) evalBoolWithPrefix(expr ast.Expr, env *symEnv, prefix string) smt.BoolExpr {
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
		case "==", "!=", "<", "<=", ">", ">=":
			l := v.evalIntPrefixed(e.Left, env, prefix)
			r := v.evalIntPrefixed(e.Right, env, prefix)
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

func (v *verifier) evalIntPrefixed(expr ast.Expr, env *symEnv, prefix string) smt.LinearTerm {
	if prefix == "" {
		return v.evalInt(expr, env, "", false)
	}
	if id, ok := expr.(*ast.Ident); ok {
		path := prefix + id.Name
		if t, ok := env.intTerms[path]; ok {
			return t
		}
		return smt.Var(path)
	}
	if be, ok := expr.(*ast.BinaryExpr); ok {
		l := v.evalIntPrefixed(be.Left, env, prefix)
		r := v.evalIntPrefixed(be.Right, env, prefix)
		switch be.Op {
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
		}
	}
	return v.evalInt(expr, env, "", false)
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
		return
	}
	switch t := subjTy.(type) {
	case *sema.IntType:
		st := v.evalInt(subj, env, scope, false)
		var dom smt.BoolExpr = smt.BoolConst{Val: true}
		var dParts []smt.BoolExpr
		if t.IsBounded {
			dParts = append(dParts, smt.Ge(st, smt.Const(t.Lo)), smt.Le(st, smt.Const(t.Hi)))
		} else {
			dParts = append(dParts, smt.Ge(st, smt.Const(0))) // assume >=0 for len() unless negative allowed
		}
		// Wait: if subject is len(...) specifically, len >= 0
		if call, ok := subj.(*ast.CallExpr); ok {
			if id, ok := call.Callee.(*ast.Ident); ok && id.Name == "len" {
				dParts = []smt.BoolExpr{smt.Ge(st, smt.Const(0))}
			}
		} else if !t.IsBounded {
			dParts = nil
		}
		if len(dParts) > 0 {
			dom = smt.And(dParts...)
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

	case *sema.ADTType:
		covered := map[string]bool{}
		hasWildcard := false
		for _, arm := range arms {
			if arm.guard != nil {
				continue // guarded arm doesn't guarantee variant coverage alone
			}
			switch p := arm.pat.(type) {
			case *ast.WildcardPat, *ast.VarPat:
				hasWildcard = true
			case *ast.VariantPat:
				covered[p.Name] = true
			}
		}
		if hasWildcard {
			v.record(scope+".match_exhaustive_adt", scope, span, t.Name, VCProved, "wildcard covers all variants", nil)
			return
		}
		var missing []string
		for _, vr := range t.Variants {
			if !covered[vr.Name] {
				missing = append(missing, vr.Name)
			}
		}
		if len(missing) > 0 {
			v.record(scope+".match_exhaustive_adt", scope, span, t.Name, VCFailed,
				fmt.Sprintf("non-exhaustive match on %s: missing variant(s) %s", t.Name, strings.Join(missing, ", ")), nil)
		} else {
			v.record(scope+".match_exhaustive_adt", scope, span, t.Name, VCProved,
				fmt.Sprintf("all %d variants of %s covered", len(t.Variants), t.Name), nil)
		}
	case sema.BoolType:
		covT, covF := false, false
		for _, arm := range arms {
			if arm.guard != nil {
				continue
			}
			switch p := arm.pat.(type) {
			case *ast.WildcardPat, *ast.VarPat:
				covT, covF = true, true
			case *ast.BoolPat:
				if p.Value {
					covT = true
				} else {
					covF = true
				}
			}
		}
		if covT && covF {
			v.record(scope+".match_exhaustive_bool", scope, span, "bool", VCProved, "both True and False covered", nil)
		} else {
			v.record(scope+".match_exhaustive_bool", scope, span, "bool", VCFailed, "non-exhaustive bool match", nil)
		}
	}
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

// collectAssignedVars lists what stmts may assign. compound holds, for the names that are
// only ever the target of a compound assignment, those targets.
func collectAssignedVars(stmts []ast.Stmt) (out []string, compound map[string][]ast.Expr) {
	seen := map[string]bool{}
	plain := map[string]bool{}
	compound = map[string][]ast.Expr{}
	add := func(name string) {
		if name != "" && !seen[name] {
			seen[name] = true
			out = append(out, name)
		}
		plain[name] = true
	}
	// path names what an assignment target denotes in a symEnv: `x` or `obj.field`.
	path := func(e ast.Expr) string {
		switch t := e.(type) {
		case *ast.Ident:
			return t.Name
		case *ast.FieldExpr:
			if obj, ok := t.Object.(*ast.Ident); ok {
				return obj.Name + "." + t.Field
			}
		}
		return ""
	}
	var walk func([]ast.Stmt)
	walk = func(ss []ast.Stmt) {
		for _, s := range ss {
			switch x := s.(type) {
			case *ast.LetAssignStmt:
				add(x.Name)
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
	for name := range plain {
		if plain[name] {
			delete(compound, name)
		}
	}
	return out, compound
}
