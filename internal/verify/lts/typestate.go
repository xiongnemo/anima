package lts

import (
	"fmt"
	"sort"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
)

type TypestateError struct {
	Span    ast.Span
	Func    string
	Message string
}

type SystemResult struct {
	SystemName string
	NumStates  int
	NumEdges   int
	NumSCCs    int
	Alphabet   []string
	ChecksRun  []string
	Failures   []SequenceTrace
	SysLTS     *SystemLTS
}

type Report struct {
	Systems         []SystemResult
	TypestateErrors []TypestateError
	BuildErrors     []string
}

func (r *Report) OK() bool {
	if len(r.BuildErrors) > 0 || len(r.TypestateErrors) > 0 {
		return false
	}
	for _, s := range r.Systems {
		if len(s.Failures) > 0 {
			return false
		}
	}
	return true
}

func (r *Report) Errors() []string {
	var out []string
	out = append(out, r.BuildErrors...)
	for _, te := range r.TypestateErrors {
		out = append(out, fmt.Sprintf("%s: Typestate protocol error in %s: %s", te.Span, te.Func, te.Message))
	}
	for _, s := range r.Systems {
		for _, f := range s.Failures {
			out = append(out, fmt.Sprintf("System %s: %s", s.SystemName, f.Violation))
		}
	}
	return out
}

// Verify runs FSP/LTS composition, Safety, Deadlock, Tarjan SCC Progress,
// FLTL checks across all SystemDecls, AND Linear Resource Typestate verification across functions/workflows.
func Verify(info *sema.ProgramInfo) *Report {
	rep := &Report{}

	// 1. Typestate checking on all functions & workflows
	ts := &typestateChecker{info: info}
	for _, d := range info.Program.Decls {
		switch node := d.(type) {
		case *ast.FuncDecl:
			ts.checkFunc(node)
		case *ast.WorkflowDecl:
			ts.checkWorkflow(node)
		case *ast.EntityDecl:
			ts.checkEntity(node)
		}
	}
	rep.TypestateErrors = ts.errs

	// 2. FSP / LTSA checking on all systems
	for _, d := range info.Program.Decls {
		sys, ok := d.(*ast.SystemDecl)
		if !ok {
			continue
		}
		sysLTS, err := Compose(sys, info)
		if err != nil {
			rep.BuildErrors = append(rep.BuildErrors, err.Error())
			continue
		}
		edgeCount := 0
		for _, es := range sysLTS.Edges {
			edgeCount += len(es)
		}
		sccs := TarjanSCC(sysLTS)
		sr := SystemResult{
			SystemName: sys.Name,
			NumStates:  len(sysLTS.States),
			NumEdges:   edgeCount,
			NumSCCs:    len(sccs),
			Alphabet:   sysLTS.SortedAlphabet(),
			SysLTS:     sysLTS,
		}
		for _, chk := range sys.Checks {
			sr.ChecksRun = append(sr.ChecksRun, chk.RawText)
			switch chk.Kind {
			case ast.CheckDeadlockFree:
				if cex := CheckDeadlock(sysLTS); cex != nil {
					sr.Failures = append(sr.Failures, *cex)
				}
			case ast.CheckSatisfies:
				if prop, ok := info.Properties[chk.Target]; ok {
					pl := CompileProperty(prop)
					if cex := CheckSafety(sysLTS, pl); cex != nil {
						sr.Failures = append(sr.Failures, *cex)
					}
				} else if prog, ok := info.Progresses[chk.Target]; ok {
					_, cex := CheckProgress(sysLTS, prog)
					if cex != nil {
						sr.Failures = append(sr.Failures, *cex)
					}
				}
			case ast.CheckLTL:
				if cex := CheckLTL(sysLTS, chk); cex != nil {
					sr.Failures = append(sr.Failures, *cex)
				}
			}
		}
		rep.Systems = append(rep.Systems, sr)
	}

	return rep
}

// ---------------------------------------------------------------------------
// Linear Resource Ownership & Typestate Verifier (Sockets, Files, Ports)
// ---------------------------------------------------------------------------
//
// Every linear handle (sock.TcpStream, sock.TcpListener, fs.File,
// conc.ThreadPool) has exactly one owner. The checker is modular: a function is checked against its own
// signature and the signatures of the functions it calls.
//
//   - A handle parameter is borrowed unless declared `own`. A borrowed handle
//     must leave the function in the state it arrived in.
//   - `f(own x)`, `y = x`, `return x` and `return Ok(x)` move x; a moved handle
//     cannot be used again.
//   - An owner must bring its handle to an accepting state (or move it) on
//     every exit path, including the early return of `?`.
//   - All paths joining after an if/match, and every loop iteration, must
//     agree on the state of each handle.
//   - Only a task closure given to pool.submit may capture a handle: either by
//     moving it in, or by borrowing a shareable handle until the future is
//     awaited or the pool is shut down.

type handleState struct {
	typeName  string
	state     string
	spec      *sema.TypestateSpec
	span      ast.Span
	owned     bool // false: borrowed parameter
	wrapped   bool // still inside an unmatched Result/Option
	moved     bool
	movedAt   ast.Span
	shareable bool // may be borrowed by several tasks at once
}

func (hs handleState) dead() bool {
	return hs.moved || isAcceptingState(hs.spec, hs.state)
}

// key identifies what a later statement may do with the handle.
func (hs handleState) key() string {
	switch {
	case hs.moved:
		return "moved"
	case isAcceptingState(hs.spec, hs.state):
		return hs.state
	case hs.wrapped:
		return "an unmatched result"
	}
	return hs.state
}

func sameHandleState(a, b handleState) bool {
	if a.dead() || b.dead() {
		return a.dead() && b.dead()
	}
	return a.state == b.state && a.wrapped == b.wrapped
}

// loan records that a task may be using a borrowed handle until the future is
// awaited or the pool is shut down. An empty name can no longer be released.
type loan struct {
	handle, fut, pool string
	fresh             bool // created by the statement being walked
}

type tsEnv struct {
	h     map[string]handleState
	ports map[string]handleState
	loans []loan
}

func newTsEnv() *tsEnv {
	return &tsEnv{h: map[string]handleState{}, ports: map[string]handleState{}}
}

func cloneHandles(m map[string]handleState) map[string]handleState {
	cp := make(map[string]handleState, len(m))
	for k, v := range m {
		cp[k] = v
	}
	return cp
}

func (e *tsEnv) clone() *tsEnv {
	return &tsEnv{h: cloneHandles(e.h), ports: cloneHandles(e.ports), loans: append([]loan(nil), e.loans...)}
}

func (e *tsEnv) lent(name string) bool {
	for _, l := range e.loans {
		if l.handle == name {
			return true
		}
	}
	return false
}

func (e *tsEnv) addLoans(ls []loan) {
	for _, l := range ls {
		dup := false
		for _, x := range e.loans {
			if x.handle == l.handle && x.fut == l.fut && x.pool == l.pool {
				dup = true
				break
			}
		}
		if !dup {
			e.loans = append(e.loans, l)
		}
	}
}

func (e *tsEnv) release(match func(loan) bool) {
	kept := e.loans[:0:0]
	for _, l := range e.loans {
		if !match(l) {
			kept = append(kept, l)
		}
	}
	e.loans = kept
}

func (e *tsEnv) names() []string {
	out := make([]string, 0, len(e.h))
	for k := range e.h {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

type typestateChecker struct {
	info     *sema.ProgramInfo
	errs     []TypestateError
	fn       string
	task     *taskCtx // inside a closure given to pool.submit
	inLambda bool     // inside any other closure
	touched  map[string]bool
}

type taskCtx struct {
	pool   string
	sawTry bool // a `?` in the closure body has already been evaluated
}

func (t *typestateChecker) err(span ast.Span, format string, args ...any) {
	e := TypestateError{Span: span, Func: t.fn, Message: fmt.Sprintf(format, args...)}
	for _, prev := range t.errs {
		if prev == e {
			return
		}
	}
	t.errs = append(t.errs, e)
}

// deferred reports whether the code being walked is a closure body, which
// runs later (if at all) and so cannot end a loan for the enclosing function.
func (t *typestateChecker) deferred() bool {
	return t.inLambda || t.task != nil
}

// touch records that the code being walked used the handle.
func (t *typestateChecker) touch(name string) {
	if t.touched != nil {
		t.touched[name] = true
	}
}

func (t *typestateChecker) newHandle(ht *sema.HandleType, span ast.Span, owned, wrapped bool) handleState {
	spec := t.info.StdHandles[ht.Name]
	return handleState{
		typeName:  ht.Name,
		state:     spec.InitState,
		spec:      spec,
		span:      span,
		owned:     owned,
		wrapped:   wrapped,
		shareable: ht.Name == "sock.TcpListener" || ht.Name == "conc.ThreadPool",
	}
}

func (t *typestateChecker) linear(e ast.Expr) (*sema.HandleType, bool) {
	return sema.LinearHandle(t.info.ExprTypes[e])
}

// handleIdent reports whether e names a tracked handle (and not a variable of
// another type that shadows it).
func (t *typestateChecker) handleIdent(e ast.Expr, env *tsEnv) (*ast.Ident, bool) {
	id, ok := e.(*ast.Ident)
	if !ok {
		return nil, false
	}
	if _, tracked := env.h[id.Name]; !tracked {
		return nil, false
	}
	if ty, known := t.info.ExprTypes[id]; known {
		if ht, _ := sema.LinearHandle(ty); ht == nil {
			return nil, false
		}
	}
	return id, true
}

func isSourceCall(e ast.Expr) bool {
	if te, ok := e.(*ast.TryExpr); ok {
		e = te.Inner
	}
	_, ok := e.(*ast.CallExpr)
	return ok
}

// buriedHandle finds a linear handle anywhere inside ty.
func buriedHandle(ty sema.Type, seen map[sema.Type]bool) *sema.HandleType {
	if seen[ty] {
		return nil
	}
	if ht, _ := sema.LinearHandle(ty); ht != nil {
		return ht
	}
	var inner []sema.Type
	switch x := ty.(type) {
	case *sema.ListType:
		inner = []sema.Type{x.Elem}
	case *sema.MapType:
		inner = []sema.Type{x.Key, x.Val}
	case *sema.HandleType:
		inner = []sema.Type{x.Elem}
	case *sema.ADTType:
		seen[ty] = true
		inner = append(inner, x.TypeArgs...)
		for _, v := range x.Variants {
			for _, f := range v.Fields {
				inner = append(inner, f.Type)
			}
		}
	case *sema.EntityType:
		seen[ty] = true
		for _, f := range x.Fields {
			inner = append(inner, f.Type)
		}
	}
	for _, in := range inner {
		if in == nil {
			continue
		}
		if ht := buriedHandle(in, seen); ht != nil {
			return ht
		}
	}
	return nil
}

func (t *typestateChecker) checkEntity(ed *ast.EntityDecl) {
	et := t.info.Entities[ed.Name]
	if et == nil {
		return
	}
	t.fn = "entity " + ed.Name
	for i, f := range et.Fields {
		if ht := buriedHandle(f.Type, map[sema.Type]bool{}); ht != nil && i < len(ed.Fields) {
			t.err(ed.Fields[i].Span, "field %q cannot hold a %s: a linear handle must be owned by a variable", f.Name, ht.Name)
		}
	}
}

// checkSignature rejects a handle nested in a type the checker cannot track.
func (t *typestateChecker) checkSignature(span ast.Span, what string, ty sema.Type) {
	if ty == nil {
		return
	}
	if ht, _ := sema.LinearHandle(ty); ht != nil {
		return
	}
	if ht := buriedHandle(ty, map[sema.Type]bool{}); ht != nil {
		t.err(span, "%s has type %s: a %s can only be passed or returned directly, or in a single Result/Option", what, ty, ht.Name)
	}
}

func (t *typestateChecker) bindParams(params []ast.Param, infos []sema.FuncParamInfo, env *tsEnv) {
	for i, p := range params {
		if i >= len(infos) {
			break
		}
		ht, wrapped := sema.LinearHandle(infos[i].Type)
		if ht == nil {
			t.checkSignature(p.Span, fmt.Sprintf("parameter %q", p.Name), infos[i].Type)
			continue
		}
		if wrapped {
			t.err(p.Span, "parameter %q: a Result/Option holding a %s cannot be passed to a function; match on it first", p.Name, ht.Name)
			continue
		}
		env.h[p.Name] = t.newHandle(ht, p.Span, p.Own, false)
	}
}

func (t *typestateChecker) checkFunc(fn *ast.FuncDecl) {
	env := newTsEnv()
	t.fn = "def " + fn.Name
	if fi := t.info.Funcs[fn.Name]; fi != nil && fi.Decl == fn {
		t.bindParams(fn.Params, fi.Type.Params, env)
		t.checkSignature(fn.Span, "the return value", fi.Type.Return)
	}
	if !t.walkBlock(fn.Body, env) {
		t.checkExit(fn.Span, env)
	}
}

// checkWorkflow follows the workflow as the backends run it, one path at a
// time: a step is checked with the handles as the way to it left them, not
// as the step written above it did, and every way out is an exit.
func (t *typestateChecker) checkWorkflow(wf *ast.WorkflowDecl) {
	env := newTsEnv()
	t.fn = "workflow " + wf.Name
	if wi := t.info.Workflows[wf.Name]; wi != nil {
		t.bindParams(wf.Params, wi.Params, env)
	}
	flow := ast.NewFlow(wf)
	if flow.Start == nil {
		t.checkExit(wf.Span, env)
		return
	}
	if t.walkBlock(flow.Start.Body, env) {
		return
	}
	t.walkWorkflow(wf, flow, flow.Start.Target, env, flow.Start.Span, map[string]bool{})
}

func (t *typestateChecker) walkWorkflow(wf *ast.WorkflowDecl, flow *ast.Flow, cur string, env *tsEnv, at ast.Span, onPath map[string]bool) {
	for {
		if flow.Ends(cur) {
			t.checkExit(at, env)
			return
		}
		if onPath[cur] {
			// The contract kernel refuses a workflow that comes back to a node.
			return
		}
		onPath[cur] = true
		choice := flow.Choice(cur)
		if st := flow.Step(cur); st != nil {
			if t.walkBlock(st.Body, env) {
				return
			}
			if cur, choice = flow.AfterStep(st); choice == nil {
				at = st.Span
				continue
			}
		}
		if choice != nil {
			// The backends try the guards in order and take the first
			// that holds: a branch has run its own guard and those
			// before it, not the ones after.
			for _, br := range choice.Branches {
				if br.Guard != nil {
					t.evalExpr(br.Guard, env, false)
				}
				path := make(map[string]bool, len(onPath))
				for k := range onPath {
					path[k] = true
				}
				t.walkWorkflow(wf, flow, br.Target, env.clone(), br.Span, path)
			}
			return
		}
		if fk := flow.Fork(cur); fk != nil {
			t.walkFork(wf, fk, env)
			cur, at = flow.AfterFork(), fk.Span
			continue
		}
		if jn := flow.Join(cur); jn != nil {
			cur, at = flow.AfterJoin(jn), jn.Span
			continue
		}
		mn := flow.Merge(cur)
		cur, at = flow.AfterMerge(mn), mn.Span
	}
}

// walkFork checks the branches of a fork, which run at the same time: each
// leaves the handles of the workflow as it found them.
func (t *typestateChecker) walkFork(wf *ast.WorkflowDecl, node *ast.ForkNode, env *tsEnv) {
	usedBy := map[string]string{}
	for _, br := range node.Branches {
		b := env.clone()
		t.fn = "workflow " + wf.Name + "." + br.Name
		t.touched = map[string]bool{}
		for _, op := range br.Ops {
			if op.Kind == ast.BranchStmt && op.Stmt != nil {
				t.walkStmt(op.Stmt, b)
			}
		}
		// Branches run concurrently: they may only share shareable handles.
		for _, k := range env.names() {
			if !t.touched[k] {
				continue
			}
			if other, ok := usedBy[k]; ok && !env.h[k].shareable {
				t.err(br.Span, "%s %q is used by concurrent branches %q and %q; it cannot be shared between threads", env.h[k].typeName, k, other, br.Name)
			}
			usedBy[k] = br.Name
		}
		t.touched = nil
		t.endScope(br.Span, env, b)
		t.requireUnchanged(br.Span, env, b, "a concurrent branch")
		t.checkPortLeaks(br.Span, b.ports)
		env.addLoans(b.loans)
		t.fn = "workflow " + wf.Name
	}
}

func (t *typestateChecker) walkBlock(stmts []ast.Stmt, env *tsEnv) bool {
	for _, s := range stmts {
		if t.walkStmt(s, env) {
			return true
		}
	}
	return false
}

func (t *typestateChecker) walkStmt(stmt ast.Stmt, env *tsEnv) bool {
	defer func() {
		for i := range env.loans {
			env.loans[i].fresh = false
		}
	}()
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		t.walkLet(s, env)

	case *ast.FieldAssignStmt:
		t.evalExpr(s.Object, env, false)
		t.evalExpr(s.Value, env, false)

	case *ast.CompoundAssignStmt:
		// The target's own sub-expressions run first, then the value.
		switch tgt := s.Target.(type) {
		case *ast.FieldExpr:
			t.evalExpr(tgt.Object, env, false)
		case *ast.IndexExpr:
			t.evalExpr(tgt.List, env, false)
			t.evalExpr(tgt.Index, env, false)
		}
		t.evalExpr(s.Value, env, false)

	case *ast.IndexAssignStmt:
		t.evalExpr(s.List, env, false)
		t.evalExpr(s.Index, env, false)
		t.evalExpr(s.Value, env, false)

	case *ast.IfStmt:
		var live []*tsEnv
		for _, br := range s.Branches {
			t.evalExpr(br.Cond, env, false)
			b := env.clone()
			if !t.walkBlock(br.Body, b) {
				t.endScope(br.Span, env, b)
				live = append(live, b)
			}
		}
		if len(s.Else) > 0 {
			b := env.clone()
			if !t.walkBlock(s.Else, b) {
				t.endScope(s.Span, env, b)
				live = append(live, b)
			}
		} else {
			live = append(live, env.clone())
		}
		if len(live) == 0 {
			return true
		}
		t.join(s.Span, env, live, true)

	case *ast.MatchStmt:
		return t.walkMatch(s, env)

	case *ast.WhileStmt:
		t.evalExpr(s.Cond, env, false)
		t.walkLoop(s.Span, s.Body, s.Cond, env)

	case *ast.ForStmt:
		t.evalExpr(s.Iterable, env, false)
		t.walkLoop(s.Span, s.Body, nil, env)

	case *ast.ReturnStmt:
		t.walkReturn(s, env)
		return true

	case *ast.ExprStmt:
		t.evalExpr(s.Expr, env, false)

	case *ast.CallStmt:
		t.evalExpr(s.Call, env, false)
	}
	return false
}

// rebind is called when name is (re)assigned: whatever it referred to before
// is no longer reachable.
func (t *typestateChecker) rebind(name string, env *tsEnv, span ast.Span) {
	if hs, ok := env.h[name]; ok {
		if !hs.dead() {
			if hs.owned {
				t.err(span, "resource handle leak: %s %q is overwritten while still in state %q", hs.typeName, name, hs.key())
			} else {
				t.err(span, "borrowed %s %q cannot be reassigned", hs.typeName, name)
			}
		}
		delete(env.h, name)
	}
	for i := range env.loans {
		if env.loans[i].fut == name {
			env.loans[i].fut = ""
		}
		if env.loans[i].pool == name {
			env.loans[i].pool = ""
		}
	}
}

// usable reports whether the handle can still be operated on, moved or lent.
func (t *typestateChecker) usable(span ast.Span, name string, hs handleState) bool {
	if hs.moved {
		t.err(span, "use of %s %q after it was moved at %s", hs.typeName, name, hs.movedAt)
		return false
	}
	return true
}

func (t *typestateChecker) walkLet(s *ast.LetAssignStmt, env *tsEnv) {
	// y = x  /  y = x?  : the handle moves from x to y.
	src := s.Value
	te, isTry := src.(*ast.TryExpr)
	if isTry {
		src = te.Inner
	}
	if id, ok := t.handleIdent(src, env); ok {
		hs := env.h[id.Name]
		if t.inLambda || t.task != nil || !t.usable(id.Span, id.Name, hs) {
			return
		}
		if env.lent(id.Name) {
			t.err(id.Span, "cannot move %s %q while a task may still be using it", hs.typeName, id.Name)
			return
		}
		if isTry {
			if !hs.wrapped {
				t.err(te.Span, "`?` applied to handle %q, which is not a Result/Option", id.Name)
				return
			}
			hs.wrapped = false
		}
		hs.moved, hs.movedAt = true, id.Span
		env.h[id.Name] = hs
		if isTry {
			t.checkTry(te.Span, env)
		}
		if s.Name == "_" {
			t.err(s.Span, "resource handle leak: %s %q is discarded", hs.typeName, id.Name)
			return
		}
		t.rebind(s.Name, env, s.Span)
		hs.moved, hs.span = false, s.Span
		env.h[s.Name] = hs
		return
	}

	t.evalExpr(s.Value, env, true)
	t.rebind(s.Name, env, s.Span)
	if ht, wrapped := t.linear(s.Value); ht != nil && isSourceCall(s.Value) {
		if s.Name == "_" {
			t.err(s.Span, "resource handle leak: the %s returned here is discarded", ht.Name)
			return
		}
		env.h[s.Name] = t.newHandle(ht, s.Span, true, wrapped)
	}
	if ce, ok := s.Value.(*ast.CallExpr); ok && s.Name != "_" && t.isPoolSubmit(ce) {
		for i := range env.loans {
			if env.loans[i].fresh {
				env.loans[i].fut = s.Name
			}
		}
	}
}

func (t *typestateChecker) walkMatch(s *ast.MatchStmt, env *tsEnv) bool {
	// A subject that may carry a handle hands it to the Ok/Some arm.
	var bound *handleState
	if id, ok := t.handleIdent(s.Subject, env); ok {
		hs := env.h[id.Name]
		switch {
		case t.inLambda || t.task != nil || !t.usable(id.Span, id.Name, hs):
		case !hs.wrapped:
			t.err(id.Span, "cannot match on handle %q; only a Result/Option holding a handle can be matched", id.Name)
		default:
			hs.moved, hs.movedAt = true, id.Span
			env.h[id.Name] = hs
			hs.moved, hs.wrapped = false, false
			bound = &hs
		}
	} else {
		t.evalExpr(s.Subject, env, true)
		if ht, wrapped := t.linear(s.Subject); ht != nil && isSourceCall(s.Subject) {
			if wrapped {
				hs := t.newHandle(ht, s.Span, true, false)
				bound = &hs
			} else {
				t.err(s.Span, "resource handle leak: the %s produced here is not bound to a variable", ht.Name)
			}
		}
	}

	var live []*tsEnv
	for _, arm := range s.Arms {
		a := env.clone()
		if bound != nil {
			vp, isVariant := arm.Pattern.(*ast.VariantPat)
			switch {
			case isVariant && (vp.Name == "Ok" || vp.Name == "Some"):
				if bp, ok := singleVarPat(vp); ok {
					t.rebind(bp.Name, a, arm.Span)
					hs := *bound
					hs.span = arm.Span
					a.h[bp.Name] = hs
				} else {
					t.err(arm.Span, "resource handle leak: pattern %s(..) must bind the %s to a variable", vp.Name, bound.typeName)
				}
			case isVariant:
			default:
				t.err(arm.Span, "resource handle leak: this pattern can match a value holding a %s without binding it", bound.typeName)
			}
		}
		// A guard that fails falls through to the next arm, so it must not
		// change any handle.
		t.evalConditional(arm.Guard, a)
		if !t.walkBlock(arm.Body, a) {
			t.endScope(arm.Span, env, a)
			t.endPorts(arm.Span, env, a)
			live = append(live, a)
		}
	}
	if len(s.Arms) == 0 {
		return false
	}
	if !t.matchIsTotal(s.Subject, len(s.Arms), func(i int) (ast.Pattern, ast.Expr) { return s.Arms[i].Pattern, s.Arms[i].Guard }) {
		// No arm may match: execution continues after the match.
		if bound != nil {
			t.err(s.Span, "resource handle leak: this match may run no arm and drop the %s; add a `_` arm or cover every case", bound.typeName)
		}
		live = append(live, env.clone())
	}
	if len(live) == 0 {
		return true
	}
	t.join(s.Span, env, live, false)
	return false
}

// matchIsTotal reports whether some arm always runs, judged from the patterns
// alone: an unguarded catch-all, both booleans, or every variant of the ADT.
// Anything else (integers, strings, guards) is treated as possibly matching
// nothing, even where the contract prover shows the arms are exhaustive.
func (t *typestateChecker) matchIsTotal(subject ast.Expr, n int, arm func(i int) (ast.Pattern, ast.Expr)) bool {
	bools := map[bool]bool{}
	variants := map[string]bool{}
	for i := 0; i < n; i++ {
		pat, guard := arm(i)
		if guard != nil {
			continue
		}
		switch p := pat.(type) {
		case *ast.WildcardPat, *ast.VarPat:
			return true
		case *ast.BoolPat:
			bools[p.Value] = true
		case *ast.VariantPat:
			irrefutable := true
			for _, f := range p.Fields {
				switch f.(type) {
				case *ast.WildcardPat, *ast.VarPat:
				default:
					irrefutable = false
				}
			}
			if irrefutable {
				variants[p.Name] = true
			}
		}
	}
	switch ty := t.info.ExprTypes[subject].(type) {
	case sema.BoolType:
		return bools[true] && bools[false]
	case *sema.ADTType:
		if len(ty.VariantMap) == 0 {
			return false
		}
		for name := range ty.VariantMap {
			if !variants[name] {
				return false
			}
		}
		return true
	}
	return false
}

func singleVarPat(vp *ast.VariantPat) (*ast.VarPat, bool) {
	if len(vp.Fields) != 1 {
		return nil, false
	}
	bp, ok := vp.Fields[0].(*ast.VarPat)
	if !ok || bp.Name == "_" {
		return nil, false
	}
	return bp, true
}

// walkLoop checks one arbitrary iteration; cond is evaluated again after it.
func (t *typestateChecker) walkLoop(span ast.Span, body []ast.Stmt, cond ast.Expr, env *tsEnv) {
	b := env.clone()
	if t.walkBlock(body, b) {
		return
	}
	t.endScope(span, env, b)
	t.endPorts(span, env, b)
	t.evalExpr(cond, b, false)
	t.requireUnchanged(span, env, b, "the loop body")
	// A loan made in the body may have been made once per iteration: its
	// future (and a pool created in the body) no longer names all of them.
	bound := map[string]bool{}
	collectBoundNames(body, bound)
	var made []loan
	for _, l := range b.loans {
		isNew := true
		for _, x := range env.loans {
			if x == l {
				isNew = false
				break
			}
		}
		if isNew {
			l.fut = ""
			if bound[l.pool] {
				l.pool = ""
			}
			made = append(made, l)
		}
	}
	env.addLoans(made)
}

func collectBoundNames(stmts []ast.Stmt, out map[string]bool) {
	for _, st := range stmts {
		switch s := st.(type) {
		case *ast.LetAssignStmt:
			out[s.Name] = true
		case *ast.IfStmt:
			for _, br := range s.Branches {
				collectBoundNames(br.Body, out)
			}
			collectBoundNames(s.Else, out)
		case *ast.MatchStmt:
			for _, arm := range s.Arms {
				collectPatternNames(arm.Pattern, out)
				collectBoundNames(arm.Body, out)
			}
		case *ast.WhileStmt:
			collectBoundNames(s.Body, out)
		case *ast.ForStmt:
			out[s.Var] = true
			collectBoundNames(s.Body, out)
		}
	}
}

func collectPatternNames(p ast.Pattern, out map[string]bool) {
	switch x := p.(type) {
	case *ast.VarPat:
		out[x.Name] = true
	case *ast.VariantPat:
		for _, f := range x.Fields {
			collectPatternNames(f, out)
		}
	}
}

func (t *typestateChecker) walkReturn(s *ast.ReturnStmt, env *tsEnv) {
	if s.Value != nil {
		target := s.Value
		viaCtor := false
		if ce, ok := s.Value.(*ast.CallExpr); ok && len(ce.Args) == 1 {
			if cid, ok := ce.Callee.(*ast.Ident); ok && (cid.Name == "Ok" || cid.Name == "Some") {
				target, viaCtor = ce.Args[0].Value, true
			}
		}
		if id, ok := t.handleIdent(target, env); ok {
			hs := env.h[id.Name]
			switch {
			case !t.usable(id.Span, id.Name, hs):
			case !hs.owned:
				t.err(id.Span, "cannot return borrowed %s %q: the caller still owns it", hs.typeName, id.Name)
			case viaCtor && hs.wrapped:
				t.err(id.Span, "%q is a Result/Option holding a handle; match on it before wrapping it again", id.Name)
			case hs.state != hs.spec.InitState:
				t.err(id.Span, "cannot return %s %q in state %q; a returned handle must be %q", hs.typeName, id.Name, hs.state, hs.spec.InitState)
			case env.lent(id.Name):
				t.err(id.Span, "cannot return %s %q while a task may still be using it", hs.typeName, id.Name)
			default:
				hs.moved, hs.movedAt = true, id.Span
				env.h[id.Name] = hs
			}
		} else {
			t.evalExpr(s.Value, env, true)
		}
	}
	t.checkExit(s.Span, env)
}

// endScope checks handles introduced inside a block: they are not visible to
// the code after it, so they must be finished before the block ends.
func (t *typestateChecker) endScope(span ast.Span, outer, inner *tsEnv) {
	for _, k := range inner.names() {
		if _, existed := outer.h[k]; existed {
			continue
		}
		if hs := inner.h[k]; !hs.dead() {
			t.err(span, "resource handle leak in inner block: %s %q left in state %q", hs.typeName, k, hs.key())
		}
		delete(inner.h, k)
	}
}

// endPorts checks port protocols first used inside a loop body or match arm,
// whose state is not carried to the code after it.
func (t *typestateChecker) endPorts(span ast.Span, outer, inner *tsEnv) {
	keys := make([]string, 0, len(inner.ports))
	for k := range inner.ports {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		if _, existed := outer.ports[k]; existed {
			continue
		}
		if hs := inner.ports[k]; !isAcceptingState(hs.spec, hs.state) {
			t.err(span, "resource handle leak in inner block: port %q left in state %q", strings.TrimPrefix(k, "port:"), hs.state)
		}
	}
}

func (t *typestateChecker) requireUnchanged(span ast.Span, before, after *tsEnv, what string) {
	for _, k := range before.names() {
		was := before.h[k]
		now, ok := after.h[k]
		if !ok {
			now = handleState{moved: true}
		}
		if !sameHandleState(was, now) {
			t.err(span, "%s changes %s %q from %q to %q; a handle that outlives it must be left in the state it had on entry",
				what, was.typeName, k, was.key(), now.key())
		}
	}
}

// join merges the paths that fall through an if/match back into env.
func (t *typestateChecker) join(span ast.Span, env *tsEnv, live []*tsEnv, mergePorts bool) {
	for _, k := range env.names() {
		first, ok := live[0].h[k]
		if !ok {
			first = handleState{moved: true}
		}
		agreed := true
		for _, b := range live[1:] {
			other, ok := b.h[k]
			if !ok {
				other = handleState{moved: true}
			}
			if !sameHandleState(first, other) {
				agreed = false
				t.err(span, "%s %q is %q on one path and %q on another; every path must leave it in the same state",
					env.h[k].typeName, k, first.key(), other.key())
				break
			}
		}
		if !agreed {
			// Report once, then treat the handle as finished.
			first = env.h[k]
			first.moved, first.movedAt = true, span
		}
		if _, ok := live[0].h[k]; ok || !agreed {
			env.h[k] = first
		} else {
			delete(env.h, k)
		}
	}
	var loans []loan
	for _, b := range live {
		loans = append(loans, b.loans...)
	}
	env.loans = nil
	env.addLoans(loans)

	if !mergePorts {
		return
	}
	// Port protocols keep their conservative merge: a non-accepting state wins.
	merged := map[string]handleState{}
	for _, b := range live {
		for k, hs := range b.ports {
			if prev, ok := merged[k]; ok {
				if !isAcceptingState(hs.spec, hs.state) && isAcceptingState(prev.spec, prev.state) {
					merged[k] = hs
				}
			} else {
				merged[k] = hs
			}
		}
	}
	env.ports = merged
}

// checkExit runs where the function returns normally.
func (t *typestateChecker) checkExit(span ast.Span, env *tsEnv) {
	for _, name := range env.names() {
		hs := env.h[name]
		switch {
		case hs.moved:
		case hs.owned:
			if !isAcceptingState(hs.spec, hs.state) {
				t.err(span, "resource handle leak: %s %q opened at %s was not transitioned to %s before leaving scope (currently in state %q)",
					hs.typeName, name, hs.span, strings.Join(hs.spec.AcceptStates, "/"), hs.key())
			}
		default:
			t.checkBorrowedAtExit(span, env, name, hs)
		}
	}
	t.checkPortLeaks(span, env.ports)
}

func (t *typestateChecker) checkBorrowedAtExit(span ast.Span, env *tsEnv, name string, hs handleState) {
	if hs.state != hs.spec.InitState {
		t.err(span, "borrowed %s %q must be returned to its owner in state %q, but is %q", hs.typeName, name, hs.spec.InitState, hs.state)
	}
	if env.lent(name) {
		t.err(span, "borrowed %s %q may still be used by a task when this function returns; await the future or shut down the pool first", hs.typeName, name)
	}
}

// checkTry runs at a `?`, which returns early on Err/None.
func (t *typestateChecker) checkTry(span ast.Span, env *tsEnv) {
	if t.task != nil {
		t.task.sawTry = true
	}
	if t.inLambda || t.task != nil {
		return
	}
	for _, name := range env.names() {
		hs := env.h[name]
		switch {
		case hs.moved:
		case hs.owned:
			if !isAcceptingState(hs.spec, hs.state) {
				t.err(span, "resource handle leak: `?` may return early while %s %q is still %q; match on the result and finish %q on the failure path",
					hs.typeName, name, hs.key(), name)
			}
		default:
			t.checkBorrowedAtExit(span, env, name, hs)
		}
	}
}

func (t *typestateChecker) checkPortLeaks(span ast.Span, ports map[string]handleState) {
	keys := make([]string, 0, len(ports))
	for k := range ports {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, name := range keys {
		hs := ports[name]
		if !isAcceptingState(hs.spec, hs.state) {
			t.err(span, "resource handle leak: %s %q opened at %s was not transitioned to %s before leaving scope (currently in state %q)",
				hs.typeName, strings.TrimPrefix(name, "port:"), hs.span, strings.Join(hs.spec.AcceptStates, "/"), hs.state)
		}
	}
}

// evalExpr applies the effects of evaluating e. source is true where a call
// that yields a new handle is allowed (its result is bound by the caller).
func (t *typestateChecker) evalExpr(expr ast.Expr, env *tsEnv, source bool) {
	if expr == nil {
		return
	}
	switch e := expr.(type) {
	case *ast.Ident:
		if id, ok := t.handleIdent(e, env); ok {
			hs := env.h[id.Name]
			if t.inLambda {
				t.err(e.Span, "%s %q cannot be captured by this closure; only a task passed to pool.submit may capture a handle", hs.typeName, id.Name)
			} else {
				t.err(e.Span, "%s %q cannot be stored, copied or passed here; a handle can only be used as a method receiver, passed to a function, moved to a variable, or returned", hs.typeName, id.Name)
			}
		} else if ht, _ := t.linear(e); ht != nil {
			if _, tracked := env.h[e.Name]; !tracked {
				t.err(e.Span, "%s %q is not owned by a variable of this function", ht.Name, e.Name)
			}
		}
		return
	case *ast.TryExpr:
		t.evalExpr(e.Inner, env, source)
		t.checkTry(e.Span, env)
		return
	case *ast.CallExpr:
		t.evalCall(e, env, source)
		return
	case *ast.LambdaExpr:
		prevL, prevT := t.inLambda, t.task
		t.inLambda, t.task = true, nil
		t.evalExpr(e.Body, env, false)
		t.inLambda, t.task = prevL, prevT
		return
	case *ast.BinaryExpr:
		t.evalExpr(e.Left, env, false)
		if e.Op == "and" || e.Op == "or" || e.Op == "implies" {
			t.evalConditional(e.Right, env)
		} else {
			t.evalExpr(e.Right, env, false)
		}
	case *ast.UnaryExpr:
		t.evalExpr(e.Expr, env, false)
	case *ast.OldExpr:
		// old(...) belongs to contracts and is not evaluated at run time, so
		// it has no effect on a handle; it still may not misuse one.
		c := env.clone()
		t.evalExpr(e.Inner, c, false)
		t.requireUnchanged(e.Span, env, c, "an old(...) expression, which is never executed,")
	case *ast.RangeExpr:
		t.evalExpr(e.Lo, env, false)
		t.evalExpr(e.Hi, env, false)
	case *ast.FieldExpr:
		t.evalExpr(e.Object, env, false)
	case *ast.IndexExpr:
		t.evalExpr(e.List, env, false)
		t.evalExpr(e.Index, env, false)
	case *ast.PipeExpr:
		t.evalExpr(e.Left, env, false)
		t.evalExpr(e.Right, env, false)
	case *ast.ListLit:
		for _, el := range e.Elems {
			t.evalExpr(el, env, false)
		}
	case *ast.MapLit:
		for _, en := range e.Entries {
			t.evalExpr(en.Key, env, false)
			t.evalExpr(en.Value, env, false)
		}
	case *ast.FStrExpr:
		for _, p := range e.Parts {
			if p.IsExpr {
				t.evalExpr(p.Expr, env, false)
			}
		}
	case *ast.MatchExpr:
		t.evalExpr(e.Subject, env, false)
		var live []*tsEnv
		for _, arm := range e.Arms {
			a := env.clone()
			t.evalConditional(arm.Guard, a)
			t.evalExpr(arm.Value, a, false)
			live = append(live, a)
		}
		if !t.matchIsTotal(e.Subject, len(e.Arms), func(i int) (ast.Pattern, ast.Expr) { return e.Arms[i].Pattern, e.Arms[i].Guard }) {
			live = append(live, env.clone())
		}
		if len(live) > 0 {
			t.join(e.Span, env, live, false)
		}
	case *ast.RunWorkflowExpr:
		if wi := t.info.Workflows[e.Name]; wi != nil {
			t.evalUserCall(e.Args, wi.Params, env)
		} else {
			t.evalArgs(e.Args, env)
		}
	case *ast.WithExpr:
		t.evalExpr(e.Base, env, false)
		for _, f := range e.Fields {
			t.evalExpr(f.Value, env, false)
		}
	}
	if ht, _ := t.linear(expr); ht != nil {
		t.err(expr.GetSpan(), "this expression yields a %s that no variable owns; bind the result of the call that produced it", ht.Name)
	}
}

// evalConditional walks an operand that may or may not be evaluated: it must
// not change the state of any handle.
func (t *typestateChecker) evalConditional(e ast.Expr, env *tsEnv) {
	if e == nil {
		return
	}
	c := env.clone()
	t.evalExpr(e, c, false)
	t.requireUnchanged(e.GetSpan(), env, c, "a conditionally evaluated expression")
	env.addLoans(c.loans)
}

func (t *typestateChecker) evalArgs(args []ast.CallArg, env *tsEnv) {
	for _, a := range args {
		if a.Own {
			t.err(a.Span, "unexpected 'own': only a user function with an `own` parameter can take ownership of a handle")
		}
		t.evalExpr(a.Value, env, false)
	}
}

func (t *typestateChecker) isPoolSubmit(ce *ast.CallExpr) bool {
	fe, ok := ce.Callee.(*ast.FieldExpr)
	if !ok || fe.Field != "submit" {
		return false
	}
	ht, ok := t.info.ExprTypes[fe.Object].(*sema.HandleType)
	return ok && ht.Name == "conc.ThreadPool"
}

func (t *typestateChecker) evalCall(e *ast.CallExpr, env *tsEnv, source bool) {
	if ht, _ := t.linear(e); ht != nil && !source {
		t.err(e.Span, "resource handle leak: this call yields a %s; bind it to a variable, match on it, or return it", ht.Name)
	}
	switch callee := e.Callee.(type) {
	case *ast.FieldExpr:
		name := ""
		if id, ok := callee.Object.(*ast.Ident); ok {
			name = id.Name
			if _, ok := t.handleIdent(id, env); ok {
				if lam := t.taskOf(e); lam != nil {
					t.walkTask(lam, name, env)
				} else {
					t.evalArgs(e.Args, env)
				}
				t.transition(e.Span, env, id.Name, callee.Field)
				if env.h[id.Name].typeName == "conc.ThreadPool" && callee.Field == "shutdown" && !t.deferred() {
					env.release(func(l loan) bool { return l.pool == name })
				}
				return
			}
			if pt, isPort := t.info.Ports[id.Name]; isPort && len(pt.Decl.States) > 0 {
				t.evalArgs(e.Args, env)
				t.checkPortCall(pt.Decl, id.Name, callee.Field, env.ports, e.Span)
				return
			}
		}
		switch objTy := t.info.ExprTypes[callee.Object].(type) {
		case *sema.HandleType:
			switch {
			case t.taskOf(e) != nil:
				t.walkTask(t.taskOf(e), name, env)
				return
			case objTy.Name == "conc.ThreadPool" && callee.Field == "shutdown" && name != "" && !t.deferred():
				env.release(func(l loan) bool { return l.pool == name })
			case objTy.Name == "Future" && callee.Field == "await" && name != "" && !t.deferred():
				env.release(func(l loan) bool { return l.fut == name })
			}
		case *sema.ModuleType:
			if objTy.Path == "std.requests" && callee.Field == "gather" && !t.deferred() {
				for _, a := range e.Args {
					if ll, ok := a.Value.(*ast.ListLit); ok {
						for _, el := range ll.Elems {
							if id, ok := el.(*ast.Ident); ok {
								env.release(func(l loan) bool { return l.fut == id.Name })
							}
						}
					}
				}
			}
		}
		t.evalExpr(callee.Object, env, false)
		t.evalArgs(e.Args, env)
	case *ast.Ident:
		if fi, ok := t.info.Funcs[callee.Name]; ok {
			t.evalUserCall(e.Args, fi.Type.Params, env)
			return
		}
		t.evalArgs(e.Args, env)
	default:
		t.evalExpr(e.Callee, env, false)
		t.evalArgs(e.Args, env)
	}
}

// taskOf returns the closure of a pool.submit(() => ...) call.
func (t *typestateChecker) taskOf(e *ast.CallExpr) *ast.LambdaExpr {
	if !t.isPoolSubmit(e) || len(e.Args) != 1 {
		return nil
	}
	lam, _ := e.Args[0].Value.(*ast.LambdaExpr)
	return lam
}

// walkTask walks the body of a closure given to pool.submit.
func (t *typestateChecker) walkTask(lam *ast.LambdaExpr, pool string, env *tsEnv) {
	prevL, prevT := t.inLambda, t.task
	// A task started by another task is not tied to a future the function
	// can await, so it may not capture handles.
	t.inLambda, t.task = prevL || prevT != nil, &taskCtx{pool: pool}
	t.evalExpr(lam.Body, env, false)
	t.inLambda, t.task = prevL, prevT
}

// evalUserCall passes args to a function or workflow with the given
// parameters: a handle is lent to a borrowed parameter and moved into an
// `own` one. The callee only runs once every argument has been evaluated, so
// the other arguments are walked first: a `?` in one of them still sees the
// handles as held by the caller, and a nested call that closes or moves one
// makes passing it here an error.
func (t *typestateChecker) evalUserCall(args []ast.CallArg, params []sema.FuncParamInfo, env *tsEnv) {
	isHandleArg := make([]bool, len(args))
	for i, a := range args {
		if _, ok := t.handleIdent(a.Value, env); ok && i < len(params) {
			isHandleArg[i] = true
			continue
		}
		if a.Own {
			// sema guarantees an `own` argument is a handle-typed variable
			if aid, isID := a.Value.(*ast.Ident); isID {
				t.err(a.Span, "%q is not a handle owned by a variable of this function", aid.Name)
			}
			continue
		}
		t.evalExpr(a.Value, env, false)
	}
	seen := map[string]bool{}
	for i, a := range args {
		if !isHandleArg[i] {
			continue
		}
		id := a.Value.(*ast.Ident)
		hs := env.h[id.Name]
		if seen[id.Name] {
			t.err(a.Span, "%s %q is passed more than once in the same call", hs.typeName, id.Name)
			continue
		}
		seen[id.Name] = true
		t.touch(id.Name)
		switch {
		case t.inLambda:
			t.err(a.Span, "%s %q cannot be captured by this closure; only a task passed to pool.submit may capture a handle", hs.typeName, id.Name)
		case !t.usable(a.Span, id.Name, hs):
		case hs.wrapped:
			t.err(a.Span, "%q is a Result/Option holding a handle; match on it before passing it on", id.Name)
		case hs.state != hs.spec.InitState:
			t.err(a.Span, "invalid use of %s %q in state %q: a handle passed to a function must be %q (use-after-close)", hs.typeName, id.Name, hs.state, hs.spec.InitState)
		case params[i].Own:
			if !hs.owned {
				t.err(a.Span, "cannot give away borrowed %s %q; only its owner can move it", hs.typeName, id.Name)
			} else if env.lent(id.Name) {
				t.err(a.Span, "cannot move %s %q while a task may still be using it; await the future or shut down the pool first", hs.typeName, id.Name)
			} else if t.task != nil && t.task.sawTry {
				// The task already owns the handle it captured; the `?`
				// would end the task before the callee receives it.
				t.err(a.Span, "resource handle leak: a `?` evaluated earlier in this task may end it before %s %q is handed over", hs.typeName, id.Name)
			} else {
				hs.moved, hs.movedAt = true, a.Span
				env.h[id.Name] = hs
			}
		case t.task != nil:
			t.lend(a.Span, env, id.Name, hs)
		}
	}
}

// lend records that a task closure borrows a handle.
func (t *typestateChecker) lend(span ast.Span, env *tsEnv, name string, hs handleState) {
	if !hs.shareable {
		t.err(span, "%s %q cannot be shared with a task; move it into the task with `own`", hs.typeName, name)
		return
	}
	env.addLoans([]loan{{handle: name, pool: t.task.pool, fresh: true}})
}

func (t *typestateChecker) transition(span ast.Span, env *tsEnv, name, method string) {
	hs := env.h[name]
	t.touch(name)
	if t.inLambda {
		t.err(span, "%s %q cannot be captured by this closure; only a task passed to pool.submit may capture a handle", hs.typeName, name)
		return
	}
	if !t.usable(span, name, hs) {
		return
	}
	if hs.wrapped {
		t.err(span, "%q is a Result/Option holding a %s; match on it before calling %s()", name, hs.typeName, method)
		return
	}
	nextMap := hs.spec.Transitions[hs.state]
	if nextMap == nil {
		t.err(span, "invalid call %s.%s() while %s is in state %q (use-after-close)", name, method, hs.typeName, hs.state)
		return
	}
	next, ok := nextMap[method]
	if !ok {
		t.err(span, "illegal operation %s.%s() in state %q of %s", name, method, hs.state, hs.typeName)
		return
	}
	if next != hs.state {
		switch {
		case t.task != nil:
			t.err(span, "a task closure cannot call %s.%s(); move %q into a function with an `own` parameter instead", name, method, name)
			return
		case !hs.owned && isAcceptingState(hs.spec, next):
			t.err(span, "cannot call %s.%s(): %s %q is borrowed; declare the parameter `own` to take ownership", name, method, hs.typeName, name)
			return
		case env.lent(name):
			t.err(span, "cannot call %s.%s() while a task may still be using %q; await the future or shut down the pool first", name, method, name)
			return
		}
	} else if t.task != nil {
		t.lend(span, env, name, hs)
	}
	hs.state = next
	env.h[name] = hs
}

func (t *typestateChecker) checkPortCall(pd *ast.PortDecl, portName, method string, st map[string]handleState, span ast.Span) {
	key := "port:" + portName
	hs, exists := st[key]
	if !exists {
		spec := &sema.TypestateSpec{
			InitState:    pd.States[0].Name,
			AcceptStates: []string{pd.States[0].Name, "Closed"},
			Transitions:  map[string]map[string]string{},
		}
		for _, psd := range pd.States {
			m := map[string]string{}
			for _, tr := range psd.Transitions {
				m[tr.Action] = tr.TargetState
			}
			spec.Transitions[psd.Name] = m
		}
		hs = handleState{typeName: key, state: spec.InitState, spec: spec, span: span}
	}
	nextMap := hs.spec.Transitions[hs.state]
	if nextMap == nil {
		t.err(span, "port %s method %s() called in terminal state %q", portName, method, hs.state)
		return
	}
	nextState, ok := nextMap[method]
	if !ok {
		t.err(span, "port protocol violation: %s.%s() not permitted in state %q", portName, method, hs.state)
		return
	}
	hs.state = nextState
	st[key] = hs
}

func isAcceptingState(spec *sema.TypestateSpec, state string) bool {
	if spec == nil {
		return true
	}
	for _, a := range spec.AcceptStates {
		if a == state {
			return true
		}
	}
	return false
}
