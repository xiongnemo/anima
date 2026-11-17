package lts

import (
	"fmt"
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

// Verify runs SWEN90004 FSP/LTS composition, Safety, Deadlock, Tarjan SCC Progress,
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
// Linear Resource Typestate Verifier (Sockets, Files, Ports)
// ---------------------------------------------------------------------------

type handleState struct {
	typeName string
	state    string
	spec     *sema.TypestateSpec
	span     ast.Span
}

type typestateChecker struct {
	info          *sema.ProgramInfo
	errs          []TypestateError
	resultHandles map[string]handleMeta
}

type handleMeta struct {
	typeName string
	spec     *sema.TypestateSpec
}

func cloneHandles(m map[string]handleState) map[string]handleState {
	cp := make(map[string]handleState, len(m))
	for k, v := range m {
		cp[k] = v
	}
	return cp
}

func (t *typestateChecker) err(span ast.Span, fn, msg string) {
	t.errs = append(t.errs, TypestateError{Span: span, Func: fn, Message: msg})
}

func (t *typestateChecker) checkFunc(fn *ast.FuncDecl) {
	st := map[string]handleState{}
	t.resultHandles = map[string]handleMeta{}
	terminated := t.walkBlock(fn.Body, st, "def "+fn.Name)
	if !terminated {
		t.checkLeaks(fn.Span, "def "+fn.Name, st, "")
	}
}

func (t *typestateChecker) checkWorkflow(wf *ast.WorkflowDecl) {
	st := map[string]handleState{}
	t.resultHandles = map[string]handleMeta{}
	for _, n := range wf.Nodes {
		switch node := n.(type) {
		case *ast.StartNode:
			t.walkBlock(node.Body, st, "workflow "+wf.Name)
		case *ast.ForkNode:
			for _, br := range node.Branches {
				brSt := cloneHandles(st)
				for _, op := range br.Ops {
					if op.Kind == ast.BranchStmt && op.Stmt != nil {
						t.walkStmt(op.Stmt, brSt, "workflow "+wf.Name)
					}
				}
				t.checkLeaks(br.Span, "workflow "+wf.Name+"."+br.Name, brSt, "")
			}
		case *ast.StepNode:
			t.walkBlock(node.Body, st, "workflow "+wf.Name)
		}
	}
	t.checkLeaks(wf.Span, "workflow "+wf.Name, st, "")
}

func (t *typestateChecker) walkBlock(stmts []ast.Stmt, st map[string]handleState, fn string) bool {
	for _, s := range stmts {
		if t.walkStmt(s, st, fn) {
			return true
		}
	}
	return false
}

func (t *typestateChecker) walkStmt(stmt ast.Stmt, st map[string]handleState, fn string) bool {
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		t.evalExprEffects(s.Value, st, fn, false)
		if specName, spec, isWrappedResult := t.detectOpenedHandleKind(s.Value); spec != nil {
			if isWrappedResult {
				if t.resultHandles == nil {
					t.resultHandles = map[string]handleMeta{}
				}
				t.resultHandles[s.Name] = handleMeta{typeName: specName, spec: spec}
			} else {
				st[s.Name] = handleState{
					typeName: specName,
					state:    spec.InitState,
					spec:     spec,
					span:     s.Span,
				}
			}
		}

	case *ast.FieldAssignStmt:
		t.evalExprEffects(s.Value, st, fn, false)

	case *ast.CompoundAssignStmt:
		t.evalExprEffects(s.Value, st, fn, false)

	case *ast.IfStmt:
		allTerm := true
		var liveBranches []map[string]handleState
		for _, br := range s.Branches {
			t.evalExprEffects(br.Cond, st, fn, false)
			bst := cloneHandles(st)
			term := t.walkBlock(br.Body, bst, fn)
			if !term {
				allTerm = false
				liveBranches = append(liveBranches, bst)
			}
		}
		if len(s.Else) > 0 {
			est := cloneHandles(st)
			term := t.walkBlock(s.Else, est, fn)
			if !term {
				allTerm = false
				liveBranches = append(liveBranches, est)
			}
		} else {
			allTerm = false
			liveBranches = append(liveBranches, cloneHandles(st))
		}
		if allTerm {
			return true
		}
		// Merge handle states conservatively: if any live branch kept handle open, keep it open!
		merged := map[string]handleState{}
		for _, b := range liveBranches {
			for k, hs := range b {
				if prev, ok := merged[k]; ok {
					if !isAcceptingState(hs.spec, hs.state) && isAcceptingState(prev.spec, prev.state) {
						merged[k] = hs
					}
				} else {
					merged[k] = hs
				}
			}
		}
		for k := range st {
			delete(st, k)
		}
		for k, v := range merged {
			st[k] = v
		}

	case *ast.MatchStmt:
		t.evalExprEffects(s.Subject, st, fn, false)
		// If matching on a Result/Option that produces a linear handle (e.g. Ok(conn)), bind conn in Ok arm!
		openedName, openedSpec, _ := t.detectOpenedHandleKind(s.Subject)
		if openedSpec == nil {
			if id, ok := s.Subject.(*ast.Ident); ok && t.resultHandles != nil {
				if hm, exists := t.resultHandles[id.Name]; exists {
					openedName = hm.typeName
					openedSpec = hm.spec
				}
			}
		}
		allTerm := true
		var liveArms []map[string]handleState
		for _, arm := range s.Arms {
			astMap := cloneHandles(st)
			if vp, ok := arm.Pattern.(*ast.VariantPat); ok && (vp.Name == "Ok" || vp.Name == "Some") && openedSpec != nil && len(vp.Fields) == 1 {
				if bindP, ok := vp.Fields[0].(*ast.VarPat); ok {
					astMap[bindP.Name] = handleState{typeName: openedName, state: openedSpec.InitState, spec: openedSpec, span: arm.Span}
				}
			}
			term := t.walkBlock(arm.Body, astMap, fn)
			if !term {
				allTerm = false
				t.checkNewHandleLeaks(arm.Span, fn, st, astMap)
				liveArms = append(liveArms, astMap)
			}
		}
		if allTerm {
			return true
		}
		_ = liveArms

	case *ast.WhileStmt:
		t.evalExprEffects(s.Cond, st, fn, false)
		wst := cloneHandles(st)
		t.walkBlock(s.Body, wst, fn)
		t.checkNewHandleLeaks(s.Span, fn, st, wst)

	case *ast.ForStmt:
		fst := cloneHandles(st)
		t.walkBlock(s.Body, fst, fn)
		t.checkNewHandleLeaks(s.Span, fn, st, fst)

	case *ast.ReturnStmt:
		returnedVar := ""
		if s.Value != nil {
			t.evalExprEffects(s.Value, st, fn, false)
			if id, ok := s.Value.(*ast.Ident); ok {
				returnedVar = id.Name
			} else if ce, ok := s.Value.(*ast.CallExpr); ok && len(ce.Args) == 1 {
				if id, ok := ce.Args[0].Value.(*ast.Ident); ok {
					returnedVar = id.Name
				}
			}
		}
		t.checkLeaks(s.Span, fn, st, returnedVar)
		return true

	case *ast.ExprStmt:
		t.evalExprEffects(s.Expr, st, fn, false)
	}
	return false
}

func (t *typestateChecker) evalExprEffects(expr ast.Expr, st map[string]handleState, fn string, insideTry bool) {
	if expr == nil {
		return
	}
	switch e := expr.(type) {
	case *ast.TryExpr:
		t.evalExprEffects(e.Inner, st, fn, true)
	case *ast.BinaryExpr:
		t.evalExprEffects(e.Left, st, fn, insideTry)
		t.evalExprEffects(e.Right, st, fn, insideTry)
	case *ast.UnaryExpr:
		t.evalExprEffects(e.Expr, st, fn, insideTry)
	case *ast.PipeExpr:
		t.evalExprEffects(e.Left, st, fn, insideTry)
		t.evalExprEffects(e.Right, st, fn, insideTry)
	case *ast.CallExpr:
		for _, a := range e.Args {
			t.evalExprEffects(a.Value, st, fn, insideTry)
		}
		if fe, ok := e.Callee.(*ast.FieldExpr); ok {
			if id, ok := fe.Object.(*ast.Ident); ok {
				// 1. Check handle variable methods (conn.send_text, conn.close, etc.)
				if hs, exists := st[id.Name]; exists && hs.spec != nil {
					nextMap := hs.spec.Transitions[hs.state]
					if nextMap == nil {
						t.err(e.Span, fn, fmt.Sprintf("invalid call %s.%s() while %s is in state %q (use-after-close)", id.Name, fe.Field, hs.typeName, hs.state))
						return
					}
					nextState, ok := nextMap[fe.Field]
					if !ok {
						t.err(e.Span, fn, fmt.Sprintf("illegal operation %s.%s() in state %q of %s", id.Name, fe.Field, hs.state, hs.typeName))
						return
					}
					hs.state = nextState
					st[id.Name] = hs
					return
				}
				// 2. Check user-defined port protocol transitions
				if pt, isPort := t.info.Ports[id.Name]; isPort && len(pt.Decl.States) > 0 {
					t.checkPortCall(pt.Decl, id.Name, fe.Field, st, e.Span, fn)
				}
			}
		}
	}
}

func (t *typestateChecker) checkPortCall(pd *ast.PortDecl, portName, method string, st map[string]handleState, span ast.Span, fn string) {
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
		t.err(span, fn, fmt.Sprintf("port %s method %s() called in terminal state %q", portName, method, hs.state))
		return
	}
	nextState, ok := nextMap[method]
	if !ok {
		t.err(span, fn, fmt.Sprintf("port protocol violation: %s.%s() not permitted in state %q", portName, method, hs.state))
		return
	}
	hs.state = nextState
	st[key] = hs
}

func (t *typestateChecker) detectOpenedHandleKind(expr ast.Expr) (string, *sema.TypestateSpec, bool) {
	isTry := false
	if te, ok := expr.(*ast.TryExpr); ok {
		isTry = true
		expr = te.Inner
	}
	ce, ok := expr.(*ast.CallExpr)
	if !ok {
		return "", nil, false
	}
	fe, ok := ce.Callee.(*ast.FieldExpr)
	if !ok {
		return "", nil, false
	}
	objTy, ok := t.info.ExprTypes[fe.Object]
	if !ok {
		return "", nil, false
	}
	if mt, ok := objTy.(*sema.ModuleType); ok {
		switch mt.Path + "." + fe.Field {
		case "std.socket.listen_tcp":
			return "sock.TcpListener", t.info.StdHandles["sock.TcpListener"], !isTry
		case "std.socket.connect_tcp":
			return "sock.TcpStream", t.info.StdHandles["sock.TcpStream"], !isTry
		case "std.fs.open":
			return "fs.File", t.info.StdHandles["fs.File"], !isTry
		}
	}
	if ht, ok := objTy.(*sema.HandleType); ok {
		if ht.Name == "sock.TcpListener" && fe.Field == "accept" {
			return "sock.TcpStream", t.info.StdHandles["sock.TcpStream"], !isTry
		}
	}
	return "", nil, false
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

func (t *typestateChecker) checkLeaks(span ast.Span, fn string, st map[string]handleState, returnedVar string) {
	for name, hs := range st {
		if name == returnedVar {
			continue
		}
		if !isAcceptingState(hs.spec, hs.state) {
			t.err(span, fn, fmt.Sprintf("resource handle leak: %s %q opened at %s was not transitioned to %s before leaving scope (currently in state %q)",
				hs.typeName, strings.TrimPrefix(name, "port:"), hs.span, strings.Join(hs.spec.AcceptStates, "/"), hs.state))
		}
	}
}

func (t *typestateChecker) checkNewHandleLeaks(span ast.Span, fn string, outer, inner map[string]handleState) {
	for k, hs := range inner {
		if _, existed := outer[k]; !existed {
			if !isAcceptingState(hs.spec, hs.state) {
				t.err(span, fn, fmt.Sprintf("resource handle leak in inner block: %s %q left in state %q", hs.typeName, k, hs.state))
			}
		}
	}
}
