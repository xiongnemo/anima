package native

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
)

// EmitC generates a standalone zero-external-dependency C11 source string for a verified program.
func EmitC(info *sema.ProgramInfo) (string, error) {
	cg := &cgen{
		info:        info,
		liftedFns:   &strings.Builder{},
		fwdDecls:    &strings.Builder{},
		bodyOut:     &strings.Builder{},
		localVars:   map[string]bool{},
		freeScanSet: map[string]bool{},
	}
	if err := cg.generate(); err != nil {
		return "", err
	}
	var final strings.Builder
	final.WriteString(runtimeHeader)
	final.WriteString("\n// === Forward Declarations ===\n")
	final.WriteString(cg.fwdDecls.String())
	final.WriteString("\n// === Lifted Closures & Entity Schema Validators ===\n")
	final.WriteString(cg.liftedFns.String())
	final.WriteString("\n// === Functions & Workflows ===\n")
	final.WriteString(cg.bodyOut.String())
	return final.String(), nil
}

// BuildNative emits C11 code and compiles it via gcc -O2 into a standalone ELF executable.
func BuildNative(info *sema.ProgramInfo, outBinary string, emitCPath string) error {
	cSrc, err := EmitC(info)
	if err != nil {
		return err
	}
	cFile := emitCPath
	tempCreated := false
	if cFile == "" {
		tmp, err := os.CreateTemp("", "anima-build-*.c")
		if err != nil {
			return err
		}
		cFile = tmp.Name()
		_ = tmp.Close()
		tempCreated = true
	}
	if err := os.WriteFile(cFile, []byte(cSrc), 0644); err != nil {
		return err
	}
	if tempCreated && emitCPath == "" {
		defer os.Remove(cFile)
	}
	if outBinary == "" {
		return nil
	}
	absOut, err := filepath.Abs(outBinary)
	if err != nil {
		absOut = outBinary
	}
	cmd := exec.Command("gcc", "-std=c11", "-O2", "-Wall", "-Wno-unused-function", "-Wno-unused-variable", "-Wno-unused-but-set-variable", "-Wno-unused-label", cFile, "-lpthread", "-lssl", "-lcrypto", "-o", absOut)
	out, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("gcc failed: %v\n%s", err, string(out))
	}
	return nil
}

type cgen struct {
	info        *sema.ProgramInfo
	fwdDecls    *strings.Builder
	liftedFns   *strings.Builder
	bodyOut     *strings.Builder
	cur         *strings.Builder
	indent      int
	tmpSeq      int
	lamSeq      int
	localVars   map[string]bool
	upvalMap    map[string]int
	freeScanSet map[string]bool
	wfVars      map[string]bool
	wfCtxPtr    string
}

func (g *cgen) freshTmp(prefix string) string {
	g.tmpSeq++
	return fmt.Sprintf("__%s_%d", prefix, g.tmpSeq)
}

func (g *cgen) line(format string, args ...any) {
	for i := 0; i < g.indent; i++ {
		g.cur.WriteString("    ")
	}
	fmt.Fprintf(g.cur, format+"\n", args...)
}

func cEscapeStr(s string) string {
	var sb strings.Builder
	sb.WriteByte('"')
	for i := 0; i < len(s); i++ {
		ch := s[i]
		switch ch {
		case '"':
			sb.WriteString(`\"`)
		case '\\':
			sb.WriteString(`\\`)
		case '\n':
			sb.WriteString(`\n`)
		case '\r':
			sb.WriteString(`\r`)
		case '\t':
			sb.WriteString(`\t`)
		default:
			sb.WriteByte(ch)
		}
	}
	sb.WriteByte('"')
	return sb.String()
}

func cVarName(name string) string {
	return "av_" + name
}

func (g *cgen) generate() error {
	// 1. Monitor mutex globals
	for name := range g.info.Machines {
		fmt.Fprintf(g.fwdDecls, "static pthread_mutex_t __mon_mu_%s = PTHREAD_MUTEX_INITIALIZER;\n", name)
	}

	// 2. Entity invariants & JSON schema validators
	for _, d := range g.info.Program.Decls {
		if ent, ok := d.(*ast.EntityDecl); ok {
			g.emitEntityValidators(ent)
		}
	}
	// Built-in fallback json decode for raw map
	g.liftedFns.WriteString("static AnimaVal __json_decode_raw(const char *raw) { bool ok = true; const char *p = raw; AnimaVal v = json_parse_val(&p, &ok); if (!ok) return v_err(\"invalid json\"); return v_ok(v); }\n")

	// 3. Forward declare all user functions and workflows
	for _, d := range g.info.Program.Decls {
		switch node := d.(type) {
		case *ast.FuncDecl:
			var ps []string
			for _, p := range node.Params {
				ps = append(ps, "AnimaVal "+cVarName(p.Name))
			}
			pStr := "void"
			if len(ps) > 0 {
				pStr = strings.Join(ps, ", ")
			}
			fmt.Fprintf(g.fwdDecls, "static AnimaVal __fn_%s(%s);\n", node.Name, pStr)
		case *ast.WorkflowDecl:
			var ps []string
			for _, p := range node.Params {
				ps = append(ps, "AnimaVal "+cVarName(p.Name))
			}
			pStr := "void"
			if len(ps) > 0 {
				pStr = strings.Join(ps, ", ")
			}
			fmt.Fprintf(g.fwdDecls, "static AnimaVal __wf_%s(%s);\n", node.Name, pStr)
		}
	}

	// 4. Emit functions & workflows
	for _, d := range g.info.Program.Decls {
		switch node := d.(type) {
		case *ast.FuncDecl:
			if err := g.emitFunc(node); err != nil {
				return err
			}
		case *ast.WorkflowDecl:
			if err := g.emitWorkflow(node); err != nil {
				return err
			}
		}
	}

	// 5. Emit C main()
	g.cur = g.bodyOut
	g.line("int main(int argc, char **argv) {")
	g.indent++
	// A send to a peer that has gone is an Err, as on the VM, not a signal.
	g.line("signal(SIGPIPE, SIG_IGN);")
	g.line("g_argc = argc; g_argv = argv;")
	if _, hasMain := g.info.Funcs["main"]; hasMain {
		g.line("AnimaVal r = __fn_main();")
		g.line("if (r.kind == VAL_INT) return (int)r.u.i;")
		g.line("return 0;")
	} else {
		called := false
		for _, d := range g.info.Program.Decls {
			if wf, ok := d.(*ast.WorkflowDecl); ok && len(wf.Params) == 0 {
				g.line("__wf_%s();", wf.Name)
				called = true
				break
			}
		}
		if !called {
			g.line("return 0;")
		} else {
			g.line("return 0;")
		}
	}
	g.indent--
	g.line("}")
	return nil
}

func (g *cgen) emitEntityValidators(ent *ast.EntityDecl) {
	et := g.info.Entities[ent.Name]
	prevCur := g.cur
	prevVars := g.localVars
	prevUp := g.upvalMap
	g.cur = g.liftedFns
	g.localVars = map[string]bool{}
	g.upvalMap = nil

	// Invariant function
	fmt.Fprintf(g.fwdDecls, "static bool __inv_%s(AnimaVal __self);\n", ent.Name)
	g.line("static bool __inv_%s(AnimaVal __self) {", ent.Name)
	g.indent++
	for _, f := range et.Fields {
		g.line("AnimaVal %s = v_entity_get(__self, %s);", cVarName(f.Name), cEscapeStr(f.Name))
		g.localVars[f.Name] = true
	}
	for _, inv := range ent.Invariants {
		exprC := g.emitExpr(inv)
		g.line("if (!v_truthy(%s)) return false;", exprC)
	}
	g.line("return true;")
	g.indent--
	g.line("}")

	// JSON Schema & Invariant Decoder function
	fmt.Fprintf(g.fwdDecls, "static AnimaVal __json_decode_%s(const char *raw);\n", ent.Name)
	g.line("static AnimaVal __json_decode_%s(const char *raw) {", ent.Name)
	g.indent++
	g.line("bool ok = true; const char *p = raw;")
	g.line("AnimaVal m = json_parse_val(&p, &ok);")
	g.line("if (!ok || m.kind != VAL_MAP) return v_err(\"invalid json object\");")
	g.line("AnimaVal ent = v_entity_new(%s);", cEscapeStr(ent.Name))
	for _, f := range et.Fields {
		g.line("AnimaVal f_%s = v_map_get(m, %s);", f.Name, cEscapeStr(f.Name))
		switch f.Type.Kind() {
		case sema.KindInt:
			g.line("if (f_%s.kind != VAL_INT) return v_err(\"field %s.%s must be int\");", f.Name, ent.Name, f.Name)
			if it, ok := f.Type.(*sema.IntType); ok && it.IsBounded {
				g.line("if (f_%s.u.i < %dLL || f_%s.u.i > %dLL) return v_err(\"field %s.%s out of range\");", f.Name, it.Lo, f.Name, it.Hi, ent.Name, f.Name)
			}
		case sema.KindBool:
			g.line("if (f_%s.kind != VAL_BOOL) return v_err(\"field %s.%s must be bool\");", f.Name, ent.Name, f.Name)
		case sema.KindStr:
			g.line("if (f_%s.kind != VAL_STR) return v_err(\"field %s.%s must be str\");", f.Name, ent.Name, f.Name)
		}
		g.line("v_entity_set(ent, %s, f_%s);", cEscapeStr(f.Name), f.Name)
	}
	g.line("if (!__inv_%s(ent)) return v_err(\"entity invariant violated\");", ent.Name)
	g.line("return v_ok(ent);")
	g.indent--
	g.line("}")

	g.cur = prevCur
	g.localVars = prevVars
	g.upvalMap = prevUp
}

func (g *cgen) emitFunc(fn *ast.FuncDecl) error {
	g.cur = g.bodyOut
	g.localVars = map[string]bool{}
	g.upvalMap = nil
	g.wfVars = nil

	var ps []string
	for _, p := range fn.Params {
		ps = append(ps, "AnimaVal "+cVarName(p.Name))
		g.localVars[p.Name] = true
	}
	pStr := "void"
	if len(ps) > 0 {
		pStr = strings.Join(ps, ", ")
	}
	g.line("static AnimaVal __fn_%s(%s) {", fn.Name, pStr)
	g.indent++
	for _, lv := range collectStmtLocals(fn.Body) {
		if !g.localVars[lv] {
			g.localVars[lv] = true
			g.line("AnimaVal %s = v_void();", cVarName(lv))
		}
	}
	for _, st := range fn.Body {
		if err := g.emitStmt(st); err != nil {
			return err
		}
	}
	g.line("return v_void();")
	g.indent--
	g.line("}")
	return nil
}

func (g *cgen) emitWorkflow(wf *ast.WorkflowDecl) error {
	// Collect workflow params + locals into a context struct
	varNames := map[string]bool{}
	var varOrder []string
	addVar := func(name string) {
		if !varNames[name] {
			varNames[name] = true
			varOrder = append(varOrder, name)
		}
	}
	for _, p := range wf.Params {
		addVar(p.Name)
	}
	for _, v := range collectWfAssignVars(wf) {
		addVar(v)
	}

	ctxName := "__wfctx_" + wf.Name
	fmt.Fprintf(g.fwdDecls, "typedef struct {\n")
	for _, vn := range varOrder {
		fmt.Fprintf(g.fwdDecls, "    AnimaVal %s;\n", cVarName(vn))
	}
	for _, pl := range wf.Pools {
		fmt.Fprintf(g.fwdDecls, "    AnimaVal pool_%s;\n", pl.Name)
	}
	fmt.Fprintf(g.fwdDecls, "} %s;\n", ctxName)

	// Emit fork branch thread worker functions into liftedFns
	prevCur := g.cur
	prevVars := g.localVars
	prevWfVars := g.wfVars
	prevCtx := g.wfCtxPtr
	g.wfVars = varNames
	g.wfCtxPtr = "ctx"

	forkWorkerMap := map[string][]string{}
	for _, n := range wf.Nodes {
		fk, ok := n.(*ast.ForkNode)
		if !ok {
			continue
		}
		var workers []string
		for _, br := range fk.Branches {
			wfn := fmt.Sprintf("__wf_%s_br_%s_%s", wf.Name, fk.Name, br.Name)
			workers = append(workers, wfn)
			fmt.Fprintf(g.fwdDecls, "static void *%s(void *arg);\n", wfn)
			g.cur = g.liftedFns
			g.localVars = map[string]bool{}
			g.line("static void *%s(void *arg) {", wfn)
			g.indent++
			g.line("%s *ctx = (%s *)arg;", ctxName, ctxName)
			for _, op := range br.Ops {
				switch op.Kind {
				case ast.BranchAcquire:
					g.line("hdl_sem_acquire(ctx->pool_%s.u.hdl);", op.Target)
				case ast.BranchRelease:
					g.line("hdl_sem_release(ctx->pool_%s.u.hdl);", op.Target)
				case ast.BranchSync:
					mon := strings.SplitN(op.Target, ".", 2)[0]
					if _, exists := g.info.Machines[mon]; exists {
						g.line("pthread_mutex_lock(&__mon_mu_%s);", mon)
						g.line("pthread_mutex_unlock(&__mon_mu_%s);", mon)
					}
				case ast.BranchStmt:
					if err := g.emitStmt(op.Stmt); err != nil {
						return err
					}
				}
			}
			g.line("return NULL;")
			g.indent--
			g.line("}")
		}
		forkWorkerMap[fk.Name] = workers
	}

	g.cur = g.bodyOut
	g.localVars = map[string]bool{}
	var ps []string
	for _, p := range wf.Params {
		ps = append(ps, "AnimaVal "+cVarName(p.Name))
	}
	pStr := "void"
	if len(ps) > 0 {
		pStr = strings.Join(ps, ", ")
	}
	g.line("static AnimaVal __wf_%s(%s) {", wf.Name, pStr)
	g.indent++
	g.line("%s ctx_val = {0};", ctxName)
	g.line("%s *ctx = &ctx_val;", ctxName)
	for _, p := range wf.Params {
		g.line("ctx->%s = %s;", cVarName(p.Name), cVarName(p.Name))
	}
	for _, pl := range wf.Pools {
		g.line("ctx->pool_%s = conc_sem_new(%d);", pl.Name, pl.Capacity)
	}

	// Map workflow steps & choices & joins
	var startNode *ast.StartNode
	steps := map[string]*ast.StepNode{}
	choices := map[string]*ast.ChoiceNode{}
	forks := map[string]*ast.ForkNode{}
	joins := map[string]*ast.JoinNode{}
	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.StartNode:
			startNode = x
		case *ast.StepNode:
			steps[x.Name] = x
		case *ast.ChoiceNode:
			k := x.After
			if k == "" {
				k = x.Name
			}
			choices[k] = x
		case *ast.ForkNode:
			forks[x.Name] = x
		case *ast.JoinNode:
			joins[x.Name] = x
		}
	}

	// Emit label-based workflow state machine
	if startNode != nil {
		for _, st := range startNode.Body {
			if err := g.emitStmt(st); err != nil {
				return err
			}
		}
		g.line("goto wf_lbl_%s;", startNode.Target)
	}
	for _, st := range steps {
		g.line("wf_lbl_%s: ;", st.Name)
		for _, s := range st.Body {
			if err := g.emitStmt(s); err != nil {
				return err
			}
		}
		if st.Target != "" {
			g.line("goto wf_lbl_%s;", st.Target)
		} else if ch, ok := choices[st.Name]; ok {
			g.emitChoiceGoto(ch)
		} else {
			// Check fork/step after st.Name
			for _, fk := range forks {
				if fk.After == st.Name {
					g.line("goto wf_lbl_%s;", fk.Name)
				}
			}
			for _, nxt := range steps {
				if nxt.After == st.Name {
					g.line("goto wf_lbl_%s;", nxt.Name)
				}
			}
		}
	}
	for name, ch := range choices {
		if _, isStep := steps[name]; !isStep {
			g.line("wf_lbl_%s: ;", name)
			g.emitChoiceGoto(ch)
		}
	}
	for _, fk := range forks {
		g.line("wf_lbl_%s: ;", fk.Name)
		workers := forkWorkerMap[fk.Name]
		if len(workers) > 0 {
			g.line("{")
			g.indent++
			g.line("pthread_t __tids[%d];", len(workers))
			for i, wfn := range workers {
				g.line("pthread_create(&__tids[%d], NULL, %s, ctx);", i, wfn)
			}
			for i := range workers {
				g.line("pthread_join(__tids[%d], NULL);", i)
			}
			g.indent--
			g.line("}")
		}
		for jname := range joins {
			g.line("goto wf_lbl_%s;", jname)
			break
		}
	}
	for _, jn := range joins {
		g.line("wf_lbl_%s: ;", jn.Name)
		if jn.Target != "" {
			g.line("goto wf_lbl_%s;", jn.Target)
		} else {
			for _, st := range steps {
				if st.After == jn.Name {
					g.line("goto wf_lbl_%s;", st.Name)
				}
			}
		}
	}
	g.line("wf_lbl_done: ;")
	g.line("wf_lbl_END: ;")
	g.line("return v_void();")
	g.indent--
	g.line("}")

	g.cur = prevCur
	g.localVars = prevVars
	g.wfVars = prevWfVars
	g.wfCtxPtr = prevCtx
	return nil
}

func (g *cgen) emitChoiceGoto(ch *ast.ChoiceNode) {
	for _, br := range ch.Branches {
		if br.IsElse {
			g.line("goto wf_lbl_%s;", br.Target)
			return
		}
		condC := g.emitExpr(br.Guard)
		g.line("if (v_truthy(%s)) goto wf_lbl_%s;", condC, br.Target)
	}
}

func collectStmtLocals(stmts []ast.Stmt) []string {
	seen := map[string]bool{}
	var out []string
	add := func(n string) {
		if n != "" && n != "_" && !seen[n] {
			seen[n] = true
			out = append(out, n)
		}
	}
	var scanPat func(ast.Pattern)
	scanPat = func(p ast.Pattern) {
		switch x := p.(type) {
		case *ast.VarPat:
			add(x.Name)
		case *ast.VariantPat:
			for _, sub := range x.Fields {
				scanPat(sub)
			}
		}
	}
	var scanExpr func(ast.Expr)
	scanExpr = func(e ast.Expr) {
		if e == nil {
			return
		}
		switch x := e.(type) {
		case *ast.MatchExpr:
			scanExpr(x.Subject)
			for _, arm := range x.Arms {
				scanPat(arm.Pattern)
				scanExpr(arm.Value)
			}
		case *ast.CallExpr:
			scanExpr(x.Callee)
			for _, a := range x.Args {
				scanExpr(a.Value)
			}
		case *ast.PipeExpr:
			scanExpr(x.Left)
			scanExpr(x.Right)
		}
	}
	var scan func([]ast.Stmt)
	scan = func(ss []ast.Stmt) {
		for _, s := range ss {
			switch x := s.(type) {
			case *ast.LetAssignStmt:
				add(x.Name)
				scanExpr(x.Value)
			case *ast.ReturnStmt:
				scanExpr(x.Value)
			case *ast.ExprStmt:
				scanExpr(x.Expr)
			case *ast.IfStmt:
				for _, br := range x.Branches {
					scan(br.Body)
				}
				scan(x.Else)
			case *ast.MatchStmt:
				for _, arm := range x.Arms {
					scanPat(arm.Pattern)
					scan(arm.Body)
				}
			case *ast.ForStmt:
				add(x.Var)
				scan(x.Body)
			case *ast.WhileStmt:
				scan(x.Body)
			}
		}
	}
	scan(stmts)
	return out
}

func collectWfAssignVars(wf *ast.WorkflowDecl) []string {
	seen := map[string]bool{}
	var out []string
	var scan func([]ast.Stmt)
	scan = func(stmts []ast.Stmt) {
		for _, s := range stmts {
			switch x := s.(type) {
			case *ast.LetAssignStmt:
				if !seen[x.Name] {
					seen[x.Name] = true
					out = append(out, x.Name)
				}
			case *ast.IfStmt:
				for _, br := range x.Branches {
					scan(br.Body)
				}
				scan(x.Else)
			case *ast.MatchStmt:
				for _, arm := range x.Arms {
					scan(arm.Body)
				}
			case *ast.ForStmt:
				if !seen[x.Var] {
					seen[x.Var] = true
					out = append(out, x.Var)
				}
				scan(x.Body)
			case *ast.WhileStmt:
				scan(x.Body)
			}
		}
	}
	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.StartNode:
			scan(x.Body)
		case *ast.StepNode:
			scan(x.Body)
		case *ast.ForkNode:
			for _, br := range x.Branches {
				for _, op := range br.Ops {
					if op.Kind == ast.BranchStmt && op.Stmt != nil {
						scan([]ast.Stmt{op.Stmt})
					}
				}
			}
		}
	}
	return out
}

func (g *cgen) varRef(name string) string {
	if g.upvalMap != nil {
		if idx, ok := g.upvalMap[name]; ok {
			return fmt.Sprintf("__upvals[%d]", idx)
		}
	}
	if g.wfVars != nil && g.wfVars[name] && g.wfCtxPtr != "" {
		return g.wfCtxPtr + "->" + cVarName(name)
	}
	return cVarName(name)
}

func (g *cgen) ensureVarDeclared(name string) string {
	if g.wfVars != nil && g.wfVars[name] && g.wfCtxPtr != "" {
		return g.wfCtxPtr + "->" + cVarName(name)
	}
	if !g.localVars[name] {
		g.localVars[name] = true
		g.line("AnimaVal %s = v_void();", cVarName(name))
	}
	return cVarName(name)
}

func (g *cgen) emitStmt(stmt ast.Stmt) error {
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		if me, ok := s.Value.(*ast.MatchExpr); ok {
			dest := g.ensureVarDeclared(s.Name)
			return g.emitMatchExprAssign(me, dest)
		}
		valC := g.emitExpr(s.Value)
		dest := g.ensureVarDeclared(s.Name)
		g.line("%s = %s;", dest, valC)

	case *ast.CompoundAssignStmt:
		// The target is read before the right-hand side runs, as on the VM.
		opSym := "+"
		if s.Op == "-=" {
			opSym = "-"
		} else if s.Op == "*=" {
			opSym = "*"
		}
		switch tgt := s.Target.(type) {
		case *ast.Ident:
			vref := g.varRef(tgt.Name)
			cur := g.freshTmp("cur")
			g.line("AnimaVal %s = %s;", cur, vref)
			rhsC := g.emitExpr(s.Value)
			g.line("%s = v_int(%s.u.i %s (%s).u.i);", vref, cur, opSym, rhsC)
		case *ast.FieldExpr:
			objC := g.emitExpr(tgt.Object)
			curF := g.freshTmp("fld")
			g.line("AnimaVal %s = v_entity_get(%s, %s);", curF, objC, cEscapeStr(tgt.Field))
			rhsC := g.emitExpr(s.Value)
			g.line("v_entity_set(%s, %s, v_int(%s.u.i %s (%s).u.i));", objC, cEscapeStr(tgt.Field), curF, opSym, rhsC)
		case *ast.IndexExpr:
			lC := g.emitExpr(tgt.List)
			iC := g.emitExpr(tgt.Index)
			cur := g.freshTmp("elem")
			g.line("AnimaVal %s = v_index_get(%s, %s);", cur, lC, iC)
			rhsC := g.emitExpr(s.Value)
			g.line("v_index_set(%s, %s, v_int(%s.u.i %s (%s).u.i));", lC, iC, cur, opSym, rhsC)
		}

	case *ast.FieldAssignStmt:
		objC := g.emitExpr(s.Object)
		valC := g.emitExpr(s.Value)
		g.line("v_entity_set(%s, %s, %s);", objC, cEscapeStr(s.Field), valC)

	case *ast.IndexAssignStmt:
		lC := g.emitExpr(s.List)
		iC := g.emitExpr(s.Index)
		vC := g.emitExpr(s.Value)
		g.line("v_index_set(%s, %s, %s);", lC, iC, vC)

	case *ast.IfStmt:
		// An elif condition may emit statements, so it is nested in the
		// else block of the branch before it.
		nested := 0
		for idx, br := range s.Branches {
			if idx > 0 {
				g.line("} else {")
				g.indent++
				nested++
			}
			condC := g.emitExpr(br.Cond)
			g.line("if (v_truthy(%s)) {", condC)
			g.indent++
			for _, bs := range br.Body {
				if err := g.emitStmt(bs); err != nil {
					return err
				}
			}
			g.indent--
		}
		if len(s.Else) > 0 {
			g.line("} else {")
			g.indent++
			for _, es := range s.Else {
				if err := g.emitStmt(es); err != nil {
					return err
				}
			}
			g.indent--
		}
		g.line("}")
		for ; nested > 0; nested-- {
			g.indent--
			g.line("}")
		}

	case *ast.WhileStmt:
		g.line("while (1) {")
		g.indent++
		condC := g.emitExpr(s.Cond)
		g.line("if (!v_truthy(%s)) break;", condC)
		for _, bs := range s.Body {
			if err := g.emitStmt(bs); err != nil {
				return err
			}
		}
		g.indent--
		g.line("}")

	case *ast.ForStmt:
		if rng, ok := s.Iterable.(*ast.RangeExpr); ok {
			loC := g.emitExpr(rng.Lo)
			hiC := g.emitExpr(rng.Hi)
			idxVar := g.freshTmp("i")
			hiVar := g.freshTmp("hi")
			vref := g.ensureVarDeclared(s.Var)
			g.line("int64_t %s = (%s).u.i, %s = (%s).u.i;", idxVar, loC, hiVar, hiC)
			g.line("for (; %s < %s; %s++) {", idxVar, hiVar, idxVar)
			g.indent++
			g.line("%s = v_int(%s);", vref, idxVar)
			for _, bs := range s.Body {
				if err := g.emitStmt(bs); err != nil {
					return err
				}
			}
			g.indent--
			g.line("}")
		} else {
			listC := g.emitExpr(s.Iterable)
			lvar := g.freshTmp("lst")
			idxVar := g.freshTmp("idx")
			vref := g.ensureVarDeclared(s.Var)
			g.line("AnimaVal %s = %s;", lvar, listC)
			g.line("for (size_t %s = 0; %s.kind == VAL_LIST && %s.u.list && %s < %s.u.list->len; %s++) {",
				idxVar, lvar, lvar, idxVar, lvar, idxVar)
			g.indent++
			g.line("%s = %s.u.list->items[%s];", vref, lvar, idxVar)
			for _, bs := range s.Body {
				if err := g.emitStmt(bs); err != nil {
					return err
				}
			}
			g.indent--
			g.line("}")
		}

	case *ast.MatchStmt:
		return g.emitMatchArms(s.Subject, len(s.Arms),
			func(i int) (ast.Pattern, ast.Expr) { return s.Arms[i].Pattern, s.Arms[i].Guard },
			func(i int) error {
				for _, bs := range s.Arms[i].Body {
					if err := g.emitStmt(bs); err != nil {
						return err
					}
				}
				return nil
			})

	case *ast.ReturnStmt:
		if s.Value == nil {
			g.line("return v_void();")
			return nil
		}
		if me, ok := s.Value.(*ast.MatchExpr); ok {
			tmp := g.freshTmp("mret")
			g.line("AnimaVal %s = v_none();", tmp)
			if err := g.emitMatchExprAssign(me, tmp); err != nil {
				return err
			}
			g.line("return %s;", tmp)
			return nil
		}
		valC := g.emitExpr(s.Value)
		g.line("return %s;", valC)

	case *ast.ExprStmt:
		valC := g.emitExpr(s.Expr)
		g.line("(void)(%s);", valC)
	}
	return nil
}

// emitMatchArms tries the arms in order and runs body for the first whose
// pattern matches and whose guard holds; a failed guard falls through to the
// next arm.
func (g *cgen) emitMatchArms(subject ast.Expr, n int, arm func(i int) (ast.Pattern, ast.Expr), body func(i int) error) error {
	subjC := g.emitExpr(subject)
	subjTmp := g.freshTmp("msubj")
	done := g.freshTmp("mdone")
	g.line("AnimaVal %s = %s;", subjTmp, subjC)
	g.line("bool %s = false;", done)
	for i := 0; i < n; i++ {
		pat, guard := arm(i)
		g.line("if (!%s && %s) {", done, g.emitPatternCond(pat, subjTmp))
		g.indent++
		// An arm whose guard fails binds nothing: its names get their
		// values back.
		var restore []string
		if guard != nil {
			for _, name := range patternNames(pat) {
				dst := g.ensureVarDeclared(name)
				sv := g.freshTmp("msave")
				g.line("AnimaVal %s = %s;", sv, dst)
				restore = append(restore, fmt.Sprintf("%s = %s;", dst, sv))
			}
		}
		g.emitPatternBinds(pat, subjTmp)
		if guard != nil {
			guardC := g.emitExpr(guard)
			g.line("if (v_truthy(%s)) {", guardC)
			g.indent++
		}
		g.line("%s = true;", done)
		if err := body(i); err != nil {
			return err
		}
		if guard != nil {
			g.indent--
			g.line("} else {")
			g.indent++
			for k := len(restore) - 1; k >= 0; k-- {
				g.line("%s", restore[k])
			}
			g.indent--
			g.line("}")
		}
		g.indent--
		g.line("}")
	}
	return nil
}

func (g *cgen) emitMatchExprAssign(me *ast.MatchExpr, dest string) error {
	return g.emitMatchArms(me.Subject, len(me.Arms),
		func(i int) (ast.Pattern, ast.Expr) { return me.Arms[i].Pattern, me.Arms[i].Guard },
		func(i int) error {
			g.line("%s = %s;", dest, g.emitExpr(me.Arms[i].Value))
			return nil
		})
}

func (g *cgen) emitPatternCond(pat ast.Pattern, subj string) string {
	switch p := pat.(type) {
	case *ast.WildcardPat, *ast.VarPat:
		return "true"
	case *ast.IntPat:
		return fmt.Sprintf("(%s.kind == VAL_INT && %s.u.i == %dLL)", subj, subj, p.Value)
	case *ast.RangePat:
		return fmt.Sprintf("(%s.kind == VAL_INT && %s.u.i >= %dLL && %s.u.i <= %dLL)", subj, subj, p.Lo, subj, p.Hi)
	case *ast.BoolPat:
		b := "false"
		if p.Value {
			b = "true"
		}
		return fmt.Sprintf("(%s.kind == VAL_BOOL && %s.u.b == %s)", subj, subj, b)
	case *ast.StrPat:
		return fmt.Sprintf("(%s.kind == VAL_STR && strcmp(%s.u.s, %s) == 0)", subj, subj, cEscapeStr(p.Value))
	case *ast.VariantPat:
		cond := fmt.Sprintf("v_is_variant(%s, %s)", subj, cEscapeStr(p.Name))
		for i, sub := range p.Fields {
			switch sub.(type) {
			case *ast.WildcardPat, *ast.VarPat:
				continue
			}
			cond += " && " + g.emitPatternCond(sub, fmt.Sprintf("v_variant_field(%s, %d)", subj, i))
		}
		return "(" + cond + ")"
	}
	return "true"
}

// patternNames lists the names pat binds.
func patternNames(pat ast.Pattern) []string {
	switch p := pat.(type) {
	case *ast.VarPat:
		return []string{p.Name}
	case *ast.VariantPat:
		var out []string
		for _, sub := range p.Fields {
			out = append(out, patternNames(sub)...)
		}
		return out
	}
	return nil
}

func (g *cgen) emitPatternBinds(pat ast.Pattern, subj string) {
	switch p := pat.(type) {
	case *ast.VarPat:
		dst := g.ensureVarDeclared(p.Name)
		g.line("%s = %s;", dst, subj)
	case *ast.VariantPat:
		for i, sub := range p.Fields {
			g.emitPatternBinds(sub, fmt.Sprintf("v_variant_field(%s, %d)", subj, i))
		}
	}
}

// emitExpr returns a C expression for expr. Calls, workflow runs, and reads of
// fields and elements a later call could change, are evaluated into a temporary right
// here, so an expression runs once and in source order as it does on the VM:
// C leaves the evaluation order of operands and arguments unspecified.
func (g *cgen) emitExpr(expr ast.Expr) string {
	c := g.emitExprInline(expr)
	switch expr.(type) {
	case *ast.CallExpr, *ast.RunWorkflowExpr, *ast.FieldExpr, *ast.IndexExpr:
		tmp := g.freshTmp("val")
		g.line("AnimaVal %s = %s;", tmp, c)
		return tmp
	}
	return c
}

func (g *cgen) emitExprInline(expr ast.Expr) string {
	switch e := expr.(type) {
	case *ast.IntLit:
		return fmt.Sprintf("v_int(%dLL)", e.Value)
	case *ast.BoolLit:
		if e.Value {
			return "v_bool(true)"
		}
		return "v_bool(false)"
	case *ast.StrLit:
		return fmt.Sprintf("v_str(%s)", cEscapeStr(e.Value))
	case *ast.NoneLit:
		return "v_none()"
	case *ast.FStrExpr:
		if len(e.Parts) == 0 {
			return `v_str("")`
		}
		var acc string
		for i, p := range e.Parts {
			var cur string
			if !p.IsExpr {
				cur = fmt.Sprintf("v_str(%s)", cEscapeStr(p.Text))
			} else {
				cur = g.emitExpr(p.Expr)
			}
			if i == 0 {
				acc = cur
			} else {
				tmp := g.freshTmp("fs")
				g.line("AnimaVal %s = v_str_cat(%s, %s);", tmp, acc, cur)
				acc = tmp
			}
		}
		return acc
	case *ast.Ident:
		if _, isVar := g.info.Variants[e.Name]; isVar {
			return fmt.Sprintf("v_variant(%s, 0, NULL)", cEscapeStr(e.Name))
		}
		return g.varRef(e.Name)
	case *ast.UnaryExpr:
		inner := g.emitExpr(e.Expr)
		if e.Op == "-" {
			return fmt.Sprintf("v_int(-(%s).u.i)", inner)
		}
		if e.Op == "not" {
			return fmt.Sprintf("v_bool(!v_truthy(%s))", inner)
		}
	case *ast.BinaryExpr:
		l := g.emitExpr(e.Left)
		switch e.Op {
		case "and", "or", "implies":
			// The right operand may emit statements; run them only when it
			// is evaluated.
			res := g.freshTmp("sc")
			if e.Op == "and" {
				g.line("AnimaVal %s = v_bool(false);", res)
				g.line("if (v_truthy(%s)) {", l)
			} else if e.Op == "or" {
				g.line("AnimaVal %s = v_bool(true);", res)
				g.line("if (!v_truthy(%s)) {", l)
			} else {
				g.line("AnimaVal %s = v_bool(true);", res)
				g.line("if (v_truthy(%s)) {", l)
			}
			g.indent++
			r := g.emitExpr(e.Right)
			g.line("%s = v_bool(v_truthy(%s));", res, r)
			g.indent--
			g.line("}")
			return res
		}
		r := g.emitExpr(e.Right)
		switch e.Op {
		case "+":
			if lt, ok := g.info.ExprTypes[e.Left]; ok && lt.Kind() == sema.KindStr {
				return fmt.Sprintf("v_str_cat(%s, %s)", l, r)
			}
			return fmt.Sprintf("v_int((%s).u.i + (%s).u.i)", l, r)
		case "-":
			return fmt.Sprintf("v_int((%s).u.i - (%s).u.i)", l, r)
		case "*":
			return fmt.Sprintf("v_int((%s).u.i * (%s).u.i)", l, r)
		case "/":
			return fmt.Sprintf("v_div(%s, %s, %d)", l, r, e.Span.Line)
		case "%":
			return fmt.Sprintf("v_mod(%s, %s, %d)", l, r, e.Span.Line)
		case "==":
			return fmt.Sprintf("v_bool(v_eq(%s, %s))", l, r)
		case "!=":
			return fmt.Sprintf("v_bool(!v_eq(%s, %s))", l, r)
		case "<", "<=", ">", ">=":
			// Integers are compared in place; v_order also orders strings.
			if lt, ok := g.info.ExprTypes[e.Left]; ok && lt.Kind() == sema.KindInt {
				if rt, ok := g.info.ExprTypes[e.Right]; ok && rt.Kind() == sema.KindInt {
					return fmt.Sprintf("v_bool((%s).u.i %s (%s).u.i)", l, e.Op, r)
				}
			}
			return fmt.Sprintf("v_bool(v_order(%s, %s) %s 0)", l, r, e.Op)
		case "in":
			return fmt.Sprintf("v_bool(v_in(%s, %s))", l, r)
		}
	case *ast.ListLit:
		if len(e.Elems) == 0 {
			return "v_list_new(0, NULL)"
		}
		arr := g.freshTmp("arr")
		var items []string
		for _, el := range e.Elems {
			items = append(items, g.emitExpr(el))
		}
		g.line("AnimaVal %s[%d] = {%s};", arr, len(items), strings.Join(items, ", "))
		return fmt.Sprintf("v_list_new(%d, %s)", len(items), arr)
	case *ast.MapLit:
		m := g.freshTmp("map")
		g.line("AnimaVal %s = v_map_new();", m)
		for _, ent := range e.Entries {
			k := g.emitExpr(ent.Key)
			v := g.emitExpr(ent.Value)
			g.line("{ char *__ks = v_to_cstr(%s); v_map_set(%s, __ks, %s); free(__ks); }", k, m, v)
		}
		return m
	case *ast.FieldExpr:
		obj := g.emitExpr(e.Object)
		return fmt.Sprintf("v_entity_get(%s, %s)", obj, cEscapeStr(e.Field))
	case *ast.IndexExpr:
		lst := g.emitExpr(e.List)
		idx := g.emitExpr(e.Index)
		return fmt.Sprintf("v_index_get(%s, %s)", lst, idx)
	case *ast.WithExpr:
		base := g.emitExpr(e.Base)
		cp := g.freshTmp("with")
		g.line("AnimaVal %s = v_entity_clone(%s);", cp, base)
		for _, fld := range e.Fields {
			fv := g.emitExpr(fld.Value)
			g.line("v_entity_set(%s, %s, %s);", cp, cEscapeStr(fld.Name), fv)
		}
		return cp
	case *ast.TryExpr:
		inner := g.emitExpr(e.Inner)
		res := g.freshTmp("try")
		g.line("AnimaVal %s = %s;", res, inner)
		g.line("if (v_is_variant(%s, \"Err\") || v_is_variant(%s, \"None\") || %s.kind == VAL_NONE) {", res, res, res)
		g.indent++
		g.line("return %s;", res)
		g.indent--
		g.line("}")
		return fmt.Sprintf("v_variant_field(%s, 0)", res)
	case *ast.LambdaExpr:
		return g.emitLambda(e)
	case *ast.PipeExpr:
		if ce, ok := e.Right.(*ast.CallExpr); ok {
			newArgs := append([]ast.CallArg{{Span: e.Span, Value: e.Left}}, ce.Args...)
			return g.emitExpr(&ast.CallExpr{Span: e.Span, Callee: ce.Callee, TypeArgs: ce.TypeArgs, Args: newArgs})
		}
		if id, ok := e.Right.(*ast.Ident); ok {
			return g.emitExpr(&ast.CallExpr{Span: e.Span, Callee: id, Args: []ast.CallArg{{Span: e.Span, Value: e.Left}}})
		}
	case *ast.RunWorkflowExpr:
		var args []string
		for _, a := range e.Args {
			args = append(args, g.emitExpr(a.Value))
		}
		return fmt.Sprintf("__wf_%s(%s)", e.Name, strings.Join(args, ", "))
	case *ast.MatchExpr:
		tmp := g.freshTmp("mexpr")
		g.line("AnimaVal %s = v_none();", tmp)
		if err := g.emitMatchExprAssign(e, tmp); err != nil {
			return "v_void()"
		}
		return tmp
	case *ast.CallExpr:
		return g.emitCallExpr(e)
	}
	return "v_void()"
}

func (g *cgen) emitLambda(lam *ast.LambdaExpr) string {
	g.lamSeq++
	lname := fmt.Sprintf("__lam_%d", g.lamSeq)

	// Collect free vars (captured upvalues) present in g.localVars or g.wfVars
	paramSet := map[string]bool{}
	for _, p := range lam.Params {
		paramSet[p] = true
	}
	var freeVars []string
	seen := map[string]bool{}
	collectFreeVarsExpr(lam.Body, paramSet, g.localVars, g.wfVars, &freeVars, seen)

	fmt.Fprintf(g.fwdDecls, "static AnimaVal %s(AnimaVal *__upvals, int __argc, AnimaVal *__argv);\n", lname)

	prevCur := g.cur
	prevVars := g.localVars
	prevUp := g.upvalMap

	g.cur = g.liftedFns
	g.localVars = map[string]bool{}
	g.upvalMap = map[string]int{}
	for i, fv := range freeVars {
		g.upvalMap[fv] = i
	}
	g.line("static AnimaVal %s(AnimaVal *__upvals, int __argc, AnimaVal *__argv) {", lname)
	g.indent++
	g.line("(void)__upvals; (void)__argc; (void)__argv;")
	for i, p := range lam.Params {
		g.line("AnimaVal %s = (%d < __argc) ? __argv[%d] : v_void();", cVarName(p), i, i)
		g.localVars[p] = true
	}
	bodyC := g.emitExpr(lam.Body)
	g.line("return %s;", bodyC)
	g.indent--
	g.line("}")

	g.cur = prevCur
	g.localVars = prevVars
	g.upvalMap = prevUp

	if len(freeVars) == 0 {
		return fmt.Sprintf("v_closure(%s, 0, NULL)", lname)
	}
	arr := g.freshTmp("ups")
	var refs []string
	for _, fv := range freeVars {
		refs = append(refs, g.varRef(fv))
	}
	g.line("AnimaVal %s[%d] = {%s};", arr, len(refs), strings.Join(refs, ", "))
	return fmt.Sprintf("v_closure(%s, %d, %s)", lname, len(refs), arr)
}

func collectFreeVarsExpr(expr ast.Expr, params, locals, wfVars map[string]bool, out *[]string, seen map[string]bool) {
	if expr == nil {
		return
	}
	switch e := expr.(type) {
	case *ast.Ident:
		if !params[e.Name] && !seen[e.Name] && (locals[e.Name] || (wfVars != nil && wfVars[e.Name])) {
			seen[e.Name] = true
			*out = append(*out, e.Name)
		}
	case *ast.UnaryExpr:
		collectFreeVarsExpr(e.Expr, params, locals, wfVars, out, seen)
	case *ast.BinaryExpr:
		collectFreeVarsExpr(e.Left, params, locals, wfVars, out, seen)
		collectFreeVarsExpr(e.Right, params, locals, wfVars, out, seen)
	case *ast.FieldExpr:
		collectFreeVarsExpr(e.Object, params, locals, wfVars, out, seen)
	case *ast.IndexExpr:
		collectFreeVarsExpr(e.List, params, locals, wfVars, out, seen)
		collectFreeVarsExpr(e.Index, params, locals, wfVars, out, seen)
	case *ast.CallExpr:
		collectFreeVarsExpr(e.Callee, params, locals, wfVars, out, seen)
		for _, a := range e.Args {
			collectFreeVarsExpr(a.Value, params, locals, wfVars, out, seen)
		}
	case *ast.ListLit:
		for _, el := range e.Elems {
			collectFreeVarsExpr(el, params, locals, wfVars, out, seen)
		}
	}
}

func (g *cgen) emitCallExpr(e *ast.CallExpr) string {
	// 1. Entity constructor
	if id, ok := e.Callee.(*ast.Ident); ok {
		if et, isEnt := g.info.Entities[id.Name]; isEnt {
			tmp := g.freshTmp("ent")
			g.line("AnimaVal %s = v_entity_new(%s);", tmp, cEscapeStr(id.Name))
			for i, a := range e.Args {
				fname := a.Name
				if fname == "" && i < len(et.Fields) {
					fname = et.Fields[i].Name
				}
				vc := g.emitExpr(a.Value)
				g.line("v_entity_set(%s, %s, %s);", tmp, cEscapeStr(fname), vc)
			}
			return tmp
		}
		if _, isVar := g.info.Variants[id.Name]; isVar {
			if len(e.Args) == 0 {
				return fmt.Sprintf("v_variant(%s, 0, NULL)", cEscapeStr(id.Name))
			}
			arr := g.freshTmp("vf")
			var items []string
			for _, a := range e.Args {
				items = append(items, g.emitExpr(a.Value))
			}
			g.line("AnimaVal %s[%d] = {%s};", arr, len(items), strings.Join(items, ", "))
			return fmt.Sprintf("v_variant(%s, %d, %s)", cEscapeStr(id.Name), len(items), arr)
		}
	}

	// 2. Module or method calls
	if fe, ok := e.Callee.(*ast.FieldExpr); ok {
		if objID, ok := fe.Object.(*ast.Ident); ok {
			if modPath, isImp := g.info.Imports[objID.Name]; isImp {
				if modPath == "std.fp" {
					return g.emitPrelude(fe.Field, e)
				}
				return g.emitStdlibCall(modPath, fe.Field, e)
			}
			if _, isPort := g.info.Ports[objID.Name]; isPort {
				return "v_void()"
			}
		}
		recv := g.emitExpr(fe.Object)
		return g.emitMethodCall(recv, fe.Field, e)
	}

	// 3. Built-in / User / Closure calls
	if id, ok := e.Callee.(*ast.Ident); ok {
		// Closure variable?
		if g.localVars[id.Name] || (g.upvalMap != nil && g.upvalMap[id.Name] >= 0 && func() bool { _, ok := g.upvalMap[id.Name]; return ok }()) {
			if len(e.Args) == 0 {
				return fmt.Sprintf("v_call_clos(%s, 0, NULL)", g.varRef(id.Name))
			}
			arr := g.freshTmp("cargs")
			var items []string
			for _, a := range e.Args {
				items = append(items, g.emitExpr(a.Value))
			}
			g.line("AnimaVal %s[%d] = {%s};", arr, len(items), strings.Join(items, ", "))
			return fmt.Sprintf("v_call_clos(%s, %d, %s)", g.varRef(id.Name), len(items), arr)
		}

		// User function?
		if fi, isUser := g.info.Funcs[id.Name]; isUser {
			args := e.Args
			if len(args) == len(fi.Type.Params) {
				hasKw := false
				for _, a := range args {
					if a.Name != "" {
						hasKw = true
						break
					}
				}
				if hasKw {
					ordered := make([]ast.CallArg, len(args))
					byName := map[string]int{}
					for i, p := range fi.Type.Params {
						byName[p.Name] = i
					}
					for i, a := range args {
						if a.Name != "" {
							ordered[byName[a.Name]] = a
						} else {
							ordered[i] = a
						}
					}
					args = ordered
				}
			}
			var items []string
			for _, a := range args {
				items = append(items, g.emitExpr(a.Value))
			}
			return fmt.Sprintf("__fn_%s(%s)", id.Name, strings.Join(items, ", "))
		}

		return g.emitPrelude(id.Name, e)
	}
	return "v_void()"
}

// emitPrelude emits a call of the built-in function or pipeline stage name,
// however the program names it: `take(...)` in a pipeline or `fp.take(...)`.
func (g *cgen) emitPrelude(name string, e *ast.CallExpr) string {
	{
		var args []string
		for _, a := range e.Args {
			args = append(args, g.emitExpr(a.Value))
		}
		switch name {
		case "len":
			return fmt.Sprintf("v_int(anima_len(%s))", args[0])
		case "print":
			if len(args) == 1 {
				return fmt.Sprintf("anima_print(%s)", args[0])
			}
			if len(args) == 0 {
				return "anima_print_n(0, NULL)"
			}
			arr := g.freshTmp("pargs")
			g.line("AnimaVal %s[%d] = {%s};", arr, len(args), strings.Join(args, ", "))
			return fmt.Sprintf("anima_print_n(%d, %s)", len(args), arr)
		case "str", "to_str":
			tmp := g.freshTmp("s")
			g.line("char *%s_c = v_to_cstr(%s); AnimaVal %s = v_str(%s_c); free(%s_c);", tmp, args[0], tmp, tmp, tmp)
			return tmp
		case "abs":
			return fmt.Sprintf("v_int(llabs((%s).u.i))", args[0])
		case "min":
			return fmt.Sprintf("(((%s).u.i < (%s).u.i) ? (%s) : (%s))", args[0], args[1], args[0], args[1])
		case "max":
			return fmt.Sprintf("(((%s).u.i > (%s).u.i) ? (%s) : (%s))", args[0], args[1], args[0], args[1])
		case "assert":
			// As on the VM: the message, when one is given, is what is reported.
			if len(args) >= 2 {
				g.line("if (!v_truthy(%s)) { fflush(stdout); fprintf(stderr, \"runtime error: %%s\\n\", v_to_cstr(%s)); exit(1); }", args[0], args[1])
			} else {
				g.line("if (!v_truthy(%s)) { fflush(stdout); fprintf(stderr, \"runtime error: assertion failed\\n\"); exit(1); }", args[0])
			}
			return "v_void()"
		case "Some":
			return fmt.Sprintf("v_some(%s)", args[0])
		case "Ok":
			return fmt.Sprintf("v_ok(%s)", args[0])
		case "Err":
			return fmt.Sprintf("v_err((%s).u.s)", args[0])
		case "filter":
			return fmt.Sprintf("fp_filter(%s, %s)", args[0], args[1])
		case "map":
			return fmt.Sprintf("fp_map(%s, %s)", args[0], args[1])
		case "flat_map":
			return fmt.Sprintf("fp_flat_map(%s, %s)", args[0], args[1])
		case "fold":
			return fmt.Sprintf("fp_fold(%s, %s, %s)", args[0], args[1], args[2])
		case "sum":
			return fmt.Sprintf("fp_sum(%s)", args[0])
		case "any":
			return fmt.Sprintf("fp_any(%s, %s)", args[0], args[1])
		case "all":
			return fmt.Sprintf("fp_all(%s, %s)", args[0], args[1])
		case "find":
			return fmt.Sprintf("fp_find(%s, %s)", args[0], args[1])
		case "take":
			return fmt.Sprintf("fp_take(%s, %s)", args[0], args[1])
		case "drop":
			return fmt.Sprintf("fp_drop(%s, %s)", args[0], args[1])
		case "filter_ok":
			return fmt.Sprintf("fp_filter_ok(%s)", args[0])
		case "unwrap_or":
			return fmt.Sprintf("fp_unwrap_or(%s, %s)", args[0], args[1])
		case "and_then":
			return fmt.Sprintf("fp_and_then(%s, %s)", args[0], args[1])
		}
	}
	return "v_void()"
}

func (g *cgen) emitStdlibCall(modPath, member string, e *ast.CallExpr) string {
	var args []string
	var timeoutArg string
	for _, a := range e.Args {
		ec := g.emitExpr(a.Value)
		if a.Name == "timeout_ms" {
			timeoutArg = ec
		} else {
			args = append(args, ec)
		}
	}
	if timeoutArg == "" && len(args) > 1 && (member == "get" || member == "post") {
		if member == "get" && len(args) >= 2 {
			timeoutArg = args[1]
		} else if member == "post" && len(args) >= 3 {
			timeoutArg = args[2]
		}
	}
	if timeoutArg == "" {
		timeoutArg = "v_int(5000)"
	}

	switch modPath + "." + member {
	case "std.socket.listen_tcp":
		return fmt.Sprintf("sock_listen_tcp((%s).u.s, (%s).u.i)", args[0], args[1])
	case "std.socket.connect_tcp":
		return fmt.Sprintf("sock_connect_tcp((%s).u.s, (%s).u.i)", args[0], args[1])
	case "std.requests.get":
		return fmt.Sprintf("http_do(\"GET\", (%s).u.s, \"\", (%s).u.i)", args[0], timeoutArg)
	case "std.requests.post":
		return fmt.Sprintf("http_do(\"POST\", (%s).u.s, (%s).u.s, (%s).u.i)", args[0], args[1], timeoutArg)
	case "std.requests.Session":
		psz := "v_int(4)"
		if len(args) >= 1 {
			psz = args[0]
		}
		return fmt.Sprintf("req_session_new((%s).u.i)", psz)
	case "std.requests.gather":
		return fmt.Sprintf("req_gather(%s)", args[0])
	case "std.concurrent.ThreadPool":
		return fmt.Sprintf("conc_threadpool_new((%s).u.i, (%s).u.i)", args[0], args[1])
	case "std.concurrent.Channel":
		capC := "v_int(8)"
		if len(args) >= 1 {
			capC = args[0]
		}
		return fmt.Sprintf("conc_channel_new((%s).u.i)", capC)
	case "std.concurrent.Mutex":
		iv := "v_void()"
		if len(args) >= 1 {
			iv = args[0]
		}
		return fmt.Sprintf("conc_mutex_new(%s)", iv)
	case "std.concurrent.Semaphore":
		return fmt.Sprintf("conc_sem_new((%s).u.i)", args[0])
	case "std.concurrent.parallel_map":
		return fmt.Sprintf("conc_parallel_map(%s, %s)", args[0], args[1])
	case "std.json.encode":
		return fmt.Sprintf("json_encode(%s)", args[0])
	case "std.json.decode":
		if len(e.TypeArgs) == 1 {
			tname := strings.TrimSpace(e.TypeArgs[0].String())
			if _, isEnt := g.info.Entities[tname]; isEnt {
				return fmt.Sprintf("__json_decode_%s((%s).u.s)", tname, args[0])
			}
		}
		return fmt.Sprintf("__json_decode_raw((%s).u.s)", args[0])
	case "std.bytes.from_str":
		return fmt.Sprintf("bytes_from_str((%s).u.s)", args[0])
	case "std.bytes.from_hex":
		return fmt.Sprintf("bytes_from_hex((%s).u.s)", args[0])
	case "std.crypto.sha256":
		return fmt.Sprintf("crypto_sha256((%s).u.s)", args[0])
	case "std.crypto.hmac_sha256":
		return fmt.Sprintf("crypto_hmac_sha256((%s).u.s, (%s).u.s)", args[0], args[1])
	case "std.crypto.constant_time_eq":
		return fmt.Sprintf("crypto_ct_eq((%s).u.s, (%s).u.s)", args[0], args[1])
	case "std.fs.open":
		mode := `"r"`
		if len(args) >= 2 {
			mode = fmt.Sprintf("(%s).u.s", args[1])
		}
		return fmt.Sprintf("fs_open((%s).u.s, %s)", args[0], mode)
	case "std.fs.read_text":
		return fmt.Sprintf("fs_read_text((%s).u.s)", args[0])
	case "std.fs.write_atomic":
		return fmt.Sprintf("fs_write_atomic((%s).u.s, (%s).u.s)", args[0], args[1])
	case "std.cli.args":
		tmp := g.freshTmp("cargs")
		g.line("AnimaVal %s = v_list_new(0, NULL); for (int _ai = 0; _ai < g_argc; _ai++) v_list_push(%s, v_str(g_argv[_ai]));", tmp, tmp)
		return tmp
	case "std.cli.env_get":
		tmp := g.freshTmp("env")
		g.line("const char *%s_p = getenv((%s).u.s); AnimaVal %s = %s_p ? v_some(v_str(%s_p)) : v_none();", tmp, args[0], tmp, tmp, tmp)
		return tmp
	case "std.time.now_ms":
		return "time_now_ms()"
	case "std.time.sleep_ms":
		g.line("if ((%s).u.i > 0) { struct timespec __ts = { (%s).u.i / 1000, ((%s).u.i %% 1000) * 1000000L }; nanosleep(&__ts, NULL); }", args[0], args[0], args[0])
		return "v_void()"
	}
	return "v_void()"
}

func (g *cgen) emitMethodCall(recv, method string, e *ast.CallExpr) string {
	var args []string
	var timeoutArg string
	for _, a := range e.Args {
		ec := g.emitExpr(a.Value)
		if a.Name == "timeout_ms" {
			timeoutArg = ec
		} else {
			args = append(args, ec)
		}
	}
	if timeoutArg == "" && len(args) >= 1 && method == "accept" {
		timeoutArg = args[0]
	}
	if timeoutArg == "" && len(args) >= 2 && (method == "get" || method == "get_async") {
		timeoutArg = args[1]
	}
	if timeoutArg == "" && len(args) >= 3 && method == "post" {
		timeoutArg = args[2]
	}
	if timeoutArg == "" {
		timeoutArg = "v_int(5000)"
	}

	switch method {
	case "len":
		return fmt.Sprintf("v_int(anima_len(%s))", recv)
	case "port":
		return fmt.Sprintf("hdl_listener_port(%s)", recv)
	case "accept":
		return fmt.Sprintf("hdl_listener_accept(%s, (%s).u.i)", recv, timeoutArg)
	case "send_text":
		return fmt.Sprintf("hdl_stream_send(%s, (%s).u.s)", recv, args[0])
	case "recv_text":
		maxb := "v_int(4096)"
		if len(args) >= 1 {
			maxb = args[0]
		}
		return fmt.Sprintf("hdl_stream_recv(%s, (%s).u.i)", recv, maxb)
	case "close", "shutdown":
		g.line("hdl_close(%s);", recv)
		return "v_void()"
	case "get":
		if ht, ok := g.info.ExprTypes[e.Callee.(*ast.FieldExpr).Object].(*sema.HandleType); ok && ht.Name == "conc.Mutex" {
			tmp := g.freshTmp("mg")
			g.line("pthread_mutex_lock(&(%s).u.hdl->mu); AnimaVal %s = (%s).u.hdl->cell_val; pthread_mutex_unlock(&(%s).u.hdl->mu);", recv, tmp, recv, recv)
			return tmp
		}
		return fmt.Sprintf("http_do(\"GET\", (%s).u.s, \"\", (%s).u.i)", args[0], timeoutArg)
	case "post":
		return fmt.Sprintf("http_do(\"POST\", (%s).u.s, (%s).u.s, (%s).u.i)", args[0], args[1], timeoutArg)
	case "get_async":
		return fmt.Sprintf("req_session_get_async(%s, (%s).u.s, (%s).u.i)", recv, args[0], timeoutArg)
	case "await":
		return fmt.Sprintf("fut_await(%s)", recv)
	case "submit":
		return fmt.Sprintf("conc_pool_submit(%s, %s)", recv, args[0])
	case "send":
		return fmt.Sprintf("conc_chan_send(%s, %s)", recv, args[0])
	case "recv":
		return fmt.Sprintf("conc_chan_recv(%s)", recv)
	case "set":
		g.line("pthread_mutex_lock(&(%s).u.hdl->mu); (%s).u.hdl->cell_val = %s; pthread_mutex_unlock(&(%s).u.hdl->mu);", recv, recv, args[0], recv)
		return "v_void()"
	case "with_lock":
		g.line("conc_mutex_with_lock(%s, %s);", recv, args[0])
		return "v_void()"
	case "read_text":
		return fmt.Sprintf("fs_file_read_text(%s)", recv)
	case "write_text":
		return fmt.Sprintf("fs_file_write_text(%s, (%s).u.s)", recv, args[0])
	case "slice":
		return fmt.Sprintf("bytes_slice(%s, (%s).u.i, (%s).u.i)", recv, args[0], args[1])
	case "acquire":
		g.line("hdl_sem_acquire((%s).u.hdl);", recv)
		return "v_void()"
	case "release":
		g.line("hdl_sem_release((%s).u.hdl);", recv)
		return "v_void()"
	case "read_u8":
		return fmt.Sprintf("v_int((%s).u.hdl->bytes[(%s).u.i])", recv, args[0])
	case "read_u16_be":
		tmp := g.freshTmp("u16")
		g.line("const uint8_t *%s_p = (%s).u.hdl->bytes + (%s).u.i; AnimaVal %s = v_int(((int64_t)%s_p[0] << 8) | %s_p[1]);", tmp, recv, args[0], tmp, tmp, tmp)
		return tmp
	case "read_u32_be":
		tmp := g.freshTmp("u32")
		g.line("const uint8_t *%s_p = (%s).u.hdl->bytes + (%s).u.i; AnimaVal %s = v_int(((int64_t)%s_p[0] << 24) | ((int64_t)%s_p[1] << 16) | ((int64_t)%s_p[2] << 8) | %s_p[3]);",
			tmp, recv, args[0], tmp, tmp, tmp, tmp, tmp)
		return tmp
	}
	return "v_void()"
}
