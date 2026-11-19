package vm

import (
	"fmt"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
)

// WorkflowStepCompiled holds compiled bytecode function names for workflow execution.
type WorkflowCompiled struct {
	Name        string
	Params      []string
	Pools       map[string]int64
	StartTarget string
	StartFn     string
	Steps       map[string]WorkflowStepMeta
	Choices     map[string]WorkflowChoiceMeta
	Forks       map[string]WorkflowForkMeta
	Joins       map[string]WorkflowJoinMeta
	Merges      map[string]WorkflowMergeMeta
}

type WorkflowStepMeta struct {
	Name   string
	After  string
	Target string
	FnName string
}

type WorkflowChoiceBranchMeta struct {
	GuardFn string
	IsElse  bool
	Target  string
}

type WorkflowChoiceMeta struct {
	After    string
	Branches []WorkflowChoiceBranchMeta
}

type WorkflowBranchOpMeta struct {
	Kind   int // 0=stmt, 1=sync, 2=acquire, 3=release, 4=stepref
	Target string
	FnName string
}

type WorkflowBranchMeta struct {
	Name string
	Ops  []WorkflowBranchOpMeta
}

type WorkflowForkMeta struct {
	Name     string
	After    string
	Branches []WorkflowBranchMeta
}

type WorkflowJoinMeta struct {
	Name   string
	Target string
}

type WorkflowMergeMeta struct {
	Name   string
	Afters []string
	Target string
}

type CompiledProgram struct {
	Module    *BytecodeModule
	Workflows map[string]*WorkflowCompiled
	Machines  map[string]*ast.MachineDecl
	Entities  map[string]*sema.EntityType
}

// Compile translates a semantically checked ProgramInfo into a BytecodeModule (.anbc) + workflow tables.
func Compile(info *sema.ProgramInfo, rawSource string, verified bool) (*CompiledProgram, error) {
	c := &compiler{
		info: info,
		mod: &BytecodeModule{
			File:        info.Program.File,
			EntityIndex: map[string]int{},
			FuncIndex:   map[string]int{},
			WorkflowIdx: map[string]int{},
		},
		constMap:   map[string]int{},
		callMap:    map[string]int{},
		wfCompiled: map[string]*WorkflowCompiled{},
		machines:   map[string]*ast.MachineDecl{},
	}

	// Register entities & compile invariant checker bytecode functions
	for _, d := range info.Program.Decls {
		if ent, ok := d.(*ast.EntityDecl); ok {
			if err := c.compileEntity(ent); err != nil {
				return nil, err
			}
		}
		if m, ok := d.(*ast.MachineDecl); ok {
			c.machines[m.Name] = m
		}
	}
	// Also register built-in HttpResponse entity schema
	if hr, ok := info.Entities["HttpResponse"]; ok && c.mod.EntityIndex["HttpResponse"] == 0 && len(c.mod.Entities) == 0 {
		_ = c.registerBuiltinEntity(hr)
	} else if hr, ok := info.Entities["HttpResponse"]; ok {
		if _, exists := c.mod.EntityIndex["HttpResponse"]; !exists {
			_ = c.registerBuiltinEntity(hr)
		}
	}

	// Compile user functions
	for _, d := range info.Program.Decls {
		if fn, ok := d.(*ast.FuncDecl); ok {
			if err := c.compileFunc(fn); err != nil {
				return nil, err
			}
		}
	}

	// Compile workflows
	for _, d := range info.Program.Decls {
		if wf, ok := d.(*ast.WorkflowDecl); ok {
			if err := c.compileWorkflow(wf); err != nil {
				return nil, err
			}
		}
	}

	c.mod.Seal(rawSource, verified)
	return &CompiledProgram{
		Module:    c.mod,
		Workflows: c.wfCompiled,
		Machines:  c.machines,
		Entities:  info.Entities,
	}, nil
}

type compiler struct {
	info       *sema.ProgramInfo
	mod        *BytecodeModule
	constMap   map[string]int
	callMap    map[string]int
	wfCompiled map[string]*WorkflowCompiled
	machines   map[string]*ast.MachineDecl
	lambdaSeq  int
}

func (c *compiler) addIntConst(v int64) uint32 {
	k := fmt.Sprintf("I:%d", v)
	if idx, ok := c.constMap[k]; ok {
		return uint32(idx)
	}
	idx := len(c.mod.Constants)
	c.mod.Constants = append(c.mod.Constants, Constant{Kind: ConstInt, Int: v})
	c.constMap[k] = idx
	return uint32(idx)
}

func (c *compiler) addStrConst(s string) uint32 {
	k := "S:" + s
	if idx, ok := c.constMap[k]; ok {
		return uint32(idx)
	}
	idx := len(c.mod.Constants)
	c.mod.Constants = append(c.mod.Constants, Constant{Kind: ConstStr, Str: s})
	c.constMap[k] = idx
	return uint32(idx)
}

func (c *compiler) addCallMeta(cm CallMeta) uint16 {
	idx := len(c.mod.CallMetas)
	c.mod.CallMetas = append(c.mod.CallMetas, cm)
	return uint16(idx)
}

func (c *compiler) addFieldMeta(names []string) uint16 {
	idx := len(c.mod.FieldMetas)
	c.mod.FieldMetas = append(c.mod.FieldMetas, FieldMeta{Names: names})
	return uint16(idx)
}

func (c *compiler) registerBuiltinEntity(et *sema.EntityType) int {
	es := EntitySchema{Name: et.Name}
	for _, f := range et.Fields {
		fs := EntityFieldSchema{Name: f.Name, Kind: typeKindStr(f.Type)}
		if it, ok := f.Type.(*sema.IntType); ok && it.IsBounded {
			fs.HasLo, fs.HasHi, fs.Lo, fs.Hi = true, true, it.Lo, it.Hi
		}
		es.Fields = append(es.Fields, fs)
	}
	idx := len(c.mod.Entities)
	c.mod.Entities = append(c.mod.Entities, es)
	c.mod.EntityIndex[et.Name] = idx
	return idx
}

func (c *compiler) compileEntity(ent *ast.EntityDecl) error {
	et := c.info.Entities[ent.Name]
	idx := c.registerBuiltinEntity(et)
	if len(ent.Invariants) == 0 {
		return nil
	}
	// Compile invariant function: __inv_<Name>(self) -> bool
	fnName := "__inv_" + ent.Name
	fc := newFnCompiler(c, fnName, []string{"__self"}, nil)
	for _, f := range et.Fields {
		slot := fc.declareLocal(f.Name)
		fc.emit(EncodeImm(OpLoadLocal, 0), ent.Span.Line)
		fc.emit(EncodeImm(OpGetField, c.addStrConst(f.Name)), ent.Span.Line)
		fc.emit(EncodeImm(OpStoreLocal, uint32(slot)), ent.Span.Line)
	}
	var failJumps []int
	for i, inv := range ent.Invariants {
		if err := fc.compileExpr(inv); err != nil {
			return err
		}
		if i < len(ent.Invariants)-1 {
			failJumps = append(failJumps, fc.emitJump(OpJmpIfFalsePeek, ent.Span.Line))
			fc.emit(EncodeImm(OpPop, 0), ent.Span.Line)
		}
	}
	endJ := fc.emitJump(OpJmp, ent.Span.Line)
	for _, fj := range failJumps {
		fc.patchJump(fj)
	}
	fc.patchJump(endJ)
	fc.emit(EncodeABC(OpRet, 1, 0), ent.Span.Line)
	fc.finish()
	c.mod.Entities[idx].Invariants = []string{fnName}
	return nil
}

func typeKindStr(t sema.Type) string {
	switch t.Kind() {
	case sema.KindInt:
		return "int"
	case sema.KindBool:
		return "bool"
	case sema.KindStr:
		return "str"
	default:
		return "any"
	}
}

func (c *compiler) compileFunc(fn *ast.FuncDecl) error {
	var pnames []string
	for _, p := range fn.Params {
		pnames = append(pnames, p.Name)
	}
	fc := newFnCompiler(c, fn.Name, pnames, nil)
	for _, st := range fn.Body {
		if err := fc.compileStmt(st); err != nil {
			return err
		}
	}
	fc.emit(EncodeABC(OpRet, 0, 0), fn.Span.Line)
	fc.finish()
	return nil
}

func (c *compiler) compileSynthFunc(name string, params []string, stmts []ast.Stmt, retExpr ast.Expr, line int) error {
	fc := newFnCompiler(c, name, params, nil)
	for _, st := range stmts {
		if err := fc.compileStmt(st); err != nil {
			return err
		}
	}
	if retExpr != nil {
		if err := fc.compileExpr(retExpr); err != nil {
			return err
		}
		fc.emit(EncodeABC(OpRet, 1, 0), line)
	} else {
		fc.emit(EncodeABC(OpRet, 0, 0), line)
	}
	fc.finish()
	return nil
}

func (c *compiler) compileWorkflow(wf *ast.WorkflowDecl) error {
	var pnames []string
	for _, p := range wf.Params {
		pnames = append(pnames, p.Name)
	}
	wfc := &WorkflowCompiled{
		Name:    wf.Name,
		Params:  pnames,
		Pools:   map[string]int64{},
		Steps:   map[string]WorkflowStepMeta{},
		Choices: map[string]WorkflowChoiceMeta{},
		Forks:   map[string]WorkflowForkMeta{},
		Joins:   map[string]WorkflowJoinMeta{},
		Merges:  map[string]WorkflowMergeMeta{},
	}
	for _, pl := range wf.Pools {
		wfc.Pools[pl.Name] = pl.Capacity
	}

	// Collect all workflow-scoped variable names so steps/branches share a workflow frame!
	wfVars := collectWorkflowVars(wf)
	sharedParams := append([]string{}, pnames...)
	seenP := map[string]bool{}
	for _, p := range sharedParams {
		seenP[p] = true
	}
	for _, v := range wfVars {
		if !seenP[v] {
			seenP[v] = true
			sharedParams = append(sharedParams, v)
		}
	}

	// Compile workflow-scoped helper that takes & returns updated workflow env map, or runs with workflow env slots!
	// Even cleaner: each synth func takes a single `env` map? Wait: no! Using `sharedParams` where VM preserves workflow frame locals by name across steps makes `ok = lock_funds(...)` and `r1 = req.get(...)` and `return aggregate_quotes(...)` work with ZERO friction!
	for _, n := range wf.Nodes {
		switch node := n.(type) {
		case *ast.StartNode:
			wfc.StartTarget = node.Target
			if len(node.Body) > 0 {
				fn := fmt.Sprintf("__wf_%s_start", wf.Name)
				if err := c.compileSynthFunc(fn, sharedParams, node.Body, nil, node.Span.Line); err != nil {
					return err
				}
				wfc.StartFn = fn
			}
		case *ast.StepNode:
			fn := ""
			if len(node.Body) > 0 {
				fn = fmt.Sprintf("__wf_%s_step_%s", wf.Name, node.Name)
				if err := c.compileSynthFunc(fn, sharedParams, node.Body, nil, node.Span.Line); err != nil {
					return err
				}
			}
			wfc.Steps[node.Name] = WorkflowStepMeta{
				Name: node.Name, After: node.After, Target: node.Target, FnName: fn,
			}
		case *ast.ChoiceNode:
			cm := WorkflowChoiceMeta{After: node.After}
			for i, br := range node.Branches {
				gfn := ""
				if !br.IsElse && br.Guard != nil {
					gfn = fmt.Sprintf("__wf_%s_choice_%s_%d", wf.Name, node.After, i)
					if err := c.compileSynthFunc(gfn, sharedParams, nil, br.Guard, br.Span.Line); err != nil {
						return err
					}
				}
				cm.Branches = append(cm.Branches, WorkflowChoiceBranchMeta{
					GuardFn: gfn, IsElse: br.IsElse, Target: br.Target,
				})
			}
			key := node.After
			if key == "" {
				key = node.Name
			}
			wfc.Choices[key] = cm
		case *ast.ForkNode:
			fm := WorkflowForkMeta{Name: node.Name, After: node.After}
			for _, br := range node.Branches {
				bm := WorkflowBranchMeta{Name: br.Name}
				for idx, op := range br.Ops {
					bop := WorkflowBranchOpMeta{Kind: int(op.Kind), Target: op.Target}
					if op.Kind == ast.BranchStmt && op.Stmt != nil {
						fn := fmt.Sprintf("__wf_%s_fk_%s_%s_%d", wf.Name, node.Name, br.Name, idx)
						if err := c.compileSynthFunc(fn, sharedParams, []ast.Stmt{op.Stmt}, nil, op.Span.Line); err != nil {
							return err
						}
						bop.FnName = fn
					}
					bm.Ops = append(bm.Ops, bop)
				}
				fm.Branches = append(fm.Branches, bm)
			}
			wfc.Forks[node.Name] = fm
		case *ast.JoinNode:
			wfc.Joins[node.Name] = WorkflowJoinMeta{Name: node.Name, Target: node.Target}
		case *ast.MergeNode:
			wfc.Merges[node.Name] = WorkflowMergeMeta{Name: node.Name, Afters: node.Afters, Target: node.Target}
		}
	}

	c.wfCompiled[wf.Name] = wfc
	idx := len(c.mod.Workflows)
	c.mod.Workflows = append(c.mod.Workflows, WorkflowProto{
		Name:   wf.Name,
		Params: sharedParams,
		Pools:  wfc.Pools,
	})
	c.mod.WorkflowIdx[wf.Name] = idx
	return nil
}

func collectWorkflowVars(wf *ast.WorkflowDecl) []string {
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

// ---------------------------------------------------------------------------
// Function Bytecode Emitter
// ---------------------------------------------------------------------------

type fnCompiler struct {
	root   *compiler
	parent *fnCompiler
	proto  *FuncProto
	locals map[string]int
	upvals map[string]int
}

func newFnCompiler(root *compiler, name string, params []string, parent *fnCompiler) *fnCompiler {
	fc := &fnCompiler{
		root:   root,
		parent: parent,
		proto: &FuncProto{
			Name:   name,
			Params: params,
		},
		locals: map[string]int{},
		upvals: map[string]int{},
	}
	for _, p := range params {
		fc.declareLocal(p)
	}
	return fc
}

func (f *fnCompiler) declareLocal(name string) int {
	if slot, ok := f.locals[name]; ok {
		return slot
	}
	slot := f.proto.NumLocals
	f.proto.NumLocals++
	f.locals[name] = slot
	return slot
}

func (f *fnCompiler) resolveVar(name string) (isLocal bool, isUpval bool, slot int) {
	if s, ok := f.locals[name]; ok {
		return true, false, s
	}
	if s, ok := f.upvals[name]; ok {
		return false, true, s
	}
	if f.parent != nil {
		if pl, pu, _ := f.parent.resolveVar(name); pl || pu {
			idx := len(f.proto.UpvalNames)
			f.proto.UpvalNames = append(f.proto.UpvalNames, name)
			f.upvals[name] = idx
			return false, true, idx
		}
	}
	return false, false, -1
}

func (f *fnCompiler) emit(w uint32, line int) int {
	pc := len(f.proto.Code)
	f.proto.Code = append(f.proto.Code, w)
	f.proto.Lines = append(f.proto.Lines, line)
	return pc
}

func (f *fnCompiler) emitJump(op OpCode, line int) int {
	return f.emit(EncodeImm(op, 0), line)
}

func (f *fnCompiler) patchJump(pc int) {
	op, _, _, _ := DecodeInstr(f.proto.Code[pc])
	target := uint32(len(f.proto.Code))
	f.proto.Code[pc] = EncodeImm(op, target)
}

func (f *fnCompiler) finish() int {
	idx := len(f.root.mod.Funcs)
	f.root.mod.Funcs = append(f.root.mod.Funcs, f.proto)
	f.root.mod.FuncIndex[f.proto.Name] = idx
	return idx
}

func (f *fnCompiler) compileStmt(stmt ast.Stmt) error {
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		if err := f.compileExpr(s.Value); err != nil {
			return err
		}
		slot := f.declareLocal(s.Name)
		f.emit(EncodeImm(OpStoreLocal, uint32(slot)), s.Span.Line)

	case *ast.CompoundAssignStmt:
		opCode := OpAdd
		switch s.Op {
		case "-=":
			opCode = OpSub
		case "*=":
			opCode = OpMul
		}
		switch tgt := s.Target.(type) {
		case *ast.Ident:
			slot := f.declareLocal(tgt.Name)
			f.emit(EncodeImm(OpLoadLocal, uint32(slot)), s.Span.Line)
			if err := f.compileExpr(s.Value); err != nil {
				return err
			}
			f.emit(EncodeImm(opCode, 0), s.Span.Line)
			f.emit(EncodeImm(OpStoreLocal, uint32(slot)), s.Span.Line)
		case *ast.FieldExpr:
			if err := f.compileExpr(tgt.Object); err != nil {
				return err
			}
			f.emit(EncodeImm(OpDup, 0), s.Span.Line)
			f.emit(EncodeImm(OpGetField, f.root.addStrConst(tgt.Field)), s.Span.Line)
			if err := f.compileExpr(s.Value); err != nil {
				return err
			}
			f.emit(EncodeImm(opCode, 0), s.Span.Line)
			f.emit(EncodeImm(OpSetField, f.root.addStrConst(tgt.Field)), s.Span.Line)
		case *ast.IndexExpr:
			// list and index are evaluated once, the element is read, then
			// the right-hand side runs.
			line := s.Span.Line
			if err := f.compileExpr(tgt.List); err != nil {
				return err
			}
			listSlot := f.declareLocal(fmt.Sprintf("__cidx_list_%d", f.proto.NumLocals))
			f.emit(EncodeImm(OpStoreLocal, uint32(listSlot)), line)
			if err := f.compileExpr(tgt.Index); err != nil {
				return err
			}
			idxSlot := f.declareLocal(fmt.Sprintf("__cidx_idx_%d", f.proto.NumLocals))
			f.emit(EncodeImm(OpStoreLocal, uint32(idxSlot)), line)
			f.emit(EncodeImm(OpLoadLocal, uint32(listSlot)), line)
			f.emit(EncodeImm(OpLoadLocal, uint32(idxSlot)), line)
			f.emit(EncodeImm(OpLoadLocal, uint32(listSlot)), line)
			f.emit(EncodeImm(OpLoadLocal, uint32(idxSlot)), line)
			f.emit(EncodeImm(OpGetIndex, 0), line)
			if err := f.compileExpr(s.Value); err != nil {
				return err
			}
			f.emit(EncodeImm(opCode, 0), line)
			f.emit(EncodeImm(OpSetIndex, 0), line)
		}

	case *ast.FieldAssignStmt:
		if err := f.compileExpr(s.Object); err != nil {
			return err
		}
		if err := f.compileExpr(s.Value); err != nil {
			return err
		}
		f.emit(EncodeImm(OpSetField, f.root.addStrConst(s.Field)), s.Span.Line)

	case *ast.IndexAssignStmt:
		if err := f.compileExpr(s.List); err != nil {
			return err
		}
		if err := f.compileExpr(s.Index); err != nil {
			return err
		}
		if err := f.compileExpr(s.Value); err != nil {
			return err
		}
		f.emit(EncodeImm(OpSetIndex, 0), s.Span.Line)

	case *ast.IfStmt:
		var endJumps []int
		for _, br := range s.Branches {
			if err := f.compileExpr(br.Cond); err != nil {
				return err
			}
			jf := f.emitJump(OpJmpIfFalse, br.Span.Line)
			for _, st := range br.Body {
				if err := f.compileStmt(st); err != nil {
					return err
				}
			}
			endJumps = append(endJumps, f.emitJump(OpJmp, br.Span.Line))
			f.patchJump(jf)
		}
		for _, st := range s.Else {
			if err := f.compileStmt(st); err != nil {
				return err
			}
		}
		for _, ej := range endJumps {
			f.patchJump(ej)
		}

	case *ast.WhileStmt:
		loopStart := uint32(len(f.proto.Code))
		if err := f.compileExpr(s.Cond); err != nil {
			return err
		}
		exitJmp := f.emitJump(OpJmpIfFalse, s.Span.Line)
		for _, st := range s.Body {
			if err := f.compileStmt(st); err != nil {
				return err
			}
		}
		f.emit(EncodeImm(OpJmp, loopStart), s.Span.Line)
		f.patchJump(exitJmp)

	case *ast.ForStmt:
		if rng, ok := s.Iterable.(*ast.RangeExpr); ok {
			// Compile `for i in lo..hi:`
			if err := f.compileExpr(rng.Lo); err != nil {
				return err
			}
			slotI := f.declareLocal(s.Var)
			f.emit(EncodeImm(OpStoreLocal, uint32(slotI)), s.Span.Line)
			if err := f.compileExpr(rng.Hi); err != nil {
				return err
			}
			slotHi := f.declareLocal(fmt.Sprintf("__hi_%d", s.Span.Line))
			f.emit(EncodeImm(OpStoreLocal, uint32(slotHi)), s.Span.Line)

			loopTop := uint32(len(f.proto.Code))
			f.emit(EncodeImm(OpLoadLocal, uint32(slotI)), s.Span.Line)
			f.emit(EncodeImm(OpLoadLocal, uint32(slotHi)), s.Span.Line)
			f.emit(EncodeImm(OpLt, 0), s.Span.Line)
			exitJmp := f.emitJump(OpJmpIfFalse, s.Span.Line)
			for _, st := range s.Body {
				if err := f.compileStmt(st); err != nil {
					return err
				}
			}
			f.emit(EncodeImm(OpLoadLocal, uint32(slotI)), s.Span.Line)
			f.emit(EncodeImm(OpPushConst, f.root.addIntConst(1)), s.Span.Line)
			f.emit(EncodeImm(OpAdd, 0), s.Span.Line)
			f.emit(EncodeImm(OpStoreLocal, uint32(slotI)), s.Span.Line)
			f.emit(EncodeImm(OpJmp, loopTop), s.Span.Line)
			f.patchJump(exitJmp)
		} else {
			// Compile `for item in xs:`
			if err := f.compileExpr(s.Iterable); err != nil {
				return err
			}
			slotList := f.declareLocal(fmt.Sprintf("__list_%d", s.Span.Line))
			f.emit(EncodeImm(OpStoreLocal, uint32(slotList)), s.Span.Line)
			slotIdx := f.declareLocal(fmt.Sprintf("__idx_%d", s.Span.Line))
			f.emit(EncodeImm(OpPushConst, f.root.addIntConst(0)), s.Span.Line)
			f.emit(EncodeImm(OpStoreLocal, uint32(slotIdx)), s.Span.Line)

			loopTop := uint32(len(f.proto.Code))
			f.emit(EncodeImm(OpLoadLocal, uint32(slotIdx)), s.Span.Line)
			f.emit(EncodeImm(OpLoadLocal, uint32(slotList)), s.Span.Line)
			cmIdx := f.root.addCallMeta(CallMeta{CalleeName: "len", ArgCount: 1})
			f.emit(EncodeABC(OpCall, 1, cmIdx), s.Span.Line)
			f.emit(EncodeImm(OpLt, 0), s.Span.Line)
			exitJmp := f.emitJump(OpJmpIfFalse, s.Span.Line)

			f.emit(EncodeImm(OpLoadLocal, uint32(slotList)), s.Span.Line)
			f.emit(EncodeImm(OpLoadLocal, uint32(slotIdx)), s.Span.Line)
			f.emit(EncodeImm(OpGetIndex, 0), s.Span.Line)
			slotVar := f.declareLocal(s.Var)
			f.emit(EncodeImm(OpStoreLocal, uint32(slotVar)), s.Span.Line)

			for _, st := range s.Body {
				if err := f.compileStmt(st); err != nil {
					return err
				}
			}
			f.emit(EncodeImm(OpLoadLocal, uint32(slotIdx)), s.Span.Line)
			f.emit(EncodeImm(OpPushConst, f.root.addIntConst(1)), s.Span.Line)
			f.emit(EncodeImm(OpAdd, 0), s.Span.Line)
			f.emit(EncodeImm(OpStoreLocal, uint32(slotIdx)), s.Span.Line)
			f.emit(EncodeImm(OpJmp, loopTop), s.Span.Line)
			f.patchJump(exitJmp)
		}

	case *ast.MatchStmt:
		if err := f.compileExpr(s.Subject); err != nil {
			return err
		}
		subjSlot := f.declareLocal(fmt.Sprintf("__subj_%d", s.Span.Line))
		f.emit(EncodeImm(OpStoreLocal, uint32(subjSlot)), s.Span.Line)
		var endJumps []int
		for _, arm := range s.Arms {
			if err := f.compilePatternCheck(arm.Pattern, subjSlot, arm.Span.Line); err != nil {
				return err
			}
			if arm.Guard != nil {
				jfPat := f.emitJump(OpJmpIfFalse, arm.Span.Line)
				if err := f.compileExpr(arm.Guard); err != nil {
					return err
				}
				jfGuard := f.emitJump(OpJmpIfFalse, arm.Span.Line)
				for _, st := range arm.Body {
					if err := f.compileStmt(st); err != nil {
						return err
					}
				}
				endJumps = append(endJumps, f.emitJump(OpJmp, arm.Span.Line))
				f.patchJump(jfPat)
				f.patchJump(jfGuard)
			} else {
				jf := f.emitJump(OpJmpIfFalse, arm.Span.Line)
				for _, st := range arm.Body {
					if err := f.compileStmt(st); err != nil {
						return err
					}
				}
				endJumps = append(endJumps, f.emitJump(OpJmp, arm.Span.Line))
				f.patchJump(jf)
			}
		}
		for _, ej := range endJumps {
			f.patchJump(ej)
		}

	case *ast.ReturnStmt:
		if s.Value != nil {
			if err := f.compileExpr(s.Value); err != nil {
				return err
			}
			f.emit(EncodeABC(OpRet, 1, 0), s.Span.Line)
		} else {
			f.emit(EncodeABC(OpRet, 0, 0), s.Span.Line)
		}

	case *ast.ExprStmt:
		if err := f.compileExpr(s.Expr); err != nil {
			return err
		}
		// Only pop if expression leaves a value (all expressions push 1 value!)
		f.emit(EncodeImm(OpPop, 0), s.Span.Line)
	}
	return nil
}

func (f *fnCompiler) compilePatternCheck(pat ast.Pattern, subjSlot int, line int) error {
	switch p := pat.(type) {
	case *ast.WildcardPat:
		f.emit(EncodeABC(OpPushBool, 1, 0), line)
	case *ast.VarPat:
		f.emit(EncodeImm(OpLoadLocal, uint32(subjSlot)), line)
		slot := f.declareLocal(p.Name)
		f.emit(EncodeImm(OpStoreLocal, uint32(slot)), line)
		f.emit(EncodeABC(OpPushBool, 1, 0), line)
	case *ast.IntPat:
		f.emit(EncodeImm(OpLoadLocal, uint32(subjSlot)), line)
		f.emit(EncodeImm(OpPushConst, f.root.addIntConst(p.Value)), line)
		f.emit(EncodeImm(OpEq, 0), line)
	case *ast.BoolPat:
		f.emit(EncodeImm(OpLoadLocal, uint32(subjSlot)), line)
		b := uint8(0)
		if p.Value {
			b = 1
		}
		f.emit(EncodeABC(OpPushBool, b, 0), line)
		f.emit(EncodeImm(OpEq, 0), line)
	case *ast.StrPat:
		f.emit(EncodeImm(OpLoadLocal, uint32(subjSlot)), line)
		f.emit(EncodeImm(OpPushConst, f.root.addStrConst(p.Value)), line)
		f.emit(EncodeImm(OpEq, 0), line)
	case *ast.RangePat:
		f.emit(EncodeImm(OpLoadLocal, uint32(subjSlot)), line)
		f.emit(EncodeImm(OpPushConst, f.root.addIntConst(p.Lo)), line)
		f.emit(EncodeImm(OpGe, 0), line)
		jf := f.emitJump(OpJmpIfFalse, line)
		f.emit(EncodeImm(OpLoadLocal, uint32(subjSlot)), line)
		f.emit(EncodeImm(OpPushConst, f.root.addIntConst(p.Hi)), line)
		f.emit(EncodeImm(OpLe, 0), line)
		endJ := f.emitJump(OpJmp, line)
		f.patchJump(jf)
		f.emit(EncodeABC(OpPushBool, 0, 0), line)
		f.patchJump(endJ)
	case *ast.VariantPat:
		f.emit(EncodeImm(OpLoadLocal, uint32(subjSlot)), line)
		f.emit(EncodeImm(OpCheckVariant, f.root.addStrConst(p.Name)), line)
		if len(p.Fields) > 0 {
			jf := f.emitJump(OpJmpIfFalse, line)
			for i, sub := range p.Fields {
				f.emit(EncodeImm(OpLoadLocal, uint32(subjSlot)), line)
				f.emit(EncodeImm(OpExtractField, uint32(i)), line)
				subSlot := f.declareLocal(fmt.Sprintf("__pat_%d_%d", line, i))
				f.emit(EncodeImm(OpStoreLocal, uint32(subSlot)), line)
				if err := f.compilePatternCheck(sub, subSlot, line); err != nil {
					return err
				}
				f.emit(EncodeImm(OpPop, 0), line)
			}
			f.emit(EncodeABC(OpPushBool, 1, 0), line)
			endJ := f.emitJump(OpJmp, line)
			f.patchJump(jf)
			f.emit(EncodeABC(OpPushBool, 0, 0), line)
			f.patchJump(endJ)
		}
	}
	return nil
}

func (f *fnCompiler) compileExpr(expr ast.Expr) error {
	switch e := expr.(type) {
	case *ast.IntLit:
		f.emit(EncodeImm(OpPushConst, f.root.addIntConst(e.Value)), e.Span.Line)
	case *ast.BoolLit:
		b := uint8(0)
		if e.Value {
			b = 1
		}
		f.emit(EncodeABC(OpPushBool, b, 0), e.Span.Line)
	case *ast.StrLit:
		f.emit(EncodeImm(OpPushConst, f.root.addStrConst(e.Value)), e.Span.Line)
	case *ast.NoneLit:
		f.emit(EncodeImm(OpPushNone, 0), e.Span.Line)
	case *ast.FStrExpr:
		for _, part := range e.Parts {
			if !part.IsExpr {
				f.emit(EncodeImm(OpPushConst, f.root.addStrConst(part.Text)), e.Span.Line)
			} else {
				if err := f.compileExpr(part.Expr); err != nil {
					return err
				}
			}
		}
		f.emit(EncodeImm(OpFmtStr, uint32(len(e.Parts))), e.Span.Line)
	case *ast.Ident:
		isL, isU, slot := f.resolveVar(e.Name)
		if isL {
			f.emit(EncodeImm(OpLoadLocal, uint32(slot)), e.Span.Line)
		} else if isU {
			f.emit(EncodeImm(OpLoadUpval, uint32(slot)), e.Span.Line)
		} else if _, isVar := f.root.info.Variants[e.Name]; isVar {
			// Bare 0-arg ADT variant like Degraded or None
			f.emit(EncodeABC(OpMakeVariant, 0, uint16(f.root.addStrConst(e.Name))), e.Span.Line)
		} else {
			// Module, Port, or Function reference pushed as string symbol
			f.emit(EncodeImm(OpPushConst, f.root.addStrConst("__sym:"+e.Name)), e.Span.Line)
		}
	case *ast.UnaryExpr:
		if err := f.compileExpr(e.Expr); err != nil {
			return err
		}
		if e.Op == "-" {
			f.emit(EncodeImm(OpNeg, 0), e.Span.Line)
		} else if e.Op == "not" {
			f.emit(EncodeImm(OpNot, 0), e.Span.Line)
		}
	case *ast.BinaryExpr:
		if e.Op == "and" {
			if err := f.compileExpr(e.Left); err != nil {
				return err
			}
			jf := f.emitJump(OpJmpIfFalsePeek, e.Span.Line)
			f.emit(EncodeImm(OpPop, 0), e.Span.Line)
			if err := f.compileExpr(e.Right); err != nil {
				return err
			}
			f.patchJump(jf)
			return nil
		}
		if e.Op == "or" {
			if err := f.compileExpr(e.Left); err != nil {
				return err
			}
			jt := f.emitJump(OpJmpIfTruePeek, e.Span.Line)
			f.emit(EncodeImm(OpPop, 0), e.Span.Line)
			if err := f.compileExpr(e.Right); err != nil {
				return err
			}
			f.patchJump(jt)
			return nil
		}
		if e.Op == "implies" {
			if err := f.compileExpr(e.Left); err != nil {
				return err
			}
			f.emit(EncodeImm(OpNot, 0), e.Span.Line)
			jt := f.emitJump(OpJmpIfTruePeek, e.Span.Line)
			f.emit(EncodeImm(OpPop, 0), e.Span.Line)
			if err := f.compileExpr(e.Right); err != nil {
				return err
			}
			f.patchJump(jt)
			return nil
		}
		if err := f.compileExpr(e.Left); err != nil {
			return err
		}
		if err := f.compileExpr(e.Right); err != nil {
			return err
		}
		switch e.Op {
		case "+":
			f.emit(EncodeImm(OpAdd, 0), e.Span.Line)
		case "-":
			f.emit(EncodeImm(OpSub, 0), e.Span.Line)
		case "*":
			f.emit(EncodeImm(OpMul, 0), e.Span.Line)
		case "/":
			f.emit(EncodeImm(OpDiv, 0), e.Span.Line)
		case "%":
			f.emit(EncodeImm(OpMod, 0), e.Span.Line)
		case "==":
			f.emit(EncodeImm(OpEq, 0), e.Span.Line)
		case "!=":
			f.emit(EncodeImm(OpNeq, 0), e.Span.Line)
		case "<":
			f.emit(EncodeImm(OpLt, 0), e.Span.Line)
		case "<=":
			f.emit(EncodeImm(OpLe, 0), e.Span.Line)
		case ">":
			f.emit(EncodeImm(OpGt, 0), e.Span.Line)
		case ">=":
			f.emit(EncodeImm(OpGe, 0), e.Span.Line)
		}
	case *ast.ListLit:
		for _, el := range e.Elems {
			if err := f.compileExpr(el); err != nil {
				return err
			}
		}
		f.emit(EncodeImm(OpMakeList, uint32(len(e.Elems))), e.Span.Line)
	case *ast.MapLit:
		for _, ent := range e.Entries {
			if err := f.compileExpr(ent.Key); err != nil {
				return err
			}
			if err := f.compileExpr(ent.Value); err != nil {
				return err
			}
		}
		f.emit(EncodeImm(OpMakeMap, uint32(len(e.Entries))), e.Span.Line)
	case *ast.FieldExpr:
		if err := f.compileExpr(e.Object); err != nil {
			return err
		}
		f.emit(EncodeImm(OpGetField, f.root.addStrConst(e.Field)), e.Span.Line)
	case *ast.IndexExpr:
		if err := f.compileExpr(e.List); err != nil {
			return err
		}
		if err := f.compileExpr(e.Index); err != nil {
			return err
		}
		f.emit(EncodeImm(OpGetIndex, 0), e.Span.Line)
	case *ast.WithExpr:
		if err := f.compileExpr(e.Base); err != nil {
			return err
		}
		var names []string
		for _, fld := range e.Fields {
			names = append(names, fld.Name)
			if err := f.compileExpr(fld.Value); err != nil {
				return err
			}
		}
		fmIdx := f.root.addFieldMeta(names)
		f.emit(EncodeABC(OpWithUpdate, uint8(len(names)), fmIdx), e.Span.Line)
	case *ast.TryExpr:
		if err := f.compileExpr(e.Inner); err != nil {
			return err
		}
		f.emit(EncodeImm(OpTryUnwrap, 0), e.Span.Line)
	case *ast.MatchExpr:
		if err := f.compileExpr(e.Subject); err != nil {
			return err
		}
		subjSlot := f.declareLocal(fmt.Sprintf("__mexpr_%d", e.Span.Line))
		f.emit(EncodeImm(OpStoreLocal, uint32(subjSlot)), e.Span.Line)
		var endJumps []int
		for _, arm := range e.Arms {
			if err := f.compilePatternCheck(arm.Pattern, subjSlot, arm.Span.Line); err != nil {
				return err
			}
			jf := f.emitJump(OpJmpIfFalse, arm.Span.Line)
			if arm.Guard != nil {
				if err := f.compileExpr(arm.Guard); err != nil {
					return err
				}
				jf2 := f.emitJump(OpJmpIfFalse, arm.Span.Line)
				if err := f.compileExpr(arm.Value); err != nil {
					return err
				}
				endJumps = append(endJumps, f.emitJump(OpJmp, arm.Span.Line))
				f.patchJump(jf2)
				f.patchJump(jf)
			} else {
				if err := f.compileExpr(arm.Value); err != nil {
					return err
				}
				endJumps = append(endJumps, f.emitJump(OpJmp, arm.Span.Line))
				f.patchJump(jf)
			}
		}
		f.emit(EncodeImm(OpPushNone, 0), e.Span.Line)
		for _, ej := range endJumps {
			f.patchJump(ej)
		}
	case *ast.LambdaExpr:
		f.root.lambdaSeq++
		lname := fmt.Sprintf("__lambda_%d", f.root.lambdaSeq)
		lfc := newFnCompiler(f.root, lname, e.Params, f)
		if err := lfc.compileExpr(e.Body); err != nil {
			return err
		}
		lfc.emit(EncodeABC(OpRet, 1, 0), e.Span.Line)
		fnIdx := lfc.finish()
		for _, up := range lfc.proto.UpvalNames {
			isL, isU, slot := f.resolveVar(up)
			if isL {
				f.emit(EncodeImm(OpLoadLocal, uint32(slot)), e.Span.Line)
			} else if isU {
				f.emit(EncodeImm(OpLoadUpval, uint32(slot)), e.Span.Line)
			} else {
				f.emit(EncodeImm(OpPushNone, 0), e.Span.Line)
			}
		}
		f.emit(EncodeABC(OpMakeClosure, uint8(fnIdx), uint16(len(lfc.proto.UpvalNames))), e.Span.Line)
	case *ast.PipeExpr:
		// Transform `lhs |> rhs(args...)` -> `rhs(lhs, args...)`
		if ce, ok := e.Right.(*ast.CallExpr); ok {
			newArgs := append([]ast.CallArg{{Span: e.Span, Value: e.Left}}, ce.Args...)
			desugared := &ast.CallExpr{
				Span:     e.Span,
				Callee:   ce.Callee,
				TypeArgs: ce.TypeArgs,
				Args:     newArgs,
			}
			return f.compileExpr(desugared)
		}
		if id, ok := e.Right.(*ast.Ident); ok {
			desugared := &ast.CallExpr{
				Span:   e.Span,
				Callee: id,
				Args:   []ast.CallArg{{Span: e.Span, Value: e.Left}},
			}
			return f.compileExpr(desugared)
		}
		return f.compileExpr(e.Right)
	case *ast.RunWorkflowExpr:
		for _, a := range e.Args {
			if err := f.compileExpr(a.Value); err != nil {
				return err
			}
		}
		wfIdx := f.root.mod.WorkflowIdx[e.Name]
		f.emit(EncodeABC(OpRunWorkflow, uint8(len(e.Args)), uint16(wfIdx)), e.Span.Line)
	case *ast.CallExpr:
		return f.compileCallExpr(e)
	}
	return nil
}

func (f *fnCompiler) compileCallExpr(e *ast.CallExpr) error {
	// 1. Check if Entity constructor
	if id, ok := e.Callee.(*ast.Ident); ok {
		if entIdx, isEnt := f.root.mod.EntityIndex[id.Name]; isEnt {
			var names []string
			et := f.root.info.Entities[id.Name]
			for i, a := range e.Args {
				if err := f.compileExpr(a.Value); err != nil {
					return err
				}
				name := a.Name
				if name == "" && et != nil && i < len(et.Fields) {
					name = et.Fields[i].Name
				}
				names = append(names, name)
			}
			fmIdx := f.root.addFieldMeta(names)
			f.emit(EncodeABC(OpMakeEntity, uint8(entIdx), fmIdx), e.Span.Line)
			return nil
		}
		// 2. Check if ADT Variant constructor
		if _, isVar := f.root.info.Variants[id.Name]; isVar {
			for _, a := range e.Args {
				if err := f.compileExpr(a.Value); err != nil {
					return err
				}
			}
			cIdx := f.root.addStrConst(id.Name)
			f.emit(EncodeABC(OpMakeVariant, uint8(len(e.Args)), uint16(cIdx)), e.Span.Line)
			return nil
		}
	}

	// 3. Method call: receiver.method(args...)
	if fe, ok := e.Callee.(*ast.FieldExpr); ok {
		// Check if receiver is an imported module alias (e.g., sock.listen_tcp) or Port (AuditLog.write_entry)
		if objID, ok := fe.Object.(*ast.Ident); ok {
			if modPath, isImp := f.root.info.Imports[objID.Name]; isImp {
				return f.emitNamedCall(modPath+"."+fe.Field, e.Args, e.TypeArgs, false, e.Span.Line)
			}
			if _, isPort := f.root.info.Ports[objID.Name]; isPort {
				return f.emitNamedCall("port:"+objID.Name+"."+fe.Field, e.Args, e.TypeArgs, false, e.Span.Line)
			}
		}
		// Instance method call on handle/value: push receiver first, then args!
		if err := f.compileExpr(fe.Object); err != nil {
			return err
		}
		var kwNames []string
		for _, a := range e.Args {
			if err := f.compileExpr(a.Value); err != nil {
				return err
			}
			kwNames = append(kwNames, a.Name)
		}
		var targs []string
		for _, ta := range e.TypeArgs {
			targs = append(targs, ta.String())
		}
		cmIdx := f.root.addCallMeta(CallMeta{
			CalleeName: fe.Field,
			ArgCount:   len(e.Args) + 1,
			KwNames:    append([]string{""}, kwNames...),
			TypeArgs:   targs,
			IsMethod:   true,
		})
		f.emit(EncodeABC(OpCall, uint8(len(e.Args)+1), cmIdx), e.Span.Line)
		return nil
	}

	// 4. Direct named function call OR dynamic closure variable call
	if id, ok := e.Callee.(*ast.Ident); ok {
		isL, isU, _ := f.resolveVar(id.Name)
		if isL || isU {
			if err := f.compileExpr(id); err != nil {
				return err
			}
			for _, a := range e.Args {
				if err := f.compileExpr(a.Value); err != nil {
					return err
				}
			}
			f.emit(EncodeABC(OpCallDyn, uint8(len(e.Args)), 0), e.Span.Line)
			return nil
		}
		return f.emitNamedCall(id.Name, e.Args, e.TypeArgs, false, e.Span.Line)
	}

	// General dynamic callable
	if err := f.compileExpr(e.Callee); err != nil {
		return err
	}
	for _, a := range e.Args {
		if err := f.compileExpr(a.Value); err != nil {
			return err
		}
	}
	f.emit(EncodeABC(OpCallDyn, uint8(len(e.Args)), 0), e.Span.Line)
	return nil
}

func (f *fnCompiler) emitNamedCall(name string, args []ast.CallArg, typeArgs []ast.TypeExpr, isMethod bool, line int) error {
	var kwNames []string
	// Normalize keyword args for known user functions if needed
	if fi, ok := f.root.info.Funcs[name]; ok && len(args) == len(fi.Type.Params) {
		ordered := make([]ast.CallArg, len(args))
		hasKw := false
		for _, a := range args {
			if a.Name != "" {
				hasKw = true
				break
			}
		}
		if hasKw {
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
	for _, a := range args {
		if err := f.compileExpr(a.Value); err != nil {
			return err
		}
		kwNames = append(kwNames, a.Name)
	}
	var targs []string
	for _, ta := range typeArgs {
		targs = append(targs, strings.TrimSpace(ta.String()))
	}
	cmIdx := f.root.addCallMeta(CallMeta{
		CalleeName: name,
		ArgCount:   len(args),
		KwNames:    kwNames,
		TypeArgs:   targs,
		IsMethod:   isMethod,
	})
	f.emit(EncodeABC(OpCall, uint8(len(args)), cmIdx), line)
	return nil
}
