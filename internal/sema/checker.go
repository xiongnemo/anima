package sema

import (
	"fmt"
	"math"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
)

// Check performs static type checking, alias/mut exclusivity analysis,
// port/timeout contract enforcement, and frame condition inference.
func Check(prog *ast.Program) (*ProgramInfo, error) {
	c := &checker{
		info: &ProgramInfo{
			Program:        prog,
			Types:          map[string]Type{},
			Entities:       map[string]*EntityType{},
			ADTs:           map[string]*ADTType{},
			Variants:       map[string]*ADTType{},
			Ports:          map[string]*PortType{},
			Machines:       map[string]*ast.MachineDecl{},
			Properties:     map[string]*ast.PropertyDecl{},
			Progresses:     map[string]*ast.ProgressDecl{},
			Workflows:      map[string]*WorkflowInfo{},
			Systems:        map[string]*ast.SystemDecl{},
			Funcs:          map[string]*FuncInfo{},
			ExprTypes:      map[ast.Expr]Type{},
			LiteralTargets: map[ast.Expr]Type{},
			TimeoutArgs:    map[*ast.CallExpr]ast.Expr{},
			Imports:        map[string]string{},
			StdHandles:     defaultStdHandles(),
		},
	}
	c.registerBuiltins()
	if err := c.checkProgram(); err != nil {
		return c.info, err
	}
	return c.info, nil
}

type checker struct {
	info        *ProgramInfo
	curReturn   Type
	curFuncInfo *FuncInfo
}

type scope struct {
	parent *scope
	vars   map[string]varBinding
}

type varBinding struct {
	ty      Type
	mutable bool
	isParam bool
	span    ast.Span
}

func newScope(parent *scope) *scope {
	return &scope{parent: parent, vars: map[string]varBinding{}}
}

func (s *scope) lookup(name string) (varBinding, bool) {
	for cur := s; cur != nil; cur = cur.parent {
		if b, ok := cur.vars[name]; ok {
			return b, true
		}
	}
	return varBinding{}, false
}

func (s *scope) set(name string, b varBinding) {
	// If already exists in current or parent function scope, update in place if same scope
	for cur := s; cur != nil; cur = cur.parent {
		if _, ok := cur.vars[name]; ok {
			cur.vars[name] = b
			return
		}
	}
	s.vars[name] = b
}

func (s *scope) defineLocal(name string, b varBinding) {
	s.vars[name] = b
}

func defaultStdHandles() map[string]*TypestateSpec {
	return map[string]*TypestateSpec{
		"sock.TcpListener": {
			InitState:    "Listening",
			AcceptStates: []string{"Closed"},
			Transitions: map[string]map[string]string{
				"Listening": {
					"accept": "Listening",
					"port":   "Listening",
					"close":  "Closed",
				},
			},
		},
		"sock.TcpStream": {
			InitState:    "Open",
			AcceptStates: []string{"Closed"},
			Transitions: map[string]map[string]string{
				"Open": {
					"send_text":  "Open",
					"recv_text":  "Open",
					"send_bytes": "Open",
					"recv_bytes": "Open",
					"close":      "Closed",
				},
			},
		},
		"fs.File": {
			InitState:    "Open",
			AcceptStates: []string{"Closed"},
			Transitions: map[string]map[string]string{
				"Open": {
					"read_text":  "Open",
					"write_text": "Open",
					"close":      "Closed",
				},
			},
		},
		"conc.ThreadPool": {
			InitState:    "Running",
			AcceptStates: []string{"Shutdown"},
			Transitions: map[string]map[string]string{
				"Running": {
					"submit":       "Running",
					"map_parallel": "Running",
					"shutdown":     "Shutdown",
				},
			},
		},
		"conc.Channel": {
			InitState:    "Open",
			AcceptStates: []string{"Closed", "Open"},
			Transitions: map[string]map[string]string{
				"Open": {
					"send":  "Open",
					"recv":  "Open",
					"close": "Closed",
				},
			},
		},
		"req.Session": {
			InitState:    "Open",
			AcceptStates: []string{"Closed", "Open"},
			Transitions: map[string]map[string]string{
				"Open": {
					"get":       "Open",
					"post":      "Open",
					"get_async": "Open",
					"close":     "Closed",
				},
			},
		},
	}
}

func (c *checker) registerBuiltins() {
	c.info.Types["int"] = NewUnboundedInt()
	c.info.Types["bool"] = BoolType{}
	c.info.Types["byte"] = NewIntRange(0, 255, "byte")
	c.info.Types["str"] = StrType{}
	c.info.Types["void"] = VoidType{}

	// Built-in Result[T, E] & Option[T] ADTs
	resADT := &ADTType{
		Name:       "Result",
		TypeParams: []string{"T", "E"},
		Variants: []VariantInfo{
			{Name: "Ok", Fields: []EntityFieldInfo{{Name: "val", Type: TypeVar{Name: "T"}}}},
			{Name: "Err", Fields: []EntityFieldInfo{{Name: "err", Type: TypeVar{Name: "E"}}}},
		},
		VariantMap: map[string]VariantInfo{},
	}
	for _, v := range resADT.Variants {
		resADT.VariantMap[v.Name] = v
		c.info.Variants[v.Name] = resADT
	}
	c.info.ADTs["Result"] = resADT
	c.info.Types["Result"] = resADT

	optADT := &ADTType{
		Name:       "Option",
		TypeParams: []string{"T"},
		Variants: []VariantInfo{
			{Name: "Some", Fields: []EntityFieldInfo{{Name: "val", Type: TypeVar{Name: "T"}}}},
			{Name: "None", Fields: nil},
		},
		VariantMap: map[string]VariantInfo{},
	}
	for _, v := range optADT.Variants {
		optADT.VariantMap[v.Name] = v
		c.info.Variants[v.Name] = optADT
	}
	c.info.ADTs["Option"] = optADT
	c.info.Types["Option"] = optADT

	// Built-in HttpResponse & IoErr entities/aliases
	httpResp := &EntityType{
		Name: "HttpResponse",
		Fields: []EntityFieldInfo{
			{Name: "status", Type: NewIntRange(100, 599, "")},
			{Name: "body", Type: StrType{}},
			{Name: "ok", Type: BoolType{}},
		},
		FieldMap: map[string]Type{
			"status": NewIntRange(100, 599, ""),
			"body":   StrType{},
			"ok":     BoolType{},
		},
	}
	c.info.Entities["HttpResponse"] = httpResp
	c.info.Types["HttpResponse"] = httpResp
	c.info.Types["IoErr"] = StrType{}
	c.info.Types["sock.IoErr"] = StrType{}
	c.info.Types["req.HttpResponse"] = httpResp
	c.info.Types["http.HttpResponse"] = httpResp
	c.info.Types["sock.TcpListener"] = &HandleType{Name: "sock.TcpListener", Protocol: c.info.StdHandles["sock.TcpListener"]}
	c.info.Types["sock.TcpStream"] = &HandleType{Name: "sock.TcpStream", Protocol: c.info.StdHandles["sock.TcpStream"]}
	c.info.Types["fs.File"] = &HandleType{Name: "fs.File", Protocol: c.info.StdHandles["fs.File"]}
	c.info.Types["bytes.ByteView"] = &HandleType{Name: "bytes.ByteView"}
}

func (c *checker) checkProgram() error {
	prog := c.info.Program

	// Pass 1: Register imports and top-level names
	for _, d := range prog.Decls {
		switch node := d.(type) {
		case *ast.ImportDecl:
			if err := c.registerImport(node); err != nil {
				return err
			}
		case *ast.TypeDecl:
			if node.Kind == ast.TypeADT {
				adt := &ADTType{
					Name:       node.Name,
					TypeParams: node.TypeParams,
					VariantMap: map[string]VariantInfo{},
					Decl:       node,
				}
				c.info.ADTs[node.Name] = adt
				c.info.Types[node.Name] = adt
			} else {
				c.info.Types[node.Name] = UnknownType{}
			}
		case *ast.EntityDecl:
			et := &EntityType{
				Name:       node.Name,
				FieldMap:   map[string]Type{},
				Relations:  node.Relations,
				Invariants: node.Invariants,
				Decl:       node,
			}
			c.info.Entities[node.Name] = et
			c.info.Types[node.Name] = et
		case *ast.PortDecl:
			pt := &PortType{Name: node.Name, Decl: node}
			c.info.Ports[node.Name] = pt
			c.info.Types[node.Name] = pt
		case *ast.MachineDecl:
			c.info.Machines[node.Name] = node
		case *ast.PropertyDecl:
			c.info.Properties[node.Name] = node
		case *ast.ProgressDecl:
			c.info.Progresses[node.Name] = node
		case *ast.WorkflowDecl:
			c.info.Workflows[node.Name] = &WorkflowInfo{Decl: node}
		case *ast.SystemDecl:
			c.info.Systems[node.Name] = node
		}
	}

	// Pass 2: Resolve TypeDecls, Entity fields, Port externs, Function sigs, Workflow sigs
	for _, d := range prog.Decls {
		switch node := d.(type) {
		case *ast.TypeDecl:
			if node.Kind == ast.TypeAlias {
				ty, err := c.resolveTypeExpr(node.Alias)
				if err != nil {
					return err
				}
				if it, ok := ty.(*IntType); ok {
					cp := *it
					cp.AliasName = node.Name
					ty = &cp
				}
				c.info.Types[node.Name] = ty
			} else {
				adt := c.info.ADTs[node.Name]
				for _, v := range node.Variants {
					vi := VariantInfo{Name: v.Name}
					for _, f := range v.Fields {
						ft, err := c.resolveTypeExpr(f.Type)
						if err != nil {
							return err
						}
						vi.Fields = append(vi.Fields, EntityFieldInfo{Name: f.Name, Type: ft})
					}
					adt.Variants = append(adt.Variants, vi)
					adt.VariantMap[v.Name] = vi
					c.info.Variants[v.Name] = adt
				}
			}
		case *ast.EntityDecl:
			et := c.info.Entities[node.Name]
			for _, f := range node.Fields {
				ft, err := c.resolveTypeExpr(f.Type)
				if err != nil {
					return err
				}
				et.Fields = append(et.Fields, EntityFieldInfo{Name: f.Name, Type: ft})
				et.FieldMap[f.Name] = ft
			}
			for _, rel := range node.Relations {
				if _, ok := c.info.Entities[rel.Target]; !ok {
					return fmt.Errorf("%s: relation %s targets unknown entity %q", rel.Span, rel.Name, rel.Target)
				}
			}
		case *ast.FuncDecl:
			var params []FuncParamInfo
			for _, p := range node.Params {
				pt, err := c.resolveTypeExpr(p.Type)
				if err != nil {
					return err
				}
				if p.Own {
					if h, wrapped := LinearHandle(pt); h == nil || wrapped {
						return fmt.Errorf("%s: 'own' parameter %s must be a linear handle (sock.TcpStream, sock.TcpListener, fs.File), got %s", p.Span, p.Name, pt)
					}
				}
				params = append(params, FuncParamInfo{Name: p.Name, Mut: p.Mut, Own: p.Own, Type: pt})
			}
			var ret Type = VoidType{}
			if node.ReturnType != nil {
				var err error
				ret, err = c.resolveTypeExpr(node.ReturnType)
				if err != nil {
					return err
				}
			}
			c.info.Funcs[node.Name] = &FuncInfo{
				Decl: node,
				Type: &FuncType{Params: params, Return: ret},
			}
		case *ast.WorkflowDecl:
			wf := c.info.Workflows[node.Name]
			for _, p := range node.Params {
				pt, err := c.resolveTypeExpr(p.Type)
				if err != nil {
					return err
				}
				if p.Own {
					return fmt.Errorf("%s: workflow parameter %s cannot be 'own'", p.Span, p.Name)
				}
				wf.Params = append(wf.Params, FuncParamInfo{Name: p.Name, Mut: p.Mut, Type: pt})
			}
			wf.Return = VoidType{}
			if node.ReturnType != nil {
				var err error
				wf.Return, err = c.resolveTypeExpr(node.ReturnType)
				if err != nil {
					return err
				}
			}
		}
	}

	// Pass 3: Type-check entities, functions, machines, workflows, systems
	for _, d := range prog.Decls {
		switch node := d.(type) {
		case *ast.EntityDecl:
			if err := c.checkEntity(node); err != nil {
				return err
			}
		case *ast.FuncDecl:
			if err := c.checkFunc(node); err != nil {
				return err
			}
		case *ast.MachineDecl:
			if err := c.checkMachine(node); err != nil {
				return err
			}
		case *ast.WorkflowDecl:
			if err := c.checkWorkflow(node); err != nil {
				return err
			}
		case *ast.SystemDecl:
			if err := c.checkSystem(node); err != nil {
				return err
			}
		}
	}
	return nil
}

func (c *checker) registerImport(imp *ast.ImportDecl) error {
	knownStd := map[string]bool{
		"std.fp":         true,
		"std.concurrent": true,
		"std.socket":     true,
		"std.requests":   true,
		"std.http":       true,
		"std.json":       true,
		"std.bytes":      true,
		"std.crypto":     true,
		"std.fs":         true,
		"std.cli":        true,
		"std.time":       true,
	}
	canonical := imp.Path
	if canonical == "std.http" {
		canonical = "std.requests"
	}
	if strings.HasPrefix(imp.Path, "std.") && !knownStd[imp.Path] {
		return fmt.Errorf("%s: unknown standard library module %q", imp.Span, imp.Path)
	}
	c.info.Imports[imp.Alias] = canonical
	// Bind alias-qualified types like sock.IoErr, sock.TcpStream, etc.
	if canonical == "std.socket" {
		c.info.Types[imp.Alias+".IoErr"] = StrType{}
		c.info.Types[imp.Alias+".TcpListener"] = c.info.Types["sock.TcpListener"]
		c.info.Types[imp.Alias+".TcpStream"] = c.info.Types["sock.TcpStream"]
	}
	if canonical == "std.requests" {
		c.info.Types[imp.Alias+".HttpResponse"] = c.info.Entities["HttpResponse"]
		c.info.Types[imp.Alias+".Session"] = &HandleType{Name: "req.Session", Protocol: c.info.StdHandles["req.Session"]}
	}
	if canonical == "std.fs" {
		c.info.Types[imp.Alias+".File"] = c.info.Types["fs.File"]
	}
	if canonical == "std.bytes" {
		c.info.Types[imp.Alias+".ByteView"] = c.info.Types["bytes.ByteView"]
	}
	return nil
}

func (c *checker) resolveTypeExpr(te ast.TypeExpr) (Type, error) {
	if te == nil {
		return VoidType{}, nil
	}
	switch t := te.(type) {
	case *ast.SimpleType:
		if ty, ok := c.info.Types[t.Name]; ok {
			return ty, nil
		}
		if strings.Contains(t.Name, ".") {
			parts := strings.SplitN(t.Name, ".", 2)
			if mod, ok := c.info.Imports[parts[0]]; ok {
				switch mod + "." + parts[1] {
				case "std.socket.IoErr":
					return StrType{}, nil
				case "std.socket.TcpListener":
					return c.info.Types["sock.TcpListener"], nil
				case "std.socket.TcpStream":
					return c.info.Types["sock.TcpStream"], nil
				case "std.requests.HttpResponse":
					return c.info.Entities["HttpResponse"], nil
				case "std.requests.Session":
					return &HandleType{Name: "req.Session", Protocol: c.info.StdHandles["req.Session"]}, nil
				case "std.fs.File":
					return c.info.Types["fs.File"], nil
				case "std.bytes.ByteView":
					return c.info.Types["bytes.ByteView"], nil
				case "std.concurrent.ThreadPool":
					return &HandleType{Name: "conc.ThreadPool", Protocol: c.info.StdHandles["conc.ThreadPool"]}, nil
				}
			}
		}
		return nil, fmt.Errorf("%s: unknown type %q", t.Span, t.Name)
	case *ast.IntRangeType:
		if t.Lo > t.Hi {
			return nil, fmt.Errorf("%s: invalid integer range [%d..%d]", t.Span, t.Lo, t.Hi)
		}
		return NewIntRange(t.Lo, t.Hi, ""), nil
	case *ast.GenericType:
		switch t.Name {
		case "list":
			if len(t.Args) != 1 {
				return nil, fmt.Errorf("%s: list requires 1 element type", t.Span)
			}
			elem, err := c.resolveTypeExpr(t.Args[0])
			if err != nil {
				return nil, err
			}
			return &ListType{Elem: elem, Cap: t.Cap, HasCap: t.HasCap}, nil
		case "map":
			if len(t.Args) != 2 {
				return nil, fmt.Errorf("%s: map requires key and value types", t.Span)
			}
			kt, err := c.resolveTypeExpr(t.Args[0])
			if err != nil {
				return nil, err
			}
			vt, err := c.resolveTypeExpr(t.Args[1])
			if err != nil {
				return nil, err
			}
			if !isMapKeyType(kt) {
				return nil, fmt.Errorf("%s: a map key must be str, int or bool, got %s", t.Span, kt)
			}
			return &MapType{Key: kt, Val: vt, Cap: t.Cap, HasCap: t.HasCap}, nil
		case "Channel", "conc.Channel":
			if len(t.Args) != 1 {
				return nil, fmt.Errorf("%s: Channel requires element type", t.Span)
			}
			elem, err := c.resolveTypeExpr(t.Args[0])
			if err != nil {
				return nil, err
			}
			return &HandleType{Name: "conc.Channel", Elem: elem, Cap: t.Cap, HasCap: t.HasCap, Protocol: c.info.StdHandles["conc.Channel"]}, nil
		case "Mutex", "conc.Mutex":
			if len(t.Args) != 1 {
				return nil, fmt.Errorf("%s: Mutex requires value type", t.Span)
			}
			elem, err := c.resolveTypeExpr(t.Args[0])
			if err != nil {
				return nil, err
			}
			return &HandleType{Name: "conc.Mutex", Elem: elem}, nil
		case "Future", "req.Future", "conc.Future":
			if len(t.Args) != 1 {
				return nil, fmt.Errorf("%s: Future requires result type", t.Span)
			}
			elem, err := c.resolveTypeExpr(t.Args[0])
			if err != nil {
				return nil, err
			}
			return &HandleType{Name: "Future", Elem: elem}, nil
		default:
			if adt, ok := c.info.ADTs[t.Name]; ok {
				var args []Type
				for _, a := range t.Args {
					ra, err := c.resolveTypeExpr(a)
					if err != nil {
						return nil, err
					}
					args = append(args, ra)
				}
				cp := *adt
				cp.TypeArgs = args
				return &cp, nil
			}
			return nil, fmt.Errorf("%s: unknown generic type %q", t.Span, t.Name)
		}
	case *ast.FuncType:
		var ps []FuncParamInfo
		for i, pt := range t.Params {
			rt, err := c.resolveTypeExpr(pt)
			if err != nil {
				return nil, err
			}
			ps = append(ps, FuncParamInfo{Name: fmt.Sprintf("p%d", i), Type: rt})
		}
		ret, err := c.resolveTypeExpr(t.ReturnType)
		if err != nil {
			return nil, err
		}
		return &FuncType{Params: ps, Return: ret}, nil
	}
	return nil, fmt.Errorf("%s: unsupported type expression", te.GetSpan())
}

func (c *checker) checkEntity(ent *ast.EntityDecl) error {
	et := c.info.Entities[ent.Name]
	sc := newScope(nil)
	for _, f := range et.Fields {
		sc.defineLocal(f.Name, varBinding{ty: f.Type, span: ent.Span})
	}
	for _, inv := range ent.Invariants {
		ty, err := c.checkExpr(inv, sc)
		if err != nil {
			return err
		}
		if ty.Kind() != KindBool && ty.Kind() != KindUnknown {
			return fmt.Errorf("%s: entity %s invariant must be bool, got %s", inv.GetSpan(), ent.Name, ty)
		}
	}
	return nil
}

func (c *checker) checkFunc(fn *ast.FuncDecl) error {
	fi := c.info.Funcs[fn.Name]
	sc := newScope(nil)
	for _, p := range fi.Type.Params {
		sc.defineLocal(p.Name, varBinding{ty: p.Type, mutable: p.Mut, isParam: true, span: fn.Span})
	}
	c.curReturn = fi.Type.Return
	c.curFuncInfo = fi
	defer func() {
		c.curReturn = nil
		c.curFuncInfo = nil
	}()

	for _, req := range fn.Requires {
		ty, err := c.checkExpr(req, sc)
		if err != nil {
			return err
		}
		if ty.Kind() != KindBool && ty.Kind() != KindUnknown {
			return fmt.Errorf("%s: requires clause must be bool, got %s", req.GetSpan(), ty)
		}
	}
	if fn.Decreases != nil {
		ty, err := c.checkExpr(fn.Decreases, sc)
		if err != nil {
			return err
		}
		if ty.Kind() != KindInt && ty.Kind() != KindUnknown {
			return fmt.Errorf("%s: decreases expression must be int, got %s", fn.Decreases.GetSpan(), ty)
		}
	}
	for _, st := range fn.Body {
		if err := c.checkStmt(st, sc); err != nil {
			return err
		}
	}
	// Check ensures with result & old()
	ensScope := newScope(sc)
	ensScope.defineLocal("result", varBinding{ty: fi.Type.Return, span: fn.Span})
	for _, ens := range fn.Ensures {
		ty, err := c.checkExpr(ens, ensScope)
		if err != nil {
			return err
		}
		if ty.Kind() != KindBool && ty.Kind() != KindUnknown {
			return fmt.Errorf("%s: ensures clause must be bool, got %s", ens.GetSpan(), ty)
		}
	}
	return nil
}

func (c *checker) checkMachine(m *ast.MachineDecl) error {
	sc := newScope(nil)
	for _, cv := range m.ControlVars {
		ty, err := c.resolveTypeExpr(cv.Type)
		if err != nil {
			return err
		}
		if cv.Init != nil {
			_, err := c.checkExpr(cv.Init, sc)
			if err != nil {
				return err
			}
		}
		sc.defineLocal(cv.Name, varBinding{ty: ty, mutable: true, span: cv.Span})
	}
	stateNames := map[string]bool{}
	for _, st := range m.States {
		stateNames[st.Name] = true
	}
	for _, st := range m.States {
		for _, inv := range st.Invariants {
			ty, err := c.checkExpr(inv, sc)
			if err != nil {
				return err
			}
			if ty.Kind() != KindBool && ty.Kind() != KindUnknown {
				return fmt.Errorf("%s: state %s invariant must be bool", inv.GetSpan(), st.Name)
			}
		}
		for _, tr := range st.Transitions {
			if tr.TargetState != "END" && tr.TargetState != "ERROR" && !stateNames[tr.TargetState] {
				return fmt.Errorf("%s: transition %s targets unknown state %q in %s", tr.Span, tr.Action, tr.TargetState, m.Name)
			}
			if tr.Guard != nil {
				gty, err := c.checkExpr(tr.Guard, sc)
				if err != nil {
					return err
				}
				if gty.Kind() != KindBool && gty.Kind() != KindUnknown {
					return fmt.Errorf("%s: transition guard must be bool", tr.Guard.GetSpan())
				}
			}
			for _, bs := range tr.Body {
				if err := c.checkStmt(bs, sc); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

func (c *checker) checkWorkflow(wf *ast.WorkflowDecl) error {
	wi := c.info.Workflows[wf.Name]
	sc := newScope(nil)
	for _, p := range wi.Params {
		sc.defineLocal(p.Name, varBinding{ty: p.Type, mutable: p.Mut, isParam: true, span: wf.Span})
	}
	pools := map[string]bool{}
	for _, pl := range wf.Pools {
		pools[pl.Name] = true
	}
	c.curReturn = wi.Return
	defer func() { c.curReturn = nil }()

	// First pass: check start & step bodies so variables bound before fork/choice are visible
	for _, n := range wf.Nodes {
		switch node := n.(type) {
		case *ast.StartNode:
			for _, st := range node.Body {
				if err := c.checkStmt(st, sc); err != nil {
					return err
				}
			}
		case *ast.ForkNode:
			branchWrites := map[string]string{}
			for _, br := range node.Branches {
				brSc := newScope(sc)
				for _, op := range br.Ops {
					switch op.Kind {
					case ast.BranchAcquire, ast.BranchRelease:
						if !pools[op.Target] {
							return fmt.Errorf("%s: workflow %s references unknown pool %q", op.Span, wf.Name, op.Target)
						}
					case ast.BranchSync:
						parts := strings.SplitN(op.Target, ".", 2)
						if _, ok := c.info.Machines[parts[0]]; !ok {
							return fmt.Errorf("%s: sync references unknown monitor/machine %q", op.Span, parts[0])
						}
					case ast.BranchStmt:
						if err := c.checkStmt(op.Stmt, brSc); err != nil {
							return err
						}
						if la, ok := op.Stmt.(*ast.LetAssignStmt); ok {
							if prevBr, dup := branchWrites[la.Name]; dup && prevBr != br.Name {
								return fmt.Errorf("%s: concurrent write race on variable %q in fork branches %q and %q", op.Span, la.Name, prevBr, br.Name)
							}
							branchWrites[la.Name] = br.Name
							if b, exists := brSc.vars[la.Name]; exists {
								sc.defineLocal(la.Name, b)
							}
						}
						// An element write or an in-place update changes the
						// variable it reaches, like an assignment to it.
						var written ast.Expr
						switch st := op.Stmt.(type) {
						case *ast.IndexAssignStmt:
							written = st.List
						case *ast.CompoundAssignStmt:
							written = st.Target
						}
						if path, ok := elementOwnerPath(written); written != nil && ok {
							if prevBr, dup := branchWrites[path]; dup && prevBr != br.Name {
								return fmt.Errorf("%s: concurrent write race on variable %q in fork branches %q and %q", op.Span, path, prevBr, br.Name)
							}
							branchWrites[path] = br.Name
						}
					}
				}
			}
		case *ast.ChoiceNode:
			for _, br := range node.Branches {
				if br.Guard != nil {
					ty, err := c.checkExpr(br.Guard, sc)
					if err != nil {
						return err
					}
					if ty.Kind() != KindBool && ty.Kind() != KindUnknown {
						return fmt.Errorf("%s: choice guard must be bool, got %s", br.Guard.GetSpan(), ty)
					}
				}
			}
		case *ast.StepNode:
			for _, st := range node.Body {
				if err := c.checkStmt(st, sc); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

func (c *checker) checkSystem(sys *ast.SystemDecl) error {
	for _, inst := range sys.Instances {
		_, isMachine := c.info.Machines[inst.TypeName]
		_, isWorkflow := c.info.Workflows[inst.TypeName]
		if !isMachine && !isWorkflow {
			return fmt.Errorf("%s: system %s instance %s has unknown process/workflow type %q", inst.Span, sys.Name, inst.Name, inst.TypeName)
		}
	}
	for _, chk := range sys.Checks {
		if chk.Kind == ast.CheckSatisfies {
			_, isProp := c.info.Properties[chk.Target]
			_, isProg := c.info.Progresses[chk.Target]
			if !isProp && !isProg {
				return fmt.Errorf("%s: system %s check satisfies unknown property/progress %q", chk.Span, sys.Name, chk.Target)
			}
		}
	}
	return nil
}

// ---------------------------------------------------------------------------
// Statement Checking
// ---------------------------------------------------------------------------

func (c *checker) checkStmt(stmt ast.Stmt, sc *scope) error {
	switch s := stmt.(type) {
	case *ast.LetAssignStmt:
		valTy, err := c.checkExpr(s.Value, sc)
		if err != nil {
			return err
		}
		// The literal `{}` fits every map type: a declared one, or the one
		// the variable already has. On its own it has str keys.
		lit, _ := s.Value.(*ast.MapLit)
		emptyMap := lit != nil && len(lit.Entries) == 0
		if s.TypeAnno != nil {
			annoTy, err := c.resolveTypeExpr(s.TypeAnno)
			if err != nil {
				return err
			}
			if !(emptyMap && annoTy.Kind() == KindMap) && !c.assignable(annoTy, valTy, s.Value) {
				return fmt.Errorf("%s: cannot assign %s to %s (%s)", s.Span, valTy, s.Name, annoTy)
			}
			// A variable keeps the type of its lists, maps and variants:
			// the kernel reads the range of an element from it.
			if prev, found := sc.lookup(s.Name); found && keepsType(prev.ty) && !(isAssignable(prev.ty, annoTy) && isAssignable(annoTy, prev.ty)) {
				return fmt.Errorf("%s: %s is a %s and cannot be declared again as a %s", s.Span, s.Name, prev.ty, annoTy)
			}
			valTy = annoTy
		} else if emptyMap {
			if prev, found := sc.lookup(s.Name); found && prev.ty != nil && prev.ty.Kind() == KindMap {
				valTy = prev.ty
			}
		} else if prev, found := sc.lookup(s.Name); found && keepsType(prev.ty) && valTy != nil && prev.ty.Kind() == valTy.Kind() {
			target, ok := fillUnknown(prev.ty, valTy, false)
			if !ok {
				return fmt.Errorf("%s: cannot assign %s to %s (%s): give %s a type where it is first assigned", s.Span, valTy, s.Name, prev.ty, s.Name)
			}
			if !c.assignable(target, valTy, s.Value) {
				return fmt.Errorf("%s: cannot assign %s to %s (%s): a variable keeps the type of its elements", s.Span, valTy, s.Name, target)
			}
			valTy = target
		} else if _, isInt := valTy.(*IntType); isInt {
			// The value of an int variable is the kernel's to work out;
			// its type holds across every later assignment.
			valTy = NewUnboundedInt()
		}
		if c.curFuncInfo != nil {
			c.addUnique(&c.curFuncInfo.Frame.Writes, s.Name)
		}
		sc.set(s.Name, varBinding{ty: valTy, mutable: true, span: s.Span})
		return nil

	case *ast.CompoundAssignStmt:
		lhsTy, err := c.checkExpr(s.Target, sc)
		if err != nil {
			return err
		}
		rhsTy, err := c.checkExpr(s.Value, sc)
		if err != nil {
			return err
		}
		if lhsTy.Kind() != KindInt || (rhsTy.Kind() != KindInt && rhsTy.Kind() != KindUnknown) {
			return fmt.Errorf("%s: compound assignment %s requires int operands", s.Span, s.Op)
		}
		if root, ok := elementOwnerPath(s.Target); ok {
			if err := c.ensureMutableTarget(root, sc, s.Span); err != nil {
				return err
			}
			if c.curFuncInfo != nil {
				c.addUnique(&c.curFuncInfo.Frame.Writes, root)
			}
		}
		return nil

	case *ast.FieldAssignStmt:
		objTy, err := c.checkExpr(s.Object, sc)
		if err != nil {
			return err
		}
		valTy, err := c.checkExpr(s.Value, sc)
		if err != nil {
			return err
		}
		if root, ok := rootVarPath(s.Object); ok {
			if err := c.ensureMutableTarget(root, sc, s.Span); err != nil {
				return err
			}
			if c.curFuncInfo != nil {
				c.addUnique(&c.curFuncInfo.Frame.Writes, root+"."+s.Field)
			}
		}
		if et, ok := objTy.(*EntityType); ok {
			ft, exists := et.FieldMap[s.Field]
			if !exists {
				return fmt.Errorf("%s: entity %s has no field %q", s.Span, et.Name, s.Field)
			}
			if !c.assignable(ft, valTy, s.Value) {
				return fmt.Errorf("%s: field %s.%s expects %s, got %s", s.Span, et.Name, s.Field, ft, valTy)
			}
		}
		return nil

	case *ast.IndexAssignStmt:
		lty, err := c.checkExpr(s.List, sc)
		if err != nil {
			return err
		}
		ity, err := c.checkExpr(s.Index, sc)
		if err != nil {
			return err
		}
		vty, err := c.checkExpr(s.Value, sc)
		if err != nil {
			return err
		}
		if lt, ok := lty.(*ListType); ok {
			if ity.Kind() != KindInt {
				return fmt.Errorf("%s: list index must be int, got %s", s.Span, ity)
			}
			if !c.assignable(lt.Elem, vty, s.Value) {
				return fmt.Errorf("%s: list element expects %s, got %s", s.Span, lt.Elem, vty)
			}
		}
		if mt, ok := lty.(*MapType); ok {
			if !isAssignable(mt.Key, ity) || !isMapKeyType(ity) {
				return fmt.Errorf("%s: map key expects %s, got %s", s.Span, mt.Key, ity)
			}
			if !c.assignable(mt.Val, vty, s.Value) {
				return fmt.Errorf("%s: map value expects %s, got %s", s.Span, mt.Val, vty)
			}
		}
		// Writing an element writes the list: a read-only parameter cannot
		// be changed this way either.
		if root, ok := elementOwnerPath(s.List); ok {
			if err := c.ensureMutableTarget(root, sc, s.Span); err != nil {
				return err
			}
			if c.curFuncInfo != nil {
				c.addUnique(&c.curFuncInfo.Frame.Writes, root)
			}
		}
		return nil

	case *ast.IfStmt:
		for _, br := range s.Branches {
			cty, err := c.checkExpr(br.Cond, sc)
			if err != nil {
				return err
			}
			if cty.Kind() != KindBool && cty.Kind() != KindUnknown {
				return fmt.Errorf("%s: if condition must be bool, got %s", br.Cond.GetSpan(), cty)
			}
			sub := newScope(sc)
			for _, bst := range br.Body {
				if err := c.checkStmt(bst, sub); err != nil {
					return err
				}
			}
		}
		if len(s.Else) > 0 {
			sub := newScope(sc)
			for _, est := range s.Else {
				if err := c.checkStmt(est, sub); err != nil {
					return err
				}
			}
		}
		return nil

	case *ast.MatchStmt:
		sty, err := c.checkExpr(s.Subject, sc)
		if err != nil {
			return err
		}
		for _, arm := range s.Arms {
			armSc := newScope(sc)
			if err := c.bindPattern(arm.Pattern, sty, armSc); err != nil {
				return err
			}
			if arm.Guard != nil {
				gty, err := c.checkExpr(arm.Guard, armSc)
				if err != nil {
					return err
				}
				if gty.Kind() != KindBool && gty.Kind() != KindUnknown {
					return fmt.Errorf("%s: match guard must be bool", arm.Guard.GetSpan())
				}
			}
			for _, bst := range arm.Body {
				if err := c.checkStmt(bst, armSc); err != nil {
					return err
				}
			}
		}
		return nil

	case *ast.ForStmt:
		sub := newScope(sc)
		if r, ok := s.Iterable.(*ast.RangeExpr); ok {
			lt, err := c.checkExpr(r.Lo, sc)
			if err != nil {
				return err
			}
			ht, err := c.checkExpr(r.Hi, sc)
			if err != nil {
				return err
			}
			if lt.Kind() != KindInt || ht.Kind() != KindInt {
				return fmt.Errorf("%s: range bounds must be int", r.Span)
			}
			sub.defineLocal(s.Var, varBinding{ty: NewUnboundedInt(), span: s.Span})
		} else {
			ity, err := c.checkExpr(s.Iterable, sc)
			if err != nil {
				return err
			}
			var elem Type = UnknownType{}
			if lt, ok := ity.(*ListType); ok {
				elem = lt.Elem
			}
			sub.defineLocal(s.Var, varBinding{ty: elem, span: s.Span})
		}
		for _, bst := range s.Body {
			if err := c.checkStmt(bst, sub); err != nil {
				return err
			}
		}
		return nil

	case *ast.WhileStmt:
		cty, err := c.checkExpr(s.Cond, sc)
		if err != nil {
			return err
		}
		if cty.Kind() != KindBool && cty.Kind() != KindUnknown {
			return fmt.Errorf("%s: while condition must be bool", s.Cond.GetSpan())
		}
		for _, inv := range s.Invariants {
			ity, err := c.checkExpr(inv, sc)
			if err != nil {
				return err
			}
			if ity.Kind() != KindBool && ity.Kind() != KindUnknown {
				return fmt.Errorf("%s: loop invariant must be bool", inv.GetSpan())
			}
		}
		if s.Decreases != nil {
			dty, err := c.checkExpr(s.Decreases, sc)
			if err != nil {
				return err
			}
			if dty.Kind() != KindInt && dty.Kind() != KindUnknown {
				return fmt.Errorf("%s: decreases must be int", s.Decreases.GetSpan())
			}
		}
		sub := newScope(sc)
		for _, bst := range s.Body {
			if err := c.checkStmt(bst, sub); err != nil {
				return err
			}
		}
		return nil

	case *ast.ReturnStmt:
		if s.Value == nil {
			return nil
		}
		vty, err := c.checkExpr(s.Value, sc)
		if err != nil {
			return err
		}
		if c.curReturn != nil && c.curReturn.Kind() != KindVoid {
			if !c.assignable(c.curReturn, vty, s.Value) {
				return fmt.Errorf("%s: return type mismatch: expected %s, got %s", s.Span, c.curReturn, vty)
			}
		}
		return nil

	case *ast.ExprStmt:
		_, err := c.checkExpr(s.Expr, sc)
		return err
	}
	return nil
}

func (c *checker) ensureMutableTarget(root string, sc *scope, span ast.Span) error {
	b, ok := sc.lookup(root)
	if !ok {
		return nil
	}
	if b.isParam && !b.mutable {
		return fmt.Errorf("%s: cannot mutate read-only parameter %q (declare parameter as 'mut %s')", span, root, root)
	}
	return nil
}

func (c *checker) bindPattern(pat ast.Pattern, subjTy Type, sc *scope) error {
	switch p := pat.(type) {
	case *ast.WildcardPat, *ast.IntPat, *ast.RangePat, *ast.BoolPat, *ast.StrPat:
		return nil
	case *ast.VarPat:
		sc.defineLocal(p.Name, varBinding{ty: subjTy, span: p.Span})
		return nil
	case *ast.VariantPat:
		adt, ok := c.info.Variants[p.Name]
		if !ok {
			if subjADT, isADT := subjTy.(*ADTType); isADT {
				adt = subjADT
			} else {
				return fmt.Errorf("%s: unknown ADT variant %q", p.Span, p.Name)
			}
		}
		vi, ok := adt.VariantMap[p.Name]
		if !ok {
			return fmt.Errorf("%s: variant %q not in ADT %s", p.Span, p.Name, adt.Name)
		}
		if len(p.Fields) > len(vi.Fields) {
			return fmt.Errorf("%s: variant %s expects %d fields, pattern has %d", p.Span, p.Name, len(vi.Fields), len(p.Fields))
		}
		// Resolve TypeVars using subjTy TypeArgs if applicable
		subMap := map[string]Type{}
		if subjADT, isADT := subjTy.(*ADTType); isADT && subjADT.Name == adt.Name {
			for i, tp := range adt.TypeParams {
				if i < len(subjADT.TypeArgs) {
					subMap[tp] = subjADT.TypeArgs[i]
				}
			}
		}
		for i, subPat := range p.Fields {
			fty := vi.Fields[i].Type
			if tv, isTV := fty.(TypeVar); isTV {
				if rep, ok := subMap[tv.Name]; ok {
					fty = rep
				}
			}
			if err := c.bindPattern(subPat, fty, sc); err != nil {
				return err
			}
		}
		return nil
	}
	return nil
}

// ---------------------------------------------------------------------------
// Expression Checking
// ---------------------------------------------------------------------------

func (c *checker) checkExpr(expr ast.Expr, sc *scope) (Type, error) {
	if expr == nil {
		return VoidType{}, nil
	}
	ty, err := c.checkExprInner(expr, sc)
	if err != nil {
		return nil, err
	}
	c.info.ExprTypes[expr] = ty
	return ty, nil
}

func (c *checker) checkExprInner(expr ast.Expr, sc *scope) (Type, error) {
	switch e := expr.(type) {
	case *ast.IntLit:
		return NewIntRange(e.Value, e.Value, ""), nil
	case *ast.BoolLit:
		return BoolType{}, nil
	case *ast.StrLit:
		return StrType{}, nil
	case *ast.NoneLit:
		return &ADTType{Name: "Option", TypeParams: []string{"T"}, VariantMap: c.info.ADTs["Option"].VariantMap}, nil
	case *ast.FStrExpr:
		for _, part := range e.Parts {
			if part.IsExpr {
				if _, err := c.checkExpr(part.Expr, sc); err != nil {
					return nil, err
				}
			}
		}
		return StrType{}, nil
	case *ast.Ident:
		if b, ok := sc.lookup(e.Name); ok {
			if c.curFuncInfo != nil {
				c.addUnique(&c.curFuncInfo.Frame.Reads, e.Name)
			}
			return b.ty, nil
		}
		if modPath, ok := c.info.Imports[e.Name]; ok {
			return &ModuleType{Path: modPath, Alias: e.Name}, nil
		}
		if pt, ok := c.info.Ports[e.Name]; ok {
			return pt, nil
		}
		if fi, ok := c.info.Funcs[e.Name]; ok {
			return fi.Type, nil
		}
		if adt, ok := c.info.Variants[e.Name]; ok {
			return adt, nil
		}
		return nil, fmt.Errorf("%s: undefined identifier %q", e.Span, e.Name)

	case *ast.OldExpr:
		return c.checkExpr(e.Inner, sc)

	case *ast.UnaryExpr:
		ity, err := c.checkExpr(e.Expr, sc)
		if err != nil {
			return nil, err
		}
		if e.Op == "not" {
			return BoolType{}, nil
		}
		if it, ok := ity.(*IntType); ok && e.Op == "-" {
			if it.IsBounded {
				return NewIntRange(-it.Hi, -it.Lo, ""), nil
			}
			return NewUnboundedInt(), nil
		}
		return ity, nil

	case *ast.BinaryExpr:
		lt, err := c.checkExpr(e.Left, sc)
		if err != nil {
			return nil, err
		}
		rt, err := c.checkExpr(e.Right, sc)
		if err != nil {
			return nil, err
		}
		switch e.Op {
		case "+", "-", "*", "/", "%":
			if lt.Kind() == KindStr && e.Op == "+" {
				return StrType{}, nil
			}
			if (lt.Kind() != KindInt && lt.Kind() != KindUnknown) || (rt.Kind() != KindInt && rt.Kind() != KindUnknown) {
				return nil, fmt.Errorf("%s: arithmetic %s requires int, got %s and %s", e.Span, e.Op, lt, rt)
			}
			return NewUnboundedInt(), nil
		case "==", "!=", "<", "<=", ">", ">=", "and", "or", "implies", "in":
			return BoolType{}, nil
		}
		return UnknownType{}, nil

	case *ast.RangeExpr:
		if _, err := c.checkExpr(e.Lo, sc); err != nil {
			return nil, err
		}
		if _, err := c.checkExpr(e.Hi, sc); err != nil {
			return nil, err
		}
		return &ListType{Elem: NewUnboundedInt()}, nil

	case *ast.ListLit:
		var elem Type = UnknownType{}
		for _, el := range e.Elems {
			et, err := c.checkExpr(el, sc)
			if err != nil {
				return nil, err
			}
			// The element type covers every element: the ranges of ints
			// are joined, as are the arguments of Result and Option.
			elem = unifyTypes(elem, et)
		}
		// On its own a literal is a list of int: a narrower element range
		// is one it is given where it goes (assignable).
		elem = widenInt(elem)
		return &ListType{Elem: elem, Cap: int64(len(e.Elems)), HasCap: false}, nil

	case *ast.MapLit:
		var kt, vt Type = StrType{}, UnknownType{}
		for i, ent := range e.Entries {
			k, err := c.checkExpr(ent.Key, sc)
			if err != nil {
				return nil, err
			}
			v, err := c.checkExpr(ent.Value, sc)
			if err != nil {
				return nil, err
			}
			if i > 0 && !isAssignable(kt, k) {
				return nil, fmt.Errorf("%s: map keys must have one type, got %s and %s", e.Span, kt, k)
			}
			kt = k
			if vt.Kind() == KindUnknown {
				vt = v
			} else {
				vt = unifyTypes(vt, v)
			}
		}
		if !isMapKeyType(kt) {
			return nil, fmt.Errorf("%s: a map key must be str, int or bool, got %s", e.Span, kt)
		}
		vt = widenInt(vt)
		return &MapType{Key: kt, Val: vt}, nil

	case *ast.WithExpr:
		baseTy, err := c.checkExpr(e.Base, sc)
		if err != nil {
			return nil, err
		}
		for _, f := range e.Fields {
			vt, err := c.checkExpr(f.Value, sc)
			if err != nil {
				return nil, err
			}
			if et, ok := baseTy.(*EntityType); ok {
				ft, exists := et.FieldMap[f.Name]
				if !exists {
					return nil, fmt.Errorf("%s: entity %s has no field %q in with-update", e.Span, et.Name, f.Name)
				}
				if !c.assignable(ft, vt, f.Value) {
					return nil, fmt.Errorf("%s: field %s.%s expects %s, got %s", e.Span, et.Name, f.Name, ft, vt)
				}
			}
		}
		return baseTy, nil

	case *ast.FieldExpr:
		objTy, err := c.checkExpr(e.Object, sc)
		if err != nil {
			return nil, err
		}
		if mt, ok := objTy.(*ModuleType); ok {
			if c.curFuncInfo != nil {
				c.addUnique(&c.curFuncInfo.Frame.PortEffects, mt.Path+"."+e.Field)
			}
			return c.lookupModuleMemberType(mt.Path, e.Field, e.Span)
		}
		if pt, ok := objTy.(*PortType); ok {
			if c.curFuncInfo != nil {
				c.addUnique(&c.curFuncInfo.Frame.PortEffects, pt.Name+"."+e.Field)
			}
			for _, ex := range pt.Decl.Externs {
				if ex.Name == e.Field {
					return c.funcSigToType(ex)
				}
			}
			// Also allow state-machine protocol actions as callable extern methods
			for _, st := range pt.Decl.States {
				for _, tr := range st.Transitions {
					if tr.Action == e.Field {
						return &FuncType{Return: VoidType{}}, nil
					}
				}
			}
			return nil, fmt.Errorf("%s: port %s has no member %q", e.Span, pt.Name, e.Field)
		}
		if et, ok := objTy.(*EntityType); ok {
			if ft, exists := et.FieldMap[e.Field]; exists {
				return ft, nil
			}
			for _, rel := range et.Relations {
				if rel.Name == e.Field {
					if rel.Multiplicity == "1" || rel.Multiplicity == "0..1" {
						return c.info.Entities[rel.Target], nil
					}
					return &ListType{Elem: c.info.Entities[rel.Target]}, nil
				}
			}
			return nil, fmt.Errorf("%s: entity %s has no field %q", e.Span, et.Name, e.Field)
		}
		if ht, ok := objTy.(*HandleType); ok {
			return c.lookupHandleMethod(ht, e.Field, e.Span)
		}
		if objTy.Kind() == KindList && e.Field == "len" {
			return &FuncType{Return: NewIntRange(0, DefaultMaxInt, "")}, nil
		}
		if objTy.Kind() == KindStr && e.Field == "len" {
			return &FuncType{Return: NewIntRange(0, DefaultMaxInt, "")}, nil
		}
		return UnknownType{}, nil

	case *ast.IndexExpr:
		lty, err := c.checkExpr(e.List, sc)
		if err != nil {
			return nil, err
		}
		ity, err := c.checkExpr(e.Index, sc)
		if err != nil {
			return nil, err
		}
		if lt, ok := lty.(*ListType); ok {
			if ity.Kind() != KindInt && ity.Kind() != KindUnknown {
				return nil, fmt.Errorf("%s: list index must be int, got %s", e.Span, ity)
			}
			return lt.Elem, nil
		}
		if mt, ok := lty.(*MapType); ok {
			return mt.Val, nil
		}
		if lty.Kind() == KindStr {
			return StrType{}, nil
		}
		return UnknownType{}, nil

	case *ast.TryExpr:
		innerTy, err := c.checkExpr(e.Inner, sc)
		if err != nil {
			return nil, err
		}
		if adt, ok := innerTy.(*ADTType); ok {
			if adt.Name == "Result" && len(adt.TypeArgs) >= 1 {
				return adt.TypeArgs[0], nil
			}
			if adt.Name == "Option" && len(adt.TypeArgs) >= 1 {
				return adt.TypeArgs[0], nil
			}
		}
		return UnknownType{}, nil

	case *ast.MatchExpr:
		sty, err := c.checkExpr(e.Subject, sc)
		if err != nil {
			return nil, err
		}
		var resTy Type = UnknownType{}
		for _, arm := range e.Arms {
			armSc := newScope(sc)
			if err := c.bindPattern(arm.Pattern, sty, armSc); err != nil {
				return nil, err
			}
			if arm.Guard != nil {
				if _, err := c.checkExpr(arm.Guard, armSc); err != nil {
					return nil, err
				}
			}
			vt, err := c.checkExpr(arm.Value, armSc)
			if err != nil {
				return nil, err
			}
			resTy = unifyTypes(resTy, vt)
		}
		return resTy, nil

	case *ast.RunWorkflowExpr:
		wi, ok := c.info.Workflows[e.Name]
		if !ok {
			return nil, fmt.Errorf("%s: unknown workflow %q", e.Span, e.Name)
		}
		if len(e.Args) != len(wi.Params) {
			return nil, fmt.Errorf("%s: workflow %s expects %d args, got %d", e.Span, e.Name, len(wi.Params), len(e.Args))
		}
		if err := c.checkCallAliasing(e.Args, false); err != nil {
			return nil, err
		}
		for i, arg := range e.Args {
			at, err := c.checkExpr(arg.Value, sc)
			if err != nil {
				return nil, err
			}
			pi, ok := boundParam(wi.Params, arg, i)
			if !ok {
				return nil, fmt.Errorf("%s: workflow %s has no parameter %q", arg.Span, e.Name, arg.Name)
			}
			if wi.Params[pi].Mut && !arg.Mut {
				return nil, fmt.Errorf("%s: argument %d to workflow %s must be marked 'mut'", arg.Span, i+1, e.Name)
			}
			if arg.Own {
				return nil, fmt.Errorf("%s: unexpected 'own': a workflow cannot take ownership of a handle", arg.Span)
			}
			if !c.assignable(wi.Params[pi].Type, at, arg.Value) {
				return nil, fmt.Errorf("%s: workflow %s arg %d expects %s, got %s", arg.Span, e.Name, i+1, wi.Params[pi].Type, at)
			}
		}
		if err := c.checkCallAliasing(e.Args, true); err != nil {
			return nil, err
		}
		return wi.Return, nil

	case *ast.LambdaExpr:
		// When checked standalone without pipe context, infer params as Unknown
		lsc := newScope(sc)
		var ps []FuncParamInfo
		for _, pname := range e.Params {
			lsc.defineLocal(pname, varBinding{ty: UnknownType{}, span: e.Span})
			ps = append(ps, FuncParamInfo{Name: pname, Type: UnknownType{}})
		}
		rt, err := c.checkExpr(e.Body, lsc)
		if err != nil {
			return nil, err
		}
		return &FuncType{Params: ps, Return: rt}, nil

	case *ast.PipeExpr:
		return c.checkPipeExpr(e, sc)

	case *ast.CallExpr:
		return c.checkCallExpr(e, sc)
	}
	return UnknownType{}, nil
}

func (c *checker) checkCallExpr(e *ast.CallExpr, sc *scope) (Type, error) {
	// SPARK Anti-Aliasing rule on all call sites
	if err := c.checkCallAliasing(e.Args, false); err != nil {
		return nil, err
	}

	// Check special built-in functions first
	if id, ok := e.Callee.(*ast.Ident); ok {
		switch id.Name {
		case "len":
			if len(e.Args) != 1 {
				return nil, fmt.Errorf("%s: len() takes 1 argument", e.Span)
			}
			if _, err := c.checkExpr(e.Args[0].Value, sc); err != nil {
				return nil, err
			}
			return NewIntRange(0, DefaultMaxInt, ""), nil
		case "print", "assert":
			for _, a := range e.Args {
				if _, err := c.checkExpr(a.Value, sc); err != nil {
					return nil, err
				}
			}
			return VoidType{}, nil
		case "str", "to_str":
			for _, a := range e.Args {
				if _, err := c.checkExpr(a.Value, sc); err != nil {
					return nil, err
				}
			}
			return StrType{}, nil
		case "abs", "min", "max":
			for _, a := range e.Args {
				if _, err := c.checkExpr(a.Value, sc); err != nil {
					return nil, err
				}
			}
			return NewUnboundedInt(), nil
		case "Some":
			if len(e.Args) != 1 {
				return nil, fmt.Errorf("%s: Some() expects 1 argument", e.Span)
			}
			vt, err := c.checkExpr(e.Args[0].Value, sc)
			if err != nil {
				return nil, err
			}
			return c.instantiateADT("Option", []Type{widenInt(vt)}), nil
		case "Ok":
			if len(e.Args) != 1 {
				return nil, fmt.Errorf("%s: Ok() expects 1 argument", e.Span)
			}
			vt, err := c.checkExpr(e.Args[0].Value, sc)
			if err != nil {
				return nil, err
			}
			return c.instantiateADT("Result", []Type{widenInt(vt), UnknownType{}}), nil
		case "Err":
			if len(e.Args) != 1 {
				return nil, fmt.Errorf("%s: Err() expects 1 argument", e.Span)
			}
			et, err := c.checkExpr(e.Args[0].Value, sc)
			if err != nil {
				return nil, err
			}
			return c.instantiateADT("Result", []Type{UnknownType{}, widenInt(et)}), nil
		}

		// Entity constructor: Account(balance=10, frozen=0)
		if et, ok := c.info.Entities[id.Name]; ok {
			for _, a := range e.Args {
				at, err := c.checkExpr(a.Value, sc)
				if err != nil {
					return nil, err
				}
				if a.Name != "" {
					ft, exists := et.FieldMap[a.Name]
					if !exists {
						isRel := false
						for _, rel := range et.Relations {
							if rel.Name == a.Name {
								isRel = true
								break
							}
						}
						if !isRel {
							return nil, fmt.Errorf("%s: entity %s has no field %q", a.Span, et.Name, a.Name)
						}
					} else if !c.assignable(ft, at, a.Value) {
						return nil, fmt.Errorf("%s: field %s.%s expects %s, got %s", a.Span, et.Name, a.Name, ft, at)
					}
				}
			}
			return et, nil
		}

		// User ADT variant constructor
		if adt, ok := c.info.Variants[id.Name]; ok {
			vi := adt.VariantMap[id.Name]
			for i, a := range e.Args {
				at, err := c.checkExpr(a.Value, sc)
				if err != nil {
					return nil, err
				}
				// Both backends fill the fields of a variant in the order
				// the arguments are written, whatever they are named.
				if i >= len(vi.Fields) {
					return nil, fmt.Errorf("%s: %s has %d field(s), got %d arguments", e.Span, id.Name, len(vi.Fields), len(e.Args))
				}
				if a.Name != "" && a.Name != vi.Fields[i].Name {
					return nil, fmt.Errorf("%s: field %d of %s is %s, not %s: the fields of a variant are given in order", a.Span, i+1, id.Name, vi.Fields[i].Name, a.Name)
				}
				ft := vi.Fields[i].Type
				if !c.assignable(ft, at, a.Value) {
					return nil, fmt.Errorf("%s: field %d of %s expects %s, got %s", a.Span, i+1, id.Name, ft, at)
				}
			}
			return adt, nil
		}

		// User function call
		if fi, ok := c.info.Funcs[id.Name]; ok {
			if err := c.checkFuncArgs(id.Name, fi, e.Args, sc, e.Span); err != nil {
				return nil, err
			}
			if c.curFuncInfo != nil {
				for _, pe := range fi.Frame.PortEffects {
					c.addUnique(&c.curFuncInfo.Frame.PortEffects, pe)
				}
			}
			return fi.Type.Return, nil
		}
	}

	// Module or Method call
	if fe, ok := e.Callee.(*ast.FieldExpr); ok {
		objTy, err := c.checkExpr(fe.Object, sc)
		if err != nil {
			return nil, err
		}
		// Enforce std.requests explicit bounded timeout_ms contract!
		if mt, ok := objTy.(*ModuleType); ok && mt.Path == "std.requests" {
			if fe.Field == "get" || fe.Field == "post" {
				if err := c.checkRequestsTimeout(e, fe.Field, sc); err != nil {
					return nil, err
				}
			}
		}
		if ht, ok := objTy.(*HandleType); ok && (ht.Name == "req.Session" || ht.Name == "sock.TcpListener") {
			if fe.Field == "get" || fe.Field == "post" || fe.Field == "get_async" || fe.Field == "accept" {
				if err := c.checkRequestsTimeout(e, fe.Field, sc); err != nil {
					return nil, err
				}
			}
		}
		// std.json.decode[T](str) -> Result[T, str]
		if mt, ok := objTy.(*ModuleType); ok && mt.Path == "std.json" && fe.Field == "decode" {
			for _, a := range e.Args {
				if _, err := c.checkExpr(a.Value, sc); err != nil {
					return nil, err
				}
			}
			var targetTy Type = UnknownType{}
			if len(e.TypeArgs) == 1 {
				var err error
				targetTy, err = c.resolveTypeExpr(e.TypeArgs[0])
				if err != nil {
					return nil, err
				}
			}
			return c.instantiateADT("Result", []Type{targetTy, StrType{}}), nil
		}
		// std.concurrent.Channel[T](cap=N) or ThreadPool(workers, queue_cap)
		if mt, ok := objTy.(*ModuleType); ok && mt.Path == "std.concurrent" {
			for _, a := range e.Args {
				if _, err := c.checkExpr(a.Value, sc); err != nil {
					return nil, err
				}
			}
			switch fe.Field {
			case "Channel":
				var elem Type = UnknownType{}
				if len(e.TypeArgs) == 1 {
					elem, _ = c.resolveTypeExpr(e.TypeArgs[0])
				}
				return &HandleType{Name: "conc.Channel", Elem: elem, Protocol: c.info.StdHandles["conc.Channel"]}, nil
			case "ThreadPool":
				return &HandleType{Name: "conc.ThreadPool", Protocol: c.info.StdHandles["conc.ThreadPool"]}, nil
			case "Mutex":
				var elem Type = UnknownType{}
				if len(e.Args) >= 1 {
					elem, _ = c.checkExpr(e.Args[0].Value, sc)
				}
				return &HandleType{Name: "conc.Mutex", Elem: elem}, nil
			case "Semaphore":
				return &HandleType{Name: "conc.Semaphore"}, nil
			case "parallel_map":
				return &ListType{Elem: UnknownType{}}, nil
			}
		}
	}

	calleeTy, err := c.checkExpr(e.Callee, sc)
	if err != nil {
		return nil, err
	}
	for _, a := range e.Args {
		if _, err := c.checkExpr(a.Value, sc); err != nil {
			return nil, err
		}
	}
	if err := c.checkCallAliasing(e.Args, true); err != nil {
		return nil, err
	}
	if ft, ok := calleeTy.(*FuncType); ok {
		return ft.Return, nil
	}
	return UnknownType{}, nil
}

// checkRequestsTimeout requires a blocking call to name its timeout. A
// timeout whose type has a range is checked here; the kernel proves the
// value in 1..300_000 whatever its type (ProgramInfo.TimeoutArgs).
func (c *checker) checkRequestsTimeout(call *ast.CallExpr, method string, sc *scope) error {
	args, span := call.Args, call.Span
	var timeoutExpr ast.Expr
	for _, a := range args {
		if a.Name == "timeout_ms" {
			timeoutExpr = a.Value
			break
		}
	}
	if timeoutExpr == nil {
		// Check positional index for get(url, timeout_ms) or post(url, body, timeout_ms)
		if (method == "get" || method == "get_async") && len(args) >= 2 && args[1].Name == "" {
			timeoutExpr = args[1].Value
		} else if method == "post" && len(args) >= 3 && args[2].Name == "" {
			timeoutExpr = args[2].Value
		} else if method == "accept" && len(args) >= 1 && args[0].Name == "" {
			timeoutExpr = args[0].Value
		}
	}
	if timeoutExpr == nil {
		return fmt.Errorf("%s: '%s' requires explicit bounded 'timeout_ms: int[1..300_000]' to prevent unbounded blocking (liveness contract)", span, method)
	}
	ty, err := c.checkExpr(timeoutExpr, sc)
	if err != nil {
		return err
	}
	c.info.TimeoutArgs[call] = timeoutExpr
	if it, ok := ty.(*IntType); ok && it.IsBounded {
		if it.Lo < 1 || it.Hi > 300_000 {
			return fmt.Errorf("%s: timeout_ms range [%d..%d] exceeds legal contract int[1..300_000]", timeoutExpr.GetSpan(), it.Lo, it.Hi)
		}
	} else if ty.Kind() != KindInt && ty.Kind() != KindUnknown {
		return fmt.Errorf("%s: timeout_ms must be int[1..300_000], got %s", timeoutExpr.GetSpan(), ty)
	}
	return nil
}

// boundParam returns the index of the parameter that argument i of a call
// is bound to, as both backends do: the one a keyword argument names, else
// the one at its position.
func boundParam(params []FuncParamInfo, a ast.CallArg, i int) (int, bool) {
	if a.Name == "" {
		return i, i < len(params)
	}
	for k, p := range params {
		if p.Name == a.Name {
			return k, true
		}
	}
	return 0, false
}

// checkFuncArgs checks the arguments of a call of the function name
// against its parameters.
func (c *checker) checkFuncArgs(name string, fi *FuncInfo, args []ast.CallArg, sc *scope, span ast.Span) error {
	if len(args) != len(fi.Type.Params) {
		return fmt.Errorf("%s: function %s expects %d args, got %d", span, name, len(fi.Type.Params), len(args))
	}
	for i, a := range args {
		at, err := c.checkExpr(a.Value, sc)
		if err != nil {
			return err
		}
		pi, ok := boundParam(fi.Type.Params, a, i)
		if !ok {
			return fmt.Errorf("%s: function %s has no parameter %q", a.Span, name, a.Name)
		}
		p := fi.Type.Params[pi]
		if p.Mut {
			if !a.Mut {
				return fmt.Errorf("%s: argument %d to %s requires 'mut'", a.Span, i+1, name)
			}
			if root, ok := rootVarPath(a.Value); ok {
				if err := c.ensureMutableTarget(root, sc, a.Span); err != nil {
					return err
				}
			} else {
				return fmt.Errorf("%s: 'mut' argument must be a variable or field", a.Span)
			}
		} else if a.Mut {
			return fmt.Errorf("%s: unexpected 'mut' on read-only parameter %d of %s", a.Span, pi+1, name)
		}
		if p.Own {
			if !a.Own {
				return fmt.Errorf("%s: argument %d to %s takes ownership and requires 'own'", a.Span, i+1, name)
			}
			if _, ok := a.Value.(*ast.Ident); !ok {
				return fmt.Errorf("%s: 'own' argument must be a variable", a.Span)
			}
		} else if a.Own {
			return fmt.Errorf("%s: unexpected 'own' on borrowed parameter %d of %s", a.Span, pi+1, name)
		}
		if !c.assignable(p.Type, at, a.Value) {
			return fmt.Errorf("%s: arg %d of %s expects %s, got %s", a.Span, i+1, name, p.Type, at)
		}
	}
	return c.checkCallAliasing(args, true)
}

func (c *checker) checkPipeExpr(e *ast.PipeExpr, sc *scope) (Type, error) {
	lhsTy, err := c.checkExpr(e.Left, sc)
	if err != nil {
		return nil, err
	}
	// Determine function name and arguments on RHS
	var fnName string
	var callArgs []ast.CallArg
	direct := false // the stage names a function: `x |> f` or `x |> f(a)`
	switch rhs := e.Right.(type) {
	case *ast.CallExpr:
		callArgs = rhs.Args
		switch cal := rhs.Callee.(type) {
		case *ast.Ident:
			fnName, direct = cal.Name, true
		case *ast.FieldExpr:
			fnName = cal.Field
		}
	case *ast.Ident:
		fnName, direct = rhs.Name, true
	}

	var elemTy Type = UnknownType{}
	if lt, ok := lhsTy.(*ListType); ok {
		elemTy = lt.Elem
	}

	switch fnName {
	case "filter":
		if len(callArgs) == 1 {
			if lam, ok := callArgs[0].Value.(*ast.LambdaExpr); ok && len(lam.Params) == 1 {
				lsc := newScope(sc)
				lsc.defineLocal(lam.Params[0], varBinding{ty: elemTy, span: lam.Span})
				bty, err := c.checkExpr(lam.Body, lsc)
				if err != nil {
					return nil, err
				}
				if bty.Kind() != KindBool && bty.Kind() != KindUnknown {
					return nil, fmt.Errorf("%s: filter predicate must return bool, got %s", lam.Span, bty)
				}
				c.info.ExprTypes[lam] = &FuncType{Params: []FuncParamInfo{{Name: lam.Params[0], Type: elemTy}}, Return: BoolType{}}
				return lhsTy, nil
			}
		}
		return lhsTy, nil

	case "map":
		if len(callArgs) == 1 {
			if lam, ok := callArgs[0].Value.(*ast.LambdaExpr); ok && len(lam.Params) == 1 {
				lsc := newScope(sc)
				lsc.defineLocal(lam.Params[0], varBinding{ty: elemTy, span: lam.Span})
				rty, err := c.checkExpr(lam.Body, lsc)
				if err != nil {
					return nil, err
				}
				c.info.ExprTypes[lam] = &FuncType{Params: []FuncParamInfo{{Name: lam.Params[0], Type: elemTy}}, Return: rty}
				var capVal int64
				var hasCap bool
				if lt, ok := lhsTy.(*ListType); ok {
					capVal, hasCap = lt.Cap, lt.HasCap
				}
				return &ListType{Elem: widenInt(rty), Cap: capVal, HasCap: hasCap}, nil
			}
		}
		return &ListType{Elem: UnknownType{}}, nil

	case "flat_map":
		if len(callArgs) == 1 {
			if lam, ok := callArgs[0].Value.(*ast.LambdaExpr); ok && len(lam.Params) == 1 {
				lsc := newScope(sc)
				lsc.defineLocal(lam.Params[0], varBinding{ty: elemTy, span: lam.Span})
				rty, err := c.checkExpr(lam.Body, lsc)
				if err != nil {
					return nil, err
				}
				c.info.ExprTypes[lam] = &FuncType{Params: []FuncParamInfo{{Name: lam.Params[0], Type: elemTy}}, Return: rty}
				if rlt, ok := rty.(*ListType); ok {
					return rlt, nil
				}
				return &ListType{Elem: rty}, nil
			}
		}
		return &ListType{Elem: UnknownType{}}, nil

	case "fold":
		if len(callArgs) == 2 {
			accTy, err := c.checkExpr(callArgs[0].Value, sc)
			if err != nil {
				return nil, err
			}
			if lam, ok := callArgs[1].Value.(*ast.LambdaExpr); ok && len(lam.Params) == 2 {
				lsc := newScope(sc)
				lsc.defineLocal(lam.Params[0], varBinding{ty: accTy, span: lam.Span})
				lsc.defineLocal(lam.Params[1], varBinding{ty: elemTy, span: lam.Span})
				rty, err := c.checkExpr(lam.Body, lsc)
				if err != nil {
					return nil, err
				}
				c.info.ExprTypes[lam] = &FuncType{
					Params: []FuncParamInfo{{Name: lam.Params[0], Type: accTy}, {Name: lam.Params[1], Type: elemTy}},
					Return: rty,
				}
				return unifyTypes(accTy, rty), nil
			}
			return accTy, nil
		}
	case "sum":
		return NewUnboundedInt(), nil
	case "any", "all":
		if len(callArgs) == 1 {
			if lam, ok := callArgs[0].Value.(*ast.LambdaExpr); ok && len(lam.Params) == 1 {
				lsc := newScope(sc)
				lsc.defineLocal(lam.Params[0], varBinding{ty: elemTy, span: lam.Span})
				if _, err := c.checkExpr(lam.Body, lsc); err != nil {
					return nil, err
				}
			}
		}
		return BoolType{}, nil
	case "find":
		if len(callArgs) == 1 {
			if lam, ok := callArgs[0].Value.(*ast.LambdaExpr); ok && len(lam.Params) == 1 {
				lsc := newScope(sc)
				lsc.defineLocal(lam.Params[0], varBinding{ty: elemTy, span: lam.Span})
				if _, err := c.checkExpr(lam.Body, lsc); err != nil {
					return nil, err
				}
			}
		}
		return c.instantiateADT("Option", []Type{elemTy}), nil
	case "take", "drop":
		for _, a := range callArgs {
			if _, err := c.checkExpr(a.Value, sc); err != nil {
				return nil, err
			}
		}
		return lhsTy, nil
	case "filter_ok":
		if adt, ok := elemTy.(*ADTType); ok && (adt.Name == "Result" || adt.Name == "Option") && len(adt.TypeArgs) >= 1 {
			return &ListType{Elem: adt.TypeArgs[0]}, nil
		}
		return &ListType{Elem: UnknownType{}}, nil
	case "unwrap_or":
		if len(callArgs) == 1 {
			dt, err := c.checkExpr(callArgs[0].Value, sc)
			if err != nil {
				return nil, err
			}
			return dt, nil
		}
	case "and_then":
		if len(callArgs) == 1 {
			if lam, ok := callArgs[0].Value.(*ast.LambdaExpr); ok && len(lam.Params) == 1 {
				var okTy Type = UnknownType{}
				if adt, ok := lhsTy.(*ADTType); ok && len(adt.TypeArgs) >= 1 {
					okTy = adt.TypeArgs[0]
				}
				lsc := newScope(sc)
				lsc.defineLocal(lam.Params[0], varBinding{ty: okTy, span: lam.Span})
				return c.checkExpr(lam.Body, lsc)
			}
		}
	}

	// Generic pipe: `x |> f(a)` -> call f(x, a)
	if fi, ok := c.info.Funcs[fnName]; ok {
		if !direct {
			for _, a := range callArgs {
				if _, err := c.checkExpr(a.Value, sc); err != nil {
					return nil, err
				}
			}
			return fi.Type.Return, nil
		}
		args := append([]ast.CallArg{{Value: e.Left, Span: e.Left.GetSpan()}}, callArgs...)
		if err := c.checkFuncArgs(fnName, fi, args, sc, e.Span); err != nil {
			return nil, err
		}
		return fi.Type.Return, nil
	}
	if _, err := c.checkExpr(e.Right, sc); err != nil {
		return nil, err
	}
	return UnknownType{}, nil
}

// checkCallAliasing rejects a call whose mut argument overlaps another
// argument. With elements set, which needs the arguments to be type-checked
// already, an entity, list or map read out of a container counts as that
// container.
func (c *checker) checkCallAliasing(args []ast.CallArg, elements bool) error {
	var mutRoots []struct {
		root string
		span ast.Span
	}
	var allRoots []struct {
		root string
		mut  bool
		span ast.Span
	}
	for _, a := range args {
		root, ok := rootVarPath(a.Value)
		if !ok && elements && c.isSharedElement(a.Value) {
			// An entity, list or map read out of a container is the same
			// object the container holds.
			root, ok = containerPath(a.Value)
		}
		if ok {
			allRoots = append(allRoots, struct {
				root string
				mut  bool
				span ast.Span
			}{root, a.Mut, a.Span})
			if a.Mut {
				mutRoots = append(mutRoots, struct {
					root string
					span ast.Span
				}{root, a.Span})
			}
		}
	}
	for _, m := range mutRoots {
		seenCount := 0
		for _, r := range allRoots {
			if pathsOverlap(m.root, r.root) {
				seenCount++
			}
		}
		if seenCount > 1 {
			return fmt.Errorf("%s: SPARK anti-aliasing violation: mutable argument %q overlaps with another argument in the same call", m.span, m.root)
		}
	}
	return nil
}

func pathsOverlap(a, b string) bool {
	return a == b || strings.HasPrefix(a, b+".") || strings.HasPrefix(b, a+".")
}

func rootVarPath(e ast.Expr) (string, bool) {
	switch x := e.(type) {
	case *ast.Ident:
		return x.Name, true
	case *ast.FieldExpr:
		base, ok := rootVarPath(x.Object)
		if !ok {
			return "", false
		}
		return base + "." + x.Field, true
	default:
		return "", false
	}
}

// containerPath returns the variable path e is read from, ignoring indexes:
// box.rows for box.rows[i], rows.inner for rows[i].inner.
func containerPath(e ast.Expr) (string, bool) {
	switch x := e.(type) {
	case *ast.Ident:
		return x.Name, true
	case *ast.FieldExpr:
		base, ok := containerPath(x.Object)
		if !ok {
			return "", false
		}
		return base + "." + x.Field, true
	case *ast.IndexExpr:
		return containerPath(x.List)
	}
	return "", false
}

// isSharedElement reports whether e reads, through an index, a value that is
// passed by reference.
func (c *checker) isSharedElement(e ast.Expr) bool {
	switch e.(type) {
	case *ast.IndexExpr, *ast.FieldExpr:
	default:
		return false
	}
	ty := c.info.ExprTypes[e]
	if ty == nil {
		return false
	}
	switch ty.Kind() {
	case KindEntity, KindList, KindMap:
		return true
	}
	return false
}

// isMapKeyType reports whether keys of type t are told apart by the runtimes,
// which compare keys by their printed form.
func isMapKeyType(t Type) bool {
	switch t.Kind() {
	case KindStr, KindInt, KindBool, KindUnknown:
		return true
	}
	return false
}

// elementOwnerPath returns the variable path of the list or map that the
// assignment target e is an element of (xs for xs[i], box.rows for
// box.rows[i][j]); for any other target it is rootVarPath.
func elementOwnerPath(e ast.Expr) (string, bool) {
	for {
		ix, ok := e.(*ast.IndexExpr)
		if !ok {
			return rootVarPath(e)
		}
		e = ix.List
	}
}

func (c *checker) instantiateADT(name string, args []Type) *ADTType {
	base := c.info.ADTs[name]
	cp := *base
	cp.TypeArgs = args
	return &cp
}

func (c *checker) funcSigToType(sig ast.FuncSig) (*FuncType, error) {
	var ps []FuncParamInfo
	for _, p := range sig.Params {
		pt, err := c.resolveTypeExpr(p.Type)
		if err != nil {
			return nil, err
		}
		ps = append(ps, FuncParamInfo{Name: p.Name, Mut: p.Mut, Own: p.Own, Type: pt})
	}
	ret := Type(VoidType{})
	if sig.ReturnType != nil {
		var err error
		ret, err = c.resolveTypeExpr(sig.ReturnType)
		if err != nil {
			return nil, err
		}
	}
	return &FuncType{Params: ps, Return: ret}, nil
}

func (c *checker) lookupModuleMemberType(modPath, member string, span ast.Span) (Type, error) {
	intTy := NewUnboundedInt()
	switch modPath {
	case "std.socket":
		switch member {
		case "listen_tcp":
			return &FuncType{Return: c.instantiateADT("Result", []Type{c.info.Types["sock.TcpListener"], StrType{}})}, nil
		case "connect_tcp":
			return &FuncType{Return: c.instantiateADT("Result", []Type{c.info.Types["sock.TcpStream"], StrType{}})}, nil
		}
	case "std.requests":
		switch member {
		case "get", "post":
			return &FuncType{Return: c.instantiateADT("Result", []Type{c.info.Entities["HttpResponse"], StrType{}})}, nil
		case "Session":
			return &FuncType{Return: &HandleType{Name: "req.Session", Protocol: c.info.StdHandles["req.Session"]}}, nil
		case "gather":
			return &FuncType{Return: &ListType{Elem: c.instantiateADT("Result", []Type{c.info.Entities["HttpResponse"], StrType{}})}}, nil
		case "serve_once":
			return &FuncType{Return: c.instantiateADT("Result", []Type{intTy, StrType{}})}, nil
		}
	case "std.json":
		switch member {
		case "encode":
			return &FuncType{Return: StrType{}}, nil
		case "decode":
			return &FuncType{Return: c.instantiateADT("Result", []Type{UnknownType{}, StrType{}})}, nil
		}
	case "std.bytes":
		switch member {
		case "from_str", "from_hex":
			return &FuncType{Return: c.info.Types["bytes.ByteView"]}, nil
		}
	case "std.crypto":
		switch member {
		case "sha256", "hmac_sha256":
			return &FuncType{Return: StrType{}}, nil
		case "constant_time_eq":
			return &FuncType{Return: BoolType{}}, nil
		}
	case "std.fs":
		switch member {
		case "open":
			return &FuncType{Return: c.instantiateADT("Result", []Type{c.info.Types["fs.File"], StrType{}})}, nil
		case "read_text":
			return &FuncType{Return: c.instantiateADT("Result", []Type{StrType{}, StrType{}})}, nil
		case "write_atomic":
			return &FuncType{Return: c.instantiateADT("Result", []Type{intTy, StrType{}})}, nil
		}
	case "std.cli":
		switch member {
		case "args":
			return &FuncType{Return: &ListType{Elem: StrType{}}}, nil
		case "env_get":
			return &FuncType{Return: c.instantiateADT("Option", []Type{StrType{}})}, nil
		}
	case "std.time":
		switch member {
		case "now_ms":
			return &FuncType{Return: NewIntRange(0, math.MaxInt64, "")}, nil
		case "sleep_ms":
			return &FuncType{Return: VoidType{}}, nil
		}
	case "std.concurrent":
		return &FuncType{Return: UnknownType{}}, nil
	case "std.fp":
		return &FuncType{Return: UnknownType{}}, nil
	}
	return nil, fmt.Errorf("%s: module %s has no member %q", span, modPath, member)
}

func (c *checker) lookupHandleMethod(ht *HandleType, method string, span ast.Span) (Type, error) {
	switch ht.Name {
	case "sock.TcpListener":
		switch method {
		case "accept":
			return &FuncType{Return: c.instantiateADT("Result", []Type{c.info.Types["sock.TcpStream"], StrType{}})}, nil
		case "port":
			return &FuncType{Return: NewIntRange(1, 65535, "")}, nil
		case "close":
			return &FuncType{Return: VoidType{}}, nil
		}
	case "sock.TcpStream":
		switch method {
		case "send_text", "send_bytes":
			return &FuncType{Return: c.instantiateADT("Result", []Type{NewUnboundedInt(), StrType{}})}, nil
		case "recv_text":
			return &FuncType{Return: c.instantiateADT("Result", []Type{StrType{}, StrType{}})}, nil
		case "close":
			return &FuncType{Return: VoidType{}}, nil
		}
	case "fs.File":
		switch method {
		case "read_text":
			return &FuncType{Return: c.instantiateADT("Result", []Type{StrType{}, StrType{}})}, nil
		case "write_text":
			return &FuncType{Return: c.instantiateADT("Result", []Type{NewUnboundedInt(), StrType{}})}, nil
		case "close":
			return &FuncType{Return: VoidType{}}, nil
		}
	case "req.Session":
		switch method {
		case "get", "post":
			return &FuncType{Return: c.instantiateADT("Result", []Type{c.info.Entities["HttpResponse"], StrType{}})}, nil
		case "get_async":
			return &FuncType{Return: &HandleType{Name: "Future", Elem: c.instantiateADT("Result", []Type{c.info.Entities["HttpResponse"], StrType{}})}}, nil
		case "close":
			return &FuncType{Return: VoidType{}}, nil
		}
	case "conc.ThreadPool":
		switch method {
		case "submit":
			return &FuncType{Return: &HandleType{Name: "Future", Elem: UnknownType{}}}, nil
		case "map_parallel":
			return &FuncType{Return: &ListType{Elem: UnknownType{}}}, nil
		case "shutdown":
			return &FuncType{Return: VoidType{}}, nil
		}
	case "conc.Channel":
		elem := ht.Elem
		if elem == nil {
			elem = UnknownType{}
		}
		switch method {
		case "send":
			return &FuncType{Return: BoolType{}}, nil
		case "recv":
			return &FuncType{Return: c.instantiateADT("Option", []Type{elem})}, nil
		case "close":
			return &FuncType{Return: VoidType{}}, nil
		}
	case "conc.Mutex":
		switch method {
		case "get":
			return &FuncType{Return: ht.Elem}, nil
		case "set", "with_lock":
			return &FuncType{Return: VoidType{}}, nil
		}
		return &FuncType{Return: VoidType{}}, nil
	case "conc.Semaphore":
		return &FuncType{Return: VoidType{}}, nil
	case "Future":
		if method == "await" {
			return &FuncType{Return: ht.Elem}, nil
		}
	case "bytes.ByteView":
		switch method {
		case "len":
			return &FuncType{Return: NewIntRange(0, DefaultMaxInt, "")}, nil
		case "read_u8":
			return &FuncType{Return: NewIntRange(0, 255, "byte")}, nil
		case "read_u16_be":
			return &FuncType{Return: NewIntRange(0, 65535, "")}, nil
		case "read_u32_be":
			return &FuncType{Return: NewIntRange(0, math.MaxUint32, "")}, nil
		case "slice":
			return &FuncType{Return: ht}, nil
		}
	}
	return nil, fmt.Errorf("%s: handle %s has no method %q", span, ht.Name, method)
}

func isAssignable(expected, actual Type) bool {
	if expected == nil || actual == nil {
		return true
	}
	if expected.Kind() == KindUnknown || actual.Kind() == KindUnknown || expected.Kind() == KindTypeVar || actual.Kind() == KindTypeVar {
		return true
	}
	if expected.Kind() == KindInt && actual.Kind() == KindInt {
		return true // exact range checks are verified by AnimaSMT / SPARK WP!
	}
	if expected.Kind() == KindList && actual.Kind() == KindList {
		el := expected.(*ListType)
		al := actual.(*ListType)
		return isAssignable(el.Elem, al.Elem) && sameElemRange(el.Elem, al.Elem)
	}
	if expected.Kind() == KindMap && actual.Kind() == KindMap {
		em := expected.(*MapType)
		am := actual.(*MapType)
		return isAssignable(em.Key, am.Key) && isAssignable(em.Val, am.Val) && sameElemRange(em.Val, am.Val)
	}
	if ea, ok := expected.(*ADTType); ok {
		if aa, ok := actual.(*ADTType); ok && ea.Name == aa.Name {
			for i := 0; i < len(ea.TypeArgs) && i < len(aa.TypeArgs); i++ {
				if !isAssignable(ea.TypeArgs[i], aa.TypeArgs[i]) || !withinRange(ea.TypeArgs[i], aa.TypeArgs[i]) {
					return false
				}
			}
			return true
		}
	}
	return expected.Equals(actual)
}

// sameElemRange reports whether two element types of a list or map agree on
// the range of an int. A list is a reference: seen as a list of int[1..9]
// by one name and as a list of int by another, a write through the second
// breaks what the first relies on, so the two ranges have to be the same.
func sameElemRange(expected, actual Type) bool {
	e, ok := expected.(*IntType)
	a, ok2 := actual.(*IntType)
	if !ok || !ok2 {
		return true
	}
	if e.IsBounded != a.IsBounded {
		return false
	}
	return !e.IsBounded || (e.Lo == a.Lo && e.Hi == a.Hi)
}

// withinRange reports whether an int in a variant of type actual is one of
// type expected. A variant is not written after it is made, so a narrower
// range is accepted where a wider one is expected.
func withinRange(expected, actual Type) bool {
	e, ok := expected.(*IntType)
	a, ok2 := actual.(*IntType)
	if !ok || !ok2 || !e.IsBounded {
		return true
	}
	return a.IsBounded && e.Lo <= a.Lo && a.Hi <= e.Hi
}

// widenInt drops the range of an int that becomes the element of a list or
// the field of a variant without a declared type: the range sema infers for
// an expression is not one the kernel proves.
func widenInt(t Type) Type {
	if _, ok := t.(*IntType); ok {
		return NewUnboundedInt()
	}
	return t
}

// isMapStage reports whether e is a pipeline that ends in map(lambda): its
// value is a new list.
func isMapStage(e ast.Expr) bool {
	pe, ok := e.(*ast.PipeExpr)
	if !ok {
		return false
	}
	call, ok := pe.Right.(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return false
	}
	id, ok := call.Callee.(*ast.Ident)
	_, isLam := call.Args[0].Value.(*ast.LambdaExpr)
	return ok && id.Name == "map" && isLam
}

// fillUnknown is the type a variable of type prev has once a value of type
// val is assigned to it: prev, with what was not known yet taken from val.
// An unknown element type of a list or map does not become a bounded int,
// since the elements written so far were not proved in that range.
func fillUnknown(prev, val Type, inContainer bool) (Type, bool) {
	if prev == nil || prev.Kind() == KindUnknown {
		if inContainer && hasBoundedInt(val) {
			return prev, false
		}
		return val, true
	}
	switch p := prev.(type) {
	case *ListType:
		if v, ok := val.(*ListType); ok {
			elem, ok := fillUnknown(p.Elem, v.Elem, true)
			cp := *p
			cp.Elem = elem
			return &cp, ok
		}
	case *MapType:
		if v, ok := val.(*MapType); ok {
			vt, ok := fillUnknown(p.Val, v.Val, true)
			cp := *p
			cp.Val = vt
			return &cp, ok
		}
	case *ADTType:
		if v, ok := val.(*ADTType); ok && v.Name == p.Name && len(v.TypeArgs) == len(p.TypeArgs) {
			cp := *p
			cp.TypeArgs = make([]Type, len(p.TypeArgs))
			all := true
			for i := range p.TypeArgs {
				var ok bool
				cp.TypeArgs[i], ok = fillUnknown(p.TypeArgs[i], v.TypeArgs[i], inContainer)
				all = all && ok
			}
			return &cp, all
		}
	}
	return prev, true
}

// hasBoundedInt reports whether a bounded int appears in t.
func hasBoundedInt(t Type) bool {
	switch x := t.(type) {
	case *IntType:
		return x.IsBounded
	case *ListType:
		return hasBoundedInt(x.Elem)
	case *MapType:
		return hasBoundedInt(x.Val)
	case *ADTType:
		for _, a := range x.TypeArgs {
			if hasBoundedInt(a) {
				return true
			}
		}
	}
	return false
}

// keepsType reports whether a variable of type t keeps it when assigned
// again: the types whose parts have a range of their own.
func keepsType(t Type) bool {
	switch t.(type) {
	case *ListType, *MapType, *ADTType:
		return true
	}
	return false
}

// assignable is isAssignable for the value of expr. A list or map literal
// is a new value, so it takes the element type of where it goes: its type
// becomes expected, and the kernel proves each element in that range
// (ProgramInfo.LiteralTargets).
func (c *checker) assignable(expected, actual Type, expr ast.Expr) bool {
	if expected == nil || actual == nil {
		return true
	}
	switch lit := expr.(type) {
	case *ast.ListLit:
		el, ok := expected.(*ListType)
		if !ok {
			break
		}
		for _, x := range lit.Elems {
			if !c.assignable(el.Elem, c.info.ExprTypes[x], x) {
				return false
			}
		}
		c.info.ExprTypes[lit] = expected
		c.info.LiteralTargets[lit] = expected
		return true
	case *ast.MapLit:
		em, ok := expected.(*MapType)
		if !ok {
			break
		}
		for _, en := range lit.Entries {
			if !isAssignable(em.Key, c.info.ExprTypes[en.Key]) || !c.assignable(em.Val, c.info.ExprTypes[en.Value], en.Value) {
				return false
			}
		}
		c.info.ExprTypes[lit] = expected
		c.info.LiteralTargets[lit] = expected
		return true
	case *ast.MatchExpr:
		for _, arm := range lit.Arms {
			if !c.assignable(expected, c.info.ExprTypes[arm.Value], arm.Value) {
				return false
			}
		}
		if isAssignable(expected, actual) {
			return true
		}
		// Every arm took the expected type.
		if expected.Kind() == actual.Kind() {
			c.info.ExprTypes[lit] = expected
			return true
		}
		return false
	case *ast.PipeExpr:
		// The list a map stage makes: the kernel proves what the lambda
		// yields in the expected element range.
		el, ok := expected.(*ListType)
		al, ok2 := actual.(*ListType)
		if !ok || !ok2 || !isMapStage(lit) {
			break
		}
		ei, ok := el.Elem.(*IntType)
		ai, ok2 := al.Elem.(*IntType)
		if !ok || !ok2 || !ei.IsBounded || ai.IsBounded {
			break
		}
		c.info.ExprTypes[lit] = expected
		c.info.LiteralTargets[lit] = expected
		return true
	case *ast.CallExpr:
		// Some(x), Ok(x) and Err(x) make a new variant.
		id, ok := lit.Callee.(*ast.Ident)
		ea, ok2 := expected.(*ADTType)
		if !ok || !ok2 || len(lit.Args) != 1 {
			break
		}
		arg := -1
		switch {
		case id.Name == "Some" && ea.Name == "Option", id.Name == "Ok" && ea.Name == "Result":
			arg = 0
		case id.Name == "Err" && ea.Name == "Result":
			arg = 1
		}
		if arg < 0 || arg >= len(ea.TypeArgs) {
			break
		}
		if !c.assignable(ea.TypeArgs[arg], c.info.ExprTypes[lit.Args[0].Value], lit.Args[0].Value) {
			return false
		}
		c.info.ExprTypes[lit] = expected
		c.info.LiteralTargets[lit] = expected
		return true
	}
	return isAssignable(expected, actual)
}

func unifyTypes(a, b Type) Type {
	if a == nil || a.Kind() == KindUnknown {
		return b
	}
	if b == nil || b.Kind() == KindUnknown {
		return a
	}
	switch x := a.(type) {
	case *IntType:
		// The smallest range that holds the values of both.
		y, ok := b.(*IntType)
		if !ok {
			return a
		}
		if !x.IsBounded || !y.IsBounded {
			return NewUnboundedInt()
		}
		if x.Lo == y.Lo && x.Hi == y.Hi {
			return a
		}
		return NewIntRange(min(x.Lo, y.Lo), max(x.Hi, y.Hi), "")
	case *ListType:
		if y, ok := b.(*ListType); ok {
			cp := *x
			cp.Elem = unifyTypes(x.Elem, y.Elem)
			return &cp
		}
	case *MapType:
		if y, ok := b.(*MapType); ok {
			return &MapType{Key: unifyTypes(x.Key, y.Key), Val: unifyTypes(x.Val, y.Val)}
		}
	}
	if aa, ok := a.(*ADTType); ok {
		if ba, ok := b.(*ADTType); ok && aa.Name == ba.Name {
			cp := *aa
			maxL := len(aa.TypeArgs)
			if len(ba.TypeArgs) > maxL {
				maxL = len(ba.TypeArgs)
			}
			args := make([]Type, maxL)
			for i := 0; i < maxL; i++ {
				var at, bt Type = UnknownType{}, UnknownType{}
				if i < len(aa.TypeArgs) {
					at = aa.TypeArgs[i]
				}
				if i < len(ba.TypeArgs) {
					bt = ba.TypeArgs[i]
				}
				args[i] = unifyTypes(at, bt)
			}
			cp.TypeArgs = args
			return &cp
		}
	}
	return a
}

func (c *checker) addUnique(slice *[]string, val string) {
	for _, x := range *slice {
		if x == val {
			return
		}
	}
	*slice = append(*slice, val)
}
