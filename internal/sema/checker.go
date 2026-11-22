package sema

import (
	"fmt"
	"math"
	"slices"
	"strconv"
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
			LetRanges:      map[*ast.LetAssignStmt]*IntType{},
			TimeoutArgs:    map[*ast.CallExpr]ast.Expr{},
			ArgRanges:      map[*ast.CallExpr][]ArgRange{},
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
	callee      ast.Expr // the callee of the call being checked
	// `x |> o.f(a)`: the x each such call o.f(a) is given first. By call,
	// since an argument of a piped call may hold a piped call of its own.
	piped map[*ast.CallExpr]ast.Expr
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
	lam     *namedLambda // the lambda with parameters the name was given
}

// namedLambda is a lambda with parameters that was given a name. Nothing
// says what its parameters are where it is written, so its body is checked
// there with parameters of any type, and again at its first use with the
// types it is given: those are the types it takes from then on. It is only
// used by its name, called or given to a stage, so that no use goes
// unchecked.
type namedLambda struct {
	expr   *ast.LambdaExpr
	sc     *scope
	params []Type
	ret    Type
	fixed  bool
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
					"send_text": "Open",
					"recv_text": "Open",
					"close":     "Closed",
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
					"submit":   "Running",
					"shutdown": "Shutdown",
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

// once is the names declared so far in one place: the parameters of a
// function, the fields of an entity. Of two parameters of one name the VM
// bound the first and sema typed the last, and the native build failed.
type once struct {
	what, of string
	seen     map[string]bool
}

func newOnce(what, of string) *once { return &once{what: what, of: of, seen: map[string]bool{}} }

func (o *once) add(name string, span ast.Span) error {
	if o.seen[name] {
		return fmt.Errorf("%s: %s has two %s named %s: a name is declared once", span, o.of, o.what, name)
	}
	o.seen[name] = true
	return nil
}

// patternNames adds the names pat binds to seen.
func patternNames(pat ast.Pattern, seen *once) error {
	switch p := pat.(type) {
	case *ast.VarPat:
		return seen.add(p.Name, p.Span)
	case *ast.VariantPat:
		for _, f := range p.Fields {
			if err := patternNames(f, seen); err != nil {
				return err
			}
		}
	}
	return nil
}

// checkNames says a name is declared once. Each part of the toolchain looks
// a name up in its own way: sema took `len(xs)` for the built-in while both
// backends called the program's `def len`, and of an entity and a function
// of one name the function could never be called, unreported. So a name
// means one thing: what is called (a function, an entity,
// a variant, a built-in) shares one set of names, types share another, and
// so does each kind of model.
func (c *checker) checkNames() error {
	called := map[string]string{}
	for n := range builtinCallables {
		called[n] = "a built-in"
	}
	// A pipeline stage is the one built-in a function may be named like:
	// `xs |> take(2)` is then a call of that function, to sema, the
	// kernels and both backends.
	stage := func(name, what string) bool {
		return what == "a function" && called[name] == "a built-in" && !calledByName[name]
	}
	for n := range c.info.Variants {
		called[n] = "a built-in variant"
	}
	types := map[string]string{"list": "a built-in type", "map": "a built-in type", "Channel": "a built-in type", "Mutex": "a built-in type", "Future": "a built-in type"}
	for n := range c.info.Types {
		types[n] = "a built-in type"
	}
	kinds := map[string]map[string]string{}
	declare := func(in map[string]string, name, what string, span ast.Span) error {
		if was, ok := in[name]; ok && !stage(name, what) {
			return fmt.Errorf("%s: %s is declared as %s, and is already %s: a name is declared once", span, name, what, was)
		}
		in[name] = what
		return nil
	}
	model := func(kind, name string, span ast.Span) error {
		if kinds[kind] == nil {
			kinds[kind] = map[string]string{}
		}
		return declare(kinds[kind], name, "a "+kind, span)
	}
	params := func(of string, ps []ast.Param) error {
		seen := newOnce("parameters", of)
		for _, p := range ps {
			if err := seen.add(p.Name, p.Span); err != nil {
				return err
			}
		}
		return nil
	}
	// Of two states of one name the model kept the last, so a property
	// could be weakened by a second state the reader never reaches.
	states := func(of string, sts []ast.StateDecl) error {
		seen := newOnce("states", of)
		for _, st := range sts {
			if err := seen.add(st.Name, st.Span); err != nil {
				return err
			}
		}
		return nil
	}
	for _, d := range c.info.Program.Decls {
		var err error
		switch node := d.(type) {
		case *ast.FuncDecl:
			if err = declare(called, node.Name, "a function", node.Span); err == nil {
				err = params(node.Name, node.Params)
			}
		case *ast.EntityDecl:
			if err = declare(called, node.Name, "an entity", node.Span); err == nil {
				err = declare(types, node.Name, "an entity", node.Span)
			}
			seen := newOnce("fields", node.Name)
			for _, f := range node.Fields {
				if err == nil {
					err = seen.add(f.Name, f.Span)
				}
			}
			for _, rel := range node.Relations {
				if err == nil {
					err = seen.add(rel.Name, rel.Span)
				}
			}
		case *ast.TypeDecl:
			err = declare(types, node.Name, "a type", node.Span)
			for _, v := range node.Variants {
				if err == nil {
					err = declare(called, v.Name, "a variant of "+node.Name, v.Span)
				}
				seen := newOnce("fields", v.Name)
				for _, f := range v.Fields {
					if err == nil {
						err = seen.add(f.Name, f.Span)
					}
				}
			}
		case *ast.PortDecl:
			err = declare(types, node.Name, "a port", node.Span)
			if err == nil {
				err = states(node.Name, node.States)
			}
			seen := newOnce("extern functions", node.Name)
			for _, x := range node.Externs {
				if err == nil {
					err = seen.add(x.Name, x.Span)
				}
				if err == nil {
					err = params(node.Name+"."+x.Name, x.Params)
				}
			}
		case *ast.MachineDecl:
			if err = model("machine", node.Name, node.Span); err == nil {
				err = states(node.Name, node.States)
			}
			seen := newOnce("control variables", node.Name)
			for _, cv := range node.ControlVars {
				if err == nil {
					err = seen.add(cv.Name, cv.Span)
				}
			}
		case *ast.PropertyDecl:
			if err = model("property", node.Name, node.Span); err == nil {
				err = states(node.Name, node.States)
			}
		case *ast.ProgressDecl:
			err = model("progress", node.Name, node.Span)
		case *ast.WorkflowDecl:
			if err = model("workflow", node.Name, node.Span); err == nil {
				err = params(node.Name, node.Params)
			}
			pools := newOnce("pools", node.Name)
			for _, pl := range node.Pools {
				if err == nil {
					err = pools.add(pl.Name, pl.Span)
				}
			}
			// Both backends ran the last of two nodes of one name.
			seen := newOnce("nodes", node.Name)
			for _, n := range node.Nodes {
				name, branches := "", []ast.ForkBranch(nil)
				switch n := n.(type) {
				case *ast.StepNode:
					name = n.Name
				case *ast.ChoiceNode:
					name = n.Name
				case *ast.MergeNode:
					name = n.Name
				case *ast.ForkNode:
					name, branches = n.Name, n.Branches
				case *ast.JoinNode:
					name = n.Name
				}
				if err == nil && name != "" {
					err = seen.add(name, n.GetSpan())
				}
				inFork := newOnce("branches", name)
				for _, br := range branches {
					if err == nil {
						err = inFork.add(br.Name, br.Span)
					}
				}
			}
		case *ast.SystemDecl:
			err = model("system", node.Name, node.Span)
			seen := newOnce("parts", node.Name)
			for _, in := range node.Instances {
				if err == nil {
					err = seen.add(in.Name, in.Span)
				}
			}
		}
		if err != nil {
			return err
		}
	}
	return nil
}

func (c *checker) checkProgram() error {
	prog := c.info.Program
	if err := c.checkNames(); err != nil {
		return err
	}

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
			// A relation is a field that holds the entities it names: one,
			// one or none, or a list of them.
			for _, rel := range node.Relations {
				target, ok := c.info.Entities[rel.Target]
				if !ok {
					return fmt.Errorf("%s: relation %s targets unknown entity %q", rel.Span, rel.Name, rel.Target)
				}
				lo, hi, err := relationBounds(rel)
				if err != nil {
					return err
				}
				var ft Type = &ListType{Elem: target}
				switch {
				case lo == 1 && hi == 1:
					ft = target
				case lo == 0 && hi == 1:
					ft = c.instantiateADT("Option", []Type{target})
				}
				et.Fields = append(et.Fields, EntityFieldInfo{Name: rel.Name, Type: ft})
				et.FieldMap[rel.Name] = ft
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
						return fmt.Errorf("%s: 'own' parameter %s must be a linear handle (sock.TcpStream, sock.TcpListener, fs.File, conc.ThreadPool), got %s", p.Span, p.Name, pt)
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
			// `Option` on its own is an Option of anything: what it holds
			// is of unknown type.
			if adt, ok := ty.(*ADTType); ok && len(adt.TypeParams) > 0 && len(adt.TypeArgs) == 0 {
				cp := *adt
				for range adt.TypeParams {
					cp.TypeArgs = append(cp.TypeArgs, UnknownType{})
				}
				return &cp, nil
			}
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
				// `Option` on its own is an Option of anything: what it
				// holds is of unknown type.
				for len(args) < len(adt.TypeParams) {
					args = append(args, UnknownType{})
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
		if !boolLike(ty) {
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
		if !boolLike(ty) {
			return fmt.Errorf("%s: requires clause must be bool, got %s", req.GetSpan(), ty)
		}
	}
	if fn.Decreases != nil {
		ty, err := c.checkExpr(fn.Decreases, sc)
		if err != nil {
			return err
		}
		if !intLike(ty) {
			return fmt.Errorf("%s: decreases expression must be int, got %s", fn.Decreases.GetSpan(), ty)
		}
	}
	for _, st := range fn.Body {
		if err := c.checkStmt(st, sc); err != nil {
			return err
		}
	}
	if ret := fi.Type.Return; ret != nil && ret.Kind() != KindVoid && !alwaysReturns(fn.Body) {
		return fmt.Errorf("%s: function %s can end without a return, and it returns %s", fn.Span, fn.Name, ret)
	}
	// Check ensures with result & old()
	ensScope := newScope(sc)
	ensScope.defineLocal("result", varBinding{ty: fi.Type.Return, span: fn.Span})
	for _, ens := range fn.Ensures {
		ty, err := c.checkExpr(ens, ensScope)
		if err != nil {
			return err
		}
		if !boolLike(ty) {
			return fmt.Errorf("%s: ensures clause must be bool, got %s", ens.GetSpan(), ty)
		}
	}
	return nil
}

// alwaysReturns reports whether every way through the statements ends in a
// return. A function that returns a value must: one that ends without a
// return gives (), which is of no type, and its caller is told the declared
// one. A match counts when each arm returns, the kernel proving that some arm
// is taken; a loop counts only as `while True`, which nothing leaves but a
// return.
func alwaysReturns(body []ast.Stmt) bool {
	for _, st := range body {
		switch s := st.(type) {
		case *ast.ReturnStmt:
			return true
		case *ast.IfStmt:
			if s.Else == nil || !alwaysReturns(s.Else) {
				continue
			}
			all := true
			for _, br := range s.Branches {
				all = all && alwaysReturns(br.Body)
			}
			if all {
				return true
			}
		case *ast.MatchStmt:
			all := len(s.Arms) > 0
			for _, arm := range s.Arms {
				all = all && alwaysReturns(arm.Body)
			}
			if all {
				return true
			}
		case *ast.WhileStmt:
			if lit, ok := s.Cond.(*ast.BoolLit); ok && lit.Value {
				return true
			}
		}
	}
	return false
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
			if !boolLike(ty) {
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
				if !boolLike(gty) {
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
	starts := 0
	for _, n := range wf.Nodes {
		switch node := n.(type) {
		case *ast.StartNode:
			// A workflow starts in one place: the backends would run the
			// last start and never the others.
			if starts++; starts > 1 {
				return fmt.Errorf("%s: workflow %s has more than one start", node.Span, wf.Name)
			}
			for _, st := range node.Body {
				if err := c.checkStmt(st, sc); err != nil {
					return err
				}
			}
		case *ast.ForkNode:
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
						// What a branch binds is a variable of the workflow
						// after the join.
						if la, ok := op.Stmt.(*ast.LetAssignStmt); ok {
							if b, exists := brSc.vars[la.Name]; exists {
								sc.defineLocal(la.Name, b)
							}
						}
					}
				}
			}
			if err := checkForkBranches(node); err != nil {
				return err
			}
		case *ast.ChoiceNode:
			for _, br := range node.Branches {
				if br.Guard != nil {
					ty, err := c.checkExpr(br.Guard, sc)
					if err != nil {
						return err
					}
					if !boolLike(ty) {
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
	return checkWorkflowAssigned(wf)
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
		prevLam, isLam := sc.lookup(s.Name)
		if isLam && prevLam.lam != nil {
			return fmt.Errorf("%s: %s names a lambda and is not assigned again", s.Span, s.Name)
		}
		if lam, ok := s.Value.(*ast.LambdaExpr); ok && len(lam.Params) > 0 && s.TypeAnno == nil {
			if isLam {
				return fmt.Errorf("%s: %s is a %s: a lambda with parameters is given a name of its own", s.Span, s.Name, prevLam.ty)
			}
			types := make([]Type, len(lam.Params))
			for i := range types {
				types[i] = UnknownType{Generic: true}
			}
			ft, err := c.checkLambdaWith(lam, sc, types)
			if err != nil {
				return err
			}
			if c.curFuncInfo != nil {
				c.addUnique(&c.curFuncInfo.Frame.Writes, s.Name)
			}
			sc.set(s.Name, varBinding{ty: ft, mutable: true, span: s.Span, lam: &namedLambda{expr: lam, sc: sc}})
			return nil
		}
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
			// And its range, which the kernel takes the variable to be in
			// wherever it is read.
			if prev, found := sc.lookup(s.Name); found && !sameRange(prev.ty, annoTy) {
				return fmt.Errorf("%s: %s is a %s and cannot be declared again as a %s: a variable keeps its range", s.Span, s.Name, prev.ty, annoTy)
			}
			if rng := rangeOf(annoTy); rng != nil {
				c.info.LetRanges[s] = rng
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
			// A part of its type that no value has typed stays so: a read
			// placed before this assignment and run after it, in a loop,
			// took the variable for a value of any type there.
			if !sameWhole(target, prev.ty) {
				return fmt.Errorf("%s: cannot assign %s to %s (%s), which does not say the type of all it holds: declare the type of %s where it is first assigned", s.Span, valTy, s.Name, prev.ty, s.Name)
			}
			if !c.assignable(target, valTy, s.Value) {
				return fmt.Errorf("%s: cannot assign %s to %s (%s): a variable keeps the type of its elements", s.Span, valTy, s.Name, target)
			}
			valTy = target
		} else if _, isInt := valTy.(*IntType); isInt {
			// The value of an int variable is the kernel's to work out;
			// its type holds across every later assignment, and the kernel
			// proves each value in the range, when the variable has one.
			valTy = NewUnboundedInt()
			if prev, found := sc.lookup(s.Name); found {
				if rng := rangeOf(prev.ty); rng != nil {
					valTy = prev.ty
					c.info.LetRanges[s] = rng
				}
			}
		}
		// `_` is where a future is left to its pool: it takes one of any
		// type, so what its future gives has none. Nothing is written
		// through a future; a channel or a mutex keeps its type under `_`.
		if ht, ok := valTy.(*HandleType); ok && s.Name == "_" && ht.Name == "Future" && ht.Elem != nil {
			cp := *ht
			cp.Elem = UnknownType{}
			valTy = &cp
		}
		if err := keepsSort(sc, s.Name, valTy, s.Span); err != nil {
			return err
		}
		if err := wholeSlots(s.Name, valTy, s.Span); err != nil {
			return err
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
		if lhsTy.Kind() != KindInt || (!intLike(rhsTy)) {
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
			if !boolLike(cty) {
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
			if err := patternNames(arm.Pattern, newOnce("bindings", "a pattern")); err != nil {
				return err
			}
			if err := c.bindPattern(arm.Pattern, sty, armSc); err != nil {
				return err
			}
			if arm.Guard != nil {
				gty, err := c.checkExpr(arm.Guard, armSc)
				if err != nil {
					return err
				}
				if !boolLike(gty) {
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
			if err := keepsElements(sc, s.Var, NewUnboundedInt(), s.Span); err != nil {
				return err
			}
			sub.defineLocal(s.Var, varBinding{ty: NewUnboundedInt(), span: s.Span})
		} else {
			ity, err := c.checkExpr(s.Iterable, sc)
			if err != nil {
				return err
			}
			var elem Type = UnknownType{Generic: generic(ity)}
			if lt, ok := ity.(*ListType); ok {
				elem = lt.Elem
			} else if opaque(ity) {
				return unknownUse(s.Iterable.GetSpan(), "for over")
			}
			if err := keepsElements(sc, s.Var, elem, s.Span); err != nil {
				return err
			}
			if err := wholeSlots(s.Var, elem, s.Span); err != nil {
				return err
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
		if !boolLike(cty) {
			return fmt.Errorf("%s: while condition must be bool", s.Cond.GetSpan())
		}
		for _, inv := range s.Invariants {
			ity, err := c.checkExpr(inv, sc)
			if err != nil {
				return err
			}
			if !boolLike(ity) {
				return fmt.Errorf("%s: loop invariant must be bool", inv.GetSpan())
			}
		}
		if s.Decreases != nil {
			dty, err := c.checkExpr(s.Decreases, sc)
			if err != nil {
				return err
			}
			if !intLike(dty) {
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
			if c.curReturn != nil && c.curReturn.Kind() != KindVoid {
				return fmt.Errorf("%s: return needs a value of type %s", s.Span, c.curReturn)
			}
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
	// A pattern of another type than a subject whose type is known never
	// matches: it is a mistake, not an arm.
	fits := func(span ast.Span, what string, kind TypeKind) error {
		if subjTy == nil {
			return nil
		}
		switch k := subjTy.Kind(); k {
		case KindInt, KindBool, KindStr, KindList, KindMap, KindEntity, KindADT:
			if k != kind {
				return fmt.Errorf("%s: %s pattern cannot match a value of type %s", span, what, subjTy)
			}
		}
		return nil
	}
	switch p := pat.(type) {
	case *ast.WildcardPat:
		return nil
	case *ast.IntPat:
		return fits(p.Span, "an int", KindInt)
	case *ast.RangePat:
		return fits(p.Span, "an int range", KindInt)
	case *ast.BoolPat:
		return fits(p.Span, "a bool", KindBool)
	case *ast.StrPat:
		return fits(p.Span, "a string", KindStr)
	case *ast.VarPat:
		if err := keepsElements(sc, p.Name, subjTy, p.Span); err != nil {
			return err
		}
		if err := wholeSlots(p.Name, subjTy, p.Span); err != nil {
			return err
		}
		sc.defineLocal(p.Name, varBinding{ty: subjTy, span: p.Span})
		return nil
	case *ast.VariantPat:
		if err := fits(p.Span, "a variant", KindADT); err != nil {
			return err
		}
		adt, ok := c.info.Variants[p.Name]
		if !ok {
			if subjADT, isADT := subjTy.(*ADTType); isADT {
				adt = subjADT
			} else {
				return fmt.Errorf("%s: unknown ADT variant %q", p.Span, p.Name)
			}
		}
		if subjADT, isADT := subjTy.(*ADTType); isADT && subjADT.Name != adt.Name {
			return fmt.Errorf("%s: variant %s of %s cannot match a value of type %s", p.Span, p.Name, adt.Name, subjTy)
		}
		vi, ok := adt.VariantMap[p.Name]
		if !ok {
			return fmt.Errorf("%s: variant %q not in ADT %s", p.Span, p.Name, adt.Name)
		}
		if len(p.Fields) != len(vi.Fields) {
			return fmt.Errorf("%s: variant %s has %d field(s), pattern has %d", p.Span, p.Name, len(vi.Fields), len(p.Fields))
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
				// What a variant with no type argument holds is of
				// unknown type.
				fty = UnknownType{}
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
		return c.instantiateADT("Option", []Type{UnknownType{Empty: true}}), nil
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
			if b.lam != nil {
				return nil, fmt.Errorf("%s: %s is a lambda with parameters and is used by its name only: call it, or give it to a pipeline stage", e.Span, e.Name)
			}
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
		if _, ok := c.info.Funcs[e.Name]; ok {
			// Neither backend has a value for a function that is not called.
			return nil, fmt.Errorf("%s: function %s is not a value: call it, or write a lambda such as `(v) => %s(v)`", e.Span, e.Name, e.Name)
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
			if !boolLike(ity) {
				return nil, fmt.Errorf("%s: not needs a bool, got %s", e.Span, ity)
			}
			return BoolType{}, nil
		}
		// Both backends negate whatever they are given as if it were an int.
		if !intLike(ity) {
			return nil, fmt.Errorf("%s: %s needs an int, got %s", e.Span, e.Op, ity)
		}
		if it, ok := ity.(*IntType); ok {
			// The least int has no negation: its range is not turned around.
			if e.Op == "-" && it.IsBounded && it.Lo != math.MinInt64 {
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
			if (!intLike(lt)) || (!intLike(rt)) {
				return nil, fmt.Errorf("%s: arithmetic %s requires int, got %s and %s", e.Span, e.Op, lt, rt)
			}
			return NewUnboundedInt(), nil
		case "&", "|", "^", "<<", ">>":
			if (!intLike(lt)) || (!intLike(rt)) {
				return nil, fmt.Errorf("%s: %s works on the bits of two ints, got %s and %s", e.Span, e.Op, lt, rt)
			}
			return NewUnboundedInt(), nil
		case "==", "!=", "<", "<=", ">", ">=", "and", "or", "implies", "in":
			if err := checkComparison(e, lt, rt); err != nil {
				return nil, err
			}
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
		var elem Type = UnknownType{Empty: true}
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
		var kt, vt Type = StrType{}, UnknownType{Empty: true}
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
			if i == 0 {
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
		// The result is typed as the base, so the base is an entity: both
		// backends give an object of the fields alone for anything else.
		et, ok := baseTy.(*EntityType)
		if !ok && generic(baseTy) {
			// A parameter of a named lambda has no type where the lambda is
			// written: the body is checked again with those of its first use.
			for _, f := range e.Fields {
				if _, err := c.checkExpr(f.Value, sc); err != nil {
					return nil, err
				}
			}
			return baseTy, nil
		}
		if !ok {
			return nil, fmt.Errorf("%s: 'with' copies an entity with some fields replaced, got %s", e.Span, baseTy)
		}
		given := map[string]bool{}
		for _, f := range e.Fields {
			vt, err := c.checkExpr(f.Value, sc)
			if err != nil {
				return nil, err
			}
			ft, exists := et.FieldMap[f.Name]
			if !exists {
				return nil, fmt.Errorf("%s: entity %s has no field %q in with-update", e.Span, et.Name, f.Name)
			}
			if given[f.Name] {
				return nil, fmt.Errorf("%s: field %s.%s is given twice", e.Span, et.Name, f.Name)
			}
			given[f.Name] = true
			if !c.assignable(ft, vt, f.Value) {
				return nil, fmt.Errorf("%s: field %s.%s expects %s, got %s", e.Span, et.Name, f.Name, ft, vt)
			}
		}
		return baseTy, nil

	case *ast.FieldExpr:
		// A function of a standard module or a method of a standard handle
		// is only there to be called: neither backend has it as a value.
		called := c.callee == ast.Expr(e)
		c.callee = nil
		objTy, err := c.checkExpr(e.Object, sc)
		if err != nil {
			return nil, err
		}
		if mt, ok := objTy.(*ModuleType); ok {
			if c.curFuncInfo != nil {
				c.addUnique(&c.curFuncInfo.Frame.PortEffects, mt.Path+"."+e.Field)
			}
			if !called {
				return nil, fmt.Errorf("%s: %s.%s is not a value: call it, or write a lambda that does", e.Span, mt.Path, e.Field)
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
			return nil, fmt.Errorf("%s: entity %s has no field %q", e.Span, et.Name, e.Field)
		}
		if ht, ok := objTy.(*HandleType); ok {
			if !called {
				return nil, fmt.Errorf("%s: %s() of a %s is not a value: call it, or write a lambda that does", e.Span, e.Field, ht.Name)
			}
			return c.lookupHandleMethod(ht, e.Field, e.Span)
		}
		if objTy.Kind() == KindList && e.Field == "len" {
			return &FuncType{Return: NewIntRange(0, DefaultMaxInt, "")}, nil
		}
		if objTy.Kind() == KindStr && e.Field == "len" {
			return &FuncType{Return: NewIntRange(0, DefaultMaxInt, "")}, nil
		}
		// A value of a type that is known has no other member: the VM
		// stops on one and the native backend gives `()`.
		switch objTy.Kind() {
		case KindADT:
			return nil, fmt.Errorf("%s: a value of type %s has no member %q; match on it to reach what it holds", e.Span, objTy, e.Field)
		case KindInt, KindBool, KindStr, KindList, KindMap:
			return nil, fmt.Errorf("%s: a value of type %s has no member %q", e.Span, objTy, e.Field)
		}
		if opaque(objTy) {
			return nil, unknownUse(e.Span, fmt.Sprintf("member %q of", e.Field))
		}
		return UnknownType{Generic: generic(objTy)}, nil

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
			if !intLike(ity) {
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
		if generic(lty) {
			return lty, nil
		}
		if opaque(lty) {
			return nil, unknownUse(e.Span, "an index into")
		}
		return nil, fmt.Errorf("%s: a value of type %s is not indexed", e.Span, lty)

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
		if generic(innerTy) {
			return innerTy, nil
		}
		return nil, fmt.Errorf("%s: ? takes a Result or an Option, got %s", e.Span, innerTy)

	case *ast.MatchExpr:
		sty, err := c.checkExpr(e.Subject, sc)
		if err != nil {
			return nil, err
		}
		var resTy Type = UnknownType{Empty: true}
		for _, arm := range e.Arms {
			armSc := newScope(sc)
			if err := patternNames(arm.Pattern, newOnce("bindings", "a pattern")); err != nil {
				return nil, err
			}
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
			// Both backends give a workflow its arguments in the order
			// they are written, whatever they are named.
			if arg.Name != "" && arg.Name != wi.Params[i].Name {
				return nil, fmt.Errorf("%s: parameter %d of workflow %s is %s, not %s: the arguments of a workflow are given in order", arg.Span, i+1, e.Name, wi.Params[i].Name, arg.Name)
			}
			if wi.Params[i].Mut && !arg.Mut {
				return nil, fmt.Errorf("%s: argument %d to workflow %s must be marked 'mut'", arg.Span, i+1, e.Name)
			}
			if arg.Own {
				return nil, fmt.Errorf("%s: unexpected 'own': a workflow cannot take ownership of a handle", arg.Span)
			}
			if !c.assignable(wi.Params[i].Type, at, arg.Value) {
				return nil, fmt.Errorf("%s: workflow %s arg %d expects %s, got %s", arg.Span, e.Name, i+1, wi.Params[i].Type, at)
			}
		}
		if err := c.checkCallAliasing(e.Args, true); err != nil {
			return nil, err
		}
		return wi.Return, nil

	case *ast.LambdaExpr:
		// When checked standalone without pipe context, infer params as Unknown
		types := make([]Type, len(e.Params))
		for i := range types {
			types[i] = UnknownType{}
		}
		return c.checkLambdaWith(e, sc, types)

	case *ast.PipeExpr:
		return c.checkPipeExpr(e, sc)

	case *ast.CallExpr:
		return c.checkCallExpr(e, sc)
	}
	return UnknownType{}, nil
}

// builtinCallables are the names that mean something of their own when
// called, to sema and to the kernels.
var builtinCallables = map[string]bool{
	"len": true, "print": true, "assert": true, "str": true, "to_str": true,
	"abs": true, "min": true, "max": true, "Some": true, "Ok": true, "Err": true,
	"filter": true, "map": true, "flat_map": true, "fold": true, "sum": true,
	"any": true, "all": true, "find": true, "take": true, "drop": true,
	"filter_ok": true, "unwrap_or": true, "and_then": true,
}

// calledByName are the built-ins that are called as `name(...)` and not as
// a pipeline stage. No function of the program has one of these names.
var calledByName = map[string]bool{
	"len": true, "print": true, "assert": true, "str": true, "to_str": true,
	"abs": true, "min": true, "max": true, "Some": true, "Ok": true, "Err": true,
}

// checkCalleeNotShadowed rejects a call by a name that is a variable and a
// function at once. Both backends call the variable; sema and the kernels
// would check the function.
// knownType is false for a type sema could not work out: nothing is said
// about such an operand.
// generic reports whether t is the type of a parameter of a named lambda
// where the lambda is written.
func generic(t Type) bool {
	u, ok := t.(UnknownType)
	return ok && u.Generic
}

// opaque reports whether t is the type of a value sema cannot tell the type
// of: nothing is done with it but passing it on.
func opaque(t Type) bool {
	u, ok := t.(UnknownType)
	return ok && !u.Generic
}

// vacuous reports whether t is the type argument that no value has.
func vacuous(t Type) bool {
	u, ok := t.(UnknownType)
	return ok && u.Empty
}

// untyped reports whether t is the type of a value that is only passed on:
// one of unknown type, or what a function with no return type gives.
func untyped(t Type) bool {
	return t != nil && (t.Kind() == KindVoid || (opaque(t) && !vacuous(t)))
}

// untypedName names such a value in an error.
func untypedName(t Type) string {
	if t.Kind() == KindVoid {
		return "what a function with no return type gives"
	}
	return "a value of unknown type"
}

func intLike(t Type) bool  { return t != nil && (t.Kind() == KindInt || generic(t)) }
func boolLike(t Type) bool { return t != nil && (t.Kind() == KindBool || generic(t)) }

// unknownUse is the error for doing op with a value of unknown type.
func unknownUse(span ast.Span, op string) error {
	return fmt.Errorf("%s: %s a value of unknown type: sema cannot tell what it is, so it is only passed on, printed or matched; give the value a type where it is made", span, op)
}

func knownType(t Type) bool {
	if t == nil {
		return false
	}
	switch t.Kind() {
	case KindUnknown, KindTypeVar, KindVoid:
		return false
	}
	return true
}

// sameSort says whether a value of type a can be equal to one of type b:
// the same kind, and for entities and variant types the same declaration.
func sameSort(a, b Type) bool {
	if !knownType(a) || !knownType(b) {
		return true
	}
	if a.Kind() != b.Kind() {
		return false
	}
	switch x := a.(type) {
	case *EntityType:
		y, ok := b.(*EntityType)
		return !ok || x.Name == y.Name
	case *ADTType:
		y, ok := b.(*ADTType)
		return !ok || x.Name == y.Name
	}
	return true
}

// keepsSort refuses to give the variable name, when there is one in scope, a
// value of another sort than it has: an assignment, a loop variable and a
// name in a pattern all write the one variable, and what it holds after an
// if, a loop or a match is read with one type, whichever branch ran.
func keepsSort(sc *scope, name string, ty Type, span ast.Span) error {
	prev, found := sc.lookup(name)
	if !found {
		return nil
	}
	if !sameSort(prev.ty, ty) {
		return fmt.Errorf("%s: %s is a %s and cannot be given a %s: a variable keeps its sort", span, name, prev.ty, ty)
	}
	// A handle is read as a handle of what its variable holds, whichever
	// path gave it, and a lambda that names the variable keeps the handle it
	// had: the variable keeps the type of what its handle holds.
	if _, ok := prev.ty.(*HandleType); ok && knownType(ty) && !(isAssignable(prev.ty, ty) && isAssignable(ty, prev.ty)) {
		return fmt.Errorf("%s: %s is a %s and cannot be given a %s: a variable keeps the type of what its handle holds", span, name, prev.ty, ty)
	}
	// A part of its type that no value has typed is any type where the
	// variable is read: it is not given a value that has one there.
	if hasGap(prev.ty) && knownType(ty) && !sameWhole(prev.ty, ty) {
		return fmt.Errorf("%s: %s is a %s, which does not say the type of all it holds, and cannot be given a %s: declare the type of %s where it is first assigned", span, name, prev.ty, ty, name)
	}
	// Nor is it of a type on one path and of none on another.
	switch {
	case knownType(prev.ty) && untyped(ty):
		return fmt.Errorf("%s: %s is a %s and cannot be given %s: a variable keeps its sort", span, name, prev.ty, untypedName(ty))
	case untyped(prev.ty) && knownType(ty):
		return fmt.Errorf("%s: %s holds %s and cannot be given a %s: a variable keeps its sort", span, name, untypedName(prev.ty), ty)
	}
	return nil
}

// keepsElements is keepsSort for a loop variable and a name in a pattern,
// which take the type of what they are bound to: a list, a map or a variant
// already in scope under that name must have that very type, as the kernel
// reads the range of its elements from the type the variable has afterwards.
func keepsElements(sc *scope, name string, ty Type, span ast.Span) error {
	if err := keepsSort(sc, name, ty, span); err != nil {
		return err
	}
	if prev, found := sc.lookup(name); found && keepsType(prev.ty) && knownType(ty) && !(isAssignable(prev.ty, ty) && isAssignable(ty, prev.ty)) {
		return fmt.Errorf("%s: %s is a %s and cannot be given a %s: a variable keeps the type of its elements", span, name, prev.ty, ty)
	}
	// Nothing proves what a loop or a pattern binds in a range it does not
	// have, so the value must come with the very range of the variable.
	if prev, found := sc.lookup(name); found && rangeOf(prev.ty) != nil && !sameRange(prev.ty, ty) {
		return fmt.Errorf("%s: %s is a %s and cannot be given a %s: a variable keeps its range", span, name, prev.ty, ty)
	}
	return nil
}

// rangeOf is t when it is an int with a range, nil otherwise.
func rangeOf(t Type) *IntType {
	if it, ok := t.(*IntType); ok && it.IsBounded {
		return it
	}
	return nil
}

// sameRange reports whether a variable of type a may be written as one of
// type b: two ints must have the one range, or neither a range. The kernel
// takes a variable with a range to be in it wherever it is read, which
// holds as long as every value it is given is proved in that range.
func sameRange(a, b Type) bool {
	ai, aInt := a.(*IntType)
	if !aInt {
		return true
	}
	bi, bInt := b.(*IntType)
	if !bInt {
		return !ai.IsBounded
	}
	if ai.IsBounded != bi.IsBounded {
		return false
	}
	return !ai.IsBounded || (ai.Lo == bi.Lo && ai.Hi == bi.Hi)
}

// checkComparison checks the operands of a comparison or a logical operator.
// Both backends run any of them on any two values, and do not agree on the
// answer when the operands are not what the operator is for.
func checkComparison(e *ast.BinaryExpr, lt, rt Type) error {
	if opaque(rt) || (opaque(lt) && e.Op != "in") {
		return unknownUse(e.Span, e.Op+" on")
	}
	switch e.Op {
	case "==", "!=":
		if !sameSort(lt, rt) {
			return fmt.Errorf("%s: %s between %s and %s: they are never equal", e.Span, e.Op, lt, rt)
		}
	case "<", "<=", ">", ">=":
		for _, t := range []Type{lt, rt} {
			if knownType(t) && t.Kind() != KindInt && t.Kind() != KindStr {
				return fmt.Errorf("%s: %s orders integers or strings, got %s", e.Span, e.Op, t)
			}
		}
		if !sameSort(lt, rt) {
			return fmt.Errorf("%s: %s between %s and %s: both sides must be integers, or both strings", e.Span, e.Op, lt, rt)
		}
	case "and", "or", "implies":
		for _, t := range []Type{lt, rt} {
			if knownType(t) && t.Kind() != KindBool {
				return fmt.Errorf("%s: %s needs a bool on both sides, got %s", e.Span, e.Op, t)
			}
		}
	case "in":
		if !knownType(rt) {
			return nil
		}
		var of Type
		switch r := rt.(type) {
		case *ListType:
			of = r.Elem
		case *MapType:
			of = r.Key
		case StrType:
			of = rt
		default:
			return fmt.Errorf("%s: in looks into a list, a map or a string, got %s", e.Span, rt)
		}
		if !sameSort(lt, of) {
			return fmt.Errorf("%s: in looks for %s in %s, which holds %s", e.Span, lt, rt, of)
		}
	}
	return nil
}

func (c *checker) checkCalleeNotShadowed(name string, span ast.Span, sc *scope) error {
	if _, local := sc.lookup(name); !local {
		return nil
	}
	if _, fn := c.info.Funcs[name]; fn || builtinCallables[name] {
		return fmt.Errorf("%s: %s is called here, and is both a variable and a function: rename the variable", span, name)
	}
	return nil
}

func (c *checker) checkCallExpr(e *ast.CallExpr, sc *scope) (Type, error) {
	// SPARK Anti-Aliasing rule on all call sites
	if err := c.checkCallAliasing(e.Args, false); err != nil {
		return nil, err
	}
	if id, ok := e.Callee.(*ast.Ident); ok {
		if err := c.checkCalleeNotShadowed(id.Name, id.Span, sc); err != nil {
			return nil, err
		}
	}

	// Check special built-in functions first
	if id, ok := e.Callee.(*ast.Ident); ok {
		switch id.Name {
		case "len":
			if len(e.Args) != 1 {
				return nil, fmt.Errorf("%s: len() takes 1 argument", e.Span)
			}
			at, err := c.checkExpr(e.Args[0].Value, sc)
			if err != nil {
				return nil, err
			}
			switch at.Kind() {
			case KindList, KindMap, KindStr:
			default:
				if generic(at) {
					break
				}
				return nil, fmt.Errorf("%s: len() takes a list, a map or a string, got %s", e.Args[0].Value.GetSpan(), at)
			}
			return NewIntRange(0, DefaultMaxInt, ""), nil
		case "print":
			for _, a := range e.Args {
				if _, err := c.checkExpr(a.Value, sc); err != nil {
					return nil, err
				}
			}
			return VoidType{}, nil
		case "assert":
			// assert(condition) or assert(condition, message).
			if len(e.Args) == 2 {
				return VoidType{}, c.checkBuiltinArgs(e, sc, KindBool, KindStr)
			}
			return VoidType{}, c.checkBuiltinArgs(e, sc, KindBool)
		case "str", "to_str":
			return StrType{}, c.checkBuiltinArgs(e, sc, KindUnknown)
		case "abs":
			return NewUnboundedInt(), c.checkBuiltinArgs(e, sc, KindInt)
		case "min", "max":
			return NewUnboundedInt(), c.checkBuiltinArgs(e, sc, KindInt, KindInt)
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
			return c.instantiateADT("Result", []Type{widenInt(vt), UnknownType{Empty: true}}), nil
		case "Err":
			if len(e.Args) != 1 {
				return nil, fmt.Errorf("%s: Err() expects 1 argument", e.Span)
			}
			et, err := c.checkExpr(e.Args[0].Value, sc)
			if err != nil {
				return nil, err
			}
			return c.instantiateADT("Result", []Type{UnknownType{Empty: true}, widenInt(et)}), nil
		}

		// Entity constructor: Account(balance=10, frozen=0). Both backends
		// give a field the argument that names it, else the one at its
		// position, and a field that is given none holds no value at all.
		if et, ok := c.info.Entities[id.Name]; ok {
			given := make([]bool, len(et.Fields))
			for i, a := range e.Args {
				at, err := c.checkExpr(a.Value, sc)
				if err != nil {
					return nil, err
				}
				if a.Mut || a.Own {
					return nil, fmt.Errorf("%s: a field of %s is given a value: 'mut' and 'own' are for the parameters of a function", a.Span, et.Name)
				}
				fi := i
				if a.Name != "" {
					fi = slices.IndexFunc(et.Fields, func(f EntityFieldInfo) bool { return f.Name == a.Name })
					if fi < 0 {
						return nil, fmt.Errorf("%s: entity %s has no field %q", a.Span, et.Name, a.Name)
					}
				} else if i >= len(et.Fields) {
					return nil, fmt.Errorf("%s: entity %s has %s, got %d arguments", e.Span, et.Name, plural(len(et.Fields), "field"), len(e.Args))
				}
				f := et.Fields[fi]
				if given[fi] {
					return nil, fmt.Errorf("%s: field %s.%s is given twice", a.Span, et.Name, f.Name)
				}
				given[fi] = true
				if !c.assignable(f.Type, at, a.Value) {
					return nil, fmt.Errorf("%s: field %s.%s expects %s, got %s", a.Span, et.Name, f.Name, f.Type, at)
				}
			}
			for fi, f := range et.Fields {
				if !given[fi] {
					return nil, fmt.Errorf("%s: field %s.%s is not given: an entity is made with a value for each of its fields", e.Span, et.Name, f.Name)
				}
			}
			return et, nil
		}

		// User ADT variant constructor
		if adt, ok := c.info.Variants[id.Name]; ok {
			vi := adt.VariantMap[id.Name]
			if len(e.Args) < len(vi.Fields) {
				return nil, fmt.Errorf("%s: %s has %d field(s), got %d arguments", e.Span, id.Name, len(vi.Fields), len(e.Args))
			}
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
		// `fp.take(xs, 2)` is `xs |> take(2)`.
		if mt, ok := objTy.(*ModuleType); ok && mt.Path == "std.fp" {
			if _, ok := stageShapes[fe.Field]; ok {
				if len(e.Args) == 0 || e.Args[0].Name != "" || e.Args[0].Mut || e.Args[0].Own {
					return nil, fmt.Errorf("%s: %s takes the value it works on as its first argument", e.Span, fe.Field)
				}
				stage := &ast.CallExpr{Span: e.Span, Callee: e.Callee, Args: e.Args[1:]}
				return c.checkPipeExpr(&ast.PipeExpr{Span: e.Span, Left: e.Args[0].Value, Right: stage}, sc)
			}
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
			if err := c.checkStdCall(e, fe); err != nil {
				return nil, err
			}
			var targetTy Type = UnknownType{}
			if len(e.TypeArgs) == 1 {
				var err error
				targetTy, err = c.resolveTypeExpr(e.TypeArgs[0])
				if err != nil {
					return nil, err
				}
				// What is decoded is given the type named, so every part
				// of that type has to be one the decoder checks.
				et, ok := targetTy.(*EntityType)
				if !ok {
					return nil, fmt.Errorf("%s: json.decode[%s]: only an entity is decoded into", e.Span, targetTy)
				}
				if why := jsonUndecodable(et, et.Name, map[string]bool{}); why != "" {
					return nil, fmt.Errorf("%s: json.decode[%s]: %s", e.Span, et.Name, why)
				}
			}
			return c.instantiateADT("Result", []Type{targetTy, StrType{}}), nil
		}
		// std.concurrent.Channel[T](cap=N) or ThreadPool(workers, queue_cap)
		if mt, ok := objTy.(*ModuleType); ok && mt.Path == "std.concurrent" {
			// The function of parallel_map is called with an element of
			// the list, and its results are those of the list it gives.
			var mapped Type
			for i, a := range e.Args {
				// The list is the first argument, or the piped value.
				var list ast.Expr
				if piped := c.piped[e]; piped != nil && len(e.Args) == 1 {
					list = piped
				} else if i == 1 && len(e.Args) == 2 {
					list = e.Args[0].Value
				}
				if fe.Field == "parallel_map" && list != nil {
					if lt, ok := c.info.ExprTypes[list].(*ListType); ok {
						ret, ok, err := c.stageFn(a.Value, sc, lt.Elem)
						if err != nil {
							return nil, err
						}
						if ok {
							mapped = widenInt(ret)
							continue
						}
					}
				}
				if _, err := c.checkExpr(a.Value, sc); err != nil {
					return nil, err
				}
			}
			if err := c.checkStdCall(e, fe); err != nil {
				return nil, err
			}
			switch fe.Field {
			case "Channel":
				var elem Type = UnknownType{}
				if len(e.TypeArgs) == 1 {
					var err error
					if elem, err = c.resolveTypeExpr(e.TypeArgs[0]); err != nil {
						return nil, err
					}
				}
				return &HandleType{Name: "conc.Channel", Elem: elem, Protocol: c.info.StdHandles["conc.Channel"]}, nil
			case "ThreadPool":
				return &HandleType{Name: "conc.ThreadPool", Protocol: c.info.StdHandles["conc.ThreadPool"]}, nil
			case "Mutex":
				// The mutex holds values of the type of its first one, not
				// of that one's range: set() gives it others.
				return &HandleType{Name: "conc.Mutex", Elem: widenInt(c.info.ExprTypes[c.stdArgs(e)[0].Value])}, nil
			case "Semaphore":
				return &HandleType{Name: "conc.Semaphore"}, nil
			case "parallel_map":
				if mapped != nil {
					return &ListType{Elem: mapped}, nil
				}
				return &ListType{Elem: UnknownType{}}, nil
			}
			return nil, fmt.Errorf("%s: module std.concurrent has no member %q", e.Span, fe.Field)
		}
	}

	if nl, name := namedLambdaOf(e.Callee, sc); nl != nil {
		var types []Type
		for _, a := range e.Args {
			if a.Name != "" {
				return nil, fmt.Errorf("%s: a lambda takes its arguments by position", a.Span)
			}
			at, err := c.checkExpr(a.Value, sc)
			if err != nil {
				return nil, err
			}
			types = append(types, at)
		}
		if err := c.checkCallAliasing(e.Args, true); err != nil {
			return nil, err
		}
		ret, err := c.useLambda(nl, name, types, e.Span)
		if err != nil {
			return nil, err
		}
		c.info.ExprTypes[e.Callee] = &FuncType{Return: ret}
		return ret, nil
	}
	c.callee = e.Callee
	calleeTy, err := c.checkExpr(e.Callee, sc)
	c.callee = nil
	if err != nil {
		return nil, err
	}
	// The function of with_lock is called with what the mutex holds.
	var held Type
	if fe, ok := e.Callee.(*ast.FieldExpr); ok && fe.Field == "with_lock" && len(e.Args) == 1 {
		if ht, ok := c.info.ExprTypes[fe.Object].(*HandleType); ok && ht.Name == "conc.Mutex" && ht.Elem != nil {
			held = ht.Elem
		}
	}
	for _, a := range e.Args {
		if held != nil {
			if _, ok, err := c.stageFn(a.Value, sc, held); err != nil {
				return nil, err
			} else if ok {
				continue
			}
		}
		if _, err := c.checkExpr(a.Value, sc); err != nil {
			return nil, err
		}
	}
	if err := c.checkCallAliasing(e.Args, true); err != nil {
		return nil, err
	}
	if ft, ok := calleeTy.(*FuncType); ok {
		// A lambda takes its arguments by position, and one it is not given
		// is None when it runs. The members of a module or a handle are
		// checked where they are looked up.
		if _, member := e.Callee.(*ast.FieldExpr); !member {
			for _, a := range e.Args {
				if a.Name != "" {
					return nil, fmt.Errorf("%s: a lambda takes its arguments by position", a.Span)
				}
			}
			if len(e.Args) != len(ft.Params) {
				return nil, fmt.Errorf("%s: this function takes %s, got %d", e.Span, plural(len(ft.Params), "argument"), len(e.Args))
			}
		} else if err := c.checkStdCall(e, e.Callee.(*ast.FieldExpr)); err != nil {
			return nil, err
		} else if mt, ok := c.info.ExprTypes[e.Callee.(*ast.FieldExpr).Object].(*ModuleType); ok && mt.Path == "std.requests" && e.Callee.(*ast.FieldExpr).Field == "gather" {
			return c.gatherType(e)
		} else if ht, ok := c.info.ExprTypes[e.Callee.(*ast.FieldExpr).Object].(*HandleType); ok && ht.Name == "conc.ThreadPool" && e.Callee.(*ast.FieldExpr).Field == "submit" {
			// The future of a task holds what the task gives.
			if args := c.stdArgs(e); len(args) == 1 {
				if task, ok := c.info.ExprTypes[args[0].Value].(*FuncType); ok && task.Return != nil {
					return &HandleType{Name: "Future", Elem: widenInt(task.Return)}, nil
				}
			}
		}
		return ft.Return, nil
	}
	// A value of a type that is known and is not a function cannot be
	// called: the VM stops on it and the native backend gives `()`.
	switch calleeTy.Kind() {
	case KindInt, KindBool, KindStr, KindList, KindMap, KindADT, KindEntity:
		return nil, fmt.Errorf("%s: a value of type %s cannot be called", e.Span, calleeTy)
	}
	if opaque(calleeTy) {
		return nil, unknownUse(e.Span, "a call of")
	}
	return UnknownType{Generic: generic(calleeTy)}, nil
}

// checkBuiltinArgs checks the arguments of a built-in function, which both
// backends take by position and read without looking at how many there are:
// one argument of each kind in kinds, KindUnknown standing for any value.
func (c *checker) checkBuiltinArgs(e *ast.CallExpr, sc *scope, kinds ...TypeKind) error {
	name := e.Callee.(*ast.Ident).Name
	for i, a := range e.Args {
		at, err := c.checkExpr(a.Value, sc)
		if err != nil {
			return err
		}
		if a.Name != "" {
			return fmt.Errorf("%s: %s() takes its arguments by position", a.Span, name)
		}
		if i < len(kinds) && kinds[i] != KindUnknown && at.Kind() != kinds[i] && !generic(at) {
			return fmt.Errorf("%s: argument %d of %s() is %s, got %s", a.Value.GetSpan(), i+1, name, kindNoun(kinds[i]), at)
		}
	}
	if len(e.Args) != len(kinds) {
		return fmt.Errorf("%s: %s() takes %s, got %d", e.Span, name, plural(len(kinds), "argument"), len(e.Args))
	}
	return nil
}

func kindNoun(k TypeKind) string {
	switch k {
	case KindInt:
		return "an int"
	case KindBool:
		return "a bool"
	case KindStr:
		return "a str"
	case KindList:
		return "a list"
	}
	return "a value"
}

func plural(n int, noun string) string {
	if n == 1 {
		return "1 " + noun
	}
	return fmt.Sprintf("%d %ss", n, noun)
}

// checkRequestsTimeout requires a blocking call to name its timeout. A
// timeout whose type has a range is checked here; the kernel proves the
// value in 1..300_000 whatever its type (ProgramInfo.TimeoutArgs).
func (c *checker) checkRequestsTimeout(call *ast.CallExpr, method string, sc *scope) error {
	// With the piped value first: `url |> sess.get(5)` is sess.get(url, 5).
	args, span := c.stdArgs(call), call.Span
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
	} else if !intLike(ty) {
		return fmt.Errorf("%s: timeout_ms must be int[1..300_000], got %s", timeoutExpr.GetSpan(), ty)
	}
	return nil
}

// relationBounds reads the multiplicity of a relation: how many entities
// it holds at least and at most, -1 standing for any number.
func relationBounds(rel ast.RelationDecl) (lo, hi int64, err error) {
	bad := func() (int64, int64, error) {
		return 0, 0, fmt.Errorf("%s: relation %s holds %s entities: a multiplicity is 1, 0..1, *, or a count n or n..m or n..* with n <= m and m >= 1", rel.Span, rel.Name, rel.Multiplicity)
	}
	if rel.Multiplicity == "*" {
		return 0, -1, nil
	}
	first, second, ranged := strings.Cut(rel.Multiplicity, "..")
	lo, err = strconv.ParseInt(first, 10, 64)
	if err != nil {
		return bad()
	}
	switch {
	case !ranged:
		hi = lo
	case second == "*":
		hi = -1
	default:
		if hi, err = strconv.ParseInt(second, 10, 64); err != nil {
			return bad()
		}
	}
	if hi == 0 || hi > 0 && lo > hi {
		return bad()
	}
	return lo, hi, nil
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

// eitherOf is the type of a value that is one of type a or one of type b,
// and whether there is such a type. An int has the range of both. A list, a
// map or a variant is a reference whose element ranges are part of its
// type, so the two types are the same one; with one of them unknown, the
// value has no type the kernel could read a range from.
func eitherOf(a, b Type) (Type, bool) {
	// The type argument no value has leaves the other; a value of
	// unknown type on one side makes the result one.
	switch {
	case vacuous(a):
		return b, true
	case vacuous(b):
		return a, true
	case untyped(a) || untyped(b):
		return UnknownType{}, true
	}
	if keepsType(a) || keepsType(b) {
		if !knownType(a) || !knownType(b) {
			return UnknownType{}, true
		}
		return a, isAssignable(a, b) && isAssignable(b, a)
	}
	if !knownType(a) || !knownType(b) {
		if knownType(a) {
			return widenInt(a), true
		}
		return widenInt(b), true
	}
	if a.Kind() != b.Kind() || !sameSort(a, b) {
		return nil, false
	}
	return unifyTypes(a, b), true
}

// stageShape is what a pipeline stage takes after the piped value.
type stageShape struct {
	args    int  // how many arguments
	fn      int  // which of them is the function, -1 for none
	arity   int  // how many parameters that function has
	variant bool // the piped value is an Option or a Result, not a list
}

var stageShapes = map[string]stageShape{
	"filter":    {args: 1, fn: 0, arity: 1},
	"map":       {args: 1, fn: 0, arity: 1},
	"flat_map":  {args: 1, fn: 0, arity: 1},
	"any":       {args: 1, fn: 0, arity: 1},
	"all":       {args: 1, fn: 0, arity: 1},
	"find":      {args: 1, fn: 0, arity: 1},
	"fold":      {args: 2, fn: 1, arity: 2},
	"sum":       {args: 0, fn: -1},
	"take":      {args: 1, fn: -1},
	"drop":      {args: 1, fn: -1},
	"filter_ok": {args: 0, fn: -1},
	"unwrap_or": {args: 1, fn: -1, variant: true},
	"and_then":  {args: 1, fn: 0, arity: 1, variant: true},
}

func (c *checker) checkStage(name string, shape stageShape, lhsTy Type, args []ast.CallArg, e *ast.PipeExpr, sc *scope) error {
	if len(args) != shape.args {
		return fmt.Errorf("%s: %s takes %s after the value it works on, got %d", e.Right.GetSpan(), name, plural(shape.args, "argument"), len(args))
	}
	for _, a := range args {
		if a.Name != "" || a.Mut || a.Own {
			return fmt.Errorf("%s: %s takes its arguments by position", a.Span, name)
		}
	}
	switch lt := lhsTy.(type) {
	case UnknownType:
	case *ListType:
		if shape.variant {
			return fmt.Errorf("%s: %s takes an Option or a Result, got %s", e.Left.GetSpan(), name, lhsTy)
		}
		if name == "sum" && lt.Elem.Kind() != KindInt && lt.Elem.Kind() != KindUnknown {
			return fmt.Errorf("%s: sum takes a list of int, got %s", e.Left.GetSpan(), lhsTy)
		}
	case *ADTType:
		if !shape.variant || (lt.Name != "Option" && lt.Name != "Result") {
			return fmt.Errorf("%s: %s takes %s, got %s", e.Left.GetSpan(), name, stageInput(shape), lhsTy)
		}
	default:
		return fmt.Errorf("%s: %s takes %s, got %s", e.Left.GetSpan(), name, stageInput(shape), lhsTy)
	}
	if name == "take" || name == "drop" {
		at, err := c.checkExpr(args[0].Value, sc)
		if err != nil {
			return err
		}
		if !intLike(at) {
			return fmt.Errorf("%s: %s takes an int, got %s", args[0].Value.GetSpan(), name, at)
		}
	}
	if shape.fn < 0 {
		return nil
	}
	// The function is a lambda or a variable holding one.
	fn := args[shape.fn].Value
	params := -1
	if lam, ok := fn.(*ast.LambdaExpr); ok {
		params = len(lam.Params)
	} else if nl, _ := namedLambdaOf(fn, sc); nl != nil {
		params = len(nl.expr.Params)
	} else {
		at, err := c.checkExpr(fn, sc)
		if err != nil {
			return err
		}
		switch at.Kind() {
		case KindInt, KindBool, KindStr, KindList, KindMap, KindADT, KindEntity:
			return fmt.Errorf("%s: %s takes a function, got %s", fn.GetSpan(), name, at)
		}
		if ft, ok := at.(*FuncType); ok {
			params = len(ft.Params)
		}
	}
	if params >= 0 && params != shape.arity {
		return fmt.Errorf("%s: the function of %s takes %s, got one with %d", fn.GetSpan(), name, plural(shape.arity, "parameter"), params)
	}
	return nil
}

func stageInput(shape stageShape) string {
	if shape.variant {
		return "an Option or a Result"
	}
	return "a list"
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

	var elemTy Type = UnknownType{Generic: generic(lhsTy)}
	if lt, ok := lhsTy.(*ListType); ok {
		elemTy = lt.Elem
	}

	if direct {
		if err := c.checkCalleeNotShadowed(fnName, e.Right.GetSpan(), sc); err != nil {
			return nil, err
		}
	}

	// A function of the program named like a stage is what both backends
	// call: `xs |> filter(2)` is then `filter(xs, 2)`.
	stage := fnName
	if _, user := c.info.Funcs[fnName]; user && direct {
		stage = ""
	}

	// A stage is given what it takes: both backends read its arguments by
	// position without looking at how many there are, and call its function
	// with one element (fold: the sum so far and one element).
	if shape, ok := stageShapes[stage]; ok {
		if opaque(lhsTy) && !vacuous(lhsTy) {
			return nil, unknownUse(e.Left.GetSpan(), "the stage "+fnName+" on")
		}
		if err := c.checkStage(fnName, shape, lhsTy, callArgs, e, sc); err != nil {
			return nil, err
		}
	}

	switch stage {
	case "filter":
		if len(callArgs) == 1 {
			bty, ok, err := c.stageFn(callArgs[0].Value, sc, elemTy)
			if err != nil {
				return nil, err
			}
			if ok && !boolLike(bty) {
				return nil, fmt.Errorf("%s: filter predicate must return bool, got %s", callArgs[0].Value.GetSpan(), bty)
			}
		}
		return lhsTy, nil

	case "map":
		if len(callArgs) == 1 {
			rty, ok, err := c.stageFn(callArgs[0].Value, sc, elemTy)
			if err != nil {
				return nil, err
			}
			if ok {
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
			rty, ok, err := c.stageFn(callArgs[0].Value, sc, elemTy)
			if err != nil {
				return nil, err
			}
			if ok {
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
			rty, ok, err := c.stageFn(callArgs[1].Value, sc, accTy, elemTy)
			if err != nil {
				return nil, err
			}
			if ok {
				// The start when the list is empty, else what the
				// function gave last.
				ty, ok := eitherOf(accTy, rty)
				if !ok {
					return nil, fmt.Errorf("%s: the function of fold gives %s as fold starts with, got %s", stageBody(callArgs[1].Value).GetSpan(), accTy, rty)
				}
				return ty, nil
			}
			return accTy, nil
		}
	case "sum":
		return NewUnboundedInt(), nil
	case "any", "all":
		if len(callArgs) == 1 {
			if _, _, err := c.stageFn(callArgs[0].Value, sc, elemTy); err != nil {
				return nil, err
			}
		}
		return BoolType{}, nil
	case "find":
		if len(callArgs) == 1 {
			if _, _, err := c.stageFn(callArgs[0].Value, sc, elemTy); err != nil {
				return nil, err
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
			// What the variant holds, or the default.
			var held Type = UnknownType{}
			if adt, ok := lhsTy.(*ADTType); ok && len(adt.TypeArgs) > 0 {
				held = adt.TypeArgs[0]
			}
			ty, ok := eitherOf(held, dt)
			// The default is given to what the variant holds as a value is
			// to a variable of that type: a literal or a constructor call is
			// a new value that takes the type, and the kernel proves it.
			if keepsType(held) && c.assignable(held, dt, callArgs[0].Value) {
				ty, ok = held, true
			}
			if !ok {
				return nil, fmt.Errorf("%s: unwrap_or on %s takes a default that is %s, got %s", callArgs[0].Value.GetSpan(), lhsTy, held, dt)
			}
			return ty, nil
		}
	case "and_then":
		if len(callArgs) == 1 {
			var okTy Type = UnknownType{Generic: generic(lhsTy)}
			adt, known := lhsTy.(*ADTType)
			if known && len(adt.TypeArgs) >= 1 {
				okTy = adt.TypeArgs[0]
			}
			bty, isFn, err := c.stageFn(callArgs[0].Value, sc, okTy)
			if err != nil {
				return nil, err
			}
			if isFn {
				body := stageBody(callArgs[0].Value)
				// A None or an Err is passed on as it is, so the function
				// gives the same kind of variant.
				if bty.Kind() == KindUnknown {
					return bty, nil
				}
				bdt, ok := bty.(*ADTType)
				if !ok || (bdt.Name != "Option" && bdt.Name != "Result") || (known && bdt.Name != adt.Name) {
					want := "an Option or a Result"
					if known {
						want = "an " + adt.Name
						if adt.Name == "Result" {
							want = "a Result"
						}
					}
					return nil, fmt.Errorf("%s: the function of and_then gives %s, got %s", body.GetSpan(), want, bty)
				}
				if bdt.Name == "Result" && len(bdt.TypeArgs) == 2 {
					// The error is the one it is given or the one it gives.
					var le Type = UnknownType{}
					if known && len(adt.TypeArgs) == 2 {
						le = adt.TypeArgs[1]
					}
					et, ok := eitherOf(le, bdt.TypeArgs[1])
					if !ok {
						return nil, fmt.Errorf("%s: the function of and_then gives a Result with the error of %s, got %s", body.GetSpan(), lhsTy, bty)
					}
					return c.instantiateADT("Result", []Type{bdt.TypeArgs[0], et}), nil
				}
				return bty, nil
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
	// `x |> g(a)` and `x |> g` call g(x, a) on both backends, whatever g
	// is: a lambda in a variable, a built-in function, a constructor.
	if _, isStage := stageShapes[fnName]; direct && !isStage {
		// The kernel proves the fields of an entity or a variant where it
		// is made, and that is a call.
		_, isEntity := c.info.Entities[fnName]
		_, isVariant := c.info.Variants[fnName]
		if isEntity || isVariant || fnName == "Some" || fnName == "Ok" || fnName == "Err" {
			return nil, fmt.Errorf("%s: %s makes a value and is not a pipeline stage: write %s(...)", e.Right.GetSpan(), fnName, fnName)
		}
		call := &ast.CallExpr{Span: e.Span, Callee: &ast.Ident{Span: e.Right.GetSpan(), Name: fnName}}
		if rhs, ok := e.Right.(*ast.CallExpr); ok {
			call.Callee, call.TypeArgs = rhs.Callee, rhs.TypeArgs
		}
		call.Args = append([]ast.CallArg{{Value: e.Left, Span: e.Left.GetSpan()}}, callArgs...)
		return c.checkExpr(call, sc)
	}
	// `x |> o.f(a)` calls o.f(x, a) on both backends too. The call that is
	// written is the one the kernels look at (its timeout, the handle it
	// makes), so it is that one that is checked, with the piped value
	// counted as its first argument.
	if rhs, ok := e.Right.(*ast.CallExpr); ok {
		if _, member := rhs.Callee.(*ast.FieldExpr); member {
			if c.piped == nil {
				c.piped = map[*ast.CallExpr]ast.Expr{}
			}
			c.piped[rhs] = e.Left
		}
	}
	rt, err := c.checkExpr(e.Right, sc)
	if err != nil {
		return nil, err
	}
	if _, member := e.Right.(*ast.CallExpr); member && rt != nil {
		if _, isField := e.Right.(*ast.CallExpr).Callee.(*ast.FieldExpr); isField {
			return rt, nil
		}
	}
	return UnknownType{}, nil
}

// stageBody is the body of the lambda a stage is given, or what it is
// given when that is the name of one.
func stageBody(fn ast.Expr) ast.Expr {
	if lam, ok := fn.(*ast.LambdaExpr); ok {
		return lam.Body
	}
	return fn
}

// checkLambdaWith checks the body of lam with its parameters of the given
// types, and records the type of the lambda.
func (c *checker) checkLambdaWith(lam *ast.LambdaExpr, sc *scope, types []Type) (*FuncType, error) {
	lsc := newScope(sc)
	ps := make([]FuncParamInfo, len(lam.Params))
	seen := newOnce("parameters", "a lambda")
	for i, pname := range lam.Params {
		if err := seen.add(pname, lam.Span); err != nil {
			return nil, err
		}
		lsc.defineLocal(pname, varBinding{ty: types[i], span: lam.Span})
		ps[i] = FuncParamInfo{Name: pname, Type: types[i]}
	}
	rt, err := c.checkExpr(lam.Body, lsc)
	if err != nil {
		return nil, err
	}
	ft := &FuncType{Params: ps, Return: rt}
	c.info.ExprTypes[lam] = ft
	return ft, nil
}

// useLambda is a use of the named lambda nl with arguments of the given
// types: the first fixes the types of its parameters, an int as an int of
// any range, and checks its body with them; the others are given those.
func (c *checker) useLambda(nl *namedLambda, name string, args []Type, span ast.Span) (Type, error) {
	if len(args) != len(nl.expr.Params) {
		return nil, fmt.Errorf("%s: this function takes %s, got %d", span, plural(len(nl.expr.Params), "argument"), len(args))
	}
	// An argument made where another named lambda is written, of a
	// parameter that has no type yet, says nothing of this one: `[x]` there
	// would fix it as taking a list of anything, for every later use.
	for _, a := range args {
		if holdsGeneric(a) {
			return UnknownType{Generic: true}, nil
		}
	}
	if !nl.fixed {
		params := make([]Type, len(args))
		for i, a := range args {
			// The types of this use are those of every later one, and a
			// type argument no value has would be any type there: `None`
			// here would let `Some(0)` in later as an Option of nothing.
			if hasGap(a) {
				return nil, fmt.Errorf("%s: %s is first used with %s, which does not say the type of all it holds: use it first with a value that has its whole type", span, name, a)
			}
			params[i] = widenInt(a)
		}
		ft, err := c.checkLambdaWith(nl.expr, nl.sc, params)
		if err != nil {
			return nil, fmt.Errorf("%w (the lambda %s, as it is first used at %s)", err, name, span)
		}
		nl.params, nl.ret, nl.fixed = params, ft.Return, true
		return nl.ret, nil
	}
	for i, a := range args {
		if !c.assignable(nl.params[i], a, nil) || !isAssignable(nl.params[i], a) {
			return nil, fmt.Errorf("%s: %s takes %s where it is first used, got %s: a lambda takes the same types at every use", span, name, nl.params[i], a)
		}
	}
	return nl.ret, nil
}

// holdsGeneric reports whether t is, or has as a part, the type of a
// parameter of a named lambda where the lambda is written.
func holdsGeneric(t Type) bool {
	switch x := t.(type) {
	case UnknownType:
		return x.Generic
	case *ListType:
		return holdsGeneric(x.Elem)
	case *MapType:
		return holdsGeneric(x.Key) || holdsGeneric(x.Val)
	case *ADTType:
		return slices.ContainsFunc(x.TypeArgs, holdsGeneric)
	case *HandleType:
		return x.Elem != nil && holdsGeneric(x.Elem)
	case *FuncType:
		return x.Return != nil && holdsGeneric(x.Return) ||
			slices.ContainsFunc(x.Params, func(p FuncParamInfo) bool { return holdsGeneric(p.Type) })
	}
	return false
}

// hasGap reports whether t has a part no value has given a type: the
// elements of `[]`, what `None` holds.
func hasGap(t Type) bool {
	switch x := t.(type) {
	case UnknownType:
		return x.Empty
	case TypeVar:
		return true
	case *ListType:
		return hasGap(x.Elem)
	case *MapType:
		return hasGap(x.Key) || hasGap(x.Val)
	case *ADTType:
		if len(x.TypeArgs) < len(x.TypeParams) {
			return true
		}
		for _, a := range x.TypeArgs {
			if hasGap(a) {
				return true
			}
		}
	case *HandleType:
		return x.Elem != nil && hasGap(x.Elem)
	}
	return false
}

// slotGap reports whether t has such a part in something that is written
// after it is made: an element of a list, an entry of a map, what a mutex
// holds. A list of nothing has no element to write.
// jsonUndecodable says why a JSON text cannot be decoded into t, or "". The
// decoder checks an int against its range, a bool, a str, the elements of a
// list, the values of a map with str keys, what an Option holds and the
// fields of an entity; it has no rule for anything else, and what it does
// not check would be given the declared type as it comes.
func jsonUndecodable(t Type, path string, open map[string]bool) string {
	switch x := t.(type) {
	case *IntType, BoolType, StrType:
		return ""
	case *ListType:
		return jsonUndecodable(x.Elem, path+"[]", open)
	case *MapType:
		if _, ok := x.Key.(StrType); !ok {
			return fmt.Sprintf("%s is a %s, and the keys of a JSON object are str", path, t)
		}
		return jsonUndecodable(x.Val, path+"[]", open)
	case *ADTType:
		if x.Name == "Option" && len(x.TypeArgs) == 1 {
			return jsonUndecodable(x.TypeArgs[0], path, open)
		}
	case *EntityType:
		if open[x.Name] {
			return ""
		}
		open[x.Name] = true
		for _, f := range x.Fields {
			if why := jsonUndecodable(f.Type, path+"."+f.Name, open); why != "" {
				return why
			}
		}
		return ""
	}
	return fmt.Sprintf("%s is a %s, which is not read from JSON (an int, a bool, a str, a list, a map with str keys, an Option and an entity of these are)", path, t)
}

func slotGap(t Type) bool {
	switch x := t.(type) {
	case *ListType:
		return !vacuous(x.Elem) && hasGap(x.Elem)
	case *MapType:
		return hasGap(x.Key) || hasGap(x.Val)
	case *HandleType:
		if x.Elem == nil {
			return false
		}
		if x.Name == "conc.Mutex" {
			return hasGap(x.Elem)
		}
		return slotGap(x.Elem)
	case *ADTType:
		for _, a := range x.TypeArgs {
			if slotGap(a) {
				return true
			}
		}
	}
	return false
}

// wholeSlots refuses to give the variable name a value of a type with such
// a part. The part would be any type: a write through the variable would put
// a value there that a read, through it or through another name for the
// same list, map or mutex, takes for one of another type.
func wholeSlots(name string, ty Type, span ast.Span) error {
	if slotGap(ty) {
		return fmt.Errorf("%s: %s would be a %s, which can be written to and does not say the type of all it holds: declare the type of %s", span, name, ty, name)
	}
	return nil
}

// namedLambdaOf is the named lambda e is the name of.
func namedLambdaOf(e ast.Expr, sc *scope) (*namedLambda, string) {
	if id, ok := e.(*ast.Ident); ok {
		if b, found := sc.lookup(id.Name); found && b.lam != nil {
			return b.lam, id.Name
		}
	}
	return nil, ""
}

// stageFn checks the function a stage or a standard call is given, a lambda
// or the name of one, with the types it is called with. ok is false for
// anything else.
func (c *checker) stageFn(fn ast.Expr, sc *scope, params ...Type) (Type, bool, error) {
	if lam, ok := fn.(*ast.LambdaExpr); ok {
		if len(lam.Params) != len(params) {
			return nil, false, nil
		}
		ft, err := c.checkLambdaWith(lam, sc, params)
		if err != nil {
			return nil, true, err
		}
		return ft.Return, true, nil
	}
	if nl, name := namedLambdaOf(fn, sc); nl != nil {
		if len(nl.expr.Params) != len(params) {
			return nil, false, nil
		}
		ret, err := c.useLambda(nl, name, params, fn.GetSpan())
		if err != nil {
			return nil, true, err
		}
		c.info.ExprTypes[fn] = &FuncType{Return: ret}
		return ret, true, nil
	}
	return nil, false, nil
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
	case "std.fp":
		if _, ok := stageShapes[member]; ok {
			return &FuncType{Return: UnknownType{}}, nil
		}
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
		case "send_text":
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
	case "conc.Semaphore":
		switch method {
		case "acquire", "release":
			return &FuncType{Return: VoidType{}}, nil
		}
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
	// A value of unknown type is not one of a type that is known: nothing
	// says it is. The type argument no value has is any type.
	if untyped(actual) && knownType(expected) {
		return false
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
	// A handle is a reference: the two sides read and write what it holds,
	// so they agree on its type.
	if eh, ok := expected.(*HandleType); ok {
		ah, ok := actual.(*HandleType)
		if !ok || ah.Name != eh.Name {
			return false
		}
		if eh.Elem == nil || ah.Elem == nil {
			return eh.Elem == nil && ah.Elem == nil
		}
		return untyped(eh.Elem) == untyped(ah.Elem) && sameHeld(eh.Elem, ah.Elem)
	}
	return expected.Equals(actual)
}

// sameHeld reports whether a and b are one type, ranges included: what two
// names for one reference, or the results of futures gathered into one list,
// have to agree on.
func sameHeld(a, b Type) bool {
	return isAssignable(a, b) && isAssignable(b, a) && sameElemRange(a, b) && sameElemRange(b, a)
}

// sameWhole reports whether a and b are one type, part by part: a part no
// value has typed is the same as such a part only, where sameHeld takes it
// for any type.
func sameWhole(a, b Type) bool {
	if a == nil || b == nil {
		return a == nil && b == nil
	}
	switch x := a.(type) {
	case UnknownType:
		y, ok := b.(UnknownType)
		return ok && x == y
	case *IntType:
		y, ok := b.(*IntType)
		return ok && x.IsBounded == y.IsBounded && (!x.IsBounded || (x.Lo == y.Lo && x.Hi == y.Hi))
	case *ListType:
		y, ok := b.(*ListType)
		return ok && sameWhole(x.Elem, y.Elem)
	case *MapType:
		y, ok := b.(*MapType)
		// The range of a key is not part of a map type: isAssignable
		// does not read it either.
		return ok && sameWhole(widenInt(x.Key), widenInt(y.Key)) && sameWhole(x.Val, y.Val)
	case *HandleType:
		y, ok := b.(*HandleType)
		return ok && x.Name == y.Name && sameWhole(x.Elem, y.Elem)
	case *ADTType:
		y, ok := b.(*ADTType)
		if !ok || x.Name != y.Name || len(x.TypeArgs) != len(y.TypeArgs) {
			return false
		}
		for i := range x.TypeArgs {
			if !sameWhole(x.TypeArgs[i], y.TypeArgs[i]) {
				return false
			}
		}
		return true
	}
	if _, unknown := b.(UnknownType); unknown {
		return false
	}
	return a.Kind() == b.Kind() && a.Equals(b) && b.Equals(a)
}

// sameElemRange reports whether two element types of a list or map agree on
// the range of an int. A list is a reference: seen as a list of int[1..9]
// by one name and as a list of int by another, a write through the second
// breaks what the first relies on, so the two ranges have to be the same.
func sameElemRange(expected, actual Type) bool {
	e, ok := expected.(*IntType)
	a, ok2 := actual.(*IntType)
	if _, unknown := actual.(UnknownType); unknown && ok && e.IsBounded {
		return false
	}
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
	// The part no value has typed holds nothing: `None` is in every range.
	if _, unknown := actual.(UnknownType); unknown && ok && e.IsBounded {
		return vacuous(actual)
	}
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
		// A variable of unknown type stays one: a branch may leave in it
		// the value it had.
		if untyped(prev) {
			return prev, true
		}
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
	// A value of unknown type (a lambda parameter) carries no element
	// range for the kernel to rely on.
	if _, unknown := actual.(UnknownType); unknown && keepsType(expected) && hasBoundedInt(expected) {
		return false
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
	// One of the two may be of unknown type, so the value is.
	for _, t := range []Type{a, b} {
		if untyped(t) {
			return t
		}
	}
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
