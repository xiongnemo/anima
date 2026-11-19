package vm

import (
	"bufio"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"math/rand"
	"net"
	"net/http"
	"os"
	"reflect"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/verify/lts"
)

type ValKind int

const (
	ValVoid ValKind = iota
	ValInt
	ValBool
	ValStr
	ValNone
	ValList
	ValMap
	ValEntity
	ValVariant
	ValClosure
	ValHandle
)

type EntityInstance struct {
	TypeName string
	Fields   map[string]Value
}

type VariantValue struct {
	Name   string
	Fields []Value
}

type ClosureValue struct {
	FuncIdx int
	Upvals  []Value
}

type HandleKind int

const (
	HandleListener HandleKind = iota
	HandleStream
	HandleFile
	HandleThreadPool
	HandleChannel
	HandleMutex
	HandleSemaphore
	HandleSession
	HandleFuture
	HandleByteView
)

type HandleValue struct {
	Kind       HandleKind
	Listener   net.Listener
	Conn       net.Conn
	File       *os.File
	FilePath   string
	Bytes      []byte
	PoolCh     chan func()
	PoolWG     *sync.WaitGroup
	PoolClosed bool
	Chan       chan Value
	ChanClosed bool
	ChanMu     *sync.Mutex
	Mu         *sync.Mutex
	MutexVal   *Value
	Sem        chan struct{}
	HTTPClient *http.Client
	FutCh      chan Value
	FutDone    bool
	FutVal     Value
	Closed     bool
}

func (h *HandleValue) Close() {
	if h == nil || h.Closed {
		return
	}
	h.Closed = true
	switch h.Kind {
	case HandleListener:
		if h.Listener != nil {
			_ = h.Listener.Close()
		}
	case HandleStream:
		if h.Conn != nil {
			_ = h.Conn.Close()
		}
	case HandleFile:
		if h.File != nil {
			_ = h.File.Close()
		}
	case HandleThreadPool:
		if !h.PoolClosed && h.PoolCh != nil {
			h.PoolClosed = true
			close(h.PoolCh)
			if h.PoolWG != nil {
				h.PoolWG.Wait()
			}
		}
	case HandleChannel:
		if h.ChanMu != nil {
			h.ChanMu.Lock()
			if !h.ChanClosed && h.Chan != nil {
				h.ChanClosed = true
				close(h.Chan)
			}
			h.ChanMu.Unlock()
		}
	}
}

type Value struct {
	Kind    ValKind
	Int     int64
	Bool    bool
	Str     string
	List    *[]Value
	Map     map[string]Value
	Entity  *EntityInstance
	Variant *VariantValue
	Closure *ClosureValue
	Handle  *HandleValue
}

func VVoid() Value           { return Value{Kind: ValVoid} }
func VInt(n int64) Value     { return Value{Kind: ValInt, Int: n} }
func VBool(b bool) Value     { return Value{Kind: ValBool, Bool: b} }
func VStr(s string) Value    { return Value{Kind: ValStr, Str: s} }
func VNone() Value           { return Value{Kind: ValNone} }
func VList(xs []Value) Value { cp := append([]Value{}, xs...); return Value{Kind: ValList, List: &cp} }
func VMap(m map[string]Value) Value {
	return Value{Kind: ValMap, Map: m}
}
func VOk(v Value) Value {
	return Value{Kind: ValVariant, Variant: &VariantValue{Name: "Ok", Fields: []Value{v}}}
}
func VErr(e string) Value {
	return Value{Kind: ValVariant, Variant: &VariantValue{Name: "Err", Fields: []Value{VStr(e)}}}
}
func VSome(v Value) Value {
	return Value{Kind: ValVariant, Variant: &VariantValue{Name: "Some", Fields: []Value{v}}}
}

func (v Value) IsTruthy() bool {
	switch v.Kind {
	case ValBool:
		return v.Bool
	case ValInt:
		return v.Int != 0
	case ValStr:
		return v.Str != ""
	case ValNone, ValVoid:
		return false
	case ValList:
		return v.List != nil && len(*v.List) > 0
	default:
		return true
	}
}

// Equals is `==`: lists, maps and variants are equal when what they hold is
// equal, an entity is equal to itself only. The native runtime has the same
// rule (v_eq in runtime_c.go).
func (v Value) Equals(o Value) bool {
	return valuesEqual(v, o, nil)
}

// eqPair is two containers being compared. A pair met again while it is
// being compared is inside a cycle and holds nothing new to compare.
type eqPair struct{ a, b uintptr }

func valuesEqual(v, o Value, open []eqPair) bool {
	if v.Kind != o.Kind {
		return false
	}
	var pair eqPair
	switch v.Kind {
	case ValVoid, ValNone:
		return true
	case ValInt:
		return v.Int == o.Int
	case ValBool:
		return v.Bool == o.Bool
	case ValStr:
		return v.Str == o.Str
	case ValEntity:
		return v.Entity == o.Entity
	case ValClosure:
		return v.Closure == o.Closure
	case ValHandle:
		return v.Handle == o.Handle
	case ValList:
		pair = eqPair{reflect.ValueOf(v.List).Pointer(), reflect.ValueOf(o.List).Pointer()}
	case ValMap:
		pair = eqPair{reflect.ValueOf(v.Map).Pointer(), reflect.ValueOf(o.Map).Pointer()}
	case ValVariant:
		pair = eqPair{reflect.ValueOf(v.Variant).Pointer(), reflect.ValueOf(o.Variant).Pointer()}
	default:
		return false
	}
	if pair.a == pair.b {
		return true
	}
	for _, p := range open {
		if p == pair {
			return true
		}
	}
	open = append(open, pair)
	switch v.Kind {
	case ValList:
		var a, b []Value
		if v.List != nil {
			a = *v.List
		}
		if o.List != nil {
			b = *o.List
		}
		if len(a) != len(b) {
			return false
		}
		for i := range a {
			if !valuesEqual(a[i], b[i], open) {
				return false
			}
		}
		return true
	case ValMap:
		if len(v.Map) != len(o.Map) {
			return false
		}
		for k, x := range v.Map {
			y, ok := o.Map[k]
			if !ok || !valuesEqual(x, y, open) {
				return false
			}
		}
		return true
	default:
		if v.Variant == nil || o.Variant == nil {
			return false
		}
		if v.Variant.Name != o.Variant.Name || len(v.Variant.Fields) != len(o.Variant.Fields) {
			return false
		}
		for i := range v.Variant.Fields {
			if !valuesEqual(v.Variant.Fields[i], o.Variant.Fields[i], open) {
				return false
			}
		}
		return true
	}
}

// reboundFrom says whether a branch of a fork gave a variable that held pre
// another value. A list, a map or an entity is another one unless it is the
// very same object, whatever it holds: later writes must reach the one the
// branch left there, and a branch that did not touch the variable must not
// bring the old one back.
func (v Value) reboundFrom(pre Value) bool {
	if v.Kind != pre.Kind {
		return true
	}
	switch v.Kind {
	case ValList:
		return v.List != pre.List
	case ValMap:
		return reflect.ValueOf(v.Map).Pointer() != reflect.ValueOf(pre.Map).Pointer()
	case ValEntity:
		return v.Entity != pre.Entity
	}
	return !v.Equals(pre)
}

// order is `<` and its kin: negative, zero or positive as v comes before, with
// or after o. Two strings are ordered byte by byte, anything else as integers.
func (v Value) order(o Value) int {
	if v.Kind == ValStr && o.Kind == ValStr {
		return strings.Compare(v.Str, o.Str)
	}
	switch {
	case v.Int < o.Int:
		return -1
	case v.Int > o.Int:
		return 1
	}
	return 0
}

// in is `v in o`: an element of a list, a key of a map, a part of a string.
func (v Value) in(o Value) bool {
	switch o.Kind {
	case ValList:
		if o.List != nil {
			for _, el := range *o.List {
				if v.Equals(el) {
					return true
				}
			}
		}
	case ValMap:
		_, ok := o.Map[v.String()]
		return ok
	case ValStr:
		return v.Kind == ValStr && strings.Contains(o.Str, v.Str)
	}
	return false
}

func sortedKeys(m map[string]Value) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

// quoteKey writes a map key between double quotes. The native runtime has
// the same escapes (v_fmt_key in runtime_c.go).
func quoteKey(k string) string {
	var b strings.Builder
	b.WriteByte('"')
	for i := 0; i < len(k); i++ {
		switch c := k[i]; {
		case c == '"' || c == '\\':
			b.WriteByte('\\')
			b.WriteByte(c)
		case c == '\n':
			b.WriteString(`\n`)
		case c == '\t':
			b.WriteString(`\t`)
		case c == '\r':
			b.WriteString(`\r`)
		case c < 0x20 || c == 0x7f:
			fmt.Fprintf(&b, `\x%02x`, c)
		default:
			b.WriteByte(c)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func (v Value) String() string {
	switch v.Kind {
	case ValVoid:
		return "()"
	case ValNone:
		return "None"
	case ValInt:
		return fmt.Sprintf("%d", v.Int)
	case ValBool:
		if v.Bool {
			return "True"
		}
		return "False"
	case ValStr:
		return v.Str
	case ValList:
		if v.List == nil {
			return "[]"
		}
		var parts []string
		for _, el := range *v.List {
			parts = append(parts, el.String())
		}
		return "[" + strings.Join(parts, ", ") + "]"
	case ValMap:
		// In the order of the keys: the order of a Go map changes from one
		// run to the next, and the native backend has to print the same.
		var parts []string
		for _, k := range sortedKeys(v.Map) {
			parts = append(parts, quoteKey(k)+": "+v.Map[k].String())
		}
		return "{" + strings.Join(parts, ", ") + "}"
	case ValEntity:
		var parts []string
		for _, k := range sortedKeys(v.Entity.Fields) {
			parts = append(parts, fmt.Sprintf("%s=%s", k, v.Entity.Fields[k].String()))
		}
		return fmt.Sprintf("%s(%s)", v.Entity.TypeName, strings.Join(parts, ", "))
	case ValVariant:
		if len(v.Variant.Fields) == 0 {
			return v.Variant.Name
		}
		var parts []string
		for _, f := range v.Variant.Fields {
			parts = append(parts, f.String())
		}
		return fmt.Sprintf("%s(%s)", v.Variant.Name, strings.Join(parts, ", "))
	case ValHandle:
		return fmt.Sprintf("<handle:%d>", v.Handle.Kind)
	case ValClosure:
		return fmt.Sprintf("<fn#%d>", v.Closure.FuncIdx)
	}
	return "<val>"
}

type RunOptions struct {
	Seed    int64
	Stdout  io.Writer
	Stdin   io.Reader
	Args    []string
	Animate bool
	Replay  *lts.SequenceTrace
}

type VM struct {
	prog      *CompiledProgram
	opts      RunOptions
	rng       *rand.Rand
	outMu     sync.Mutex
	monMu     sync.Mutex
	monStates map[string]string
	portLogs  []string
	pools     map[string]chan struct{}
	exitCode  int
}

func NewVM(prog *CompiledProgram, opts RunOptions) *VM {
	if opts.Stdout == nil {
		opts.Stdout = os.Stdout
	}
	if opts.Stdin == nil {
		opts.Stdin = os.Stdin
	}
	if opts.Seed == 0 {
		opts.Seed = 42
	}
	v := &VM{
		prog:      prog,
		opts:      opts,
		rng:       rand.New(rand.NewSource(opts.Seed)),
		monStates: map[string]string{},
		pools:     map[string]chan struct{}{},
	}
	for name, m := range prog.Machines {
		if len(m.States) > 0 {
			v.monStates[name] = m.States[0].Name
		}
	}
	return v
}

func (vm *VM) printf(format string, args ...any) {
	vm.outMu.Lock()
	defer vm.outMu.Unlock()
	fmt.Fprintf(vm.opts.Stdout, format, args...)
}

// Run executes `main()` (or the first workflow/trace replay if specified).
func (vm *VM) Run() (Value, error) {
	if vm.opts.Replay != nil {
		return vm.runReplay(vm.opts.Replay)
	}
	if vm.opts.Animate {
		return vm.runCLIAnimator()
	}
	if _, hasMain := vm.prog.Module.FuncIndex["main"]; hasMain {
		val, _, _, err := vm.callFuncByName("main", nil, nil)
		return val, err
	}
	// If no main(), run the first parameterless workflow if any
	for _, wf := range vm.prog.Module.Workflows {
		if len(vm.prog.Workflows[wf.Name].Params) == 0 {
			return vm.RunWorkflow(wf.Name, nil)
		}
	}
	return VVoid(), nil
}

func (vm *VM) runReplay(trace *lts.SequenceTrace) (Value, error) {
	vm.printf("[AnimaVM Replay] Replaying %d counterexample steps for %s\n", len(trace.Steps), trace.Title)
	for i, step := range trace.Steps {
		target := ""
		if step.Receiver != "" {
			target = " -> " + step.Receiver
		}
		vm.printf("  step %d: [%s%s] %s  ==>  state: %s\n", i+1, step.Actor, target, step.Action, step.StateStr)
	}
	if trace.Violation != "" {
		vm.printf("  [REPRODUCED] %s\n", trace.Violation)
	}
	return VInt(1), nil
}

func (vm *VM) runCLIAnimator() (Value, error) {
	if len(vm.prog.Workflows) == 0 && len(vm.prog.Machines) == 0 {
		return vm.Run()
	}
	scanner := bufio.NewScanner(vm.opts.Stdin)
	vm.printf("[AnimaVM Interactive Animator] Loaded %d machines, %d workflows\n",
		len(vm.prog.Machines), len(vm.prog.Workflows))

	// Interactive loop over machines / workflows
	for {
		type option struct {
			label string
			apply func()
		}
		var opts []option
		for mName, m := range vm.prog.Machines {
			curSt := vm.monStates[mName]
			for _, st := range m.States {
				if st.Name == curSt {
					for _, tr := range st.Transitions {
						mn, act, dst := mName, tr.Action, tr.TargetState
						opts = append(opts, option{
							label: fmt.Sprintf("%s.%s (%s -> %s)", mn, act, curSt, dst),
							apply: func() { vm.monStates[mn] = dst },
						})
					}
				}
			}
		}
		vm.printf("\nCurrent Machine States: %v\n", vm.monStates)
		if len(opts) == 0 {
			vm.printf("No enabled transitions (Deadlock/End).\n")
			break
		}
		for i, o := range opts {
			vm.printf("  [%d] %s\n", i, o.label)
		}
		vm.printf("Select transition index (or 'q' to quit): ")
		if !scanner.Scan() {
			break
		}
		txt := strings.TrimSpace(scanner.Text())
		if txt == "q" || txt == "quit" {
			break
		}
		idx := -1
		if _, err := fmt.Sscanf(txt, "%d", &idx); err != nil || idx < 0 || idx >= len(opts) {
			vm.printf("Invalid selection.\n")
			continue
		}
		opts[idx].apply()
	}
	return VVoid(), nil
}

func (vm *VM) callFuncByName(name string, args []Value, presetLocals []Value) (Value, bool, []Value, error) {
	fIdx, ok := vm.prog.Module.FuncIndex[name]
	if !ok {
		return VVoid(), false, nil, fmt.Errorf("undefined bytecode function %q", name)
	}
	return vm.execProto(vm.prog.Module.Funcs[fIdx], args, nil, presetLocals)
}

func (vm *VM) callClosure(cl *ClosureValue, args []Value) (Value, error) {
	val, _, _, err := vm.execProto(vm.prog.Module.Funcs[cl.FuncIdx], args, cl.Upvals, nil)
	return val, err
}

func (vm *VM) execProto(fp *FuncProto, args []Value, upvals []Value, presetLocals []Value) (Value, bool, []Value, error) {
	locals := make([]Value, fp.NumLocals)
	if presetLocals != nil {
		for i := 0; i < len(presetLocals) && i < len(locals); i++ {
			locals[i] = presetLocals[i]
		}
	}
	for i := 0; i < len(args) && i < len(locals); i++ {
		locals[i] = args[i]
	}

	var stack []Value
	// Handles stored in this frame that a failing `?` closes on its early
	// return. Sockets and files are excluded: the ownership checker rejects `?`
	// while the function owns an open one, so any still reachable here is
	// either borrowed or was moved to another owner (possibly another thread).
	var ownedHandles []*HandleValue
	cleanupHandles := func(except Value) {
		for _, h := range ownedHandles {
			if except.Kind == ValHandle && except.Handle == h {
				continue
			}
			h.Close()
		}
	}

	push := func(v Value) {
		stack = append(stack, v)
	}
	pop := func() Value {
		v := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		return v
	}

	mod := vm.prog.Module
	pc := 0
	for pc < len(fp.Code) {
		w := fp.Code[pc]
		pc++
		op, a, bc, imm := DecodeInstr(w)

		switch op {
		case OpNop:
		case OpPushConst:
			c := mod.Constants[imm]
			if c.Kind == ConstInt {
				push(VInt(c.Int))
			} else {
				push(VStr(c.Str))
			}
		case OpPushInt:
			push(VInt(int64(imm)))
		case OpPushBool:
			push(VBool(a != 0))
		case OpPushNone:
			push(VNone())
		case OpPop:
			if len(stack) > 0 {
				pop()
			}
		case OpDup:
			push(stack[len(stack)-1])
		case OpLoadLocal:
			push(locals[imm])
		case OpStoreLocal:
			val := pop()
			locals[imm] = val
			if val.Kind == ValHandle && val.Handle != nil {
				switch val.Handle.Kind {
				case HandleListener, HandleStream, HandleFile:
				default:
					ownedHandles = append(ownedHandles, val.Handle)
				}
			}
		case OpLoadUpval:
			push(upvals[imm])
		case OpAdd:
			r, l := pop(), pop()
			if l.Kind == ValStr || r.Kind == ValStr {
				push(VStr(l.String() + r.String()))
			} else {
				push(VInt(l.Int + r.Int))
			}
		case OpSub:
			r, l := pop(), pop()
			push(VInt(l.Int - r.Int))
		case OpMul:
			r, l := pop(), pop()
			push(VInt(l.Int * r.Int))
		case OpDiv:
			r, l := pop(), pop()
			if r.Int == 0 {
				cleanupHandles(VVoid())
				return VVoid(), false, locals, fmt.Errorf("runtime division by zero at line %d", lineAt(fp, pc-1))
			}
			push(VInt(l.Int / r.Int))
		case OpMod:
			r, l := pop(), pop()
			if r.Int == 0 {
				cleanupHandles(VVoid())
				return VVoid(), false, locals, fmt.Errorf("runtime modulo by zero at line %d", lineAt(fp, pc-1))
			}
			push(VInt(l.Int % r.Int))
		case OpNeg:
			x := pop()
			push(VInt(-x.Int))
		case OpNot:
			x := pop()
			push(VBool(!x.IsTruthy()))
		case OpEq:
			r, l := pop(), pop()
			push(VBool(l.Equals(r)))
		case OpNeq:
			r, l := pop(), pop()
			push(VBool(!l.Equals(r)))
		case OpLt:
			r, l := pop(), pop()
			push(VBool(l.order(r) < 0))
		case OpLe:
			r, l := pop(), pop()
			push(VBool(l.order(r) <= 0))
		case OpGt:
			r, l := pop(), pop()
			push(VBool(l.order(r) > 0))
		case OpGe:
			r, l := pop(), pop()
			push(VBool(l.order(r) >= 0))
		case OpIn:
			r, l := pop(), pop()
			push(VBool(l.in(r)))
		case OpJmp:
			pc = int(imm)
		case OpJmpIfFalse:
			c := pop()
			if !c.IsTruthy() {
				pc = int(imm)
			}
		case OpJmpIfFalsePeek:
			if !stack[len(stack)-1].IsTruthy() {
				pc = int(imm)
			}
		case OpJmpIfTruePeek:
			if stack[len(stack)-1].IsTruthy() {
				pc = int(imm)
			}
		case OpMakeList:
			n := int(imm)
			els := make([]Value, n)
			for i := n - 1; i >= 0; i-- {
				els[i] = pop()
			}
			push(VList(els))
		case OpMakeMap:
			n := int(imm)
			m := make(map[string]Value, n)
			pairs := make([]struct {
				k string
				v Value
			}, n)
			for i := n - 1; i >= 0; i-- {
				val := pop()
				key := pop()
				pairs[i] = struct {
					k string
					v Value
				}{key.String(), val}
			}
			for _, pr := range pairs {
				m[pr.k] = pr.v
			}
			push(VMap(m))
		case OpMakeEntity:
			es := mod.Entities[a]
			fm := mod.FieldMetas[bc]
			fields := map[string]Value{}
			vals := make([]Value, len(fm.Names))
			for i := len(fm.Names) - 1; i >= 0; i-- {
				vals[i] = pop()
			}
			for i, name := range fm.Names {
				fields[name] = vals[i]
			}
			push(Value{Kind: ValEntity, Entity: &EntityInstance{TypeName: es.Name, Fields: fields}})
		case OpMakeVariant:
			n := int(a)
			vname := mod.Constants[bc].Str
			flds := make([]Value, n)
			for i := n - 1; i >= 0; i-- {
				flds[i] = pop()
			}
			push(Value{Kind: ValVariant, Variant: &VariantValue{Name: vname, Fields: flds}})
		case OpGetField:
			fname := mod.Constants[imm].Str
			obj := pop()
			switch obj.Kind {
			case ValEntity:
				push(obj.Entity.Fields[fname])
			case ValMap:
				push(obj.Map[fname])
			default:
				push(VVoid())
			}
		case OpSetField:
			fname := mod.Constants[imm].Str
			val := pop()
			obj := pop()
			if obj.Kind == ValEntity {
				obj.Entity.Fields[fname] = val
			} else if obj.Kind == ValMap {
				obj.Map[fname] = val
			}
		case OpGetIndex:
			idx := pop()
			obj := pop()
			if obj.Kind == ValList && obj.List != nil && idx.Int >= 0 && int(idx.Int) < len(*obj.List) {
				push((*obj.List)[idx.Int])
			} else if obj.Kind == ValMap {
				push(obj.Map[idx.String()])
			} else if obj.Kind == ValStr && idx.Int >= 0 && idx.Int < int64(len(obj.Str)) {
				push(VStr(string(obj.Str[idx.Int])))
			} else {
				push(VNone())
			}
		case OpSetIndex:
			val := pop()
			idx := pop()
			obj := pop()
			if obj.Kind == ValList && obj.List != nil && idx.Int >= 0 && int(idx.Int) < len(*obj.List) {
				(*obj.List)[idx.Int] = val
			} else if obj.Kind == ValMap {
				obj.Map[idx.String()] = val
			}
		case OpWithUpdate:
			fm := mod.FieldMetas[bc]
			vals := make([]Value, len(fm.Names))
			for i := len(fm.Names) - 1; i >= 0; i-- {
				vals[i] = pop()
			}
			base := pop()
			cpFields := map[string]Value{}
			tname := ""
			if base.Kind == ValEntity && base.Entity != nil {
				tname = base.Entity.TypeName
				for k, v := range base.Entity.Fields {
					cpFields[k] = v
				}
			}
			for i, fn := range fm.Names {
				cpFields[fn] = vals[i]
			}
			push(Value{Kind: ValEntity, Entity: &EntityInstance{TypeName: tname, Fields: cpFields}})
		case OpMakeClosure:
			nUp := int(bc)
			ups := make([]Value, nUp)
			for i := nUp - 1; i >= 0; i-- {
				ups[i] = pop()
			}
			push(Value{Kind: ValClosure, Closure: &ClosureValue{FuncIdx: int(a), Upvals: ups}})
		case OpCheckVariant:
			vname := mod.Constants[imm].Str
			subj := pop()
			ok := false
			if subj.Kind == ValVariant && subj.Variant != nil && subj.Variant.Name == vname {
				ok = true
			} else if subj.Kind == ValNone && vname == "None" {
				ok = true
			}
			push(VBool(ok))
		case OpExtractField:
			subj := pop()
			if subj.Kind == ValVariant && subj.Variant != nil && int(imm) < len(subj.Variant.Fields) {
				push(subj.Variant.Fields[imm])
			} else {
				push(VNone())
			}
		case OpFmtStr:
			n := int(imm)
			parts := make([]string, n)
			for i := n - 1; i >= 0; i-- {
				parts[i] = pop().String()
			}
			push(VStr(strings.Join(parts, "")))
		case OpTryUnwrap:
			v := pop()
			if v.Kind == ValVariant && v.Variant != nil {
				switch v.Variant.Name {
				case "Ok", "Some":
					if len(v.Variant.Fields) > 0 {
						push(v.Variant.Fields[0])
					} else {
						push(VVoid())
					}
					continue
				case "Err", "None":
					cleanupHandles(VVoid())
					return v, true, locals, nil
				}
			}
			if v.Kind == ValNone {
				cleanupHandles(VVoid())
				return v, true, locals, nil
			}
			push(v)
		case OpCallDyn:
			nArgs := int(a)
			args := make([]Value, nArgs)
			for i := nArgs - 1; i >= 0; i-- {
				args[i] = pop()
			}
			fnVal := pop()
			if fnVal.Kind != ValClosure || fnVal.Closure == nil {
				return VVoid(), false, locals, fmt.Errorf("attempt to call non-closure value %s", fnVal)
			}
			ret, err := vm.callClosure(fnVal.Closure, args)
			if err != nil {
				cleanupHandles(VVoid())
				return VVoid(), false, locals, err
			}
			push(ret)
		case OpCall:
			cm := mod.CallMetas[bc]
			args := make([]Value, cm.ArgCount)
			for i := cm.ArgCount - 1; i >= 0; i-- {
				args[i] = pop()
			}
			ret, err := vm.dispatchCall(cm, args)
			if err != nil {
				cleanupHandles(VVoid())
				return VVoid(), false, locals, err
			}
			push(ret)
		case OpRunWorkflow:
			wfName := mod.Workflows[bc].Name
			nArgs := int(a)
			args := make([]Value, nArgs)
			for i := nArgs - 1; i >= 0; i-- {
				args[i] = pop()
			}
			ret, err := vm.RunWorkflow(wfName, args)
			if err != nil {
				cleanupHandles(VVoid())
				return VVoid(), false, locals, err
			}
			push(ret)
		case OpRet:
			if a != 0 && len(stack) > 0 {
				rv := pop()
				return rv, true, locals, nil
			}
			return VVoid(), false, locals, nil
		case OpHalt:
			return VVoid(), false, locals, nil
		}
	}
	return VVoid(), false, locals, nil
}

func lineAt(fp *FuncProto, pc int) int {
	if pc >= 0 && pc < len(fp.Lines) {
		return fp.Lines[pc]
	}
	return 0
}

// RunWorkflow executes a Petri-net-verified workflow with real pool semaphores,
// monitor locks, and parallel fork/join fibers.
func (vm *VM) RunWorkflow(wfName string, args []Value) (Value, error) {
	wfc, ok := vm.prog.Workflows[wfName]
	if !ok {
		return VVoid(), fmt.Errorf("unknown workflow %q", wfName)
	}
	wp := vm.prog.Module.Workflows[vm.prog.Module.WorkflowIdx[wfName]]
	locals := make([]Value, len(wp.Params))
	for i := 0; i < len(args) && i < len(locals); i++ {
		locals[i] = args[i]
	}

	// Initialize Petri resource pool semaphores
	pools := map[string]chan struct{}{}
	for pname, capVal := range wfc.Pools {
		ch := make(chan struct{}, capVal)
		for i := int64(0); i < capVal; i++ {
			ch <- struct{}{}
		}
		pools[pname] = ch
	}

	// Run start body if present
	if wfc.StartFn != "" {
		rv, hasRet, updated, err := vm.callFuncByName(wfc.StartFn, nil, locals)
		if err != nil {
			return VVoid(), err
		}
		locals = updated
		if hasRet {
			return rv, nil
		}
	}

	cur := wfc.StartTarget
	visitedSteps := 0
	for cur != "" && cur != "done" && cur != "END" {
		visitedSteps++
		if visitedSteps > 10000 {
			return VVoid(), fmt.Errorf("workflow %s exceeded max step guard", wfName)
		}

		if st, ok := wfc.Steps[cur]; ok {
			if st.FnName != "" {
				rv, hasRet, updated, err := vm.callFuncByName(st.FnName, nil, locals)
				if err != nil {
					return VVoid(), err
				}
				locals = updated
				if hasRet {
					return rv, nil
				}
			}
			if st.Target != "" {
				cur = st.Target
				continue
			}
			if ch, hasChoice := wfc.Choices[cur]; hasChoice {
				next, err := vm.evalChoice(ch, locals)
				if err != nil {
					return VVoid(), err
				}
				cur = next
				continue
			}
			if fk := findForkAfter(wfc, cur); fk != nil {
				cur = fk.Name
				continue
			}
			if nextSt := findStepAfter(wfc, cur); nextSt != nil {
				cur = nextSt.Name
				continue
			}
			break
		}

		if ch, ok := wfc.Choices[cur]; ok {
			next, err := vm.evalChoice(ch, locals)
			if err != nil {
				return VVoid(), err
			}
			cur = next
			continue
		}

		if fk, ok := wfc.Forks[cur]; ok {
			preFork := append([]Value{}, locals...)
			type branchRes struct {
				updated []Value
				err     error
			}
			results := make([]branchRes, len(fk.Branches))
			var wg sync.WaitGroup
			for bIdx, br := range fk.Branches {
				wg.Add(1)
				go func(idx int, branch WorkflowBranchMeta) {
					defer wg.Done()
					brLocals := append([]Value{}, preFork...)
					for _, op := range branch.Ops {
						switch op.Kind {
						case 2: // acquire pool
							<-pools[op.Target]
						case 3: // release pool
							pools[op.Target] <- struct{}{}
						case 1: // sync Monitor.action
							vm.monMu.Lock()
							parts := strings.SplitN(op.Target, ".", 2)
							if len(parts) == 2 {
								if m, ok := vm.prog.Machines[parts[0]]; ok {
									vm.stepMachineLocked(m, parts[1])
								}
							}
							vm.monMu.Unlock()
						case 0: // stmt
							_, _, upd, err := vm.callFuncByName(op.FnName, nil, brLocals)
							if err != nil {
								results[idx] = branchRes{err: err}
								return
							}
							brLocals = upd
						}
					}
					results[idx] = branchRes{updated: brLocals}
				}(bIdx, br)
			}
			wg.Wait()

			// Join: merge disjoint variable updates from branches back into locals
			for _, r := range results {
				if r.err != nil {
					return VVoid(), r.err
				}
				for i := range locals {
					if i < len(r.updated) && r.updated[i].Kind != ValVoid && r.updated[i].reboundFrom(preFork[i]) {
						locals[i] = r.updated[i]
					}
				}
			}

			// Move to matching Join
			nextNode := ""
			for jName := range wfc.Joins {
				nextNode = jName
				break
			}
			if nextNode == "" {
				break
			}
			cur = nextNode
			continue
		}

		if jn, ok := wfc.Joins[cur]; ok {
			if jn.Target != "" {
				cur = jn.Target
				continue
			}
			if nextSt := findStepAfter(wfc, cur); nextSt != nil {
				cur = nextSt.Name
				continue
			}
			break
		}
		break
	}
	return VVoid(), nil
}

func (vm *VM) evalChoice(ch WorkflowChoiceMeta, locals []Value) (string, error) {
	for _, br := range ch.Branches {
		if br.IsElse {
			return br.Target, nil
		}
		res, _, _, err := vm.callFuncByName(br.GuardFn, nil, locals)
		if err != nil {
			return "", err
		}
		if res.IsTruthy() {
			return br.Target, nil
		}
	}
	return "done", nil
}

func (vm *VM) stepMachineLocked(m *ast.MachineDecl, action string) {
	cur := vm.monStates[m.Name]
	for _, st := range m.States {
		if st.Name == cur {
			for _, tr := range st.Transitions {
				if tr.Action == action {
					vm.monStates[m.Name] = tr.TargetState
					return
				}
			}
		}
	}
}

func findForkAfter(wfc *WorkflowCompiled, after string) *WorkflowForkMeta {
	for _, fk := range wfc.Forks {
		if fk.After == after {
			cp := fk
			return &cp
		}
	}
	return nil
}

func findStepAfter(wfc *WorkflowCompiled, after string) *WorkflowStepMeta {
	for _, st := range wfc.Steps {
		if st.After == after {
			cp := st
			return &cp
		}
	}
	return nil
}

func sha256Hex(s string) string {
	sum := sha256.Sum256([]byte(s))
	return hex.EncodeToString(sum[:])
}

func decodeJSONToMap(raw string) (map[string]any, error) {
	var m map[string]any
	if err := json.Unmarshal([]byte(raw), &m); err != nil {
		return nil, err
	}
	return m, nil
}

var _ = time.Millisecond
