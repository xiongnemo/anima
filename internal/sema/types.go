package sema

import (
	"fmt"
	"math"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
)

const (
	DefaultMaxInt = int64(1_000_000_000)
	DefaultMinInt = int64(-1_000_000_000)
)

type TypeKind int

const (
	KindVoid TypeKind = iota
	KindInt
	KindBool
	KindStr
	KindList
	KindMap
	KindEntity
	KindADT
	KindFunc
	KindHandle // TcpListener, TcpStream, File, ThreadPool, Channel, Mutex, Semaphore, Session, Future, ByteView
	KindPort   // User port module
	KindModule // Imported std.* module
	KindTypeVar
	KindUnknown
)

type Type interface {
	Kind() TypeKind
	String() string
	Equals(other Type) bool
}

type VoidType struct{}

func (VoidType) Kind() TypeKind     { return KindVoid }
func (VoidType) String() string     { return "void" }
func (VoidType) Equals(o Type) bool { _, ok := o.(VoidType); return ok }

type UnknownType struct{}

func (UnknownType) Kind() TypeKind     { return KindUnknown }
func (UnknownType) String() string     { return "unknown" }
func (UnknownType) Equals(o Type) bool { return true }

type TypeVar struct{ Name string }

func (t TypeVar) Kind() TypeKind { return KindTypeVar }
func (t TypeVar) String() string { return t.Name }
func (t TypeVar) Equals(o Type) bool {
	ot, ok := o.(TypeVar)
	return ok && ot.Name == t.Name
}

type IntType struct {
	Lo        int64
	Hi        int64
	IsBounded bool
	AliasName string
}

func NewUnboundedInt() *IntType {
	return &IntType{Lo: math.MinInt32, Hi: math.MaxInt32, IsBounded: false}
}

func NewIntRange(lo, hi int64, alias string) *IntType {
	return &IntType{Lo: lo, Hi: hi, IsBounded: true, AliasName: alias}
}

func (t *IntType) Kind() TypeKind { return KindInt }
func (t *IntType) String() string {
	if t.AliasName != "" {
		return t.AliasName
	}
	if t.IsBounded {
		return fmt.Sprintf("int[%d..%d]", t.Lo, t.Hi)
	}
	return "int"
}
func (t *IntType) Equals(o Type) bool {
	_, ok := o.(*IntType)
	return ok
}

type BoolType struct{}

func (BoolType) Kind() TypeKind     { return KindBool }
func (BoolType) String() string     { return "bool" }
func (BoolType) Equals(o Type) bool { _, ok := o.(BoolType); return ok }

type StrType struct{}

func (StrType) Kind() TypeKind     { return KindStr }
func (StrType) String() string     { return "str" }
func (StrType) Equals(o Type) bool { _, ok := o.(StrType); return ok }

type ListType struct {
	Elem   Type
	Cap    int64
	HasCap bool
}

func (t *ListType) Kind() TypeKind { return KindList }
func (t *ListType) String() string {
	if t.HasCap {
		return fmt.Sprintf("list[%s, cap=%d]", t.Elem, t.Cap)
	}
	return fmt.Sprintf("list[%s]", t.Elem)
}
func (t *ListType) Equals(o Type) bool {
	ol, ok := o.(*ListType)
	if !ok {
		return false
	}
	return t.Elem.Equals(ol.Elem)
}

type MapType struct {
	Key    Type
	Val    Type
	Cap    int64
	HasCap bool
}

func (t *MapType) Kind() TypeKind { return KindMap }
func (t *MapType) String() string {
	if t.HasCap {
		return fmt.Sprintf("map[%s, %s, cap=%d]", t.Key, t.Val, t.Cap)
	}
	return fmt.Sprintf("map[%s, %s]", t.Key, t.Val)
}
func (t *MapType) Equals(o Type) bool {
	om, ok := o.(*MapType)
	if !ok {
		return false
	}
	return t.Key.Equals(om.Key) && t.Val.Equals(om.Val)
}

type EntityFieldInfo struct {
	Name string
	Type Type
}

type EntityType struct {
	Name       string
	Fields     []EntityFieldInfo
	FieldMap   map[string]Type
	Relations  []ast.RelationDecl
	Invariants []ast.Expr
	Decl       *ast.EntityDecl
}

func (t *EntityType) Kind() TypeKind { return KindEntity }
func (t *EntityType) String() string { return t.Name }
func (t *EntityType) Equals(o Type) bool {
	oe, ok := o.(*EntityType)
	return ok && oe.Name == t.Name
}

type VariantInfo struct {
	Name   string
	Fields []EntityFieldInfo
}

type ADTType struct {
	Name       string
	TypeParams []string
	TypeArgs   []Type
	Variants   []VariantInfo
	VariantMap map[string]VariantInfo
	Decl       *ast.TypeDecl
}

func (t *ADTType) Kind() TypeKind { return KindADT }
func (t *ADTType) String() string {
	if len(t.TypeArgs) == 0 {
		return t.Name
	}
	var parts []string
	for _, a := range t.TypeArgs {
		parts = append(parts, a.String())
	}
	return fmt.Sprintf("%s[%s]", t.Name, strings.Join(parts, ", "))
}
func (t *ADTType) Equals(o Type) bool {
	oa, ok := o.(*ADTType)
	if !ok || oa.Name != t.Name {
		return false
	}
	if len(t.TypeArgs) == 0 || len(oa.TypeArgs) == 0 {
		return true
	}
	if len(t.TypeArgs) != len(oa.TypeArgs) {
		return false
	}
	for i := range t.TypeArgs {
		if !t.TypeArgs[i].Equals(oa.TypeArgs[i]) {
			return false
		}
	}
	return true
}

type FuncParamInfo struct {
	Name string
	Mut  bool
	Own  bool
	Type Type
}

type FuncType struct {
	Params []FuncParamInfo
	Return Type
}

func (t *FuncType) Kind() TypeKind { return KindFunc }
func (t *FuncType) String() string {
	var ps []string
	for _, p := range t.Params {
		if p.Mut {
			ps = append(ps, "mut "+p.Type.String())
		} else if p.Own {
			ps = append(ps, "own "+p.Type.String())
		} else {
			ps = append(ps, p.Type.String())
		}
	}
	return fmt.Sprintf("fn(%s) -> %s", strings.Join(ps, ", "), t.Return)
}
func (t *FuncType) Equals(o Type) bool {
	of, ok := o.(*FuncType)
	if !ok || len(of.Params) != len(t.Params) {
		return false
	}
	for i := range t.Params {
		if !t.Params[i].Type.Equals(of.Params[i].Type) {
			return false
		}
	}
	return t.Return.Equals(of.Return)
}

// HandleType represents a linear resource / handle with optional typestate protocol.
type HandleType struct {
	Name     string // e.g. "sock.TcpListener", "sock.TcpStream", "fs.File", "conc.ThreadPool"
	Elem     Type   // e.g. Channel[T] element type or Future[T]
	Cap      int64
	HasCap   bool
	Protocol *TypestateSpec
}

type TypestateSpec struct {
	InitState    string
	AcceptStates []string                     // states legal when handle drops out of scope (e.g. "Closed")
	Transitions  map[string]map[string]string // state -> method -> nextState
}

func (t *HandleType) Kind() TypeKind { return KindHandle }
func (t *HandleType) String() string {
	if t.Elem != nil {
		return fmt.Sprintf("%s[%s]", t.Name, t.Elem)
	}
	return t.Name
}
func (t *HandleType) Equals(o Type) bool {
	oh, ok := o.(*HandleType)
	return ok && oh.Name == t.Name
}

// LinearHandle returns the handle type whose ownership the typestate checker
// tracks, or nil. wrapped is true when ty is a Result/Option carrying it.
func LinearHandle(ty Type) (ht *HandleType, wrapped bool) {
	switch t := ty.(type) {
	case *HandleType:
		switch t.Name {
		case "sock.TcpListener", "sock.TcpStream", "fs.File":
			return t, false
		}
	case *ADTType:
		if (t.Name == "Result" || t.Name == "Option") && len(t.TypeArgs) > 0 {
			if h, w := LinearHandle(t.TypeArgs[0]); h != nil && !w {
				return h, true
			}
		}
	}
	return nil, false
}

type PortType struct {
	Name string
	Decl *ast.PortDecl
}

func (t *PortType) Kind() TypeKind     { return KindPort }
func (t *PortType) String() string     { return "port:" + t.Name }
func (t *PortType) Equals(o Type) bool { op, ok := o.(*PortType); return ok && op.Name == t.Name }

type ModuleType struct {
	Path  string
	Alias string
}

func (t *ModuleType) Kind() TypeKind     { return KindModule }
func (t *ModuleType) String() string     { return "module:" + t.Path }
func (t *ModuleType) Equals(o Type) bool { om, ok := o.(*ModuleType); return ok && om.Path == t.Path }

// FrameInfo summarizes automatic SPARK frame inference for a function.
type FrameInfo struct {
	Reads       []string
	Writes      []string
	PortEffects []string
}

type FuncInfo struct {
	Decl  *ast.FuncDecl
	Type  *FuncType
	Frame FrameInfo
}

type WorkflowInfo struct {
	Decl   *ast.WorkflowDecl
	Params []FuncParamInfo
	Return Type
}

// ProgramInfo holds all resolved types, symbol tables, and inferred frames.
type ProgramInfo struct {
	Program    *ast.Program
	Types      map[string]Type
	Entities   map[string]*EntityType
	ADTs       map[string]*ADTType
	Variants   map[string]*ADTType // variant name -> owning ADT
	Ports      map[string]*PortType
	Machines   map[string]*ast.MachineDecl
	Properties map[string]*ast.PropertyDecl
	Progresses map[string]*ast.ProgressDecl
	Workflows  map[string]*WorkflowInfo
	Systems    map[string]*ast.SystemDecl
	Funcs      map[string]*FuncInfo
	ExprTypes  map[ast.Expr]Type
	// LiteralTargets: the declared type a list or map literal was given to.
	// The kernel proves the literal's elements in its element range.
	LiteralTargets map[ast.Expr]Type
	// LetRanges: the range of the variable an assignment writes, when it
	// has one. The kernel proves the value assigned in it.
	LetRanges map[*ast.LetAssignStmt]*IntType
	// TimeoutArgs: the timeout_ms argument of a call that blocks on the
	// network, which the kernel proves in 1..300_000.
	TimeoutArgs map[*ast.CallExpr]ast.Expr
	Imports     map[string]string // alias -> canonical std module path
	StdHandles  map[string]*TypestateSpec
	Diagnostics []string
}
