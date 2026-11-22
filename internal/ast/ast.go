package ast

import "fmt"

// Span identifies a source file location.
type Span struct {
	File string
	Line int
	Col  int
}

func (s Span) String() string {
	if s.File == "" {
		return fmt.Sprintf("line %d:%d", s.Line, s.Col)
	}
	return fmt.Sprintf("%s:%d:%d", s.File, s.Line, s.Col)
}

// Program is the root AST node for a single .anm module.
type Program struct {
	File  string
	Decls []Decl
}

// Decl is any top-level declaration.
type Decl interface {
	declNode()
	GetSpan() Span
}

// TypeExpr represents any type annotation in Anima.
type TypeExpr interface {
	typeExprNode()
	GetSpan() Span
	String() string
}

// Stmt represents any procedural or modeling statement.
type Stmt interface {
	stmtNode()
	GetSpan() Span
}

// Expr represents any expression.
type Expr interface {
	exprNode()
	GetSpan() Span
}

// Pattern represents a match arm pattern.
type Pattern interface {
	patternNode()
	GetSpan() Span
}

// ---------------------------------------------------------------------------
// Top-level Declarations
// ---------------------------------------------------------------------------

type ImportDecl struct {
	Span  Span
	Path  string // e.g. "std.socket" or "./helper.anm"
	Alias string // e.g. "sock" or "socket"
}

func (*ImportDecl) declNode()       {}
func (d *ImportDecl) GetSpan() Span { return d.Span }

type TypeDeclKind int

const (
	TypeAlias TypeDeclKind = iota
	TypeADT
)

type VariantField struct {
	Span Span
	Name string
	Type TypeExpr
}

type VariantDecl struct {
	Span   Span
	Name   string
	Fields []VariantField
}

type TypeDecl struct {
	Span       Span
	Name       string
	TypeParams []string
	Kind       TypeDeclKind
	Alias      TypeExpr      // for TypeAlias
	Variants   []VariantDecl // for TypeADT
}

func (*TypeDecl) declNode()       {}
func (d *TypeDecl) GetSpan() Span { return d.Span }

type FieldDecl struct {
	Span Span
	Name string
	Type TypeExpr
}

type RelationDecl struct {
	Span         Span
	Name         string
	Multiplicity string // "1", "0..1", "1..*", "0..*", "1..N", etc.
	Target       string
}

type EntityDecl struct {
	Span       Span
	Name       string
	Fields     []FieldDecl
	Relations  []RelationDecl
	Invariants []Expr
}

func (*EntityDecl) declNode()       {}
func (d *EntityDecl) GetSpan() Span { return d.Span }

type Param struct {
	Span Span
	Mut  bool
	Own  bool // ownership of a linear handle is transferred to the callee
	Name string
	Type TypeExpr
}

type FuncSig struct {
	Span       Span
	Name       string
	Params     []Param
	ReturnType TypeExpr // nil means void
	FromState  string   // optional typestate pre-state for port extern def
	ToState    string   // optional typestate post-state for port extern def
}

type PortDecl struct {
	Span      Span
	Name      string
	States    []StateDecl // protocol state machine
	Externs   []FuncSig
	InitState string
}

func (*PortDecl) declNode()       {}
func (d *PortDecl) GetSpan() Span { return d.Span }

type FuncDecl struct {
	Span       Span
	Name       string
	TypeParams []string
	Params     []Param
	ReturnType TypeExpr // nil means void
	Requires   []Expr
	Ensures    []Expr
	Decreases  Expr
	Body       []Stmt
}

func (*FuncDecl) declNode()       {}
func (d *FuncDecl) GetSpan() Span { return d.Span }

type ControlVarDecl struct {
	Span Span
	Name string
	Type TypeExpr
	Init Expr
}

type TransitionDecl struct {
	Span        Span
	Action      string
	Guard       Expr   // optional `when`
	TargetState string // target state name (or "END" / "ERROR")
	Body        []Stmt
}

type StateDecl struct {
	Span        Span
	Name        string
	Invariants  []Expr
	Transitions []TransitionDecl
}

type MachineDecl struct {
	Span        Span
	Kind        string // "monitor" or "machine"
	Name        string
	ControlVars []ControlVarDecl
	States      []StateDecl
}

func (*MachineDecl) declNode()       {}
func (d *MachineDecl) GetSpan() Span { return d.Span }

type PropertyDecl struct {
	Span   Span
	Name   string
	States []StateDecl
}

func (*PropertyDecl) declNode()       {}
func (d *PropertyDecl) GetSpan() Span { return d.Span }

type ProgressDecl struct {
	Span    Span
	Name    string
	Actions []string
}

func (*ProgressDecl) declNode()       {}
func (d *ProgressDecl) GetSpan() Span { return d.Span }

type PoolDecl struct {
	Span     Span
	Name     string
	Type     TypeExpr
	Capacity int64
}

type WorkflowNode interface {
	wfNode()
	GetSpan() Span
}

type StartNode struct {
	Span   Span
	Target string
	Body   []Stmt
}

func (*StartNode) wfNode()         {}
func (n *StartNode) GetSpan() Span { return n.Span }

type StepNode struct {
	Span   Span
	Name   string
	After  string // optional `after X`
	Target string // optional `-> Y` (may be "done")
	Body   []Stmt
}

func (*StepNode) wfNode()         {}
func (n *StepNode) GetSpan() Span { return n.Span }

type ChoiceBranch struct {
	Span   Span
	Guard  Expr // nil if `else`
	IsElse bool
	Target string
}

type ChoiceNode struct {
	Span     Span
	Name     string // optional name
	After    string
	Branches []ChoiceBranch
}

func (*ChoiceNode) wfNode()         {}
func (n *ChoiceNode) GetSpan() Span { return n.Span }

type MergeNode struct {
	Span   Span
	Name   string
	Target string
	Afters []string
}

func (*MergeNode) wfNode()         {}
func (n *MergeNode) GetSpan() Span { return n.Span }

type BranchActionKind int

const (
	BranchStmt BranchActionKind = iota
	BranchSync
	BranchAcquire
	BranchRelease
	BranchStepRef
)

type BranchOp struct {
	Span   Span
	Kind   BranchActionKind
	Target string // e.g. "VaultMutex.acquire", pool name, or step name
	Stmt   Stmt   // when Kind == BranchStmt
}

type ForkBranch struct {
	Span Span
	Name string
	Ops  []BranchOp
}

type ForkNode struct {
	Span     Span
	Name     string
	After    string
	Branches []ForkBranch
}

func (*ForkNode) wfNode()         {}
func (n *ForkNode) GetSpan() Span { return n.Span }

type JoinNode struct {
	Span   Span
	Name   string
	Target string
}

func (*JoinNode) wfNode()         {}
func (n *JoinNode) GetSpan() Span { return n.Span }

type WorkflowDecl struct {
	Span        Span
	Name        string
	Params      []Param
	ReturnType  TypeExpr
	VerifyFlags []string
	Pools       []PoolDecl
	Nodes       []WorkflowNode
}

func (*WorkflowDecl) declNode()       {}
func (d *WorkflowDecl) GetSpan() Span { return d.Span }

type RelabelRule struct {
	Span Span
	From string
	To   string
}

type InstanceDecl struct {
	Span     Span
	Name     string
	TypeName string
	Bindings map[string]string // e.g. Philosopher(left=f0, right=f1)
	Relabels []RelabelRule
}

type SystemCheckKind int

const (
	CheckDeadlockFree SystemCheckKind = iota
	CheckSatisfies
	CheckLTL
)

type LTLFormula interface {
	ltlNode()
}

type LTLAlwaysEventually struct {
	Trigger  string
	Response string
}

func (*LTLAlwaysEventually) ltlNode() {}

type LTLAlways struct {
	Action string
}

func (*LTLAlways) ltlNode() {}

type LTLNever struct {
	Action string
}

func (*LTLNever) ltlNode() {}

type SystemCheck struct {
	Span    Span
	Kind    SystemCheckKind
	Target  string // for CheckSatisfies
	RawText string
	LTL     LTLFormula
}

type SystemDecl struct {
	Span        Span
	Name        string
	Instances   []InstanceDecl
	Hide        []string
	PriorityLow []string
	Checks      []SystemCheck
}

func (*SystemDecl) declNode()       {}
func (d *SystemDecl) GetSpan() Span { return d.Span }

// ---------------------------------------------------------------------------
// Type Expressions
// ---------------------------------------------------------------------------

type SimpleType struct {
	Span Span
	Name string
}

func (*SimpleType) typeExprNode()    {}
func (t *SimpleType) GetSpan() Span  { return t.Span }
func (t *SimpleType) String() string { return t.Name }

type IntRangeType struct {
	Span Span
	Lo   int64
	Hi   int64
}

func (*IntRangeType) typeExprNode()   {}
func (t *IntRangeType) GetSpan() Span { return t.Span }
func (t *IntRangeType) String() string {
	return fmt.Sprintf("int[%d..%d]", t.Lo, t.Hi)
}

type GenericType struct {
	Span   Span
	Name   string
	Args   []TypeExpr
	Cap    int64 // optional cap=N (-1 if not specified)
	HasCap bool
}

func (*GenericType) typeExprNode()   {}
func (t *GenericType) GetSpan() Span { return t.Span }
func (t *GenericType) String() string {
	out := t.Name + "["
	for i, a := range t.Args {
		if i > 0 {
			out += ", "
		}
		out += a.String()
	}
	if t.HasCap {
		out += fmt.Sprintf(", cap=%d", t.Cap)
	}
	return out + "]"
}

type FuncType struct {
	Span       Span
	Params     []TypeExpr
	ReturnType TypeExpr
}

func (*FuncType) typeExprNode()   {}
func (t *FuncType) GetSpan() Span { return t.Span }
func (t *FuncType) String() string {
	out := "fn("
	for i, p := range t.Params {
		if i > 0 {
			out += ", "
		}
		out += p.String()
	}
	out += ")"
	if t.ReturnType != nil {
		out += " -> " + t.ReturnType.String()
	}
	return out
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

type LetAssignStmt struct {
	Span     Span
	Name     string
	TypeAnno TypeExpr // nil if inferred
	Value    Expr
}

func (*LetAssignStmt) stmtNode()       {}
func (s *LetAssignStmt) GetSpan() Span { return s.Span }

type CompoundAssignStmt struct {
	Span   Span
	Target Expr   // Ident or FieldExpr or IndexExpr
	Op     string // "+=", "-=", "*="
	Value  Expr
}

func (*CompoundAssignStmt) stmtNode()       {}
func (s *CompoundAssignStmt) GetSpan() Span { return s.Span }

type FieldAssignStmt struct {
	Span   Span
	Object Expr
	Field  string
	Value  Expr
}

func (*FieldAssignStmt) stmtNode()       {}
func (s *FieldAssignStmt) GetSpan() Span { return s.Span }

type IndexAssignStmt struct {
	Span  Span
	List  Expr
	Index Expr
	Value Expr
}

func (*IndexAssignStmt) stmtNode()       {}
func (s *IndexAssignStmt) GetSpan() Span { return s.Span }

type IfBranch struct {
	Span Span
	Cond Expr
	Body []Stmt
}

type IfStmt struct {
	Span     Span
	Branches []IfBranch
	Else     []Stmt
}

func (*IfStmt) stmtNode()       {}
func (s *IfStmt) GetSpan() Span { return s.Span }

type MatchArm struct {
	Span    Span
	Pattern Pattern
	Guard   Expr // optional `if guard`
	Body    []Stmt
}

type MatchStmt struct {
	Span    Span
	Subject Expr
	Arms    []MatchArm
}

func (*MatchStmt) stmtNode()       {}
func (s *MatchStmt) GetSpan() Span { return s.Span }

type ForStmt struct {
	Span     Span
	Var      string
	Iterable Expr // either expression or RangeExpr
	Body     []Stmt
}

func (*ForStmt) stmtNode()       {}
func (s *ForStmt) GetSpan() Span { return s.Span }

type WhileStmt struct {
	Span       Span
	Cond       Expr
	Invariants []Expr
	Decreases  Expr
	Body       []Stmt
}

func (*WhileStmt) stmtNode()       {}
func (s *WhileStmt) GetSpan() Span { return s.Span }

type ReturnStmt struct {
	Span  Span
	Value Expr // nil for bare return
}

func (*ReturnStmt) stmtNode()       {}
func (s *ReturnStmt) GetSpan() Span { return s.Span }

type ExprStmt struct {
	Span Span
	Expr Expr
}

func (*ExprStmt) stmtNode()       {}
func (s *ExprStmt) GetSpan() Span { return s.Span }

type CallStmt struct {
	Span Span
	Call *CallExpr
}

func (*CallStmt) stmtNode()       {}
func (s *CallStmt) GetSpan() Span { return s.Span }

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

type WildcardPat struct{ Span Span }

func (*WildcardPat) patternNode()    {}
func (p *WildcardPat) GetSpan() Span { return p.Span }

type IntPat struct {
	Span  Span
	Value int64
}

func (*IntPat) patternNode()    {}
func (p *IntPat) GetSpan() Span { return p.Span }

type RangePat struct {
	Span Span
	Lo   int64
	Hi   int64
}

func (*RangePat) patternNode()    {}
func (p *RangePat) GetSpan() Span { return p.Span }

type BoolPat struct {
	Span  Span
	Value bool
}

func (*BoolPat) patternNode()    {}
func (p *BoolPat) GetSpan() Span { return p.Span }

type StrPat struct {
	Span  Span
	Value string
}

func (*StrPat) patternNode()    {}
func (p *StrPat) GetSpan() Span { return p.Span }

type VarPat struct {
	Span Span
	Name string
}

func (*VarPat) patternNode()    {}
func (p *VarPat) GetSpan() Span { return p.Span }

type VariantPat struct {
	Span   Span
	Name   string
	Fields []Pattern
}

func (*VariantPat) patternNode()    {}
func (p *VariantPat) GetSpan() Span { return p.Span }

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

type IntLit struct {
	Span  Span
	Value int64
}

func (*IntLit) exprNode()       {}
func (e *IntLit) GetSpan() Span { return e.Span }

type BoolLit struct {
	Span  Span
	Value bool
}

func (*BoolLit) exprNode()       {}
func (e *BoolLit) GetSpan() Span { return e.Span }

type StrLit struct {
	Span  Span
	Value string
}

func (*StrLit) exprNode()       {}
func (e *StrLit) GetSpan() Span { return e.Span }

type FStrExpr struct {
	Span  Span
	Parts []FStrPart
}

type FStrPart struct {
	IsExpr bool
	Text   string
	Expr   Expr
}

func (*FStrExpr) exprNode()       {}
func (e *FStrExpr) GetSpan() Span { return e.Span }

type NoneLit struct{ Span Span }

func (*NoneLit) exprNode()       {}
func (e *NoneLit) GetSpan() Span { return e.Span }

type Ident struct {
	Span Span
	Name string
}

func (*Ident) exprNode()       {}
func (e *Ident) GetSpan() Span { return e.Span }

type OldExpr struct {
	Span  Span
	Inner Expr
}

func (*OldExpr) exprNode()       {}
func (e *OldExpr) GetSpan() Span { return e.Span }

type UnaryExpr struct {
	Span Span
	Op   string // "-", "not"
	Expr Expr
}

func (*UnaryExpr) exprNode()       {}
func (e *UnaryExpr) GetSpan() Span { return e.Span }

type BinaryExpr struct {
	Span  Span
	Op    string // "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "==", "!=", "<", "<=", ">", ">=", "and", "or", "implies"
	Left  Expr
	Right Expr
}

func (*BinaryExpr) exprNode()       {}
func (e *BinaryExpr) GetSpan() Span { return e.Span }

type RangeExpr struct {
	Span Span
	Lo   Expr
	Hi   Expr
}

func (*RangeExpr) exprNode()       {}
func (e *RangeExpr) GetSpan() Span { return e.Span }

type FieldExpr struct {
	Span   Span
	Object Expr
	Field  string
}

func (*FieldExpr) exprNode()       {}
func (e *FieldExpr) GetSpan() Span { return e.Span }

type IndexExpr struct {
	Span  Span
	List  Expr
	Index Expr
}

func (*IndexExpr) exprNode()       {}
func (e *IndexExpr) GetSpan() Span { return e.Span }

type CallArg struct {
	Span  Span
	Name  string // optional keyword argument name
	Mut   bool
	Own   bool // `own x`: the caller gives up the handle x
	Value Expr
}

type CallExpr struct {
	Span     Span
	Callee   Expr
	TypeArgs []TypeExpr // e.g. json.decode[UpstreamQuote](...)
	Args     []CallArg
}

func (*CallExpr) exprNode()       {}
func (e *CallExpr) GetSpan() Span { return e.Span }

type LambdaExpr struct {
	Span   Span
	Params []string
	Body   Expr
}

func (*LambdaExpr) exprNode()       {}
func (e *LambdaExpr) GetSpan() Span { return e.Span }

type PipeExpr struct {
	Span  Span
	Left  Expr
	Right Expr
}

func (*PipeExpr) exprNode()       {}
func (e *PipeExpr) GetSpan() Span { return e.Span }

type TryExpr struct {
	Span  Span
	Inner Expr
}

func (*TryExpr) exprNode()       {}
func (e *TryExpr) GetSpan() Span { return e.Span }

type ListLit struct {
	Span  Span
	Elems []Expr
}

func (*ListLit) exprNode()       {}
func (e *ListLit) GetSpan() Span { return e.Span }

type MapEntry struct {
	Key   Expr
	Value Expr
}

type MapLit struct {
	Span    Span
	Entries []MapEntry
}

func (*MapLit) exprNode()       {}
func (e *MapLit) GetSpan() Span { return e.Span }

type MatchExpr struct {
	Span    Span
	Subject Expr
	Arms    []MatchExprArm
}

type MatchExprArm struct {
	Span    Span
	Pattern Pattern
	Guard   Expr
	Value   Expr
}

func (*MatchExpr) exprNode()       {}
func (e *MatchExpr) GetSpan() Span { return e.Span }

type RunWorkflowExpr struct {
	Span     Span
	Name     string
	TypeArgs []TypeExpr
	Args     []CallArg
}

func (*RunWorkflowExpr) exprNode()       {}
func (e *RunWorkflowExpr) GetSpan() Span { return e.Span }

type WithUpdateField struct {
	Name  string
	Value Expr
}

type WithExpr struct {
	Span   Span
	Base   Expr
	Fields []WithUpdateField
}

func (*WithExpr) exprNode()       {}
func (e *WithExpr) GetSpan() Span { return e.Span }
