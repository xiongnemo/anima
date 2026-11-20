package petri

import (
	"fmt"
	"reflect"
	"sort"
	"strconv"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
)

type RGEdge struct {
	TransID int
	Target  int
}

type WorkflowResult struct {
	Name              string
	Places            int
	Transitions       int
	ReachableMarkings int
	Bounded           bool
	OneSafe           bool
	StructurallyWF    bool
	OptionToComplete  bool
	ProperCompletion  bool
	NoDeadTransitions bool
	ShortCircuitL4    bool
	Sound             bool
	Net               *PetriNet
	Errors            []string
}

type Report struct {
	Workflows  []WorkflowResult
	CallErrors []string
}

func (r *Report) OK() bool {
	if len(r.CallErrors) > 0 {
		return false
	}
	for _, w := range r.Workflows {
		if !w.Sound && wantsSound(w.Net) {
			return false
		}
		if !w.Bounded || !w.OptionToComplete || !w.ProperCompletion || !w.NoDeadTransitions {
			return false
		}
		if wants1Safe(w.Net) && !w.OneSafe {
			return false
		}
	}
	return true
}

func (r *Report) Errors() []string {
	var out []string
	out = append(out, r.CallErrors...)
	for _, w := range r.Workflows {
		for _, e := range w.Errors {
			out = append(out, fmt.Sprintf("workflow %s: %s", w.Name, e))
		}
	}
	return out
}

func wantsSound(net *PetriNet) bool {
	if net == nil || len(net.VerifyFlags) == 0 {
		return true
	}
	for _, f := range net.VerifyFlags {
		if f == "sound" {
			return true
		}
	}
	return true
}

func wants1Safe(net *PetriNet) bool {
	if net == nil {
		return false
	}
	for _, f := range net.VerifyFlags {
		if f == "1_safe" {
			return true
		}
	}
	return false
}

// Verify compiles all workflows into WF-Nets, runs Karp-Miller Coverability,
// van der Aalst Soundness (Option to complete, Proper completion, Dead transitions),
// and cross-validates using the Short-Circuit Theorem (N-bar bounded & L4-live).
// Also verifies async Future/ThreadPool conservation in procedural functions.
func Verify(info *sema.ProgramInfo) *Report {
	rep := &Report{}

	for _, d := range info.Program.Decls {
		switch node := d.(type) {
		case *ast.WorkflowDecl:
			wr := verifyWorkflow(node)
			rep.Workflows = append(rep.Workflows, wr)
		case *ast.FuncDecl:
			rep.CallErrors = append(rep.CallErrors, checkAsyncResourceFutures(info, node)...)
		}
	}
	return rep
}

func verifyWorkflow(wf *ast.WorkflowDecl) WorkflowResult {
	net, err := CompileWorkflow(wf)
	if err != nil {
		return WorkflowResult{Name: wf.Name, Errors: []string{err.Error()}}
	}

	wr := WorkflowResult{
		Name:        wf.Name,
		Places:      len(net.Places),
		Transitions: len(net.Transitions),
		Net:         net,
	}

	// 1. Structural WF-Net check: every non-pool node lies on a directed path start -> done
	wr.StructurallyWF = checkStructuralWF(net)

	// 2. Karp-Miller Coverability Tree for Boundedness & 1-Safety
	cov := ComputeCoverability(net)
	wr.Bounded = cov.Bounded
	wr.OneSafe = cov.OneSafe
	if !cov.Bounded {
		wr.Errors = append(wr.Errors, fmt.Sprintf("UNBOUNDED (omega detected at places: %s)", strings.Join(cov.UnboundedPlaces, ", ")))
		return wr
	}
	if wants1Safe(net) && !cov.OneSafe {
		wr.Errors = append(wr.Errors, "NOT 1-SAFE: a control place can accumulate > 1 token concurrently")
	}

	// 3. Build Reachability Graph RG(N, M0)
	markings, edges, markIdx, ok := buildReachabilityGraph(net, 50_000)
	wr.ReachableMarkings = len(markings)
	if !ok {
		wr.Errors = append(wr.Errors, "reachability graph exceeded 50,000 markings")
		return wr
	}

	targetKey := markKey(net.TargetMark)
	targetIdx, targetReachable := markIdx[targetKey]

	// 4. Law 1: Proper Completion — whenever done >= 1, M MUST equal TargetMark (zero orphan tokens & all pools returned!)
	properOK := true
	for mid, m := range markings {
		if m[net.DonePlace] >= 1 && !equalMarkings(m, net.TargetMark) {
			properOK = false
			wr.Errors = append(wr.Errors, fmt.Sprintf("IMPROPER COMPLETION at marking #%d [%s]: token reached 'done' while residual/pool tokens remain or done > 1",
				mid, formatMarking(net, m)))
			break
		}
	}
	wr.ProperCompletion = properOK

	// 5. Law 2: Option to Complete — every reachable marking M can reach TargetMark!
	optOK := targetReachable
	if !targetReachable {
		wr.Errors = append(wr.Errors, "OPTION TO COMPLETE VIOLATED: clean final marking 'done' (with full pools restored) is unreachable")
	} else {
		canReachTarget := reverseReachable(len(markings), edges, targetIdx)
		for mid, m := range markings {
			if !canReachTarget[mid] {
				optOK = false
				wr.Errors = append(wr.Errors, fmt.Sprintf("OPTION TO COMPLETE VIOLATED (deadlock/livelock) at marking #%d [%s]: cannot reach clean completion",
					mid, formatMarking(net, m)))
				break
			}
		}
	}
	wr.OptionToComplete = optOK

	// 6. Law 3: No Dead Transitions (L1-Liveness)
	fired := make([]bool, len(net.Transitions))
	for _, es := range edges {
		for _, e := range es {
			fired[e.TransID] = true
		}
	}
	noDead := true
	for tid, tr := range net.Transitions {
		if !fired[tid] {
			noDead = false
			wr.Errors = append(wr.Errors, fmt.Sprintf("DEAD TRANSITION %q never fires in any reachable execution", tr.Name))
		}
	}
	wr.NoDeadTransitions = noDead

	// 7. Short-Circuit Theorem (N-bar = N union {t*: done -> start}):
	// N is Sound iff N-bar is Bounded AND L4-Live!
	wr.ShortCircuitL4 = verifyShortCircuitL4(net)
	if !wr.ShortCircuitL4 && len(wr.Errors) == 0 {
		wr.Errors = append(wr.Errors, "SHORT-CIRCUIT THEOREM VIOLATED: N-bar is not bounded & L4-live")
	}

	wr.Sound = wr.Bounded && wr.ProperCompletion && wr.OptionToComplete && wr.NoDeadTransitions && wr.ShortCircuitL4
	return wr
}

func checkStructuralWF(net *PetriNet) bool {
	// Forward adjacency (place <-> transition) ignoring PoolPlaces
	numP := len(net.Places)
	numT := len(net.Transitions)
	adj := map[int][]int{} // node 0..numP-1 = places, numP..numP+numT-1 = transitions
	rev := map[int][]int{}
	isPool := map[int]bool{}
	for _, pid := range net.PoolPlaces {
		isPool[pid] = true
	}
	for tid, tr := range net.Transitions {
		tnode := numP + tid
		for p, w := range tr.Pre {
			if w > 0 && !isPool[p] {
				adj[p] = append(adj[p], tnode)
				rev[tnode] = append(rev[tnode], p)
			}
		}
		for p, w := range tr.Post {
			if w > 0 && !isPool[p] {
				adj[tnode] = append(adj[tnode], p)
				rev[p] = append(rev[p], tnode)
			}
		}
	}
	reachStart := bfsNodes(net.StartPlace, adj)
	reachDone := bfsNodes(net.DonePlace, rev)
	for pid := 0; pid < numP; pid++ {
		if isPool[pid] {
			continue
		}
		if !reachStart[pid] || !reachDone[pid] {
			return false
		}
	}
	for tid := 0; tid < numT; tid++ {
		tnode := numP + tid
		if !reachStart[tnode] || !reachDone[tnode] {
			return false
		}
	}
	return true
}

func bfsNodes(start int, adj map[int][]int) map[int]bool {
	vis := map[int]bool{start: true}
	q := []int{start}
	for len(q) > 0 {
		u := q[0]
		q = q[1:]
		for _, v := range adj[u] {
			if !vis[v] {
				vis[v] = true
				q = append(q, v)
			}
		}
	}
	return vis
}

func buildReachabilityGraph(net *PetriNet, maxStates int) ([][]int, map[int][]RGEdge, map[string]int, bool) {
	markings := [][]int{append([]int{}, net.InitMarking...)}
	edges := map[int][]RGEdge{}
	markIdx := map[string]int{markKey(net.InitMarking): 0}
	q := []int{0}

	for len(q) > 0 {
		curID := q[0]
		q = q[1:]
		m := markings[curID]
		for _, tr := range net.Transitions {
			if !isEnabled(m, tr) {
				continue
			}
			nm := fireMarking(m, tr)
			k := markKey(nm)
			dstID, exists := markIdx[k]
			if !exists {
				if len(markings) >= maxStates {
					return markings, edges, markIdx, false
				}
				dstID = len(markings)
				markings = append(markings, nm)
				markIdx[k] = dstID
				q = append(q, dstID)
			}
			edges[curID] = append(edges[curID], RGEdge{TransID: tr.ID, Target: dstID})
		}
	}
	return markings, edges, markIdx, true
}

func verifyShortCircuitL4(orig *PetriNet) bool {
	// Clone PetriNet and add t*: done -> start
	sc := &PetriNet{
		Name:        orig.Name + "_shortcircuit",
		Places:      append([]Place{}, orig.Places...),
		Transitions: append([]Transition{}, orig.Transitions...),
		StartPlace:  orig.StartPlace,
		DonePlace:   orig.DonePlace,
		PoolPlaces:  append([]int{}, orig.PoolPlaces...),
		InitMarking: append([]int{}, orig.InitMarking...),
		TargetMark:  append([]int{}, orig.TargetMark...),
	}
	sc.addTrans("t_short_circuit", TransShortCircuit,
		map[int]int{sc.DonePlace: 1},
		map[int]int{sc.StartPlace: 1},
	)

	cov := ComputeCoverability(sc)
	if !cov.Bounded {
		return false
	}

	markings, edges, _, ok := buildReachabilityGraph(sc, 50_000)
	if !ok {
		return false
	}

	// Run Tarjan SCC on RG(N-bar).
	// N-bar is L4-live iff every Terminal SCC contains transitions firing ALL transitions of N-bar!
	n := len(markings)
	index := make([]int, n)
	low := make([]int, n)
	onStack := make([]bool, n)
	for i := range index {
		index[i] = -1
	}
	curIdx := 0
	var stack []int
	var sccs [][]int
	var strongConnect func(int)
	strongConnect = func(v int) {
		index[v] = curIdx
		low[v] = curIdx
		curIdx++
		stack = append(stack, v)
		onStack[v] = true
		for _, e := range edges[v] {
			if index[e.Target] == -1 {
				strongConnect(e.Target)
				if low[e.Target] < low[v] {
					low[v] = low[e.Target]
				}
			} else if onStack[e.Target] && index[e.Target] < low[v] {
				low[v] = index[e.Target]
			}
		}
		if low[v] == index[v] {
			var comp []int
			for {
				w := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				onStack[w] = false
				comp = append(comp, w)
				if w == v {
					break
				}
			}
			sccs = append(sccs, comp)
		}
	}
	strongConnect(0)

	compID := make([]int, n)
	for cid, comp := range sccs {
		for _, v := range comp {
			compID[v] = cid
		}
	}

	for cid, comp := range sccs {
		hasOut := false
		firedInSCC := make([]bool, len(sc.Transitions))
		for _, u := range comp {
			for _, e := range edges[u] {
				if compID[e.Target] != cid {
					hasOut = true
				} else {
					firedInSCC[e.TransID] = true
				}
			}
		}
		if !hasOut {
			// Terminal SCC must fire ALL transitions of sc (L4-liveness)
			for _, f := range firedInSCC {
				if !f {
					return false
				}
			}
		}
	}
	return true
}

func reverseReachable(n int, edges map[int][]RGEdge, target int) []bool {
	rev := make([][]int, n)
	for u, es := range edges {
		for _, e := range es {
			rev[e.Target] = append(rev[e.Target], u)
		}
	}
	reach := make([]bool, n)
	reach[target] = true
	q := []int{target}
	for len(q) > 0 {
		v := q[0]
		q = q[1:]
		for _, u := range rev[v] {
			if !reach[u] {
				reach[u] = true
				q = append(q, u)
			}
		}
	}
	return reach
}

func markKey(m []int) string {
	var sb strings.Builder
	for i, v := range m {
		if i > 0 {
			sb.WriteByte(',')
		}
		sb.WriteString(strconv.Itoa(v))
	}
	return sb.String()
}

func formatMarking(net *PetriNet, m []int) string {
	var parts []string
	for i, tok := range m {
		if tok > 0 {
			parts = append(parts, fmt.Sprintf("%s=%d", net.Places[i].Name, tok))
		}
	}
	return strings.Join(parts, ", ")
}

// checkAsyncResourceFutures checks the futures a function makes.
//
// A task given to a pool is waited for by the shutdown of that pool, which
// the ownership checker proves on every path. So its future need not be
// awaited: one given a name is awaited or gathered somewhere in the function
// (outside any closure), and one that is not wanted is written
// `_ = pool.submit(...)`.
//
// Nothing else waits for a request started by get_async: its future is
// awaited or gathered on every path, before the function returns and before
// its name is given another value.
func checkAsyncResourceFutures(info *sema.ProgramInfo, fn *ast.FuncDecl) []string {
	c := &futureCheck{info: info, fn: fn.Name, awaited: map[string]bool{}, seen: map[string]bool{}}
	st := newPending()
	if !c.block(fn.Body, st) {
		c.leak(st.open, "when the function ends")
	}
	for _, f := range c.tasks {
		if !c.awaited[f.name] {
			c.report(fmt.Sprintf("%s: Petri Future token leak in %s: %q created by async call was never awaited or gathered (write `_ = pool.submit(...)` to leave a task to the shutdown of its pool)", f.span, fn.Name, f.name))
		}
	}
	return c.errs
}

// pendingFutures is what a path knows of the requests it has started: those
// not awaited yet, by where they were made, and the requests each name may
// hold. Two names may hold one request, and awaiting either ends its wait.
type pendingFutures struct {
	open map[ast.Span]string // request -> the name it was made under
	held map[string][]ast.Span
}

func newPending() *pendingFutures {
	return &pendingFutures{open: map[ast.Span]string{}, held: map[string][]ast.Span{}}
}

func (p *pendingFutures) clone() *pendingFutures {
	cp := newPending()
	for k, v := range p.open {
		cp.open[k] = v
	}
	for k, v := range p.held {
		cp.held[k] = append([]ast.Span(nil), v...)
	}
	return cp
}

// become makes p what may be so on any of the paths.
func (p *pendingFutures) become(paths []*pendingFutures) {
	joined := newPending()
	for _, q := range paths {
		for sp, name := range q.open {
			joined.open[sp] = name
		}
		for name, spans := range q.held {
			for _, sp := range spans {
				if !hasSpan(joined.held[name], sp) {
					joined.held[name] = append(joined.held[name], sp)
				}
			}
		}
	}
	*p = *joined
}

// await ends the wait for every request name may hold.
func (p *pendingFutures) await(name string) {
	for _, sp := range p.held[name] {
		delete(p.open, sp)
	}
}

// drop is called when name is given another value. It returns the requests
// that no name holds any more and were not awaited.
func (p *pendingFutures) drop(name string) map[ast.Span]string {
	lost := map[ast.Span]string{}
	old := p.held[name]
	delete(p.held, name)
	for _, sp := range old {
		made, open := p.open[sp]
		if !open {
			continue
		}
		reachable := false
		for _, spans := range p.held {
			reachable = reachable || hasSpan(spans, sp)
		}
		if !reachable {
			lost[sp] = made
			delete(p.open, sp)
		}
	}
	return lost
}

func hasSpan(spans []ast.Span, sp ast.Span) bool {
	for _, have := range spans {
		if have == sp {
			return true
		}
	}
	return false
}

type namedFuture struct {
	name string
	span ast.Span
}

type futureCheck struct {
	info    *sema.ProgramInfo
	fn      string
	tasks   []namedFuture   // futures of pool tasks that were given a name
	awaited map[string]bool // names awaited or gathered outside a closure
	errs    []string
	seen    map[string]bool
}

func (c *futureCheck) report(msg string) {
	if !c.seen[msg] {
		c.seen[msg] = true
		c.errs = append(c.errs, msg)
	}
}

// leak reports the requests in open, which were not awaited.
func (c *futureCheck) leak(open map[ast.Span]string, when string) {
	spans := make([]ast.Span, 0, len(open))
	for sp := range open {
		spans = append(spans, sp)
	}
	sort.Slice(spans, func(i, j int) bool { return spans[i].String() < spans[j].String() })
	for _, sp := range spans {
		c.report(fmt.Sprintf("%s: Petri Future token leak in %s: %q created by async call is not awaited or gathered %s", sp, c.fn, open[sp], when))
	}
}

// exprs walks the expressions of a statement: an await or a gather outside a
// closure ends the wait for the futures it names. A `?` may return early,
// leaving what is still pending.
func (c *futureCheck) exprs(st *pendingFutures, nodes ...any) {
	try := false
	done := func(e ast.Expr) {
		if id, ok := e.(*ast.Ident); ok {
			c.awaited[id.Name] = true
			st.await(id.Name)
		}
	}
	for _, n := range nodes {
		visit(reflect.ValueOf(n), func(n any) bool {
			switch x := n.(type) {
			case *ast.LambdaExpr:
				// A closure runs later, if at all.
				return false
			case *ast.TryExpr:
				try = true
			case *ast.CallExpr:
				fe, ok := x.Callee.(*ast.FieldExpr)
				if !ok {
					break
				}
				switch fe.Field {
				case "await":
					done(fe.Object)
				case "gather":
					for _, a := range x.Args {
						if ll, ok := a.Value.(*ast.ListLit); ok {
							for _, el := range ll.Elems {
								done(el)
							}
						}
					}
				}
			}
			return true
		}, func(any) {})
	}
	if try {
		c.leak(st.open, "where `?` may return early")
	}
}

// block walks stmts on one path and reports whether every path through them
// returns.
func (c *futureCheck) block(stmts []ast.Stmt, st *pendingFutures) bool {
	for _, stmt := range stmts {
		switch s := stmt.(type) {
		case *ast.LetAssignStmt:
			c.exprs(st, s.Value)
			// A second name for a future holds the same requests.
			var same []ast.Span
			if id, ok := s.Value.(*ast.Ident); ok {
				same = append(same, st.held[id.Name]...)
			}
			if s.Name != "_" {
				lost := st.drop(s.Name)
				for sp := range lost {
					if hasSpan(same, sp) {
						delete(lost, sp)
						st.open[sp] = s.Name
					}
				}
				c.leak(lost, "before the name is given another value")
				if len(same) > 0 {
					st.held[s.Name] = same
				}
			}
			switch {
			case !isFutureProducer(c.info, s.Value):
			case isPoolSubmit(c.info, s.Value):
				if s.Name != "_" {
					c.tasks = append(c.tasks, namedFuture{s.Name, s.Span})
				}
			case s.Name == "_":
				c.report(fmt.Sprintf("%s: Petri Future token leak in %s: the future made here is discarded and nothing waits for it", s.Span, c.fn))
			default:
				st.open[s.Span] = s.Name
				st.held[s.Name] = []ast.Span{s.Span}
			}

		case *ast.IfStmt:
			// A condition is only reached when those before it were false.
			var live []*pendingFutures
			for _, br := range s.Branches {
				c.exprs(st, br.Cond)
				b := st.clone()
				if !c.block(br.Body, b) {
					live = append(live, b)
				}
			}
			b := st.clone()
			if !c.block(s.Else, b) {
				live = append(live, b)
			}
			if len(live) == 0 {
				return true
			}
			st.become(live)

		case *ast.MatchStmt:
			c.exprs(st, s.Subject)
			var live []*pendingFutures
			for _, arm := range s.Arms {
				b := st.clone()
				if arm.Guard != nil {
					c.exprs(b, arm.Guard)
				}
				if !c.block(arm.Body, b) {
					live = append(live, b)
				}
			}
			if len(live) == 0 && len(s.Arms) > 0 {
				return true
			}
			st.become(live)

		case *ast.WhileStmt:
			c.exprs(st, s.Cond)
			c.loop(s.Body, st)

		case *ast.ForStmt:
			c.exprs(st, s.Iterable)
			c.loop(s.Body, st)

		case *ast.ReturnStmt:
			c.exprs(st, s.Value)
			c.leak(st.open, "before this return")
			return true

		default:
			c.exprs(st, stmt)
		}
	}
	return false
}

// loop walks a loop body, which may run any number of times: a request it
// starts is awaited in the same pass, and an await in it does not count for
// a request started before the loop.
func (c *futureCheck) loop(body []ast.Stmt, st *pendingFutures) {
	b := st.clone()
	c.block(body, b)
	made := map[ast.Span]string{}
	for sp, name := range b.open {
		if _, before := st.open[sp]; !before {
			made[sp] = name
		}
	}
	c.leak(made, "in the pass of the loop that makes it")
}

// visit walks every AST node reachable from v, whatever statement or
// expression it is nested in: pre before the nodes inside it (which are
// skipped when it returns false), post after them.
func visit(v reflect.Value, pre func(any) bool, post func(any)) {
	switch v.Kind() {
	case reflect.Interface:
		if !v.IsNil() {
			visit(v.Elem(), pre, post)
		}
	case reflect.Ptr:
		if !v.IsNil() && pre(v.Interface()) {
			visit(v.Elem(), pre, post)
			post(v.Interface())
		}
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			visit(v.Field(i), pre, post)
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			visit(v.Index(i), pre, post)
		}
	}
}

// isFutureProducer reports whether e is a call that starts a task or a request.
func isFutureProducer(info *sema.ProgramInfo, e ast.Expr) bool {
	ce, ok := e.(*ast.CallExpr)
	if !ok {
		return false
	}
	if ht, ok := info.ExprTypes[e].(*sema.HandleType); ok {
		return ht.Name == "Future"
	}
	fe, ok := ce.Callee.(*ast.FieldExpr)
	return ok && (fe.Field == "get_async" || fe.Field == "submit")
}

// isPoolSubmit reports whether e is pool.submit(...) on a thread pool.
func isPoolSubmit(info *sema.ProgramInfo, e ast.Expr) bool {
	ce, ok := e.(*ast.CallExpr)
	if !ok {
		return false
	}
	fe, ok := ce.Callee.(*ast.FieldExpr)
	if !ok || fe.Field != "submit" {
		return false
	}
	ht, ok := info.ExprTypes[fe.Object].(*sema.HandleType)
	return ok && ht.Name == "conc.ThreadPool"
}
