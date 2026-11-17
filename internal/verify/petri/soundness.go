package petri

import (
	"fmt"
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
			rep.CallErrors = append(rep.CallErrors, checkAsyncResourceFutures(node)...)
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

// checkAsyncResourceFutures verifies Future tokens opened by get_async/submit are awaited or gathered,
// and ThreadPool handles are cleanly shut down before leaving scope.
func checkAsyncResourceFutures(fn *ast.FuncDecl) []string {
	var errs []string
	pendingFutures := map[string]ast.Span{}
	openPools := map[string]ast.Span{}

	var walkExpr func(ast.Expr)
	walkExpr = func(e ast.Expr) {
		if e == nil {
			return
		}
		switch x := e.(type) {
		case *ast.CallExpr:
			for _, a := range x.Args {
				walkExpr(a.Value)
			}
			if fe, ok := x.Callee.(*ast.FieldExpr); ok {
				if fe.Field == "await" {
					if id, ok := fe.Object.(*ast.Ident); ok {
						delete(pendingFutures, id.Name)
					}
				} else if fe.Field == "shutdown" {
					if id, ok := fe.Object.(*ast.Ident); ok {
						delete(openPools, id.Name)
					}
				} else if fe.Field == "gather" {
					for _, a := range x.Args {
						if ll, ok := a.Value.(*ast.ListLit); ok {
							for _, el := range ll.Elems {
								if id, ok := el.(*ast.Ident); ok {
									delete(pendingFutures, id.Name)
								}
							}
						}
					}
				}
			}
		case *ast.PipeExpr:
			walkExpr(x.Left)
			walkExpr(x.Right)
		case *ast.TryExpr:
			walkExpr(x.Inner)
		}
	}

	var walkStmts func([]ast.Stmt)
	walkStmts = func(stmts []ast.Stmt) {
		for _, s := range stmts {
			switch x := s.(type) {
			case *ast.LetAssignStmt:
				walkExpr(x.Value)
				if isFutureProducer(x.Value) {
					pendingFutures[x.Name] = x.Span
				}
				if isPoolProducer(x.Value) {
					openPools[x.Name] = x.Span
				}
			case *ast.ExprStmt:
				walkExpr(x.Expr)
			case *ast.ReturnStmt:
				walkExpr(x.Value)
			case *ast.IfStmt:
				for _, br := range x.Branches {
					walkStmts(br.Body)
				}
				walkStmts(x.Else)
			}
		}
	}
	walkStmts(fn.Body)

	for fname, sp := range pendingFutures {
		errs = append(errs, fmt.Sprintf("%s: Petri Future token leak in %s: %q created by async call was never awaited or gathered", sp, fn.Name, fname))
	}
	for pname, sp := range openPools {
		errs = append(errs, fmt.Sprintf("%s: ThreadPool %q created in %s was never shut down (pool.shutdown())", sp, pname, fn.Name))
	}
	return errs
}

func isFutureProducer(e ast.Expr) bool {
	ce, ok := e.(*ast.CallExpr)
	if !ok {
		return false
	}
	if fe, ok := ce.Callee.(*ast.FieldExpr); ok {
		return fe.Field == "get_async" || fe.Field == "submit"
	}
	return false
}

func isPoolProducer(e ast.Expr) bool {
	ce, ok := e.(*ast.CallExpr)
	if !ok {
		return false
	}
	if fe, ok := ce.Callee.(*ast.FieldExpr); ok {
		return fe.Field == "ThreadPool"
	}
	return false
}
