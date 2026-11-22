package lts

import (
	"fmt"
	"sort"
	"strconv"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
)

const ErrorState = -1

type Edge struct {
	Action     string // instance-qualified action name e.g. "w1.acquire" or "red_enter"
	BaseAction string // raw action name e.g. "acquire"
	Actor      string // originating instance e.g. "w1"
	TargetMon  string // optional monitor/resource target e.g. "VaultMutex"
	Target     int
	Hidden     bool
}

type ComponentLTS struct {
	Name        string
	IsMonitor   bool
	IsWorkflow  bool
	States      []string
	Init        int
	Terminal    map[int]bool
	Alphabet    map[string]bool
	BaseAlpha   map[string]bool
	Edges       map[int][]Edge
	ActionsInfo map[string]bool
}

type CompositeEdge struct {
	Action     string
	BaseAction string
	Actor      string
	Receiver   string
	Target     int
	Hidden     bool
}

type CompositeState struct {
	ID       int
	Vec      []int
	Labels   []string
	Terminal bool // true if all non-monitor components are in Terminal AND monitors are clean
}

type SystemLTS struct {
	SystemName  string
	Instances   []string
	Components  []*ComponentLTS
	States      []CompositeState
	Init        int
	Edges       map[int][]CompositeEdge
	Alphabet    map[string]bool
	PriorityLow map[string]bool
	HideSet     map[string]bool
}

// CompileMachine converts a MachineDecl (expanding state x control vars) into an explicit ComponentLTS.
//
// The alphabet is every action the machine is written with, in a state it
// reaches or not, under a guard that holds somewhere or nowhere: what it
// names it takes part in, and an action it never offers never happens. The
// edges are the transitions it can make.
func CompileMachine(m *ast.MachineDecl, info *sema.ProgramInfo) (*ComponentLTS, error) {
	type ctrlVar struct {
		name string
		lo   int64
		hi   int64
	}
	var cvs []ctrlVar
	initEnv := map[string]int64{}
	inRange := func(span ast.Span, env map[string]int64, when string) error {
		for _, cv := range cvs {
			if v := env[cv.name]; v < cv.lo || v > cv.hi {
				return fmt.Errorf("%s: control variable %s of %s is %d %s, outside its range %d..%d", span, cv.name, m.Name, v, when, cv.lo, cv.hi)
			}
		}
		return nil
	}
	for _, cv := range m.ControlVars {
		lo, hi, err := sema.ControlRange(cv, info.Types)
		if err != nil {
			return nil, err
		}
		// A first value is worked out with those before it, as the contract
		// kernel reads it; with none written it is the least of the range.
		initVal := lo
		if cv.Init != nil {
			if initVal, err = evalInt(cv.Init, initEnv); err != nil {
				return nil, err
			}
		}
		cvs = append(cvs, ctrlVar{name: cv.Name, lo: lo, hi: hi})
		initEnv[cv.Name] = initVal
		if err := inRange(cv.Span, initEnv, "at first"); err != nil {
			return nil, err
		}
	}

	lts := &ComponentLTS{
		Name:      m.Name,
		IsMonitor: m.Kind == "monitor",
		Terminal:  map[int]bool{},
		Alphabet:  map[string]bool{},
		BaseAlpha: map[string]bool{},
		Edges:     map[int][]Edge{},
	}

	stateKey := func(stName string, env map[string]int64) string {
		if len(cvs) == 0 {
			return stName
		}
		var parts []string
		for _, cv := range cvs {
			parts = append(parts, fmt.Sprintf("%s=%d", cv.name, env[cv.name]))
		}
		return stName + "[" + strings.Join(parts, ",") + "]"
	}

	stateIDMap := map[string]int{}
	ensureState := func(stName string, env map[string]int64) int {
		k := stateKey(stName, env)
		if id, ok := stateIDMap[k]; ok {
			return id
		}
		id := len(lts.States)
		lts.States = append(lts.States, k)
		stateIDMap[k] = id
		if stName == "END" || stName == "done" {
			lts.Terminal[id] = true
		}
		return id
	}

	if len(m.States) == 0 {
		return nil, fmt.Errorf("%s: %s %s has no states", m.Span, m.Kind, m.Name)
	}

	stateDecls := map[string]ast.StateDecl{}
	for _, st := range m.States {
		stateDecls[st.Name] = st
		for _, tr := range st.Transitions {
			lts.Alphabet[tr.Action] = true
			lts.BaseAlpha[baseAct(tr.Action)] = true
		}
	}

	// The contract kernel proves each invariant where a transition arrives,
	// so one that does not hold is of a program it refused.
	invariants := func(span ast.Span, stName string, env map[string]int64) error {
		for _, inv := range stateDecls[stName].Invariants {
			holds, err := evalBool(inv, env)
			if err != nil {
				return err
			}
			if !holds {
				return fmt.Errorf("%s: %s arrives in %s where the invariant of %s at %s does not hold", span, m.Name, stateKey(stName, env), stName, inv.GetSpan())
			}
		}
		return nil
	}

	// Initial state
	if err := invariants(m.Span, m.States[0].Name, initEnv); err != nil {
		return nil, err
	}
	lts.Init = ensureState(m.States[0].Name, initEnv)

	// BFS reachable concrete (State, ControlVars) pairs
	type workItem struct {
		stName string
		env    map[string]int64
		id     int
	}
	visited := map[int]bool{lts.Init: true}
	queue := []workItem{{stName: m.States[0].Name, env: initEnv, id: lts.Init}}

	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		sd := stateDecls[cur.stName]
		for _, tr := range sd.Transitions {
			if tr.Guard != nil {
				open, err := evalBool(tr.Guard, cur.env)
				if err != nil {
					return nil, err
				}
				if !open {
					continue
				}
			}
			nextEnv := cloneIntMap(cur.env)
			for _, bs := range tr.Body {
				if err := execStmt(bs, nextEnv); err != nil {
					return nil, err
				}
			}
			// A value outside its range would be a state the model does not
			// hold, and one after another of them a model without end.
			if err := inRange(tr.Span, nextEnv, fmt.Sprintf("after %s from %s", tr.Action, stateKey(cur.stName, cur.env))); err != nil {
				return nil, err
			}
			if err := invariants(tr.Span, tr.TargetState, nextEnv); err != nil {
				return nil, err
			}
			dstID := ensureState(tr.TargetState, nextEnv)
			act := tr.Action
			targetMon := ""
			if strings.Contains(act, ".") {
				parts := strings.SplitN(act, ".", 2)
				targetMon = parts[0]
			}
			lts.Edges[cur.id] = append(lts.Edges[cur.id], Edge{
				Action:     act,
				BaseAction: baseAct(act),
				Actor:      m.Name,
				TargetMon:  targetMon,
				Target:     dstID,
			})
			if !visited[dstID] {
				visited[dstID] = true
				queue = append(queue, workItem{stName: tr.TargetState, env: nextEnv, id: dstID})
			}
		}
	}

	return lts, nil
}

// CompileWorkflowLTS extracts the synchronization/control LTS projection of a WorkflowDecl.
func CompileWorkflowLTS(wf *ast.WorkflowDecl) *ComponentLTS {
	lts := &ComponentLTS{
		Name:       wf.Name,
		IsWorkflow: true,
		Terminal:   map[int]bool{},
		Alphabet:   map[string]bool{},
		BaseAlpha:  map[string]bool{},
		Edges:      map[int][]Edge{},
	}
	stateIDs := map[string]int{}
	getState := func(name string) int {
		if id, ok := stateIDs[name]; ok {
			return id
		}
		id := len(lts.States)
		lts.States = append(lts.States, name)
		stateIDs[name] = id
		if name == "done" || name == "END" {
			lts.Terminal[id] = true
		}
		return id
	}

	initID := getState("start")
	lts.Init = initID
	doneID := getState("done")
	lts.Terminal[doneID] = true

	nodeMap := map[string]ast.WorkflowNode{}
	var startNode *ast.StartNode
	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.StartNode:
			startNode = x
		case *ast.StepNode:
			nodeMap[x.Name] = x
		case *ast.ChoiceNode:
			if x.Name != "" {
				nodeMap[x.Name] = x
			}
			if x.After != "" {
				nodeMap["choice_after_"+x.After] = x
			}
		case *ast.ForkNode:
			nodeMap[x.Name] = x
		case *ast.JoinNode:
			nodeMap[x.Name] = x
		case *ast.MergeNode:
			nodeMap[x.Name] = x
		}
	}

	addEdge := func(from, to int, act, base, mon string) {
		if act == "" {
			act = "tau"
			base = "tau"
		}
		lts.Alphabet[act] = true
		lts.BaseAlpha[base] = true
		lts.Edges[from] = append(lts.Edges[from], Edge{
			Action: act, BaseAction: base, Actor: wf.Name, TargetMon: mon, Target: to, Hidden: act == "tau",
		})
	}

	if startNode != nil {
		addEdge(initID, getState(startNode.Target), "tau", "tau", "")
	}

	// Build outgoing maps for `after` links
	afterChoice := map[string]*ast.ChoiceNode{}
	afterSteps := map[string][]*ast.StepNode{}
	afterForks := map[string][]*ast.ForkNode{}
	var joinNodes []*ast.JoinNode
	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.ChoiceNode:
			if x.After != "" {
				afterChoice[x.After] = x
			}
		case *ast.StepNode:
			if x.After != "" {
				afterSteps[x.After] = append(afterSteps[x.After], x)
			}
		case *ast.ForkNode:
			if x.After != "" {
				afterForks[x.After] = append(afterForks[x.After], x)
			}
		case *ast.JoinNode:
			joinNodes = append(joinNodes, x)
		}
	}

	for _, n := range wf.Nodes {
		switch x := n.(type) {
		case *ast.StepNode:
			sid := getState(x.Name)
			// Collect any sync/call actions in step body
			cur := sid
			syncs := collectStmtSyncs(x.Body)
			for i, sc := range syncs {
				next := cur
				if i < len(syncs)-1 || x.Target != "" || afterChoice[x.Name] != nil || len(afterForks[x.Name]) > 0 {
					next = getState(fmt.Sprintf("%s__%d", x.Name, i+1))
				}
				addEdge(cur, next, sc.full, sc.base, sc.mon)
				cur = next
			}
			if x.Target != "" {
				addEdge(cur, getState(x.Target), x.Name, x.Name, "")
			} else if ch, ok := afterChoice[x.Name]; ok {
				for _, br := range ch.Branches {
					addEdge(cur, getState(br.Target), "tau", "tau", "")
				}
			} else if fks, ok := afterForks[x.Name]; ok {
				for _, fk := range fks {
					addEdge(cur, getState(fk.Name), "tau", "tau", "")
				}
			}
		case *ast.ChoiceNode:
			if x.Name != "" {
				cid := getState(x.Name)
				for _, br := range x.Branches {
					addEdge(cid, getState(br.Target), "tau", "tau", "")
				}
			}
			if x.After != "" {
				// If there is no explicit StepNode for x.After (e.g. `start -> check_and_lock:` followed by `choice after check_and_lock:`)
				if _, isStep := nodeMap[x.After]; !isStep {
					aid := getState(x.After)
					for _, br := range x.Branches {
						addEdge(aid, getState(br.Target), "tau", "tau", "")
					}
				}
			}
		case *ast.ForkNode:
			fid := getState(x.Name)
			if x.After != "" {
				if _, isStep := nodeMap[x.After]; !isStep {
					addEdge(getState(x.After), fid, "tau", "tau", "")
				}
			}
			// Find corresponding join node
			joinTarget := doneID
			for _, jn := range joinNodes {
				joinTarget = getState(jn.Name)
				break
			}
			// Build product interleaving of branches' ops from fid to joinTarget!
			var branchOps [][]forkOpItem
			for _, br := range x.Branches {
				var ops []forkOpItem
				for _, bo := range br.Ops {
					switch bo.Kind {
					case ast.BranchSync:
						parts := strings.SplitN(bo.Target, ".", 2)
						if len(parts) == 2 {
							ops = append(ops, forkOpItem{full: parts[1], base: parts[1], mon: parts[0]})
						} else {
							ops = append(ops, forkOpItem{full: bo.Target, base: bo.Target})
						}
					case ast.BranchAcquire:
						ops = append(ops, forkOpItem{full: "acquire_" + bo.Target, base: "acquire_" + bo.Target})
					case ast.BranchRelease:
						ops = append(ops, forkOpItem{full: "release_" + bo.Target, base: "release_" + bo.Target})
					case ast.BranchStepRef:
						ops = append(ops, forkOpItem{full: bo.Target, base: bo.Target})
					}
				}
				branchOps = append(branchOps, ops)
			}
			expandForkInterleaving(lts, getState, fid, joinTarget, x.Name, branchOps, wf.Name)

		case *ast.JoinNode:
			jid := getState(x.Name)
			if x.Target != "" {
				addEdge(jid, getState(x.Target), "join_"+x.Name, "join_"+x.Name, "")
			} else if steps, ok := afterSteps[x.Name]; ok {
				for _, st := range steps {
					addEdge(jid, getState(st.Name), "join_"+x.Name, "join_"+x.Name, "")
				}
			}
		case *ast.MergeNode:
			mid := getState(x.Name)
			if x.Target != "" {
				addEdge(mid, getState(x.Target), "tau", "tau", "")
			}
		}
	}

	return lts
}

type forkOpItem struct{ full, base, mon string }

func expandForkInterleaving(
	lts *ComponentLTS,
	getState func(string) int,
	startID, endID int,
	forkName string,
	branchOps [][]forkOpItem,
	wfName string,
) {
	if len(branchOps) == 0 {
		lts.Edges[startID] = append(lts.Edges[startID], Edge{Action: "tau", BaseAction: "tau", Actor: wfName, Target: endID, Hidden: true})
		return
	}
	vecKey := func(pc []int) string {
		var s []string
		for _, v := range pc {
			s = append(s, strconv.Itoa(v))
		}
		return strings.Join(s, "_")
	}
	isDone := func(pc []int) bool {
		for i, v := range pc {
			if v < len(branchOps[i]) {
				return false
			}
		}
		return true
	}

	initPC := make([]int, len(branchOps))
	if isDone(initPC) {
		lts.Edges[startID] = append(lts.Edges[startID], Edge{Action: "tau", BaseAction: "tau", Actor: wfName, Target: endID, Hidden: true})
		return
	}
	visited := map[string]int{vecKey(initPC): startID}
	queue := [][]int{initPC}

	for len(queue) > 0 {
		pc := queue[0]
		queue = queue[1:]
		fromID := visited[vecKey(pc)]
		for b := 0; b < len(branchOps); b++ {
			if pc[b] >= len(branchOps[b]) {
				continue
			}
			op := branchOps[b][pc[b]]
			nextPC := append([]int{}, pc...)
			nextPC[b]++
			var toID int
			if isDone(nextPC) {
				toID = endID
			} else {
				nk := vecKey(nextPC)
				if existing, ok := visited[nk]; ok {
					toID = existing
				} else {
					toID = getState(fmt.Sprintf("%s_par_%s", forkName, nk))
					visited[nk] = toID
					queue = append(queue, nextPC)
				}
			}
			lts.Alphabet[op.full] = true
			lts.BaseAlpha[op.base] = true
			lts.Edges[fromID] = append(lts.Edges[fromID], Edge{
				Action: op.full, BaseAction: op.base, Actor: wfName, TargetMon: op.mon, Target: toID, Hidden: op.full == "tau",
			})
		}
	}
}

// Compose builds the synchronous parallel composition of all instances in SystemDecl.
func Compose(sys *ast.SystemDecl, info *sema.ProgramInfo) (*SystemLTS, error) {
	n := len(sys.Instances)
	if n == 0 {
		return nil, fmt.Errorf("%s: system %s has no instances in compose", sys.Span, sys.Name)
	}

	type instMeta struct {
		name      string
		typeName  string
		comp      *ComponentLTS
		isMonitor bool
		bindings  map[string]string
		relabels  map[string]string
	}
	insts := make([]instMeta, n)
	byName := map[string]int{}
	for i, inst := range sys.Instances {
		var comp *ComponentLTS
		var err error
		if m, ok := info.Machines[inst.TypeName]; ok {
			comp, err = CompileMachine(m, info)
			if err != nil {
				return nil, err
			}
		} else if wf, ok := info.Workflows[inst.TypeName]; ok {
			comp = CompileWorkflowLTS(wf.Decl)
		} else {
			return nil, fmt.Errorf("%s: unknown instance type %q", inst.Span, inst.TypeName)
		}
		relabels := map[string]string{}
		for _, r := range inst.Relabels {
			relabels[r.From] = r.To
		}
		insts[i] = instMeta{
			name:      inst.Name,
			typeName:  inst.TypeName,
			comp:      comp,
			isMonitor: comp.IsMonitor,
			bindings:  inst.Bindings,
			relabels:  relabels,
		}
		byName[inst.Name] = i
	}

	hideSet := map[string]bool{}
	for _, h := range sys.Hide {
		hideSet[h] = true
	}
	prioLow := map[string]bool{}
	for _, p := range sys.PriorityLow {
		prioLow[p] = true
	}

	// Build reverse type -> monitor indices
	monitorsByType := map[string][]int{}
	for i, im := range insts {
		if im.isMonitor {
			monitorsByType[im.typeName] = append(monitorsByType[im.typeName], i)
		}
	}

	// Track instances referenced as bound resources (left=f0, or an action
	// f0.get, written so or relabelled to it) so they only transition when
	// synchronized with a caller, never solo! A part named by `on f0.get`
	// alone was left to do its get and put by itself, and with a fork that
	// is taken and put down by no one the philosophers were never stuck.
	isBoundResource := make([]bool, n)
	for i, im := range insts {
		for _, target := range im.bindings {
			if rIdx, ok := byName[target]; ok {
				isBoundResource[rIdx] = true
			}
		}
		for act := range writtenWith(im.comp) {
			parts := strings.SplitN(relabelled(im.relabels, act), ".", 2)
			if len(parts) != 2 {
				continue
			}
			if _, bound := im.bindings[parts[0]]; bound {
				continue
			}
			if rIdx, ok := byName[parts[0]]; ok && rIdx != i {
				isBoundResource[rIdx] = true
			}
		}
	}

	// What an action is done with is in the system. `on left.get` of a part
	// with no left, `Phil(left=f9)` of a system with no f9, and `sync Gate.go`
	// of a system with no monitor Gate would each be done alone, as often as
	// the part likes: the guards of what it names would hold nothing back.
	for i, im := range insts {
		for _, target := range sortedValues(im.bindings) {
			if rIdx, ok := byName[target]; !ok || rIdx == i {
				return nil, fmt.Errorf("%s: %s of system %s is bound to %s, which is no other part of the system", sys.Instances[i].Span, im.name, sys.Name, target)
			}
		}
		does := writtenWith(im.comp)
		if im.comp.IsWorkflow {
			for _, from := range sortedKeys(im.relabels) {
				if !does[from] {
					return nil, fmt.Errorf("%s: %s of system %s relabels %s, which is no action of %s", sys.Instances[i].Span, im.name, sys.Name, from, im.comp.Name)
				}
				// What a workflow does alone no other part holds back, so
				// `Gate.go` under the name `go` would be held back by none.
				if to := im.relabels[from]; strings.Contains(from, ".") && !strings.Contains(to, ".") {
					return nil, fmt.Errorf("%s: %s of system %s relabels %s to %s: a workflow does with a part what it is written to do with one", sys.Instances[i].Span, im.name, sys.Name, from, to)
				}
			}
		}
		with := map[string]string{}
		named := map[string]bool{}
		for act := range does {
			to := relabelled(im.relabels, act)
			if parts := strings.SplitN(to, ".", 2); len(parts) == 2 {
				with[parts[0]] = to
				named[parts[0]] = named[parts[0]] || to != act
			}
		}
		// A monitor, and a part other parts do their actions with, moves
		// only with the part that calls it. Its own `on b.put` would be
		// matched to a caller's put with b left where it is.
		if im.isMonitor || isBoundResource[i] {
			if names := sortedKeys(with); len(names) > 0 {
				what := "other parts do their actions with it"
				if im.isMonitor {
					what = "it is a monitor"
				}
				return nil, fmt.Errorf("%s: %s of system %s does %s, and %s: it moves only with the part that calls it, and calls none", sys.Instances[i].Span, im.name, sys.Name, with[names[0]], what)
			}
			continue
		}
		for _, name := range sortedKeys(with) {
			_, bound := im.bindings[name]
			rIdx, part := byName[name]
			if part && !bound && rIdx == i {
				return nil, fmt.Errorf("%s: %s of system %s does %s with itself", sys.Instances[i].Span, im.name, sys.Name, with[name])
			}
			// `Gate.go` names a monitor by its type, and is done with one.
			if mons := monitorsByType[name]; !bound && !part && len(mons) > 1 {
				return nil, fmt.Errorf("%s: %s of system %s does %s with the monitor %s, and the system has two: %s and %s", sys.Instances[i].Span, im.name, sys.Name, with[name], name, insts[mons[0]].name, insts[mons[1]].name)
			}
			_, declared := info.Machines[name]
			// A workflow calls methods of its values too: `xs.append(1)`.
			// The name a relabel gives an action is of no value of it.
			if bound || part || len(monitorsByType[name]) > 0 || (im.comp.IsWorkflow && !declared && !named[name]) {
				continue
			}
			what := "bound to no part of the system"
			if m, ok := info.Machines[name]; ok {
				what = "a " + m.Kind + " the system has no part of"
				if m.Kind != "monitor" {
					what = "a " + m.Kind + " and no monitor"
				}
			}
			return nil, fmt.Errorf("%s: %s of system %s does %s with %s, which is %s", sys.Instances[i].Span, im.name, sys.Name, with[name], name, what)
		}
	}

	isCleanTerminal := func(vec []int) bool {
		hasActor := false
		for i, im := range insts {
			if im.isMonitor || isBoundResource[i] {
				if vec[i] != im.comp.Init {
					return false
				}
				continue
			}
			hasActor = true
			if !im.comp.Terminal[vec[i]] {
				return false
			}
		}
		return hasActor
	}

	stateKey := func(vec []int) string {
		var sb strings.Builder
		for i, v := range vec {
			if i > 0 {
				sb.WriteByte('|')
			}
			sb.WriteString(strconv.Itoa(v))
		}
		return sb.String()
	}

	vecLabels := func(vec []int) []string {
		out := make([]string, n)
		for i, v := range vec {
			out[i] = insts[i].name + "=" + insts[i].comp.States[v]
		}
		return out
	}

	sysLTS := &SystemLTS{
		SystemName:  sys.Name,
		Instances:   make([]string, n),
		Components:  make([]*ComponentLTS, n),
		Edges:       map[int][]CompositeEdge{},
		Alphabet:    map[string]bool{},
		PriorityLow: prioLow,
		HideSet:     hideSet,
	}
	for i, im := range insts {
		sysLTS.Instances[i] = im.name
		sysLTS.Components[i] = im.comp
	}

	initVec := make([]int, n)
	for i, im := range insts {
		initVec[i] = im.comp.Init
	}
	initCS := CompositeState{
		ID:       0,
		Vec:      initVec,
		Labels:   vecLabels(initVec),
		Terminal: isCleanTerminal(initVec),
	}
	sysLTS.States = append(sysLTS.States, initCS)
	sysLTS.Init = 0

	visited := map[string]int{stateKey(initVec): 0}
	queue := []int{0}

	const maxCompositeStates = 100_000
	for len(queue) > 0 {
		sid := queue[0]
		queue = queue[1:]
		vec := sysLTS.States[sid].Vec

		type candTransition struct {
			action   string
			base     string
			actor    string
			receiver string
			nextVec  []int
			hidden   bool
			isLow    bool
		}
		var cands []candTransition

		// Resolve each component's enabled edges at current state
		for i, im := range insts {
			// Monitors and bound resources are passive: they transition strictly when driven by a caller.
			if im.isMonitor || isBoundResource[i] {
				continue
			}
			edges := im.comp.Edges[vec[i]]
			for _, e := range edges {
				act := doneAs(im.relabels, e)
				base := baseAct(act)
				// What the action is done with is in the name the instance
				// gives it: `Gate.go` relabelled to `go` is with no monitor,
				// and `go` relabelled to `Gate.go` is with the monitor Gate.
				targetMon := ""
				if parts := strings.SplitN(act, ".", 2); len(parts) == 2 {
					targetMon = parts[0]
				}

				// Check binding mapping e.g. left.get -> f0.get when left=f0
				receiver := ""
				if strings.Contains(act, ".") {
					parts := strings.SplitN(act, ".", 2)
					if boundName, ok := im.bindings[parts[0]]; ok {
						receiver = boundName
						base = parts[1]
					} else if _, exists := byName[parts[0]]; exists {
						receiver = parts[0]
						base = parts[1]
					}
				}

				// Case 1: Internal tau move
				if act == "tau" {
					nv := append([]int{}, vec...)
					nv[i] = e.Target
					cands = append(cands, candTransition{
						action: "tau", base: "tau", actor: im.name, nextVec: nv, hidden: true,
					})
					continue
				}

				// Case 2: Bound resource synchronization (e.g. p0: Philosopher(left=f0))
				if receiver != "" {
					rIdx := byName[receiver]
					rComp := insts[rIdx].comp
					for _, re := range rComp.Edges[vec[rIdx]] {
						if ra := relabelled(insts[rIdx].relabels, re.Action); ra == base {
							nv := append([]int{}, vec...)
							nv[i] = e.Target
							nv[rIdx] = re.Target
							qual := im.name + "." + base
							isHid := hideSet[qual] || hideSet[base]
							isLow := prioLow[qual] || prioLow[base]
							cands = append(cands, candTransition{
								action: qual, base: base, actor: im.name, receiver: receiver,
								nextVec: nv, hidden: isHid, isLow: isLow,
							})
						}
					}
					continue
				}

				// Case 3: Monitor synchronization (e.g. workflow sync VaultMutex.acquire)
				if targetMon != "" {
					if mIndices, ok := monitorsByType[targetMon]; ok && len(mIndices) > 0 {
						mIdx := mIndices[0]
						mComp := insts[mIdx].comp
						for _, me := range mComp.Edges[vec[mIdx]] {
							if ma := relabelled(insts[mIdx].relabels, me.Action); ma == base {
								nv := append([]int{}, vec...)
								nv[i] = e.Target
								nv[mIdx] = me.Target
								qual := im.name + "." + base
								isHid := hideSet[qual] || hideSet[base]
								isLow := prioLow[qual] || prioLow[base]
								cands = append(cands, candTransition{
									action: qual, base: base, actor: im.name, receiver: insts[mIdx].name,
									nextVec: nv, hidden: isHid, isLow: isLow,
								})
							}
						}
						continue
					}
				}

				// Case 4: Standard FSP multi-way rendezvous across all non-target-mon peers sharing `act` in alphabet.
				// Note: If `im` itself IS a monitor, let active peers drive the shared transition so we don't duplicate!
				if im.isMonitor {
					// Check if any non-monitor peer has `act` in its alphabet
					drivenByPeer := false
					for j, pm := range insts {
						if j != i && !pm.isMonitor && pm.comp.Alphabet[act] {
							drivenByPeer = true
							break
						}
					}
					if drivenByPeer {
						continue
					}
				}

				// Find all peers j != i whose alphabet contains act (with their relabels applied)
				// Workflow-internal actions (non-monitor, non-bound) remain local to that workflow instance!
				var syncParticipants []int
				possible := true
				if !im.comp.IsWorkflow {
					for j, pm := range insts {
						if j == i || pm.comp.IsWorkflow {
							continue
						}
						if hasAction(pm.comp, pm.relabels, act) {
							syncParticipants = append(syncParticipants, j)
						}
					}
				}

				// Compute Cartesian product of matching edges across syncParticipants
				nextVecs := [][]int{append([]int{}, vec...)}
				nextVecs[0][i] = e.Target
				var receiverName string
				for _, pj := range syncParticipants {
					if insts[pj].isMonitor && receiverName == "" {
						receiverName = insts[pj].name
					}
					var pTargets []int
					for _, pe := range insts[pj].comp.Edges[vec[pj]] {
						pAct := pe.Action
						if rep, ok := insts[pj].relabels[pAct]; ok {
							pAct = rep
						}
						if pAct == act {
							pTargets = append(pTargets, pe.Target)
						}
					}
					if len(pTargets) == 0 {
						possible = false
						break
					}
					var expanded [][]int
					for _, nv := range nextVecs {
						for _, pt := range pTargets {
							cp := append([]int{}, nv...)
							cp[pj] = pt
							expanded = append(expanded, cp)
						}
					}
					nextVecs = expanded
				}
				if !possible {
					continue
				}
				qual := act
				if im.comp.IsWorkflow && !strings.Contains(act, ".") {
					qual = im.name + "." + act
				}
				isHid := hideSet[act] || hideSet[base] || hideSet[im.name+"."+base]
				isLow := prioLow[act] || prioLow[base] || prioLow[im.name+"."+base]
				for _, nv := range nextVecs {
					cands = append(cands, candTransition{
						action: qual, base: base, actor: im.name, receiver: receiverName,
						nextVec: nv, hidden: isHid, isLow: isLow,
					})
				}
			}
		}

		// Apply priority_low pruning if any non-low-priority transition exists
		hasHigh := false
		for _, c := range cands {
			if !c.isLow {
				hasHigh = true
				break
			}
		}

		for _, c := range cands {
			if hasHigh && c.isLow {
				continue
			}
			nk := stateKey(c.nextVec)
			dstID, seen := visited[nk]
			if !seen {
				if len(sysLTS.States) >= maxCompositeStates {
					return nil, fmt.Errorf("LTS state space exceeded %d states in system %s", maxCompositeStates, sys.Name)
				}
				dstID = len(sysLTS.States)
				sysLTS.States = append(sysLTS.States, CompositeState{
					ID:       dstID,
					Vec:      c.nextVec,
					Labels:   vecLabels(c.nextVec),
					Terminal: isCleanTerminal(c.nextVec),
				})
				visited[nk] = dstID
				queue = append(queue, dstID)
			}
			actLabel := c.action
			if c.hidden {
				actLabel = "tau"
			}
			sysLTS.Alphabet[actLabel] = true
			sysLTS.Edges[sid] = append(sysLTS.Edges[sid], CompositeEdge{
				Action:     actLabel,
				BaseAction: c.base,
				Actor:      c.actor,
				Receiver:   c.receiver,
				Target:     dstID,
				Hidden:     c.hidden,
			})
		}
	}

	return sysLTS, nil
}

// relabelled is the name an instance with relabels gives the action act.
func relabelled(relabels map[string]string, act string) string {
	if to, ok := relabels[act]; ok {
		return to
	}
	return act
}

func sortedKeys(m map[string]string) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

func sortedValues(m map[string]string) []string {
	out := make([]string, 0, len(m))
	for _, v := range m {
		out = append(out, v)
	}
	sort.Strings(out)
	return out
}

// hasAction reports whether target is in the alphabet of comp as an instance
// with relabels: the actions of comp, each under the name the instance gives
// it. An action relabelled away is not in it.
func hasAction(comp *ComponentLTS, relabels map[string]string, target string) bool {
	for act := range comp.Alphabet {
		if relabelled(relabels, act) == target {
			return true
		}
	}
	return false
}

// doneAs is the name an instance does an edge under: a `sync Gate.go` of a
// workflow is Gate.go, and a relabel gives an action another name.
func doneAs(relabels map[string]string, e Edge) string {
	act := e.Action
	if e.TargetMon != "" && !strings.Contains(act, ".") {
		act = e.TargetMon + "." + act
	}
	return relabelled(relabels, act)
}

// writtenWith is every action a part is written with, under the names its
// machine gives them: the alphabet of a machine, and what the edges of a
// workflow do.
func writtenWith(comp *ComponentLTS) map[string]bool {
	if !comp.IsWorkflow {
		return comp.Alphabet
	}
	does := map[string]bool{}
	for _, edges := range comp.Edges {
		for _, e := range edges {
			does[doneAs(nil, e)] = true
		}
	}
	return does
}

func baseAct(a string) string {
	if idx := strings.LastIndex(a, "."); idx >= 0 {
		return a[idx+1:]
	}
	return a
}

type syncCall struct {
	full string
	base string
	mon  string
}

func collectStmtSyncs(stmts []ast.Stmt) []syncCall {
	var out []syncCall
	for _, s := range stmts {
		switch x := s.(type) {
		case *ast.ExprStmt:
			if ce, ok := x.Expr.(*ast.CallExpr); ok {
				if fe, ok := ce.Callee.(*ast.FieldExpr); ok {
					if id, ok := fe.Object.(*ast.Ident); ok {
						out = append(out, syncCall{full: id.Name + "." + fe.Field, base: fe.Field, mon: id.Name})
					}
				}
			}
		}
	}
	return out
}

func cloneIntMap(m map[string]int64) map[string]int64 {
	cp := make(map[string]int64, len(m))
	for k, v := range m {
		cp[k] = v
	}
	return cp
}

// SortedAlphabet returns deterministic ordered action list.
func (s *SystemLTS) SortedAlphabet() []string {
	out := make([]string, 0, len(s.Alphabet))
	for a := range s.Alphabet {
		out = append(out, a)
	}
	sort.Strings(out)
	return out
}
