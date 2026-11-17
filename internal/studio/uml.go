package studio

import (
	"fmt"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/lts"
	"github.com/xiongnemo/anima/internal/verify/petri"
	"github.com/xiongnemo/anima/internal/verify/spark"
)

// FormatUML renders all 4 UML views (Class/Composite, Statechart, Activity/Petri, Sequence CEX)
// in either "mermaid" or "dot" (Graphviz) format.
func FormatUML(info *sema.ProgramInfo, sparkRep *spark.Report, ltsRep *lts.Report, petriRep *petri.Report, format string) string {
	if strings.EqualFold(format, "dot") {
		return formatDOT(info, ltsRep, petriRep)
	}
	return formatMermaid(info, ltsRep, petriRep)
}

func formatMermaid(info *sema.ProgramInfo, ltsRep *lts.Report, petriRep *petri.Report) string {
	var sb strings.Builder

	// 1. UML Class & Composite Structure Diagram
	sb.WriteString("# UML View 1: Class & System Composite Structure\n```mermaid\nclassDiagram\n")
	for _, d := range info.Program.Decls {
		switch x := d.(type) {
		case *ast.EntityDecl:
			sb.WriteString(fmt.Sprintf("    class %s {\n", x.Name))
			for _, f := range x.Fields {
				sb.WriteString(fmt.Sprintf("        +%s %s\n", f.Type.String(), f.Name))
			}
			for _, inv := range x.Invariants {
				sb.WriteString(fmt.Sprintf("        <<invariant: %s>>\n", summarizeExpr(inv)))
			}
			sb.WriteString("    }\n")
			for _, rel := range x.Relations {
				sb.WriteString(fmt.Sprintf("    %s \"1\" --> \"%s\" %s : %s\n", x.Name, rel.Multiplicity, rel.Target, rel.Name))
			}
		case *ast.TypeDecl:
			if x.Kind == ast.TypeADT {
				sb.WriteString(fmt.Sprintf("    class %s {\n        <<ADT>>\n", x.Name))
				for _, vr := range x.Variants {
					sb.WriteString(fmt.Sprintf("        +%s\n", vr.Name))
				}
				sb.WriteString("    }\n")
			}
		case *ast.PortDecl:
			sb.WriteString(fmt.Sprintf("    class %s {\n        <<port>>\n", x.Name))
			for _, ex := range x.Externs {
				sb.WriteString(fmt.Sprintf("        +%s()\n", ex.Name))
			}
			sb.WriteString("    }\n")
		case *ast.MachineDecl:
			sb.WriteString(fmt.Sprintf("    class %s {\n        <<%s>>\n", x.Name, x.Kind))
			for _, cv := range x.ControlVars {
				sb.WriteString(fmt.Sprintf("        -%s %s\n", cv.Type.String(), cv.Name))
			}
			sb.WriteString("    }\n")
		case *ast.WorkflowDecl:
			sb.WriteString(fmt.Sprintf("    class %s {\n        <<workflow>>\n", x.Name))
			for _, pl := range x.Pools {
				sb.WriteString(fmt.Sprintf("        +pool %s = %d\n", pl.Name, pl.Capacity))
			}
			sb.WriteString("    }\n")
		case *ast.SystemDecl:
			sb.WriteString(fmt.Sprintf("    class %s {\n        <<system>>\n    }\n", x.Name))
			for _, inst := range x.Instances {
				sb.WriteString(fmt.Sprintf("    %s *-- \"1\" %s : %s\n", x.Name, inst.TypeName, inst.Name))
			}
		}
	}
	sb.WriteString("```\n\n")

	// 2. UML Statechart Diagrams (Monitors, Machines, Ports, Properties)
	sb.WriteString("# UML View 2: Statechart Diagrams (LTS / FSP)\n")
	for _, d := range info.Program.Decls {
		switch x := d.(type) {
		case *ast.MachineDecl:
			sb.WriteString(fmt.Sprintf("## %s (%s)\n```mermaid\nstateDiagram-v2\n", x.Name, x.Kind))
			if len(x.States) > 0 {
				sb.WriteString(fmt.Sprintf("    [*] --> %s\n", x.States[0].Name))
			}
			for _, st := range x.States {
				for _, tr := range st.Transitions {
					lbl := tr.Action
					if tr.Guard != nil {
						lbl += " [" + summarizeExpr(tr.Guard) + "]"
					}
					sb.WriteString(fmt.Sprintf("    %s --> %s : %s\n", st.Name, tr.TargetState, lbl))
				}
			}
			sb.WriteString("```\n\n")
		case *ast.PortDecl:
			if len(x.States) > 0 {
				sb.WriteString(fmt.Sprintf("## %s (port typestate)\n```mermaid\nstateDiagram-v2\n", x.Name))
				sb.WriteString(fmt.Sprintf("    [*] --> %s\n", x.States[0].Name))
				for _, st := range x.States {
					for _, tr := range st.Transitions {
						sb.WriteString(fmt.Sprintf("    %s --> %s : %s\n", st.Name, tr.TargetState, tr.Action))
					}
				}
				sb.WriteString("```\n\n")
			}
		}
	}

	// 3. UML Activity / Petri Net Diagram
	sb.WriteString("# UML View 3: Activity & Petri Workflow Nets\n")
	if petriRep != nil {
		for _, w := range petriRep.Workflows {
			if w.Net == nil {
				continue
			}
			sb.WriteString(fmt.Sprintf("## Workflow %s (sound=%v, 1_safe=%v, short_circuit_L4=%v)\n```mermaid\nflowchart TD\n",
				w.Name, w.Sound, w.OneSafe, w.ShortCircuitL4))
			for _, pl := range w.Net.Places {
				shape := fmt.Sprintf("p%d([%s])", pl.ID, pl.Name)
				if pl.Kind == petri.PlacePool {
					shape = fmt.Sprintf("p%d[(pool: %s = %d)]", pl.ID, strings.TrimPrefix(pl.Name, "pool:"), pl.InitTokens)
				}
				sb.WriteString("    " + shape + "\n")
			}
			for _, tr := range w.Net.Transitions {
				sb.WriteString(fmt.Sprintf("    t%d[\"%s\"]\n", tr.ID, tr.Name))
				for p := range tr.Pre {
					sb.WriteString(fmt.Sprintf("    p%d --> t%d\n", p, tr.ID))
				}
				for p := range tr.Post {
					sb.WriteString(fmt.Sprintf("    t%d --> p%d\n", tr.ID, p))
				}
			}
			sb.WriteString("```\n\n")
		}
	}

	// 4. UML Sequence Diagram (Counterexample Trace)
	sb.WriteString("# UML View 4: Verification Sequence Trace\n")
	hasCex := false
	if ltsRep != nil {
		for _, sr := range ltsRep.Systems {
			for _, cex := range sr.Failures {
				hasCex = true
				sb.WriteString(FormatSequenceMermaid(&cex))
				sb.WriteString("\n")
			}
		}
	}
	if !hasCex {
		sb.WriteString("```mermaid\nsequenceDiagram\n    Note over System: All formal verification checks PASSED (0 counterexamples)\n```\n")
	}
	return sb.String()
}

// FormatSequenceMermaid renders an LTS/Petri counterexample SequenceTrace as a Mermaid sequenceDiagram.
func FormatSequenceMermaid(cex *lts.SequenceTrace) string {
	var sb strings.Builder
	sb.WriteString("```mermaid\nsequenceDiagram\n")
	for _, p := range cex.Participants {
		sb.WriteString(fmt.Sprintf("    participant %s\n", p))
	}
	for i, step := range cex.Steps {
		if i == cex.CycleStartIdx {
			sb.WriteString("    loop Fair Cycle (Starvation / Livelock)\n")
		}
		recv := step.Receiver
		if recv == "" {
			recv = step.Actor
		}
		if step.Actor == "" {
			step.Actor = "System"
		}
		sb.WriteString(fmt.Sprintf("    %s->>%s: %s\n", step.Actor, recv, step.Action))
	}
	if cex.CycleStartIdx >= 0 {
		sb.WriteString("    end\n")
	}
	if cex.Violation != "" && len(cex.Participants) > 0 {
		first := cex.Participants[0]
		last := cex.Participants[len(cex.Participants)-1]
		sb.WriteString(fmt.Sprintf("    Note over %s,%s: %s\n", first, last, cex.Violation))
	}
	sb.WriteString("```\n")
	return sb.String()
}

func formatDOT(info *sema.ProgramInfo, ltsRep *lts.Report, petriRep *petri.Report) string {
	var sb strings.Builder
	sb.WriteString("digraph AnimaModel {\n")
	sb.WriteString("  bgcolor=\"#16161e\";\n")
	sb.WriteString("  node [style=filled, fillcolor=\"#1e2030\", color=\"#82aaff\", fontcolor=\"#c8d3f5\", fontname=\"monospace\"];\n")
	sb.WriteString("  edge [color=\"#c099ff\", fontcolor=\"#c8d3f5\", fontname=\"monospace\"];\n")

	for _, d := range info.Program.Decls {
		if m, ok := d.(*ast.MachineDecl); ok {
			sb.WriteString(fmt.Sprintf("  subgraph cluster_%s {\n    label=\"%s (%s)\"; color=\"#82aaff\"; fontcolor=\"#82aaff\";\n", m.Name, m.Name, m.Kind))
			for _, st := range m.States {
				for _, tr := range st.Transitions {
					sb.WriteString(fmt.Sprintf("    \"%s_%s\" -> \"%s_%s\" [label=\"%s\"];\n", m.Name, st.Name, m.Name, tr.TargetState, tr.Action))
				}
			}
			sb.WriteString("  }\n")
		}
	}
	if petriRep != nil {
		for _, w := range petriRep.Workflows {
			if w.Net == nil {
				continue
			}
			sb.WriteString(fmt.Sprintf("  subgraph cluster_wf_%s {\n    label=\"workflow %s\"; color=\"#c3e88d\"; fontcolor=\"#c3e88d\";\n", w.Name, w.Name))
			for _, pl := range w.Net.Places {
				shape := "circle"
				if pl.Kind == petri.PlacePool {
					shape = "box3d"
				}
				sb.WriteString(fmt.Sprintf("    \"%s_p%d\" [label=\"%s (%d)\", shape=%s];\n", w.Name, pl.ID, pl.Name, pl.InitTokens, shape))
			}
			for _, tr := range w.Net.Transitions {
				sb.WriteString(fmt.Sprintf("    \"%s_t%d\" [label=\"%s\", shape=box];\n", w.Name, tr.ID, tr.Name))
				for p := range tr.Pre {
					sb.WriteString(fmt.Sprintf("    \"%s_p%d\" -> \"%s_t%d\";\n", w.Name, p, w.Name, tr.ID))
				}
				for p := range tr.Post {
					sb.WriteString(fmt.Sprintf("    \"%s_t%d\" -> \"%s_p%d\";\n", w.Name, tr.ID, w.Name, p))
				}
			}
			sb.WriteString("  }\n")
		}
	}
	_ = ltsRep
	sb.WriteString("}\n")
	return sb.String()
}

func summarizeExpr(expr ast.Expr) string {
	switch e := expr.(type) {
	case *ast.IntLit:
		return fmt.Sprintf("%d", e.Value)
	case *ast.BoolLit:
		if e.Value {
			return "True"
		}
		return "False"
	case *ast.Ident:
		return e.Name
	case *ast.FieldExpr:
		return summarizeExpr(e.Object) + "." + e.Field
	case *ast.UnaryExpr:
		return e.Op + " " + summarizeExpr(e.Expr)
	case *ast.BinaryExpr:
		return summarizeExpr(e.Left) + " " + e.Op + " " + summarizeExpr(e.Right)
	}
	return "..."
}

// ---------------------------------------------------------------------------
// Structured JSON Graph Model for Offline Interactive Dark Studio SVG Canvas
// ---------------------------------------------------------------------------

type ClassNodeJSON struct {
	Name       string   `json:"name"`
	Kind       string   `json:"kind"`
	Fields     []string `json:"fields"`
	Invariants []string `json:"invariants"`
}

type ClassEdgeJSON struct {
	From  string `json:"from"`
	To    string `json:"to"`
	Label string `json:"label"`
}

type StateNodeJSON struct {
	ID   string `json:"id"`
	Init bool   `json:"init"`
}

type StateEdgeJSON struct {
	From  string `json:"from"`
	To    string `json:"to"`
	Label string `json:"label"`
}

type MachineGraphJSON struct {
	Name   string          `json:"name"`
	Kind   string          `json:"kind"`
	States []StateNodeJSON `json:"states"`
	Edges  []StateEdgeJSON `json:"edges"`
}

type PetriPlaceJSON struct {
	ID         int    `json:"id"`
	Name       string `json:"name"`
	Kind       string `json:"kind"`
	InitTokens int    `json:"init_tokens"`
}

type PetriTransJSON struct {
	ID   int    `json:"id"`
	Name string `json:"name"`
	Pre  []int  `json:"pre"`
	Post []int  `json:"post"`
}

type PetriGraphJSON struct {
	Name        string           `json:"name"`
	Sound       bool             `json:"sound"`
	OneSafe     bool             `json:"one_safe"`
	Places      []PetriPlaceJSON `json:"places"`
	Transitions []PetriTransJSON `json:"transitions"`
}

type StudioModelJSON struct {
	OK          bool                `json:"ok"`
	ParseError  string              `json:"parse_error,omitempty"`
	SparkProved int                 `json:"spark_proved"`
	SparkFailed int                 `json:"spark_failed"`
	SparkErrors []string            `json:"spark_errors"`
	LTSErrors   []string            `json:"lts_errors"`
	PetriErrors []string            `json:"petri_errors"`
	VCs         []spark.VCRecord    `json:"vcs"`
	Classes     []ClassNodeJSON     `json:"classes"`
	ClassEdges  []ClassEdgeJSON     `json:"class_edges"`
	Machines    []MachineGraphJSON  `json:"machines"`
	PetriNets   []PetriGraphJSON    `json:"petri_nets"`
	Failures    []lts.SequenceTrace `json:"failures"`
	Mermaid     string              `json:"mermaid"`
	FSP         string              `json:"fsp"`
	PNML        string              `json:"pnml"`
	Disasm      string              `json:"disasm"`
}

func BuildStudioModel(info *sema.ProgramInfo, sparkRep *spark.Report, ltsRep *lts.Report, petriRep *petri.Report, disasm string) StudioModelJSON {
	out := StudioModelJSON{
		OK:          sparkRep.OK() && ltsRep.OK() && petriRep.OK(),
		SparkProved: sparkRep.Proved,
		SparkFailed: sparkRep.Failed,
		SparkErrors: sparkRep.Errors(),
		LTSErrors:   ltsRep.Errors(),
		PetriErrors: petriRep.Errors(),
		VCs:         sparkRep.VCs,
		Mermaid:     FormatUML(info, sparkRep, ltsRep, petriRep, "mermaid"),
		FSP:         lts.ExportFSP(info),
		Disasm:      disasm,
	}

	var nets []*petri.PetriNet
	for _, w := range petriRep.Workflows {
		if w.Net != nil {
			nets = append(nets, w.Net)
			pg := PetriGraphJSON{Name: w.Name, Sound: w.Sound, OneSafe: w.OneSafe}
			for _, pl := range w.Net.Places {
				pk := "control"
				switch pl.Kind {
				case petri.PlaceStart:
					pk = "start"
				case petri.PlaceDone:
					pk = "done"
				case petri.PlacePool:
					pk = "pool"
				}
				pg.Places = append(pg.Places, PetriPlaceJSON{
					ID: pl.ID, Name: pl.Name, Kind: pk, InitTokens: pl.InitTokens,
				})
			}
			for _, tr := range w.Net.Transitions {
				tj := PetriTransJSON{ID: tr.ID, Name: tr.Name}
				for p := range tr.Pre {
					tj.Pre = append(tj.Pre, p)
				}
				for p := range tr.Post {
					tj.Post = append(tj.Post, p)
				}
				pg.Transitions = append(pg.Transitions, tj)
			}
			out.PetriNets = append(out.PetriNets, pg)
		}
	}
	out.PNML = petri.ExportPNML(nets)

	for _, d := range info.Program.Decls {
		switch x := d.(type) {
		case *ast.EntityDecl:
			cn := ClassNodeJSON{Name: x.Name, Kind: "entity"}
			for _, f := range x.Fields {
				cn.Fields = append(cn.Fields, f.Name+": "+f.Type.String())
			}
			for _, inv := range x.Invariants {
				cn.Invariants = append(cn.Invariants, summarizeExpr(inv))
			}
			out.Classes = append(out.Classes, cn)
			for _, rel := range x.Relations {
				out.ClassEdges = append(out.ClassEdges, ClassEdgeJSON{From: x.Name, To: rel.Target, Label: rel.Name + " (" + rel.Multiplicity + ")"})
			}
		case *ast.MachineDecl:
			cn := ClassNodeJSON{Name: x.Name, Kind: x.Kind}
			for _, cv := range x.ControlVars {
				cn.Fields = append(cn.Fields, cv.Name+": "+cv.Type.String())
			}
			out.Classes = append(out.Classes, cn)
			mg := MachineGraphJSON{Name: x.Name, Kind: x.Kind}
			for idx, st := range x.States {
				mg.States = append(mg.States, StateNodeJSON{ID: st.Name, Init: idx == 0})
				for _, tr := range st.Transitions {
					lbl := tr.Action
					if tr.Guard != nil {
						lbl += " [" + summarizeExpr(tr.Guard) + "]"
					}
					mg.Edges = append(mg.Edges, StateEdgeJSON{From: st.Name, To: tr.TargetState, Label: lbl})
				}
			}
			out.Machines = append(out.Machines, mg)
		case *ast.WorkflowDecl:
			cn := ClassNodeJSON{Name: x.Name, Kind: "workflow"}
			for _, pl := range x.Pools {
				cn.Fields = append(cn.Fields, fmt.Sprintf("pool %s=%d", pl.Name, pl.Capacity))
			}
			out.Classes = append(out.Classes, cn)
		case *ast.SystemDecl:
			cn := ClassNodeJSON{Name: x.Name, Kind: "system"}
			out.Classes = append(out.Classes, cn)
			for _, inst := range x.Instances {
				out.ClassEdges = append(out.ClassEdges, ClassEdgeJSON{From: x.Name, To: inst.TypeName, Label: inst.Name})
			}
		}
	}
	for _, sr := range ltsRep.Systems {
		out.Failures = append(out.Failures, sr.Failures...)
	}
	return out
}
