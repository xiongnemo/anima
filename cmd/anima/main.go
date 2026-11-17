package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/xiongnemo/anima/internal/native"
	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/stdlib"
	"github.com/xiongnemo/anima/internal/studio"
	"github.com/xiongnemo/anima/internal/verify/lts"
	"github.com/xiongnemo/anima/internal/verify/petri"
	"github.com/xiongnemo/anima/internal/verify/spark"
	"github.com/xiongnemo/anima/internal/vm"
)

const version = "0.1.0"

func main() {
	if len(os.Args) < 2 {
		printUsage()
		os.Exit(1)
	}
	cmd := os.Args[1]
	args := os.Args[2:]

	var code int
	switch cmd {
	case "check":
		code = cmdCheck(args)
	case "run":
		code = cmdRun(args)
	case "build":
		code = cmdBuild(args)
	case "disasm":
		code = cmdDisasm(args)
	case "uml":
		code = cmdUML(args)
	case "export":
		code = cmdExport(args)
	case "studio":
		code = cmdStudio(args)
	case "stdlib":
		code = cmdStdlib()
	case "version", "--version", "-v":
		fmt.Printf("anima v%s (AnimaSMT + SWEN90004 FSP/LTSA + Petri/WF-Net + BytecodeVM + Native C11)\n", version)
	case "help", "--help", "-h":
		printUsage()
	default:
		// Convenience: `anima foo.anm` runs `run foo.anm`
		if strings.HasSuffix(cmd, ".anm") {
			code = cmdRun(os.Args[1:])
		} else {
			fmt.Fprintf(os.Stderr, "unknown command %q\n", cmd)
			printUsage()
			code = 1
		}
	}
	os.Exit(code)
}

func printUsage() {
	fmt.Print(`Anima — Executable Formally Verified Unified Modeling & Systems Language

Usage:
  anima check   [--explain] [--json] [--save-cex trace.json] <file.anm>
  anima run     [--seed N] [--animate] [--replay trace.json] <file.anm> [-- args...]
  anima build   [-o out_bin] [--emit-c out.c] <file.anm>
  anima disasm  <file.anm>
  anima uml     [--format mermaid|dot] <file.anm>
  anima export  [--fsp out.fsp] [--pnml out.pnml] <file.anm>
  anima studio  [--addr 127.0.0.1:7788] <file.anm>
  anima stdlib
`)
}

type pipelineResult struct {
	src      string
	info     *sema.ProgramInfo
	sparkRep *spark.Report
	ltsRep   *lts.Report
	petriRep *petri.Report
}

func runFrontendAndVerify(filePath string) (*pipelineResult, error) {
	raw, err := os.ReadFile(filePath)
	if err != nil {
		return nil, err
	}
	src := string(raw)
	prog, err := parser.Parse(filePath, src)
	if err != nil {
		return nil, fmt.Errorf("parse error: %w", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		return nil, fmt.Errorf("semantic error: %w", err)
	}
	sp := spark.Verify(info)
	lr := lts.Verify(info)
	pr := petri.Verify(info)
	return &pipelineResult{
		src:      src,
		info:     info,
		sparkRep: sp,
		ltsRep:   lr,
		petriRep: pr,
	}, nil
}

func (p *pipelineResult) AllOK() bool {
	return p.sparkRep.OK() && p.ltsRep.OK() && p.petriRep.OK()
}

func cmdCheck(args []string) int {
	fs := flag.NewFlagSet("check", flag.ExitOnError)
	explain := fs.Bool("explain", false, "print detailed proof steps and formulas")
	jsonOut := fs.Bool("json", false, "output structured JSON report")
	saveCex := fs.String("save-cex", "", "write first LTS counterexample SequenceTrace to JSON")
	_ = fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Fprintln(os.Stderr, "usage: anima check [--explain] [--json] <file.anm>")
		return 1
	}
	file := fs.Arg(0)
	res, err := runFrontendAndVerify(file)
	if err != nil {
		if *jsonOut {
			_ = json.NewEncoder(os.Stdout).Encode(map[string]any{"ok": false, "error": err.Error()})
		} else {
			fmt.Fprintf(os.Stderr, "[FAIL] %v\n", err)
		}
		return 1
	}

	if *saveCex != "" {
		for _, sr := range res.ltsRep.Systems {
			if len(sr.Failures) > 0 {
				data, _ := json.MarshalIndent(sr.Failures[0], "", "  ")
				_ = os.WriteFile(*saveCex, data, 0644)
				break
			}
		}
	}

	if *jsonOut {
		_ = json.NewEncoder(os.Stdout).Encode(studio.BuildStudioModel(res.info, res.sparkRep, res.ltsRep, res.petriRep, ""))
		if !res.AllOK() {
			return 1
		}
		return 0
	}

	fmt.Printf("=== Anima 3-Core Formal Verification: %s ===\n", file)
	fmt.Printf("[1/3] SPARK + AnimaSMT (Octagon + CDCL/LIA): %d proved, %d failed, %d unknown\n",
		res.sparkRep.Proved, res.sparkRep.Failed, res.sparkRep.Unknown)
	if *explain {
		for _, vc := range res.sparkRep.VCs {
			fmt.Printf("      - [%s] %s (%s): %s | %s\n", vc.Status, vc.Name, vc.Span, vc.Formula, vc.Explain)
		}
	}
	for _, e := range res.sparkRep.Errors() {
		fmt.Fprintf(os.Stderr, "      ERROR: %s\n", e)
	}

	fmt.Printf("[2/3] SWEN90004 FSP/LTSA & Typestate: %d system(s), %d typestate error(s)\n",
		len(res.ltsRep.Systems), len(res.ltsRep.TypestateErrors))
	for _, sr := range res.ltsRep.Systems {
		status := "PASS"
		if len(sr.Failures) > 0 {
			status = fmt.Sprintf("FAIL (%d violation(s))", len(sr.Failures))
		}
		fmt.Printf("      - System %-18s states=%-5d edges=%-6d SCCs=%-4d checks=%d -> %s\n",
			sr.SystemName, sr.NumStates, sr.NumEdges, sr.NumSCCs, len(sr.ChecksRun), status)
		for _, cex := range sr.Failures {
			fmt.Fprintf(os.Stderr, "      VIOLATION: %s\n", cex.Violation)
			fmt.Fprintln(os.Stderr, studio.FormatSequenceMermaid(&cex))
		}
	}
	for _, te := range res.ltsRep.TypestateErrors {
		fmt.Fprintf(os.Stderr, "      TYPESTATE ERROR (%s in %s): %s\n", te.Span, te.Func, te.Message)
	}
	for _, be := range res.ltsRep.BuildErrors {
		fmt.Fprintf(os.Stderr, "      LTS BUILD ERROR: %s\n", be)
	}

	fmt.Printf("[3/3] SWEN90004 Petri / WF-Net Soundness: %d workflow(s)\n", len(res.petriRep.Workflows))
	for _, wr := range res.petriRep.Workflows {
		fmt.Printf("      - Workflow %-16s places=%d trans=%d markings=%d bounded=%v 1_safe=%v sound=%v short_circuit_L4=%v\n",
			wr.Name, wr.Places, wr.Transitions, wr.ReachableMarkings, wr.Bounded, wr.OneSafe, wr.Sound, wr.ShortCircuitL4)
		for _, e := range wr.Errors {
			fmt.Fprintf(os.Stderr, "      PETRI ERROR (%s): %s\n", wr.Name, e)
		}
	}
	for _, ce := range res.petriRep.CallErrors {
		fmt.Fprintf(os.Stderr, "      PETRI RESOURCE ERROR: %s\n", ce)
	}

	if !res.AllOK() {
		fmt.Fprintln(os.Stderr, "\n[RESULT] VERIFICATION FAILED")
		return 1
	}
	fmt.Println("\n[RESULT] ALL 3 FORMAL VERIFICATION KERNELS PASSED")
	return 0
}

func cmdRun(args []string) int {
	fs := flag.NewFlagSet("run", flag.ExitOnError)
	seed := fs.Int64("seed", 42, "deterministic scheduler PRNG seed")
	animate := fs.Bool("animate", false, "interactive LTSA/Petri CLI animator mode")
	replayPath := fs.String("replay", "", "counterexample SequenceTrace JSON file to replay deterministically")
	_ = fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Fprintln(os.Stderr, "usage: anima run [--seed N] [--animate] [--replay trace.json] <file.anm>")
		return 1
	}
	file := fs.Arg(0)
	progArgs := fs.Args()[1:]

	var replayTrace *lts.SequenceTrace
	if *replayPath != "" {
		raw, err := os.ReadFile(*replayPath)
		if err != nil {
			fmt.Fprintf(os.Stderr, "failed to read replay trace: %v\n", err)
			return 1
		}
		var tr lts.SequenceTrace
		if err := json.Unmarshal(raw, &tr); err != nil {
			fmt.Fprintf(os.Stderr, "invalid replay trace JSON: %v\n", err)
			return 1
		}
		replayTrace = &tr
	}

	raw, err := os.ReadFile(file)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	prog, err := parser.Parse(file, string(raw))
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse error: %v\n", err)
		return 1
	}
	info, err := sema.Check(prog)
	if err != nil {
		fmt.Fprintf(os.Stderr, "semantic error: %v\n", err)
		return 1
	}

	// Enforce 3-core formal verification before execution unless replaying a counterexample!
	verified := true
	if replayTrace == nil && !*animate {
		sp := spark.Verify(info)
		lr := lts.Verify(info)
		pr := petri.Verify(info)
		if !sp.OK() || !lr.OK() || !pr.OK() {
			verified = false
			for _, e := range sp.Errors() {
				fmt.Fprintln(os.Stderr, e)
			}
			for _, e := range lr.Errors() {
				fmt.Fprintln(os.Stderr, e)
			}
			for _, e := range pr.Errors() {
				fmt.Fprintln(os.Stderr, e)
			}
			fmt.Fprintln(os.Stderr, "refusing to run unverified program (run `anima check` for full diagnostics)")
			return 1
		}
	}

	cp, err := vm.Compile(info, string(raw), verified)
	if err != nil {
		fmt.Fprintf(os.Stderr, "bytecode compile error: %v\n", err)
		return 1
	}
	machine := vm.NewVM(cp, vm.RunOptions{
		Seed:    *seed,
		Animate: *animate,
		Replay:  replayTrace,
		Args:    append([]string{file}, progArgs...),
	})
	val, err := machine.Run()
	if err != nil {
		fmt.Fprintf(os.Stderr, "runtime error: %v\n", err)
		return 1
	}
	if replayTrace != nil {
		return 0
	}
	if val.Kind == vm.ValInt {
		return int(val.Int)
	}
	if val.Kind == vm.ValVariant && val.Variant != nil && val.Variant.Name == "Err" {
		fmt.Fprintf(os.Stderr, "main returned %s\n", val.String())
		return 1
	}
	return 0
}

func cmdBuild(args []string) int {
	fs := flag.NewFlagSet("build", flag.ExitOnError)
	outBin := fs.String("o", "", "output native ELF binary path")
	emitC := fs.String("emit-c", "", "save generated C11 source path")
	_ = fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Fprintln(os.Stderr, "usage: anima build [-o out_bin] [--emit-c out.c] <file.anm>")
		return 1
	}
	file := fs.Arg(0)
	res, err := runFrontendAndVerify(file)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	if !res.AllOK() {
		for _, e := range res.sparkRep.Errors() {
			fmt.Fprintln(os.Stderr, e)
		}
		for _, e := range res.ltsRep.Errors() {
			fmt.Fprintln(os.Stderr, e)
		}
		for _, e := range res.petriRep.Errors() {
			fmt.Fprintln(os.Stderr, e)
		}
		fmt.Fprintln(os.Stderr, "native build aborted: formal verification failed")
		return 1
	}

	target := *outBin
	if target == "" {
		base := filepath.Base(file)
		target = strings.TrimSuffix(base, filepath.Ext(base))
	}
	if err := native.BuildNative(res.info, target, *emitC); err != nil {
		fmt.Fprintf(os.Stderr, "native build error: %v\n", err)
		return 1
	}
	fmt.Printf("Verified & compiled native ELF executable: %s\n", target)
	return 0
}

func cmdDisasm(args []string) int {
	if len(args) < 1 {
		fmt.Fprintln(os.Stderr, "usage: anima disasm <file.anm>")
		return 1
	}
	file := args[0]
	raw, err := os.ReadFile(file)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	prog, err := parser.Parse(file, string(raw))
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	info, err := sema.Check(prog)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	cp, err := vm.Compile(info, string(raw), true)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	fmt.Print(cp.Module.Disassemble())
	return 0
}

func cmdUML(args []string) int {
	fs := flag.NewFlagSet("uml", flag.ExitOnError)
	format := fs.String("format", "mermaid", "UML format: mermaid or dot")
	_ = fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Fprintln(os.Stderr, "usage: anima uml [--format mermaid|dot] <file.anm>")
		return 1
	}
	res, err := runFrontendAndVerify(fs.Arg(0))
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	fmt.Print(studio.FormatUML(res.info, res.sparkRep, res.ltsRep, res.petriRep, *format))
	return 0
}

func cmdExport(args []string) int {
	fs := flag.NewFlagSet("export", flag.ExitOnError)
	fspPath := fs.String("fsp", "", "output .fsp file path")
	pnmlPath := fs.String("pnml", "", "output .pnml file path")
	_ = fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Fprintln(os.Stderr, "usage: anima export [--fsp out.fsp] [--pnml out.pnml] <file.anm>")
		return 1
	}
	res, err := runFrontendAndVerify(fs.Arg(0))
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	fspText := lts.ExportFSP(res.info)
	var nets []*petri.PetriNet
	for _, wr := range res.petriRep.Workflows {
		if wr.Net != nil {
			nets = append(nets, wr.Net)
		}
	}
	pnmlText := petri.ExportPNML(nets)

	if *fspPath != "" {
		if err := os.WriteFile(*fspPath, []byte(fspText), 0644); err != nil {
			fmt.Fprintf(os.Stderr, "%v\n", err)
			return 1
		}
		fmt.Printf("Exported FSP: %s\n", *fspPath)
	}
	if *pnmlPath != "" {
		if err := os.WriteFile(*pnmlPath, []byte(pnmlText), 0644); err != nil {
			fmt.Fprintf(os.Stderr, "%v\n", err)
			return 1
		}
		fmt.Printf("Exported PNML: %s\n", *pnmlPath)
	}
	if *fspPath == "" && *pnmlPath == "" {
		fmt.Println("=== SWEN90004 FSP ===")
		fmt.Println(fspText)
		fmt.Println("=== ISO PNML ===")
		fmt.Println(pnmlText)
	}
	return 0
}

func cmdStudio(args []string) int {
	fs := flag.NewFlagSet("studio", flag.ExitOnError)
	addr := fs.String("addr", "127.0.0.1:7788", "HTTP listen address")
	_ = fs.Parse(args)
	if fs.NArg() < 1 {
		fmt.Fprintln(os.Stderr, "usage: anima studio [--addr 127.0.0.1:7788] <file.anm>")
		return 1
	}
	file := fs.Arg(0)
	raw, err := os.ReadFile(file)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	srv := studio.NewServer(file, string(raw))
	fmt.Printf("Anima Studio (Orchis Dark Material) running at http://%s\n", *addr)
	if err := srv.ListenAndServe(*addr); err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	return 0
}

func cmdStdlib() int {
	fmt.Println("=== Anima Verified Standard Library (8 Modules) ===")
	for _, m := range stdlib.Modules {
		fmt.Printf("- %-16s %s\n    Formal Guarantee: %s\n", m.Path, m.Description, m.VerificationGuarantee)
	}
	return 0
}
