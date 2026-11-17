package studio

import (
	"embed"
	"encoding/json"
	"fmt"
	"io/fs"
	"net/http"
	"strings"
	"sync"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/lts"
	"github.com/xiongnemo/anima/internal/verify/petri"
	"github.com/xiongnemo/anima/internal/verify/spark"
	"github.com/xiongnemo/anima/internal/vm"
)

//go:embed web/index.html
var webFS embed.FS

type EnabledTrans struct {
	Kind   string `json:"kind"` // "lts" or "petri"
	Target string `json:"target"`
	Index  int    `json:"index"`
	Label  string `json:"label"`
}

type AnimState struct {
	MachineStates map[string]string `json:"machine_states"`
	SystemLabels  []string          `json:"system_labels"`
	PetriMarkings map[string][]int  `json:"petri_markings"`
	Enabled       []EnabledTrans    `json:"enabled"`
	History       []string          `json:"history"`
}

type Server struct {
	mu         sync.Mutex
	file       string
	source     string
	info       *sema.ProgramInfo
	ltsRep     *lts.Report
	petriRep   *petri.Report
	model      StudioModelJSON
	sysState   int
	machStates map[string]string
	petriMarks map[string][]int
	petriNets  map[string]*petri.PetriNet
	history    []string
}

func NewServer(file, initialSrc string) *Server {
	s := &Server{
		file:       file,
		source:     initialSrc,
		machStates: map[string]string{},
		petriMarks: map[string][]int{},
		petriNets:  map[string]*petri.PetriNet{},
	}
	s.evaluateSource(initialSrc)
	return s
}

func (s *Server) evaluateSource(src string) {
	s.source = src
	prog, err := parser.Parse(s.file, src)
	if err != nil {
		s.model = StudioModelJSON{ParseError: err.Error()}
		return
	}
	info, err := sema.Check(prog)
	if err != nil {
		s.model = StudioModelJSON{ParseError: err.Error()}
		return
	}
	sparkRep := spark.Verify(info)
	ltsRep := lts.Verify(info)
	petriRep := petri.Verify(info)

	disasm := ""
	if cp, err := vm.Compile(info, src, sparkRep.OK() && ltsRep.OK() && petriRep.OK()); err == nil {
		disasm = cp.Module.Disassemble()
	}

	s.info = info
	s.ltsRep = ltsRep
	s.petriRep = petriRep
	s.model = BuildStudioModel(info, sparkRep, ltsRep, petriRep, disasm)
	s.resetAnimLocked()
}

func (s *Server) resetAnimLocked() {
	s.sysState = 0
	s.machStates = map[string]string{}
	s.petriMarks = map[string][]int{}
	s.petriNets = map[string]*petri.PetriNet{}
	s.history = nil

	if s.info == nil {
		return
	}
	for name, m := range s.info.Machines {
		if len(m.States) > 0 {
			s.machStates[name] = m.States[0].Name
		}
	}
	if s.ltsRep != nil && len(s.ltsRep.Systems) > 0 && s.ltsRep.Systems[0].SysLTS != nil {
		s.sysState = s.ltsRep.Systems[0].SysLTS.Init
	}
	if s.petriRep != nil {
		for _, wr := range s.petriRep.Workflows {
			if wr.Net != nil {
				s.petriNets[wr.Name] = wr.Net
				s.petriMarks[wr.Name] = append([]int{}, wr.Net.InitMarking...)
			}
		}
	}
}

func (s *Server) snapshotAnimLocked() AnimState {
	as := AnimState{
		MachineStates: map[string]string{},
		PetriMarkings: map[string][]int{},
		History:       append([]string{}, s.history...),
	}
	for k, v := range s.machStates {
		as.MachineStates[k] = v
	}
	for k, v := range s.petriMarks {
		as.PetriMarkings[k] = append([]int{}, v...)
	}

	// Enabled LTS composite transitions (or individual machine transitions)
	if s.ltsRep != nil && len(s.ltsRep.Systems) > 0 && s.ltsRep.Systems[0].SysLTS != nil {
		sys := s.ltsRep.Systems[0].SysLTS
		if s.sysState < len(sys.States) {
			as.SystemLabels = append([]string{}, sys.States[s.sysState].Labels...)
			// Sync machStates from labels like "lock=Unlocked"
			for idx, lbl := range sys.States[s.sysState].Labels {
				parts := strings.SplitN(lbl, "=", 2)
				if len(parts) == 2 && idx < len(sys.Components) {
					stBase := strings.SplitN(parts[1], "[", 2)[0]
					as.MachineStates[sys.Components[idx].Name] = stBase
				}
			}
		}
		for idx, e := range sys.Edges[s.sysState] {
			as.Enabled = append(as.Enabled, EnabledTrans{
				Kind:   "lts",
				Target: sys.SystemName,
				Index:  idx,
				Label:  fmt.Sprintf("[LTS] %s (%s)", e.Action, e.Actor),
			})
		}
	} else if s.info != nil {
		for mName, m := range s.info.Machines {
			cur := s.machStates[mName]
			for _, st := range m.States {
				if st.Name == cur {
					for idx, tr := range st.Transitions {
						as.Enabled = append(as.Enabled, EnabledTrans{
							Kind:   "machine",
							Target: mName,
							Index:  idx,
							Label:  fmt.Sprintf("[%s] %s -> %s", mName, tr.Action, tr.TargetState),
						})
					}
				}
			}
		}
	}

	// Enabled Petri workflow net transitions
	for wfName, net := range s.petriNets {
		m := s.petriMarks[wfName]
		for tid, tr := range net.Transitions {
			enabled := true
			for p, req := range tr.Pre {
				if m[p] < req {
					enabled = false
					break
				}
			}
			if enabled {
				as.Enabled = append(as.Enabled, EnabledTrans{
					Kind:   "petri",
					Target: wfName,
					Index:  tid,
					Label:  fmt.Sprintf("[Petri:%s] %s", wfName, tr.Name),
				})
			}
		}
	}

	return as
}

// Handler returns the HTTP handler for `anima studio`.
func (s *Server) Handler() http.Handler {
	mux := http.NewServeMux()
	sub, _ := fs.Sub(webFS, "web")
	fileSrv := http.FileServer(http.FS(sub))

	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/" {
			fileSrv.ServeHTTP(w, r)
			return
		}
		data, err := webFS.ReadFile("web/index.html")
		if err != nil {
			http.Error(w, err.Error(), 500)
			return
		}
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		_, _ = w.Write(data)
	})

	mux.HandleFunc("/api/model", func(w http.ResponseWriter, r *http.Request) {
		s.mu.Lock()
		defer s.mu.Unlock()
		resp := struct {
			File   string          `json:"file"`
			Source string          `json:"source"`
			Model  StudioModelJSON `json:"model"`
			Anim   AnimState       `json:"anim"`
		}{
			File:   s.file,
			Source: s.source,
			Model:  s.model,
			Anim:   s.snapshotAnimLocked(),
		}
		writeJSON(w, resp)
	})

	mux.HandleFunc("/api/verify", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "POST required", 405)
			return
		}
		var req struct {
			Source string `json:"source"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}
		s.mu.Lock()
		s.evaluateSource(req.Source)
		resp := struct {
			Model StudioModelJSON `json:"model"`
			Anim  AnimState       `json:"anim"`
		}{
			Model: s.model,
			Anim:  s.snapshotAnimLocked(),
		}
		s.mu.Unlock()
		writeJSON(w, resp)
	})

	mux.HandleFunc("/api/anim/reset", func(w http.ResponseWriter, r *http.Request) {
		s.mu.Lock()
		s.resetAnimLocked()
		anim := s.snapshotAnimLocked()
		s.mu.Unlock()
		writeJSON(w, anim)
	})

	mux.HandleFunc("/api/anim/step", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			Kind   string `json:"kind"`
			Target string `json:"target"`
			Index  int    `json:"index"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}
		s.mu.Lock()
		switch req.Kind {
		case "lts":
			if s.ltsRep != nil && len(s.ltsRep.Systems) > 0 && s.ltsRep.Systems[0].SysLTS != nil {
				sys := s.ltsRep.Systems[0].SysLTS
				edges := sys.Edges[s.sysState]
				if req.Index >= 0 && req.Index < len(edges) {
					e := edges[req.Index]
					s.sysState = e.Target
					s.history = append(s.history, fmt.Sprintf("%s: %s", e.Actor, e.Action))
				}
			}
		case "machine":
			if s.info != nil {
				if m, ok := s.info.Machines[req.Target]; ok {
					cur := s.machStates[req.Target]
					for _, st := range m.States {
						if st.Name == cur && req.Index >= 0 && req.Index < len(st.Transitions) {
							tr := st.Transitions[req.Index]
							s.machStates[req.Target] = tr.TargetState
							s.history = append(s.history, fmt.Sprintf("%s: %s -> %s", req.Target, tr.Action, tr.TargetState))
							break
						}
					}
				}
			}
		case "petri":
			if net, ok := s.petriNets[req.Target]; ok && req.Index >= 0 && req.Index < len(net.Transitions) {
				tr := net.Transitions[req.Index]
				m := s.petriMarks[req.Target]
				enabled := true
				for p, reqTok := range tr.Pre {
					if m[p] < reqTok {
						enabled = false
						break
					}
				}
				if enabled {
					for p, reqTok := range tr.Pre {
						m[p] -= reqTok
					}
					for p, prodTok := range tr.Post {
						m[p] += prodTok
					}
					s.history = append(s.history, fmt.Sprintf("%s: fire %s", req.Target, tr.Name))
				}
			}
		}
		anim := s.snapshotAnimLocked()
		s.mu.Unlock()
		writeJSON(w, anim)
	})

	return mux
}

func (s *Server) ListenAndServe(addr string) error {
	return http.ListenAndServe(addr, s.Handler())
}

func writeJSON(w http.ResponseWriter, v any) {
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(v)
}
