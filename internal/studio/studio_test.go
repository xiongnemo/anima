package studio

import (
	"bytes"
	"encoding/json"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
	"github.com/xiongnemo/anima/internal/verify/lts"
	"github.com/xiongnemo/anima/internal/verify/petri"
	"github.com/xiongnemo/anima/internal/verify/spark"
)

func TestUMLProjectorAndDarkMaterialStudioServer(t *testing.T) {
	src := `
entity Account:
    balance: int[0..1000]
    invariant: balance >= 0

monitor Lock:
    state Free:
        on acquire -> Busy
    state Busy:
        on release -> Free

workflow Job:
    verify: sound, 1_safe
    pool worker: int[0..1] = 1
    start -> split
    fork split:
        branch b1:
            acquire worker
            sync Lock.acquire
            sync Lock.release
            release worker
    join done_j -> done

system Sys:
    compose:
        j: Job
        l: Lock
    check:
        deadlock_free
`
	prog, err := parser.Parse("studio_test.anm", src)
	if err != nil {
		t.Fatal(err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatal(err)
	}
	sp := spark.Verify(info)
	lr := lts.Verify(info)
	pr := petri.Verify(info)

	merm := FormatUML(info, sp, lr, pr, "mermaid")
	if !strings.Contains(merm, "classDiagram") || !strings.Contains(merm, "stateDiagram-v2") || !strings.Contains(merm, "flowchart TD") {
		t.Fatalf("missing UML views in Mermaid output:\n%s", merm)
	}
	dot := FormatUML(info, sp, lr, pr, "dot")
	if !strings.Contains(dot, "digraph AnimaModel") || !strings.Contains(dot, "#16161e") {
		t.Fatalf("expected dark Graphviz DOT output, got:\n%s", dot)
	}

	srv := NewServer("studio_test.anm", src)
	h := srv.Handler()

	// 1. GET / must serve dark Material UI
	rec := httptest.NewRecorder()
	h.ServeHTTP(rec, httptest.NewRequest("GET", "/", nil))
	if rec.Code != 200 || !strings.Contains(rec.Body.String(), "#16161e") {
		t.Fatalf("unexpected index response: code=%d", rec.Code)
	}

	// 2. GET /api/model
	rec = httptest.NewRecorder()
	h.ServeHTTP(rec, httptest.NewRequest("GET", "/api/model", nil))
	if rec.Code != 200 {
		t.Fatalf("api/model status=%d", rec.Code)
	}

	// 3. POST /api/anim/step (fire Petri transition 0)
	stepBody, _ := json.Marshal(map[string]any{"kind": "petri", "target": "Job", "index": 0})
	rec = httptest.NewRecorder()
	h.ServeHTTP(rec, httptest.NewRequest("POST", "/api/anim/step", bytes.NewReader(stepBody)))
	if rec.Code != 200 {
		t.Fatalf("api/anim/step status=%d", rec.Code)
	}
	var as AnimState
	if err := json.Unmarshal(rec.Body.Bytes(), &as); err != nil {
		t.Fatal(err)
	}
	if len(as.History) != 1 {
		t.Fatalf("expected 1 animator step in history, got %+v", as.History)
	}

	// 4. POST /api/verify with live code
	verBody, _ := json.Marshal(map[string]string{"source": src})
	rec = httptest.NewRecorder()
	h.ServeHTTP(rec, httptest.NewRequest("POST", "/api/verify", bytes.NewReader(verBody)))
	if rec.Code != 200 || !strings.Contains(rec.Body.String(), `"ok":true`) {
		t.Fatalf("api/verify failed: %s", rec.Body.String())
	}
}
