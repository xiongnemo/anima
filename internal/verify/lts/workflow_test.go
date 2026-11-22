package lts

import (
	"sort"
	"strings"
	"testing"

	"github.com/xiongnemo/anima/internal/parser"
	"github.com/xiongnemo/anima/internal/sema"
)

// A workflow's handles are followed along the paths it runs, not down the
// page: a step is checked with the handles as the way to it left them, and
// each way out is an exit.
func TestOwnershipFollowsTheWorkflow(t *testing.T) {
	const head = `
def work(x: int[0..100]) -> int:
    return x

def shut(own p: conc.ThreadPool) -> bool:
    p.shutdown()
    return True

workflow W(n: int) -> int:
    start -> a:
        ok = n > 0
        r = 0
        pool = conc.ThreadPool(1, 2)
`
	const choice = `
    choice after a:
        when ok -> yes
        when not ok -> no
`
	const use = `
        f = pool.submit(() => work(1))
        r = f.await()
`
	cases := []struct {
		name, body string
		want       string // part of an error, or "" when it is accepted
	}{
		{"a step written above the one that runs before it", `
    step a -> close:
        r = 1
    step use -> fin:` + use + `
    step close -> use:
        pool.shutdown()
    step fin -> done:
        return r
`, "use-after-close"},
		{"a path that does not shut the pool down", choice + `
    step yes -> done:
        pool.shutdown()
        return 1
    step no -> done:
        return 2
`, "resource handle leak"},
		{"the same, the paths written the other way round", choice + `
    step no -> done:
        return 2
    step yes -> done:
        pool.shutdown()
        return 1
`, "resource handle leak"},
		{"a path that ends without a return", choice + `
    step yes -> done:
        pool.shutdown()
        return 1
    step no -> done:
        r = 2
`, "resource handle leak"},
		{"shut down on one path to a merge, used after it", choice + `
    step yes -> m:
        r = 1
    step no -> m:
        pool.shutdown()
    merge m after yes, no -> fin
    step fin -> done:` + use + `
        pool.shutdown()
        return r
`, "use-after-close"},
		{"a guard that takes the pool is not run for the branch before it", `
    choice after a:
        when ok -> yes
        when shut(own pool) -> no
    step yes -> done:
        return 1
    step no -> done:
        return 2
`, "resource handle leak"},
		{"a log left open on one path", choice + `
    step yes -> fin:
        AuditLog.open_log()
        AuditLog.close_log()
    step no -> fin:
        AuditLog.open_log()
    step fin -> done:
        pool.shutdown()
        return r
`, "port:AuditLog \"AuditLog\" opened"},

		{"each path uses the pool and shuts it down", choice + `
    step yes -> done:
        pool.shutdown()
        return 1
    step no -> done:` + use + `
        pool.shutdown()
        return r
`, ""},
		{"shut down after a merge", choice + `
    step yes -> m:` + use + `
    step no -> m:
        r = 2
    merge m after yes, no -> fin
    step fin -> done:
        pool.shutdown()
        return r
`, ""},
		{"shut down in the step written first, which runs last", `
    step a -> use:
        r = 1
    step close -> done:
        pool.shutdown()
        return r
    step use -> close:` + use + `
`, ""},
		{"a fork between the steps", `
    step a -> split:
        r = 1
    fork split:
        branch left:
            x = work(1)
        branch right:
            y = work(2)
    join both
    step fin after both -> done:
        pool.shutdown()
        return x + y
`, ""},
	}
	for _, c := range cases {
		got := ownershipErrors(t, head+c.body)
		switch {
		case c.want == "" && got != "":
			t.Errorf("%s: expected it accepted, got:\n%s", c.name, got)
		case c.want != "" && !strings.Contains(got, c.want):
			t.Errorf("%s: expected an error containing %q, got:\n%s", c.name, c.want, got)
		}
	}
}

// edgesOf writes the LTS of workflow W of src as its edges, each once and in
// order.
func edgesOf(t *testing.T, src string) string {
	t.Helper()
	prog, err := parser.Parse("lts_test.anm", src)
	if err != nil {
		t.Fatalf("parse error: %v", err)
	}
	info, err := sema.Check(prog)
	if err != nil {
		t.Fatalf("sema error: %v", err)
	}
	model := CompileWorkflowLTS(info.Workflows["W"].Decl)
	var out []string
	seen := map[string]bool{}
	for from, edges := range model.Edges {
		for _, e := range edges {
			edge := model.States[from] + " -" + e.Action + "-> " + model.States[e.Target]
			if !seen[edge] {
				seen[edge] = true
				out = append(out, edge)
			}
		}
	}
	sort.Strings(out)
	return strings.Join(out, "\n")
}

// The LTS of a workflow is the workflow as it runs: a body does the action
// of its step wherever it goes next, and ends the workflow where it may
// return.
func TestWorkflowLTSFollowsTheFlow(t *testing.T) {
	const head = `
def f(x: int) -> Result[int, str]:
    if x > 3:
        return Err("big")
    return Ok(x)

def note() -> int:
    return 1

workflow W(k: int[0..9]) -> Result[int, str]:
`
	for _, c := range []struct {
		name, nodes string
		want        []string
	}{
		{"a start that may return", `
    start -> a:
        if k > 3:
            return Ok(0)
    step a -> done:
        return Ok(1)
`, []string{"a -a-> done", "start -tau-> a", "start -tau-> done"}},
		{"a start that returns", `
    start -> a:
        return Ok(0)
    step a -> done:
        return Ok(1)
`, []string{"start -tau-> done"}},
		{"a ? in a step", `
    start -> a
    step a -> b:
        v = f(k)?
    step b -> done:
        return Ok(1)
`, []string{"a -a-> b", "a -a-> done", "b -b-> done", "start -tau-> a"}},
		{"a ? in a lambda leaves the lambda", `
    start -> a
    step a -> b:
        g = (x) => f(x)?
    step b -> done:
        return Ok(1)
`, []string{"a -a-> b", "b -b-> done", "start -tau-> a"}},
		{"a step before its choice", `
    start -> a
    step a:
        if k > 8:
            return Ok(0)
    choice after a:
        when k > 3 -> b
        else -> done
    step b -> done:
        return Ok(1)
`, []string{"a -a-> b", "a -a-> done", "b -b-> done", "start -tau-> a"}},
		{"a choice of its own name", `
    start -> c
    choice c:
        when k > 3 -> b
        else -> done
    step b -> done:
        return Ok(1)
`, []string{"b -b-> done", "c -tau-> b", "c -tau-> done", "start -tau-> c"}},
		{"a merge and the choice after it", `
    start -> m
    merge m
    choice after m:
        when k > 3 -> b
        else -> m2
    merge m2 -> b
    step b -> done:
        return Ok(1)
`, []string{"b -b-> done", "m -tau-> b", "m -tau-> m2", "m2 -tau-> b", "start -tau-> m"}},
		{"a join and the choice after it", `
    start -> fk
    fork fk:
        branch x:
            call note()
    join j
    choice after j:
        when k > 3 -> b
        else -> done
    step b -> done:
        return Ok(1)
`, []string{"b -b-> done", "fk -tau-> j", "j -join_j-> b", "j -join_j-> done", "start -tau-> fk"}},
		{"a fork after a join is not gone to", `
    start -> fk
    fork fk:
        branch x:
            call note()
    join j
    fork g after j:
        branch y:
            call note()
`, []string{"fk -tau-> j", "j -join_j-> done", "start -tau-> fk"}},
		{"a choice after a node is not come to by its name", `
    start -> a
    step a
    choice c after a:
        when k > 3 -> b
        else -> done
    step b -> c
`, []string{"a -a-> b", "a -a-> done", "b -b-> done", "start -tau-> a"}},
		{"the first step after a step, and the fork after it before that", `
    start -> a
    step a
    step b after a -> a2
    step c after a -> a2
    step a2
    step d after a2 -> done:
        return Ok(1)
    fork fk after a2:
        branch x:
            call note()
    join j -> done
`, []string{"a -a-> b", "a2 -a2-> fk", "b -b-> a2", "fk -tau-> j", "j -join_j-> done", "start -tau-> a"}},
	} {
		if got, want := edgesOf(t, head+c.nodes), strings.Join(c.want, "\n"); got != want {
			t.Errorf("%s:\n got %s\nwant %s", c.name, strings.ReplaceAll(got, "\n", "; "), strings.ReplaceAll(want, "\n", "; "))
		}
	}
}
