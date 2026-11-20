package lts

import (
	"strings"
	"testing"
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
