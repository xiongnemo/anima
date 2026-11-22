package tests

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io"
	"math/rand"
	"net"
	"net/netip"
	neturl "net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"
)

type httpAsk struct {
	N    int    `json:"n"`
	Post bool   `json:"post"`
	URL  string `json:"url"`
	Body string `json:"body"`
}

// httpAsks lists requests; PORT is the port of the test's server, DEAD one
// that nothing listens on.
func httpAsks() []httpAsk {
	gets := []string{
		"http://127.0.0.1:PORT/a",
		"http://127.0.0.1:PORT",
		"http://127.0.0.1:PORT?x=1",
		"http://127.0.0.1:PORT/a#frag",
		"http://127.0.0.1:PORT#frag",
		"http://127.0.0.1:PORT/a?b=c#d?e",
		"http://127.0.0.1:PORT/a b",
		"http://127.0.0.1:PORT/a?b c",
		"http://127.0.0.1:PORT/a%20b",
		"http://127.0.0.1:PORT/a%zzb",
		"http://127.0.0.1:PORT/a%",
		"http://127.0.0.1:PORT/a%2",
		"http://127.0.0.1:PORT/a?b=%zz",
		"http://127.0.0.1:PORT/a#%zz",
		"http://127.0.0.1:PORT/a#b c%20d",
		"http://127.0.0.1:PORT/é/日本?q=é",
		"http://127.0.0.1:PORT/%C3%A9/é",
		"http://127.0.0.1:PORT/a%2Fb/c",
		"http://127.0.0.1:PORT/a%2Fb c",
		"http://127.0.0.1:PORT/a%00b",
		"http://127.0.0.1:PORT/a%00b c",
		"http://127.0.0.1:PORT/a\"<b>{c}|d^e`f",
		"http://127.0.0.1:PORT/?a\"<b>{c}|d^e'f",
		"http://127.0.0.1:PORT/a\tb",
		"http://127.0.0.1:PORT/a\nX-Evil: 1",
		"http://127.0.0.1:PORT/a\r\nX-Evil: 1",
		"http://127.0.0.1:PORT/a?b\r\nX-Evil: 1",
		"http://127.0.0.1:PORT/a#b\r\nX-Evil: 1",
		"http://127.0.0.1:PORT/a\x7fb",
		"http://127.0.0.1:PORT/a HTTP/1.1\r\nX-Evil: 1\r\n\r\n",
		"http://127.0.0.1:PORT//a//b",
		"http://127.0.0.1:PORT/a/../b/./c",
		"http://127.0.0.1:PORT/*",
		"http://127.0.0.1:PORT/%2A",
		"http://127.0.0.1:PORT/%2a",
		"http://127.0.0.1:PORT/a;b=c?d;e&f",
		"http://127.0.0.1:PORT/a+b:c@d$e,f=g!h'i(j)k~l",
		"http://127.0.0.1:PORT/a[b]c",
		"http://127.0.0.1:PORT/a\\b",
		"http://127.0.0.1:PORT/?",
		"http://127.0.0.1:PORT?",
		"http://127.0.0.1:PORT/#",
		"http://127.0.0.1:PORT/a??b",
		"http://127.0.0.1:PORT/a?b?c#d#e",
		"http://user@127.0.0.1:PORT/a",
		"http://user:pa ss@127.0.0.1:PORT/a",
		"http://user:pass@127.0.0.1:PORT/a",
		"http://user:@127.0.0.1:PORT/a",
		"http://:pass@127.0.0.1:PORT/a",
		"http://@127.0.0.1:PORT/a",
		"http://:@127.0.0.1:PORT/a",
		"http://a%40b:c%3Ad%2F@127.0.0.1:PORT/a",
		"http://a%00b:c@127.0.0.1:PORT/a",
		"http://us%zzer@127.0.0.1:PORT/a",
		"http://a:b:c@127.0.0.1:PORT/a",
		"http://a@b@127.0.0.1:PORT/a",
		"http://é@127.0.0.1:PORT/a",
		"http://user:pass@127.0.0.1:DEAD/a",
		"http://us er:pa%20ss@127.0.0.1:DEAD/a b",
		"http://127.0.0.1:PORT/a@b",
		"http://127.0.0.1:PORT?a@b",
		"http://127.0.0.1:PORT#a@b",
		"http://[::1]:PORT/a",
		"http://[::1]:DEAD/a",
		"http://[0:0:0:0:0:0:0:1]:PORT/a",
		"http://[::ffff:127.0.0.1]:PORT/a",
		"http://[::ffff:127.0.0.1]:DEAD/a",
		"http://[::ffff:7f00:1]:DEAD/a",
		"http://[::1%25lo]:PORT/a",
		"http://[::1%lo]:PORT/a",
		"http://[::1]x:PORT/a",
		"http://[::1/a",
		"http://::1]:PORT/a",
		"http://[127.0.0.1]:PORT/a",
		"http://[localhost]:PORT/a",
		"http://[]:PORT/a",
		"http://[::1]:PORT:PORT/a",
		"http://user@[::1]:PORT/a",
		"http://[1:2:3:4:5:6:7:8:9]:PORT/a",
		"http://[fe80::1:0:0:1]:DEAD/a",
		"http://0.0.0.0:PORT/a",
		"http://[::]:PORT/a",
		"http://:PORT/a",
		"http://localhost:PORT/a",
		"http://LOCALHOST:PORT/a",
		"http://localhost.:PORT/a",
		"http://localhost:DEAD/a",
		"HTTP://127.0.0.1:PORT/a",
		"hTtP://127.0.0.1:PORT/a",
		"127.0.0.1:PORT/a",
		"localhost:PORT/a",
		"//127.0.0.1:PORT/a",
		"/a",
		"a/b:c",
		"a:b",
		"",
		" http://127.0.0.1:PORT/a",
		"http://127.0.0.1:PORT/a ",
		"ftp://127.0.0.1:PORT/a",
		"1http://127.0.0.1:PORT/a",
		"ht+tp://127.0.0.1:PORT/a",
		"://127.0.0.1:PORT/a",
		"http:///a",
		"http://",
		"http:",
		"http:?a#b",
		"http:127.0.0.1:PORT/a",
		"http:/127.0.0.1:PORT/a",
		"http://127.0.0.1:/a",
		"http://127.0.0.1:PORTx/a",
		"http://127.0.0.1:99999/a",
		"http://127.0.0.1:65536/a",
		"http://127.0.0.1:0000000000000000000000PORT/a",
		"http://127.0.0.1:-1/a",
		"http://127.0.0.1:0/a",
		"http://127.0.0 .1:PORT/a",
		"http://127.0.0.1%31:PORT/a",
		"http://127.0.0.1%25:PORT/a",
		"http://127.0.0.1%C3%A9:PORT/a",
		"http://é.invalid:PORT/a",
		"http://127.0.0.1\\a:PORT/a",
		"http://127.0.0.1\"a:PORT/a",
		"http://a]b:PORT/a",
		"http://a<b>:PORT/a",
		"http://127.1:DEAD/a",
		"http://0x7f.0.0.1:DEAD/a",
		"http://127.0.0.01:DEAD/a",
		"http://2130706433:DEAD/a",
		"http://-a.invalid:DEAD/a",
		"http://a..invalid:DEAD/a",
		"http://a_b!c:DEAD/a",
		"http://nosuch.invalid:PORT/a",
		"http://127.0.0.1:DEAD/a",
		"http://127.0.0.1:DEAD/a?b=c d#e f",
	}
	var asks []httpAsk
	for _, u := range gets {
		asks = append(asks, httpAsk{URL: u})
	}
	for _, p := range [][2]string{
		{"http://127.0.0.1:PORT/a", "hello"},
		{"http://127.0.0.1:PORT/a", ""},
		{"http://127.0.0.1:PORT/a?x#y", `{"a": 1}`},
		{"http://127.0.0.1:PORT/a", "é日本"},
		{"http://127.0.0.1:PORT/a", "a\r\n\r\nb"},
		{"http://127.0.0.1:PORT/a", strings.Repeat("0123456789", 30000)},
		{"http://user:pass@127.0.0.1:PORT/a b", "x"},
		{"http://[::1]:PORT", "x"},
		{"http://127.0.0.1:DEAD/a", "x"},
		{"http://127.0.0.1:PORT/a%zz", "x"},
		{"ftp://127.0.0.1:PORT/a", "x"},
	} {
		asks = append(asks, httpAsk{Post: true, URL: p[0], Body: p[1]})
	}
	return asks
}

// changeURL changes a URL in up to three places.
func changeURL(r *rand.Rand, s string) string {
	parts := []string{
		"/", "//", "?", "#", "@", ":", "[", "]", " ", "\\", "\"", "'", "<", ">", "é", "日", "%C3%A9",
		".", "..", ";", "&", "=", "+", "*", "~", "{", "}", "|", "^", "`", "\t", "\n", "\r\n", "\x7f", "\x01",
		"%", "%2", "%25", "%zz", "%2f", "%2A", "%3F", "%23", "%00", "%41", "%7e", "0", "1", "a", "A", "-", "_",
		"$", "!", "(", ")", ",", "::1", "user", "http:", "HTTP", "://", "127.0.0.1", "localhost",
	}
	b := []byte(s)
	for k := 1 + r.Intn(3); k > 0; k-- {
		at := r.Intn(len(b) + 1)
		switch r.Intn(4) {
		case 0, 1:
			b = append(b[:at:at], append([]byte(parts[r.Intn(len(parts))]), b[at:]...)...)
		case 2:
			if at < len(b) {
				end := min(len(b), at+1+r.Intn(3))
				b = append(b[:at:at], b[end:]...)
			}
		default:
			if at < len(b) {
				end := min(len(b), at+1+r.Intn(6))
				b = append(b[:end:end], b[at:]...)
			}
		}
	}
	return strings.ToValidUTF8(string(b), "")
}

// localAsk reports whether a URL asks nothing of the world outside this
// machine and this test: it is no URL, or its host is this machine at the
// port of the test's server or the port nothing listens on.
func localAsk(raw, port, dead string) bool {
	u, err := neturl.Parse(raw)
	if err != nil || strings.ToLower(u.Scheme) != "http" || u.Host == "" {
		return true
	}
	if p := u.Port(); p != port && p != dead {
		n, err := strconv.ParseUint(p, 10, 64)
		return err == nil && n > 65535 && n < 1<<40
	}
	switch u.Hostname() {
	case "", "localhost", "LOCALHOST", "nosuch.invalid":
		return true
	}
	a, err := netip.ParseAddr(u.Hostname())
	return err == nil && (a.Unmap().IsLoopback() || a.IsUnspecified())
}

// requestServer answers every request with how many it has seen, and keeps
// what each one was.
type requestServer struct {
	port string
	mu   sync.Mutex
	seen []string
}

func (s *requestServer) take() []string {
	s.mu.Lock()
	defer s.mu.Unlock()
	seen := s.seen
	s.seen = nil
	return seen
}

func newRequestServer(t *testing.T) *requestServer {
	t.Helper()
	ln, err := net.Listen("tcp", ":0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { ln.Close() })
	s := &requestServer{port: strconv.Itoa(ln.Addr().(*net.TCPAddr).Port)}
	serve := func(c net.Conn) {
		defer c.Close()
		_ = c.SetDeadline(time.Now().Add(10 * time.Second))
		r := bufio.NewReader(c)
		var got strings.Builder
		length := 0
		for {
			line, err := r.ReadString('\n')
			got.WriteString(line)
			if err != nil {
				return
			}
			if line == "\r\n" || line == "\n" {
				break
			}
			if v, ok := strings.CutPrefix(strings.ToLower(line), "content-length:"); ok {
				length, _ = strconv.Atoi(strings.TrimSpace(v))
			}
		}
		body := make([]byte, length)
		if _, err := io.ReadFull(r, body); err != nil {
			return
		}
		got.Write(body)
		s.mu.Lock()
		s.seen = append(s.seen, got.String())
		n := strconv.Itoa(len(s.seen) - 1)
		s.mu.Unlock()
		_, _ = fmt.Fprintf(c, "HTTP/1.1 200 OK\r\nContent-Length: %d\r\nConnection: close\r\n\r\n%s", len(n), n)
	}
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			go serve(c)
		}
	}()
	return s
}

// The native HTTP client asks what the VM's asks, of the same server: the
// same bytes on the wire for a URL, or the same Err. It took everything up
// to the first / for the host and up to the first : of that for the name,
// so http://h?x=1, http://user@h/ and http://[::1]/ each named a host that
// is none; it sent the URL as written, with its spaces, its #fragment and
// whatever else was in it, so a URL with a line end in it was a request
// with a header of the URL's choosing; and it took any text for a URL.
// ANIMA_HTTP_FUZZ sets how many changed URLs are tried after the listed
// ones, ANIMA_HTTP_SEED which.
func TestE2EHTTPRequestParity(t *testing.T) {
	srv := newRequestServer(t)
	gone, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	dead := strconv.Itoa(gone.Addr().(*net.TCPAddr).Port)
	gone.Close()
	ports := strings.NewReplacer("PORT", srv.port, "DEAD", dead)

	asks := httpAsks()
	for i := range asks {
		asks[i].URL = ports.Replace(asks[i].URL)
	}
	listed := len(asks)
	extra, seed := 400, int64(1)
	if v, err := strconv.Atoi(os.Getenv("ANIMA_HTTP_FUZZ")); err == nil {
		extra = v
	}
	if v, err := strconv.ParseInt(os.Getenv("ANIMA_HTTP_SEED"), 10, 64); err == nil {
		seed = v
	}
	r := rand.New(rand.NewSource(seed))
	for len(asks) < listed+extra {
		a := asks[r.Intn(listed)]
		if len(a.Body) > 100 {
			continue
		}
		a.URL = changeURL(r, a.URL)
		// Most of them are to ask the server something.
		u, err := neturl.Parse(a.URL)
		if (err != nil || u.Port() != srv.port) && r.Intn(4) != 0 {
			continue
		}
		if localAsk(a.URL, srv.port, dead) {
			asks = append(asks, a)
		}
	}
	for i := range asks {
		asks[i].N = i
	}
	tmp := t.TempDir()
	text, err := json.Marshal(map[string]any{"all": asks})
	if err != nil {
		t.Fatal(err)
	}
	asksPath := filepath.Join(tmp, "asks.json")
	if err := os.WriteFile(asksPath, text, 0o644); err != nil {
		t.Fatal(err)
	}
	src := strings.ReplaceAll(`import std.requests as req
import std.json as json
import std.fs as fs

entity Ask:
    n: int
    post: bool
    url: str
    body: str

entity Asks:
    all: list[Ask]

def show(n: int, r: Result[HttpResponse, str]) -> int:
    match r:
        Ok(x) -> print(f"#{n} ok", x.status, x.body)
        Err(m) -> print(f"#{n} err", m)
    return 0

def ask(a: Ask) -> int:
    if a.post:
        return show(a.n, req.post(a.url, a.body, timeout_ms=3000))
    return show(a.n, req.get(a.url, timeout_ms=3000))

def each(text: str) -> int:
    match json.decode[Asks](text):
        Ok(asks) ->
            for a in asks.all:
                ask(a)
        Err(m) -> print("asks:", m)
    return 0

def main() -> int:
    match fs.read_text("ASKS"):
        Ok(text) -> each(text)
        Err(m) -> print("asks:", m)
    return 0
`, "ASKS", asksPath)
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, "asks.anm")
	if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	nativeBin := filepath.Join(tmp, "asks")
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	// What each request came to: the Err, or the request the server got.
	run := func(argv ...string) map[int]string {
		srv.take()
		out, err := exec.Command(argv[0], argv[1:]...).Output()
		if err != nil {
			t.Fatalf("%v: %v\n%s", argv, err, out)
		}
		seen := srv.take()
		got := map[int]string{}
		for _, part := range strings.Split("\n"+strings.TrimSuffix(string(out), "\n"), "\n#")[1:] {
			num, rest, _ := strings.Cut(part, " ")
			n, err := strconv.Atoi(num)
			if err != nil {
				t.Fatalf("output is not by request: %q", part)
			}
			if which, ok := strings.CutPrefix(rest, "ok 200 "); ok {
				k, err := strconv.Atoi(which)
				if err != nil || k >= len(seen) {
					t.Fatalf("request %d: answer %q is none of the server's %d", n, rest, len(seen))
				}
				rest = "sent " + seen[k]
				seen[k] = ""
			}
			got[n] = rest
		}
		for _, s := range seen {
			if s != "" {
				t.Errorf("%v: the server got a request that no answer was read of: %q", argv, s)
			}
		}
		return got
	}
	vm, nat := run(animaBin, "run", path), run(nativeBin)
	// Which of a name's addresses is dialed first is the resolver's choice,
	// and the two backends have a resolver each: where nothing listens, the
	// address in the Err is this machine's by either name.
	loop := strings.NewReplacer("dial tcp [::1]:"+dead, "dial tcp 127.0.0.1:"+dead)
	bad := 0
	for i, a := range asks {
		if u, err := neturl.Parse(a.URL); err == nil && strings.EqualFold(strings.TrimSuffix(u.Hostname(), "."), "localhost") {
			vm[i], nat[i] = loop.Replace(vm[i]), loop.Replace(nat[i])
		}
		if vm[i] != nat[i] || vm[i] == "" {
			bad++
			if bad <= 20 {
				t.Errorf("request %d of %q (post %v)\n    VM:     %q\n    native: %q", i, a.URL, a.Post, vm[i], nat[i])
			}
		}
		// A URL has no say in what the request is but its first line, the
		// Host and who asks.
		if head, ok := strings.CutPrefix(nat[i], "sent "); ok {
			head, _, _ = strings.Cut(head, "\r\n\r\n")
			for k, line := range strings.Split(head, "\r\n") {
				name, _, _ := strings.Cut(line, ":")
				switch {
				case k == 0 && strings.Count(line, " ") == 2 && strings.HasSuffix(line, " HTTP/1.1"):
				case k > 0 && (name == "Host" || name == "User-Agent" || name == "Authorization" || name == "Connection"):
				case k > 0 && a.Post && (name == "Content-Length" || name == "Content-Type"):
				default:
					t.Errorf("request %d of %q has the line %q", i, a.URL, line)
				}
			}
		}
	}
	if bad > 0 {
		t.Fatalf("%d of %d requests differ", bad, len(asks))
	}
	kinds := map[string]int{}
	for i := range asks {
		kind, rest, _ := strings.Cut(nat[i], " ")
		if kind == "err" {
			kind, _, _ = strings.Cut(rest, " ")
		}
		kinds[kind]++
	}
	t.Logf("%d requests: %v", len(asks), kinds)
	// What a few of them are, so that the two do not agree on a mistake.
	at := func(url string, post bool) int {
		for i, a := range asks[:listed] {
			if a.URL == ports.Replace(url) && a.Post == post {
				return i
			}
		}
		t.Fatalf("%q is not listed", url)
		return -1
	}
	get := func(line, host, more string) string {
		return "sent GET " + line + " HTTP/1.1\r\nHost: " + host + "\r\nUser-Agent: anima\r\n" + more + "Connection: close\r\n\r\n"
	}
	here := "127.0.0.1:" + srv.port
	for _, c := range []struct {
		url, want string
		post      bool
	}{
		{"http://127.0.0.1:PORT/a", get("/a", here, ""), false},
		{"http://127.0.0.1:PORT?x=1", get("/?x=1", here, ""), false},
		{"http://127.0.0.1:PORT/a?b=c#d?e", get("/a?b=c", here, ""), false},
		{"http://127.0.0.1:PORT/a b", get("/a%20b", here, ""), false},
		{"http://127.0.0.1:PORT/a?b c", get("/a?b%20c", here, ""), false},
		{"http://127.0.0.1:DEAD/a?b=c d#e f", `err Get "http://127.0.0.1:` + dead + `/a?b=c%20d#e%20f": dial tcp 127.0.0.1:` + dead + `: connect: connection refused`, false},
		{"http://127.0.0.1:PORT/é/日本?q=é", get("/%C3%A9/%E6%97%A5%E6%9C%AC?q=%C3%A9", here, ""), false},
		{"http://127.0.0.1:PORT/a%2Fb/c", get("/a%2Fb/c", here, ""), false},
		{"http://127.0.0.1:PORT/a%zzb", `err parse "http://127.0.0.1:` + srv.port + `/a%zzb": invalid URL escape "%zz"`, false},
		{"http://127.0.0.1:PORT/a\r\nX-Evil: 1", `err parse "http://127.0.0.1:` + srv.port + `/a\r\nX-Evil: 1": net/url: invalid control character in URL`, false},
		{"http://user:pa ss@127.0.0.1:PORT/a", `err parse "http://user:pa ss@127.0.0.1:` + srv.port + `/a": net/url: invalid userinfo`, false},
		{"http://user:pass@127.0.0.1:PORT/a", get("/a", here, "Authorization: Basic dXNlcjpwYXNz\r\n"), false},
		{"http://user@127.0.0.1:PORT/a", get("/a", here, "Authorization: Basic dXNlcjo=\r\n"), false},
		{"http://user:pass@127.0.0.1:DEAD/a", `err Get "http://user:***@127.0.0.1:` + dead + `/a": dial tcp 127.0.0.1:` + dead + `: connect: connection refused`, false},
		{"http://[::1]:PORT/a", get("/a", "[::1]:"+srv.port, ""), false},
		{"http://[::ffff:127.0.0.1]:DEAD/a", `err Get "http://[::ffff:127.0.0.1]:` + dead + `/a": dial tcp 127.0.0.1:` + dead + `: connect: connection refused`, false},
		{"http://[::1%25lo]:PORT/a", `err parse "http://[::1%25lo]:` + srv.port + `/a": invalid host`, false},
		{"http://é.invalid:PORT/a", `err parse "http://é.invalid:` + srv.port + `/a": non-ASCII host name`, false},
		{"http://127.0.0.1:PORTx/a", `err parse "http://127.0.0.1:` + srv.port + `x/a": invalid port ":` + srv.port + `x" after host`, false},
		{"127.0.0.1:PORT/a", `err parse "127.0.0.1:` + srv.port + `/a": first path segment in URL cannot contain colon`, false},
		{"ftp://127.0.0.1:PORT/a", `err Get "ftp://127.0.0.1:` + srv.port + `/a": unsupported protocol scheme "ftp"`, false},
		{"/a", `err Get "/a": unsupported protocol scheme ""`, false},
		{"http:///a", `err Get "http:///a": http: no Host in request URL`, false},
		{"http://127.0.0.1:99999/a", `err Get "http://127.0.0.1:99999/a": dial tcp: address 99999: invalid port`, false},
		{"http://nosuch.invalid:PORT/a", `err Get "http://nosuch.invalid:` + srv.port + `/a": dial tcp: lookup nosuch.invalid: no such host`, false},
		{"http://127.0.0.1:PORT/a", "sent POST /a HTTP/1.1\r\nHost: " + here + "\r\nUser-Agent: anima\r\nContent-Length: 5\r\nContent-Type: application/json\r\nConnection: close\r\n\r\nhello", true},
		{"http://127.0.0.1:PORT/a", "sent POST /a HTTP/1.1\r\nHost: " + here + "\r\nUser-Agent: anima\r\nContent-Length: 0\r\nConnection: close\r\n\r\n", true},
	} {
		c.want = strings.ReplaceAll(c.want, "PORT", srv.port)
		i := at(c.url, c.post)
		if i >= 0 && c.post && c.want[len(c.want)-1] == '\n' {
			// The second POST to that URL is the one with no body.
			i++
		}
		if i >= 0 && nat[i] != c.want {
			t.Errorf("request %d of %q\n    is:   %q\n    want: %q", i, c.url, nat[i], c.want)
		}
	}
}

// fullListener gives the port of a listener that takes no more
// connections: one to it is neither made nor refused.
func fullListener(t *testing.T) string {
	t.Helper()
	fd, err := syscall.Socket(syscall.AF_INET, syscall.SOCK_STREAM|syscall.SOCK_CLOEXEC, 0)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { syscall.Close(fd) })
	if err := syscall.Bind(fd, &syscall.SockaddrInet4{Addr: [4]byte{127, 0, 0, 1}}); err != nil {
		t.Fatal(err)
	}
	if err := syscall.Listen(fd, 0); err != nil {
		t.Fatal(err)
	}
	sa, err := syscall.Getsockname(fd)
	if err != nil {
		t.Fatal(err)
	}
	port := strconv.Itoa(sa.(*syscall.SockaddrInet4).Port)
	for i := 0; i < 16; i++ {
		c, err := net.DialTimeout("tcp", "127.0.0.1:"+port, 300*time.Millisecond)
		if err != nil {
			return port
		}
		t.Cleanup(func() { c.Close() })
	}
	t.Skip("a listener with a full queue still takes connections here")
	return ""
}

// timeout_ms is the time for the whole request, on both backends, and one
// that runs out of it before an answer says so. The native client gave a
// connection that was not made in time the Err `connect: operation now in
// progress`, and a TLS handshake that was not `tls handshake failed`.
func TestE2EHTTPRequestTimesOut(t *testing.T) {
	full := fullListener(t)
	// A server that takes the connection and says nothing.
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { ln.Close() })
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			t.Cleanup(func() { c.Close() })
		}
	}()
	silent := strconv.Itoa(ln.Addr().(*net.TCPAddr).Port)
	src := strings.NewReplacer("FULL", full, "SILENT", silent).Replace(`import std.requests as req

def show(what: str, r: Result[HttpResponse, str]) -> int:
    match r:
        Ok(x) -> print(what, "ok", x.status)
        Err(m) -> print(what, m)
    return 0

def main() -> int:
    show("connect", req.get("http://127.0.0.1:FULL/a", timeout_ms=600))
    show("post", req.post("http://127.0.0.1:FULL/a", "x", timeout_ms=600))
    show("handshake", req.get("https://127.0.0.1:SILENT/a", timeout_ms=600))
    show("answer", req.get("http://127.0.0.1:SILENT/a", timeout_ms=600))
    s = req.Session(pool_size=2)
    show("session", s.get("http://127.0.0.1:FULL/a", timeout_ms=600))
    f = s.get_async("http://127.0.0.1:FULL/a", timeout_ms=600)
    show("async", f.await())
    s.close()
    return 0
`)
	late := `": context deadline exceeded (Client.Timeout exceeded while awaiting headers)` + "\n"
	want := `connect Get "http://127.0.0.1:` + full + `/a` + late +
		`post Post "http://127.0.0.1:` + full + `/a` + late +
		`handshake Get "https://127.0.0.1:` + silent + `/a` + late +
		`answer Get "http://127.0.0.1:` + silent + `/a` + late +
		`session Get "http://127.0.0.1:` + full + `/a` + late +
		`async Get "http://127.0.0.1:` + full + `/a` + late
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, "late.anm")
	if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	nativeBin := filepath.Join(tmp, "late")
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	for _, argv := range [][]string{{animaBin, "run", path}, {nativeBin}} {
		start := time.Now()
		out, err := exec.Command(argv[0], argv[1:]...).CombinedOutput()
		if err != nil || string(out) != want {
			t.Errorf("%v: err=%v, output:\n%s\nwant:\n%s", argv[len(argv)-1], err, out, want)
		}
		// Six requests of 600 ms each, and none that ends early or late.
		if took := time.Since(start); took < 3600*time.Millisecond || took > 8*time.Second {
			t.Errorf("%v: six requests of 600 ms took %v", argv[len(argv)-1], took)
		}
	}
}

// A request that ran out of time leaves nothing behind it. Go's transport
// goes on connecting, and shaking hands over TLS, for a request that is
// over, in case the next can use the connection; with the VM none can, so
// each request a silent server made give up left a socket open, for as
// long as the server kept silent.
func TestE2EHTTPRequestLeavesNoSocket(t *testing.T) {
	if _, err := os.Stat("/proc/self/fd"); err != nil {
		t.Skip("the sockets of a process are counted in /proc")
	}
	full := fullListener(t)
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { ln.Close() })
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			t.Cleanup(func() { c.Close() })
		}
	}()
	silent := strconv.Itoa(ln.Addr().(*net.TCPAddr).Port)
	src := strings.NewReplacer("FULL", full, "SILENT", silent).Replace(`import std.requests as req
import std.time as time

def ask(url: str) -> int:
    match req.get(url, timeout_ms=200):
        Ok(x) -> print("ok", x.status)
        Err(m) -> print("err")
    return 0

def main() -> int:
    print("before")
    time.sleep_ms(1500)
    for i in [1, 2, 3, 4]:
        ask("http://127.0.0.1:FULL/a")
        ask("https://127.0.0.1:SILENT/a")
        ask("http://127.0.0.1:SILENT/a")
    s = req.Session(pool_size=2)
    f = s.get_async("https://127.0.0.1:SILENT/a", timeout_ms=200)
    g = s.get_async("http://127.0.0.1:FULL/a", timeout_ms=200)
    match f.await():
        Ok(x) -> print("ok", x.status)
        Err(m) -> print("err")
    match g.await():
        Ok(x) -> print("ok", x.status)
        Err(m) -> print("err")
    s.close()
    print("after")
    time.sleep_ms(1500)
    return 0
`)
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, "left.anm")
	if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	nativeBin := filepath.Join(tmp, "left")
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	sockets := func(pid int) int {
		dir := "/proc/" + strconv.Itoa(pid) + "/fd"
		ents, err := os.ReadDir(dir)
		if err != nil {
			t.Fatal(err)
		}
		n := 0
		for _, e := range ents {
			if to, err := os.Readlink(filepath.Join(dir, e.Name())); err == nil && strings.HasPrefix(to, "socket:") {
				n++
			}
		}
		return n
	}
	for _, argv := range [][]string{{animaBin, "run", path}, {nativeBin}} {
		cmd := exec.Command(argv[0], argv[1:]...)
		out, err := cmd.StdoutPipe()
		if err != nil {
			t.Fatal(err)
		}
		if err := cmd.Start(); err != nil {
			t.Fatal(err)
		}
		// The sockets it has while it sleeps, before and after it asked.
		var before, after, errs int
		sc := bufio.NewScanner(out)
		for sc.Scan() {
			switch sc.Text() {
			case "before":
				time.Sleep(300 * time.Millisecond)
				before = sockets(cmd.Process.Pid)
			case "after":
				time.Sleep(300 * time.Millisecond)
				after = sockets(cmd.Process.Pid)
			case "err":
				errs++
			}
		}
		if err := cmd.Wait(); err != nil || errs != 14 {
			t.Errorf("%v: err=%v, %d of 14 requests ran out of time", argv[len(argv)-1], err, errs)
		}
		if after != before {
			t.Errorf("%v: %d sockets before the requests, %d after", argv[len(argv)-1], before, after)
		}
	}
}
