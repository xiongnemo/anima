package tests

import (
	"encoding/json"
	"math/rand"
	"net"
	"net/http"
	"net/netip"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
)

type sockAsk struct {
	N      int    `json:"n"`
	Listen bool   `json:"listen"`
	Host   string `json:"host"`
	Port   int    `json:"port"`
}

func sockHosts() []string {
	return []string{
		"127.0.0.1", "127.0.0.2", "localhost", "LOCALHOST", "localhost.", "::1", "::", "0.0.0.0",
		"0:0:0:0:0:0:0:1", "::ffff:127.0.0.1", "::ffff:7f00:1", "::ffff:0.0.0.0",
		"[::1]", "[127.0.0.1]", "[localhost]", "[", "]", "[]", ":", "::1%lo", "::1%25lo", "fe80::1%eth0", "%",
		"", " ", "127.1", "0x7f.0.0.1", "127.0.0.01", "2130706433", "256.1.1.1", "1.2.3.4.5", "00.0.0.0",
		"127.0.0.1.", "0.0.0.0.", "::1.", "1::2::3", "::g", "1:2:3:4:5:6:7:8:9", "127.0.0.1:80", "localhost:80",
		"127.0.0.1 ", " 127.0.0.1", "\t127.0.0.1", "127.0.0.1\n", "127.0.0.1\r\n", "a b", "-", "*", "0", "_",
		"-a.invalid", "a..invalid", "a_b!c", "nosuch.invalid", "nosuch.invalid.", ".", "..", "localhost..",
		"héllo", "é.invalid", "日本", "a/b", "a\\b", "a@b", "http://127.0.0.1", "127.0.0.1/8",
		strings.Repeat("a", 64) + ".invalid", strings.Repeat("a.", 130) + "invalid",
	}
}

func changeHost(r *rand.Rand, s string) string {
	parts := []string{
		":", "::", "[", "]", ".", "..", "%", "%25", " ", "\t", "\n", "é", "0", "1", "7", "f", "x", "-", "_", "/", "@", "*",
		"127", "::1", "ffff", "0.0.0.0", "localhost",
	}
	b := []byte(s)
	for k := 1 + r.Intn(3); k > 0; k-- {
		at := r.Intn(len(b) + 1)
		switch r.Intn(3) {
		case 0, 1:
			b = append(b[:at:at], append([]byte(parts[r.Intn(len(parts))]), b[at:]...)...)
		default:
			if at < len(b) {
				end := min(len(b), at+1+r.Intn(3))
				b = append(b[:at:at], b[end:]...)
			}
		}
	}
	return strings.ToValidUTF8(string(b), "")
}

// localHost reports whether a host asks nothing of the world outside this
// machine: it is an address of this machine, or no name that is looked up.
func localHost(h string) bool {
	if a, err := netip.ParseAddr(h); err == nil {
		a = a.Unmap()
		return a.IsLoopback() || a.IsUnspecified()
	}
	for i := 0; i < len(h); i++ {
		c := h[i]
		if !(c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' || c == '.' || c == '-' || c == '_') {
			return true
		}
	}
	return false
}

// helloServer says "hi" to whoever connects, at every address of this
// machine, and counts them.
func helloServer(t *testing.T) (port int, met *atomic.Int64) {
	t.Helper()
	ln, err := net.Listen("tcp", ":0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { ln.Close() })
	met = &atomic.Int64{}
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			met.Add(1)
			_, _ = c.Write([]byte("hi"))
			c.Close()
		}
	}()
	return ln.Addr().(*net.TCPAddr).Port, met
}

// deadPort is a port nothing listens at, and none the system connects
// from: one of those would now and then be connected to by itself.
func deadPort(t *testing.T) int {
	t.Helper()
	for port := 20011; port < 30000; port += 97 {
		gone, err := net.Listen("tcp", ":"+strconv.Itoa(port))
		if err == nil {
			gone.Close()
			return port
		}
	}
	t.Fatal("no port is free")
	return 0
}

const sockAsksSrc = `import std.socket as sock
import std.json as json
import std.fs as fs

entity Ask:
    n: int
    listen: bool
    host: str
    port: int[0..65535]

entity Asks:
    all: list[Ask]

def once(host: str, port: int[1..65535]) -> bool:
    match sock.connect_tcp(host, port):
        Ok(c) ->
            c.close()
            return True
        Err(e) -> return False
    return False

def reach(host: str, port: int[1..65535]) -> str:
    # Twice: a port nothing listens at is now and then the one the system
    # connects from, and so one that is connected to.
    if once(host, port) and once(host, port):
        return "yes"
    return "no"

def dial(a: Ask) -> int:
    match sock.connect_tcp(a.host, a.port):
        Ok(c) ->
            got = match c.recv_text(64):
                Ok(t) -> t
                Err(e) -> "err " + e
            print(f"#{a.n} ok", got)
            c.close()
        Err(e) -> print(f"#{a.n} err", e)
    return 0

def listen(a: Ask) -> int:
    match sock.listen_tcp(a.host, a.port):
        Ok(l) ->
            p = l.port()
            v4 = reach("127.0.0.1", p)
            v6 = reach("::1", p)
            # :: is dialed as ::1 and then, as Go does, as 0.0.0.0.
            any = reach("::", p)
            print(f"#{a.n} ok", a.port == 0 or a.port == p, v4, v6, any)
            l.close()
        Err(e) -> print(f"#{a.n} err", e)
    return 0

def each(text: str) -> int:
    match json.decode[Asks](text):
        Ok(asks) ->
            for a in asks.all:
                if a.listen:
                    listen(a)
                else:
                    dial(a)
        Err(m) -> print("asks:", m)
    return 0

def main() -> int:
    match fs.read_text("ASKS"):
        Ok(text) -> each(text)
        Err(m) -> print("asks:", m)
    return 0
`

// bothBackends builds src and gives what runs it on each backend.
func bothBackends(t *testing.T, name, src string) (vm, native []string) {
	t.Helper()
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, name+".anm")
	if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	nativeBin := filepath.Join(tmp, name)
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	return []string{animaBin, "run", path}, []string{nativeBin}
}

// A socket is of the host it is asked for, on both backends, or it is the
// same Err. The native listener took any host that is no IPv4 address for
// every address of the machine: listen_tcp("localhost", 0), ("::1", 0) and
// ("no.such.host", 0) were all open to the network. The native connect knew
// no IPv6, and each backend had its own words for an Err.
// ANIMA_SOCK_FUZZ sets how many changed hosts are tried after the listed
// ones, ANIMA_SOCK_SEED which.
func TestE2ESocketAddressParity(t *testing.T) {
	port, met := helloServer(t)
	dead := deadPort(t)
	hosts := sockHosts()
	listed := len(hosts)
	extra, seed := 300, int64(1)
	if v, err := strconv.Atoi(os.Getenv("ANIMA_SOCK_FUZZ")); err == nil {
		extra = v
	}
	if v, err := strconv.ParseInt(os.Getenv("ANIMA_SOCK_SEED"), 10, 64); err == nil {
		seed = v
	}
	r := rand.New(rand.NewSource(seed))
	for len(hosts) < listed+extra {
		if h := changeHost(r, hosts[r.Intn(listed)]); localHost(h) {
			hosts = append(hosts, h)
		}
	}
	var asks []sockAsk
	for _, h := range hosts {
		asks = append(asks,
			sockAsk{Host: h, Port: port}, sockAsk{Host: h, Port: dead}, sockAsk{Host: h, Port: 0},
			sockAsk{Host: h, Listen: true}, sockAsk{Host: h, Listen: true, Port: dead}, sockAsk{Host: h, Listen: true, Port: port})
	}
	for i := range asks {
		asks[i].N = i
	}
	text, err := json.Marshal(map[string]any{"all": asks})
	if err != nil {
		t.Fatal(err)
	}
	asksPath := filepath.Join(t.TempDir(), "asks.json")
	if err := os.WriteFile(asksPath, text, 0o644); err != nil {
		t.Fatal(err)
	}
	vmCmd, natCmd := bothBackends(t, "sockasks", strings.ReplaceAll(sockAsksSrc, "ASKS", asksPath))
	run := func(argv []string) (map[int]string, int64) {
		before := met.Load()
		out, err := exec.Command(argv[0], argv[1:]...).Output()
		if err != nil {
			t.Fatalf("%v: %v\n%s", argv, err, out)
		}
		got := map[int]string{}
		for _, part := range strings.Split("\n"+strings.TrimSuffix(string(out), "\n"), "\n#")[1:] {
			num, rest, _ := strings.Cut(part, " ")
			n, err := strconv.Atoi(num)
			if err != nil {
				t.Fatalf("output is not by ask: %q", part)
			}
			got[n] = rest
		}
		return got, met.Load() - before
	}
	vm, vmMet := run(vmCmd)
	nat, natMet := run(natCmd)
	if vmMet != natMet || vmMet == 0 {
		t.Errorf("the server was connected to %d times by the VM and %d by the native program", vmMet, natMet)
	}
	// Which of a name's addresses is dialed first is the resolver's choice,
	// and the two backends have a resolver each: where nothing listens, the
	// address in the Err is this machine's by either name.
	loop := strings.NewReplacer("dial tcp [::1]:", "dial tcp 127.0.0.1:")
	bad, opened := 0, 0
	for i, a := range asks {
		if strings.EqualFold(strings.TrimSuffix(a.Host, "."), "localhost") {
			vm[i], nat[i] = loop.Replace(vm[i]), loop.Replace(nat[i])
		}
		if vm[i] != nat[i] || vm[i] == "" {
			bad++
			if bad <= 20 {
				t.Errorf("ask %d of %q at %d (listen %v)\n    VM:     %q\n    native: %q", i, a.Host, a.Port, a.Listen, vm[i], nat[i])
			}
		}
		if !a.Listen || !strings.HasPrefix(nat[i], "ok ") {
			continue
		}
		opened++
		// A listener is where its host says, and nowhere else.
		addr, err := netip.ParseAddr(a.Host)
		addr = addr.Unmap()
		want := "ok True no no no"
		switch {
		case err != nil && strings.EqualFold(strings.TrimSuffix(a.Host, "."), "localhost"):
			want = "ok True yes no yes"
		case err != nil:
			t.Errorf("ask %d: a listener at %q, which is no address: %q", i, a.Host, nat[i])
			continue
		case addr == netip.MustParseAddr("127.0.0.1") || addr == netip.IPv4Unspecified():
			want = "ok True yes no yes"
		case addr == netip.IPv6Loopback() || addr == netip.IPv6Unspecified():
			want = "ok True no yes yes"
		}
		if nat[i] != want {
			t.Errorf("ask %d: a listener at %q is %q, want %q", i, a.Host, nat[i], want)
		}
	}
	if opened < 10 {
		t.Errorf("%d listeners were opened", opened)
	}
}

var sockPortRE = regexp.MustCompile(`:[0-9]{4,5}\b`)

// sameOnBothBackends runs src on both at once and requires each to print
// want, a port of four or five digits being written :P.
func sameOnBothBackends(t *testing.T, name, src, want string) {
	t.Helper()
	vmCmd, natCmd := bothBackends(t, name, src)
	var wg sync.WaitGroup
	outs := make([]string, 2)
	errs := make([]error, 2)
	for i, argv := range [][]string{vmCmd, natCmd} {
		wg.Add(1)
		go func() {
			defer wg.Done()
			out, err := exec.Command(argv[0], argv[1:]...).CombinedOutput()
			outs[i], errs[i] = sockPortRE.ReplaceAllString(string(out), ":P"), err
		}()
	}
	wg.Wait()
	for i, which := range []string{"VM", "native"} {
		if errs[i] != nil || outs[i] != want {
			t.Errorf("%s: err=%v, output:\n%s\nwant:\n%s", which, errs[i], outs[i], want)
		}
	}
}

// What is done with a stream ends the same on both backends, in the same
// words: a wait that runs out of time, a peer that left, a peer that left
// what it was sent unread, a send that the peer does not read. The native
// program said "Resource temporarily unavailable" of a wait that ran out
// and "Broken pipe" of a peer that left.
func TestE2ESocketStreamParity(t *testing.T) {
	sameOnBothBackends(t, "streams", `import std.socket as sock

def show(tag: str, r: Result[str, str]) -> int:
    match r:
        Ok(t) -> print(f"{tag}: ok [{t}] {len(t)}")
        Err(e) -> print(f"{tag}: {e}")
    return 0

def shown(tag: str, r: Result[int, str]) -> int:
    match r:
        Ok(n) -> print(f"{tag}: ok {n}")
        Err(e) -> print(f"{tag}: {e}")
    return 0

def long(n: int[0..30]) -> str:
    s = "0123456789abcdef"
    i = 0
    while i < n:
        s = s + s
        i = i + 1
    return s

def talk(c: sock.TcpStream, s: sock.TcpStream, wait: bool) -> int:
    shown("send", c.send_text("héllo world"))
    show("recv 2", s.recv_text(2))
    show("recv 1", s.recv_text(1))
    show("recv", s.recv_text())
    shown("send nothing", c.send_text(""))
    if wait:
        show("recv nothing", s.recv_text())
    return 0

def pair(host: str, wait: bool) -> int:
    match sock.listen_tcp(host, 0):
        Ok(l) ->
            match sock.listen_tcp(host, l.port()):
                Ok(again) -> again.close()
                Err(e) -> print(f"listen again: {e}")
            match l.accept(timeout_ms=50):
                Ok(s) -> s.close()
                Err(e) -> print(f"accept: {e}")
            match sock.connect_tcp(host, l.port()):
                Ok(c) ->
                    match l.accept(timeout_ms=3000):
                        Ok(s) ->
                            talk(c, s, wait)
                            s.close()
                            show("recv of one that left", c.recv_text())
                            shown("send 1", c.send_text("x"))
                            shown("send 2", c.send_text("x"))
                            show("recv after", c.recv_text())
                        Err(e) -> print(f"accept: {e}")
                    c.close()
                Err(e) -> print(f"connect: {e}")
            match sock.connect_tcp(host, l.port()):
                Ok(c) ->
                    match l.accept(timeout_ms=3000):
                        Ok(s) ->
                            shown("send", c.send_text("unread"))
                            s.close()
                            show("recv of one that read nothing", c.recv_text())
                            shown("send", c.send_text("x"))
                        Err(e) -> print(f"accept: {e}")
                    c.close()
                Err(e) -> print(f"connect: {e}")
            if wait:
                match sock.connect_tcp(host, l.port()):
                    Ok(c) ->
                        shown("send to one that does not read", c.send_text(long(20)))
                        c.close()
                    Err(e) -> print(f"connect: {e}")
            l.close()
        Err(e) -> print(f"listen: {e}")
    return 0

def main() -> int:
    pair("127.0.0.1", True)
    pair("::1", False)
    return 0
`, `listen again: listen tcp4 127.0.0.1:P: bind: address already in use
accept: accept tcp4 127.0.0.1:P: i/o timeout
send: ok 12
recv 2: ok [h`+"\xc3"+`] 2
recv 1: ok [`+"\xa9"+`] 1
recv: ok [llo world] 9
send nothing: ok 0
recv nothing: read tcp4 127.0.0.1:P->127.0.0.1:P: i/o timeout
recv of one that left: EOF
send 1: ok 1
send 2: write tcp 127.0.0.1:P->127.0.0.1:P: write: broken pipe
recv after: EOF
send: ok 6
recv of one that read nothing: read tcp 127.0.0.1:P->127.0.0.1:P: read: connection reset by peer
send: write tcp 127.0.0.1:P->127.0.0.1:P: write: broken pipe
send to one that does not read: write tcp 127.0.0.1:P->127.0.0.1:P: i/o timeout
listen again: listen tcp6 [::1]:P: bind: address already in use
accept: accept tcp6 [::1]:P: i/o timeout
send: ok 12
recv 2: ok [h`+"\xc3"+`] 2
recv 1: ok [`+"\xa9"+`] 1
recv: ok [llo world] 9
send nothing: ok 0
recv of one that left: EOF
send 1: ok 1
send 2: write tcp [::1]:P->[::1]:P: write: broken pipe
recv after: EOF
send: ok 6
recv of one that read nothing: read tcp [::1]:P->[::1]:P: read: connection reset by peer
send: write tcp [::1]:P->[::1]:P: write: broken pipe
`)
}

// A connection that is not made in five seconds is an Err that says so, of
// the host as it was written.
func TestE2ESocketDialTimesOut(t *testing.T) {
	port := fullListener(t)
	sameOnBothBackends(t, "dial_late", strings.ReplaceAll(`import std.socket as sock
import std.time as time

def main() -> int:
    t0 = time.now_ms()
    match sock.connect_tcp("127.0.0.1", PORT):
        Ok(c) ->
            print("connected")
            c.close()
        Err(e) -> print(e)
    took = time.now_ms() - t0
    print(took >= 4900 and took < 8000)
    return 0
`, "PORT", port), "dial tcp 127.0.0.1:P: i/o timeout\nTrue\n")
}

// The HTTP client dials a host as a socket does: what listens at every IPv4
// address is reached at [::], as it is by Go.
func TestE2EHTTPUnspecifiedHost(t *testing.T) {
	ln, err := net.Listen("tcp4", "0.0.0.0:0")
	if err != nil {
		t.Fatal(err)
	}
	srv := &http.Server{Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		_, _ = w.Write([]byte("here"))
	})}
	go func() { _ = srv.Serve(ln) }()
	t.Cleanup(func() { srv.Close() })
	port := strconv.Itoa(ln.Addr().(*net.TCPAddr).Port)
	sameOnBothBackends(t, "http_unspecified", strings.ReplaceAll(`import std.requests as req

def main() -> int:
    match req.get("http://[::]:PORT/", timeout_ms=3000):
        Ok(r) -> print(r.status, r.body)
        Err(e) -> print(e)
    return 0
`, "PORT", port), "200 here\n")
}
