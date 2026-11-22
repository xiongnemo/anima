package tests

import (
	"bufio"
	"bytes"
	"fmt"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"
)

// httpAnswers are answers of a server, well formed and not: each is read
// by both backends, which have to make the same of it.
func httpAnswers() []string {
	const h = "HTTP/1.1 200 OK\r\n"
	const c = "Connection: close\r\n"
	const ok = "Content-Length: 2\r\n\r\nok"
	cl := func(v string) string { return h + c + "Content-Length: " + v + "\r\n\r\nok" }
	te := func(v string) string { return h + c + "Transfer-Encoding: " + v + "\r\n\r\n2\r\nok\r\n0\r\n\r\n" }
	ch := func(body string) string { return h + c + "Transfer-Encoding: chunked\r\n\r\n" + body }
	hd := func(field string) string { return h + c + field + "\r\n" + ok }
	return []string{
		h + c + ok,
		h + ok,
		h + c + "\r\nuntil close",
		h + "\r\nok",
		"HTTP/1.0 200 OK\r\n\r\nold",
		// A NUL in the body, in the head, in the first line.
		h + c + "Content-Length: 5\r\n\r\nab\x00cd",
		h + c + "\r\n\x00",
		ch("3\r\na\x00b\r\n0\r\n\r\n"),
		hd("X-A: a\x00b"),
		hd("X\x00A: ab"),
		hd("\x00"),
		"HTTP/1.1 200 O\x00K\r\n" + c + ok,
		"HTTP/1.1 2\x000 OK\r\n" + c + ok,
		"\x00HTTP/1.1 200 OK\r\n" + c + ok,
		"HTTP/1.1\x00 200 OK\r\n" + c + ok,
		ch("2\x00\r\nok\r\n0\r\n\r\n"),
		ch("2\r\nok\r\n0\r\nX: \x00\r\n\r\n"),
		// The first line.
		"HTTP/1.1 200\r\n" + c + ok,
		"HTTP/1.1  200 OK\r\n" + c + ok,
		"HTTP/1.1 2x0 OK\r\n" + c + ok,
		"HTTP/1.1 20 OK\r\n" + c + ok,
		"HTTP/1.1 2000 OK\r\n" + c + ok,
		"HTTP/1.1 +20 OK\r\n" + c + ok,
		"HTTP/1.1 -00 OK\r\n" + c + ok,
		"HTTP/1.1 -20 OK\r\n" + c + ok,
		"HTTP/1.1 000 OK\r\n" + c + ok,
		"HTTP/1.1 999 OK\r\n" + c + ok,
		"HTTP/1.1\r\n" + c + ok,
		"HTTP/1.1\t200 OK\r\n" + c + ok,
		"HTTP/2.0 200 OK\r\n" + c + ok,
		"HTTP/1.10 200 OK\r\n" + c + ok,
		"HTTP/x.1 200 OK\r\n" + c + ok,
		"http/1.1 200 OK\r\n" + c + ok,
		"HTTP/0.9 200 OK\r\n" + c + ok,
		"ICY 200 OK\r\n" + c + ok,
		"HTTP/1.1 200 OK\n" + "Content-Length: 2\n\nok",
		"HTTP/1.1 200 OK",
		"HTTP/1.1 200 OK\r\n",
		"HTTP/1.1 200 OK\r\n" + c,
		"HTTP/1.1 200 OK\r\nConnection: clo",
		"HTTP/1.1 2",
		"garbage",
		"\r\n" + h + c + ok,
		"HTTP/1.1 200 \xe4\xbd\xa0\r\n" + c + ok,
		"HTTP/1.1 2\xe4\xbd\xa0 OK\r\n" + c + ok,
		"HTTP/1.1 2\xff0 OK\r\n" + c + ok,
		"HTTP/1.1 \xc2\xa00 OK\r\n" + c + ok,
		"HTTP/1.1 \"\\\a OK\r\n" + c + ok,
		"HTTP/1.1 \x7f\x1b\v OK\r\n" + c + ok,
		// The fields.
		hd("X-A:"),
		hd("X-A"),
		hd(": v"),
		hd("X A: v"),
		hd("X-A : v"),
		hd(" X-A: v"),
		hd("X-A: v\r\n continued"),
		hd("X-A: v\r\n\tcontinued: x"),
		hd("X-A: v\x01"),
		hd("X-A: v\x7f"),
		hd("X-A: \xe4\xbd\xa0\xff"),
		hd("X(A): v"),
		hd("X-A: v\r"),
		hd("X-A: v\rw"),
		h + " Connection: close\r\n" + ok,
		h + "\tConnection: close\r\n" + ok,
		h + c + "Content-Length: 2\r\n \r\nok",
		h + c + "Content-Length: 2\r\n 2\r\n\r\nok",
		h + c + "Content-Length: 2\r\n",
		h + c + "Content-Length: 2\r\n ",
		h + c + "Content-Length: 2\r\n\r",
		h + c + "content-length:2\r\n\r\nok",
		h + c + "CONTENT-LENGTH:\t2\t\r\n\r\nok",
		// The length of the body.
		cl("+2"), cl(" 2 "), cl("2, 2"), cl("2\r\nContent-Length: 2"), cl("2\r\nContent-Length: 1"),
		cl("2\r\nContent-Length:  2 "), cl("-1"), cl("99999999999999999999"), cl("9223372036854775807"),
		cl("9223372036854775808"), cl(""), cl("0x2"), cl("02"), cl("2 2"), cl("0"), cl("1"), cl("3"),
		cl("2\r\nTransfer-Encoding: chunked") + "\r\n0\r\n\r\n",
		te("Chunked"), te("gzip, chunked"), te("identity"), te("chunked, chunked"), te(" chunked "),
		te("chunked\r\nTransfer-Encoding: chunked"), te(""), te("chunked;q=1"),
		"HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\n\r\n",
		"HTTP/1.0 200 OK\r\nTransfer-Encoding: gzip\r\n" + ok,
		h + c + "Trailer: X\r\n" + ok,
		h + c + "Trailer: Content-Length\r\n" + ok,
		h + c + "Trailer: X, trailer\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\n\r\n",
		h + c + "Trailer: X\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\nX: 1\r\n\r\n",
		// Chunks and what follows them.
		ch("A\r\n0123456789\r\n0\r\n\r\n"), ch("a\r\n0123456789\r\n0\r\n\r\n"), ch("0002\r\nok\r\n0\r\n\r\n"),
		ch(" 2\r\nok\r\n0\r\n\r\n"), ch("2 \r\nok\r\n0\r\n\r\n"), ch("2\t\r\nok\r\n0\r\n\r\n"), ch("0x2\r\nok\r\n0\r\n\r\n"),
		ch("\r\nok\r\n0\r\n\r\n"), ch(";\r\nok\r\n0\r\n\r\n"), ch("FFFFFFFFFFFFFFFFF\r\nok\r\n0\r\n\r\n"),
		ch("2\nok\n0\n\n"), ch("2\r\nok\n0\r\n\r\n"), ch("2\r\nokX\r\n0\r\n\r\n"), ch("2\r\nok\r\n"), ch("2\r\nok\r\n0\r\n"),
		ch("2\r\nok\r\n0\r\nX: 1\r\n\r\n"), ch("2\r\nok\r\n0\r\nbad\r\n\r\n"), ch("2\r\nok\r\n0\r\nX: 1\r\n"),
		ch("2\r\nok\r\n0\r\n X: 1\r\n\r\n"), ch("2\r\nok\r\n0\r\nX: 1\n\n"), ch("2\r\nok\r\n0\r\n\n"), ch("2\r\nok\r\n0\r\nX"),
		ch("2\r\nok\r\n00\r\n\r\n"), ch("2;x=y\r\nok\r\n0;z\r\n\r\n"), ch("2\r;\r\nok\r\n0\r\n\r\n"), ch("2\r\r\nok\r\n0\r\n\r\n"),
		ch("g\r\n"), ch("-2\r\nok\r\n0\r\n\r\n"), ch("2\r\nok\r\n0\r\n\r\nextra"), ch("7fffffffffffffff\r\nok"),
		ch("8000000000000000\r\nok"), ch("ffffffffffffffff\r\nok"), ch(""), ch("2"), ch("2\r"), ch("2\r\no"), ch("2\r\nok"), ch("2\r\nok\r"),
		ch("0\r\n" + strings.Repeat("X: 1\r\n", 700) + "\r\n"),
		ch(strings.Repeat("0", 5000) + "\r\n\r\n"),
		ch(strings.Repeat("1;"+strings.Repeat("e", 40)+"\r\nx\r\n", 600) + "0\r\n\r\n"),
		ch(strings.Repeat("1;"+strings.Repeat("e", 40)+"\r\nx\r\n", 100) + "0\r\n\r\n"),
		// Answers that are not the answer, or have no body.
		"HTTP/1.1 302 Found\r\nLocation: /0\r\n" + c + ok,
		"HTTP/1.1 301 Moved\r\nLocation: /0\r\n" + c + ok,
		"HTTP/1.1 307 T\r\n" + c + ok,
		"HTTP/1.1 100 Continue\r\n\r\n" + h + c + ok,
		"HTTP/1.1 103 Early\r\nLink: x\r\n\r\nHTTP/1.1 100 Continue\r\n\r\n" + h + c + ok,
		"HTTP/1.1 100 Continue\r\nContent-Length: x\r\n\r\n" + h + c + ok,
		"HTTP/1.1 100 Continue\r\n\r\n",
		"HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 2",
		"HTTP/1.1 100 Continue\r\n\r\nbad\r\n\r\n",
		"HTTP/1.1 199 X\r\n" + c + ok,
		"HTTP/1.1 101 Switching\r\n" + c + ok,
		"HTTP/1.1 101 Switching\r\nUpgrade: x\r\nConnection: keep-alive, upgrade\r\n\r\nraw",
		"HTTP/1.1 101 Switching\r\nUpgrade: x\r\n\r\nraw",
		"HTTP/1.1 204 No\r\n" + c + ok,
		"HTTP/1.1 304 No\r\n" + c + ok,
		"HTTP/1.1 204 No\r\n" + c + "Transfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\n\r\n",
		"HTTP/1.1 204 No\r\n" + c + "Content-Length: x\r\n\r\n",
		"HTTP/1.1 500 Oops\r\n" + c + ok,
		h + c + "Content-Encoding: gzip\r\nContent-Length: 4\r\n\r\n\x1f\x8b\x08\x01",
	}
}

// mutate gives the answer with a few bytes of it changed, dropped, added
// or with its end cut off.
func mutate(r *rand.Rand, s string) string {
	b := []byte(s)
	odd := []byte("\x00\x00\r\n \t:;,-+0129afgxHTP/.\x7f\x80\xff\"\\")
	for n := 1 + r.Intn(3); n > 0 && len(b) > 0; n-- {
		at := r.Intn(len(b))
		switch r.Intn(6) {
		case 0, 1:
			b[at] = odd[r.Intn(len(odd))]
		case 2:
			b = append(b[:at], b[at+1:]...)
		case 3:
			b = append(b[:at], append([]byte{odd[r.Intn(len(odd))]}, b[at:]...)...)
		case 4:
			b = b[:at]
		case 5:
			if nl := bytes.IndexByte(b[at:], '\n'); nl >= 0 {
				end := at + nl + 1
				start := bytes.LastIndexByte(b[:at], '\n') + 1
				b = append(b[:end], append(append([]byte{}, b[start:end]...), b[end:]...)...)
			}
		}
	}
	return string(b)
}

// answerServer answers the request for /N with answers[N], in the pieces
// that cuts[N] cuts it in, one every few milliseconds.
func answerServer(t *testing.T, answers []string, cuts [][]int) string {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { ln.Close() })
	serve := func(c net.Conn) {
		defer c.Close()
		_ = c.SetDeadline(time.Now().Add(10 * time.Second))
		r := bufio.NewReader(c)
		line, err := r.ReadString('\n')
		parts := strings.Split(line, " ")
		if err != nil || len(parts) < 2 {
			return
		}
		for h := ""; h != "\r\n"; {
			if h, err = r.ReadString('\n'); err != nil {
				return
			}
		}
		n, err := strconv.Atoi(strings.TrimPrefix(parts[1], "/"))
		if err != nil || n < 0 || n >= len(answers) {
			return
		}
		rest := answers[n]
		for _, cut := range cuts[n] {
			if _, err := c.Write([]byte(rest[:cut])); err != nil {
				return
			}
			rest = rest[cut:]
			time.Sleep(3 * time.Millisecond)
		}
		_, _ = c.Write([]byte(rest))
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
	return strconv.Itoa(ln.Addr().(*net.TCPAddr).Port)
}

// The native HTTP client makes of an answer what the VM's does, whatever
// the answer and in however many pieces it arrives: the same status and
// body, or the same Err. It took a malformed answer for a good one where
// Go refuses it, read a length or a chunk Go does not, gave the 1xx answer
// before the answer, and ended a head or a body at a NUL. ANIMA_HTTP_FUZZ
// sets how many changed answers are tried after the listed ones,
// ANIMA_HTTP_SEED which.
func TestE2EHTTPAnswerParity(t *testing.T) {
	answers := httpAnswers()
	listed := len(answers)
	extra, seed := 300, int64(1)
	if v, err := strconv.Atoi(os.Getenv("ANIMA_HTTP_FUZZ")); err == nil {
		extra = v
	}
	if v, err := strconv.ParseInt(os.Getenv("ANIMA_HTTP_SEED"), 10, 64); err == nil {
		seed = v
	}
	r := rand.New(rand.NewSource(seed))
	for i := 0; i < extra; i++ {
		answers = append(answers, mutate(r, answers[r.Intn(listed)]))
	}
	cuts := make([][]int, len(answers))
	// Each listed answer again in a few pieces, and one changed answer in
	// ten: an answer is read from where the last piece left it.
	for i, n := 0, len(answers); i < n; i++ {
		a := answers[i]
		if (i >= listed && r.Intn(10) != 0) || len(a) < 2 {
			continue
		}
		var cut []int
		for left, k := len(a), 1+r.Intn(3); k > 0 && left > 1; k-- {
			c := 1 + r.Intn(left-1)
			if len(a) > 200 && r.Intn(2) == 0 {
				// Near the start, where the head is.
				c = 1 + r.Intn(min(left-1, 120))
			}
			cut = append(cut, c)
			left -= c
		}
		answers = append(answers, a)
		cuts = append(cuts, cut)
	}
	port := answerServer(t, answers, cuts)
	src := strings.NewReplacer("PORT", port, "COUNT", strconv.Itoa(len(answers))).Replace(`import std.requests as req

def get(n: int) -> int:
    match req.get(f"http://127.0.0.1:PORT/{n}", timeout_ms=5000):
        Ok(r) -> print(f"#{n} ok", r.status, r.ok, len(r.body), r.body)
        Err(m) -> print(f"#{n} err", m)
    return 0

def main() -> int:
    for i in 0..COUNT:
        get(i)
    return 0
`)
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, "answers.anm")
	if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	// Only what the program prints: Go logs to stderr about a connection
	// that says more than it was asked.
	vmOut, err := exec.Command(animaBin, "run", path).Output()
	if err != nil {
		t.Fatalf("VM: %v\n%s", err, vmOut)
	}
	nativeBin := filepath.Join(tmp, "answers")
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	natCmd := exec.Command(nativeBin)
	var natErr bytes.Buffer
	natCmd.Stderr = &natErr
	natOut, err := natCmd.Output()
	if err != nil {
		t.Fatalf("native: %v\n%s\n%s", err, natOut, natErr.String())
	}
	split := func(out []byte) map[int]string {
		got := map[int]string{}
		for _, part := range strings.Split("\n"+string(out), "\n#")[1:] {
			num, rest, _ := strings.Cut(part, " ")
			n, err := strconv.Atoi(num)
			if err != nil {
				t.Fatalf("output is not by answer: %q", part)
			}
			got[n] = strings.TrimSuffix(rest, "\n")
		}
		return got
	}
	vm, nat := split(vmOut), split(natOut)
	bad := 0
	whole := map[string]int{}
	for i, a := range answers {
		if vm[i] != nat[i] || vm[i] == "" {
			bad++
			if bad <= 20 {
				t.Errorf("answer %d %q in pieces %v\n    VM:     %q\n    native: %q", i, a, cuts[i], vm[i], nat[i])
			}
		}
		// In pieces it is the answer it is whole.
		if first, seen := whole[a]; !seen {
			whole[a] = i
		} else if was, now := strings.ReplaceAll(vm[first], fmt.Sprintf("/%d\"", first), "/N\""), strings.ReplaceAll(nat[i], fmt.Sprintf("/%d\"", i), "/N\""); was != now {
			bad++
			if bad <= 20 {
				t.Errorf("answer %d %q\n    whole:             %q\n    in pieces %v: %q", i, a, was, cuts[i], now)
			}
		}
		if strings.Contains(vm[i], "\x00") || strings.Contains(nat[i], "\x00") {
			t.Errorf("answer %d %q gives a str with a NUL\n    VM:     %q\n    native: %q", i, a, vm[i], nat[i])
		}
	}
	if bad > 0 {
		t.Fatalf("%d of %d answers are read differently", bad, len(answers))
	}
	// What a few of them are, so that the two do not agree on a mistake.
	for i, want := range map[int]string{
		0: "ok 200 True 2 ok",
		5: "err text holds a NUL",
		8: fmt.Sprintf("err Get \"http://127.0.0.1:%s/8\": net/http: HTTP/1.x transport connection broken: malformed MIME header line: X-A: a\\x00b", port),
	} {
		if vm[i] != want {
			t.Errorf("answer %d %q\n    is:   %q\n    want: %q", i, answers[i], vm[i], want)
		}
	}
}

// A str holds no NUL. The native backend's strings end at one: what it
// read of a file, a socket or an HTTP body that held one was cut there,
// with a length, a hash and bytes that were not the VM's. Such a text is
// now refused where it is read, on both backends.
func TestE2ETextWithANUL(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "nul.bin"), []byte("ab\x00cd\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "text.txt"), []byte("ab cd\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	go func() {
		// To each backend: a connection that says a NUL, then one that
		// does not.
		for _, say := range []string{"ab\x00cd", "abcd", "ab\x00cd", "abcd"} {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			_, _ = c.Write([]byte(say))
			_ = c.Close()
		}
	}()
	src := strings.NewReplacer("DIR", dir, "PORT", strconv.Itoa(ln.Addr().(*net.TCPAddr).Port)).Replace(`import std.fs as fs
import std.socket as sock

def whole(path: str) -> int:
    match fs.read_text(path):
        Ok(t) -> print("read_text", len(t), t)
        Err(m) -> print("read_text:", m)
    match fs.open(path, "r"):
        Ok(f) ->
            match f.read_text():
                Ok(t) -> print("File.read_text", len(t))
                Err(m) -> print("File.read_text:", m)
            f.close()
        Err(m) -> print("open:", m)
    return 0

def said() -> int:
    match sock.connect_tcp("127.0.0.1", PORT):
        Ok(c) ->
            match c.recv_text(100):
                Ok(t) -> print("recv_text", len(t), t)
                Err(m) -> print("recv_text:", m)
            c.close()
        Err(m) -> print("connect:", m)
    return 0

def main() -> int:
    whole("DIR/nul.bin")
    whole("DIR/text.txt")
    said()
    said()
    return 0
`)
	runOnBothBackends(t, "text_nul", src, `read_text: text holds a NUL
File.read_text: text holds a NUL
read_text 6 ab cd

File.read_text 6
recv_text: text holds a NUL
recv_text 4 abcd
`)

	// Nor does a source text hold one, in a string or anywhere else.
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, "nul_source.anm")
	if err := os.WriteFile(path, []byte("def main() -> int:\n    print(\"ab\x00cd\")\n    return 0\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	for _, cmd := range []string{"check", "run", "build"} {
		out, err := exec.Command(animaBin, cmd, path).CombinedOutput()
		if err == nil || !strings.Contains(string(out), "nul_source.anm:2:14: NUL byte in source") {
			t.Errorf("anima %s: err=%v, output:\n%s", cmd, err, out)
		}
	}
}

// A server that says part of an answer and then nothing: the request ends
// when its time is up, with the Err of the part it was in, or at once when
// what was said is an answer or cannot be one.
func TestE2EHTTPAnswerThenSilence(t *testing.T) {
	const h = "HTTP/1.1 200 OK\r\n"
	answers := map[string]string{
		"/first-line": "HTTP/1.1 200 OK",
		"/head":       h + "Content-Length: 2\r\n",
		"/1xx":        "HTTP/1.1 100 Continue\r\n\r\n",
		"/short":      h + "Content-Length: 5\r\n\r\nab",
		"/chunk":      h + "Transfer-Encoding: chunked\r\n\r\n5\r\nab",
		"/trailer":    h + "Transfer-Encoding: chunked\r\n\r\n2\r\nab\r\n0\r\nX: 1\r\n",
		"/to-close":   h + "\r\nab",
		"/length":     h + "Content-Length: 2\r\n\r\nab",
		"/chunked":    h + "Transfer-Encoding: chunked\r\n\r\n2\r\nab\r\n0\r\n\r\n",
		"/204":        "HTTP/1.1 204 No Content\r\n\r\n",
		"/garbage":    "garbage\r\n",
		"/bad-length": h + "Content-Length: x\r\n\r\n",
		"/bad-chunk":  h + "Transfer-Encoding: chunked\r\n\r\nx\r\n",
	}
	hold := map[string]bool{}
	for path := range answers {
		hold[path] = true
	}
	port := rawHTTPServer(t, answers, hold)
	src := strings.ReplaceAll(`import std.requests as req
import std.time as time

def get(path: str) -> int:
    t0 = time.now_ms()
    match req.get("http://127.0.0.1:PORT/" + path, timeout_ms=300):
        Ok(r) -> print(path, r.status, len(r.body), r.body)
        Err(m) -> print(path, "ERR", m)
    took = time.now_ms() - t0
    if took < 250:
        print("  at once")
    elif took < 900:
        print("  when the time was up")
    else:
        print("  late")
    return 0

def main() -> int:
    for path in ["first-line", "head", "1xx", "short", "chunk", "trailer", "to-close", "length", "chunked", "204", "garbage", "bad-length", "bad-chunk"]:
        get(path)
    return 0
`, "PORT", port)
	const headers = "context deadline exceeded (Client.Timeout exceeded while awaiting headers)\n  when the time was up\n"
	const body = "context deadline exceeded (Client.Timeout or context cancellation while reading body)\n  when the time was up\n"
	get := func(path string) string { return path + ` ERR Get "http://127.0.0.1:` + port + `/` + path + `": ` }
	runOnBothBackends(t, "http_silence", src, get("first-line")+headers+
		get("head")+headers+
		get("1xx")+headers+
		"short ERR "+body+
		"chunk ERR "+body+
		"trailer ERR "+body+
		"to-close ERR "+body+
		"length 200 2 ab\n  at once\n"+
		"chunked 200 2 ab\n  at once\n"+
		"204 204 0 \n  at once\n"+
		get("garbage")+"net/http: HTTP/1.x transport connection broken: malformed HTTP response \"garbage\"\n  at once\n"+
		get("bad-length")+"net/http: HTTP/1.x transport connection broken: bad Content-Length \"x\"\n  at once\n"+
		"bad-chunk ERR invalid byte in chunk length\n  at once\n")
}
