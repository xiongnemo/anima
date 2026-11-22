package tests

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
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

// What examples/stun.anm reads of a message, written again in Go. The
// functions below say what answer, request_of and reply of the example give,
// as the main of stunReads prints it.

var stunID = []byte{0x21, 0x12, 0xA4, 0x42, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}

type stunAddr struct {
	ip   uint32
	port uint16
}

func (a *stunAddr) String() string {
	if a == nil {
		return "Nowhere"
	}
	return fmt.Sprintf("At(%d, %d)", a.ip, a.port)
}

func stunAddress(v []byte, xored bool) *stunAddr {
	if len(v) != 8 || v[1] != 1 {
		return nil
	}
	a := &stunAddr{binary.BigEndian.Uint32(v[4:]), binary.BigEndian.Uint16(v[2:])}
	if xored {
		a.port ^= 0x2112
		a.ip ^= 0x2112A442
	}
	if a.port == 0 {
		return nil
	}
	return a
}

// stunAttrs gives the attributes of a message that is one, each with its value.
func stunAttrs(msg []byte) (kinds []uint16, values [][]byte, ok bool) {
	rest := msg[20:]
	for len(rest) >= 4 {
		size := int(binary.BigEndian.Uint16(rest[2:]))
		padded := (size + 3) / 4 * 4
		if padded > len(rest)-4 {
			return nil, nil, false
		}
		kinds = append(kinds, binary.BigEndian.Uint16(rest))
		values = append(values, rest[4:4+size])
		rest = rest[4+padded:]
	}
	return kinds, values, len(rest) == 0
}

func stunAnswer(msg []byte, from *stunAddr) string {
	if len(msg) < 20 || len(msg) > 65535 {
		return "-"
	}
	kind := binary.BigEndian.Uint16(msg)
	if kind != 0x0101 && kind != 0x0111 {
		return "-"
	}
	if int(binary.BigEndian.Uint16(msg[2:])) != len(msg)-20 || !bytes.Equal(msg[4:20], stunID) {
		return "-"
	}
	kinds, values, ok := stunAttrs(msg)
	if !ok {
		return "-"
	}
	var plain, xored, other *stunAddr
	code := 0
	for i, k := range kinds {
		v := values[i]
		switch {
		case k == 0x0001:
			plain = stunAddress(v, false)
		case k == 0x0020 || k == 0x8020:
			xored = stunAddress(v, true)
		case k == 0x802c || k == 0x0005 && other == nil:
			other = stunAddress(v, false)
		case k == 0x0009:
			if len(v) < 4 || v[3] > 99 {
				return "-"
			}
			code = int(v[2]&7)*100 + int(v[3])
		}
	}
	switch {
	case kind == 0x0111:
		return fmt.Sprintf("Refused(%d)", code)
	case xored != nil:
		return fmt.Sprintf("Heard(%v, %v, %v)", xored, other, from)
	case plain != nil:
		return fmt.Sprintf("Heard(%v, %v, %v)", plain, other, from)
	}
	return "-"
}

func stunAttr(kind uint16, a stunAddr, xored bool) []byte {
	b := binary.BigEndian.AppendUint16(nil, kind)
	b = append(b, 0, 8, 0, 1)
	if xored {
		a.port ^= 0x2112
		a.ip ^= 0x2112A442
	}
	b = binary.BigEndian.AppendUint16(b, a.port)
	return binary.BigEndian.AppendUint32(b, a.ip)
}

func stunMessage(kind uint16, id, body []byte) []byte {
	b := binary.BigEndian.AppendUint16(nil, kind)
	b = binary.BigEndian.AppendUint16(b, uint16(len(body)))
	return append(append(b, id...), body...)
}

// stunReplies gives what a server at ends answers a request heard at each
// of its four ends, in each of its four manners: the end it answers from and
// the answer, or "dropped".
func stunReplies(msg []byte, seen stunAddr, ends [4]stunAddr) []string {
	if len(msg) < 20 || len(msg) > 1500 {
		return []string{"-"}
	}
	if binary.BigEndian.Uint16(msg) != 1 || int(binary.BigEndian.Uint16(msg[2:])) != len(msg)-20 {
		return []string{"-"}
	}
	kinds, values, ok := stunAttrs(msg)
	if !ok {
		return []string{"-"}
	}
	change := 0
	var unknown []byte
	for i, k := range kinds {
		switch {
		case k == 0x0003:
			if len(values[i]) != 4 {
				return []string{"-"}
			}
			change = int(values[i][3]) & 6
		case k < 0x8000:
			unknown = binary.BigEndian.AppendUint16(unknown, k)
		}
	}
	id := msg[4:20]
	modern := binary.BigEndian.Uint32(id) == 0x2112A442
	var out []string
	for at := 0; at < 4; at++ {
		for manner := 0; manner < 4; manner++ {
			un := unknown
			if change != 0 && manner >= 2 {
				un = binary.BigEndian.AppendUint16(append([]byte(nil), un...), 3)
			}
			if len(un) > 1000 {
				out = append(out, "dropped")
				continue
			}
			if len(un) > 0 {
				body := append([]byte{0, 9, 0, 21, 0, 0, 4, 20}, "Unknown Attribute\x00\x00\x00"...)
				body = append(body, 0, 10)
				body = binary.BigEndian.AppendUint16(body, uint16(len(un)))
				body = append(body, un...)
				for len(body)%4 != 0 {
					body = append(body, 0)
				}
				out = append(out, fmt.Sprintf("%d %x", at, stunMessage(0x0111, id, body)))
				continue
			}
			from := at ^ change>>1
			var body []byte
			if modern && manner != 1 {
				body = append(stunAttr(0x0020, seen, true), stunAttr(0x0001, seen, false)...)
				body = append(body, stunAttr(0x802b, ends[from], false)...)
				if manner != 2 {
					body = append(body, stunAttr(0x802c, ends[3-at], false)...)
				}
			} else {
				body = append(stunAttr(0x0001, seen, false), stunAttr(0x0004, ends[from], false)...)
				body = append(body, stunAttr(0x0005, ends[3-at], false)...)
			}
			out = append(out, fmt.Sprintf("%d %x", from, stunMessage(0x0101, id, body)))
		}
	}
	return out
}

// stunReads is the main the example is given in place of its own: each
// argument is a message in hex, read as an answer and as a request.
const stunReads = `def main() -> int:
    args = cli.args()
    id = bytes.from_hex("2112a442000102030405060708090a0b")
    st = Stand(0x7F000001, 0x7F000002, 3478, 3479, 1)
    for i in 1..len(args):
        msg = bytes.from_hex(args[i])
        match answer(msg, id, At(0x7F000001, 3478)):
            Some(a) -> print(a)
            None -> print("-")
        match request_of(msg):
            None -> print("-")
            Some(q) ->
                for at in 0..4:
                    for manner in 0..4:
                        match reply(q, at, At(0xC0000201, 54321), st, manner, "192.0.2.1", 54321):
                            Say(out, data, host, port) -> print(out, data.to_hex())
                            _ -> print("dropped")
    return 0
`

func stunSeeds() [][]byte {
	a := stunAddr{0xCB007107, 40000}
	o := stunAddr{0x7F000002, 3479}
	other := []byte{9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9}
	join := func(parts ...[]byte) []byte { return bytes.Join(parts, nil) }
	attr := func(kind uint16, v string) []byte {
		b := binary.BigEndian.AppendUint16(nil, kind)
		b = binary.BigEndian.AppendUint16(b, uint16(len(v)))
		b = append(b, v...)
		for len(b)%4 != 0 {
			b = append(b, 0)
		}
		return b
	}
	return [][]byte{
		stunMessage(0x0101, stunID, stunAttr(0x0001, a, false)),
		stunMessage(0x0101, stunID, stunAttr(0x0020, a, true)),
		stunMessage(0x0101, stunID, join(stunAttr(0x0020, a, true), stunAttr(0x0001, o, false), stunAttr(0x802b, o, false), stunAttr(0x802c, o, false))),
		stunMessage(0x0101, stunID, join(stunAttr(0x0001, a, false), stunAttr(0x0004, a, false), stunAttr(0x0005, o, false))),
		stunMessage(0x0101, stunID, join(stunAttr(0x0001, a, false), stunAttr(0x0005, a, false), stunAttr(0x802c, o, false), stunAttr(0x0005, a, false))),
		stunMessage(0x0101, stunID, join(stunAttr(0x0005, o, false), stunAttr(0x0005, a, false), stunAttr(0x0020, a, true))),
		stunMessage(0x0101, stunID, join(stunAttr(0x8020, a, true), attr(0x8022, "a server"), attr(0x8028, "\x01\x02\x03\x04"))),
		stunMessage(0x0101, stunID, join(attr(0x0001, "\x00\x02\x9c\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01"), stunAttr(0x0020, a, true))),
		stunMessage(0x0101, stunID, stunAttr(0x0001, stunAddr{1, 0}, false)),
		stunMessage(0x0101, stunID, nil),
		stunMessage(0x0101, other, stunAttr(0x0001, a, false)),
		stunMessage(0x0111, stunID, attr(0x0009, "\x00\x00\x04\x14Unknown Attribute")),
		stunMessage(0x0111, stunID, join(attr(0x0009, "\x00\x00\x07\x63"), attr(0x000a, "\x00\x03"))),
		stunMessage(0x0111, stunID, attr(0x0009, "\x00\x00\xff\x64")),
		stunMessage(0x0111, stunID, attr(0x0009, "\x00\x00\x04")),
		stunMessage(0x0111, stunID, nil),
		stunMessage(0x0001, stunID, nil),
		stunMessage(0x0001, other, nil),
		stunMessage(0x0001, stunID, attr(0x0003, "\x00\x00\x00\x06")),
		stunMessage(0x0001, stunID, attr(0x0003, "\x00\x00\x00\x02")),
		stunMessage(0x0001, other, attr(0x0003, "\x00\x00\x00\x04")),
		stunMessage(0x0001, stunID, attr(0x0003, "\xff\xff\xff\xff")),
		stunMessage(0x0001, stunID, attr(0x0003, "\x00\x06")),
		stunMessage(0x0001, stunID, join(attr(0x8022, "a client"), attr(0x0003, "\x00\x00\x00\x06"), attr(0x8028, "\x01\x02\x03\x04"))),
		stunMessage(0x0001, stunID, join(attr(0x0008, "01234567890123456789"), attr(0x0006, "name"), attr(0x0027, "\x12\x34"))),
		stunMessage(0x0001, other, join(attr(0x0002, "\x00\x01\x12\x34\x01\x02\x03\x04"), attr(0x0003, "\x00\x00\x00\x06"))),
		stunMessage(0x0001, stunID, attr(0x8000, "")),
		stunMessage(0x0001, stunID, attr(0x7fff, "")),
		stunMessage(0x0001, stunID, bytes.Repeat([]byte{0, 0x26, 0, 0}, 300)),
		stunMessage(0x0001, stunID, bytes.Repeat([]byte{0, 0x26, 0, 0}, 370)),
		stunMessage(0x0002, stunID, nil),
		stunMessage(0x0011, stunID, nil),
		nil,
		{0},
		bytes.Repeat([]byte{0}, 19),
		bytes.Repeat([]byte{0}, 20),
		bytes.Repeat([]byte{0xff}, 64),
	}
}

func stunChange(r *rand.Rand, seeds [][]byte) []byte {
	m := append([]byte(nil), seeds[r.Intn(len(seeds))]...)
	for n := 1 + r.Intn(3); n > 0; n-- {
		switch k := r.Intn(8); {
		case k == 0 && len(m) > 0:
			m[r.Intn(len(m))] ^= 1 << r.Intn(8)
		case k == 1 && len(m) > 0:
			m[r.Intn(len(m))] = byte(r.Intn(256))
		case k == 2 && len(m) > 0:
			m = m[:r.Intn(len(m))]
		case k == 3:
			for i := r.Intn(9); i > 0; i-- {
				m = append(m, byte(r.Intn(4)))
			}
		case k == 4 && len(m) > 20:
			// An attribute of another message, or its value, is put after the header or at the end.
			o := seeds[r.Intn(len(seeds))]
			if len(o) > 24 {
				cut := 20 + r.Intn(len(o)-20)
				if r.Intn(2) == 0 {
					m = append(m, o[cut:]...)
				} else {
					m = append(append(append([]byte(nil), m[:20]...), o[cut:]...), m[20:]...)
				}
			}
		case k == 5 && len(m) > 24:
			// The length of an attribute is another.
			binary.BigEndian.PutUint16(m[22:], uint16(r.Intn(40)))
		case k == 6 && len(m) >= 2:
			binary.BigEndian.PutUint16(m, []uint16{0x0001, 0x0101, 0x0111}[r.Intn(3)])
		}
	}
	// Most are as long as they say, or nothing after the header is read.
	if len(m) >= 20 && len(m) < 65556 && r.Intn(4) != 0 {
		binary.BigEndian.PutUint16(m[2:], uint16(len(m)-20))
	}
	return m
}

// The example reads a datagram as the Go above does, on both backends:
// whatever its bytes, it is an answer, a request or neither, and a request
// is answered with the same bytes from the same end.
// ANIMA_STUN_FUZZ sets how many changed messages are read after the listed
// ones, ANIMA_STUN_SEED which.
func TestE2EStunReadsADatagram(t *testing.T) {
	raw, err := os.ReadFile("../examples/stun.anm")
	if err != nil {
		t.Fatal(err)
	}
	src := string(raw)
	cut := strings.Index(src, "def main() -> int:")
	if cut < 0 {
		t.Fatal("the example has no main")
	}
	vm, native := bothBackends(t, "stun_reads", src[:cut]+stunReads)

	n, seed := 600, int64(1)
	if s := os.Getenv("ANIMA_STUN_FUZZ"); s != "" {
		n, _ = strconv.Atoi(s)
	}
	if s := os.Getenv("ANIMA_STUN_SEED"); s != "" {
		seed, _ = strconv.ParseInt(s, 10, 64)
	}
	seeds := stunSeeds()
	msgs := append([][]byte(nil), seeds...)
	r := rand.New(rand.NewSource(seed))
	for i := 0; i < n; i++ {
		msgs = append(msgs, stunChange(r, seeds))
	}
	from := &stunAddr{0x7F000001, 3478}
	ends := [4]stunAddr{{0x7F000001, 3478}, {0x7F000001, 3479}, {0x7F000002, 3478}, {0x7F000002, 3479}}
	answers, requests := 0, 0
	for len(msgs) > 0 {
		batch := msgs[:min(200, len(msgs))]
		msgs = msgs[len(batch):]
		var want, args []string
		for _, m := range batch {
			a := stunAnswer(m, from)
			q := stunReplies(m, stunAddr{0xC0000201, 54321}, ends)
			if a != "-" {
				answers++
			}
			if len(q) > 1 {
				requests++
			}
			want = append(append(want, a), q...)
			args = append(args, hex.EncodeToString(m))
		}
		for name, argv := range map[string][]string{"vm": vm, "native": native} {
			out, err := exec.Command(argv[0], append(argv[1:], args...)...).CombinedOutput()
			if err != nil {
				t.Fatalf("%s: %v\n%s", name, err, out)
			}
			got := strings.Split(strings.TrimRight(string(out), "\n"), "\n")
			if len(got) != len(want) {
				t.Fatalf("%s wrote %d lines, not %d:\n%s", name, len(got), len(want), out)
			}
			at := 0
			for _, m := range batch {
				lines := 1 + len(stunReplies(m, stunAddr{0xC0000201, 54321}, ends))
				for i := at; i < at+lines; i++ {
					if got[i] != want[i] {
						t.Fatalf("%s reads %x as\n%s\nnot\n%s", name, m, strings.Join(got[at:at+lines], "\n"), strings.Join(want[at:at+lines], "\n"))
					}
				}
				at += lines
			}
		}
	}
	if answers < 20 || requests < 20 {
		t.Fatalf("only %d answers and %d requests were read as such", answers, requests)
	}
}

// freeStunPorts gives two ports that are free on both 127.0.0.1 and 127.0.0.2.
func freeStunPorts(t *testing.T) (int, int) {
	t.Helper()
	var ports []int
	for tries := 0; len(ports) < 2 && tries < 50; tries++ {
		a, err := net.ListenPacket("udp4", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		p := a.LocalAddr().(*net.UDPAddr).Port
		b, err := net.ListenPacket("udp4", "127.0.0.2:"+strconv.Itoa(p))
		a.Close()
		if err != nil {
			continue
		}
		b.Close()
		ports = append(ports, p)
	}
	if len(ports) < 2 || ports[0] == ports[1] {
		t.Fatal("no two free ports")
	}
	return ports[0], ports[1]
}

// The example's server answers from the end it is asked to, with the address
// it saw and the address of its other end, and its client finds no NAT in
// front of a host that has none. On both backends, over real sockets.
func TestE2EStunServerAndClient(t *testing.T) {
	raw, err := os.ReadFile("../examples/stun.anm")
	if err != nil {
		t.Fatal(err)
	}
	vm, native := bothBackends(t, "stun", string(raw))
	for name, argv := range map[string][]string{"vm": vm, "native": native} {
		t.Run(name, func(t *testing.T) {
			p, p2 := freeStunPorts(t)
			ends := []string{
				fmt.Sprintf("127.0.0.1:%d", p), fmt.Sprintf("127.0.0.1:%d", p2),
				fmt.Sprintf("127.0.0.2:%d", p), fmt.Sprintf("127.0.0.2:%d", p2),
			}
			server := exec.Command(argv[0], append(argv[1:], "server", "127.0.0.1", "127.0.0.2", strconv.Itoa(p), strconv.Itoa(p2))...)
			var said lockedBuf
			server.Stdout, server.Stderr = &said, &said
			if err := server.Start(); err != nil {
				t.Fatal(err)
			}
			defer func() {
				server.Process.Kill()
				server.Wait()
			}()

			c, err := net.ListenPacket("udp4", "127.0.0.1:0")
			if err != nil {
				t.Fatal(err)
			}
			defer c.Close()
			me := c.LocalAddr().(*net.UDPAddr)
			seen := fmt.Sprintf("At(%d, %d)", 0x7F000001, me.Port)
			// ask sends one request to an end and gives the end that answered and what it said.
			ask := func(to string, id, body []byte, wait time.Duration) (string, []byte) {
				dst, _ := net.ResolveUDPAddr("udp4", to)
				if _, err := c.WriteTo(stunMessage(1, id, body), dst); err != nil {
					t.Fatal(err)
				}
				buf := make([]byte, 2048)
				c.SetReadDeadline(time.Now().Add(wait))
				for {
					n, from, err := c.ReadFrom(buf)
					if err != nil {
						return "", nil
					}
					if n >= 20 && bytes.Equal(buf[4:20], id) {
						return from.String(), buf[:n]
					}
				}
			}
			// The VM proves the program before it runs it.
			up := false
			for begun := time.Now(); !up && time.Since(begun) < 60*time.Second; {
				from, _ := ask(ends[0], stunID, nil, 100*time.Millisecond)
				up = from != ""
			}
			if !up {
				t.Fatalf("the server does not answer:\n%s", said.String())
			}

			change := func(flags byte) []byte { return []byte{0, 3, 0, 4, 0, 0, 0, flags} }
			old := []byte{9, 9, 9, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
			for _, c := range []struct {
				to   int
				id   []byte
				body []byte
				from int
				want string
			}{
				{0, stunID, nil, 0, "Heard"},
				{1, stunID, nil, 1, "Heard"},
				{2, stunID, nil, 2, "Heard"},
				{3, stunID, nil, 3, "Heard"},
				{0, stunID, change(6), 3, "Heard"},
				{0, stunID, change(4), 2, "Heard"},
				{0, stunID, change(2), 1, "Heard"},
				{3, stunID, change(6), 0, "Heard"},
				{2, stunID, change(2), 3, "Heard"},
				{1, old, change(6), 2, "old"},
				{0, old, nil, 0, "old"},
				{0, stunID, []byte{0, 8, 0, 4, 1, 2, 3, 4}, 0, "Refused(420)"},
				{0, stunID, []byte{0, 3, 0, 2, 0, 6, 0, 0}, -1, ""},
				{0, stunID, []byte{0, 3, 0, 8, 0, 0, 0, 6}, -1, ""},
			} {
				wait := 2 * time.Second
				if c.from < 0 {
					wait = 150 * time.Millisecond
				}
				from, msg := ask(ends[c.to], c.id, c.body, wait)
				if c.from < 0 {
					if from != "" {
						t.Fatalf("% x to %s is answered: %x", c.body, ends[c.to], msg)
					}
					continue
				}
				if from != ends[c.from] {
					t.Fatalf("% x to %s is answered from %q, not %s:\n%s", c.body, ends[c.to], from, ends[c.from], said.String())
				}
				kinds, _, ok := stunAttrs(msg)
				if !ok {
					t.Fatalf("an answer with no end: %x", msg)
				}
				if c.want == "old" {
					// To a request without the cookie: the three addresses of RFC 3489, none of them XORed.
					if fmt.Sprint(kinds) != "[1 4 5]" {
						t.Fatalf("an old request is answered with %v", kinds)
					}
					continue
				}
				got := stunAnswer(msg, &stunAddr{1, 1})
				want := c.want
				if want == "Heard" {
					ip, port, _ := strings.Cut(ends[3-c.to], ":")
					n, _ := strconv.Atoi(port)
					other := stunAddr{0x7F000001, uint16(n)}
					if ip == "127.0.0.2" {
						other.ip = 0x7F000002
					}
					want = fmt.Sprintf("Heard(%s, %v, At(1, 1))", seen, &other)
				}
				if got != want {
					t.Fatalf("% x to %s is answered %s, not %s", c.body, ends[c.to], got, want)
				}
			}

			out, err := exec.Command(argv[0], append(argv[1:], "client", "127.0.0.1", strconv.Itoa(p))...).CombinedOutput()
			if err != nil {
				t.Fatalf("the client: %v\n%s", err, out)
			}
			lines := strings.Split(strings.TrimSpace(string(out)), "\n")
			want := []string{"mapped address: 127.0.0.1:", "mapping:        none", "filtering:      endpoint-independent", "RFC 3489:       open internet"}
			if len(lines) != 4 || !strings.HasPrefix(lines[0], want[0]) || strings.Join(lines[1:], "\n") != strings.Join(want[1:], "\n") {
				t.Fatalf("the client found\n%s", out)
			}
		})
	}

	// Arguments that are no address, no port or too few are the usage and exit 2, on both backends.
	for _, args := range [][]string{
		{"bogus"}, {"client"}, {"client", "h", "0"}, {"client", "h", "65536"}, {"client", "h", "99999999999999999999"},
		{"client", "h", "34 78"}, {"client", "h", "-1"}, {"client", "h", ""}, {"client", "h", "1", "2"},
		{"server", "127.0.0.1"}, {"server", "127.0.0.1", "127.0.0.2", "3478"}, {"server", "127.0.0.1", "127.0.0.1"},
		{"server", "1.2.3", "4.5.6.7"}, {"server", "256.1.1.1", "1.1.1.1"}, {"server", "1.1.1.1.", "1.1.1.2"},
		{"server", "1..1.1", "1.1.1.2"}, {"server", "1.1.1.0001", "1.1.1.2"}, {"server", "1.1.1.1", "1.1.1.2", "7", "7"},
		{"server", "", "1.1.1.2"}, {"server", "1.1.1.1", "1.1.1.2", "0", "7"},
	} {
		for name, argv := range map[string][]string{"vm": vm, "native": native} {
			out, err := exec.Command(argv[0], append(argv[1:], args...)...).CombinedOutput()
			code := -1
			if e, ok := err.(*exec.ExitError); ok {
				code = e.ExitCode()
			}
			if code != 2 || !strings.HasPrefix(string(out), "usage: stun ") {
				t.Fatalf("%s %q: exit %d (%v)\n%s", name, args, code, err, out)
			}
		}
	}
}

// What the example says the checker holds of it is held: with one check of
// a length, one close of a socket or one bound of a number taken out, the
// example is refused, at that place.
func TestE2EStunIsRefusedWithoutItsChecks(t *testing.T) {
	raw, err := os.ReadFile("../examples/stun.anm")
	if err != nil {
		t.Fatal(err)
	}
	src := string(raw)
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	for i, c := range []struct{ old, new, want string }{
		// A datagram shorter than a header is read as one.
		{"if msg.len() < 20 or msg.len() > 65535:", "if msg.len() < 3 or msg.len() > 65535:", "def:answer.byteview_bounds"},
		{"if msg.len() < 20 or msg.len() > 1500:", "if msg.len() < 3 or msg.len() > 1500:", "def:request_of.byteview_bounds"},
		// An attribute that says it is longer than what is left of the message.
		{"        if size > rest.len() - 4 or padded > rest.len() - 4:\n            return None\n", "        if size > rest.len() or padded > rest.len():\n            return None\n", "def:answer.byteview_bounds"},
		{"        if padded > rest.len() - 4:\n            return None\n        if attr == 0x0003:", "        if attr == 0x0003:", "def:request_of.byteview_bounds"},
		// An ERROR-CODE or a CHANGE-REQUEST shorter than the bytes read of it.
		{"            if size < 4:\n                return None\n            number", "            if size < 3:\n                return None\n            number", "def:answer.byteview_bounds"},
		{"            if size != 4 or rest.len() < 8:", "            if size > 4:", "def:request_of.byteview_bounds"},
		// An error number, or the flags of a change, outside what the type holds.
		{"            if number > 99:\n                return None\n", "", "def:answer.let_code"},
		{"change = rest.read_u32_be(4) & 6", "change = rest.read_u32_be(4) & 7", "def:request_of.let_change"},
		// The address a datagram came from, read as four bytes without a look, and its port taken for one.
		{"if d.ip.len() == 4 and d.port > 0:\n                            match answer(", "if d.port > 0:\n                            match answer(", "def:ask.byteview_bounds"},
		{"if d.ip.len() == 4 and d.port > 0:\n                            match answer(", "if d.ip.len() == 4:\n                            match answer(", "def:ask.variant_At_range"},
		// A body too long for the length field of its message.
		{"    requires: body.len() <= 65535\n", "", "def:message.value_bounds"},
		// A socket left open: the client's, and one of the server's when the next cannot be bound.
		{"            found = run_workflow Discover(s, host, port, wait)\n            s.close()\n", "            found = run_workflow Discover(s, host, port, wait)\n", `sock.UdpSocket "s" opened`},
		{"                                    b.close()\n                                    a2.close()\n                                    return e", "                                    b.close()\n                                    return e", `sock.UdpSocket "a2" opened`},
	} {
		if strings.Count(src, c.old) != 1 {
			t.Fatalf("case %d: the example has %q %d times", i, c.old, strings.Count(src, c.old))
		}
		path := filepath.Join(tmp, fmt.Sprintf("stun_%d.anm", i))
		if err := os.WriteFile(path, []byte(strings.Replace(src, c.old, c.new, 1)), 0o644); err != nil {
			t.Fatal(err)
		}
		out, err := exec.Command(animaBin, "check", path).CombinedOutput()
		if err == nil || !strings.Contains(string(out), c.want) {
			t.Errorf("case %d: without %q the example is not refused with %s (err=%v):\n%s", i, c.old, c.want, err, lastLines(string(out), 12))
		}
	}
}

func lastLines(s string, n int) string {
	lines := strings.Split(strings.TrimRight(s, "\n"), "\n")
	if len(lines) > n {
		lines = lines[len(lines)-n:]
	}
	return strings.Join(lines, "\n")
}

// The client against a server that is this test: what it sends again, what
// it passes over, and what it makes of an answer the example's own server
// does not give. On both backends.
func TestE2EStunClientAgainstAScriptedServer(t *testing.T) {
	raw, err := os.ReadFile("../examples/stun.anm")
	if err != nil {
		t.Fatal(err)
	}
	vm, native := bothBackends(t, "stun", string(raw))

	type heard struct {
		msg  []byte
		from *net.UDPAddr
		nth  int // which request of the run this is, from 0
	}
	// answer gives the body of a Binding response with the address seen and, when other is not nil, OTHER-ADDRESS.
	answer := func(q heard, mapped stunAddr, other *stunAddr) []byte {
		body := stunAttr(0x0020, mapped, true)
		if other != nil {
			body = append(body, stunAttr(0x802c, *other, false)...)
		}
		return stunMessage(0x0101, q.msg[4:20], body)
	}
	seen := func(q heard) stunAddr {
		return stunAddr{binary.BigEndian.Uint32(q.from.IP.To4()), uint16(q.from.Port)}
	}
	for _, c := range []struct {
		name string
		// say gives the datagrams sent back for a request, in order.
		say  func(q heard, port uint16) [][]byte
		want []string
		code int
		// asked is how many requests the client is to have made, 0 for any number.
		asked int
	}{
		{
			name: "an answer to the third sending",
			say: func(q heard, port uint16) [][]byte {
				if q.nth < 2 {
					return nil
				}
				return [][]byte{answer(q, seen(q), nil)}
			},
			want:  []string{"mapping:        none", "filtering:      not told", "RFC 3489:       not told"},
			asked: 3,
		},
		{
			name: "what is no answer is passed over",
			say: func(q heard, port uint16) [][]byte {
				good := answer(q, seen(q), nil)
				other := append([]byte(nil), good...)
				other[19] ^= 1
				long := append(append([]byte(nil), good...), 0, 0, 0, 0)
				request := stunMessage(0x0001, q.msg[4:20], nil)
				indication := stunMessage(0x0011, q.msg[4:20], good[20:])
				return [][]byte{nil, {0}, []byte("not STUN at all, and longer than a header is"), good[:19], good[:len(good)-1], other, long, request, indication, good}
			},
			want:  []string{"mapping:        none", "filtering:      not told", "RFC 3489:       not told"},
			asked: 1,
		},
		{
			name: "another port of the same address is no other address",
			say: func(q heard, port uint16) [][]byte {
				return [][]byte{answer(q, seen(q), &stunAddr{0x7F000001, port + 1})}
			},
			want:  []string{"mapping:        none", "filtering:      not told", "RFC 3489:       not told"},
			asked: 1,
		},
		{
			name: "the same port of another address is no other address",
			say: func(q heard, port uint16) [][]byte {
				return [][]byte{answer(q, seen(q), &stunAddr{0x7F000002, port})}
			},
			want:  []string{"mapping:        none", "filtering:      not told", "RFC 3489:       not told"},
			asked: 1,
		},
		{
			name: "this host's address at another port is a mapping",
			say: func(q heard, port uint16) [][]byte {
				m := seen(q)
				m.port ^= 1
				return [][]byte{answer(q, m, nil)}
			},
			want:  []string{"mapping:        not told", "filtering:      not told", "RFC 3489:       not told"},
			asked: 1,
		},
		{
			name: "an error",
			say: func(q heard, port uint16) [][]byte {
				return [][]byte{stunMessage(0x0111, q.msg[4:20], []byte{0, 9, 0, 4, 0, 0, 5, 0})}
			},
			want:  []string{"the server answered with error 500"},
			code:  1,
			asked: 1,
		},
		{
			name:  "no answer",
			say:   func(q heard, port uint16) [][]byte { return nil },
			want:  []string{"no answer: UDP is blocked, or no server is there"},
			code:  1,
			asked: 3,
		},
	} {
		for name, argv := range map[string][]string{"vm": vm, "native": native} {
			t.Run(c.name+"/"+name, func(t *testing.T) {
				srv, err := net.ListenUDP("udp4", &net.UDPAddr{IP: net.IPv4(127, 0, 0, 1)})
				if err != nil {
					t.Fatal(err)
				}
				port := uint16(srv.LocalAddr().(*net.UDPAddr).Port)
				var requests [][]byte
				done := make(chan struct{})
				go func() {
					defer close(done)
					buf := make([]byte, 2048)
					for {
						n, from, err := srv.ReadFromUDP(buf)
						if err != nil {
							return
						}
						q := heard{append([]byte(nil), buf[:n]...), from, len(requests)}
						requests = append(requests, q.msg)
						if n < 20 {
							continue
						}
						for _, d := range c.say(q, port) {
							srv.WriteToUDP(d, from)
						}
					}
				}()
				begun := time.Now()
				out, err := exec.Command(argv[0], append(argv[1:], "client", "127.0.0.1", strconv.Itoa(int(port)))...).CombinedOutput()
				took := time.Since(begun)
				srv.Close()
				<-done
				code := 0
				if e, ok := err.(*exec.ExitError); ok {
					code = e.ExitCode()
				} else if err != nil {
					t.Fatal(err)
				}
				lines := strings.Split(strings.TrimSpace(string(out)), "\n")
				if len(c.want) == 3 {
					if len(lines) != 4 || !strings.HasPrefix(lines[0], "mapped address: 127.0.0.1:") {
						t.Fatalf("the client says\n%s", out)
					}
					lines = lines[1:]
				}
				if code != c.code || strings.Join(lines, "\n") != strings.Join(c.want, "\n") {
					t.Fatalf("the client exits %d and says\n%s", code, out)
				}
				if len(requests) != c.asked {
					t.Fatalf("the client asked %d times, not %d", len(requests), c.asked)
				}
				// What is sent again is the same request, and each wait is twice the one before: 500 ms, 1 s, 2 s.
				for _, q := range requests {
					if len(q) != 20 || !bytes.Equal(q, requests[0]) || !bytes.Equal(q[:8], []byte{0, 1, 0, 0, 0x21, 0x12, 0xA4, 0x42}) {
						t.Fatalf("the client asked %x and then %x", requests[0], q)
					}
				}
				least := map[int]time.Duration{1: 0, 3: 1500 * time.Millisecond}[c.asked]
				if c.name == "no answer" {
					least = 3500 * time.Millisecond
				}
				if took < least {
					t.Fatalf("the client took %v, less than the %v it waits", took, least)
				}
			})
		}
	}
}
