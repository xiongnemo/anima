package tests

import (
	"bytes"
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"net"
	"os/exec"
	"strings"
	"sync"
	"testing"
	"time"
)

// What a view is built of is in it, byte for byte, on both backends, and the
// kernel knows how long each is: every read below is proved inside its view.
// Two views of the same bytes are equal, whatever made them.
func TestE2EByteBuildingParity(t *testing.T) {
	runOnBothBackends(t, "byte_building", `import std.bytes as bytes

entity Header:
    kind: int[0..65535]
    size: int[0..65535]

def header(h: Header, id: bytes.ByteView) -> bytes.ByteView:
    return bytes.u16_be(h.kind).concat(bytes.u16_be(h.size)).concat(bytes.u32_be(0x2112A442)).concat(id)

def kind_of(pkt: bytes.ByteView) -> int:
    if pkt.len() < 20:
        return 0 - 1
    return pkt.read_u16_be(0)

def padded(n: int[0..3]) -> int:
    v = bytes.u8(n).concat(bytes.random(3 - n)).concat(bytes.u32_be(7))
    return v.read_u32_be(4 - n) + v.len()

def main() -> int:
    id = bytes.from_hex("000102030405060708090a0b")
    pkt = header(Header(kind=1, size=0), id)
    print(pkt.len(), pkt.to_hex())
    # The length of a view that a function returns is not known where it is called.
    if pkt.len() == 20:
        print(kind_of(pkt), kind_of(id), pkt.slice(8, 20) == id, pkt.slice(4, 8).read_u32_be(0))
    a = bytes.u8(1).concat(bytes.u8(2))
    b = bytes.from_hex("0102")
    c = bytes.from_hex("01027f").slice(0, 2)
    e = bytes.from_hex("")
    print(a == b, a == c, a != b, a == e, e == bytes.from_str(""), e == bytes.random(0), e == e.concat(e))
    print(a in [e, c], a in [e], [a, e] == [b, e], Some(a) == Some(b))
    print(bytes.u8(0).to_hex(), bytes.u8(255).to_hex(), bytes.u16_be(0).to_hex(), bytes.u16_be(65535).to_hex())
    print(bytes.u32_be(0).to_hex(), bytes.u32_be(4294967295).to_hex(), bytes.u32_be(2147483648).read_u32_be(0))
    print(bytes.from_hex("FFab00").to_hex(), bytes.from_str("héllo").to_hex(), "[" + e.to_hex() + "]")
    r = bytes.random(65536)
    twice = r.concat(r)
    print(r.len(), twice.len(), twice.slice(65536, 131072) == r, r.slice(0, 32) == bytes.random(32))
    print(padded(0), padded(3))
    return 0
`, `20 000100002112a442000102030405060708090a0b
1 -1 True 554869826
True True False False True True True
True False True True
00 ff 0000 ffff
00000000 ffffffff 2147483648
ffab00 68c3a96c6c6f []
65536 131072 True False
15 12
`)
}

// A UDP socket is of the host it is asked for, on both backends, and what
// it does not do is the same Err in the same words: a host that is none, an
// address of a group, a port that is taken, an address of the other family,
// a datagram too long to send, a wait that runs out.
func TestE2EUDPSocketParity(t *testing.T) {
	sameOnBothBackends(t, "udp_sockets", `import std.socket as sock
import std.bytes as bytes

def show(r: Result[sock.Datagram, str], port: int) -> int:
    match r:
        Ok(d) -> print(d.data.len(), d.data.to_hex(), d.host, d.port == port, d.ip.to_hex())
        Err(e) -> print(e)
    return 0

def said(r: Result[int, str]) -> str:
    return match r:
        Ok(n) -> str(n)
        Err(e) -> e

def bound(host: str) -> int:
    match sock.bind_udp(host, 0):
        Ok(s) ->
            print(host, "is bound")
            match sock.bind_udp(host, s.port()):
                Ok(t) ->
                    print("and bound again")
                    t.close()
                Err(e) -> print(e)
            for to in ["127.0.0.1", "::1", "::ffff:127.0.0.1", "nosuch.invalid", "", "::1%lo", "127.1"]:
                print("  to [" + to + "]:", said(s.send_to(bytes.from_hex("0102"), to, 9)))
            s.close()
        Err(e) -> print(e)
    return 0

def talk(a: sock.UdpSocket, b: sock.UdpSocket, host: str) -> int:
    pa = a.port()
    pb = b.port()
    for pkt in [bytes.from_hex(""), bytes.from_hex("00"), bytes.from_str("hello world"), bytes.from_hex("ff00fe01")]:
        print(said(a.send_to(pkt, host, pb)))
        r = show(b.recv_from(8, timeout_ms=2000), pa)
    big = bytes.random(65507)
    print(said(a.send_to(big, host, pb)))
    match b.recv_from(65535, timeout_ms=2000):
        Ok(d) -> print(d.data == big)
        Err(e) -> print(e)
    print(said(a.send_to(big.concat(big), host, pb)))
    r = show(b.recv_from(8, timeout_ms=1), pa)
    # Two that wait are read in the order they came.
    print(said(a.send_to(bytes.u8(1), host, pb)), said(a.send_to(bytes.u8(2), host, pb)))
    r = show(b.recv_from(8, 2000), pa)
    r = show(b.recv_from(8, 2000), pa)
    # A socket hears itself.
    print(said(b.send_to(bytes.u16_be(515), host, pb)))
    r = show(b.recv_from(8, 2000), pb)
    return 0

def pair(host: str) -> int:
    match sock.bind_udp(host, 0):
        Ok(a) ->
            match sock.bind_udp(host, 0):
                Ok(b) ->
                    r = talk(a, b, host)
                    b.close()
                Err(e) -> print(e)
            a.close()
        Err(e) -> print(e)
    return 0

def main() -> int:
    for h in ["127.0.0.1", "::1", "0.0.0.0", "::", "::ffff:127.0.0.1", "", "224.0.0.1", "ff02::1", "nosuch.invalid", "192.0.2.1", "::1%lo", "127.0.0.1:80", "[::1]"]:
        r = bound(h)
    r = pair("127.0.0.1")
    r = pair("::1")
    return 0
`, `127.0.0.1 is bound
listen udp4 127.0.0.1:P: bind: address already in use
  to [127.0.0.1]: 2
  to [::1]: write udp4 127.0.0.1:P: address ::1: non-IPv4 address
  to [::ffff:127.0.0.1]: 2
  to [nosuch.invalid]: write udp: lookup nosuch.invalid: no such host
  to []: write udp: missing host
  to [::1%lo]: write udp: address ::1%lo: invalid host
  to [127.1]: write udp: lookup 127.1: no such host
::1 is bound
listen udp6 [::1]:P: bind: address already in use
  to [127.0.0.1]: write udp6 [::1]:P: address 127.0.0.1: non-IPv6 address
  to [::1]: 2
  to [::ffff:127.0.0.1]: write udp6 [::1]:P: address ::ffff:127.0.0.1: non-IPv6 address
  to [nosuch.invalid]: write udp: lookup nosuch.invalid: no such host
  to []: write udp: missing host
  to [::1%lo]: write udp: address ::1%lo: invalid host
  to [127.1]: write udp: lookup 127.1: no such host
0.0.0.0 is bound
listen udp4 0.0.0.0:P: bind: address already in use
  to [127.0.0.1]: 2
  to [::1]: write udp4 0.0.0.0:P: address ::1: non-IPv4 address
  to [::ffff:127.0.0.1]: 2
  to [nosuch.invalid]: write udp: lookup nosuch.invalid: no such host
  to []: write udp: missing host
  to [::1%lo]: write udp: address ::1%lo: invalid host
  to [127.1]: write udp: lookup 127.1: no such host
:: is bound
listen udp6 [::]:P: bind: address already in use
  to [127.0.0.1]: write udp6 [::]:P: address 127.0.0.1: non-IPv6 address
  to [::1]: 2
  to [::ffff:127.0.0.1]: write udp6 [::]:P: address ::ffff:127.0.0.1: non-IPv6 address
  to [nosuch.invalid]: write udp: lookup nosuch.invalid: no such host
  to []: write udp: missing host
  to [::1%lo]: write udp: address ::1%lo: invalid host
  to [127.1]: write udp: lookup 127.1: no such host
::ffff:127.0.0.1 is bound
listen udp4 127.0.0.1:P: bind: address already in use
  to [127.0.0.1]: 2
  to [::1]: write udp4 127.0.0.1:P: address ::1: non-IPv4 address
  to [::ffff:127.0.0.1]: 2
  to [nosuch.invalid]: write udp: lookup nosuch.invalid: no such host
  to []: write udp: missing host
  to [::1%lo]: write udp: address ::1%lo: invalid host
  to [127.1]: write udp: lookup 127.1: no such host
listen udp: missing host
listen udp4 224.0.0.1:0: multicast address
listen udp6 [ff02::1]:0: multicast address
listen udp: lookup nosuch.invalid: no such host
listen udp4 192.0.2.1:0: bind: cannot assign requested address
listen udp: address ::1%lo: invalid host
listen udp: lookup 127.0.0.1:80: no such host
listen udp: lookup [::1]: no such host
`+udpTalk("127.0.0.1", "7f000001", "udp4 127.0.0.1:P", "write udp4 127.0.0.1:P->127.0.0.1:P: sendto: message too long")+
		udpTalk("::1", "00000000000000000000000000000001", "udp6 [::1]:P", "write udp6 [::1]:P->[::1]:P: sendto: message too long"))
}

func udpTalk(host, ip, where, tooLong string) string {
	from := " " + host + " True " + ip + "\n"
	return "0\n0 " + from +
		"1\n1 00" + from +
		"11\n8 68656c6c6f20776f" + from +
		"4\n4 ff00fe01" + from +
		"65507\nTrue\n" +
		tooLong + "\n" +
		"read " + where + ": i/o timeout\n" +
		"1 1\n1 01" + from + "1 02" + from +
		"2\n2 0203" + from
}

const udpEchoSrc = `import std.socket as sock
import std.bytes as bytes
import std.cli as cli

# Every datagram is sent back to where it came from, with the 4 or 16 bytes
# of that address before it, until one of a single byte 0xff comes.
def serve(s: sock.UdpSocket) -> int:
    n = 0
    while n < 100000:
        match s.recv_from(2048, timeout_ms=10000):
            Ok(d) ->
                if d.port == 0:
                    return n
                if d.data == bytes.u8(255):
                    return n
                match s.send_to(d.ip.concat(d.data), d.host, d.port):
                    Ok(sent) -> n = n + 1
                    Err(e) -> print(e)
            Err(e) ->
                print(e)
                return n
    return n

def main() -> int:
    match sock.bind_udp(HOST, 0):
        Ok(s) ->
            print("port", s.port())
            print("echoed", serve(s))
            s.close()
        Err(e) -> print(e)
    return 0
`

// A program on each backend echoes what a Go peer sends it: datagrams of
// every byte value and of 0 to 3000 bytes, read 2048 bytes at most, from
// more than one address. What comes back is what was sent, cut at 2048,
// after the address the program saw it come from.
func TestE2EUDPEchoWithAPeer(t *testing.T) {
	for _, host := range []string{"127.0.0.1", "::1"} {
		vmCmd, natCmd := bothBackends(t, "udp_echo", strings.ReplaceAll(udpEchoSrc, "HOST", fmt.Sprintf("%q", host)))
		for i, argv := range [][]string{vmCmd, natCmd} {
			t.Run(host+"/"+[]string{"VM", "native"}[i], func(t *testing.T) { udpEcho(t, argv, host) })
		}
	}
}

func udpEcho(t *testing.T, argv []string, host string) {
	cmd := exec.Command(argv[0], argv[1:]...)
	out := &lockedBuf{}
	cmd.Stdout, cmd.Stderr = out, out
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	done := make(chan error, 1)
	go func() { done <- cmd.Wait(); close(done) }()
	defer func() {
		_ = cmd.Process.Kill()
		for range done {
		}
	}()
	var port int
	for deadline := time.Now().Add(20 * time.Second); ; time.Sleep(20 * time.Millisecond) {
		if _, err := fmt.Sscanf(out.String(), "port %d\n", &port); err == nil {
			break
		}
		if time.Now().After(deadline) {
			t.Fatalf("no port was printed:\n%s", out.String())
		}
	}
	to := &net.UDPAddr{IP: net.ParseIP(host), Port: port}
	sources := []string{host}
	if host == "127.0.0.1" {
		sources = append(sources, "127.0.0.2", "127.9.8.7")
	}
	sent := 0
	for _, src := range sources {
		peer, err := net.ListenUDP("udp", &net.UDPAddr{IP: net.ParseIP(src)})
		if err != nil {
			t.Fatal(err)
		}
		defer peer.Close()
		ip := net.ParseIP(src)
		if v4 := ip.To4(); v4 != nil {
			ip = v4
		}
		all := make([]byte, 256)
		for i := range all {
			all[i] = byte(i)
		}
		payloads := [][]byte{{}, {0}, {0, 0, 0}, all, bytes.Repeat([]byte{0xff}, 2), []byte("text\x00with a NUL")}
		for _, n := range []int{1, 2, 19, 20, 21, 548, 1472, 2047, 2048, 2049, 3000} {
			p := make([]byte, n)
			_, _ = rand.Read(p)
			if n == 1 && p[0] == 0xff {
				p[0] = 0
			}
			payloads = append(payloads, p)
		}
		for _, p := range payloads {
			if _, err := peer.WriteToUDP(p, to); err != nil {
				t.Fatal(err)
			}
			sent++
			want := append(append([]byte(nil), ip...), p[:min(len(p), 2048)]...)
			got := make([]byte, 4096)
			_ = peer.SetReadDeadline(time.Now().Add(5 * time.Second))
			n, from, err := peer.ReadFromUDP(got)
			if err != nil {
				t.Fatalf("from %s, %d bytes: %v\n%s", src, len(p), err, out.String())
			}
			if from.Port != port || !bytes.Equal(got[:n], want) {
				t.Fatalf("from %s, %d bytes sent: got %d bytes from port %d\n got %s\nwant %s", src, len(p), n, from.Port, hex.EncodeToString(got[:n]), hex.EncodeToString(want))
			}
		}
	}
	// One byte 0xff ends the program.
	last, err := net.DialUDP("udp", nil, to)
	if err != nil {
		t.Fatal(err)
	}
	defer last.Close()
	if _, err := last.Write([]byte{0xff}); err != nil {
		t.Fatal(err)
	}
	select {
	case err := <-done:
		want := fmt.Sprintf("port %d\nechoed %d\n", port, sent)
		if err != nil || out.String() != want {
			t.Fatalf("err=%v, output:\n%s\nwant:\n%s", err, out.String(), want)
		}
	case <-time.After(15 * time.Second):
		t.Fatalf("the program did not end:\n%s", out.String())
	}
}

type lockedBuf struct {
	mu sync.Mutex
	b  bytes.Buffer
}

func (l *lockedBuf) Write(p []byte) (int, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	return l.b.Write(p)
}

func (l *lockedBuf) String() string {
	l.mu.Lock()
	defer l.mu.Unlock()
	return l.b.String()
}
