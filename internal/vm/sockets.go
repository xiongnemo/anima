package vm

import (
	"context"
	"fmt"
	"net"
	"net/netip"
	"strconv"
	"strings"
	"time"

	"github.com/xiongnemo/anima/internal/sema"
)

// A socket is Go's, and fails in Go's words: the native runtime follows
// both (std.socket in runtime_c.go). What Go would decide by itself in a
// way the system's sockets do not is decided here instead, the same for
// both: the family of an address is the one it is written in, and a name
// is bound at the first IPv4 address it has.

const (
	sockDialTime = 5 * time.Second
	sockIOTime   = 5 * time.Second
)

// sockHostRefused is why a host is none to a socket, or "": an empty one,
// an IPv6 address with a zone, a name outside ASCII.
func sockHostRefused(op, host string) string {
	if host == "" {
		return op + ": missing host"
	}
	why := hostRefused(host)
	if why == "" {
		return ""
	}
	return op + ": address " + host + ": " + why
}

func sockBadPort(op string, port int64) string {
	return fmt.Sprintf("%s: address %d: invalid port", op, port)
}

func sockNoHost(op, host string) string {
	return op + ": lookup " + host + ": no such host"
}

// sockLocal is the one address a host is bound at: its own, or of those its
// name is looked up to be the first IPv4 one, or the first if it has none.
func sockLocal(op, host string, port int64) (netip.AddrPort, string) {
	if port < 0 || port > 65535 {
		return netip.AddrPort{}, sockBadPort(op, port)
	}
	if why := sockHostRefused(op, host); why != "" {
		return netip.AddrPort{}, why
	}
	if a, err := netip.ParseAddr(host); err == nil {
		return netip.AddrPortFrom(a.Unmap(), uint16(port)), ""
	}
	// Why a name was not found is the resolver's own business: the native
	// runtime is told no more than that it was not. One that is not found
	// in the time a dial has is one no host has.
	ctx, cancel := context.WithTimeout(context.Background(), sockDialTime)
	defer cancel()
	found, err := net.DefaultResolver.LookupNetIP(ctx, "ip", host)
	if err != nil || len(found) == 0 {
		return netip.AddrPort{}, sockNoHost(op, host)
	}
	at := found[0].Unmap()
	for _, a := range found {
		if a = a.Unmap(); a.Is4() {
			at = a
			break
		}
	}
	return netip.AddrPortFrom(at.WithZone(""), uint16(port)), ""
}

func sockListenTCP(host string, port int64) Value {
	at, why := sockLocal("listen tcp", host, port)
	if why != "" {
		return VErr(why)
	}
	// An IPv6 address is listened at for IPv6 alone: :: is not 0.0.0.0 too.
	network := "tcp4"
	if at.Addr().Is6() {
		network = "tcp6"
	}
	ln, err := net.ListenTCP(network, net.TCPAddrFromAddrPort(at))
	if err != nil {
		return VErr(err.Error())
	}
	return VOk(Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleListener, Listener: ln}})
}

func sockConnectTCP(host string, port int64) Value {
	const op = "dial tcp"
	if port < 0 || port > 65535 {
		return VErr(sockBadPort(op, port))
	}
	if why := sockHostRefused(op, host); why != "" {
		return VErr(why)
	}
	// Go would take [ ] and a colon for the marks of a host:port.
	if _, err := netip.ParseAddr(host); err != nil && strings.ContainsAny(host, ":[]") {
		return VErr(sockNoHost(op, host))
	}
	joined := net.JoinHostPort(host, strconv.FormatInt(port, 10))
	end := time.Now().Add(sockDialTime)
	ctx, cancel := context.WithDeadline(context.Background(), end)
	defer cancel()
	conn, err := (&net.Dialer{}).DialContext(ctx, "tcp", joined)
	if err != nil {
		// The time ran out, on whichever address: the host is named as
		// it was written.
		if ctx.Err() != nil || !time.Now().Before(end) {
			return VErr(op + " " + joined + ": i/o timeout")
		}
		if _, ok := asDNSError(err); ok {
			return VErr(sockNoHost(op, host))
		}
		return VErr(err.Error())
	}
	return VOk(Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleStream, Conn: conn}})
}

func asDNSError(err error) (*net.DNSError, bool) {
	for err != nil {
		if de, ok := err.(*net.DNSError); ok {
			return de, true
		}
		u, ok := err.(interface{ Unwrap() error })
		if !ok {
			return nil, false
		}
		err = u.Unwrap()
	}
	return nil, false
}

func sockAccept(h *HandleValue, timeoutMs int) Value {
	if tl, ok := h.Listener.(*net.TCPListener); ok {
		_ = tl.SetDeadline(time.Now().Add(time.Duration(timeoutMs) * time.Millisecond))
	}
	conn, err := h.Listener.Accept()
	if err != nil {
		return VErr(err.Error())
	}
	return VOk(Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleStream, Conn: conn}})
}

// sockSend sends the whole text, or it is an Err.
func sockSend(h *HandleValue, text string) Value {
	if h.Closed {
		return VErr("socket closed")
	}
	_ = h.Conn.SetWriteDeadline(time.Now().Add(sockIOTime))
	n, err := h.Conn.Write([]byte(text))
	if err != nil {
		return VErr(err.Error())
	}
	return VOk(VInt(int64(n)))
}

func sockRecv(h *HandleValue, maxBytes int64) Value {
	if h.Closed {
		return VErr("socket closed")
	}
	maxBytes = min(max(maxBytes, 1), sema.MaxRecvText)
	_ = h.Conn.SetReadDeadline(time.Now().Add(sockIOTime))
	buf := make([]byte, maxBytes)
	n, err := h.Conn.Read(buf)
	if err != nil && n == 0 {
		return VErr(err.Error())
	}
	return textRead(buf[:n])
}
