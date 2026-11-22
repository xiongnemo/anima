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
	return sockAt(op, host, port, 0)
}

// sockAt is the one address of a host: its own, or of those its name is
// looked up to be the first of the family (4 or 6), which is then the only
// one taken. With no family it is the first IPv4 one, or the first.
func sockAt(op, host string, port int64, family int) (netip.AddrPort, string) {
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
	at, of := found[0].Unmap(), family == 0
	for _, a := range found {
		if a = a.Unmap(); a.Is4() == (family != 6) {
			at, of = a, true
			break
		}
	}
	if !of {
		return netip.AddrPort{}, sockNoHost(op, host)
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

// A UDP socket is of the family of the address it is bound at, and sends
// to and hears from that family alone.

func sockBindUDP(host string, port int64) Value {
	at, why := sockLocal("listen udp", host, port)
	if why != "" {
		return VErr(why)
	}
	network := "udp4"
	if at.Addr().Is6() {
		network = "udp6"
	}
	// Go would bind the address of a group at every address, and join it.
	if at.Addr().IsMulticast() {
		return VErr("listen " + network + " " + at.String() + ": multicast address")
	}
	conn, err := net.ListenUDP(network, net.UDPAddrFromAddrPort(at))
	if err != nil {
		return VErr(err.Error())
	}
	return VOk(Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleUDP, UDP: conn}})
}

// udpWhere is "udp4 127.0.0.1:80", and whether the socket is an IPv6 one.
func udpWhere(h *HandleValue) (string, bool) {
	local := h.UDP.LocalAddr().(*net.UDPAddr).AddrPort()
	if local.Addr().Unmap().Is4() {
		return "udp4 " + netip.AddrPortFrom(local.Addr().Unmap(), local.Port()).String(), false
	}
	return "udp6 " + local.String(), true
}

// sockSendTo sends the bytes as one datagram, or it is an Err.
func sockSendTo(h *HandleValue, data Value, host string, port int64) Value {
	const op = "write udp"
	if h.Closed {
		return VErr("socket closed")
	}
	if port < 1 || port > 65535 {
		return VErr(sockBadPort(op, port))
	}
	where, v6 := udpWhere(h)
	family, other := 4, "non-IPv4 address"
	if v6 {
		family, other = 6, "non-IPv6 address"
	}
	if a, err := netip.ParseAddr(host); err == nil && !strings.Contains(host, "%") && a.Unmap().Is4() == v6 {
		return VErr("write " + where + ": address " + host + ": " + other)
	}
	to, why := sockAt(op, host, port, family)
	if why != "" {
		return VErr(why)
	}
	var b []byte
	if d := data.Handle; data.Kind == ValHandle && d != nil && d.Kind == HandleByteView {
		b = d.Bytes
	}
	_ = h.UDP.SetWriteDeadline(time.Now().Add(sockIOTime))
	n, err := h.UDP.WriteToUDPAddrPort(b, to)
	if err != nil {
		return VErr(err.Error())
	}
	return VOk(VInt(int64(n)))
}

// sockRecvFrom waits for one datagram: what of it is past maxBytes is lost.
func sockRecvFrom(h *HandleValue, maxBytes int64, timeoutMs int) Value {
	if h.Closed {
		return VErr("socket closed")
	}
	buf := make([]byte, sema.Within(maxBytes, 1, sema.MaxDatagram))
	_ = h.UDP.SetReadDeadline(time.Now().Add(time.Duration(timeoutMs) * time.Millisecond))
	n, from, err := h.UDP.ReadFromUDPAddrPort(buf)
	if err != nil {
		return VErr(err.Error())
	}
	// Where it came from is an address and no more: the zone of an IPv6
	// one is not said, as no socket is given a host with one.
	_, v6 := udpWhere(h)
	addr := from.Addr().WithZone("")
	if !v6 {
		addr = addr.Unmap()
	}
	return VOk(Value{Kind: ValEntity, Entity: &EntityInstance{
		TypeName: "Datagram",
		Fields: map[string]Value{
			"data": viewOf(append([]byte(nil), buf[:n]...)),
			"host": VStr(addr.Unmap().String()),
			"port": VInt(int64(from.Port())),
			"ip":   viewOf(addr.AsSlice()),
		},
	}})
}
