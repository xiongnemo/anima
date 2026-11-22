package vm

import (
	"net"
	"strings"
	"testing"
	"time"

	"github.com/xiongnemo/anima/internal/sema"
)

// The kernel proves a port is one and a count of bytes is one that can be
// held. The runtime does not rely on it: what is neither is an Err, or is
// taken for the most there is.
func TestSocketArgumentsOutOfRange(t *testing.T) {
	for _, port := range []int64{-1, 65536, 70000, 1 << 40, -1 << 62} {
		for _, r := range []Value{sockListenTCP("127.0.0.1", port), sockConnectTCP("127.0.0.1", port)} {
			if r.Kind != ValVariant || r.Variant.Name != "Err" || !strings.HasSuffix(r.Variant.Fields[0].Str, ": invalid port") {
				t.Errorf("port %d: %s", port, r.String())
			}
		}
	}
	a, b := net.Pipe()
	defer a.Close()
	go func() {
		_, _ = b.Write([]byte("hello"))
		b.Close()
	}()
	h := &HandleValue{Kind: HandleStream, Conn: a}
	done := make(chan Value, 1)
	go func() { done <- sockRecv(h, 1<<46) }()
	select {
	case r := <-done:
		if r.Variant.Name != "Ok" || r.Variant.Fields[0].Str != "hello" {
			t.Errorf("recv_text(1 << 46): %s", r.String())
		}
	case <-time.After(10 * time.Second):
		t.Fatal("recv_text(1 << 46) does not end")
	}
	if sema.MaxRecvText != 1<<20 {
		t.Errorf("MaxRecvText is %d", sema.MaxRecvText)
	}
}
