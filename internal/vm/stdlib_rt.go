package vm

import (
	"bytes"
	"context"
	"crypto/hmac"
	"crypto/sha256"
	"crypto/subtle"
	"crypto/tls"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	neturl "net/url"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/xiongnemo/anima/internal/sema"
)

func (vm *VM) dispatchCall(cm CallMeta, args []Value) (Value, error) {
	// 1. Instance method call (receiver is args[0])
	if cm.IsMethod && len(args) >= 1 {
		return vm.dispatchMethod(cm, args[0], args[1:])
	}

	// 2. User-defined bytecode function
	if _, isUser := vm.prog.Module.FuncIndex[cm.CalleeName]; isUser {
		rv, _, _, err := vm.callFuncByName(cm.CalleeName, args, nil)
		return rv, err
	}

	// 3. Port call (`port:AuditLog.write_entry`)
	if strings.HasPrefix(cm.CalleeName, "port:") {
		vm.monMu.Lock()
		vm.portLogs = append(vm.portLogs, fmt.Sprintf("%s(%v)", strings.TrimPrefix(cm.CalleeName, "port:"), args))
		vm.monMu.Unlock()
		return VVoid(), nil
	}

	// 4. Built-ins & std.* modules
	switch cm.CalleeName {
	case "len":
		if len(args) == 0 {
			return VInt(0), nil
		}
		switch args[0].Kind {
		case ValList:
			if args[0].List == nil {
				return VInt(0), nil
			}
			return VInt(int64(len(*args[0].List))), nil
		case ValMap:
			return VInt(int64(len(args[0].Map))), nil
		case ValStr:
			return VInt(int64(len(args[0].Str))), nil
		case ValHandle:
			if args[0].Handle != nil && args[0].Handle.Kind == HandleByteView {
				return VInt(int64(len(args[0].Handle.Bytes))), nil
			}
		}
		return VInt(0), nil

	case "print":
		var parts []string
		for _, a := range args {
			parts = append(parts, a.String())
		}
		vm.printf("%s\n", strings.Join(parts, " "))
		return VVoid(), nil

	case "str", "to_str":
		if len(args) == 0 {
			return VStr(""), nil
		}
		return VStr(args[0].String()), nil

	case "abs":
		x := args[0].Int
		if x < 0 {
			x = -x
		}
		return VInt(x), nil

	case "min":
		if args[0].Int < args[1].Int {
			return args[0], nil
		}
		return args[1], nil

	case "max":
		if args[0].Int > args[1].Int {
			return args[0], nil
		}
		return args[1], nil

	case "assert":
		if len(args) >= 1 && !args[0].IsTruthy() {
			msg := "assertion failed"
			if len(args) >= 2 {
				msg = args[1].String()
			}
			return VVoid(), fmt.Errorf("%s", msg)
		}
		return VVoid(), nil

	case "Some":
		return VSome(args[0]), nil
	case "Ok":
		return VOk(args[0]), nil
	case "Err":
		return VErr(args[0].String()), nil

	// ─── std.fp & Pipeline Combinators ───
	case "filter", "std.fp.filter":
		return vm.fpFilter(args)
	case "map", "std.fp.map":
		return vm.fpMap(args)
	case "flat_map", "std.fp.flat_map":
		return vm.fpFlatMap(args)
	case "fold", "std.fp.fold":
		return vm.fpFold(args)
	case "sum", "std.fp.sum":
		var s int64
		if args[0].List != nil {
			for _, el := range *args[0].List {
				s += el.Int
			}
		}
		return VInt(s), nil
	case "take", "std.fp.take":
		n := int(args[1].Int)
		if args[0].List == nil || n <= 0 {
			return VList(nil), nil
		}
		xs := *args[0].List
		if n > len(xs) {
			n = len(xs)
		}
		return VList(xs[:n]), nil
	case "drop", "std.fp.drop":
		n := int(args[1].Int)
		if args[0].List == nil {
			return VList(nil), nil
		}
		xs := *args[0].List
		if n < 0 {
			n = 0
		}
		if n >= len(xs) {
			return VList(nil), nil
		}
		return VList(xs[n:]), nil
	case "zip", "std.fp.zip":
		var out []Value
		if args[0].List != nil && args[1].List != nil {
			a, b := *args[0].List, *args[1].List
			for i := 0; i < len(a) && i < len(b); i++ {
				out = append(out, VList([]Value{a[i], b[i]}))
			}
		}
		return VList(out), nil
	case "any", "std.fp.any":
		if args[0].List != nil && args[1].Closure != nil {
			for _, el := range *args[0].List {
				r, err := vm.callClosure(args[1].Closure, []Value{el})
				if err != nil {
					return VVoid(), err
				}
				if r.IsTruthy() {
					return VBool(true), nil
				}
			}
		}
		return VBool(false), nil
	case "all", "std.fp.all":
		if args[0].List != nil && args[1].Closure != nil {
			for _, el := range *args[0].List {
				r, err := vm.callClosure(args[1].Closure, []Value{el})
				if err != nil {
					return VVoid(), err
				}
				if !r.IsTruthy() {
					return VBool(false), nil
				}
			}
		}
		return VBool(true), nil
	case "find", "std.fp.find":
		if args[0].List != nil && args[1].Closure != nil {
			for _, el := range *args[0].List {
				r, err := vm.callClosure(args[1].Closure, []Value{el})
				if err != nil {
					return VVoid(), err
				}
				if r.IsTruthy() {
					return VSome(el), nil
				}
			}
		}
		return VNone(), nil
	case "filter_ok", "std.fp.filter_ok":
		var out []Value
		if args[0].List != nil {
			for _, el := range *args[0].List {
				if el.Kind == ValVariant && el.Variant != nil && (el.Variant.Name == "Ok" || el.Variant.Name == "Some") && len(el.Variant.Fields) > 0 {
					out = append(out, el.Variant.Fields[0])
				}
			}
		}
		return VList(out), nil
	case "unwrap_or", "std.fp.unwrap_or":
		if args[0].Kind == ValVariant && args[0].Variant != nil && (args[0].Variant.Name == "Ok" || args[0].Variant.Name == "Some") && len(args[0].Variant.Fields) > 0 {
			return args[0].Variant.Fields[0], nil
		}
		return args[1], nil
	case "and_then", "std.fp.and_then":
		if args[0].Kind == ValVariant && args[0].Variant != nil && (args[0].Variant.Name == "Ok" || args[0].Variant.Name == "Some") && len(args[0].Variant.Fields) > 0 && args[1].Closure != nil {
			return vm.callClosure(args[1].Closure, []Value{args[0].Variant.Fields[0]})
		}
		return args[0], nil

	// ─── std.socket ───
	case "std.socket.listen_tcp":
		return sockListenTCP(args[0].Str, args[1].Int), nil

	case "std.socket.connect_tcp":
		return sockConnectTCP(args[0].Str, args[1].Int), nil

	// ─── std.requests ───
	case "std.requests.get":
		url := args[0].Str
		ms := extractTimeoutMs(cm, args, 1, 5000)
		return vm.httpDo("GET", url, "", ms, nil), nil

	case "std.requests.post":
		url := args[0].Str
		body := ""
		if len(args) >= 2 {
			body = args[1].Str
		}
		ms := extractTimeoutMs(cm, args, 2, 5000)
		return vm.httpDo("POST", url, body, ms, nil), nil

	case "std.requests.Session":
		poolSize := 4
		if len(args) >= 1 {
			poolSize = int(sema.Within(args[0].Int, 1, sema.MaxWorkers))
		}
		tr := newTransport()
		tr.MaxIdleConnsPerHost, tr.MaxIdleConns = poolSize, poolSize*2
		cl := &http.Client{Transport: tr}
		return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleSession, HTTPClient: cl}}, nil

	case "std.requests.gather":
		var out []Value
		if len(args) >= 1 && args[0].List != nil {
			for _, f := range *args[0].List {
				if f.Kind == ValHandle && f.Handle != nil && f.Handle.Kind == HandleFuture {
					if !f.Handle.FutDone {
						f.Handle.FutVal = <-f.Handle.FutCh
						f.Handle.FutDone = true
					}
					out = append(out, f.Handle.FutVal)
				}
			}
		}
		return VList(out), nil

	// ─── std.concurrent ───
	case "std.concurrent.ThreadPool":
		// The kernel proves both in range; they are held to it again for
		// what it did not read.
		workers := int(sema.Within(args[0].Int, 1, sema.MaxWorkers))
		qcap := int(sema.Within(args[1].Int, 1, sema.MaxQueueCap))
		ch := make(chan func(), qcap)
		var wg sync.WaitGroup
		for i := 0; i < workers; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				for task := range ch {
					task()
				}
			}()
		}
		return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleThreadPool, PoolCh: ch, PoolWG: &wg}}, nil

	case "std.concurrent.Channel":
		capVal := 8
		if len(args) >= 1 {
			capVal = int(sema.Within(args[0].Int, 1, sema.MaxQueueCap))
		}
		return Value{Kind: ValHandle, Handle: &HandleValue{
			Kind:   HandleChannel,
			Chan:   make(chan Value, capVal),
			ChanMu: &sync.Mutex{},
		}}, nil

	case "std.concurrent.Mutex":
		var initVal Value
		if len(args) >= 1 {
			initVal = args[0]
		}
		return Value{Kind: ValHandle, Handle: &HandleValue{
			Kind:     HandleMutex,
			Mu:       &sync.Mutex{},
			MutexVal: &initVal,
		}}, nil

	case "std.concurrent.Semaphore":
		return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleSemaphore, Sem: newSemaphore(sema.Within(args[0].Int, 1, sema.MaxPermits))}}, nil

	case "std.concurrent.parallel_map":
		if len(args) >= 2 && args[0].List != nil && args[1].Closure != nil {
			// At most MaxWorkers calls at a time, begun in the order of
			// xs: what the native runtime has the threads for.
			xs := append([]Value(nil), *args[0].List...)
			out := make([]Value, len(xs))
			var wg sync.WaitGroup
			var firstErr error
			var errMu sync.Mutex
			slots := make(chan struct{}, sema.MaxWorkers)
			for i, item := range xs {
				slots <- struct{}{}
				wg.Add(1)
				go func(idx int, v Value) {
					defer wg.Done()
					defer func() { <-slots }()
					r, err := vm.callClosure(args[1].Closure, []Value{v})
					if err != nil {
						errMu.Lock()
						if firstErr == nil {
							firstErr = err
						}
						errMu.Unlock()
						return
					}
					out[idx] = r
				}(i, item)
			}
			wg.Wait()
			if firstErr != nil {
				return VVoid(), firstErr
			}
			return VList(out), nil
		}
		return VList(nil), nil

	// ─── std.json ───
	case "std.json.encode":
		b, err := json.Marshal(valueToGoJSON(args[0]))
		if err != nil {
			return VStr("{}"), nil
		}
		return VStr(string(b)), nil

	case "std.json.decode":
		raw := args[0].Str
		typeName := ""
		if len(cm.TypeArgs) > 0 {
			typeName = cm.TypeArgs[0]
		}
		return vm.jsonDecodeSchema(typeName, raw), nil

	// ─── std.bytes & std.crypto ───
	case "std.bytes.from_str":
		return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleByteView, Bytes: []byte(args[0].Str)}}, nil
	case "std.bytes.from_hex":
		b, err := hex.DecodeString(args[0].Str)
		if err != nil {
			b = nil
		}
		return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleByteView, Bytes: b}}, nil
	case "std.crypto.sha256":
		sum := sha256.Sum256([]byte(args[0].Str))
		return VStr(hex.EncodeToString(sum[:])), nil
	case "std.crypto.hmac_sha256":
		mac := hmac.New(sha256.New, []byte(args[0].Str))
		mac.Write([]byte(args[1].Str))
		return VStr(hex.EncodeToString(mac.Sum(nil))), nil
	case "std.crypto.constant_time_eq":
		eq := subtle.ConstantTimeCompare([]byte(args[0].Str), []byte(args[1].Str)) == 1
		return VBool(eq), nil

	// ─── std.fs & std.cli & std.time ───
	case "std.fs.open":
		path := args[0].Str
		mode := "r"
		if len(args) >= 2 {
			mode = args[1].Str
		}
		var f *os.File
		var err error
		if strings.Contains(mode, "w") {
			f, err = os.Create(path)
		} else {
			f, err = os.Open(path)
		}
		if err != nil {
			return VErr(err.Error()), nil
		}
		return VOk(Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleFile, File: f, FilePath: path}}), nil

	case "std.fs.read_text":
		b, err := os.ReadFile(args[0].Str)
		if err != nil {
			return VErr(err.Error()), nil
		}
		return textRead(b), nil

	case "std.fs.write_atomic":
		path := args[0].Str
		content := args[1].Str
		dir := filepath.Dir(path)
		tmp, err := os.CreateTemp(dir, ".anima-tmp-*")
		if err != nil {
			return VErr(err.Error()), nil
		}
		tmpName := tmp.Name()
		_, werr := tmp.WriteString(content)
		cerr := tmp.Close()
		if werr != nil || cerr != nil {
			_ = os.Remove(tmpName)
			return VErr("write failed"), nil
		}
		if err := os.Rename(tmpName, path); err != nil {
			_ = os.Remove(tmpName)
			return VErr(err.Error()), nil
		}
		return VOk(VInt(int64(len(content)))), nil

	case "std.cli.args":
		out := make([]Value, len(vm.opts.Args))
		for i, a := range vm.opts.Args {
			out[i] = VStr(a)
		}
		return VList(out), nil

	case "std.cli.env_get":
		v, ok := os.LookupEnv(args[0].Str)
		if !ok {
			return VNone(), nil
		}
		return VSome(VStr(v)), nil

	case "std.time.now_ms":
		return VInt(time.Now().UnixMilli()), nil

	case "std.time.sleep_ms":
		if ms := sema.Within(args[0].Int, 0, sema.MaxSleepMs); ms > 0 {
			time.Sleep(time.Duration(ms) * time.Millisecond)
		}
		return VVoid(), nil
	}

	return VVoid(), fmt.Errorf("unknown runtime call %q", cm.CalleeName)
}

func (vm *VM) dispatchMethod(cm CallMeta, recv Value, args []Value) (Value, error) {
	if recv.Kind == ValList && cm.CalleeName == "len" {
		if recv.List == nil {
			return VInt(0), nil
		}
		return VInt(int64(len(*recv.List))), nil
	}
	if recv.Kind == ValStr && cm.CalleeName == "len" {
		return VInt(int64(len(recv.Str))), nil
	}
	if recv.Kind != ValHandle || recv.Handle == nil {
		return VVoid(), fmt.Errorf("method %s called on non-handle value %s", cm.CalleeName, recv)
	}
	h := recv.Handle
	switch h.Kind {
	case HandleListener:
		switch cm.CalleeName {
		case "port":
			addr := h.Listener.Addr().(*net.TCPAddr)
			return VInt(int64(addr.Port)), nil
		case "accept":
			return sockAccept(h, extractTimeoutMsFromMethod(cm, args, 0, 5000)), nil
		case "close":
			h.Close()
			return VVoid(), nil
		}
	case HandleStream:
		switch cm.CalleeName {
		case "send_text":
			return sockSend(h, args[0].Str), nil
		case "recv_text":
			maxB := int64(4096)
			if len(args) >= 1 {
				maxB = args[0].Int
			}
			return sockRecv(h, maxB), nil
		case "close":
			h.Close()
			return VVoid(), nil
		}
	case HandleFile:
		switch cm.CalleeName {
		case "read_text":
			b, err := io.ReadAll(h.File)
			if err != nil {
				return VErr(err.Error()), nil
			}
			return textRead(b), nil
		case "write_text":
			n, err := h.File.WriteString(args[0].Str)
			if err != nil {
				return VErr(err.Error()), nil
			}
			return VOk(VInt(int64(n))), nil
		case "close":
			h.Close()
			return VVoid(), nil
		}
	case HandleSession:
		switch cm.CalleeName {
		case "get":
			ms := extractTimeoutMsFromMethod(cm, args, 1, 5000)
			return vm.httpDo("GET", args[0].Str, "", ms, h.HTTPClient), nil
		case "post":
			ms := extractTimeoutMsFromMethod(cm, args, 2, 5000)
			body := ""
			if len(args) >= 2 {
				body = args[1].Str
			}
			return vm.httpDo("POST", args[0].Str, body, ms, h.HTTPClient), nil
		case "get_async":
			url := args[0].Str
			ms := extractTimeoutMsFromMethod(cm, args, 1, 5000)
			ch := make(chan Value, 1)
			go func() {
				ch <- vm.httpDo("GET", url, "", ms, h.HTTPClient)
			}()
			return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleFuture, FutCh: ch}}, nil
		case "close":
			h.Close()
			return VVoid(), nil
		}
	case HandleFuture:
		if cm.CalleeName == "await" {
			if !h.FutDone {
				h.FutVal = <-h.FutCh
				h.FutDone = true
			}
			return h.FutVal, nil
		}
	case HandleThreadPool:
		switch cm.CalleeName {
		case "submit":
			cl := args[0].Closure
			ch := make(chan Value, 1)
			h.PoolCh <- func() {
				r, err := vm.callClosure(cl, nil)
				if err != nil {
					ch <- VErr(err.Error())
				} else {
					ch <- r
				}
			}
			return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleFuture, FutCh: ch}}, nil
		case "shutdown":
			h.Close()
			return VVoid(), nil
		}
	case HandleChannel:
		switch cm.CalleeName {
		case "send":
			h.ChanMu.Lock()
			closed := h.ChanClosed
			h.ChanMu.Unlock()
			if closed {
				return VBool(false), nil
			}
			h.Chan <- args[0]
			return VBool(true), nil
		case "recv":
			v, ok := <-h.Chan
			if !ok {
				return VNone(), nil
			}
			return VSome(v), nil
		case "close":
			h.Close()
			return VVoid(), nil
		}
	case HandleMutex:
		switch cm.CalleeName {
		case "get":
			h.Mu.Lock()
			v := *h.MutexVal
			h.Mu.Unlock()
			return v, nil
		case "set":
			h.Mu.Lock()
			*h.MutexVal = args[0]
			h.Mu.Unlock()
			return VVoid(), nil
		case "with_lock":
			h.Mu.Lock()
			defer h.Mu.Unlock()
			if len(args) >= 1 && args[0].Closure != nil {
				res, err := vm.callClosure(args[0].Closure, []Value{*h.MutexVal})
				if err != nil {
					return VVoid(), err
				}
				*h.MutexVal = res
			}
			return VVoid(), nil
		}
	case HandleSemaphore:
		switch cm.CalleeName {
		case "acquire":
			h.Sem.acquire()
			return VVoid(), nil
		case "release":
			h.Sem.release()
			return VVoid(), nil
		}
	case HandleByteView:
		switch cm.CalleeName {
		case "len":
			return VInt(int64(len(h.Bytes))), nil
		case "read_u8":
			off := int(args[0].Int)
			return VInt(int64(h.Bytes[off])), nil
		case "read_u16_be":
			off := int(args[0].Int)
			return VInt(int64(binary.BigEndian.Uint16(h.Bytes[off : off+2]))), nil
		case "read_u32_be":
			off := int(args[0].Int)
			return VInt(int64(binary.BigEndian.Uint32(h.Bytes[off : off+4]))), nil
		case "slice":
			// The ends are brought inside the view, as on the native
			// backend: an empty view rather than a panic.
			lo, hi := args[0].Int, args[1].Int
			if hi > int64(len(h.Bytes)) {
				hi = int64(len(h.Bytes))
			}
			if hi < 0 {
				hi = 0
			}
			if lo < 0 {
				lo = 0
			}
			if lo > hi {
				lo = hi
			}
			return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleByteView, Bytes: h.Bytes[lo:hi]}}, nil
		}
	}
	return VVoid(), fmt.Errorf("unknown method %s on handle kind %d", cm.CalleeName, h.Kind)
}

func extractTimeoutMs(arg interface{}, args []Value, posIdx int, def int, _ ...any) int {
	switch v := arg.(type) {
	case CallMeta:
		for i, k := range v.KwNames {
			if k == "timeout_ms" && i < len(args) {
				return int(args[i].Int)
			}
		}
		if posIdx < len(args) {
			return int(args[posIdx].Int)
		}
	case *VM:
		// Reordered args passed from dispatchMethod: (vm, args, posIdx, cm, def)
		if len(args) > 0 && args[0].Kind == ValInt {
			return int(args[0].Int)
		}
	}
	return def
}

func extractTimeoutMsFromMethod(cm CallMeta, args []Value, posIdx int, def int) int {
	// KwNames has index 0 = receiver, 1.. = method args
	for i := 1; i < len(cm.KwNames); i++ {
		if cm.KwNames[i] == "timeout_ms" && i-1 < len(args) {
			return int(args[i-1].Int)
		}
	}
	if posIdx < len(args) {
		return int(args[posIdx].Int)
	}
	return def
}

// The answer of a server is given as the server gave it, as the native
// client gives it: a body is not asked for compressed nor decompressed, and
// a redirect is an answer like another, not followed. Each request has a
// connection of its own, as it has there: on one used again, what a server
// sent after an answer was read as the start of the next.
var plainTransport = newTransport()

// newTransport gives a transport that does what the native client does and
// no more: it speaks HTTP/1.1 only, straight to the server and through no
// proxy the environment names, and the one time limit is the request's.
func newTransport() *http.Transport {
	return &http.Transport{
		DialContext:        dialUntil,
		DisableCompression: true,
		DisableKeepAlives:  true,
		TLSNextProto:       map[string]func(string, *tls.Conn) http.RoundTripper{},
	}
}

// until is the key of a request's context under which its time limit is
// kept for the dialer.
type until struct{}

// dialUntil connects for a request, and what it connects ends with the
// request. Go's transport goes on connecting, and shaking hands over TLS,
// for a request that is over, so that the next may use the connection;
// here none does, and a server that never answered kept a socket of every
// request that gave it up. The connection is one request's, so the
// request's time limit is the connection's.
func dialUntil(ctx context.Context, network, addr string) (net.Conn, error) {
	end, ok := ctx.Value(until{}).(time.Time)
	if !ok {
		return (&net.Dialer{}).DialContext(ctx, network, addr)
	}
	ctx, cancel := context.WithDeadline(ctx, end)
	defer cancel()
	c, err := (&net.Dialer{}).DialContext(ctx, network, addr)
	if err == nil {
		_ = c.SetDeadline(end)
	}
	return c, err
}

// asAnswered hides from Go's client where a redirect leads, so that the
// client follows none and has no word to say on where one leads.
type asAnswered struct{ rt http.RoundTripper }

func (a asAnswered) RoundTrip(r *http.Request) (*http.Response, error) {
	resp, err := a.rt.RoundTrip(r)
	if resp != nil {
		resp.Header.Del("Location")
	}
	return resp, err
}

func escapeQuery(q string) string {
	var b strings.Builder
	for i := 0; i < len(q); i++ {
		if c := q[i]; c == ' ' || c == '"' || c == '<' || c == '>' || c >= 0x80 {
			fmt.Fprintf(&b, "%%%02X", c)
		} else {
			b.WriteByte(c)
		}
	}
	return b.String()
}

func hostRefused(host string) string {
	if strings.Contains(host, "%") {
		return "invalid host"
	}
	for i := 0; i < len(host); i++ {
		if host[i] >= 0x80 {
			return "non-ASCII host name"
		}
	}
	return ""
}

func (vm *VM) httpDo(method, url, body string, timeoutMs int, baseClient *http.Client) Value {
	var bodyReader io.Reader
	if body != "" {
		bodyReader = strings.NewReader(body)
	}
	// One time limit for the whole request. It is kept here and not by
	// http.Client.Timeout: that ends a request in two ways at once, and
	// which of the two is first decides the words of the error.
	end := time.Now().Add(time.Duration(timeoutMs) * time.Millisecond)
	ctx, cancel := context.WithDeadline(context.WithValue(context.Background(), until{}, end), end)
	defer cancel()
	// The time is up by the clock: the request and its connection end at
	// the same moment, and either may be the first to say so.
	late := func() bool { return ctx.Err() != nil || !time.Now().Before(end) }
	req, err := http.NewRequestWithContext(ctx, method, url, bodyReader)
	if err != nil {
		// Why an address in [ ] is none is said in more words than the
		// native client has for it.
		var ue *neturl.Error
		if errors.As(err, &ue) && strings.HasPrefix(ue.Err.Error(), "invalid host: ") {
			ue.Err = errors.New("invalid host")
		}
		return VErr(err.Error())
	}
	// Two hosts Go takes are no host here, nor to the native client: an
	// IPv6 address with a zone, and a name outside ASCII, which Go would
	// rewrite before it asks for it.
	if why := hostRefused(req.URL.Host); why != "" {
		named, _, _ := strings.Cut(url, "#")
		return VErr(fmt.Sprintf("parse %q: %s", named, why))
	}
	// Go sends a query as written. One with a space in it makes a first
	// line that is none, so what may not stand in one is written %XX, here
	// and by the native client.
	req.URL.RawQuery = escapeQuery(req.URL.RawQuery)
	// What is sent is what the native client sends.
	req.Header.Set("User-Agent", "anima")
	if body != "" {
		req.Header.Set("Content-Type", "application/json")
	}
	var tr http.RoundTripper = plainTransport
	if baseClient != nil {
		tr = baseClient.Transport
	}
	cl := &http.Client{Transport: asAnswered{tr}}
	// No str holds a NUL, the message of an Err no more than another: Go
	// gives some of a malformed answer as it came, and a NUL in that is
	// written \x00.
	resp, err := cl.Do(req)
	if err != nil {
		var ue *neturl.Error
		if late() && errors.As(err, &ue) {
			ue.Err = errors.New("context deadline exceeded (Client.Timeout exceeded while awaiting headers)")
		}
		msg := err.Error()
		// Which resolver was asked is this machine's own business. The
		// error is not changed to leave it out: requests that look up one
		// name at the same time are given the same one.
		var de *net.DNSError
		if errors.As(err, &de) && de.Server != "" {
			unasked := *de
			unasked.Server = ""
			if at := strings.LastIndex(msg, de.Error()); at >= 0 {
				msg = msg[:at] + unasked.Error() + msg[at+len(de.Error()):]
			}
		}
		return VErr(strings.ReplaceAll(msg, "\x00", `\x00`))
	}
	defer resp.Body.Close()
	raw, err := io.ReadAll(resp.Body)
	if err != nil {
		if late() {
			return VErr("context deadline exceeded (Client.Timeout or context cancellation while reading body)")
		}
		return VErr(strings.ReplaceAll(err.Error(), "\x00", `\x00`))
	}
	if bytes.IndexByte(raw, 0) >= 0 {
		return VErr(errTextNUL)
	}
	ent := &EntityInstance{
		TypeName: "HttpResponse",
		Fields: map[string]Value{
			"status": VInt(int64(resp.StatusCode)),
			"body":   VStr(string(raw)),
			"ok":     VBool(resp.StatusCode >= 200 && resp.StatusCode < 300),
		},
	}
	return VOk(Value{Kind: ValEntity, Entity: ent})
}

// A str holds no NUL: the native backend's strings end at one. What is read
// from outside the program and holds one is refused, on both backends.
const errTextNUL = "text holds a NUL"

func textRead(b []byte) Value {
	if bytes.IndexByte(b, 0) >= 0 {
		return VErr(errTextNUL)
	}
	return VOk(VStr(string(b)))
}

// jsonDecodeSchema is json.decode. With no type it gives the value of the
// JSON text, whatever it is. With an entity it gives that entity, checked
// by jsonAs. The native runtime does the same (json_decode_raw and
// json_decode_as).
func (vm *VM) jsonDecodeSchema(typeName, raw string) Value {
	if _, ok := vm.prog.Module.EntityIndex[typeName]; !ok {
		x, msg := parseJSON(raw, true)
		if msg != "" {
			return VErr(msg)
		}
		return VOk(goJSONToValue(x))
	}
	x, msg := parseJSON(raw, false)
	if msg != "" {
		return VErr(msg)
	}
	// Only an object is an entity: a null is not one with every field
	// absent.
	if _, ok := x.(map[string]any); !ok {
		return VErr(fmt.Sprintf("schema error: %s must be object", typeName))
	}
	v, msg := vm.jsonAs(&JSONType{Kind: "entity", Entity: typeName}, x, typeName)
	if msg != "" {
		return VErr(msg)
	}
	return VOk(v)
}

// jsonAs checks decoded JSON against a type and gives the value of that
// type, or says what is wrong. What it gives is typed as declared, so there
// is nothing it lets through unchecked: an int is in its range, every
// element of a list, value of a map and field of an entity is checked the
// same way, and an entity holds its invariant. The native runtime has the
// same rule and the same words (json_as in runtime_c.go).
func (vm *VM) jsonAs(t *JSONType, raw any, path string) (Value, string) {
	switch t.Kind {
	case "int":
		// A number with a fraction or an exponent, or outside 64 bits, is
		// a jsonNotInt: it is no int, however it is written.
		iv, ok := raw.(int64)
		if !ok {
			return Value{}, fmt.Sprintf("schema error: field %s must be integer", path)
		}
		if t.HasLo && iv < t.Lo {
			return Value{}, fmt.Sprintf("schema violation: %s=%d below minimum %d", path, iv, t.Lo)
		}
		if t.HasHi && iv > t.Hi {
			return Value{}, fmt.Sprintf("schema violation: %s=%d exceeds maximum %d", path, iv, t.Hi)
		}
		return VInt(iv), ""
	case "bool":
		bv, ok := raw.(bool)
		if !ok {
			return Value{}, fmt.Sprintf("schema error: field %s must be bool", path)
		}
		return VBool(bv), ""
	case "str":
		sv, ok := raw.(string)
		if !ok {
			return Value{}, fmt.Sprintf("schema error: field %s must be str", path)
		}
		return VStr(sv), ""
	case "list":
		arr, ok := raw.([]any)
		if !ok {
			return Value{}, fmt.Sprintf("schema error: field %s must be list", path)
		}
		out := make([]Value, len(arr))
		for i, el := range arr {
			v, msg := vm.jsonAs(t.Elem, el, fmt.Sprintf("%s[%d]", path, i))
			if msg != "" {
				return Value{}, msg
			}
			out[i] = v
		}
		return VList(out), ""
	case "map":
		obj, ok := raw.(map[string]any)
		if !ok {
			return Value{}, fmt.Sprintf("schema error: field %s must be map", path)
		}
		out := make(map[string]Value, len(obj))
		// In the order of the keys, so that the first thing wrong is the
		// same one from run to run and on the native backend.
		keys := make([]string, 0, len(obj))
		for k := range obj {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			v, msg := vm.jsonAs(t.Elem, obj[k], path+"["+quoteKey(k)+"]")
			if msg != "" {
				return Value{}, msg
			}
			out[k] = v
		}
		return VMap(out), ""
	case "option":
		if raw == nil {
			return VNone(), ""
		}
		v, msg := vm.jsonAs(t.Elem, raw, path)
		if msg != "" {
			return Value{}, msg
		}
		return VSome(v), ""
	case "entity":
		obj, ok := raw.(map[string]any)
		idx, known := vm.prog.Module.EntityIndex[t.Entity]
		if !ok || !known {
			return Value{}, fmt.Sprintf("schema error: field %s must be %s", path, t.Entity)
		}
		schema := vm.prog.Module.Entities[idx]
		fields := map[string]Value{}
		for _, f := range schema.Fields {
			rawVal, exists := obj[f.Name]
			if !exists && f.Type.Kind != "option" {
				return Value{}, fmt.Sprintf("schema error: missing field %s.%s", path, f.Name)
			}
			v, msg := vm.jsonAs(f.Type, rawVal, path+"."+f.Name)
			if msg != "" {
				return Value{}, msg
			}
			fields[f.Name] = v
		}
		entVal := Value{Kind: ValEntity, Entity: &EntityInstance{TypeName: t.Entity, Fields: fields}}
		for _, invFn := range schema.Invariants {
			okVal, _, _, err := vm.callFuncByName(invFn, []Value{entVal}, nil)
			if err != nil {
				return Value{}, "invariant evaluation error: " + err.Error()
			}
			if !okVal.IsTruthy() {
				return Value{}, fmt.Sprintf("entity invariant violated for %s on JSON input", t.Entity)
			}
		}
		return entVal, ""
	}
	return Value{}, fmt.Sprintf("schema error: field %s is not read from JSON", path)
}

func goJSONToValue(x any) Value {
	switch v := x.(type) {
	case int64:
		return VInt(v)
	case bool:
		return VBool(v)
	case string:
		return VStr(v)
	case []any:
		out := make([]Value, len(v))
		for i, e := range v {
			out[i] = goJSONToValue(e)
		}
		return VList(out)
	case map[string]any:
		out := make(map[string]Value, len(v))
		for k, e := range v {
			out[k] = goJSONToValue(e)
		}
		return VMap(out)
	default:
		return VNone()
	}
}

func valueToGoJSON(v Value) any {
	return valueToJSON(v, nil)
}

// valueToJSON gives null for a list, map or entity met again inside itself:
// one can hold itself, and its encoding would have no end.
func valueToJSON(v Value, open []uintptr) any {
	if box, ok := boxOf(v); ok {
		for _, o := range open {
			if o == box {
				return nil
			}
		}
		open = append(open, box)
	}
	switch v.Kind {
	case ValInt:
		return v.Int
	case ValBool:
		return v.Bool
	case ValStr:
		return v.Str
	case ValList:
		if v.List == nil {
			return []any{}
		}
		out := make([]any, len(*v.List))
		for i, el := range *v.List {
			out[i] = valueToJSON(el, open)
		}
		return out
	case ValMap:
		out := map[string]any{}
		for k, val := range v.Map {
			out[k] = valueToJSON(val, open)
		}
		return out
	case ValEntity:
		out := map[string]any{}
		for k, val := range v.Entity.Fields {
			out[k] = valueToJSON(val, open)
		}
		return out
	case ValVariant:
		// Some(x) is x and None is null, which is what json.decode reads
		// an Option from; any other variant is its text.
		if v.Variant != nil && v.Variant.Name == "Some" && len(v.Variant.Fields) == 1 {
			return valueToJSON(v.Variant.Fields[0], open)
		}
		return v.text(open[:len(open)-1])
	default:
		return nil
	}
}

func (vm *VM) fpFilter(args []Value) (Value, error) {
	if len(args) < 2 || args[0].List == nil || args[1].Closure == nil {
		return VList(nil), nil
	}
	var out []Value
	for _, el := range *args[0].List {
		keep, err := vm.callClosure(args[1].Closure, []Value{el})
		if err != nil {
			return VVoid(), err
		}
		if keep.IsTruthy() {
			out = append(out, el)
		}
	}
	return VList(out), nil
}

func (vm *VM) fpMap(args []Value) (Value, error) {
	if len(args) < 2 || args[0].List == nil || args[1].Closure == nil {
		return VList(nil), nil
	}
	var out []Value
	for _, el := range *args[0].List {
		r, err := vm.callClosure(args[1].Closure, []Value{el})
		if err != nil {
			return VVoid(), err
		}
		out = append(out, r)
	}
	return VList(out), nil
}

func (vm *VM) fpFlatMap(args []Value) (Value, error) {
	if len(args) < 2 || args[0].List == nil || args[1].Closure == nil {
		return VList(nil), nil
	}
	var out []Value
	for _, el := range *args[0].List {
		r, err := vm.callClosure(args[1].Closure, []Value{el})
		if err != nil {
			return VVoid(), err
		}
		if r.Kind == ValList && r.List != nil {
			out = append(out, *r.List...)
		}
	}
	return VList(out), nil
}

func (vm *VM) fpFold(args []Value) (Value, error) {
	if len(args) < 3 || args[0].List == nil || args[2].Closure == nil {
		return args[1], nil
	}
	acc := args[1]
	for _, el := range *args[0].List {
		var err error
		acc, err = vm.callClosure(args[2].Closure, []Value{acc, el})
		if err != nil {
			return VVoid(), err
		}
	}
	return acc, nil
}
