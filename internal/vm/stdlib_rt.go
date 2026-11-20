package vm

import (
	"crypto/hmac"
	"crypto/sha256"
	"crypto/subtle"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"
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
		host := args[0].Str
		port := args[1].Int
		ln, err := net.Listen("tcp", fmt.Sprintf("%s:%d", host, port))
		if err != nil {
			return VErr(err.Error()), nil
		}
		return VOk(Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleListener, Listener: ln}}), nil

	case "std.socket.connect_tcp":
		host := args[0].Str
		port := args[1].Int
		conn, err := net.DialTimeout("tcp", fmt.Sprintf("%s:%d", host, port), 5*time.Second)
		if err != nil {
			return VErr(err.Error()), nil
		}
		return VOk(Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleStream, Conn: conn}}), nil

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
		if len(args) >= 1 && args[0].Int > 0 {
			poolSize = int(args[0].Int)
		}
		tr := &http.Transport{MaxIdleConnsPerHost: poolSize, MaxIdleConns: poolSize * 2}
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
		workers := 4
		qcap := 16
		if len(args) >= 1 && args[0].Int > 0 {
			workers = int(args[0].Int)
		}
		if len(args) >= 2 && args[1].Int > 0 {
			qcap = int(args[1].Int)
		}
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
		if len(args) >= 1 && args[0].Int > 0 {
			capVal = int(args[0].Int)
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
		n := 1
		if len(args) >= 1 && args[0].Int > 0 {
			n = int(args[0].Int)
		}
		sem := make(chan struct{}, n)
		for i := 0; i < n; i++ {
			sem <- struct{}{}
		}
		return Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleSemaphore, Sem: sem}}, nil

	case "std.concurrent.parallel_map":
		if len(args) >= 2 && args[0].List != nil && args[1].Closure != nil {
			xs := *args[0].List
			out := make([]Value, len(xs))
			var wg sync.WaitGroup
			var firstErr error
			var errMu sync.Mutex
			for i, item := range xs {
				wg.Add(1)
				go func(idx int, v Value) {
					defer wg.Done()
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
		return VOk(VStr(string(b))), nil

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
		if len(args) >= 1 && args[0].Int > 0 {
			time.Sleep(time.Duration(args[0].Int) * time.Millisecond)
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
			ms := extractTimeoutMsFromMethod(cm, args, 0, 5000)
			if tl, ok := h.Listener.(*net.TCPListener); ok {
				_ = tl.SetDeadline(time.Now().Add(time.Duration(ms) * time.Millisecond))
			}
			conn, err := h.Listener.Accept()
			if err != nil {
				return VErr(err.Error()), nil
			}
			return VOk(Value{Kind: ValHandle, Handle: &HandleValue{Kind: HandleStream, Conn: conn}}), nil
		case "close":
			h.Close()
			return VVoid(), nil
		}
	case HandleStream:
		switch cm.CalleeName {
		case "send_text":
			if h.Closed {
				return VErr("socket closed"), nil
			}
			n, err := h.Conn.Write([]byte(args[0].Str))
			if err != nil {
				return VErr(err.Error()), nil
			}
			return VOk(VInt(int64(n))), nil
		case "recv_text":
			if h.Closed {
				return VErr("socket closed"), nil
			}
			maxB := 4096
			if len(args) >= 1 && args[0].Int > 0 {
				maxB = int(args[0].Int)
			}
			_ = h.Conn.SetReadDeadline(time.Now().Add(5 * time.Second))
			buf := make([]byte, maxB)
			n, err := h.Conn.Read(buf)
			if err != nil && n == 0 {
				return VErr(err.Error()), nil
			}
			return VOk(VStr(string(buf[:n]))), nil
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
			return VOk(VStr(string(b))), nil
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
			<-h.Sem
			return VVoid(), nil
		case "release":
			h.Sem <- struct{}{}
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

func (vm *VM) httpDo(method, url, body string, timeoutMs int, baseClient *http.Client) Value {
	var bodyReader io.Reader
	if body != "" {
		bodyReader = strings.NewReader(body)
	}
	req, err := http.NewRequest(method, url, bodyReader)
	if err != nil {
		return VErr(err.Error())
	}
	cl := &http.Client{Timeout: time.Duration(timeoutMs) * time.Millisecond}
	if baseClient != nil {
		cl.Transport = baseClient.Transport
	}
	resp, err := cl.Do(req)
	if err != nil {
		return VErr(err.Error())
	}
	defer resp.Body.Close()
	raw, err := io.ReadAll(resp.Body)
	if err != nil {
		return VErr(err.Error())
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

func (vm *VM) jsonDecodeSchema(typeName, raw string) Value {
	m, err := decodeJSONToMap(raw)
	if err != nil {
		return VErr("invalid JSON: " + err.Error())
	}
	idx, ok := vm.prog.Module.EntityIndex[typeName]
	if !ok {
		out := map[string]Value{}
		for k, v := range m {
			out[k] = goJSONToValue(v)
		}
		return VOk(VMap(out))
	}
	schema := vm.prog.Module.Entities[idx]
	fields := map[string]Value{}
	for _, f := range schema.Fields {
		rawVal, exists := m[f.Name]
		if !exists {
			return VErr(fmt.Sprintf("schema error: missing field %s.%s", typeName, f.Name))
		}
		switch f.Kind {
		case "int":
			num, ok := rawVal.(float64)
			if !ok {
				return VErr(fmt.Sprintf("schema error: field %s.%s must be integer", typeName, f.Name))
			}
			iv := int64(num)
			if float64(iv) != num {
				return VErr(fmt.Sprintf("schema error: field %s.%s must be exact integer", typeName, f.Name))
			}
			if f.HasLo && iv < f.Lo {
				return VErr(fmt.Sprintf("schema violation: %s.%s=%d below minimum %d", typeName, f.Name, iv, f.Lo))
			}
			if f.HasHi && iv > f.Hi {
				return VErr(fmt.Sprintf("schema violation: %s.%s=%d exceeds maximum %d", typeName, f.Name, iv, f.Hi))
			}
			fields[f.Name] = VInt(iv)
		case "bool":
			bv, ok := rawVal.(bool)
			if !ok {
				return VErr(fmt.Sprintf("schema error: field %s.%s must be bool", typeName, f.Name))
			}
			fields[f.Name] = VBool(bv)
		case "str":
			sv, ok := rawVal.(string)
			if !ok {
				return VErr(fmt.Sprintf("schema error: field %s.%s must be str", typeName, f.Name))
			}
			fields[f.Name] = VStr(sv)
		default:
			fields[f.Name] = goJSONToValue(rawVal)
		}
	}
	entVal := Value{Kind: ValEntity, Entity: &EntityInstance{TypeName: typeName, Fields: fields}}
	// Evaluate compiled SPARK entity invariant bytecode function!
	for _, invFn := range schema.Invariants {
		okVal, _, _, err := vm.callFuncByName(invFn, []Value{entVal}, nil)
		if err != nil {
			return VErr("invariant evaluation error: " + err.Error())
		}
		if !okVal.IsTruthy() {
			return VErr(fmt.Sprintf("entity invariant violated for %s on JSON input", typeName))
		}
	}
	return VOk(entVal)
}

func goJSONToValue(x any) Value {
	switch v := x.(type) {
	case float64:
		return VInt(int64(v))
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
