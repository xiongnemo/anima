package vm

import (
	"bytes"
	"encoding/json"
	"math/rand"
	"reflect"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

// What parseJSON is held to: Go's encoding/json decides what a JSON text
// is and what its strings are. parseJSON differs from it where the language
// has to: a number that is not an int has no value, a string does not hold
// a NUL, and the nesting ends at jsonMaxDepth.

var jsonIntRE = regexp.MustCompile(`^-?(0|[1-9][0-9]*)$`)

func jsonRefValue(x any) any {
	switch v := x.(type) {
	case json.Number:
		if jsonIntRE.MatchString(string(v)) {
			if n, err := strconv.ParseInt(string(v), 10, 64); err == nil {
				return n
			}
		}
		return jsonNotInt{}
	case []any:
		out := make([]any, len(v))
		for i, e := range v {
			out[i] = jsonRefValue(e)
		}
		return out
	case map[string]any:
		out := make(map[string]any, len(v))
		for k, e := range v {
			out[k] = jsonRefValue(e)
		}
		return out
	}
	return x
}

// jsonRefScan reads a text that is valid JSON for how deep it nests and
// whether a string of it has an escaped NUL.
func jsonRefScan(s string) (depth int, nul bool) {
	d, inStr := 0, false
	for i := 0; i < len(s); i++ {
		switch c := s[i]; {
		case inStr && c == '\\':
			if strings.HasPrefix(s[i+1:], "u0000") {
				nul = true
			}
			i++
		case c == '"':
			inStr = !inStr
		case !inStr && (c == '[' || c == '{'):
			d++
			if d > depth {
				depth = d
			}
		case !inStr && (c == ']' || c == '}'):
			d--
		}
	}
	return depth, nul
}

func checkJSONAgainstRef(t *testing.T, s string) {
	t.Helper()
	got, msg := parseJSON(s, false)
	valid := json.Valid([]byte(s))
	depth, nul := 0, false
	if valid {
		depth, nul = jsonRefScan(s)
	}
	switch {
	case !valid:
		if msg == "" {
			t.Fatalf("%q: accepted as %#v, and is not JSON", s, got)
		}
		if strings.Contains(msg, "NUL in string") || strings.Contains(msg, "nested too deep") || strings.Contains(msg, "not an int") {
			// Such a text may be malformed further on; these are found first.
			return
		}
	case nul:
		if !strings.Contains(msg, "NUL in string") && !(depth > jsonMaxDepth && strings.Contains(msg, "nested too deep")) {
			t.Fatalf("%q: a NUL in a string, got %#v %q", s, got, msg)
		}
	case depth > jsonMaxDepth:
		if !strings.Contains(msg, "nested too deep") {
			t.Fatalf("%q: nested %d deep, got %q", s, depth, msg)
		}
	default:
		if msg != "" {
			t.Fatalf("%q: refused with %q, and is JSON", s, msg)
		}
		dec := json.NewDecoder(bytes.NewReader([]byte(s)))
		dec.UseNumber()
		var ref any
		if err := dec.Decode(&ref); err != nil {
			t.Fatalf("%q: reference: %v", s, err)
		}
		if want := jsonRefValue(ref); !reflect.DeepEqual(got, want) {
			t.Fatalf("%q: got %#v, want %#v", s, got, want)
		}
	}
	// With ints the same text is the same value, or it has a number that
	// is not an int.
	got2, msg2 := parseJSON(s, true)
	switch {
	case msg != "":
		if msg2 == "" {
			t.Fatalf("%q: refused without ints (%q), accepted with", s, msg)
		}
	case msg2 != "":
		// The number may be in a member that a later one with its key
		// replaced, so it need not be in the value.
		if !strings.Contains(msg2, "number is not an int") || !strings.ContainsAny(s, ".eE0123456789") {
			t.Fatalf("%q: with ints %q, without %#v", s, msg2, got)
		}
	default:
		if hasNotInt(got) || !reflect.DeepEqual(got, got2) {
			t.Fatalf("%q: with ints %#v, without %#v", s, got2, got)
		}
	}
}

func hasNotInt(x any) bool {
	switch v := x.(type) {
	case jsonNotInt:
		return true
	case []any:
		for _, e := range v {
			if hasNotInt(e) {
				return true
			}
		}
	case map[string]any:
		for _, e := range v {
			if hasNotInt(e) {
				return true
			}
		}
	}
	return false
}

var jsonSeeds = []string{
	``, ` `, `null`, `true`, `false`, `0`, `-0`, `1`, `-1`, `01`, `-01`, `+1`, `1.0`, `1.`, `.5`, `1e2`, `1E+2`, `1e-2`, `1e`, `1e+`, `-`, `--1`,
	`9223372036854775807`, `9223372036854775808`, `-9223372036854775808`, `-9223372036854775809`, `9007199254740993`, `123456789012345678901234567890`,
	`""`, `"a"`, `"a\"b"`, `"\\"`, `"\/"`, `"\b\f\n\r\t"`, `"\q"`, `"\u12"`, `"\u12zz"`, `"\u0041"`, `"\u00e9"`, `"\u0000"`, `"\ud83d\ude00"`, `"\ud83d"`, `"\ude00"`,
	`"\ud83d\u0041"`, `"\ud83d\ud83d\ude00"`, `"\ud83d\u0000"`, `"\uD83D\uDE00"`, "\"a\tb\"", "\"a\nb\"", "\"\x7f\"", "\"\xff\"", "\"\xc3\xa9\"", "\"\xc3\"", "\"\xed\xa0\x80\"", "\"\xf4\x90\x80\x80\"", "\"\xe2\x80\xa8\"",
	`"abc`, `"abc\`, `"abc\u`, `"abc\u12`,
	`[]`, `[1]`, `[1,2]`, `[1,]`, `[,1]`, `[1 2]`, `[`, `]`, `[[]]`, `[[[[[]]]]]`, `[1,[2,[3,{"a":[4]}]]]`,
	`{}`, `{"a":1}`, `{"a":1,}`, `{,}`, `{"a"}`, `{"a":}`, `{"a" 1}`, `{a:1}`, `{'a':1}`, `{"a":1 "b":2}`, `{"a":1,"a":2}`, `{"a":{"b":{"c":null}}}`, `{"":0}`, `{"a":"\u0000","a":1}`,
	`{"a":1} x`, `{"a":1}}`, `{"a":1}{"a":1}`, ` {"a" : 1 , "b" : [ true , false , null ] } `, "\t\n\r {}", "{}\v", "{}\f", "\xef\xbb\xbf{}", "{}\x00", "\x00",
	`tru`, `truex`, `True`, `nul`, `nulll`, `falsee`, `NaN`, `Infinity`, `-Infinity`, `undefined`,
	`{"n":1,"ok":true,"s":"a","xs":[1,2],"m":{"b":2,"a":1},"inner":{"d":3,"tag":"t"},"o":null,"f":1.5,"big":1e400}`,
}

var jsonBits = []string{
	`{`, `}`, `[`, `]`, `,`, `:`, `"`, `\`, `\u`, `\u0000`, `\ud83d`, `\ude00`, `\n`, `\"`, `null`, `true`, `false`, `0`, `1`, `-`, `+`, `.`, `e`, `E`, `9223372036854775808`,
	` `, "\t", "\n", "\r", "\v", "\x01", "\x1f", "\x7f", "\x80", "\xc3", "\xa9", "\xff", "\xed\xa0\x80", "é", "😀", `"a":`, `[1]`, `{"k":"v"}`, `/`, `a`,
}

func mutateJSON(r *rand.Rand, s string) string {
	b := []byte(s)
	for n := 1 + r.Intn(3); n > 0; n-- {
		at := 0
		if len(b) > 0 {
			at = r.Intn(len(b) + 1)
		}
		switch r.Intn(5) {
		case 0: // insert
			bit := jsonBits[r.Intn(len(jsonBits))]
			b = append(b[:at:at], append([]byte(bit), b[at:]...)...)
		case 1: // delete
			if at < len(b) {
				b = append(b[:at:at], b[at+1:]...)
			}
		case 2: // replace
			if at < len(b) {
				bit := jsonBits[r.Intn(len(jsonBits))]
				b = append(b[:at:at], append([]byte(bit), b[at+1:]...)...)
			}
		case 3: // cut short
			b = b[:at]
		case 4: // repeat a part
			if at < len(b) {
				end := at + 1 + r.Intn(len(b)-at)
				b = append(b[:end:end], append(append([]byte{}, b[at:end]...), b[end:]...)...)
			}
		}
	}
	return string(b)
}

func randomJSON(r *rand.Rand, depth int) string {
	k := r.Intn(9)
	if depth <= 0 && k >= 7 {
		k = r.Intn(7)
	}
	ws := func() string { return []string{"", "", "", " ", "\n", "\t", "\r"}[r.Intn(7)] }
	str := func() string {
		var sb strings.Builder
		sb.WriteByte('"')
		for n := r.Intn(5); n > 0; n-- {
			sb.WriteString([]string{"a", "é", "😀", `\n`, `\"`, `\\`, `\/`, `\u0041`, `\ud83d\ude00`, `\ud83d`, `\udead`, " ", "<", "\x7f", `\u00E9`}[r.Intn(15)])
		}
		sb.WriteByte('"')
		return sb.String()
	}
	switch k {
	case 0:
		return "null"
	case 1:
		return "true"
	case 2:
		return "false"
	case 3:
		return strconv.FormatInt(r.Int63()>>uint(r.Intn(64))-r.Int63()>>uint(r.Intn(64)), 10)
	case 4:
		return []string{"0", "-0", "1.5", "1e3", "-2E-2", "9223372036854775807", "-9223372036854775808", "9223372036854775808", "0.0", "10"}[r.Intn(10)]
	case 5, 6:
		return str()
	case 7:
		var sb strings.Builder
		sb.WriteString("[" + ws())
		for i, n := 0, r.Intn(4); i < n; i++ {
			if i > 0 {
				sb.WriteString(ws() + "," + ws())
			}
			sb.WriteString(randomJSON(r, depth-1))
		}
		sb.WriteString(ws() + "]")
		return sb.String()
	default:
		var sb strings.Builder
		sb.WriteString("{" + ws())
		for i, n := 0, r.Intn(4); i < n; i++ {
			if i > 0 {
				sb.WriteString(ws() + "," + ws())
			}
			sb.WriteString(str() + ws() + ":" + ws() + randomJSON(r, depth-1))
		}
		sb.WriteString(ws() + "}")
		return sb.String()
	}
}

func TestParseJSONAgainstEncodingJSON(t *testing.T) {
	for _, s := range jsonSeeds {
		checkJSONAgainstRef(t, s)
	}
	r := rand.New(rand.NewSource(1))
	n := 200000
	if testing.Short() {
		n = 20000
	}
	for i := 0; i < n; i++ {
		var s string
		if i%2 == 0 {
			s = randomJSON(r, 4)
		} else {
			s = jsonSeeds[r.Intn(len(jsonSeeds))]
		}
		if i%4 >= 2 {
			s = mutateJSON(r, s)
		}
		checkJSONAgainstRef(t, s)
	}
}

func TestParseJSONDepth(t *testing.T) {
	for _, open := range []string{"[", `{"a":`} {
		closeBy := map[string]string{"[": "]", `{"a":`: "}"}[open]
		for _, d := range []int{1, jsonMaxDepth - 1, jsonMaxDepth, jsonMaxDepth + 1, 3 * jsonMaxDepth} {
			s := strings.Repeat(open, d) + "1" + strings.Repeat(closeBy, d)
			_, msg := parseJSON(s, true)
			if (msg == "") != (d <= jsonMaxDepth) {
				t.Fatalf("%d deep: %q", d, msg)
			}
			checkJSONAgainstRef(t, s)
		}
	}
	// Side by side is not deep.
	if _, msg := parseJSON("["+strings.Repeat("[[]],", 5000)+"[]]", true); msg != "" {
		t.Fatal(msg)
	}
}

func TestParseJSONErrors(t *testing.T) {
	for _, c := range []struct{ in, want string }{
		{``, "invalid JSON at offset 0: unexpected end of text"},
		{`{"a":1} x`, "invalid JSON at offset 8: unexpected character"},
		{`{"a":01}`, "invalid JSON at offset 6: unexpected character"},
		{`{"a":1.5}`, "invalid JSON at offset 5: number is not an int"},
		{`[9223372036854775808]`, "invalid JSON at offset 1: number is not an int"},
		{`"a\qb"`, "invalid JSON at offset 2: invalid escape"},
		{`"a\u0000b"`, "invalid JSON at offset 2: NUL in string"},
		{"\"a\tb\"", "invalid JSON at offset 2: control character in string"},
		{`"abc`, "invalid JSON at offset 4: unexpected end of text"},
		{`[1,]`, "invalid JSON at offset 3: unexpected character"},
	} {
		if _, msg := parseJSON(c.in, true); msg != c.want {
			t.Errorf("%q: %q, want %q", c.in, msg, c.want)
		}
	}
}

func FuzzParseJSON(f *testing.F) {
	for _, s := range jsonSeeds {
		f.Add(s)
	}
	f.Fuzz(func(t *testing.T, s string) {
		checkJSONAgainstRef(t, s)
	})
}
