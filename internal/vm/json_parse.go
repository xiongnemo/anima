package vm

import (
	"fmt"
	"strconv"
	"unicode/utf8"
)

// jsonMaxDepth is how deep the arrays and objects of a JSON text nest. The
// native parser recurses on the C stack, so there is a limit, and it is the
// same here.
const jsonMaxDepth = 1000

// jsonNotInt is a JSON number that is not an int: one written with a
// fraction or an exponent, or outside 64 bits. There is no value for it, so
// it is an error wherever a value is read from it.
type jsonNotInt struct{}

// jsonParser reads a JSON text as RFC 8259 defines one, and nothing else:
// the native runtime has the same parser, statement for statement
// (json_parse in runtime_c.go), so that a text is read as the same value,
// or refused with the same words, on both backends.
//
// What it gives is nil, bool, int64, string, []any and map[string]any, and
// jsonNotInt where ints is false; where ints is true such a number is an
// error. Of two members with one key the last is kept.
type jsonParser struct {
	s     string
	i     int
	ints  bool
	depth int
	err   string
}

func parseJSON(s string, ints bool) (any, string) {
	p := &jsonParser{s: s, ints: ints}
	p.ws()
	v := p.value()
	if p.err == "" {
		p.ws()
		if p.i < len(p.s) {
			p.fail("unexpected character")
		}
	}
	if p.err != "" {
		return nil, p.err
	}
	return v, ""
}

func (p *jsonParser) fail(what string) {
	if p.err == "" {
		p.err = fmt.Sprintf("invalid JSON at offset %d: %s", p.i, what)
	}
}

// unexpected fails at the byte the parser is on, or at the end of the text.
func (p *jsonParser) unexpected() {
	if p.i >= len(p.s) {
		p.fail("unexpected end of text")
	} else {
		p.fail("unexpected character")
	}
}

func (p *jsonParser) ws() {
	for p.i < len(p.s) && (p.s[p.i] == ' ' || p.s[p.i] == '\t' || p.s[p.i] == '\n' || p.s[p.i] == '\r') {
		p.i++
	}
}

func (p *jsonParser) digit() bool {
	return p.i < len(p.s) && p.s[p.i] >= '0' && p.s[p.i] <= '9'
}

func (p *jsonParser) word(w string) bool {
	if len(p.s)-p.i >= len(w) && p.s[p.i:p.i+len(w)] == w {
		p.i += len(w)
		return true
	}
	return false
}

func (p *jsonParser) value() any {
	if p.i >= len(p.s) {
		p.unexpected()
		return nil
	}
	switch c := p.s[p.i]; {
	case c == '"':
		return p.str()
	case c == '{':
		return p.object()
	case c == '[':
		return p.array()
	case c == '-' || (c >= '0' && c <= '9'):
		return p.number()
	}
	if p.word("true") {
		return true
	}
	if p.word("false") {
		return false
	}
	if p.word("null") {
		return nil
	}
	p.unexpected()
	return nil
}

func (p *jsonParser) number() any {
	start := p.i
	if p.s[p.i] == '-' {
		p.i++
	}
	if !p.digit() {
		p.unexpected()
		return nil
	}
	// A number does not start with a 0 it could do without: 01 ends at the
	// 0, and the 1 is where no character is expected.
	if p.s[p.i] == '0' {
		p.i++
	} else {
		for p.digit() {
			p.i++
		}
	}
	isInt := true
	if p.i < len(p.s) && p.s[p.i] == '.' {
		isInt = false
		p.i++
		if !p.digit() {
			p.unexpected()
			return nil
		}
		for p.digit() {
			p.i++
		}
	}
	if p.i < len(p.s) && (p.s[p.i] == 'e' || p.s[p.i] == 'E') {
		isInt = false
		p.i++
		if p.i < len(p.s) && (p.s[p.i] == '+' || p.s[p.i] == '-') {
			p.i++
		}
		if !p.digit() {
			p.unexpected()
			return nil
		}
		for p.digit() {
			p.i++
		}
	}
	if isInt {
		if n, err := strconv.ParseInt(p.s[start:p.i], 10, 64); err == nil {
			return n
		}
	}
	if p.ints {
		p.i = start
		p.fail("number is not an int")
		return nil
	}
	return jsonNotInt{}
}

// hex4 reads the four hex digits of a \u escape at i, or gives -1.
func (p *jsonParser) hex4(i int) int {
	if len(p.s)-i < 4 {
		return -1
	}
	r := 0
	for _, c := range []byte(p.s[i : i+4]) {
		d := 0
		switch {
		case c >= '0' && c <= '9':
			d = int(c - '0')
		case c >= 'a' && c <= 'f':
			d = int(c-'a') + 10
		case c >= 'A' && c <= 'F':
			d = int(c-'A') + 10
		default:
			return -1
		}
		r = r*16 + d
	}
	return r
}

// str reads a string, the parser being on its opening quote. Nil is given
// with an error.
func (p *jsonParser) str() any {
	p.i++
	var out []byte
	for {
		if p.i >= len(p.s) {
			p.unexpected()
			return nil
		}
		c := p.s[p.i]
		switch {
		case c == '"':
			p.i++
			return string(out)
		case c < 0x20:
			p.fail("control character in string")
			return nil
		case c == '\\':
			if p.i+1 >= len(p.s) {
				p.i++
				p.unexpected()
				return nil
			}
			e := p.s[p.i+1]
			if e == 'u' {
				cp := p.hex4(p.i + 2)
				if cp < 0 {
					p.fail("invalid escape")
					return nil
				}
				// A string of the native runtime ends at a NUL, so it
				// cannot hold one: the text is refused on both backends.
				if cp == 0 {
					p.fail("NUL in string")
					return nil
				}
				p.i += 6
				// Two escapes can be a surrogate pair; half a pair is
				// U+FFFD, and what follows it is read on its own.
				if cp >= 0xd800 && cp <= 0xdbff {
					lo := -1
					if p.i+1 < len(p.s) && p.s[p.i] == '\\' && p.s[p.i+1] == 'u' {
						lo = p.hex4(p.i + 2)
					}
					if lo >= 0xdc00 && lo <= 0xdfff {
						cp = 0x10000 + (cp-0xd800)<<10 + (lo - 0xdc00)
						p.i += 6
					} else {
						cp = 0xfffd
					}
				} else if cp >= 0xdc00 && cp <= 0xdfff {
					cp = 0xfffd
				}
				out = utf8.AppendRune(out, rune(cp))
				continue
			}
			switch e {
			case '"', '\\', '/':
				out = append(out, e)
			case 'b':
				out = append(out, '\b')
			case 'f':
				out = append(out, '\f')
			case 'n':
				out = append(out, '\n')
			case 'r':
				out = append(out, '\r')
			case 't':
				out = append(out, '\t')
			default:
				p.fail("invalid escape")
				return nil
			}
			p.i += 2
		case c < 0x80:
			out = append(out, c)
			p.i++
		default:
			// A byte that is not UTF-8 is U+FFFD, as json.encode writes it.
			r, n := utf8.DecodeRuneInString(p.s[p.i:])
			if r == utf8.RuneError && n == 1 {
				out = append(out, "\ufffd"...)
			} else {
				out = append(out, p.s[p.i:p.i+n]...)
			}
			p.i += n
		}
	}
}

func (p *jsonParser) open() bool {
	if p.depth >= jsonMaxDepth {
		p.fail("nested too deep")
		return false
	}
	p.depth++
	p.i++
	p.ws()
	return true
}

func (p *jsonParser) array() any {
	if !p.open() {
		return nil
	}
	out := []any{}
	if p.i < len(p.s) && p.s[p.i] == ']' {
		p.i++
		p.depth--
		return out
	}
	for {
		p.ws()
		v := p.value()
		if p.err != "" {
			return nil
		}
		out = append(out, v)
		p.ws()
		if p.i < len(p.s) && p.s[p.i] == ',' {
			p.i++
			continue
		}
		if p.i < len(p.s) && p.s[p.i] == ']' {
			p.i++
			p.depth--
			return out
		}
		p.unexpected()
		return nil
	}
}

func (p *jsonParser) object() any {
	if !p.open() {
		return nil
	}
	out := map[string]any{}
	if p.i < len(p.s) && p.s[p.i] == '}' {
		p.i++
		p.depth--
		return out
	}
	for {
		p.ws()
		if p.i >= len(p.s) || p.s[p.i] != '"' {
			p.unexpected()
			return nil
		}
		k := p.str()
		if p.err != "" {
			return nil
		}
		p.ws()
		if p.i >= len(p.s) || p.s[p.i] != ':' {
			p.unexpected()
			return nil
		}
		p.i++
		p.ws()
		v := p.value()
		if p.err != "" {
			return nil
		}
		out[k.(string)] = v
		p.ws()
		if p.i < len(p.s) && p.s[p.i] == ',' {
			p.i++
			continue
		}
		if p.i < len(p.s) && p.s[p.i] == '}' {
			p.i++
			p.depth--
			return out
		}
		p.unexpected()
		return nil
	}
}
