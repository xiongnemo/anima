package lexer

import (
	"fmt"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/xiongnemo/anima/internal/ast"
)

type TokenKind int

const (
	TokEOF TokenKind = iota
	TokNewline
	TokIndent
	TokDedent
	TokIdent
	TokInt
	TokStr
	TokFStr

	// Hard keywords
	TokImport
	TokAs
	TokDef
	TokMut
	TokIf
	TokElif
	TokElse
	TokMatch
	TokFor
	TokIn
	TokWhile
	TokReturn
	TokRunWorkflow
	TokAnd
	TokOr
	TokNot
	TokImplies
	TokTrue
	TokFalse
	TokNone
	TokWith

	// Operators & Punctuation
	TokPlus     // +
	TokMinus    // -
	TokStar     // *
	TokSlash    // /
	TokPercent  // %
	TokEq       // ==
	TokNeq      // !=
	TokLt       // <
	TokLe       // <=
	TokGt       // >
	TokGe       // >=
	TokAssign   // =
	TokPlusEq   // +=
	TokMinusEq  // -=
	TokStarEq   // *=
	TokAmp      // &
	TokCaret    // ^
	TokTilde    // ~
	TokShl      // <<
	TokShr      // >>
	TokArrow    // ->
	TokFatArrow // =>
	TokPipe     // |>
	TokDotDot   // ..
	TokDot      // .
	TokComma    // ,
	TokColon    // :
	TokSemi     // ;
	TokQuestion // ?
	TokBar      // |
	TokLParen   // (
	TokRParen   // )
	TokLBracket // [
	TokRBracket // ]
	TokLBrace   // {
	TokRBrace   // }
)

var kindNames = map[TokenKind]string{
	TokEOF:         "EOF",
	TokNewline:     "NEWLINE",
	TokIndent:      "INDENT",
	TokDedent:      "DEDENT",
	TokIdent:       "IDENT",
	TokInt:         "INT",
	TokStr:         "STR",
	TokFStr:        "FSTR",
	TokImport:      "import",
	TokAs:          "as",
	TokDef:         "def",
	TokMut:         "mut",
	TokIf:          "if",
	TokElif:        "elif",
	TokElse:        "else",
	TokMatch:       "match",
	TokFor:         "for",
	TokIn:          "in",
	TokWhile:       "while",
	TokReturn:      "return",
	TokRunWorkflow: "run_workflow",
	TokAnd:         "and",
	TokOr:          "or",
	TokNot:         "not",
	TokImplies:     "implies",
	TokTrue:        "True",
	TokFalse:       "False",
	TokNone:        "None",
	TokWith:        "with",
	TokPlus:        "+",
	TokMinus:       "-",
	TokStar:        "*",
	TokSlash:       "/",
	TokPercent:     "%",
	TokEq:          "==",
	TokNeq:         "!=",
	TokLt:          "<",
	TokLe:          "<=",
	TokGt:          ">",
	TokGe:          ">=",
	TokAssign:      "=",
	TokPlusEq:      "+=",
	TokMinusEq:     "-=",
	TokStarEq:      "*=",
	TokAmp:         "&",
	TokCaret:       "^",
	TokTilde:       "~",
	TokShl:         "<<",
	TokShr:         ">>",
	TokArrow:       "->",
	TokFatArrow:    "=>",
	TokPipe:        "|>",
	TokDotDot:      "..",
	TokDot:         ".",
	TokComma:       ",",
	TokColon:       ":",
	TokSemi:        ";",
	TokQuestion:    "?",
	TokBar:         "|",
	TokLParen:      "(",
	TokRParen:      ")",
	TokLBracket:    "[",
	TokRBracket:    "]",
	TokLBrace:      "{",
	TokRBrace:      "}",
}

func (k TokenKind) String() string {
	if s, ok := kindNames[k]; ok {
		return s
	}
	return fmt.Sprintf("Tok(%d)", int(k))
}

var keywords = map[string]TokenKind{
	"import":       TokImport,
	"as":           TokAs,
	"def":          TokDef,
	"mut":          TokMut,
	"if":           TokIf,
	"elif":         TokElif,
	"else":         TokElse,
	"match":        TokMatch,
	"for":          TokFor,
	"in":           TokIn,
	"while":        TokWhile,
	"return":       TokReturn,
	"run_workflow": TokRunWorkflow,
	"and":          TokAnd,
	"or":           TokOr,
	"not":          TokNot,
	"implies":      TokImplies,
	"True":         TokTrue,
	"False":        TokFalse,
	"None":         TokNone,
	"with":         TokWith,
}

type Token struct {
	Kind TokenKind
	Text string
	Int  int64
	Span ast.Span
}

func (t Token) String() string {
	if t.Kind == TokIdent || t.Kind == TokInt || t.Kind == TokStr || t.Kind == TokFStr {
		return fmt.Sprintf("%s(%s)", t.Kind, t.Text)
	}
	return t.Kind.String()
}

// Lex tokenizes an Anima source string into indentation-aware tokens.
func Lex(file, src string) ([]Token, error) {
	// A str holds no NUL, so no string literal does; nor does anything else.
	if at := strings.IndexByte(src, 0); at >= 0 {
		line := strings.Count(src[:at], "\n") + 1
		col := at - strings.LastIndexByte(src[:at], '\n')
		return nil, fmt.Errorf("%s:%d:%d: NUL byte in source", file, line, col)
	}
	src = strings.ReplaceAll(src, "\r\n", "\n")
	lines := strings.Split(src, "\n")

	var tokens []Token
	indentStack := []int{0}
	bracketDepth := 0
	inPipeCont := false
	pipeBaseIndent := 0

	emit := func(kind TokenKind, text string, intVal int64, line, col int) {
		tokens = append(tokens, Token{
			Kind: kind,
			Text: text,
			Int:  intVal,
			Span: ast.Span{File: file, Line: line, Col: col},
		})
	}

	// Precompute next non-empty, non-comment line lookup for |> continuation.
	isBlankOrComment := func(s string) bool {
		t := strings.TrimSpace(s)
		return t == "" || strings.HasPrefix(t, "#")
	}

	nextSigLine := func(from int) (int, int, string, bool) {
		for idx := from + 1; idx < len(lines); idx++ {
			raw := lines[idx]
			if isBlankOrComment(raw) {
				continue
			}
			ind := 0
			for i := 0; i < len(raw); i++ {
				if raw[i] == ' ' {
					ind++
				} else if raw[i] == '\t' {
					ind += 4
				} else {
					return idx, ind, strings.TrimLeft(raw, " \t"), true
				}
			}
		}
		return -1, 0, "", false
	}

	for lineIdx, rawLine := range lines {
		lineNo := lineIdx + 1
		if isBlankOrComment(rawLine) {
			continue
		}

		// Measure leading indentation.
		indent := 0
		pos := 0
		hasTab := false
		hasSpace := false
		for pos < len(rawLine) {
			if rawLine[pos] == ' ' {
				hasSpace = true
				indent++
				pos++
			} else if rawLine[pos] == '\t' {
				hasTab = true
				indent += 4
				pos++
			} else {
				break
			}
		}
		if hasTab && hasSpace {
			return nil, fmt.Errorf("%s:%d:1: mixed tabs and spaces in indentation", file, lineNo)
		}

		trimmed := rawLine[pos:]
		startsPipe := strings.HasPrefix(trimmed, "|>")

		if bracketDepth == 0 {
			if inPipeCont {
				if startsPipe && indent >= pipeBaseIndent {
					// Stay in multi-line pipe continuation without INDENT/DEDENT/NEWLINE.
				} else {
					// Pipe continuation ended; emit NEWLINE before evaluating indentation.
					inPipeCont = false
					lastLine := lineNo
					if len(tokens) > 0 {
						lastLine = tokens[len(tokens)-1].Span.Line
					}
					emit(TokNewline, "\n", 0, lastLine, 1)
					if err := adjustIndent(file, lineNo, indent, &indentStack, &tokens); err != nil {
						return nil, err
					}
				}
			} else {
				if err := adjustIndent(file, lineNo, indent, &indentStack, &tokens); err != nil {
					return nil, err
				}
			}
		}

		// Tokenize characters on this line starting from pos.
		lineTokensStart := len(tokens)
		i := pos
		for i < len(rawLine) {
			ch := rawLine[i]
			if ch == ' ' || ch == '\t' {
				i++
				continue
			}
			if ch == '#' {
				break
			}
			col := i + 1

			// f-string: f"..." or f'...'
			if ch == 'f' && i+1 < len(rawLine) && (rawLine[i+1] == '"' || rawLine[i+1] == '\'') {
				quote := rawLine[i+1]
				val, nextI, err := lexString(rawLine, i+1, quote, file, lineNo, col)
				if err != nil {
					return nil, err
				}
				emit(TokFStr, val, 0, lineNo, col)
				i = nextI
				continue
			}

			// Normal string literal
			if ch == '"' || ch == '\'' {
				val, nextI, err := lexString(rawLine, i, ch, file, lineNo, col)
				if err != nil {
					return nil, err
				}
				emit(TokStr, val, 0, lineNo, col)
				i = nextI
				continue
			}

			// Multi-char operators
			if i+1 < len(rawLine) {
				two := rawLine[i : i+2]
				switch two {
				case "==":
					emit(TokEq, two, 0, lineNo, col)
					i += 2
					continue
				case "!=":
					emit(TokNeq, two, 0, lineNo, col)
					i += 2
					continue
				case "<=":
					emit(TokLe, two, 0, lineNo, col)
					i += 2
					continue
				case "<<":
					emit(TokShl, two, 0, lineNo, col)
					i += 2
					continue
				case ">>":
					emit(TokShr, two, 0, lineNo, col)
					i += 2
					continue
				case ">=":
					emit(TokGe, two, 0, lineNo, col)
					i += 2
					continue
				case "+=":
					emit(TokPlusEq, two, 0, lineNo, col)
					i += 2
					continue
				case "-=":
					emit(TokMinusEq, two, 0, lineNo, col)
					i += 2
					continue
				case "*=":
					emit(TokStarEq, two, 0, lineNo, col)
					i += 2
					continue
				case "->":
					emit(TokArrow, two, 0, lineNo, col)
					i += 2
					continue
				case "=>":
					emit(TokFatArrow, two, 0, lineNo, col)
					i += 2
					continue
				case "|>":
					emit(TokPipe, two, 0, lineNo, col)
					i += 2
					continue
				case "..":
					emit(TokDotDot, two, 0, lineNo, col)
					i += 2
					continue
				}
			}

			// Single-char operators & brackets
			switch ch {
			case '+':
				emit(TokPlus, "+", 0, lineNo, col)
				i++
				continue
			case '-':
				emit(TokMinus, "-", 0, lineNo, col)
				i++
				continue
			case '*':
				emit(TokStar, "*", 0, lineNo, col)
				i++
				continue
			case '/':
				emit(TokSlash, "/", 0, lineNo, col)
				i++
				continue
			case '%':
				emit(TokPercent, "%", 0, lineNo, col)
				i++
				continue
			case '&':
				emit(TokAmp, "&", 0, lineNo, col)
				i++
				continue
			case '^':
				emit(TokCaret, "^", 0, lineNo, col)
				i++
				continue
			case '~':
				emit(TokTilde, "~", 0, lineNo, col)
				i++
				continue
			case '<':
				emit(TokLt, "<", 0, lineNo, col)
				i++
				continue
			case '>':
				emit(TokGt, ">", 0, lineNo, col)
				i++
				continue
			case '=':
				emit(TokAssign, "=", 0, lineNo, col)
				i++
				continue
			case '.':
				emit(TokDot, ".", 0, lineNo, col)
				i++
				continue
			case ',':
				emit(TokComma, ",", 0, lineNo, col)
				i++
				continue
			case ':':
				emit(TokColon, ":", 0, lineNo, col)
				i++
				continue
			case ';':
				emit(TokSemi, ";", 0, lineNo, col)
				i++
				continue
			case '?':
				emit(TokQuestion, "?", 0, lineNo, col)
				i++
				continue
			case '|':
				emit(TokBar, "|", 0, lineNo, col)
				i++
				continue
			case '(':
				bracketDepth++
				emit(TokLParen, "(", 0, lineNo, col)
				i++
				continue
			case ')':
				if bracketDepth > 0 {
					bracketDepth--
				}
				emit(TokRParen, ")", 0, lineNo, col)
				i++
				continue
			case '[':
				bracketDepth++
				emit(TokLBracket, "[", 0, lineNo, col)
				i++
				continue
			case ']':
				if bracketDepth > 0 {
					bracketDepth--
				}
				emit(TokRBracket, "]", 0, lineNo, col)
				i++
				continue
			case '{':
				bracketDepth++
				emit(TokLBrace, "{", 0, lineNo, col)
				i++
				continue
			case '}':
				if bracketDepth > 0 {
					bracketDepth--
				}
				emit(TokRBrace, "}", 0, lineNo, col)
				i++
				continue
			}

			// Integer literal (supports _ between digits, and 0x/0b prefixes)
			if ch >= '0' && ch <= '9' {
				j := i
				isHex := false
				isBin := false
				if ch == '0' && i+1 < len(rawLine) {
					if rawLine[i+1] == 'x' || rawLine[i+1] == 'X' {
						isHex = true
						j = i + 2
					} else if rawLine[i+1] == 'b' || rawLine[i+1] == 'B' {
						isBin = true
						j = i + 2
					}
				}
				isDigitChar := func(c byte) bool {
					if isHex {
						return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
					}
					if isBin {
						return c == '0' || c == '1'
					}
					return c >= '0' && c <= '9'
				}
				for j < len(rawLine) {
					c := rawLine[j]
					if isDigitChar(c) {
						j++
					} else if c == '_' && j+1 < len(rawLine) && isDigitChar(rawLine[j+1]) {
						j++
					} else {
						break
					}
				}
				rawNum := rawLine[i:j]
				clean := strings.ReplaceAll(rawNum, "_", "")
				val, err := strconv.ParseInt(clean, 0, 64)
				if err != nil {
					return nil, fmt.Errorf("%s:%d:%d: invalid integer literal %q: %v", file, lineNo, col, rawNum, err)
				}
				emit(TokInt, rawNum, val, lineNo, col)
				i = j
				continue
			}

			// Identifiers / Keywords
			r, size := utf8.DecodeRuneInString(rawLine[i:])
			if r == '_' || unicode.IsLetter(r) {
				j := i + size
				for j < len(rawLine) {
					r2, s2 := utf8.DecodeRuneInString(rawLine[j:])
					if r2 == '_' || unicode.IsLetter(r2) || unicode.IsDigit(r2) {
						j += s2
					} else {
						break
					}
				}
				word := rawLine[i:j]
				if kw, ok := keywords[word]; ok {
					emit(kw, word, 0, lineNo, col)
				} else {
					emit(TokIdent, word, 0, lineNo, col)
				}
				i = j
				continue
			}

			return nil, fmt.Errorf("%s:%d:%d: unexpected character %q", file, lineNo, col, string(r))
		}

		// End of physical line: decide whether to emit NEWLINE or enter pipe continuation.
		if bracketDepth == 0 && len(tokens) > lineTokensStart {
			lastTok := tokens[len(tokens)-1]
			if lastTok.Kind != TokColon {
				_, nextInd, nextTrim, ok := nextSigLine(lineIdx)
				curTop := indentStack[len(indentStack)-1]
				if ok && strings.HasPrefix(nextTrim, "|>") && nextInd >= curTop {
					if !inPipeCont {
						inPipeCont = true
						pipeBaseIndent = curTop
					}
					continue
				}
			}
			inPipeCont = false
			emit(TokNewline, "\n", 0, lineNo, len(rawLine)+1)
		}
	}

	if inPipeCont && len(tokens) > 0 && tokens[len(tokens)-1].Kind != TokNewline {
		emit(TokNewline, "\n", 0, tokens[len(tokens)-1].Span.Line, 1)
	}

	eofLine := len(lines)
	for len(indentStack) > 1 {
		indentStack = indentStack[:len(indentStack)-1]
		emit(TokDedent, "", 0, eofLine, 1)
	}
	emit(TokEOF, "", 0, eofLine, 1)
	return tokens, nil
}

func adjustIndent(file string, lineNo, indent int, stack *[]int, tokens *[]Token) error {
	top := (*stack)[len(*stack)-1]
	if indent > top {
		*stack = append(*stack, indent)
		*tokens = append(*tokens, Token{
			Kind: TokIndent,
			Span: ast.Span{File: file, Line: lineNo, Col: 1},
		})
		return nil
	}
	if indent < top {
		for len(*stack) > 1 && (*stack)[len(*stack)-1] > indent {
			*stack = (*stack)[:len(*stack)-1]
			*tokens = append(*tokens, Token{
				Kind: TokDedent,
				Span: ast.Span{File: file, Line: lineNo, Col: 1},
			})
		}
		if (*stack)[len(*stack)-1] != indent {
			return fmt.Errorf("%s:%d:1: inconsistent indentation level %d (expected %d)", file, lineNo, indent, (*stack)[len(*stack)-1])
		}
	}
	return nil
}

func lexString(line string, start int, quote byte, file string, lineNo, col int) (string, int, error) {
	var b strings.Builder
	i := start + 1
	for i < len(line) {
		ch := line[i]
		if ch == quote {
			return b.String(), i + 1, nil
		}
		if ch == '\\' {
			if i+1 >= len(line) {
				return "", 0, fmt.Errorf("%s:%d:%d: unterminated escape in string", file, lineNo, col)
			}
			esc := line[i+1]
			switch esc {
			case 'n':
				b.WriteByte('\n')
			case 't':
				b.WriteByte('\t')
			case 'r':
				b.WriteByte('\r')
			case '\\':
				b.WriteByte('\\')
			case '"':
				b.WriteByte('"')
			case '\'':
				b.WriteByte('\'')
			default:
				b.WriteByte(esc)
			}
			i += 2
			continue
		}
		b.WriteByte(ch)
		i++
	}
	return "", 0, fmt.Errorf("%s:%d:%d: unterminated string literal", file, lineNo, col)
}
