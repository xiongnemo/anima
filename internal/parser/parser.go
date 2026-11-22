package parser

import (
	"fmt"
	"slices"
	"strconv"
	"strings"

	"github.com/xiongnemo/anima/internal/ast"
	"github.com/xiongnemo/anima/internal/lexer"
)

// Parse lexes and parses an Anima source file into an AST Program.
func Parse(file, src string) (*ast.Program, error) {
	toks, err := lexer.Lex(file, src)
	if err != nil {
		return nil, err
	}
	p := &Parser{file: file, toks: toks}
	return p.parseProgram()
}

type Parser struct {
	file string
	toks []lexer.Token
	pos  int
}

func (p *Parser) cur() lexer.Token {
	if p.pos >= len(p.toks) {
		return p.toks[len(p.toks)-1]
	}
	return p.toks[p.pos]
}

func (p *Parser) peek(offset int) lexer.Token {
	idx := p.pos + offset
	if idx >= len(p.toks) {
		return p.toks[len(p.toks)-1]
	}
	if idx < 0 {
		return p.toks[0]
	}
	return p.toks[idx]
}

func (p *Parser) advance() lexer.Token {
	t := p.cur()
	if p.pos < len(p.toks)-1 {
		p.pos++
	}
	return t
}

func (p *Parser) at(k lexer.TokenKind) bool {
	return p.cur().Kind == k
}

func (p *Parser) atWord(w string) bool {
	return p.cur().Kind == lexer.TokIdent && p.cur().Text == w
}

func (p *Parser) matchWord(w string) bool {
	if p.atWord(w) {
		p.advance()
		return true
	}
	return false
}

func (p *Parser) match(k lexer.TokenKind) bool {
	if p.at(k) {
		p.advance()
		return true
	}
	return false
}

func (p *Parser) expect(k lexer.TokenKind) (lexer.Token, error) {
	if p.at(k) {
		return p.advance(), nil
	}
	return lexer.Token{}, p.errAt(p.cur(), "expected %s, got %s", k, p.cur())
}

func (p *Parser) expectIdent() (lexer.Token, error) {
	if p.at(lexer.TokIdent) {
		return p.advance(), nil
	}
	return lexer.Token{}, p.errAt(p.cur(), "expected identifier, got %s", p.cur())
}

func (p *Parser) errAt(t lexer.Token, format string, args ...any) error {
	msg := fmt.Sprintf(format, args...)
	return fmt.Errorf("%s: %s", t.Span, msg)
}

func (p *Parser) skipNewlines() {
	for p.at(lexer.TokNewline) {
		p.advance()
	}
}

func (p *Parser) expectEndOfLine() error {
	if p.at(lexer.TokNewline) {
		p.advance()
		p.skipNewlines()
		return nil
	}
	if p.at(lexer.TokEOF) || p.at(lexer.TokDedent) {
		return nil
	}
	return p.errAt(p.cur(), "expected end of line, got %s", p.cur())
}

// ---------------------------------------------------------------------------
// Program & Top-level Decls
// ---------------------------------------------------------------------------

func (p *Parser) parseProgram() (*ast.Program, error) {
	prog := &ast.Program{File: p.file}
	p.skipNewlines()
	for !p.at(lexer.TokEOF) {
		decl, err := p.parseTopDecl()
		if err != nil {
			return nil, err
		}
		prog.Decls = append(prog.Decls, decl)
		p.skipNewlines()
	}
	return prog, nil
}

func (p *Parser) parseTopDecl() (ast.Decl, error) {
	t := p.cur()
	switch {
	case t.Kind == lexer.TokImport:
		return p.parseImport()
	case t.Kind == lexer.TokDef:
		return p.parseFuncDecl()
	case p.atWord("type"):
		return p.parseTypeDecl()
	case p.atWord("entity"):
		return p.parseEntityDecl()
	case p.atWord("port"):
		return p.parsePortDecl()
	case p.atWord("monitor") || p.atWord("machine"):
		return p.parseMachineDecl()
	case p.atWord("property"):
		return p.parsePropertyDecl()
	case p.atWord("progress"):
		return p.parseProgressDecl()
	case p.atWord("workflow"):
		return p.parseWorkflowDecl()
	case p.atWord("system"):
		return p.parseSystemDecl()
	default:
		return nil, p.errAt(t, "unexpected top-level token %s", t)
	}
}

func (p *Parser) parseImport() (*ast.ImportDecl, error) {
	tok, _ := p.expect(lexer.TokImport)
	var path string
	if p.at(lexer.TokStr) {
		path = p.advance().Text
	} else {
		part, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		parts := []string{part.Text}
		for p.match(lexer.TokDot) {
			next, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			parts = append(parts, next.Text)
		}
		path = strings.Join(parts, ".")
	}
	alias := ""
	if p.match(lexer.TokAs) {
		al, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		alias = al.Text
	} else {
		if strings.Contains(path, ".") && !strings.HasSuffix(path, ".anm") {
			segs := strings.Split(path, ".")
			alias = segs[len(segs)-1]
		} else {
			base := strings.TrimSuffix(path, ".anm")
			if idx := strings.LastIndex(base, "/"); idx >= 0 {
				base = base[idx+1:]
			}
			alias = base
		}
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	return &ast.ImportDecl{Span: tok.Span, Path: path, Alias: alias}, nil
}

func (p *Parser) parseTypeParams() ([]string, error) {
	if !p.match(lexer.TokLBracket) {
		return nil, nil
	}
	var params []string
	for !p.at(lexer.TokRBracket) {
		id, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		params = append(params, id.Text)
		if !p.match(lexer.TokComma) {
			break
		}
	}
	if _, err := p.expect(lexer.TokRBracket); err != nil {
		return nil, err
	}
	return params, nil
}

func (p *Parser) parseTypeDecl() (*ast.TypeDecl, error) {
	kw := p.advance() // "type"
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	tparams, err := p.parseTypeParams()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokAssign); err != nil {
		return nil, err
	}

	decl := &ast.TypeDecl{Span: kw.Span, Name: nameTok.Text, TypeParams: tparams}

	multilineADT := false
	if p.at(lexer.TokNewline) && p.peek(1).Kind == lexer.TokIndent {
		p.advance()
		p.advance()
		multilineADT = true
	}

	// Distinguish ADT (Variant(f: T) | Variant2 or multi-line |) vs TypeAlias.
	if multilineADT || p.looksLikeADT() {
		decl.Kind = ast.TypeADT
		p.match(lexer.TokBar) // optional leading |
		for {
			p.skipNewlines()
			vname, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			var fields []ast.VariantField
			if p.match(lexer.TokLParen) {
				for !p.at(lexer.TokRParen) {
					fTok, err := p.expectIdent()
					if err != nil {
						return nil, err
					}
					if _, err := p.expect(lexer.TokColon); err != nil {
						return nil, err
					}
					fty, err := p.parseTypeExpr()
					if err != nil {
						return nil, err
					}
					fields = append(fields, ast.VariantField{Span: fTok.Span, Name: fTok.Text, Type: fty})
					if !p.match(lexer.TokComma) {
						break
					}
				}
				if _, err := p.expect(lexer.TokRParen); err != nil {
					return nil, err
				}
			}
			decl.Variants = append(decl.Variants, ast.VariantDecl{
				Span:   vname.Span,
				Name:   vname.Text,
				Fields: fields,
			})
			if multilineADT {
				p.skipNewlines()
				if p.match(lexer.TokBar) {
					continue
				}
				break
			}
			if !p.match(lexer.TokBar) {
				break
			}
		}
		if multilineADT {
			p.skipNewlines()
			if _, err := p.expect(lexer.TokDedent); err != nil {
				return nil, err
			}
		} else if err := p.expectEndOfLine(); err != nil {
			return nil, err
		}
		return decl, nil
	}

	ty, err := p.parseTypeExpr()
	if err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	decl.Kind = ast.TypeAlias
	decl.Alias = ty
	return decl, nil
}

func (p *Parser) looksLikeADT() bool {
	if p.at(lexer.TokBar) {
		return true
	}
	// Scan until NEWLINE/EOF at depth 0 for TokBar or Ident(name: Type)
	depth := 0
	for i := p.pos; i < len(p.toks); i++ {
		tk := p.toks[i]
		switch tk.Kind {
		case lexer.TokLParen, lexer.TokLBracket, lexer.TokLBrace:
			depth++
		case lexer.TokRParen, lexer.TokRBracket, lexer.TokRBrace:
			if depth > 0 {
				depth--
			}
		case lexer.TokNewline, lexer.TokEOF:
			return false
		case lexer.TokBar:
			if depth == 0 {
				return true
			}
		}
	}
	return false
}

func (p *Parser) parseTypeExpr() (ast.TypeExpr, error) {
	if p.atWord("fn") {
		kw := p.advance()
		if _, err := p.expect(lexer.TokLParen); err != nil {
			return nil, err
		}
		var params []ast.TypeExpr
		for !p.at(lexer.TokRParen) {
			pt, err := p.parseTypeExpr()
			if err != nil {
				return nil, err
			}
			params = append(params, pt)
			if !p.match(lexer.TokComma) {
				break
			}
		}
		if _, err := p.expect(lexer.TokRParen); err != nil {
			return nil, err
		}
		var ret ast.TypeExpr
		if p.match(lexer.TokArrow) {
			var err error
			ret, err = p.parseTypeExpr()
			if err != nil {
				return nil, err
			}
		}
		return &ast.FuncType{Span: kw.Span, Params: params, ReturnType: ret}, nil
	}

	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	fullName := nameTok.Text
	for p.match(lexer.TokDot) {
		part, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		fullName += "." + part.Text
	}

	if fullName == "int" && p.match(lexer.TokLBracket) {
		lo, err := p.parseSignedInt()
		if err != nil {
			return nil, err
		}
		if _, err := p.expect(lexer.TokDotDot); err != nil {
			return nil, err
		}
		hi, err := p.parseSignedInt()
		if err != nil {
			return nil, err
		}
		if _, err := p.expect(lexer.TokRBracket); err != nil {
			return nil, err
		}
		return &ast.IntRangeType{Span: nameTok.Span, Lo: lo, Hi: hi}, nil
	}

	if p.match(lexer.TokLBracket) {
		gt := &ast.GenericType{Span: nameTok.Span, Name: fullName, Cap: -1}
		for !p.at(lexer.TokRBracket) {
			if p.atWord("cap") && p.peek(1).Kind == lexer.TokAssign {
				p.advance()
				p.advance()
				capVal, err := p.parseSignedInt()
				if err != nil {
					return nil, err
				}
				gt.Cap = capVal
				gt.HasCap = true
			} else {
				arg, err := p.parseTypeExpr()
				if err != nil {
					return nil, err
				}
				gt.Args = append(gt.Args, arg)
			}
			if !p.match(lexer.TokComma) {
				break
			}
		}
		if _, err := p.expect(lexer.TokRBracket); err != nil {
			return nil, err
		}
		return gt, nil
	}

	return &ast.SimpleType{Span: nameTok.Span, Name: fullName}, nil
}

func (p *Parser) parseSignedInt() (int64, error) {
	neg := p.match(lexer.TokMinus)
	if p.at(lexer.TokInt) {
		v := p.advance().Int
		if neg {
			return -v, nil
		}
		return v, nil
	}
	if p.atWord("MAX") {
		p.advance()
		return 1_000_000_000, nil
	}
	return 0, p.errAt(p.cur(), "expected integer literal, got %s", p.cur())
}

// ---------------------------------------------------------------------------
// Entity, Port, Func
// ---------------------------------------------------------------------------

func (p *Parser) parseEntityDecl() (*ast.EntityDecl, error) {
	kw := p.advance()
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	ent := &ast.EntityDecl{Span: kw.Span, Name: nameTok.Text}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		if p.atWord("invariant") && p.peek(1).Kind == lexer.TokColon {
			p.advance()
			p.advance()
			inv, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			ent.Invariants = append(ent.Invariants, inv)
			continue
		}
		if p.atWord("rel") {
			relTok := p.advance()
			rname, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokArrow); err != nil {
				return nil, err
			}
			mult, err := p.parseMultiplicity()
			if err != nil {
				return nil, err
			}
			target, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			ent.Relations = append(ent.Relations, ast.RelationDecl{
				Span: relTok.Span, Name: rname.Text, Multiplicity: mult, Target: target.Text,
			})
			continue
		}
		fTok, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		if _, err := p.expect(lexer.TokColon); err != nil {
			return nil, err
		}
		fty, err := p.parseTypeExpr()
		if err != nil {
			return nil, err
		}
		if err := p.expectEndOfLine(); err != nil {
			return nil, err
		}
		ent.Fields = append(ent.Fields, ast.FieldDecl{Span: fTok.Span, Name: fTok.Text, Type: fty})
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return ent, nil
}

func (p *Parser) parseMultiplicity() (string, error) {
	first := ""
	switch {
	case p.at(lexer.TokInt):
		first = strconv.FormatInt(p.advance().Int, 10)
	case p.at(lexer.TokStar):
		p.advance()
		return "*", nil
	case p.at(lexer.TokIdent):
		first = p.advance().Text
	default:
		return "", p.errAt(p.cur(), "expected relation multiplicity, got %s", p.cur())
	}
	if p.match(lexer.TokDotDot) {
		second := ""
		switch {
		case p.at(lexer.TokInt):
			second = strconv.FormatInt(p.advance().Int, 10)
		case p.at(lexer.TokStar):
			p.advance()
			second = "*"
		case p.at(lexer.TokIdent):
			second = p.advance().Text
		default:
			return "", p.errAt(p.cur(), "expected upper multiplicity after ..")
		}
		return first + ".." + second, nil
	}
	return first, nil
}

func (p *Parser) parsePortDecl() (*ast.PortDecl, error) {
	kw := p.advance()
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	port := &ast.PortDecl{Span: kw.Span, Name: nameTok.Text}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		if p.atWord("protocol") {
			p.advance()
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokIndent); err != nil {
				return nil, err
			}
			for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
				p.skipNewlines()
				if p.at(lexer.TokDedent) {
					break
				}
				st, err := p.parseStateDecl()
				if err != nil {
					return nil, err
				}
				if port.InitState == "" {
					port.InitState = st.Name
				}
				port.States = append(port.States, st)
			}
			if _, err := p.expect(lexer.TokDedent); err != nil {
				return nil, err
			}
			continue
		}
		if p.atWord("extern") {
			p.advance()
			if _, err := p.expect(lexer.TokDef); err != nil {
				return nil, err
			}
			fnTok, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			params, err := p.parseParamList()
			if err != nil {
				return nil, err
			}
			var ret ast.TypeExpr
			if p.match(lexer.TokArrow) {
				ret, err = p.parseTypeExpr()
				if err != nil {
					return nil, err
				}
			}
			fromState, toState := "", ""
			if p.matchWord("from") {
				fs, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				fromState = fs.Text
				if _, err := p.expect(lexer.TokArrow); err != nil {
					return nil, err
				}
				ts, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				toState = ts.Text
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			port.Externs = append(port.Externs, ast.FuncSig{
				Span: fnTok.Span, Name: fnTok.Text, Params: params, ReturnType: ret,
				FromState: fromState, ToState: toState,
			})
			continue
		}
		return nil, p.errAt(p.cur(), "unexpected item in port %s: %s", port.Name, p.cur())
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return port, nil
}

// atOwn reports whether the parser is at the contextual keyword `own`, which
// is only a keyword when directly followed by a name (`own conn`).
func (p *Parser) atOwn() bool {
	return p.at(lexer.TokIdent) && p.cur().Text == "own" && p.peek(1).Kind == lexer.TokIdent
}

func (p *Parser) parseParamList() ([]ast.Param, error) {
	if _, err := p.expect(lexer.TokLParen); err != nil {
		return nil, err
	}
	var params []ast.Param
	for !p.at(lexer.TokRParen) {
		isMut := p.match(lexer.TokMut)
		isOwn := !isMut && p.atOwn()
		if isOwn {
			p.advance()
		}
		pTok, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		if _, err := p.expect(lexer.TokColon); err != nil {
			return nil, err
		}
		pty, err := p.parseTypeExpr()
		if err != nil {
			return nil, err
		}
		params = append(params, ast.Param{Span: pTok.Span, Mut: isMut, Own: isOwn, Name: pTok.Text, Type: pty})
		if !p.match(lexer.TokComma) {
			break
		}
	}
	if _, err := p.expect(lexer.TokRParen); err != nil {
		return nil, err
	}
	return params, nil
}

func (p *Parser) parseFuncDecl() (*ast.FuncDecl, error) {
	kw, _ := p.expect(lexer.TokDef)
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	tparams, err := p.parseTypeParams()
	if err != nil {
		return nil, err
	}
	params, err := p.parseParamList()
	if err != nil {
		return nil, err
	}
	var ret ast.TypeExpr
	if p.match(lexer.TokArrow) {
		ret, err = p.parseTypeExpr()
		if err != nil {
			return nil, err
		}
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}

	fn := &ast.FuncDecl{
		Span: kw.Span, Name: nameTok.Text, TypeParams: tparams, Params: params, ReturnType: ret,
	}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		if p.atWord("requires") && p.peek(1).Kind == lexer.TokColon {
			p.advance()
			p.advance()
			e, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			fn.Requires = append(fn.Requires, e)
			continue
		}
		if p.atWord("ensures") && p.peek(1).Kind == lexer.TokColon {
			p.advance()
			p.advance()
			e, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			fn.Ensures = append(fn.Ensures, e)
			continue
		}
		if p.atWord("decreases") && p.peek(1).Kind == lexer.TokColon {
			p.advance()
			p.advance()
			e, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			fn.Decreases = e
			continue
		}
		st, err := p.parseStmt()
		if err != nil {
			return nil, err
		}
		fn.Body = append(fn.Body, st)
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return fn, nil
}

// ---------------------------------------------------------------------------
// Machine / Monitor, Property, Progress
// ---------------------------------------------------------------------------

func (p *Parser) parseMachineDecl() (*ast.MachineDecl, error) {
	kw := p.advance()
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	m := &ast.MachineDecl{Span: kw.Span, Kind: kw.Text, Name: nameTok.Text}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		if p.atWord("state") {
			st, err := p.parseStateDecl()
			if err != nil {
				return nil, err
			}
			m.States = append(m.States, st)
			continue
		}
		// Control variable: writers: control int[0..1] = 0
		cvTok, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		if _, err := p.expect(lexer.TokColon); err != nil {
			return nil, err
		}
		p.matchWord("control")
		ty, err := p.parseTypeExpr()
		if err != nil {
			return nil, err
		}
		var initExpr ast.Expr
		if p.match(lexer.TokAssign) {
			initExpr, err = p.parseExpr()
			if err != nil {
				return nil, err
			}
		}
		if err := p.expectEndOfLine(); err != nil {
			return nil, err
		}
		m.ControlVars = append(m.ControlVars, ast.ControlVarDecl{
			Span: cvTok.Span, Name: cvTok.Text, Type: ty, Init: initExpr,
		})
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return m, nil
}

func (p *Parser) parseStateDecl() (ast.StateDecl, error) {
	kw := p.advance() // "state"
	if kw.Kind != lexer.TokIdent || kw.Text != "state" {
		return ast.StateDecl{}, p.errAt(kw, "expected 'state', got %s", kw)
	}
	nameTok, err := p.expectIdent()
	if err != nil {
		return ast.StateDecl{}, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return ast.StateDecl{}, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return ast.StateDecl{}, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return ast.StateDecl{}, err
	}
	st := ast.StateDecl{Span: kw.Span, Name: nameTok.Text}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		if p.atWord("invariant") && p.peek(1).Kind == lexer.TokColon {
			p.advance()
			p.advance()
			inv, err := p.parseExpr()
			if err != nil {
				return ast.StateDecl{}, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return ast.StateDecl{}, err
			}
			st.Invariants = append(st.Invariants, inv)
			continue
		}
		if p.atWord("on") {
			trTok := p.advance()
			actName, err := p.parseActionName()
			if err != nil {
				return ast.StateDecl{}, err
			}
			var guard ast.Expr
			if p.matchWord("when") {
				guard, err = p.parseExpr()
				if err != nil {
					return ast.StateDecl{}, err
				}
			}
			if _, err := p.expect(lexer.TokArrow); err != nil {
				return ast.StateDecl{}, err
			}
			targetTok, err := p.expectIdent()
			if err != nil {
				return ast.StateDecl{}, err
			}
			var body []ast.Stmt
			if p.match(lexer.TokColon) {
				if err := p.expectEndOfLine(); err != nil {
					return ast.StateDecl{}, err
				}
				body, err = p.parseBlock()
				if err != nil {
					return ast.StateDecl{}, err
				}
			} else {
				if err := p.expectEndOfLine(); err != nil {
					return ast.StateDecl{}, err
				}
			}
			st.Transitions = append(st.Transitions, ast.TransitionDecl{
				Span: trTok.Span, Action: actName, Guard: guard, TargetState: targetTok.Text, Body: body,
			})
			continue
		}
		return ast.StateDecl{}, p.errAt(p.cur(), "unexpected token inside state %s: %s", st.Name, p.cur())
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return ast.StateDecl{}, err
	}
	return st, nil
}

func (p *Parser) parsePropertyDecl() (*ast.PropertyDecl, error) {
	kw := p.advance()
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	prop := &ast.PropertyDecl{Span: kw.Span, Name: nameTok.Text}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		st, err := p.parseStateDecl()
		if err != nil {
			return nil, err
		}
		prop.States = append(prop.States, st)
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return prop, nil
}

func (p *Parser) parseProgressDecl() (*ast.ProgressDecl, error) {
	kw := p.advance()
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokAssign); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokLBrace); err != nil {
		return nil, err
	}
	var acts []string
	for !p.at(lexer.TokRBrace) {
		a, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		name := a.Text
		for p.match(lexer.TokDot) {
			sub, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			name += "." + sub.Text
		}
		acts = append(acts, name)
		if !p.match(lexer.TokComma) {
			break
		}
	}
	if _, err := p.expect(lexer.TokRBrace); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	return &ast.ProgressDecl{Span: kw.Span, Name: nameTok.Text, Actions: acts}, nil
}

// ---------------------------------------------------------------------------
// Workflow (Petri / WF-Net)
// ---------------------------------------------------------------------------

func (p *Parser) parseWorkflowDecl() (*ast.WorkflowDecl, error) {
	kw := p.advance()
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	var params []ast.Param
	if p.at(lexer.TokLParen) {
		params, err = p.parseParamList()
		if err != nil {
			return nil, err
		}
	}
	var ret ast.TypeExpr
	if p.match(lexer.TokArrow) {
		ret, err = p.parseTypeExpr()
		if err != nil {
			return nil, err
		}
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	wf := &ast.WorkflowDecl{Span: kw.Span, Name: nameTok.Text, Params: params, ReturnType: ret}

	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		switch {
		case p.atWord("verify") && p.peek(1).Kind == lexer.TokColon:
			p.advance()
			p.advance()
			for {
				if p.at(lexer.TokInt) && p.peek(1).Kind == lexer.TokIdent {
					num := p.advance().Text
					suf := p.advance().Text
					wf.VerifyFlags = append(wf.VerifyFlags, num+suf)
				} else {
					f, err := p.expectIdent()
					if err != nil {
						return nil, err
					}
					wf.VerifyFlags = append(wf.VerifyFlags, f.Text)
				}
				if !p.match(lexer.TokComma) {
					break
				}
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
		case p.atWord("pool"):
			ptok := p.advance()
			pname, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			var pty ast.TypeExpr
			var capVal int64
			if p.atWord("capacity") {
				p.advance()
				if _, err := p.expect(lexer.TokAssign); err != nil {
					return nil, err
				}
				capVal, err = p.parseSignedInt()
				if err != nil {
					return nil, err
				}
				pty = &ast.IntRangeType{Span: ptok.Span, Lo: 0, Hi: capVal}
			} else {
				pty, err = p.parseTypeExpr()
				if err != nil {
					return nil, err
				}
				if _, err := p.expect(lexer.TokAssign); err != nil {
					return nil, err
				}
				capVal, err = p.parseSignedInt()
				if err != nil {
					return nil, err
				}
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			wf.Pools = append(wf.Pools, ast.PoolDecl{
				Span: ptok.Span, Name: pname.Text, Type: pty, Capacity: capVal,
			})
		case p.atWord("start"):
			stok := p.advance()
			if _, err := p.expect(lexer.TokArrow); err != nil {
				return nil, err
			}
			targ, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			var body []ast.Stmt
			if p.match(lexer.TokColon) {
				if err := p.expectEndOfLine(); err != nil {
					return nil, err
				}
				body, err = p.parseBlock()
				if err != nil {
					return nil, err
				}
			} else if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			wf.Nodes = append(wf.Nodes, &ast.StartNode{Span: stok.Span, Target: targ.Text, Body: body})
		case p.atWord("step"):
			stok := p.advance()
			sname, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			after := ""
			if p.matchWord("after") {
				af, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				after = af.Text
			}
			target := ""
			if p.match(lexer.TokArrow) {
				tg, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				target = tg.Text
			}
			var body []ast.Stmt
			if p.match(lexer.TokColon) {
				if err := p.expectEndOfLine(); err != nil {
					return nil, err
				}
				body, err = p.parseBlock()
				if err != nil {
					return nil, err
				}
			} else if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			wf.Nodes = append(wf.Nodes, &ast.StepNode{
				Span: stok.Span, Name: sname.Text, After: after, Target: target, Body: body,
			})
		case p.atWord("choice"):
			ctok := p.advance()
			cname := ""
			if p.at(lexer.TokIdent) && !p.atWord("after") {
				cname = p.advance().Text
			}
			after := ""
			if p.matchWord("after") {
				af, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				after = af.Text
			}
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokIndent); err != nil {
				return nil, err
			}
			cn := &ast.ChoiceNode{Span: ctok.Span, Name: cname, After: after}
			for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
				p.skipNewlines()
				if p.at(lexer.TokDedent) {
					break
				}
				btok := p.cur()
				var guard ast.Expr
				isElse := false
				if p.match(lexer.TokElse) {
					isElse = true
				} else if p.matchWord("when") {
					guard, err = p.parseExpr()
					if err != nil {
						return nil, err
					}
				} else {
					return nil, p.errAt(btok, "expected 'when' or 'else' in choice")
				}
				if _, err := p.expect(lexer.TokArrow); err != nil {
					return nil, err
				}
				tg, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				if err := p.expectEndOfLine(); err != nil {
					return nil, err
				}
				cn.Branches = append(cn.Branches, ast.ChoiceBranch{
					Span: btok.Span, Guard: guard, IsElse: isElse, Target: tg.Text,
				})
			}
			if _, err := p.expect(lexer.TokDedent); err != nil {
				return nil, err
			}
			wf.Nodes = append(wf.Nodes, cn)
		case p.atWord("merge"):
			mtok := p.advance()
			mname, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			var afters []string
			if p.matchWord("after") {
				for {
					af, err := p.expectIdent()
					if err != nil {
						return nil, err
					}
					afters = append(afters, af.Text)
					if !p.match(lexer.TokComma) {
						break
					}
				}
			}
			target := ""
			if p.match(lexer.TokArrow) {
				tg, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				target = tg.Text
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			wf.Nodes = append(wf.Nodes, &ast.MergeNode{
				Span: mtok.Span, Name: mname.Text, Afters: afters, Target: target,
			})
		case p.atWord("fork"):
			ftok := p.advance()
			fname, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			after := ""
			if p.matchWord("after") {
				af, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				after = af.Text
			}
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokIndent); err != nil {
				return nil, err
			}
			fn := &ast.ForkNode{Span: ftok.Span, Name: fname.Text, After: after}
			for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
				p.skipNewlines()
				if p.at(lexer.TokDedent) {
					break
				}
				btok := p.cur()
				if !p.matchWord("branch") {
					return nil, p.errAt(btok, "expected 'branch' inside fork")
				}
				bname, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				if _, err := p.expect(lexer.TokColon); err != nil {
					return nil, err
				}
				if err := p.expectEndOfLine(); err != nil {
					return nil, err
				}
				if _, err := p.expect(lexer.TokIndent); err != nil {
					return nil, err
				}
				fb := ast.ForkBranch{Span: btok.Span, Name: bname.Text}
				for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
					p.skipNewlines()
					if p.at(lexer.TokDedent) {
						break
					}
					op, err := p.parseBranchOp()
					if err != nil {
						return nil, err
					}
					fb.Ops = append(fb.Ops, op)
				}
				if _, err := p.expect(lexer.TokDedent); err != nil {
					return nil, err
				}
				fn.Branches = append(fn.Branches, fb)
			}
			if _, err := p.expect(lexer.TokDedent); err != nil {
				return nil, err
			}
			wf.Nodes = append(wf.Nodes, fn)
		case p.atWord("join"):
			jtok := p.advance()
			jname, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			target := ""
			if p.match(lexer.TokArrow) {
				tg, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				target = tg.Text
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			wf.Nodes = append(wf.Nodes, &ast.JoinNode{Span: jtok.Span, Name: jname.Text, Target: target})
		default:
			return nil, p.errAt(p.cur(), "unexpected workflow element: %s", p.cur())
		}
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return wf, nil
}

func (p *Parser) parseBranchOp() (ast.BranchOp, error) {
	t := p.cur()
	switch {
	case p.matchWord("sync"):
		id, err := p.expectIdent()
		if err != nil {
			return ast.BranchOp{}, err
		}
		target := id.Text
		for p.match(lexer.TokDot) {
			sub, err := p.expectIdent()
			if err != nil {
				return ast.BranchOp{}, err
			}
			target += "." + sub.Text
		}
		if err := p.expectEndOfLine(); err != nil {
			return ast.BranchOp{}, err
		}
		return ast.BranchOp{Span: t.Span, Kind: ast.BranchSync, Target: target}, nil
	case p.matchWord("acquire"):
		id, err := p.expectIdent()
		if err != nil {
			return ast.BranchOp{}, err
		}
		if err := p.expectEndOfLine(); err != nil {
			return ast.BranchOp{}, err
		}
		return ast.BranchOp{Span: t.Span, Kind: ast.BranchAcquire, Target: id.Text}, nil
	case p.matchWord("release"):
		id, err := p.expectIdent()
		if err != nil {
			return ast.BranchOp{}, err
		}
		if err := p.expectEndOfLine(); err != nil {
			return ast.BranchOp{}, err
		}
		return ast.BranchOp{Span: t.Span, Kind: ast.BranchRelease, Target: id.Text}, nil
	case p.matchWord("step"):
		id, err := p.expectIdent()
		if err != nil {
			return ast.BranchOp{}, err
		}
		if err := p.expectEndOfLine(); err != nil {
			return ast.BranchOp{}, err
		}
		return ast.BranchOp{Span: t.Span, Kind: ast.BranchStepRef, Target: id.Text}, nil
	case p.matchWord("call"):
		st, err := p.parseStmt()
		if err != nil {
			return ast.BranchOp{}, err
		}
		return ast.BranchOp{Span: t.Span, Kind: ast.BranchStmt, Stmt: st}, nil
	default:
		st, err := p.parseStmt()
		if err != nil {
			return ast.BranchOp{}, err
		}
		return ast.BranchOp{Span: t.Span, Kind: ast.BranchStmt, Stmt: st}, nil
	}
}

// ---------------------------------------------------------------------------
// System
// ---------------------------------------------------------------------------

func (p *Parser) parseSystemDecl() (*ast.SystemDecl, error) {
	kw := p.advance()
	nameTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	sys := &ast.SystemDecl{Span: kw.Span, Name: nameTok.Text}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		switch {
		case p.matchWord("compose"):
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokIndent); err != nil {
				return nil, err
			}
			for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
				p.skipNewlines()
				if p.at(lexer.TokDedent) {
					break
				}
				iname, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				if _, err := p.expect(lexer.TokColon); err != nil {
					return nil, err
				}
				tname, err := p.expectIdent()
				if err != nil {
					return nil, err
				}
				inst := ast.InstanceDecl{
					Span: iname.Span, Name: iname.Text, TypeName: tname.Text,
					Bindings: map[string]string{},
				}
				if p.match(lexer.TokLParen) {
					for !p.at(lexer.TokRParen) {
						k, err := p.expectIdent()
						if err != nil {
							return nil, err
						}
						if _, err := p.expect(lexer.TokAssign); err != nil {
							return nil, err
						}
						v, err := p.expectIdent()
						if err != nil {
							return nil, err
						}
						inst.Bindings[k.Text] = v.Text
						if !p.match(lexer.TokComma) {
							break
						}
					}
					if _, err := p.expect(lexer.TokRParen); err != nil {
						return nil, err
					}
				}
				if p.match(lexer.TokSlash) {
					if _, err := p.expect(lexer.TokLBrace); err != nil {
						return nil, err
					}
					for !p.at(lexer.TokRBrace) {
						fromName, err := p.parseActionName()
						if err != nil {
							return nil, err
						}
						if _, err := p.expect(lexer.TokArrow); err != nil {
							return nil, err
						}
						toName, err := p.parseActionName()
						if err != nil {
							return nil, err
						}
						inst.Relabels = append(inst.Relabels, ast.RelabelRule{
							Span: iname.Span, From: fromName, To: toName,
						})
						if !p.match(lexer.TokComma) {
							break
						}
					}
					if _, err := p.expect(lexer.TokRBrace); err != nil {
						return nil, err
					}
				}
				if err := p.expectEndOfLine(); err != nil {
					return nil, err
				}
				sys.Instances = append(sys.Instances, inst)
			}
			if _, err := p.expect(lexer.TokDedent); err != nil {
				return nil, err
			}
		case p.matchWord("hide"):
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			acts, err := p.parseActionSet()
			if err != nil {
				return nil, err
			}
			sys.Hide = append(sys.Hide, acts...)
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
		case p.matchWord("priority_low"):
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			acts, err := p.parseActionSet()
			if err != nil {
				return nil, err
			}
			sys.PriorityLow = append(sys.PriorityLow, acts...)
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
		case p.matchWord("check"):
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokIndent); err != nil {
				return nil, err
			}
			for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
				p.skipNewlines()
				if p.at(lexer.TokDedent) {
					break
				}
				chk, err := p.parseSystemCheck()
				if err != nil {
					return nil, err
				}
				sys.Checks = append(sys.Checks, chk)
			}
			if _, err := p.expect(lexer.TokDedent); err != nil {
				return nil, err
			}
		default:
			return nil, p.errAt(p.cur(), "unexpected token in system %s: %s", sys.Name, p.cur())
		}
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return sys, nil
}

func (p *Parser) parseActionName() (string, error) {
	first, err := p.expectIdent()
	if err != nil {
		return "", err
	}
	name := first.Text
	for p.match(lexer.TokDot) {
		sub, err := p.expectIdent()
		if err != nil {
			return "", err
		}
		name += "." + sub.Text
	}
	return name, nil
}

func (p *Parser) parseActionSet() ([]string, error) {
	openTok := lexer.TokLBracket
	closeTok := lexer.TokRBracket
	if p.at(lexer.TokLBrace) {
		openTok = lexer.TokLBrace
		closeTok = lexer.TokRBrace
	}
	if _, err := p.expect(openTok); err != nil {
		return nil, err
	}
	var out []string
	for !p.at(closeTok) {
		a, err := p.parseActionName()
		if err != nil {
			return nil, err
		}
		out = append(out, a)
		if !p.match(lexer.TokComma) {
			break
		}
	}
	if _, err := p.expect(closeTok); err != nil {
		return nil, err
	}
	return out, nil
}

func (p *Parser) parseSystemCheck() (ast.SystemCheck, error) {
	t := p.cur()
	if p.matchWord("deadlock_free") {
		if err := p.expectEndOfLine(); err != nil {
			return ast.SystemCheck{}, err
		}
		return ast.SystemCheck{Span: t.Span, Kind: ast.CheckDeadlockFree, RawText: "deadlock_free"}, nil
	}
	if p.matchWord("satisfies") {
		target, err := p.expectIdent()
		if err != nil {
			return ast.SystemCheck{}, err
		}
		if err := p.expectEndOfLine(); err != nil {
			return ast.SystemCheck{}, err
		}
		return ast.SystemCheck{
			Span: t.Span, Kind: ast.CheckSatisfies, Target: target.Text, RawText: "satisfies " + target.Text,
		}, nil
	}
	if p.matchWord("ltl") {
		if _, err := p.expect(lexer.TokColon); err != nil {
			return ast.SystemCheck{}, err
		}
		if p.matchWord("always") {
			if p.match(lexer.TokLParen) {
				trig, err := p.parseActionName()
				if err != nil {
					return ast.SystemCheck{}, err
				}
				if _, err := p.expect(lexer.TokArrow); err != nil {
					return ast.SystemCheck{}, err
				}
				if !p.matchWord("eventually") {
					return ast.SystemCheck{}, p.errAt(p.cur(), "expected 'eventually' in LTL response formula")
				}
				resp, err := p.parseActionName()
				if err != nil {
					return ast.SystemCheck{}, err
				}
				if _, err := p.expect(lexer.TokRParen); err != nil {
					return ast.SystemCheck{}, err
				}
				if err := p.expectEndOfLine(); err != nil {
					return ast.SystemCheck{}, err
				}
				return ast.SystemCheck{
					Span:    t.Span,
					Kind:    ast.CheckLTL,
					RawText: fmt.Sprintf("always (%s -> eventually %s)", trig, resp),
					LTL:     &ast.LTLAlwaysEventually{Trigger: trig, Response: resp},
				}, nil
			}
			act, err := p.parseActionName()
			if err != nil {
				return ast.SystemCheck{}, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return ast.SystemCheck{}, err
			}
			return ast.SystemCheck{
				Span: t.Span, Kind: ast.CheckLTL, RawText: "always " + act, LTL: &ast.LTLAlways{Action: act},
			}, nil
		}
		if p.matchWord("never") {
			act, err := p.parseActionName()
			if err != nil {
				return ast.SystemCheck{}, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return ast.SystemCheck{}, err
			}
			return ast.SystemCheck{
				Span: t.Span, Kind: ast.CheckLTL, RawText: "never " + act, LTL: &ast.LTLNever{Action: act},
			}, nil
		}
		return ast.SystemCheck{}, p.errAt(p.cur(), "unsupported LTL form near %s", p.cur())
	}
	return ast.SystemCheck{}, p.errAt(t, "unknown check directive %s", t)
}

// ---------------------------------------------------------------------------
// Statements & Blocks
// ---------------------------------------------------------------------------

func (p *Parser) parseBlock() ([]ast.Stmt, error) {
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	var stmts []ast.Stmt
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		st, err := p.parseStmt()
		if err != nil {
			return nil, err
		}
		stmts = append(stmts, st)
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return stmts, nil
}

func (p *Parser) parseStmt() (ast.Stmt, error) {
	t := p.cur()
	switch t.Kind {
	case lexer.TokIf:
		return p.parseIfStmt()
	case lexer.TokMatch:
		return p.parseMatchStmt()
	case lexer.TokFor:
		return p.parseForStmt()
	case lexer.TokWhile:
		return p.parseWhileStmt()
	case lexer.TokReturn:
		p.advance()
		if p.at(lexer.TokNewline) || p.at(lexer.TokDedent) || p.at(lexer.TokEOF) {
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			return &ast.ReturnStmt{Span: t.Span}, nil
		}
		var val ast.Expr
		var err error
		isBlockMatch := false
		if p.at(lexer.TokMatch) {
			val, err = p.parseMatchExpr()
			isBlockMatch = true
		} else {
			val, err = p.parseExpr()
		}
		if err != nil {
			return nil, err
		}
		if !isBlockMatch {
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
		}
		return &ast.ReturnStmt{Span: t.Span, Value: val}, nil
	}

	// Typed local declaration: `x: Type = expr`
	if t.Kind == lexer.TokIdent && p.peek(1).Kind == lexer.TokColon {
		nameTok := p.advance()
		p.advance() // :
		ty, err := p.parseTypeExpr()
		if err != nil {
			return nil, err
		}
		if _, err := p.expect(lexer.TokAssign); err != nil {
			return nil, err
		}
		var rhs ast.Expr
		isBlockMatch := false
		if p.at(lexer.TokMatch) {
			rhs, err = p.parseMatchExpr()
			isBlockMatch = true
		} else {
			rhs, err = p.parseExpr()
		}
		if err != nil {
			return nil, err
		}
		if !isBlockMatch {
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
		}
		return &ast.LetAssignStmt{Span: t.Span, Name: nameTok.Text, TypeAnno: ty, Value: rhs}, nil
	}

	// Parse LHS / Expr
	lhs, err := p.parseExpr()
	if err != nil {
		return nil, err
	}

	switch p.cur().Kind {
	case lexer.TokAssign:
		p.advance()
		var rhs ast.Expr
		isBlockMatch := false
		if p.at(lexer.TokMatch) {
			rhs, err = p.parseMatchExpr()
			isBlockMatch = true
		} else {
			rhs, err = p.parseExpr()
		}
		if err != nil {
			return nil, err
		}
		if !isBlockMatch {
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
		}
		switch target := lhs.(type) {
		case *ast.Ident:
			return &ast.LetAssignStmt{Span: t.Span, Name: target.Name, Value: rhs}, nil
		case *ast.FieldExpr:
			return &ast.FieldAssignStmt{Span: t.Span, Object: target.Object, Field: target.Field, Value: rhs}, nil
		case *ast.IndexExpr:
			return &ast.IndexAssignStmt{Span: t.Span, List: target.List, Index: target.Index, Value: rhs}, nil
		default:
			return nil, p.errAt(t, "invalid assignment target")
		}
	case lexer.TokPlusEq, lexer.TokMinusEq, lexer.TokStarEq:
		op := p.advance().Text
		rhs, err := p.parseExpr()
		if err != nil {
			return nil, err
		}
		if err := p.expectEndOfLine(); err != nil {
			return nil, err
		}
		return &ast.CompoundAssignStmt{Span: t.Span, Target: lhs, Op: op, Value: rhs}, nil
	default:
		if err := p.expectEndOfLine(); err != nil {
			return nil, err
		}
		return &ast.ExprStmt{Span: t.Span, Expr: lhs}, nil
	}
}

func (p *Parser) parseIfStmt() (*ast.IfStmt, error) {
	kw, _ := p.expect(lexer.TokIf)
	cond, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	body, err := p.parseBlock()
	if err != nil {
		return nil, err
	}
	stmt := &ast.IfStmt{
		Span:     kw.Span,
		Branches: []ast.IfBranch{{Span: kw.Span, Cond: cond, Body: body}},
	}
	for {
		p.skipNewlines()
		if p.at(lexer.TokElif) {
			et := p.advance()
			ec, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			eb, err := p.parseBlock()
			if err != nil {
				return nil, err
			}
			stmt.Branches = append(stmt.Branches, ast.IfBranch{Span: et.Span, Cond: ec, Body: eb})
		} else {
			break
		}
	}
	p.skipNewlines()
	if p.match(lexer.TokElse) {
		if _, err := p.expect(lexer.TokColon); err != nil {
			return nil, err
		}
		if err := p.expectEndOfLine(); err != nil {
			return nil, err
		}
		eb, err := p.parseBlock()
		if err != nil {
			return nil, err
		}
		stmt.Else = eb
	}
	return stmt, nil
}

func (p *Parser) parseMatchStmt() (*ast.MatchStmt, error) {
	kw, _ := p.expect(lexer.TokMatch)
	subj, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	ms := &ast.MatchStmt{Span: kw.Span, Subject: subj}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		armSpan := p.cur().Span
		pat, err := p.parsePattern()
		if err != nil {
			return nil, err
		}
		var guard ast.Expr
		if p.match(lexer.TokIf) {
			guard, err = p.parseExpr()
			if err != nil {
				return nil, err
			}
		}
		if _, err := p.expect(lexer.TokArrow); err != nil {
			return nil, err
		}
		var body []ast.Stmt
		if p.at(lexer.TokNewline) {
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			body, err = p.parseBlock()
			if err != nil {
				return nil, err
			}
		} else {
			st, err := p.parseStmt()
			if err != nil {
				return nil, err
			}
			body = []ast.Stmt{st}
		}
		ms.Arms = append(ms.Arms, ast.MatchArm{Span: armSpan, Pattern: pat, Guard: guard, Body: body})
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return ms, nil
}

func (p *Parser) parseMatchExpr() (*ast.MatchExpr, error) {
	kw, _ := p.expect(lexer.TokMatch)
	subj, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	me := &ast.MatchExpr{Span: kw.Span, Subject: subj}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		armSpan := p.cur().Span
		pat, err := p.parsePattern()
		if err != nil {
			return nil, err
		}
		var guard ast.Expr
		if p.match(lexer.TokIf) {
			guard, err = p.parseExpr()
			if err != nil {
				return nil, err
			}
		}
		if _, err := p.expect(lexer.TokArrow); err != nil {
			return nil, err
		}
		val, err := p.parseExpr()
		if err != nil {
			return nil, err
		}
		if err := p.expectEndOfLine(); err != nil {
			return nil, err
		}
		me.Arms = append(me.Arms, ast.MatchExprArm{Span: armSpan, Pattern: pat, Guard: guard, Value: val})
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return me, nil
}

func (p *Parser) parsePattern() (ast.Pattern, error) {
	t := p.cur()
	switch t.Kind {
	case lexer.TokTrue:
		p.advance()
		return &ast.BoolPat{Span: t.Span, Value: true}, nil
	case lexer.TokFalse:
		p.advance()
		return &ast.BoolPat{Span: t.Span, Value: false}, nil
	case lexer.TokStr:
		p.advance()
		return &ast.StrPat{Span: t.Span, Value: t.Text}, nil
	case lexer.TokMinus, lexer.TokInt:
		lo, err := p.parseSignedInt()
		if err != nil {
			return nil, err
		}
		if p.match(lexer.TokDotDot) {
			hi, err := p.parseSignedInt()
			if err != nil {
				return nil, err
			}
			return &ast.RangePat{Span: t.Span, Lo: lo, Hi: hi}, nil
		}
		return &ast.IntPat{Span: t.Span, Value: lo}, nil
	case lexer.TokIdent:
		if t.Text == "_" {
			p.advance()
			return &ast.WildcardPat{Span: t.Span}, nil
		}
		name := p.advance().Text
		if p.match(lexer.TokLParen) {
			var sub []ast.Pattern
			for !p.at(lexer.TokRParen) {
				sp, err := p.parsePattern()
				if err != nil {
					return nil, err
				}
				sub = append(sub, sp)
				if !p.match(lexer.TokComma) {
					break
				}
			}
			if _, err := p.expect(lexer.TokRParen); err != nil {
				return nil, err
			}
			return &ast.VariantPat{Span: t.Span, Name: name, Fields: sub}, nil
		}
		// Uppercase bare identifier (like Degraded or None) -> VariantPat with 0 fields
		if len(name) > 0 && name[0] >= 'A' && name[0] <= 'Z' {
			return &ast.VariantPat{Span: t.Span, Name: name}, nil
		}
		return &ast.VarPat{Span: t.Span, Name: name}, nil
	case lexer.TokNone:
		p.advance()
		return &ast.VariantPat{Span: t.Span, Name: "None"}, nil
	default:
		return nil, p.errAt(t, "expected pattern, got %s", t)
	}
}

func (p *Parser) parseForStmt() (*ast.ForStmt, error) {
	kw, _ := p.expect(lexer.TokFor)
	vTok, err := p.expectIdent()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIn); err != nil {
		return nil, err
	}
	iter, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	body, err := p.parseBlock()
	if err != nil {
		return nil, err
	}
	return &ast.ForStmt{Span: kw.Span, Var: vTok.Text, Iterable: iter, Body: body}, nil
}

func (p *Parser) parseWhileStmt() (*ast.WhileStmt, error) {
	kw, _ := p.expect(lexer.TokWhile)
	cond, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokColon); err != nil {
		return nil, err
	}
	if err := p.expectEndOfLine(); err != nil {
		return nil, err
	}
	if _, err := p.expect(lexer.TokIndent); err != nil {
		return nil, err
	}
	ws := &ast.WhileStmt{Span: kw.Span, Cond: cond}
	for !p.at(lexer.TokDedent) && !p.at(lexer.TokEOF) {
		p.skipNewlines()
		if p.at(lexer.TokDedent) {
			break
		}
		if p.atWord("invariant") && p.peek(1).Kind == lexer.TokColon {
			p.advance()
			p.advance()
			inv, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			ws.Invariants = append(ws.Invariants, inv)
			continue
		}
		if p.atWord("decreases") && p.peek(1).Kind == lexer.TokColon {
			p.advance()
			p.advance()
			dec, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if err := p.expectEndOfLine(); err != nil {
				return nil, err
			}
			ws.Decreases = dec
			continue
		}
		st, err := p.parseStmt()
		if err != nil {
			return nil, err
		}
		ws.Body = append(ws.Body, st)
	}
	if _, err := p.expect(lexer.TokDedent); err != nil {
		return nil, err
	}
	return ws, nil
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

func (p *Parser) parseExpr() (ast.Expr, error) {
	return p.parsePipe()
}

func (p *Parser) parsePipe() (ast.Expr, error) {
	left, err := p.parseLambda()
	if err != nil {
		return nil, err
	}
	for p.at(lexer.TokPipe) {
		tok := p.advance()
		right, err := p.parseLambda()
		if err != nil {
			return nil, err
		}
		left = &ast.PipeExpr{Span: tok.Span, Left: left, Right: right}
	}
	return left, nil
}

func (p *Parser) parseLambda() (ast.Expr, error) {
	t := p.cur()
	if t.Kind == lexer.TokIdent && p.peek(1).Kind == lexer.TokFatArrow {
		param := p.advance().Text
		p.advance() // =>
		body, err := p.parseLambda()
		if err != nil {
			return nil, err
		}
		return &ast.LambdaExpr{Span: t.Span, Params: []string{param}, Body: body}, nil
	}
	if t.Kind == lexer.TokLParen && p.looksLikeParenLambda() {
		p.advance() // (
		var params []string
		for !p.at(lexer.TokRParen) {
			id, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			params = append(params, id.Text)
			if !p.match(lexer.TokComma) {
				break
			}
		}
		p.expect(lexer.TokRParen)
		p.expect(lexer.TokFatArrow)
		body, err := p.parseLambda()
		if err != nil {
			return nil, err
		}
		return &ast.LambdaExpr{Span: t.Span, Params: params, Body: body}, nil
	}
	return p.parseImplies()
}

func (p *Parser) looksLikeParenLambda() bool {
	i := p.pos
	if i >= len(p.toks) || p.toks[i].Kind != lexer.TokLParen {
		return false
	}
	depth := 0
	for ; i < len(p.toks); i++ {
		switch p.toks[i].Kind {
		case lexer.TokLParen:
			depth++
		case lexer.TokRParen:
			depth--
			if depth == 0 {
				return i+1 < len(p.toks) && p.toks[i+1].Kind == lexer.TokFatArrow
			}
		case lexer.TokEOF:
			return false
		}
	}
	return false
}

func (p *Parser) parseImplies() (ast.Expr, error) {
	left, err := p.parseOr()
	if err != nil {
		return nil, err
	}
	if p.at(lexer.TokImplies) {
		tok := p.advance()
		right, err := p.parseImplies()
		if err != nil {
			return nil, err
		}
		return &ast.BinaryExpr{Span: tok.Span, Op: "implies", Left: left, Right: right}, nil
	}
	return left, nil
}

func (p *Parser) parseOr() (ast.Expr, error) {
	left, err := p.parseAnd()
	if err != nil {
		return nil, err
	}
	for p.at(lexer.TokOr) {
		tok := p.advance()
		right, err := p.parseAnd()
		if err != nil {
			return nil, err
		}
		left = &ast.BinaryExpr{Span: tok.Span, Op: "or", Left: left, Right: right}
	}
	return left, nil
}

func (p *Parser) parseAnd() (ast.Expr, error) {
	left, err := p.parseNot()
	if err != nil {
		return nil, err
	}
	for p.at(lexer.TokAnd) {
		tok := p.advance()
		right, err := p.parseNot()
		if err != nil {
			return nil, err
		}
		left = &ast.BinaryExpr{Span: tok.Span, Op: "and", Left: left, Right: right}
	}
	return left, nil
}

func (p *Parser) parseNot() (ast.Expr, error) {
	if p.at(lexer.TokNot) {
		tok := p.advance()
		inner, err := p.parseNot()
		if err != nil {
			return nil, err
		}
		return &ast.UnaryExpr{Span: tok.Span, Op: "not", Expr: inner}, nil
	}
	return p.parseCompare()
}

func (p *Parser) parseCompare() (ast.Expr, error) {
	left, err := p.parseRange()
	if err != nil {
		return nil, err
	}
	for {
		t := p.cur()
		switch t.Kind {
		case lexer.TokEq, lexer.TokNeq, lexer.TokLt, lexer.TokLe, lexer.TokGt, lexer.TokGe, lexer.TokIn:
			p.advance()
			right, err := p.parseRange()
			if err != nil {
				return nil, err
			}
			left = &ast.BinaryExpr{Span: t.Span, Op: t.Text, Left: left, Right: right}
		default:
			return left, nil
		}
	}
}

func (p *Parser) parseRange() (ast.Expr, error) {
	left, err := p.parseWith()
	if err != nil {
		return nil, err
	}
	if p.at(lexer.TokDotDot) {
		tok := p.advance()
		right, err := p.parseWith()
		if err != nil {
			return nil, err
		}
		return &ast.RangeExpr{Span: tok.Span, Lo: left, Hi: right}, nil
	}
	return left, nil
}

func (p *Parser) parseWith() (ast.Expr, error) {
	left, err := p.parseBits(0)
	if err != nil {
		return nil, err
	}
	if p.match(lexer.TokWith) {
		tok := p.cur()
		if _, err := p.expect(lexer.TokLBrace); err != nil {
			return nil, err
		}
		var fields []ast.WithUpdateField
		for !p.at(lexer.TokRBrace) {
			fTok, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			v, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			fields = append(fields, ast.WithUpdateField{Name: fTok.Text, Value: v})
			if !p.match(lexer.TokComma) {
				break
			}
		}
		if _, err := p.expect(lexer.TokRBrace); err != nil {
			return nil, err
		}
		return &ast.WithExpr{Span: tok.Span, Base: left, Fields: fields}, nil
	}
	return left, nil
}

// bitLevels are the operators on the bits of an int, loosest first, as in
// Python: `a | b ^ c & d << 1 + 2` is `a | (b ^ (c & (d << (1 + 2))))`, and
// all of them bind tighter than a comparison.
var bitLevels = [][]lexer.TokenKind{
	{lexer.TokBar},
	{lexer.TokCaret},
	{lexer.TokAmp},
	{lexer.TokShl, lexer.TokShr},
}

func (p *Parser) parseBits(level int) (ast.Expr, error) {
	if level == len(bitLevels) {
		return p.parseAdd()
	}
	left, err := p.parseBits(level + 1)
	if err != nil {
		return nil, err
	}
	for slices.Contains(bitLevels[level], p.cur().Kind) {
		tok := p.advance()
		right, err := p.parseBits(level + 1)
		if err != nil {
			return nil, err
		}
		left = &ast.BinaryExpr{Span: tok.Span, Op: tok.Text, Left: left, Right: right}
	}
	return left, nil
}

func (p *Parser) parseAdd() (ast.Expr, error) {
	left, err := p.parseMul()
	if err != nil {
		return nil, err
	}
	for p.at(lexer.TokPlus) || p.at(lexer.TokMinus) {
		tok := p.advance()
		right, err := p.parseMul()
		if err != nil {
			return nil, err
		}
		left = &ast.BinaryExpr{Span: tok.Span, Op: tok.Text, Left: left, Right: right}
	}
	return left, nil
}

func (p *Parser) parseMul() (ast.Expr, error) {
	left, err := p.parseUnary()
	if err != nil {
		return nil, err
	}
	for p.at(lexer.TokStar) || p.at(lexer.TokSlash) || p.at(lexer.TokPercent) {
		tok := p.advance()
		right, err := p.parseUnary()
		if err != nil {
			return nil, err
		}
		left = &ast.BinaryExpr{Span: tok.Span, Op: tok.Text, Left: left, Right: right}
	}
	return left, nil
}

func (p *Parser) parseUnary() (ast.Expr, error) {
	if p.at(lexer.TokMinus) {
		tok := p.advance()
		inner, err := p.parseUnary()
		if err != nil {
			return nil, err
		}
		return &ast.UnaryExpr{Span: tok.Span, Op: "-", Expr: inner}, nil
	}
	if p.at(lexer.TokTilde) {
		tok := p.advance()
		inner, err := p.parseUnary()
		if err != nil {
			return nil, err
		}
		return &ast.UnaryExpr{Span: tok.Span, Op: "~", Expr: inner}, nil
	}
	return p.parsePostfix()
}

func (p *Parser) parsePostfix() (ast.Expr, error) {
	expr, err := p.parsePrimary()
	if err != nil {
		return nil, err
	}
	for {
		switch p.cur().Kind {
		case lexer.TokDot:
			tok := p.advance()
			fTok, err := p.expectIdent()
			if err != nil {
				return nil, err
			}
			expr = &ast.FieldExpr{Span: tok.Span, Object: expr, Field: fTok.Text}
		case lexer.TokLParen:
			tok := p.cur()
			args, err := p.parseCallArgs()
			if err != nil {
				return nil, err
			}
			expr = &ast.CallExpr{Span: tok.Span, Callee: expr, Args: args}
		case lexer.TokLBracket:
			tok := p.cur()
			if p.matchingBracketFollowedByLParen() {
				p.advance() // [
				var targs []ast.TypeExpr
				for !p.at(lexer.TokRBracket) {
					ta, err := p.parseTypeExpr()
					if err != nil {
						return nil, err
					}
					targs = append(targs, ta)
					if !p.match(lexer.TokComma) {
						break
					}
				}
				if _, err := p.expect(lexer.TokRBracket); err != nil {
					return nil, err
				}
				args, err := p.parseCallArgs()
				if err != nil {
					return nil, err
				}
				expr = &ast.CallExpr{Span: tok.Span, Callee: expr, TypeArgs: targs, Args: args}
			} else {
				p.advance() // [
				idx, err := p.parseExpr()
				if err != nil {
					return nil, err
				}
				if _, err := p.expect(lexer.TokRBracket); err != nil {
					return nil, err
				}
				expr = &ast.IndexExpr{Span: tok.Span, List: expr, Index: idx}
			}
		case lexer.TokQuestion:
			tok := p.advance()
			expr = &ast.TryExpr{Span: tok.Span, Inner: expr}
		default:
			return expr, nil
		}
	}
}

func (p *Parser) matchingBracketFollowedByLParen() bool {
	i := p.pos
	if i >= len(p.toks) || p.toks[i].Kind != lexer.TokLBracket {
		return false
	}
	depth := 0
	for ; i < len(p.toks); i++ {
		switch p.toks[i].Kind {
		case lexer.TokLBracket:
			depth++
		case lexer.TokRBracket:
			depth--
			if depth == 0 {
				return i+1 < len(p.toks) && p.toks[i+1].Kind == lexer.TokLParen
			}
		case lexer.TokEOF:
			return false
		}
	}
	return false
}

func (p *Parser) parseCallArgs() ([]ast.CallArg, error) {
	if _, err := p.expect(lexer.TokLParen); err != nil {
		return nil, err
	}
	var args []ast.CallArg
	for !p.at(lexer.TokRParen) {
		aSpan := p.cur().Span
		if p.match(lexer.TokMut) {
			val, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			args = append(args, ast.CallArg{Span: aSpan, Mut: true, Value: val})
		} else if p.atOwn() {
			p.advance()
			val, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			args = append(args, ast.CallArg{Span: aSpan, Own: true, Value: val})
		} else if p.at(lexer.TokIdent) && p.peek(1).Kind == lexer.TokAssign {
			name := p.advance().Text
			p.advance() // =
			val, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			args = append(args, ast.CallArg{Span: aSpan, Name: name, Value: val})
		} else {
			val, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			args = append(args, ast.CallArg{Span: aSpan, Value: val})
		}
		if !p.match(lexer.TokComma) {
			break
		}
	}
	if _, err := p.expect(lexer.TokRParen); err != nil {
		return nil, err
	}
	return args, nil
}

func (p *Parser) parsePrimary() (ast.Expr, error) {
	t := p.cur()
	switch t.Kind {
	case lexer.TokInt:
		p.advance()
		return &ast.IntLit{Span: t.Span, Value: t.Int}, nil
	case lexer.TokTrue:
		p.advance()
		return &ast.BoolLit{Span: t.Span, Value: true}, nil
	case lexer.TokFalse:
		p.advance()
		return &ast.BoolLit{Span: t.Span, Value: false}, nil
	case lexer.TokStr:
		p.advance()
		return &ast.StrLit{Span: t.Span, Value: t.Text}, nil
	case lexer.TokFStr:
		p.advance()
		return p.parseFStr(t)
	case lexer.TokNone:
		p.advance()
		return &ast.NoneLit{Span: t.Span}, nil
	case lexer.TokRunWorkflow:
		p.advance()
		wname, err := p.expectIdent()
		if err != nil {
			return nil, err
		}
		args, err := p.parseCallArgs()
		if err != nil {
			return nil, err
		}
		return &ast.RunWorkflowExpr{Span: t.Span, Name: wname.Text, Args: args}, nil
	case lexer.TokIdent:
		if t.Text == "old" && p.peek(1).Kind == lexer.TokLParen {
			p.advance()
			p.advance()
			inner, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokRParen); err != nil {
				return nil, err
			}
			return &ast.OldExpr{Span: t.Span, Inner: inner}, nil
		}
		p.advance()
		return &ast.Ident{Span: t.Span, Name: t.Text}, nil
	case lexer.TokLParen:
		p.advance()
		e, err := p.parseExpr()
		if err != nil {
			return nil, err
		}
		if _, err := p.expect(lexer.TokRParen); err != nil {
			return nil, err
		}
		return e, nil
	case lexer.TokLBracket:
		p.advance()
		var elems []ast.Expr
		for !p.at(lexer.TokRBracket) {
			el, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			elems = append(elems, el)
			if !p.match(lexer.TokComma) {
				break
			}
		}
		if _, err := p.expect(lexer.TokRBracket); err != nil {
			return nil, err
		}
		return &ast.ListLit{Span: t.Span, Elems: elems}, nil
	case lexer.TokLBrace:
		p.advance()
		var entries []ast.MapEntry
		for !p.at(lexer.TokRBrace) {
			k, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if _, err := p.expect(lexer.TokColon); err != nil {
				return nil, err
			}
			v, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			entries = append(entries, ast.MapEntry{Key: k, Value: v})
			if !p.match(lexer.TokComma) {
				break
			}
		}
		if _, err := p.expect(lexer.TokRBrace); err != nil {
			return nil, err
		}
		return &ast.MapLit{Span: t.Span, Entries: entries}, nil
	default:
		return nil, p.errAt(t, "unexpected token in expression: %s", t)
	}
}

func (p *Parser) parseFStr(t lexer.Token) (ast.Expr, error) {
	raw := t.Text
	var parts []ast.FStrPart
	var lit strings.Builder
	i := 0
	for i < len(raw) {
		if raw[i] == '{' {
			if i+1 < len(raw) && raw[i+1] == '{' {
				lit.WriteByte('{')
				i += 2
				continue
			}
			if lit.Len() > 0 {
				parts = append(parts, ast.FStrPart{Text: lit.String()})
				lit.Reset()
			}
			// Find matching '}'
			depth := 1
			j := i + 1
			for j < len(raw) && depth > 0 {
				if raw[j] == '{' {
					depth++
				} else if raw[j] == '}' {
					depth--
				}
				j++
			}
			if depth != 0 {
				return nil, p.errAt(t, "unclosed '{' in f-string")
			}
			subSrc := raw[i+1 : j-1]
			toks, err := lexer.Lex(p.file, subSrc)
			if err != nil {
				return nil, err
			}
			subP := &Parser{file: p.file, toks: toks}
			subExpr, err := subP.parseExpr()
			if err != nil {
				return nil, err
			}
			parts = append(parts, ast.FStrPart{IsExpr: true, Expr: subExpr})
			i = j
			continue
		}
		if raw[i] == '}' && i+1 < len(raw) && raw[i+1] == '}' {
			lit.WriteByte('}')
			i += 2
			continue
		}
		lit.WriteByte(raw[i])
		i++
	}
	if lit.Len() > 0 {
		parts = append(parts, ast.FStrPart{Text: lit.String()})
	}
	return &ast.FStrExpr{Span: t.Span, Parts: parts}, nil
}
