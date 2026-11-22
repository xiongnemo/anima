package lexer

import "testing"

func TestLexerIndentAndPipeContinuation(t *testing.T) {
	src := `
# comment ignored
def foo(xs: list[int, cap=4]) -> int:
    total = xs
        |> filter(x => x > 0)
        |> map(x => x * 2)
    if total > 0:
        return total
    return 0
`
	toks, err := Lex("test.anm", src)
	if err != nil {
		t.Fatalf("unexpected lex error: %v", err)
	}
	var kinds []TokenKind
	for _, tk := range toks {
		kinds = append(kinds, tk.Kind)
	}
	// Verify we get INDENT inside def, NO INDENT for multi-line |>, INDENT for if, and balanced DEDENTs
	indentCount := 0
	dedentCount := 0
	pipeCount := 0
	for _, k := range kinds {
		switch k {
		case TokIndent:
			indentCount++
		case TokDedent:
			dedentCount++
		case TokPipe:
			pipeCount++
		}
	}
	if indentCount != 2 || dedentCount != 2 {
		t.Fatalf("expected 2 indents and 2 dedents, got %d/%d; tokens: %v", indentCount, dedentCount, toks)
	}
	if pipeCount != 2 {
		t.Fatalf("expected 2 pipe tokens, got %d", pipeCount)
	}
}

func TestLexerRangesAndNumbers(t *testing.T) {
	src := `type Money = int[0..1_000_000]`
	toks, err := Lex("t.anm", src)
	if err != nil {
		t.Fatal(err)
	}
	want := []TokenKind{TokIdent, TokIdent, TokAssign, TokIdent, TokLBracket, TokInt, TokDotDot, TokInt, TokRBracket, TokNewline, TokEOF}
	if len(toks) != len(want) {
		t.Fatalf("got %d tokens %v, want %d", len(toks), toks, len(want))
	}
	for i, w := range want {
		if toks[i].Kind != w {
			t.Fatalf("tok[%d] = %v, want %v", i, toks[i], w)
		}
	}
	if toks[5].Int != 0 || toks[7].Int != 1000000 {
		t.Fatalf("bad int values: %d, %d", toks[5].Int, toks[7].Int)
	}
}

func TestLexerBitOperators(t *testing.T) {
	toks, err := Lex("t.anm", `a & b | c ^ ~d << 1 >> 2 |> f() <= g >= h < i > j`)
	if err != nil {
		t.Fatal(err)
	}
	want := []TokenKind{
		TokIdent, TokAmp, TokIdent, TokBar, TokIdent, TokCaret, TokTilde, TokIdent, TokShl, TokInt, TokShr, TokInt,
		TokPipe, TokIdent, TokLParen, TokRParen, TokLe, TokIdent, TokGe, TokIdent, TokLt, TokIdent, TokGt, TokIdent,
		TokNewline, TokEOF,
	}
	if len(toks) != len(want) {
		t.Fatalf("got %d tokens %v, want %d", len(toks), toks, len(want))
	}
	for i, w := range want {
		if toks[i].Kind != w {
			t.Fatalf("tok[%d] = %v, want %v", i, toks[i], w)
		}
	}
}
