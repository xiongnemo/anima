package sema

import (
	"reflect"

	"github.com/xiongnemo/anima/internal/ast"
)

// callAllPiped is callPiped of the program and of what the checker noted
// of it for the kernels.
func (c *checker) callAllPiped() {
	if len(c.pipedCalls) == 0 {
		return
	}
	c.callPiped(reflect.ValueOf(c.info.Program))
	for _, et := range c.info.Entities {
		c.callPiped(reflect.ValueOf(et.Invariants))
	}
	for _, rs := range c.info.ArgRanges {
		c.callPiped(reflect.ValueOf(rs))
	}
	for call, e := range c.info.TimeoutArgs {
		if pe, ok := e.(*ast.PipeExpr); ok && c.pipedCalls[pe] != nil {
			c.info.TimeoutArgs[call] = c.pipedCalls[pe]
		}
	}
}

// callPiped puts, in place of each pipe under n that is a call by name
// (pipedCalls), that call, with the type the pipe was given. The kernels
// and the backends are then given g(x, a) where `x |> g(a)` was written,
// so that nothing is proved of the one and not of the other.
func (c *checker) callPiped(n reflect.Value) {
	switch n.Kind() {
	case reflect.Interface:
		if n.IsNil() {
			return
		}
		if n.CanSet() {
			if pe, ok := n.Interface().(*ast.PipeExpr); ok {
				if call := c.pipedCalls[pe]; call != nil {
					if t, ok := c.info.ExprTypes[pe]; ok {
						c.info.ExprTypes[call] = t
					}
					n.Set(reflect.ValueOf(call))
				}
			}
		}
		c.callPiped(n.Elem())
	case reflect.Pointer:
		if !n.IsNil() {
			c.callPiped(n.Elem())
		}
	case reflect.Slice:
		for i := 0; i < n.Len(); i++ {
			c.callPiped(n.Index(i))
		}
	case reflect.Struct:
		for i := 0; i < n.NumField(); i++ {
			c.callPiped(n.Field(i))
		}
	}
}
