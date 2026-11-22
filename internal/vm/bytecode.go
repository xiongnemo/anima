package vm

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"strings"
)

type OpCode uint8

const (
	OpNop OpCode = iota
	OpPushConst
	OpPushInt
	OpPushBool
	OpPushNone
	OpPop
	OpDup
	OpLoadLocal
	OpStoreLocal
	OpLoadUpval
	OpAdd
	OpSub
	OpMul
	OpDiv
	OpMod
	OpNeg
	OpNot
	OpEq
	OpNeq
	OpLt
	OpLe
	OpGt
	OpGe
	OpJmp
	OpJmpIfFalse
	OpJmpIfTruePeek
	OpJmpIfFalsePeek
	OpCall
	OpCallDyn
	OpRet
	OpTryUnwrap
	OpMakeList
	OpMakeMap
	OpMakeEntity
	OpMakeVariant
	OpGetField
	OpSetField
	OpGetIndex
	OpSetIndex
	OpWithUpdate
	OpMakeClosure
	OpCheckVariant
	OpExtractField
	OpFmtStr
	// Tier 2 Macro Concurrency Opcodes (VM Scheduler Yield Points)
	OpSyncAction
	OpTokAcquire
	OpTokRelease
	OpForkSpawn
	OpJoinWait
	OpRunWorkflow
	OpHalt
	// OpIn is `x in xs`: an element of a list, a key of a map, a part of a
	// string. It comes after the others so that they keep their numbers.
	OpIn
	// The operators on the bits of an int, after it for the same reason.
	OpBitAnd
	OpBitOr
	OpBitXor
	OpBitNot
	OpShl
	OpShr
)

var opNames = map[OpCode]string{
	OpNop:            "NOP",
	OpPushConst:      "PUSH_CONST",
	OpPushInt:        "PUSH_INT",
	OpPushBool:       "PUSH_BOOL",
	OpPushNone:       "PUSH_NONE",
	OpPop:            "POP",
	OpDup:            "DUP",
	OpLoadLocal:      "LOAD_LOCAL",
	OpStoreLocal:     "STORE_LOCAL",
	OpLoadUpval:      "LOAD_UPVAL",
	OpAdd:            "ADD",
	OpSub:            "SUB",
	OpMul:            "MUL",
	OpDiv:            "DIV",
	OpMod:            "MOD",
	OpNeg:            "NEG",
	OpNot:            "NOT",
	OpEq:             "EQ",
	OpNeq:            "NEQ",
	OpLt:             "LT",
	OpLe:             "LE",
	OpGt:             "GT",
	OpGe:             "GE",
	OpJmp:            "JMP",
	OpJmpIfFalse:     "JMP_IF_FALSE",
	OpJmpIfTruePeek:  "JMP_IF_TRUE_PEEK",
	OpJmpIfFalsePeek: "JMP_IF_FALSE_PEEK",
	OpCall:           "CALL",
	OpCallDyn:        "CALL_DYN",
	OpRet:            "RET",
	OpTryUnwrap:      "TRY_UNWRAP",
	OpMakeList:       "MAKE_LIST",
	OpMakeMap:        "MAKE_MAP",
	OpMakeEntity:     "MAKE_ENTITY",
	OpMakeVariant:    "MAKE_VARIANT",
	OpGetField:       "GET_FIELD",
	OpSetField:       "SET_FIELD",
	OpGetIndex:       "GET_INDEX",
	OpSetIndex:       "SET_INDEX",
	OpWithUpdate:     "WITH_UPDATE",
	OpMakeClosure:    "MAKE_CLOSURE",
	OpCheckVariant:   "CHECK_VARIANT",
	OpExtractField:   "EXTRACT_FIELD",
	OpFmtStr:         "FMT_STR",
	OpSyncAction:     "SYNC_ACTION",
	OpTokAcquire:     "TOK_ACQUIRE",
	OpTokRelease:     "TOK_RELEASE",
	OpForkSpawn:      "FORK_SPAWN",
	OpJoinWait:       "JOIN_WAIT",
	OpRunWorkflow:    "RUN_WORKFLOW",
	OpHalt:           "HALT",
	OpIn:             "IN",
	OpBitAnd:         "BIT_AND",
	OpBitOr:          "BIT_OR",
	OpBitXor:         "BIT_XOR",
	OpBitNot:         "BIT_NOT",
	OpShl:            "SHL",
	OpShr:            "SHR",
}

func (op OpCode) String() string {
	if s, ok := opNames[op]; ok {
		return s
	}
	return fmt.Sprintf("OP_%d", op)
}

func EncodeABC(op OpCode, a uint8, bc uint16) uint32 {
	return (uint32(op) << 24) | (uint32(a) << 16) | uint32(bc)
}

func EncodeImm(op OpCode, imm uint32) uint32 {
	return (uint32(op) << 24) | (imm & 0x00FFFFFF)
}

func DecodeInstr(w uint32) (op OpCode, a uint8, bc uint16, imm uint32) {
	op = OpCode(w >> 24)
	a = uint8((w >> 16) & 0xFF)
	bc = uint16(w & 0xFFFF)
	imm = w & 0x00FFFFFF
	return
}

type ConstKind int

const (
	ConstInt ConstKind = iota
	ConstStr
)

type Constant struct {
	Kind ConstKind
	Int  int64
	Str  string
}

type CallMeta struct {
	CalleeName string
	ArgCount   int
	KwNames    []string
	TypeArgs   []string
	IsMethod   bool
}

type FieldMeta struct {
	Names []string
}

type EntityFieldSchema struct {
	Name  string
	Kind  string // "int", "bool", "str"
	HasLo bool
	HasHi bool
	Lo    int64
	Hi    int64
	Type  *JSONType
}

// JSONType is a type as json.decode checks a value against it.
type JSONType struct {
	Kind   string // "int", "bool", "str", "list", "map", "option", "entity", "any"
	HasLo  bool
	HasHi  bool
	Lo     int64
	Hi     int64
	Elem   *JSONType // of a list, a map, an option
	Entity string
}

type EntitySchema struct {
	Name       string
	Fields     []EntityFieldSchema
	Invariants []string // serialized invariant expressions for JSON boundary validation
}

type FuncProto struct {
	Name       string
	Params     []string
	NumLocals  int
	UpvalNames []string
	Code       []uint32
	Lines      []int
}

type WorkflowProto struct {
	Name   string
	Params []string
	Pools  map[string]int64
	// Compiled node table executed by VM workflow scheduler
	EntryFunc string
}

type BytecodeModule struct {
	File         string
	VerifyDigest [32]byte
	Verified     bool
	Constants    []Constant
	CallMetas    []CallMeta
	FieldMetas   []FieldMeta
	Entities     []EntitySchema
	EntityIndex  map[string]int
	Funcs        []*FuncProto
	FuncIndex    map[string]int
	Workflows    []WorkflowProto
	WorkflowIdx  map[string]int
}

var anbcMagic = []byte{'A', 'N', 'B', 'C', 0x01, 0x00}

// Encode serializes the BytecodeModule to the .anbc binary container format.
func (m *BytecodeModule) Encode() ([]byte, error) {
	payload, err := json.Marshal(m)
	if err != nil {
		return nil, err
	}
	var buf bytes.Buffer
	buf.Write(anbcMagic)
	buf.Write(m.VerifyDigest[:])
	_ = binary.Write(&buf, binary.LittleEndian, uint32(len(payload)))
	buf.Write(payload)
	return buf.Bytes(), nil
}

// Decode loads a BytecodeModule from .anbc bytes and verifies integrity.
func Decode(data []byte) (*BytecodeModule, error) {
	if len(data) < len(anbcMagic)+32+4 || !bytes.Equal(data[:len(anbcMagic)], anbcMagic) {
		return nil, fmt.Errorf("invalid .anbc bytecode magic header")
	}
	off := len(anbcMagic)
	var digest [32]byte
	copy(digest[:], data[off:off+32])
	off += 32
	length := binary.LittleEndian.Uint32(data[off : off+4])
	off += 4
	if int(length) > len(data)-off {
		return nil, fmt.Errorf("truncated .anbc bytecode payload")
	}
	var m BytecodeModule
	if err := json.Unmarshal(data[off:off+int(length)], &m); err != nil {
		return nil, err
	}
	m.VerifyDigest = digest
	return &m, nil
}

// Seal stamps the bytecode with a verification digest.
func (m *BytecodeModule) Seal(source string, verified bool) {
	m.Verified = verified
	sum := sha256.Sum256([]byte(source))
	m.VerifyDigest = sum
}

// Disassemble returns a human-readable disassembly of all functions and workflows.
func (m *BytecodeModule) Disassemble() string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "; Anima Verified Bytecode (.anbc) — %s [verified=%v, sha256=%x]\n\n",
		m.File, m.Verified, m.VerifyDigest[:8])
	for _, fn := range m.Funcs {
		fmt.Fprintf(&sb, "func %s(%s) [locals=%d, upvals=%d]:\n",
			fn.Name, strings.Join(fn.Params, ", "), fn.NumLocals, len(fn.UpvalNames))
		for pc, w := range fn.Code {
			op, a, bc, imm := DecodeInstr(w)
			line := 0
			if pc < len(fn.Lines) {
				line = fn.Lines[pc]
			}
			extra := ""
			switch op {
			case OpPushConst, OpGetField, OpSetField, OpSyncAction, OpTokAcquire, OpTokRelease, OpCheckVariant:
				if int(imm) < len(m.Constants) {
					c := m.Constants[imm]
					if c.Kind == ConstStr {
						extra = fmt.Sprintf("; %q", c.Str)
					} else {
						extra = fmt.Sprintf("; %d", c.Int)
					}
				}
			case OpCall:
				if int(bc) < len(m.CallMetas) {
					cm := m.CallMetas[bc]
					extra = fmt.Sprintf("; %s(args=%d)", cm.CalleeName, cm.ArgCount)
				}
			case OpMakeEntity:
				if int(a) < len(m.Entities) {
					extra = fmt.Sprintf("; entity %s", m.Entities[a].Name)
				}
			case OpMakeVariant:
				if int(bc) < len(m.Constants) {
					extra = fmt.Sprintf("; variant %s(args=%d)", m.Constants[bc].Str, a)
				}
			case OpMakeClosure:
				if int(a) < len(m.Funcs) {
					extra = fmt.Sprintf("; closure %s", m.Funcs[a].Name)
				}
			case OpJmp, OpJmpIfFalse, OpJmpIfTruePeek, OpJmpIfFalsePeek:
				extra = fmt.Sprintf("; -> %04d", imm)
			case OpPushInt, OpLoadLocal, OpStoreLocal, OpLoadUpval, OpMakeList, OpMakeMap:
				extra = fmt.Sprintf("; #%d", imm)
			}
			fmt.Fprintf(&sb, "  L%-4d %04d  %-18s a=%-3d bc=%-5d %s\n", line, pc, op.String(), a, bc, extra)
		}
		sb.WriteString("\n")
	}
	return sb.String()
}
