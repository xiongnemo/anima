# Anima (`.anm` / `.anbc`)

Anima is a general-purpose language in which the model of a program and the program are one source file. Data contracts, state machines, concurrency and workflows are written next to the code, and three verification kernels check them before anything runs. `anima run` and `anima build` refuse a program that `anima check` does not pass.

The verifier is written in Go with no external solver, and the whole toolchain is one static binary.

```
type Money = int[0..1_000_000]

entity Account:
    balance: Money
    escrow:  Money
    invariant: balance + escrow <= 1_000_000

def lock_funds(mut acc: Account, amt: int[1..10_000]) -> bool:
    ensures: acc.balance + acc.escrow == old(acc.balance) + old(acc.escrow)
    if acc.balance >= amt:
        acc.balance = acc.balance - amt
        acc.escrow = acc.escrow + amt
        return True
    return False

def main() -> int:
    acc = Account(balance=500, escrow=0)
    ok = lock_funds(mut acc, 120)
    print(ok, acc.balance, acc.escrow)
    return 0
```

`anima check` proves the ranges, the invariant, the `ensures` and that no operation overflows; the program prints `True 380 120` on both backends. Write `acc.escrow + amt + 1` instead and the check fails with a counterexample (`acc.balance=1, acc.escrow=999999, amt=1`).

## What is checked

| Kernel | Checks | Details |
|---|---|---|
| **Contracts** (SPARK-style weakest preconditions, own SMT solver) | range types `int[lo..hi]`, `requires` / `ensures` / `old(...)`, entity `invariant`s, int64 overflow, index, map-key and byte-view bounds, exhaustive `match`, loop and recursion termination (`decreases`) | [docs/contracts.md](docs/contracts.md) |
| **FSP / LTS and ownership** | `monitor`, `machine` and `property` as labelled transition systems: safety, deadlock freedom, `progress`, bounded FLTL; one owner for every socket, file and thread pool, closed on every path | [docs/concurrency.md](docs/concurrency.md), [docs/ownership.md](docs/ownership.md) |
| **Petri / WF-net** | a `workflow` as a workflow net: boundedness, 1-safety, soundness (option to complete, proper completion, no dead transitions) | [docs/workflows.md](docs/workflows.md) |

Before the kernels, the semantic checker settles the type of every value and refuses what the backends could not run as written: [docs/language.md](docs/language.md).

A verified program runs on a bytecode VM (`anima run`) or is compiled through C11 to a native executable (`anima build`). Both do the same thing, and tests run the same sources on both: [docs/backends.md](docs/backends.md).

## Quick start

```bash
# Build the single static binary (no Go dependencies outside the standard library)
CGO_ENABLED=0 go build -o anima ./cmd/anima

# Run the three kernels, with the proofs explained
./anima check --explain examples/escrow_service.anm

# Run on the bytecode VM
./anima run examples/secure_gateway.anm

# Compile to a native executable (needs gcc and OpenSSL 3 headers)
./anima build -o /tmp/gateway examples/secure_gateway.anm && /tmp/gateway

# Bytecode disassembly, UML views, FSP / PNML exports
./anima disasm examples/escrow_service.anm
./anima uml --format mermaid examples/escrow_service.anm
./anima export --fsp /tmp/escrow.fsp --pnml /tmp/escrow.pnml examples/escrow_service.anm

# Web studio with diagrams and an animator
./anima studio examples/escrow_service.anm
```

## Documentation

| Document | What it covers |
|---|---|
| [docs/language.md](docs/language.md) | variables, comparisons, calls, lambdas, values of unknown or open type, returns, `match` |
| [docs/contracts.md](docs/contracts.md) | what the contract kernel proves and what it knows: overflow, entities and aliases, element ranges, indexes, map keys, pipelines, byte views |
| [docs/ownership.md](docs/ownership.md) | handles: sockets, files, thread pools, futures, and `?` |
| [docs/concurrency.md](docs/concurrency.md) | monitors, machines, properties, progress |
| [docs/workflows.md](docs/workflows.md) | workflows: paths, `choice` / `merge`, `fork` / `join`, soundness |
| [docs/stdlib.md](docs/stdlib.md) | the standard modules and how they are called |
| [docs/backends.md](docs/backends.md) | the VM, the native backend, what "the same on both" covers, the studio, the CLI |
| [docs/design.md](docs/design.md) | why the language exists and the decisions behind it |

## Examples

| File | Shows |
|---|---|
| `examples/escrow_service.anm` | entities with invariants, a port protocol, a monitor with a safety property and progress, a sound workflow |
| `examples/secure_gateway.anm` | a network service: sockets, JSON decoding into entities, byte views, pipelines |
| `examples/concurrent_http.anm` | a concurrent HTTP server: each connection is moved into a worker of a thread pool |
| `examples/agent_sandbox.anm` | a reference monitor for an LLM agent: budgets, an unreachable unapproved shell call, a sound tool workflow |
| `examples/dining_philosophers_safe.anm` | the asymmetric, deadlock-free dining philosophers |
| `examples/single_lane_bridge.anm` | the single-lane bridge: safety and progress |

## Status

The six programs the language is being built towards:

| Program | Status |
|---|---|
| Concurrent HTTP server | done (`examples/concurrent_http.anm`) |
| STUN NAT detection | in progress: bit operators are in, UDP sockets and byte building are next |
| Mini Redis, then Raft replication | not started |
| DNS server | not started |
| TFTP server | not started |
| Peer-to-peer chat node | not started |

## Repository

```
cmd/anima          the command-line tool
internal/lexer     tokens
internal/parser    syntax tree (internal/ast)
internal/sema      names, types, calls, workflow paths
internal/verify    the kernels: smt (solver), spark (contracts), lts (FSP and ownership), petri (workflow nets)
internal/vm        bytecode compiler and virtual machine
internal/native    C11 generator and its runtime
internal/stdlib    catalog of the standard modules
internal/studio    web studio
examples           six verified programs
tests              end-to-end tests; tests/bugs holds programs that must be refused
```

```bash
go vet ./...
go test -race -short ./...
```

Each program in `tests/bugs` has a fault a checker is there to find (many were accepted once and went wrong when run); `tests/e2e_test.go` holds each one to the error it must give.
