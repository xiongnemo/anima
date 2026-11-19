# Anima (`.anm` / `.anbc`)

**Anima** is a single-binary, Python-readable, UML-native, **100% self-verified** general-purpose modeling and systems programming language. It unifies four historically fragmented engineering artifacts into one source language with zero external theorem-prover dependencies:

1. **Ada / SPARK-Level Data & Contract Proofs (Self-Built `AnimaSMT`)**:
   - Refinement range types (`int[0..1_000_000]`), `requires` / `ensures` / `old(...)`, entity `invariant`s, `mut` exclusive anti-aliasing, loop/recursion `decreases` termination, and SMT-verified exhaustive `match` + `choice` completeness/exclusivity.
   - `int` is a signed 64-bit integer at run time, in both backends, while proofs reason over unbounded integers. Every `+`, `-`, `*`, unary `-`, `/`, `%`, `sum` and `fold` therefore gets an `int64_overflow` proof obligation, and `anima check` fails when one cannot be proved. A product of two non-constant operands needs bounds on both (a range type or a `requires`). Inside and after a loop, a variable the loop assigns is known only through the loop's `invariant`s and its range type.
   - 100% pure-Go prover: **Interval/Octagon Abstract Domain (Floyd-Warshall)** + **CDCL SAT (2-watched literals + 1-UIP)** + **Exact Rational Dutertre-de Moura Simplex (`math/big.Rat`)** + **Integer Branch-and-Bound**.
2. **FSP / LTSA & Linear Typestate Verification**:
   - Compiles `monitor`, `machine`, and `workflow` synchronizations into explicit Labelled Transition Systems (`||` composition, relabeling, hiding, priority).
   - Verifies Safety (`property` `ERROR=-1`), Deadlock freedom, **Tarjan SCC Fair-Choice `progress` (starvation/livelock)**, bounded **FLTL**, and **Linear Socket/File/Port Typestate** (zero FD leaks & zero use-after-close).
   - Exports standard `.fsp` compatible with Magee & Kramer's **LTSA**.
3. **Petri Net & Workflow Soundness**:
   - Compiles `workflow` (`pool`, `fork`/`join` AND-split/join, `choice`/`merge` XOR-split/join) into Place/Transition WF-Nets.
   - Verifies **Karp-Miller Coverability** (`1_safe`, boundedness), **van der Aalst Soundness** (*Option to complete*, *Proper completion*, *No dead transitions*), and cross-checks via the **Short-Circuit Theorem ($\overline{N}$ bounded & $L_4$-live)**.
   - Exports ISO `.pnml` XML.
4. **OCaml-Style Dual Execution Backends + 8 Formally Verified Standard Libraries**:
   - **Bytecode VM (`anima run`)**: Compiles to 32-bit fixed-width `.anbc` bytecode with deterministic workflow/fiber scheduling, CLI `--animate`, and `--replay` counterexample reproduction.
   - **Native ELF Backend (`anima build`)**: Transpiles verified models to standalone C11 (`pthreads` + POSIX sockets + OpenSSL 3.0) and invokes `gcc -O2` to emit native executables.
   - **Embedded Dark Material Studio (`anima studio`)**: Single-binary Orchis-dark web studio projecting UML Class, Statechart, Petri Token Animation, and Counterexample Sequence diagrams.

## Quick Start

```bash
# Build single static Go binary (zero external Go deps)
CGO_ENABLED=0 go build -o anima ./cmd/anima

# Run all 3 formal verification kernels with detailed proof explanation
./anima check --explain examples/escrow_service.anm

# Run on built-in 32-bit Bytecode VM
./anima run examples/secure_gateway.anm

# Compile to standalone native ELF binary (OCamlopt-style C11 backend)
./anima build -o /tmp/gateway examples/secure_gateway.anm && /tmp/gateway

# Inspect 32-bit bytecode disassembly, UML Mermaid/DOT views, or FSP/PNML exports
./anima disasm examples/escrow_service.anm
./anima uml --format mermaid examples/escrow_service.anm
./anima export --fsp /tmp/escrow.fsp --pnml /tmp/escrow.pnml examples/escrow_service.anm

# Launch embedded Orchis-dark Studio & interactive Animator
./anima studio examples/escrow_service.anm
```

## Standard Library (8 Verified Modules)

- `std.fp` & `prelude` — Total-terminating pipelines (`|>`, `map`, `filter`, `fold`, `filter_ok`, `unwrap_or`) with length/sum refinement inference
- `std.concurrent` — `ThreadPool`, bounded `Channel`, `Mutex`, `Semaphore`, `parallel_map`
- `std.socket` — Typestate-verified `TcpListener` & `TcpStream` (compile-time FD leak & use-after-close prevention)
- `std.requests` — Sync/async HTTP(S) `get`, `post`, `Session`, `gather` with mandatory bounded `timeout_ms: int[1..300_000]`
- `std.json` — Boundary-sanitized `json.decode[EntityType]` enforcing refinement bounds & compiled entity invariants
- `std.bytes` & `std.crypto` — Bounds-checked `ByteView` (`read_u8`, `read_u16_be`, `read_u32_be`) + `sha256`, `hmac_sha256`, `constant_time_eq`
- `std.fs`, `std.cli`, `std.time` — Typestate-checked `File`, `write_atomic`, `cli.args`, `time.now_ms`
