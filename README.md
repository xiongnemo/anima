# Anima (`.anm` / `.anbc`)

**Anima** is a single-binary, Python-readable, UML-native, **100% self-verified** general-purpose modeling and systems programming language. It unifies four historically fragmented engineering artifacts into one source language with zero external theorem-prover dependencies:

1. **Ada / SPARK-Level Data & Contract Proofs (Self-Built `AnimaSMT`)**:
   - Refinement range types (`int[0..1_000_000]`), `requires` / `ensures` / `old(...)`, entity `invariant`s, `mut` exclusive anti-aliasing, loop/recursion `decreases` termination, and SMT-verified exhaustive `match` + `choice` completeness/exclusivity.
   - `int` is a signed 64-bit integer at run time, in both backends, while proofs reason over unbounded integers. Every `+`, `-`, `*`, unary `-`, `/`, `%`, `sum` and `fold` therefore gets an `int64_overflow` proof obligation, and `anima check` fails when one cannot be proved. A product of two non-constant operands needs bounds on both (a range type or a `requires`). Inside and after a loop, a variable the loop assigns is known only through the loop's `invariant`s and its range type. An assignment replaces everything known about the variable (an entity or list the prover cannot follow becomes an arbitrary value of its type), and after an `if` or a `match` each variable holds the value of whichever branch ran.
   - **Entity invariants**: a function may break an entity's `invariant` between two field updates, but the invariant is proved wherever the entity is handed on: as an argument of a call, as a returned value, or as an element or field of another value. That is what lets a function assume the invariants of its parameters, of list elements and of matched payloads. The room between two updates only exists for an entity that one variable alone can reach. Once it is shared (a loop variable, a matched payload, `r = rows[i]`, a second name `c = b`, or a variable that was put into a list, map, variant or entity), every field write has to leave the invariant true. Writing a field of an element in place (`rows[i].x = v`) has to keep the element's invariant provable from that field alone; otherwise build the new element and assign it. A field write on an object whose entity type is not known (an element of an untyped `m = {}`) is rejected: give the map a type (`m: map[str, T] = {}`).
   - **Aliases**: entities, lists and maps are references, so `c = b` gives one entity two names. The kernel tracks which variables are *shared*, meaning their entity can be reached another way: a second name, a loop variable or `r = rows[i]` and the list it comes from, a matched payload and the matched value, a variable put into a list, map, variant or entity, an argument a call may keep (inside a `mut` argument with room for it, or through a channel or pool) and the result of a call that was given an entity. A write through a shared variable, in place (`rows[i].x = v`), or by a callee given it as `mut`, makes the kernel forget what it knew about the fields of every other shared variable; a variable that is the only way to reach its entity keeps its facts. Two rules keep this sound across calls: a value received through a parameter that is not `mut` cannot be written through another name either (`c = a; c.x = 0`, `for r in rows: r.x = 0` fail `readonly_<name>`), and a `mut` argument may not be reachable from another argument of the same call (`c = b; g(mut b, c)` fails `call_g_mut_alias`), since a function is verified with its parameters taken for separate values.
   - **Calls**: a callee's `requires` is proved wherever the call is written. A call may change what it receives as `mut`: afterwards the caller knows the argument's type, an entity's `invariant`, and the callee's `ensures` clauses over its parameters (clauses about `result` are not used). So that the order of a read and the change never decides a result, a variable passed as `mut` cannot be used elsewhere in the same statement (`total = box.v + reset(mut box)` is rejected; put the call in a statement of its own). A `mut` parameter cannot be assigned a new value, a `?` has to leave the function's `ensures` and `mut` invariants true like any other return, and only a pipeline stage (`xs |> map(x => f(mut s))`) may pass an outer variable as `mut` from a lambda.
   - 100% pure-Go prover: **Interval/Octagon Abstract Domain (Floyd-Warshall)** + **CDCL SAT (2-watched literals + 1-UIP)** + **Exact Rational Dutertre-de Moura Simplex (`math/big.Rat`)** + **Integer Branch-and-Bound**.
2. **FSP / LTSA & Linear Typestate Verification**:
   - Compiles `monitor`, `machine`, and `workflow` synchronizations into explicit Labelled Transition Systems (`||` composition, relabeling, hiding, priority).
   - Verifies Safety (`property` `ERROR=-1`), Deadlock freedom, **Tarjan SCC Fair-Choice `progress` (starvation/livelock)**, bounded **FLTL**, and **Linear Socket/File/Port Typestate** (zero FD leaks & zero use-after-close).
   - **Handle ownership** (`sock.TcpStream`, `sock.TcpListener`, `fs.File`): every handle has one owner, who must close it on every path. A handle parameter is borrowed (usable, but it cannot be closed or moved) unless declared `own`; `handle(own conn)`, `c2 = conn` and `return conn` move it, and a moved handle cannot be used again. `pool.submit(() => handle(own conn))` moves a connection into a worker thread; a stream or file cannot be shared between threads, while a listener can be lent to tasks and not closed until they are awaited or the pool is shut down. `?` is rejected while the function owns an open handle: `match` on the result and close the handle on the failure path, or do the fallible work in a function that borrows it. Handles cannot be stored in entities, lists or other values. See `examples/concurrent_http.anm`.
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
