# Running a program: the VM, the native backend, the tools

A program is run only when it is verified: `anima run` and `anima build` run the three kernels first and refuse a program that fails.

## The two backends

**Bytecode VM (`anima run`).** The program is compiled to 32-bit fixed-width bytecode (`.anbc`) and run by a virtual machine with deterministic scheduling of workflows and fibers.

- `--seed N` fixes the schedule.
- `--animate` steps through the run in the terminal.
- `--replay trace.json` replays a counterexample saved by `anima check --save-cex`.

**Native backend (`anima build`).** The verified program is translated to standalone C11 (`pthreads`, POSIX sockets, OpenSSL 3.0) and compiled by `gcc -O2` to an executable. `--emit-c out.c` keeps the C source.

## The same on both

A verified program does the same on both backends. Tests run one source on both and compare the output (`runOnBothBackends` in `tests/e2e_test.go`). What that covers:

- Every standard function and handle method does the same as on the VM, down to the text of an error of the file system or of a request that got no answer (`open /p: no such file or directory`).
- A division or modulo by zero, which no verified program reaches, stops a native program with the VM's message and exit code 1 rather than a signal.
- The HTTP client frames an answer as Go's does: a chunked body is decoded, a body is exactly as long as its `Content-Length` (`unexpected EOF` when the server stops short), 204 and 304 have none, and `timeout_ms` is for the whole request, not for each read.
- A request is sent whole, whatever the length of its body.
- A send to a peer that has gone is an `Err`, not a `SIGPIPE` that ends the program. Only standard output keeps that signal, as in Go.
- A `?` that returns early closes nothing on either backend.
- A lambda copies the variables its body names when it is made; one held in a workflow variable or written in a fork branch is called as anywhere else.
- `run_workflow` runs the workflow it names, and a `merge` node is run by both.
- A value that holds itself is printed and encoded with an end, the same way: [language.md](language.md#a-value-may-hold-itself).
- `json.encode` writes the same text, and `json.decode` reads it back: [stdlib.md](stdlib.md#stdjson).
- The text of a handle is `<handle:N>`, `N` being its kind, and of a lambda `<fn>`.

Known differences, none of which a kernel relies on:

- The text of some errors: a malformed response header, a failed DNS lookup, and `write_atomic` (the name of its temporary file).
- Connecting, the TLS handshake and DNS are not under `timeout_ms`.
- A server that answers and closes before it has read the whole request: the VM gives an `Err` or the answer, depending on timing; the native client gives the answer.
- `+`, `-` and `*` are proved not to overflow, so what each backend would do on overflow is never reached; the two have not been compared there.

## The studio

`anima studio file.anm` serves a web studio from the same binary (default `127.0.0.1:7788`): UML class diagrams, statecharts, an animation of the tokens of a workflow net, and sequence diagrams of counterexamples.

## The command line

```
anima check   [--explain] [--json] [--save-cex trace.json] <file.anm>
anima run     [--seed N] [--animate] [--replay trace.json] <file.anm> [-- args...]
anima build   [-o out_bin] [--emit-c out.c] <file.anm>
anima disasm  <file.anm>
anima uml     [--format mermaid|dot] <file.anm>
anima export  [--fsp out.fsp] [--pnml out.pnml] <file.anm>
anima studio  [--addr 127.0.0.1:7788] <file.anm>
anima stdlib
```

| Command | Does |
|---|---|
| `check` | runs the three kernels; `--explain` prints each proof, `--json` a machine-readable report, `--save-cex` the counterexample trace |
| `run` | verifies, then runs on the VM |
| `build` | verifies, then compiles to a native executable |
| `disasm` | prints the bytecode |
| `uml` | prints the UML views as Mermaid or DOT |
| `export` | writes the processes as `.fsp` (LTSA) and the workflow nets as `.pnml` |
| `studio` | serves the web studio |
| `stdlib` | lists the standard modules |
