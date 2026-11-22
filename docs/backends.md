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
- `&`, `|`, `^`, `<<`, `>>` and `~` are those of a two's-complement int64: `>>` brings the sign in, in C too, where the standard leaves that open. A shift by a count outside `0..63`, which no verified program reaches, stops both with the same message.
- The HTTP client reads an answer as Go's `net/http` does, well formed or not: the same status and body, or an `Err` with the same words. A chunked body is decoded, a body is exactly as long as its `Content-Length` (`unexpected EOF` when the server stops short), 204 and 304 have none, a 1xx answer is passed over, and `timeout_ms` is for the whole request, not for each read. Neither follows a redirect, decompresses a body or uses a connection twice: [stdlib.md](stdlib.md#stdrequests). A test gives both the same answers, listed and changed at random, whole and in pieces (`TestE2EHTTPAnswerParity`).
- No `str` holds a NUL byte, and a text read from outside that holds one is refused the same way: [stdlib.md](stdlib.md#a-str-holds-no-nul).
- A request is sent whole, whatever the length of its body.
- A request is the same bytes from both: the URL read as Go's `net/url` reads it, escaped, without its fragment, `user:password@` as an `Authorization` header, an IPv6 address in brackets, the same headers; and a text that is no URL, a host that cannot be found or reached, and a lookup, connection or handshake that runs out of `timeout_ms` are the same `Err`: [stdlib.md](stdlib.md#stdrequests). Neither uses a proxy or HTTP/2. A test gives both the same URLs, listed and changed at random, and compares what the server got (`TestE2EHTTPRequestParity`).
- A TCP socket is of the host it is asked for, of the same family, at the same port, or it is the same `Err`; and what is done with it ends the same way in the same words: a wait that runs out, a peer that closed or reset, a send nobody reads: [stdlib.md](stdlib.md#stdsocket). Tests give both the same hosts, listed and changed at random (`TestE2ESocketAddressParity`), and the same streams (`TestE2ESocketStreamParity`).
- A UDP socket is of the host it is asked for and of its family, and sends and hears the same datagrams, or it is the same `Err`: [stdlib.md](stdlib.md#udp) (`TestE2EUDPSocketParity`, `TestE2EUDPEchoWithAPeer`). A view is built of the same bytes, and two views are equal when their bytes are (`TestE2EByteBuildingParity`). Only `bytes.random` gives each its own bytes.
- A send to a peer that has gone is an `Err`, not a `SIGPIPE` that ends the program. Only standard output keeps that signal, as in Go.
- A `?` that returns early closes nothing on either backend.
- A lambda copies the variables its body names when it is made; one held in a workflow variable or written in a fork branch is called as anywhere else.
- `run_workflow` runs the workflow it names, and a `merge` node is run by both.
- A value that holds itself is printed and encoded with an end, the same way: [language.md](language.md#a-value-may-hold-itself).
- `json.encode` writes the same text, and `json.decode` reads a text as the same value or refuses it with the same message: [stdlib.md](stdlib.md#stdjson).
- The text of a handle is `<handle:N>`, `N` being its kind, and of a lambda `<fn>`.
- An HTTPS server is the one the URL names or the request is an `Err`, with the same message: [stdlib.md](stdlib.md#stdrequests).

Known differences, none of which a kernel relies on:

- The text of some errors: a DNS lookup that fails for another reason than that there is no such host, a TLS handshake that fails for another reason than the server's certificate (`remote error: tls: handshake failure` and the like on the VM, `tls handshake failed` natively), a certificate refused for a reason other than its dates, its names, its authority, its key usage or the length of its line of authorities (a name an authority may not sign for is `permitted subtree violation` natively), what the VM adds to `certificate signed by unknown authority` (`(possibly because of ... while trying to verify candidate authority certificate ...)`), and `write_atomic` (the name of its temporary file).
- A few certificates the VM takes and the native client refuses, none the other way round in what was tried: one whose name is a `*` right under a top-level name (`*.test`), one with a `*` before a label that has a `_` (`*.a_b.test`), one whose name is written with a dot at its end, one with an RSA key of 1024 bits in it or in an authority above it (`EE certificate key too weak`; what is too weak is the system's OpenSSL setting), one whose extended key usage, or an authority's, is `any` rather than server authentication, one whose key usage does not let it sign a handshake, and, with OpenSSL 3.0.2, one with no subject that is itself among the authorities after two or more others. In `SSL_CERT_DIR` the VM reads every file, the native client the ones named by their hash (as `c_rehash` names them).
- Which address of a name is dialed first: each backend asks its own resolver (the VM Go's, the native client the system's `getaddrinfo`), and the two may order the addresses differently, or find different ones where the system's lookup is set up in a way Go's does not read. With one address, or with the same order, the two do the same.
- A server that answers and closes before it has read the whole request: the VM gives an `Err` or the answer, depending on timing; the native client gives the answer.
- `+`, `-`, `*` and `<<` are proved not to overflow, so what each backend would do on overflow is never reached; the two have not been compared there. `abs` is proved not to be of the least int, and of it both give the least int back.

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
