# The standard library

Eight groups of modules, the same on both backends. `anima stdlib` prints the list.

How a standard function is called (by position, exactly the arguments it reads, `timeout_ms=` last) is in [language.md](language.md#standard-functions-and-handle-methods). The parameters below are the ones the semantic checker takes; one marked `?` may be left out.

## `std.fp` and the prelude: pipelines

`map`, `filter`, `fold`, `sum`, `zip`, `take`, `drop`, `find`, `any`, `all`, `flat_map`, `filter_ok`, `unwrap_or`, `and_then`, used as stages of `|>`.

- They terminate without a `decreases` clause.
- The contract kernel carries the length and the bounds of the elements through `map`, `filter`, `take`, `drop`, `sum` and an adding `fold`: see [contracts.md](contracts.md#pipelines).

Built-in functions: `abs`, `min`, `max`, `str`, `len`, `assert`, `print`.

## `std.concurrent`

| Call | Parameters |
|---|---|
| `conc.ThreadPool` | `workers`, `queue_cap` |
| `conc.Channel` | `cap?` (write `conc.Channel[T](cap=1)` to give it a type) |
| `conc.Mutex` | `value` |
| `conc.Semaphore` | `permits` |
| `conc.parallel_map` | `xs`, `f` (a function of one argument) |
| `pool.submit` | `task` (a function of no argument); gives a `Future` |
| `pool.shutdown` | |
| `future.await` | |
| `ch.send` | `value` |
| `ch.recv`, `ch.close` | |
| `m.get` | |
| `m.set` | `value` |
| `m.with_lock` | `f` (a function of what the mutex holds, giving the same) |
| `sem.acquire`, `sem.release` | |

A channel, a mutex and a future hold one type: [language.md](language.md#handles-hold-one-type). A thread pool is an owned handle and is shut down on every path: [ownership.md](ownership.md#thread-pools).

## `std.socket`

| Call | Parameters |
|---|---|
| `sock.listen_tcp` | `host`, `port` |
| `sock.connect_tcp` | `host`, `port` |
| `listener.port`, `listener.close` | |
| `listener.accept` | `timeout_ms=` |
| `stream.send_text` | `text` |
| `stream.recv_text` | `max_bytes?` |
| `stream.close` | |

Every socket has one owner that closes it on every path; none is used after it is closed or moved, and a stream is not shared between threads: [ownership.md](ownership.md).

`recv_text` gives text: what was received and holds a NUL byte is an `Err`, and is gone ([a `str` holds no NUL](#a-str-holds-no-nul)).

## `std.requests`

| Call | Parameters |
|---|---|
| `req.get` | `url`, `timeout_ms=` |
| `req.post` | `url`, `body`, `timeout_ms=` |
| `req.Session` | `pool_size?` |
| `sess.get`, `sess.get_async` | `url`, `timeout_ms=` |
| `sess.post` | `url`, `body`, `timeout_ms=` |
| `sess.close` | |
| `req.gather` | `futures` (a list) |

- `timeout_ms` is an `int[1..300_000]` and has to be given; the kernel proves the value in range (`timeout_bounds`). The same holds for `accept` on a listener.
- It is the time for the whole request. A request that runs out of it is an `Err` that says where: `... (Client.Timeout exceeded while awaiting headers)` before the head of the answer is read, `... (Client.Timeout or context cancellation while reading body)` after.
- The answer is the one the server gave. A redirect (301, 302, ...) is not followed: it is an answer with that status. A body is not asked for compressed, and one sent compressed is not decompressed.
- Each request has a connection of its own, closed after the answer, with a `Session` as without.
- A 1xx answer other than 101 is passed over: the answer is the one after it.
- An answer is read as Go's `net/http` reads one, on both backends, and one it refuses is an `Err` with Go's words: `malformed HTTP response "..."`, `malformed HTTP status code "..."`, `malformed MIME header line: ...`, `bad Content-Length "..."`, `unsupported transfer encoding: "..."`, `invalid byte in chunk length`, `unexpected EOF` and the like.
- The body is text: one that holds a NUL byte is the `Err` `text holds a NUL` ([a `str` holds no NUL](#a-str-holds-no-nul)).
- An `https://` URL is answered only by the server it names. The server's certificate has to be for that name or address, within its dates, and signed by an authority the system knows (`SSL_CERT_FILE` and `SSL_CERT_DIR` name others, to both backends). Otherwise the request is an `Err` with Go's words, the same on both backends: `tls: failed to verify certificate: x509: certificate signed by unknown authority`, `... x509: certificate is valid for a.test, *.b.test, not c.test`, `... x509: certificate has expired or is not yet valid: current time ... is after ...`. Where more than one holds, the dates come first, then the name, then the authority. The connection is TLS 1.2 or later, with a key agreed on anew for it (no plain-RSA key exchange). Whether a certificate was revoked is not asked.
- The future of `get_async` is awaited or gathered on every path: [ownership.md](ownership.md#futures).

## `std.json`

| Call | Parameters |
|---|---|
| `json.encode` | `value` |
| `json.decode` | `text`; `json.decode[EntityType](text)` to decode into an entity |

`json.encode` writes the same text on both backends:

- an entity and a map are objects with their keys sorted, a list is an array;
- a string is escaped as Go's `encoding/json` escapes it: `<`, `>`, `&` and the control characters with no short escape are `\u00XX`, a byte that is not UTF-8 is `\ufffd`;
- `Some(x)` is `x` and `None` is `null`; any other variant is the string of its text, so `Circle(3)` is `"Circle(3)"`;
- a value met again inside itself is `null`.

`json.decode` reads a JSON text as RFC 8259 defines one, with the same parser on both backends: a text is the same value on both, or an `Err` with the same message on both.

- The text is one value with only spaces, tabs and line ends around it. `{"a":1} x`, `[1,]`, `{"a":1,}`, a comment, `NaN` and a text that is empty are each an `Err`.
- A number is an `int`: `-0`, `10`, anything from `-9223372036854775808` to `9223372036854775807`, read exactly. `01`, `+1` and `.5` are not JSON. `1.0`, `1e2` and a number outside 64 bits are JSON but no `int`, and are an `Err` wherever a value is made of them; in a member that the entity of `json.decode[E]` does not declare they are skipped with it.
- A string holds the escapes `\" \\ \/ \b \f \n \r \t \uXXXX` and no other, and no control character unescaped. A `\uXXXX` pair of surrogates is one character and half a pair is U+FFFD. A byte that is not UTF-8 is U+FFFD.
- A text with `\u0000` in a string or a key is an `Err`: [a `str` holds no NUL](#a-str-holds-no-nul).
- Of two members of an object with one key, the last is kept.
- Arrays and objects are nested at most 1000 deep.
- The `Err` says where: `invalid JSON at offset 7: unexpected character`, with the offset in bytes. What is wrong is one of `unexpected character`, `unexpected end of text`, `invalid escape`, `control character in string`, `NUL in string`, `number is not an int`, `nested too deep`.

`json.decode[EntityType]` gives a value typed as the entity, so it checks all of it at the boundary, the same way and with the same `Err` text on both backends:

| Declared | JSON |
|---|---|
| `int`, `int[lo..hi]` | an integer, within the range |
| `bool`, `str` | `true` or `false`, a string |
| `list[T]` | an array, every element a `T` |
| `map[str, T]` | an object, every value a `T` |
| `Option[T]` | `null` or a field that is absent is `None`, anything else is a `T` and gives `Some` of it |
| an entity | an object with every field that is not an `Option`, each as declared, and the `invariant` of the entity holds |

- A text that is not an object is `schema error: Order must be object`.
- The `Err` names the part that is wrong: `schema violation: Order.lines[1].qty=0 below minimum 1`, `schema error: field Order.tags["a"] must be str`, `schema error: missing field Order.customer.name`, `entity invariant violated for Pair on JSON input`.
- A member of the object that the entity does not declare is skipped.
- Only an entity is named, and only one made of the types above: `json.decode[int]`, or an entity with a `Result`, another variant, a handle or a `map[int, T]` field, is refused by the checker, as there is no rule to check it by.
- What `json.encode` writes of such an entity is read back by `json.decode`, except that `Some(None)` is written `null` and read as `None`.

Without a type, `json.decode` gives the value of the text, whatever it is: `null` is `None`, an object is a map, an array is a list. It is of unknown type: [language.md](language.md#values-of-unknown-type).

## `std.bytes` and `std.crypto`

| Call | Parameters |
|---|---|
| `bytes.from_str` | `text` |
| `bytes.from_hex` | `hex` |
| `bv.len` | |
| `bv.read_u8`, `bv.read_u16_be`, `bv.read_u32_be` | `offset` |
| `bv.slice` | `lo`, `hi` |
| `crypto.sha256` | `text` |
| `crypto.hmac_sha256` | `key`, `text` |
| `crypto.constant_time_eq` | `a`, `b` |

Every read of a `ByteView` and every slice is proved inside the view: [contracts.md](contracts.md#byte-views).

## `std.fs`, `std.cli`, `std.time`

| Call | Parameters |
|---|---|
| `fs.open` | `path`, `mode?` |
| `fs.read_text` | `path` |
| `fs.write_atomic` | `path`, `text` (written to a temporary file, then renamed) |
| `file.read_text`, `file.close` | |
| `file.write_text` | `text` |
| `cli.args` | |
| `cli.env_get` | `name` |
| `time.now_ms` | |
| `time.sleep_ms` | `ms` |

A `File` is an owned handle and is closed on every path: [ownership.md](ownership.md).

## A `str` holds no NUL

A `str` is text, and no text holds a NUL byte. The native backend's strings end at one, so a text with a NUL in it was cut there: a shorter text than on the VM, with another length, other bytes and another hash. Where a text comes in from outside the program, one that holds a NUL is refused instead, the same way on both backends:

- `fs.read_text`, `file.read_text` and `stream.recv_text` give `Err("text holds a NUL")`, and so does a request whose answer has such a body.
- `json.decode` gives an `Err` for `\u0000` in a string or a key.
- A source file with a NUL byte in it is not read: `file.anm:2:14: NUL byte in source`.

Nothing else makes a `str` out of bytes, so no `str` of a running program holds one. There is no call yet that reads a file or a socket as bytes.
