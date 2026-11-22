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
- It is the time for the whole request.
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

`json.decode` reads these escapes back, a `\uXXXX` pair of surrogates as one character and half a pair as U+FFFD. A text with `\u0000` in a string or a key is an `Err` on both backends: a string of the native backend ends at a NUL.

`json.decode[EntityType]` gives a value typed as the entity, so it checks all of it at the boundary, the same way and with the same `Err` text on both backends:

| Declared | JSON |
|---|---|
| `int`, `int[lo..hi]` | an integer, within the range |
| `bool`, `str` | `true` or `false`, a string |
| `list[T]` | an array, every element a `T` |
| `map[str, T]` | an object, every value a `T` |
| `Option[T]` | `null` or a field that is absent is `None`, anything else is a `T` and gives `Some` of it |
| an entity | an object with every field that is not an `Option`, each as declared, and the `invariant` of the entity holds |

- The `Err` names the part that is wrong: `schema violation: Order.lines[1].qty=0 below minimum 1`, `schema error: field Order.tags["a"] must be str`, `schema error: missing field Order.customer.name`, `entity invariant violated for Pair on JSON input`.
- A member of the object that the entity does not declare is skipped.
- Only an entity is named, and only one made of the types above: `json.decode[int]`, or an entity with a `Result`, another variant, a handle or a `map[int, T]` field, is refused by the checker, as there is no rule to check it by.
- What `json.encode` writes of such an entity is read back by `json.decode`, except that `Some(None)` is written `null` and read as `None`.

Without a type, what `json.decode` gives is of unknown type: [language.md](language.md#values-of-unknown-type).

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
