# Handles and ownership

A handle is a resource of the operating system or of the runtime: `sock.TcpStream`, `sock.TcpListener`, `fs.File`, `conc.ThreadPool`. The ownership checker runs with the FSP / LTS kernel and proves that no descriptor leaks and none is used after it is closed.

Contents: [One owner](#one-owner) · [Threads](#threads) · [`?` while holding a handle](#-while-holding-a-handle) · [Thread pools](#thread-pools) · [Futures](#futures) · [Workflows](#workflows) · [Port protocols](#port-protocols)

## One owner

- Every handle has one owner, who must close it (shut the pool down) on every path.
- A handle parameter is **borrowed**: usable, but it cannot be closed or moved, unless it is declared `own`.
- `handle(own conn)`, `c2 = conn` and `return conn` **move** it, and a moved handle cannot be used again.
- Handles cannot be stored in entities, lists or other values.

See `examples/concurrent_http.anm`.

## Threads

- `pool.submit(() => handle(own conn))` moves a connection into a worker thread.
- A stream or file cannot be shared between threads.
- A listener can be lent to tasks, and is not closed until they are awaited or the pool is shut down.

## `?` while holding a handle

`?` is rejected while the function owns an open handle. Either `match` on the result and close the handle on the failure path, or do the fallible work in a function that borrows it.

A `?` that returns early closes nothing on either backend: a channel, a mutex or a session a function holds may be the caller's under another name, and the handles that must be closed are the ones `?` is refused for.

## Thread pools

A thread pool is such a handle:

- after `pool.shutdown()` it takes no task;
- a function that borrows it cannot shut it down;
- a task may borrow it (to submit more) until it is awaited.

## Futures

**Of a pool task.** Shutting a pool down waits for its tasks, so the future of a task need not be awaited:

- one given a name is awaited or gathered somewhere in the function (not in a closure);
- one that is not wanted is written `_ = pool.submit(...)`.

**Of a request.** Nothing but its await waits for a request started with `get_async`:

- it is started where its future is given a name (`f = sess.get_async(...)`);
- that future is awaited or gathered on every path, before the function returns (a `?` included) and before the last name that holds it is given another value.

Only an await the statement always runs counts:

- not one on the right of `and` or `or`, in an arm of a `match` expression, or in a loop for a request started before it;
- one in the guard of a `match` arm counts in that arm.

Where a statement has a `?`, only an await inside what the `?` is applied to (`f.await()?`) has run by then: await in a statement of its own before it.

## Workflows

In a workflow the handles are followed along each path it can run, as the contract kernel follows it: a step finds them as the way to it left them, whatever is written above it, and every way out of the workflow must leave them closed. See [workflows.md](workflows.md).

## Port protocols

A `port` declares a protocol of states and the calls that move between them (`AuditLog` in `examples/escrow_service.anm`: `open_log`, `write_entry`, `close_log`). The checker follows the protocol through the code the same way: a call is made only in a state that has it (`AuditLog.write_entry() not permitted in state "Closed"`), and the port is back in its first state when the code that opened it is left.
