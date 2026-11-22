# The contract kernel: what is proved and what is known

The contract kernel turns every function, entity and workflow path into verification conditions (weakest preconditions, in the style of Ada / SPARK) and proves each one with the built-in solver. A condition that cannot be proved fails `anima check`, with a counterexample when the solver has one.

This page says what is proved, and what the kernel knows at each point of a program, since a proof can only use what it knows.

Contents: [Contracts](#contracts) · [Integers and overflow](#integers-and-overflow) · [What is known after a statement](#what-is-known-after-a-statement) · [Calls](#calls) · [Entity invariants](#entity-invariants) · [Aliases](#aliases) · [Element ranges](#element-ranges) · [Indexes](#indexes) · [Map keys](#map-keys) · [Pipelines](#pipelines) · [Byte views](#byte-views) · [The solver](#the-solver)

## Contracts

- Refinement range types: `int[0..1_000_000]`.
- `requires`, `ensures` and `old(...)` on functions.
- Entity `invariant`s.
- `mut` parameters, with exclusive access (see [Aliases](#aliases)).
- Termination of loops and recursion by `decreases`.
- Exhaustive `match`, and `choice` guards that are complete and exclusive, checked by the solver.

## Integers and overflow

`int` is a signed 64-bit integer at run time, in both backends, while proofs reason over unbounded integers.

- Every `+`, `-`, `*`, unary `-`, `/`, `%`, `sum` and `fold` therefore gets an `int64_overflow` proof obligation, and `anima check` fails when one cannot be proved.
- A product of two non-constant operands needs bounds on both (a range type or a `requires`).
- Only `fold(init, (a, x) => a + x)` is bounded as a sum.
- Every length, of a view, a list or a string, is known to fit an int64, so `n <= len(xs) - 4` is arithmetic the kernel can follow. (`n + 4 <= len(xs)` is not: `n + 4` may overflow.)

## What is known after a statement

- **Assignment.** An assignment replaces everything known about the variable. An entity or list the prover cannot follow becomes an arbitrary value of its type.
- **`if` and `match`.** Afterwards each variable holds the value of whichever branch ran.
- **Loops.** Inside and after a loop, a variable the loop assigns is known only through the loop's `invariant`s and its range type.
- **Ranges.** A variable declared with a range keeps it, and every later value is proved to be in it: see [language.md](language.md#variables).

## Calls

- A callee's `requires` is proved wherever the call is written.
- A call may change what it receives as `mut`. Afterwards the caller knows the argument's type, an entity's `invariant`, and the callee's `ensures` clauses over its parameters. Clauses about `result` are not used.
- A `?` has to leave the function's `ensures` and `mut` invariants true like any other return.

The rules on where a `mut` argument may be written are in [language.md](language.md#mut-arguments).

## Entity invariants

A function may break an entity's `invariant` between two field updates, but the invariant is proved wherever the entity is handed on:

- as an argument of a call,
- as a returned value,
- as an element or field of another value.

That is what lets a function assume the invariants of its parameters, of list elements and of matched payloads.

Where an entity is made (`Account(balance=b, frozen=f)`), its invariants and the ranges of its fields are proved of the arguments, each field standing for the argument it is given. A variable of the function that happens to be named like a field is not that field, and an argument the kernel cannot follow (a call, a nested constructor) is an arbitrary value of its type.

The room between two updates only exists for an entity that one variable alone can reach. Once it is shared, every field write has to leave the invariant true. An entity is shared when it is a loop variable, a matched payload, `r = rows[i]`, a second name `c = b`, or a variable that was put into a list, map, variant or entity.

- Writing a field of an element in place (`rows[i].x = v`, `rows[i].x += v`) has to leave the element's invariant true at once, knowing only that it held before and what the one field becomes. Otherwise build the new element and assign it.
- A field write on an object whose entity type is not known is rejected: give what holds it a type (`m: map[str, T] = {}`).

## Aliases

Entities, lists and maps are references, so `c = b` gives one entity two names.

The kernel tracks which variables are *shared*, meaning their entity can be reached another way:

- a second name;
- a loop variable or `r = rows[i]`, and the list it comes from;
- a matched payload and the matched value;
- a variable put into a list, map, variant or entity;
- an argument a call may keep (inside a `mut` argument with room for it, or through a channel or pool);
- the result of a call that was given an entity.

A write through a shared variable, in place (`rows[i].x = v`), or by a callee given it as `mut`, makes the kernel forget what it knew about the fields of every other shared variable. A variable that is the only way to reach its entity keeps its facts.

Two rules keep this sound across calls, since a function is verified with its parameters taken for separate values:

- A value received through a parameter that is not `mut` cannot be written through another name either: `c = a; c.x = 0` and `for r in rows: r.x = 0` fail `readonly_<name>`.
- A `mut` argument may not be reachable from another argument of the same call: `c = b; g(mut b, c)` fails `call_g_mut_alias`.

## Element ranges

The range of the elements of a list, of the values of a map and of the fields of a variant is part of the type, and is proved wherever such a value is made or written:

| Where | Obligation |
|---|---|
| each element of a literal given to a `list[int[1..9]]` | `list_elem_bounds`, `map_value_bounds` |
| each `xs[i] = v` and `m[k] = v` | `elem_assign_bounds` |
| each field of a constructed variant, including `Some(x)` given to an `Option[int[1..9]]` | `variant_<Name>_range` |
| what the lambda of a `map` stage yields, when the result is given a bounded list type | proved for the lambda's result |

- Because lists and maps are references, `list[int]` and `list[int[1..9]]` are different types in both directions.
- `Option[int[1..9]]` is accepted where an `Option[int]` is expected, not the reverse.
- A literal, `Some` / `Ok` / `Err` or a `map` stage takes the type of the place it is given to. On its own it holds plain `int`, as does a variable assigned an int without an annotation, so a range has to be declared to be relied on.
- A variable keeps the type of its list, map or variant when it is assigned again.
- For an un-annotated list literal the kernel still knows the hull of its elements until the list may have been written.

## Indexes

Out of range, a read `xs[i]` or `s[i]` gives `None` whatever the element type says, and a write `xs[i] = v` is dropped. So every index into a list or a string is proved inside it (`index_bounds`), reads and writes alike, a string by its bytes.

- The kernel knows the length of a literal and of what a variable or a field of one holds (`len(xs)`, `len(b.items)`, `len(s)`).
- So `if i >= 0 and i < len(b.items): b.items[i] = 0` is proved, as is `for i in 0..len(xs): xs[i]`.
- Any other list or string has to be given a name first: `row = rows[i]` and then `row[j]` under `len(row) > j`, not `rows[i][j]` or `f()[0]`.

## Map keys

A map is keyed: a write `m[k] = v` makes the key, and a read `m[k]` of a key that is not there gives `None` too. So every read of a map is proved to find its key (`key_present`):

- under `if k in m:`,
- after `m[k] = v`,
- or for a key written in the literal the map was made from.

The kernel follows a key that is a literal, an integer or a string variable, in a map that a variable or a field of one holds. Anything else is given a name first (`k = f"user:{id}"`, then `if k in m: m[k]`).

A map only gains keys, so what was found stays found. `requires: k in m` is proved at a call from what the caller knows of the map it passes.

## Pipelines

Of what a pipeline gives, the kernel knows what its last stage says:

| Last stage | Known of the result |
|---|---|
| `map` | the length is kept |
| `filter`, `take`, `drop` | a list no longer than theirs, with elements of the same range |
| `sum`, `fold(init, (a, x) => a + x)` | bounded by the elements |
| any other (a `fold` to a list, `flat_map`, a function of your own) | the length and the elements are unknown |

So `ys = xs |> take(1)` is indexed under `len(ys) > i`.

## Byte views

A read past the end of a `ByteView` is a panic on the VM and whatever lies there natively, so every `read_u8`, `read_u16_be`, `read_u32_be` is proved inside its view (`byteview_bounds`), also when the offset is piped (`off |> bv.read_u8()`).

A view never changes, and the kernel knows its length. `bv.len()` is that length, so:

- `if bv.len() >= 4: bv.read_u32_be(0)` is proved;
- a `requires: bv.len() >= 20` is proved at the call;
- `while rest.len() >= 2: ...; rest = rest.slice(2, rest.len())` eats a view to its end.

The length is known from:

- `from_str` of a string (its bytes);
- `from_hex` of a literal (an empty view when the literal is not pairs of hex digits);
- another name for a view (`w = bv`, a field `p.body`);
- a slice.

`bv.slice(lo, hi)` is proved to have `0 <= lo <= hi <= bv.len()`, and is then `hi - lo` long. Both backends would bring ends outside the view inside it, and the program would go on with a shorter view than it asked for.

A view that is not held by a variable or a field of one (`bv.slice(0, 2).read_u8(0)`, `vs[0]`) has to be given a name first, and so has the parameter of a lambda that the semantic checker has no type for.

## The solver

The prover is pure Go, with no external solver:

- an interval / octagon abstract domain (Floyd-Warshall closure);
- a CDCL SAT solver (two watched literals, first-UIP learning);
- an exact rational simplex after Dutertre and de Moura (`math/big.Rat`);
- integer branch and bound.
