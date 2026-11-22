# The language: what the semantic checker settles

Before any kernel runs, the semantic checker gives every value a type and refuses what the two backends could not run as written. The reason behind most rules here is the same: an operation on a value of the wrong sort does not fail when the program runs, it gives `()` or `None` or runs on whatever the value is, and the kernels would go on reasoning about the type the source declared.

Contents: [Names](#names) · [Variables](#variables) · [Comparisons and operators](#comparisons-and-operators) · [Calls](#calls) · [Entities](#entities) · [Lambdas](#lambdas) · [Values of unknown type](#values-of-unknown-type) · [Open parts of a type](#open-parts-of-a-type) · [Handles hold one type](#handles-hold-one-type) · [A value may hold itself](#a-value-may-hold-itself) · [Returns](#returns) · [Matches](#matches)

## Names

A name is declared once. Sema, the kernels and the two backends each look a name up in their own way, so a name that is declared twice could mean one thing to the proof and another to the program that runs.

- **What is called.** A function, an entity, a variant and a built-in function (`len`, `print`, `assert`, `str`, `to_str`, `abs`, `min`, `max`, `Some`, `Ok`, `Err`) share one set of names: `def len(...)`, two `def f`, an entity and a function of one name, or one variant name in two types is an error.
- A function may be named like a pipeline stage (`def take(xs: list[int], n: int)`): `xs |> take(2)` and `take(xs, 2)` then call that function, on both backends. An entity or a variant may not.
- **Types.** A `type`, an entity and a port share one set of names, with the built-in types (`int`, `str`, `list`, `Option`, ...).
- **Models.** Two machines, two properties, two progress properties, two workflows or two systems of one name are an error. A workflow and a function may share a name (`run_workflow W()` names the workflow).
- **Within a model.** No two states of a machine, a monitor, a property or a port protocol, no two control variables of a monitor, no two pools of a workflow and no two parts of a system have one name. Of two states of one name the model kept the last, so a second state could allow what the first forbids.
- **Within a declaration.** No two parameters of a function, a workflow, a lambda or an extern function, no two fields of an entity or of a variant, no two extern functions of a port, no two nodes of a workflow and no two branches of a `fork` have one name. One pattern binds a name once (`C(r, r)` is an error).
- A local variable may still have the name of a function; it then cannot be called (see [What can be called](#what-can-be-called)).

## Variables

- **One sort.** A variable holds values of one sort from its first assignment on: `x = 5` and later `x = "five"`, `x = True` or `x = [1]` is an error. So is a loop variable or a name in a pattern that would write a variable of another sort (`for x in names:` after `x = 5`).
- **One element type.** A list, a map or a variant keeps the type of its elements the same way.
- What a variable holds after an `if`, a loop or a `match` is then of the one type, whichever branch ran.
- **Scope.** A name first assigned inside a branch or a loop body ends with it.
- **Pattern names write variables.** A name in a pattern writes the variable of that name when its arm matches, so `x = 5` followed by `match o: Some(x) -> ...` leaves in `x` what `o` held. The contract kernel forgets the old value, in a match statement and a match expression alike.
- **Ranges are kept.** An int variable with a range keeps it. The range comes from its declaration (`y: int[1..9] = 5`), its parameter, or the list or variant a loop or a pattern takes it from. The kernel proves every later value in it (`y = n` needs `n` in 1..9), and a second declaration, a loop variable or a pattern name must have the very range.
- In return, a loop that assigns the variable knows it is in its range on every pass: `i: int[0..10] = 0` followed by `while i < 10: i = i + 1` is proved without overflow.
- A variable first assigned without a type has no range.

## Comparisons and operators

- `==` and `!=` compare two values of one sort: lists, maps and variants by what they hold, an entity is equal to itself only.
- `<`, `<=`, `>`, `>=` order two integers or two strings (byte by byte).
- `and`, `or`, `implies` and `not` take booleans.
- `x in xs` looks for an element of a list, a key of a map or a part of a string.
- `&`, `|`, `^`, `<<`, `>>` and `~` work on the bits of an `int`, and take nothing else: `True & False` and `"a" | 1` are errors. The result is an `int` with no range of its own; the ranges the contract kernel knows are in [contracts.md](contracts.md#bit-operators).
- Anything else (`xs == 5`, `"a" < 5`, `1 and 2`) is an error.

The contract kernel reasons about the equality of integers, strings and booleans. Of lists, maps, entities and variants it assumes nothing, as they change in place.

### Precedence

From the loosest to the tightest, as in Python:

| Operators | |
|---|---|
| `\|>` | pipeline |
| `implies` | |
| `or` | |
| `and` | |
| `not` | |
| `==` `!=` `<` `<=` `>` `>=` `in` | |
| `with` | a copy of an entity |
| `\|` | bitwise or |
| `^` | bitwise exclusive or |
| `&` | bitwise and |
| `<<` `>>` | shifts |
| `+` `-` | |
| `*` `/` `%` | |
| `-x` `~x` | |

So `a | b ^ c & d << 1 + 2` is `a | (b ^ (c & (d << (1 + 2))))`, and `x & 0xFF == 0` is `(x & 0xFF) == 0`.

## Calls

### How arguments are bound

- Arguments are type-checked against the parameters they are bound to: a keyword argument by its name, the piped value of `x |> f(a)` first.
- The fields of a variant and the arguments of `run_workflow` are bound by position, so a keyword there has to name the one at its place.
- A variant is made with all of its fields.

### What can be called

What is called has to exist when the program runs.

- Only a function or a variable holding a lambda can be called.
- A function that is not called is not a value: write `(v) => f(v)` to pass one on.
- A name that is both a variable and a function cannot be called (both backends would call the variable; rename it).
- A value has no members but the ones its type has (`s.upper()` is an error).

### Lambdas, built-in functions and pipeline stages

- A lambda, a built-in function (`abs`, `min`, `max`, `str`, `len`, `assert`) and a pipeline stage are given exactly the arguments they take, by position. An argument that is not given would be `None` when the program runs.
- A stage's function has one parameter (`fold`: two).
- `fp.take(xs, 2)` is `xs |> take(2)`, and `x |> g(a)` is `g(x, a)` for a lambda or a built-in function too. The kernels are given that call: `x |> abs()` has the obligation of `abs(x)`, and what `p |> keep` gives may be `p` itself.
- An entity or a variant is made by a call, not by a stage.
- `unwrap_or` gives what the variant holds or the default, so an int has the range of both, and a list, a map or a variant default has the very type of what is held. `fold` likewise: what it starts with or what its function gives.
- The function of `and_then` gives the same kind of variant as it is given.

### `mut` arguments

A call may change what it receives as `mut`. What the caller knows afterwards is in [contracts.md](contracts.md#calls). The checker adds these rules:

- So that the order of a read and the change never decides a result, a variable passed as `mut` cannot be used elsewhere in the same statement: `total = box.v + reset(mut box)` is rejected; put the call in a statement of its own.
- The same holds for another name of what is passed: after `c = b`, `if b.n == 0 or zero(mut c):` is rejected, since the callee may write the field the condition has read.
- A `mut` parameter cannot be assigned a new value.
- Only a pipeline stage (`xs |> map(x => f(mut s))`) may pass an outer variable as `mut` from a lambda.

### Standard functions and handle methods

- A function of a standard module or a method of a standard handle (`time.sleep_ms(5)`, `conn.send_text("x")`, `pool.submit(() => f())`) takes its arguments by position and exactly those it reads, each of the kind it reads.
- A keyword may only name the parameter in that place (`conc.ThreadPool(workers=2, queue_cap=4)`), and `timeout_ms=` comes last.
- Piped, `x |> o.f(a)` is `o.f(x, a)` and is checked as that call.
- Such a function is only there to be called: `g = time.sleep_ms` is rejected, write `(ms) => time.sleep_ms(ms)`.
- `pool.submit(task)` gives a `Future` of what the task gives, `conc.parallel_map(xs, f)` a list of what `f` gives for an element of `xs`, and the function of `with_lock` is checked with what the mutex holds.

The modules are listed in [stdlib.md](stdlib.md).

## Entities

An entity is made by a call of its name, with one value for each of its fields: `Account(balance=10, frozen=False)` or `Account(10, False)`.

- An argument is bound to the field it names, else to the one at its position, as both backends do. A field given twice, a field given no value, an argument past the last field and a name that is no field are errors: a field that is given nothing would hold no value at all, whatever its type says.
- Each argument has to be of the type of its field, given by name or by position. The range of an `int[lo..hi]` field and the `invariant`s of the entity are proved of the arguments by the contract kernel ([contracts.md](contracts.md#entity-invariants)).
- `mut` and `own` are for the parameters of a function, not for a field.
- `p with {d: 3, s: "b"}` is a copy of the entity `p` with those fields replaced. Its base is an entity, and it names a field once, with a value of the field's type.
- **A relation is a field.** `rel buyer -> 1 Customer` is a field of type `Customer`, `rel backup -> 0..1 Customer` one of type `Option[Customer]`, and any other multiplicity (`*`, `0..*`, `1..*`, `3`, `2..5`) one of type `list[Customer]`. It is given where the entity is made, read and assigned like any field, written and read by `json`, and may not be named like another field.
- A multiplicity is `1`, `0..1`, `*`, or a count `n`, `n..m` or `n..*` with `n <= m` and `m >= 1`. How many entities a `list` relation holds is not checked yet: `1..*` and `2..5` say what the diagram shows, and nothing is assumed from them.

## Lambdas

A lambda with parameters that is given a name (`g = (v) => v > 1`) has no declared parameter types.

- It takes the types of its **first use**, a call or a stage, and its body is checked with them.
- Every later use gives it those types.
- A use in the body of another named lambda, with a parameter of that one or something that holds it (`k = (v) => g([v])`), is not its first: it is checked when `k` is first used.
- So the first use has to say them whole: `g(None)` or `g([])` first is refused. Use it first with a value of a declared type.
- The name is only called or given to a stage (`xs |> filter(g)`), not stored, passed or assigned again.

A lambda copies the variables its body names when it is made, on both backends: after `k = 1`, `g = (v) => v > k`, `k = 5`, the call `g(2)` is `True`.

## Values of unknown type

Some values have a type nothing says:

- what `recv` gives on a `conc.Channel(cap=1)` made without a type;
- what `json.decode` gives without one;
- what an `Option` or `Result` written without its type holds;
- the parameter of a lambda that is neither named nor given to a stage;
- what a function with no return type gives.

Such a value is only **bound, passed on, printed, wrapped and matched**. A condition, an operator, an index, a member, a call, a `for`, `len`, a pipeline stage, and every parameter, field, element, return and declaration that has a type refuse it, since both backends would run the operation on whatever the value is.

A variable keeps its sort here too: one that is an `int` is not given such a value by an assignment, a loop or a pattern, nor the other way round.

## Open parts of a type

`None`, `[]`, `{}` and `Ok(1)` leave a part of their type open, which no value has typed yet.

- **A variable keeps an open part as it is.** `o = None` is not given `Some(0)` later, by an assignment, a loop or a pattern, since a read placed before that in a loop would take `o` for an `Option` of any type. Write `o: Option[int] = None`.
- **Nothing that is written to has an open part inside.** `m = {}`, `xs = [None]`, `conc.Mutex(None)` and a gathered list of `Ok`s are refused: declare the type, as in `m: map[str, int] = {}`.
- `xs = []` and `o = None` that stay so need no type.

## Handles hold one type

- A `conc.Channel[T]` and a `conc.Mutex` give back what they were given, and the kernel does not follow a value through them. So `send`, `set` and the function of `with_lock` take a value whose type is already `T`: for `Channel[int[1..9]]` a literal in the range or a variable declared `int[1..9]`, not an `int`.
- `conc.Mutex(5)` holds an `int`.
- A `conc.Channel`, a `conc.Mutex` and a `Future` are references, so one is passed, returned and assigned only as a handle of the very type it holds: a `Channel[int[1..9]]` is not a `Channel[int]`.
- A variable that holds one keeps the type of what it holds: `f = pool.submit(() => 5)` is not given a `Future` of a `str` later.
- `req.gather` gives a list of a type only when its futures all give the very same one, ranges included.

Who owns a handle and who must close it is in [ownership.md](ownership.md).

## A value may hold itself

Lists, maps, entities and variants are references, so a write in place can make one hold itself: `a.kids = [a]`.

- `==` compares such values and ends ([Comparisons](#comparisons-and-operators)).
- Its text (`print`, `str`, an f-string) has `...` where the value is met again inside itself: `Node(kids=[...], v=1)`.
- `json.encode` gives `null` there.

## Returns

A function that returns a value does so on every path, with `return value`. One that ends without a `return`, or with a bare one, gives `()` whatever type it declares, while its caller is told the declared one (`def f(n: int) -> int[1..9]` with one `return 1` under an `if`, then `10 / f(0)`).

What counts as returning on every path:

- an `if` when it has an `else` and each branch returns;
- a `match` when each arm does;
- a loop only as `while True`.

So `if n > 0: return 1` followed by `if n <= 0: return 2` is refused: use `else`, or end with a `return`. A function with no return type is not concerned.

## Matches

- Every `match` has an arm for every value. Patterns nest (`Some(Some(1))`, `Set("a", True)`), and the kernel names a value no arm takes (`no arm for Some(Some(_))`).
- A literal inside a variant matches only that value.
- A match on a string, or on an int or a string inside a variant, needs an arm with `_` or a name.
- An arm with a guard covers nothing.
- A pattern has the type of what it is matched against, and a variant pattern names every field of its variant (`Circle(r, _)`): anything else is an error, not an arm that never runs.
