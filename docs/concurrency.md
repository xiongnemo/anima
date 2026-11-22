# Concurrency models: the FSP / LTS kernel

Processes are written as state machines and composed into a `system`; the kernel builds the labelled transition system of the composition and checks it. The notation follows FSP and the LTSA tool of Magee and Kramer.

Handles (sockets, files, thread pools) are checked by the same kernel: see [ownership.md](ownership.md).

## What is written

| Declaration | Meaning |
|---|---|
| `machine` | a process: states and the actions that move between them |
| `monitor` | a process with guarded actions over control variables, and a state `invariant` |
| `property` | a safety property: a process that the system must never leave (any other trace reaches `ERROR`) |
| `progress P = {a, b}` | a progress property: one of the actions can always still happen |
| `system` | a parallel composition (`compose:`) and what to check of it (`check:`) |

From `examples/single_lane_bridge.anm`:

```
property OneWaySafety:
    state Empty:
        on red_enter -> RedBusy
        on blue_enter -> BlueBusy
    state RedBusy:
        on red_exit -> Empty
    state BlueBusy:
        on blue_exit -> Empty

progress RedProgress = {red_enter}

system SingleLaneBridge:
    compose:
        red: RedCar
        blue: BlueCar
        ctrl: BridgeController
    check:
        deadlock_free
        satisfies OneWaySafety
        satisfies RedProgress
        ltl: always (red_enter -> eventually red_exit)
```

A `workflow` takes part in a composition through its `sync` operations (`sync VaultMutex.acquire` in `examples/escrow_service.anm`).

## What is checked

- **Safety**: the composition never reaches the `ERROR` state of a `property` (state `-1`, as in LTSA).
- **Deadlock freedom** (`deadlock_free`).
- **Progress**, under fair choice: no terminal strongly connected component (found by Tarjan's algorithm) lacks the actions of the property, which rules out starvation and livelock.
- **Bounded FLTL** formulas (`ltl:`).

Composition is the `||` of FSP, with relabelling, hiding (`hide:`) and action priority (`priority_low:`).

## Who takes part in an action

The alphabet of a machine is every action it is written with: also one in a state it never reaches, and one under a guard that never holds. A part takes part in each action of its alphabet, so an action it never offers never happens. It is not left to the other parts to do without it.

| Written | Done with |
|---|---|
| `on go` in a `machine` | every other machine and monitor of the system with `go` in its alphabet, all at once |
| `on left.get`, in a part composed as `Phil(left=f0)` | the part `f0` |
| `on f0.get` | the part `f0` |
| `on Gate.go`, `sync Gate.go` | the part of the system that is a `monitor Gate` |

- A monitor, and a part that another is bound to or names, moves only with the part that calls it, and calls no part itself: `on b.put` in it is refused. The caller's action is matched to its action of the same name.
- An instance written `B / {a -> b}` has `b` in its alphabet where its machine has `a`, and no longer `a`. It relabels only actions its machine has, each once.
- A system in which `left` is bound to no part, `f0` is no part, or no part is a `monitor Gate`, is refused: the action would be done with nothing. So is one with two parts that are a `monitor Gate`, where a part does `Gate.go`.

## What a model is written with

The guards, invariants and assignments of a `machine` or `monitor` are not run by either backend; this kernel works them out, over the values of its control variables. Nothing in them is given a value it does not have, so they are written only with what the kernel works out, and anything else is a semantic error.

- A **control variable** is an int of a range, `int[lo..hi]`, of at most 33 values: the model holds a state for each. Its first value is written with the control variables before it; with none written it is `lo`.
- An **int** is an int literal, a control variable, `-` `~` `+` `-` `*` `/` `%` `&` `|` `^` `<<` `>>`, or `abs`, `min`, `max` of ints.
- A **bool** is `True`, `False`, a comparison of two ints, `==` or `!=` of two bools, or `not`, `and`, `or`, `implies` of bools.
- A **transition** holds assignments to control variables (`n = n + 1`, `n += 1`) and `if`s of them.
- A **property** has no variables: no guard, invariant or body. Each state goes one way on an action, to a state of the property or to `ERROR`.

So a call of a `def`, `len`, a list, `in`, a `str`, an `Option` and a `bool` control variable are refused in a model. They used to be read as `0` or `False`.

The contract kernel proves of every guard, invariant, first value and assignment what it proves of a function's: no overflow, no division by zero, no shift by a count outside `0..63`, and each control variable in its range. An invariant is proved to hold, and to have a value, where the machine starts (with the first values, written or `lo`) and where each transition arrives.

A failed check gives a trace to the violation. `anima check --save-cex trace.json` saves it, and `anima run --replay trace.json` replays it on the VM.

## Export

`anima export --fsp out.fsp` writes the processes as standard `.fsp`, which LTSA reads. An action a process is written with and never offers is in its alphabet there too (`P = (...) + {go}.`).

## Examples

- `examples/single_lane_bridge.anm`: safety and progress for two kinds of cars.
- `examples/dining_philosophers_safe.anm`: the asymmetric solution is deadlock free.
- `examples/escrow_service.anm`: a mutex monitor composed with two instances of a workflow.
