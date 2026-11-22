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

The guards and the assignments of a `monitor` are not run by either backend; this kernel works them out, over the values its control variables can take. The contract kernel proves of each of them what it proves of a function's: no overflow, no division by zero, no shift by a count outside `0..63`.

A failed check gives a trace to the violation. `anima check --save-cex trace.json` saves it, and `anima run --replay trace.json` replays it on the VM.

## Export

`anima export --fsp out.fsp` writes the processes as standard `.fsp`, which LTSA reads.

## Examples

- `examples/single_lane_bridge.anm`: safety and progress for two kinds of cars.
- `examples/dining_philosophers_safe.anm`: the asymmetric solution is deadlock free.
- `examples/escrow_service.anm`: a mutex monitor composed with two instances of a workflow.
