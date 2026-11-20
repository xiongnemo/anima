# Why Anima exists, and the decisions behind it

*Anima* is Latin for soul or breath. The aim is a language in which the design of a system (its data invariants, its protocols, its state machines, its workflows) is part of the program and is checked, not a diagram that is drawn once and left behind.

## Motivation

### Memory safety is not correctness

A borrow checker removes one class of faults: use after free, out-of-bounds access, double free. What is left when those are gone is logic:

- lock orders that deadlock or starve;
- handles leaked on an error path or an early return;
- state machines that take a transition they should not (a payment released before it is charged);
- two sides of a protocol that assume different things.

The more a system is distributed, concurrent or driven by a workflow, the larger that share is. Moving to a memory-safe language does not touch it.

### A fuzzer needs an oracle

Memory corruption comes with a free oracle: the program crashes, or a sanitizer reports. A logic fault does not. A balance that goes negative, a workflow that never completes or a check that is skipped all end in a normal exit, and a fuzzer passes over them however many times it takes that path.

Contracts are that oracle. An invariant written down is something a prover can prove, and where it cannot, something a test or a fuzzer can watch.

### Deterministic checking of generated code

Code written by a language model, and reviewed by another, is a guess checked by a guess. The division of work Anima is built for:

- the model (or the engineer) writes the design: ranges, `requires` / `ensures`, invariants, state machines, workflows;
- the kernels decide, deterministically: the program passes, or there is a counterexample trace that can be replayed (`--save-cex`, `--replay`) and handed back for repair.

Nothing runs until the kernels pass.

### Who verifies the specification

A proof shows that the implementation meets the specification. It says nothing about a specification that is wrong or says too little, and a contract that nothing can violate passes every check. So the work that remains for people is the design itself: what the invariants of the data are, what protocol guards a shared resource, where recovery ends. The language is meant to be the place where that is written. Checks that a specification is not vacuous are on the [roadmap](#roadmap).

## Decisions

### The code is the model

`entity` (with `rel` relations), `machine` / `monitor`, and `workflow` are part of the language. One `.anm` file is projected to a UML class diagram, state machine diagrams, an activity diagram / Petri net, and a sequence diagram for each counterexample (`anima uml`, `anima studio`).

### A procedural core with functional ergonomics

- Indentation, assignment, `if`, loops: what a systems programmer expects.
- Algebraic data types and exhaustive `match`.
- Pipelines: `xs |> filter((x) => x > 0) |> sum()`.
- Short lambdas: `(x) => x * 2`.
- `Result[T, E]`, `Option[T]` and `?`.

### No external solver

Wrapping Z3 would have been the short way. It would also have ended the single static binary (a native library per platform), and left the proofs to a general solver whose timeouts are hard to predict. The prover is written in Go for what the language needs: an interval / octagon domain, a CDCL SAT solver, an exact rational simplex and integer branch and bound. Division bounds such as `lo <= num / den <= hi` are reduced to linear constraints (`lo * den <= num` and `num < (hi + 1) * den`, for `den >= 1`, `num >= 0`).

### Two backends

As OCaml has `ocamlrun` and `ocamlopt`: a bytecode VM that is deterministic and can replay a trace, and a native backend through C11 for programs that are deployed. See [backends.md](backends.md).

### One binary

The verifier, both backends and the studio (embedded, no Node.js or front-end build) are one executable.

## Soundness is the foundation

A checker that accepts a program that then goes wrong is worth less than no checker, because its answer is trusted. The rules the project holds itself to:

- **A declared fact is proved again wherever it could stop being true.** A range is proved at every assignment, an invariant wherever an entity is handed on, a type wherever a value is written into a container. (A fact that is checked where it is declared and not after a later write is the kind of hole that stays open for years.)
- **Where the kernel does not know, it says so.** A value it cannot follow is an arbitrary value of its type, and a value with no type is only passed on, never operated on.
- **A cautious rule is preferred to an unsound one.** Several rules refuse programs that are correct (a workflow that loops, an in-place write in a fork branch) because the precise rule was not yet proved safe. They can be relaxed later; an accepted fault cannot be recalled.
- **Every accepted program that went wrong is kept.** It becomes a file in `tests/bugs` with the error it must now give.
- **The two backends are held to each other.** The same source is run on both in tests, so a fault in one shows as a difference.

## Roadmap

The language is being grown by writing six programs with it, each of which needs something new:

| Program | Needs |
|---|---|
| Concurrent HTTP server (done) | ownership of handles across threads |
| STUN NAT detection | UDP sockets, bit operations |
| Mini Redis, then Raft replication over three nodes | a protocol parser, replicated state |
| DNS server | termination of name-compression parsing |
| TFTP server | timeouts and retransmission; the duplicate-ACK fault as a model |
| Peer-to-peer chat node | no leader: vector clocks for causal order, changing membership |

Beyond those:

- **Specification checks in the manner of Alloy**: vacuity (a contract nothing can violate), multiplicity obligations on relations, and bounded relational analysis.
- **Bounded model checking of distributed protocols**: Raft, Paxos and two-phase commit unfolded over bounded delays.
- **A repair loop for generated code**: counterexamples and errors fed back to a model that proposes the fix, and the kernels deciding again.
- **A policy runtime for agents**: a plan of tool calls is run only when its workflow is sound and its handles are accounted for.
- **Self-hosting**: parts of the toolchain written in Anima and verified by it.
