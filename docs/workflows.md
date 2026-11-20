# Workflows

A `workflow` is an activity graph: steps, `choice` / `merge` (exclusive split and join), `fork` / `join` (parallel split and join) and token `pool`s. It is checked four ways:

| Checker | What it checks |
|---|---|
| Petri kernel | the graph as a workflow net: boundedness, soundness |
| Semantic checker | which variables may be read and assigned where |
| Contract kernel | every step, along every path that reaches it |
| Ownership checker | handles, along every path |

```
workflow HandleOrder(mut acc: Account, amt: TxAmount) -> bool:
    verify: sound, 1_safe
    pool verifier_slot: int[0..2] = 2

    start -> check_and_lock:
        ok = False
        if acc.balance + acc.escrow <= 990_000:
            ok = lock_funds(mut acc, amt)

    choice after check_and_lock:
        when ok -> parallel_settle
        when not ok -> reject_tx

    fork parallel_settle:
        branch commit_vault:
            sync VaultMutex.acquire
            sync VaultMutex.release
        branch risk_audit:
            acquire verifier_slot
            call AuditLog.open_log()
            call AuditLog.write_entry(amt, True)
            call AuditLog.close_log()
            release verifier_slot
    join settle_done

    step finalize_ok after settle_done -> done:
        return True
    step reject_tx -> done:
        return False
```

(`examples/escrow_service.anm`.) A function runs it with `run_workflow HandleOrder(mut acc, 250)`; the arguments are bound by position.

Contents: [The net](#the-net) · [Paths](#paths) · [Variables](#variables) · [Fork branches](#fork-branches) · [Handles](#handles)

## The net

The workflow is compiled into a place / transition workflow net: `pool`s are places with tokens, `fork` / `join` an AND-split and AND-join, `choice` / `merge` an XOR-split and XOR-join.

The Petri kernel verifies:

- **coverability** by the Karp-Miller tree: boundedness and `1_safe`;
- **soundness** after van der Aalst: *option to complete*, *proper completion*, *no dead transitions*;
- the same again through the short-circuit theorem (the short-circuited net is bounded and live), as a cross-check.

A graph the backends could not run one way only is refused here: two joins for one fork, a step with no successor, a target that does not exist, two steps after one `merge` (`DEAD TRANSITION`).

`anima export --pnml out.pnml` writes the net as ISO PNML.

## Paths

A workflow is verified one path at a time, as it runs.

- A step is checked with what is known on the way to it. It does not see what a step written above it assigned when no run goes from one to the other.
- Each branch of a `choice` is checked with its guard, and the earlier guards false.
- A `merge` node is where the branches of a `choice` come together and does nothing itself: the step after it is checked once for each path that reaches it.
- A workflow that returns a value returns one on every path (`workflow:W.returns`).
- A workflow that comes back to a node is refused (`acyclic`): a loop needs an invariant, so it is written in a function.
- A workflow has one `start`.

A sequence of k `choice`s is 2^k paths, each checked.

## Variables

A variable of a workflow is read only where every path to the read has assigned it, in the start or on each path. On a path that has not, it would be `()`.

```
step yes -> fin:
    d = 5
step no -> fin:
    print("no")
step fin -> done:
    return 10 / d      # refused: the path through `no` has not assigned d
```

The check is by name and is cautious: a nested `if c: d = 1` on a path where `d` is not yet assigned, or a loop variable of that name, is refused too.

## Fork branches

The branches of a `fork` run at the same time: on the VM each on a copy of the variables, natively as threads on the variables themselves. So:

- A branch only assigns variables that no other branch names. What each assigned is there after the join.
- A branch writes nothing in place: no field, no element, no `mut` argument, since another branch may reach the entity or list by another name. In-place work goes in a step.
- Handles (channels, mutexes) are what branches share.
- A `return` in a branch is refused: the workflow returns from a step.

## Handles

The handles of a workflow are followed along each path it can run, as the contract kernel follows it: a step finds them as the way to it left them, whatever is written above it, and every way out of the workflow must leave them closed. See [ownership.md](ownership.md).
