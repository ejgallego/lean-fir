---
id: FIR-BUG-impure-none-elimDead-release-fuel-renaming
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: e64abaf
phase: impure
pass: elimDeadVars
discovered-by: proof
first-seen: 2026-07-23
reproduction: Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean
regression: Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean#ShadowRuntimeRel.decLocationFuelBoth
---

# Summary

The reachable runtime relation proves recursive reference-count release
correct for a common fuel budget, but it does not relate the public
heap-length-derived fuel budgets of the source and target runtimes.

## Minimal reproduction

Let `left` and `right` satisfy `ShadowRuntimeRel rho left right ...`, and let
related reachable locations be selected by `rho`. The theorem
`ShadowRuntimeRel.decLocationFuelBoth` proves:

```text
decLocationFuel fuel left leftLocation = ok leftResult
  ->
exists rightResult,
  decLocationFuel fuel right rightLocation = ok rightResult
```

The public operation instead selects `left.heap.length + 1` and
`right.heap.length + 1` independently. `elimDeadVars` may remove an
unobservable allocation, so `ShadowRuntimeRel` intentionally permits those
lengths to differ.

## Exact commands

```text
lean-beam sync Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean
```

Then attempt to instantiate `ShadowRuntimeRel.decLocationFuelBoth` from a
successful `decLocation left leftLocation` and rewrite the resulting target
operation to `decLocation right rightLocation`.

## Expected semantics

Each recursive release path marks a live cell dead before visiting its owned
children. A successful path therefore cannot visit more distinct live
locations than occur in that runtime's heap. The public fuel budget should be
adequate independently on both sides, and a related successful release should
produce related results even when unreachable allocation counts differ.

## Actual behavior

`ShadowRuntimeRel` relates every reachable cell through a partial address
bijection but records no heap-length equality or release-depth adequacy fact.
Successful release is monotone when fuel is enlarged; that does not justify
shrinking a same-fuel target execution to a smaller public target budget.

## Proof or differential evidence

`ShadowRuntimeRel.decLocationFuelBoth` checks the complete same-fuel
simulation, including persistent cells, above-one decrements, count-one
parent release, and the recursive left-to-right ownership fold. The only
missing public lift is the independent fuel selection.

## Semantic impact

No runtime divergence is currently demonstrated. The gap blocks the retained
`dec` machine matcher and therefore the whole-pass non-lockstep simulation.

## Classification and triage

This is currently classified as a FIR-semantics proof-interface candidate.
The recursive runtime function appears operationally correct, but its public
fuel wrapper exposes no adequacy theorem strong enough for a relation that
intentionally forgets unreachable allocations. The proof track owns the local
relational theorem; a general runtime theorem would require integration-owner
coordination.

## Resolution design

Prove a fuel-adequacy/irrelevance theorem for `decLocationFuel`: whenever a
release succeeds with any budget, the public `heap.length + 1` budget succeeds
with the same result. Alternatively, expose a release-depth invariant that is
established for all runtime states and preserved by allocation and cell
replacement. Requiring equal heap lengths would invalidate the intended
non-lockstep relation and is not an acceptable resolution.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in the proof track by measuring live heap entries rather than total
allocations. `decLocationFuel_liveCellCount_le` proves that release never
increases the measure, and `decLocationFuel_ok_of_liveCellCount_lt` proves by
strong induction that any successful release can be replayed with a budget
strictly larger than the current live-cell count. Since
`liveCellCount heap ≤ heap.length`, every runtime's public budget is adequate
independently.

`ShadowRuntimeRel.decLocationBoth` first applies the complete same-fuel
simulation and then replays the successful target execution at the target's
own public budget. `decValueBoth_of_related` lifts the result through repeated
decrements, and `match_decrementCodeStep` is the permanent machine-level
regression. No heap-length equality or weakened decrement readiness was added.
