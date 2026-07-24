---
id: FIR-BUG-impure-elimDeadVars-reuse-token-root-gap
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: elimDeadVars-0
discovered-by: proof
first-seen: 2026-07-24
reproduction: Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean#ShadowRuntimeRel
regression: none
---

# Summary

The reachable-runtime invariant relates concrete reuse-token addresses without
requiring their live heap cells to be related, so a retained `reuse` can
succeed in the source and fault in the target.

## Minimal reproduction

Choose an address renaming that maps source location `0` to target location
`0`.  Put `.reuseToken (some 0)` in both extra-root lists, put a live
constructor cell at source location `0`, and leave the target heap empty.
Use `nextLocation := 1` on both sides and otherwise empty, equal runtime
metadata.

`ValueRel.reuseSome` relates the tokens, while `Reachable` has no root
constructor for a reuse token.  The two heaps are therefore vacuously
`HeapRel` under `runtimeRoots`, and the complete `ShadowRuntimeRel` can hold.
Calling `reuse` with a well-sized argument array succeeds on the source live
cell but `getLiveCell` reports `.deadObject 0` on the target.

## Exact commands

From the proof worktree using the pinned toolchain:

```sh
sed -n '90,125p' Fir/LeanIR/PassCorrectness.lean
sed -n '1290,1320p' Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean
sed -n '1800,1835p' Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean
lake build Fir.LeanIR.Passes.ElimDeadRuntimeRel
make bug-cards
```

The first range shows that `Reachable.root` recognizes only
`.object (.heap location)`.  The second and third show that `runtimeRoots`
passes reuse tokens through unchanged and that `ShadowRuntimeRel.heap` is
indexed only by those reachable roots.

## Expected semantics

A retained `reuse` whose token and arguments are related should take matching
successful steps.  In particular, a related concrete token must keep its
referenced live constructor cells inside the paired reachable heap, because
the token grants the next operation permission to overwrite that cell.

## Actual behavior

`ValueRel.reuseSome` records only the address-renaming equation.
`runtimeRoots` includes the token value itself, but `Reachable.root` ignores
it.  Consequently `ShadowRuntimeRel` does not require either heap to contain
the token's cell and cannot transport a successful source `getLiveCell` to
the target.

## Proof or differential evidence

The retained-`reuse` runtime proof reaches the concrete-token branch with
`rho.forward leftLocation = some rightLocation`, but
`related.heap.1 leftLocation ...` requires a
`Reachable left.heap (runtimeRoots left leftExtra) leftLocation` premise.
Membership of `.reuseToken (some leftLocation)` in `leftExtra` cannot produce
that premise.  The minimal runtime pair above demonstrates that this is not
merely a missing lemma: the current invariant admits a target with no cell at
the mapped location.

## Semantic impact

The current non-lockstep invariant cannot prove retained `reuse` steps, so
whole-pass correctness for `elimDeadVars` stops after retained `reset`.
Actual compiler traces normally obtain the token from `reset`, but that
provenance and the continued cell ownership are not represented in the
machine relation.

## Classification and triage

This is provisionally `fir-semantics`: interpreter behavior is coherent, but
the proof-facing reachable-root contract omits the heap capability carried by
a concrete reuse token.  Triage should choose between expanding runtime roots
with token-backed heap references or adding an equivalent explicit
token-to-live-cell invariant to `ShadowRuntimeRel`.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved.  Add the minimal related-runtime counterexample as a permanent
regression, then require concrete reuse tokens to keep their mapped cells in
the paired heap relation.
