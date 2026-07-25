---
id: FIR-BUG-wasm-none-reset-erased-child-release
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: a90a988
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-25
reproduction: Fir/LeanIR/Runtime.lean
regression: Fir/Wasm/Concrete/FaultCorrectness.lean
---

# Summary

Reset disagrees across the shared FIR runtime and the concrete Wasm runtime
when the released constructor prefix contains an erased ownership slot.

## Minimal reproduction

Construct a live, ordinary, uniquely owned constructor whose first
`objectFields` entry is `.erased`, and call `reset runtime 1` on it. FIR reset
passes the saved field to `decValueOnce`, which returns
`.error .expectedObject`.

Represent the same field with the ABI's canonical physical zero and call
`resetObject state 1`. Concrete checked decrement treats the erased sentinel
as a no-op, so reset succeeds and returns the nonempty reuse token.

## Exact commands

The mismatch is exposed while elaborating the public reset child-fault
refinement in:

```text
Fir/Wasm/Concrete/FaultCorrectness.lean
```

The semantic equation reduces through
`Fir.LeanIR.Impure.decValueOnce runtime .erased true` to
`.error .expectedObject`; the related concrete equation reduces through
`decrementReferenceOnce state Word32.zero true` to `.ok state`.

## Expected semantics

Erased is an admissible constructor object-field ABI kind and owns no heap
reference. Reset child release should skip it, consistently with recursive
constructor release in `decLocationFuel` and concrete checked decrement.

## Actual behavior

FIR reset uses the public `decValueOnce` helper, whose non-object branch
reports `.expectedObject`. Concrete reset uses checked decrement, whose erased
sentinel branch is the required ownership no-op.

## Proof or differential evidence

`OwnershipValuesRel` admits `.erased`, but an unconditional
`foldlM_public_fault_refines` theorem is false: FIR can stop at
`.expectedObject` while the concrete fold continues successfully.

## Semantic impact

Valid constructors with erased fields can make interpreter reset fault while
the concrete Wasm runtime succeeds. Exact reset fault correctness must exclude
`.expectedObject` until the shared semantic contract is repaired.

## Classification and triage

This is a shared semantic-contract discrepancy, not a proof-exhaustiveness
issue. The likely clean fix is for reset to release only heap object
references, matching `HeapObject.ownedValues` traversal, but that change is
owned by the integration lane.

## Workaround

The Wasm proof states the mapped child-release theorem with
`fault ≠ .expectedObject`; no runtime behavior is weakened or duplicated.

## Upstream tracking

none

## Resolution and regression

Open.
