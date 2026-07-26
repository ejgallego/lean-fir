---
id: FIR-BUG-wasm-none-reset-erased-child-release
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: a90a988
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-25
reproduction: Fir/LeanIR/Runtime.lean
regression: Fir/LeanIR/InterpreterExamples.lean#resetErasedFieldProgram
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

No workaround remains. Wasm proofs may remove the former
`fault ≠ .expectedObject` exclusion after rebasing onto the shared repair.

## Upstream tracking

none

## Resolution and regression

`releaseResetField` now makes the reset ownership protocol explicit:
`.erased` is the canonical non-owning object-field sentinel and performs no
reference-count transition, while all other values retain the existing
checked-decrement behavior. `reset` uses this helper for every cleared prefix
slot.

`resetErasedFieldProgram` allocates a constructor containing an erased field,
resets that field, reuses the retained allocation, and reads the replacement
value. The interpreter now returns the replacement rather than faulting with
`expectedObject`, matching recursive semantic ownership release and the
concrete Wasm runtime.

The validation-owned `machine-reset-erased-field` case independently compares
the exact final-impure `ctor`/`reset`/`reuse` path with a native Lean
replacement and pins its executed form trace and multiplicities.

The concrete reset refinement consumes the same `releaseResetField` fold.
Its ordered ownership theorem treats erased/physical-zero slots as matching
no-ops while preserving the existing checked decrement proof for every
non-erased slot.
