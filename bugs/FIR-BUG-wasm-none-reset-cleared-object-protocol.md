---
id: FIR-BUG-wasm-none-reset-cleared-object-protocol
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/ResetReuseCorrectness.lean
regression: Fir/Wasm/Concrete/ResetReuseCorrectness.lean
---

# Summary

FIR reset's unique path clears every selected semantic object slot to tagged
zero, but the normal concrete heap relation cannot represent that temporary
value in a slot whose frozen ABI kind is heap-only `.object` (or `.erased`).

## Minimal reproduction

Take a related unique constructor with one field kind `.object` and call
`Fir.LeanIR.Impure.reset runtime 1 (.object (.heap location))`. The semantic
cell remains live and its first field becomes `.object (.tagged 0)`. The
concrete reset correctly writes `taggedZero`, word `1`, into the corresponding
slot and returns the allocation address as a reuse token.

Reconstructing `ConstructorObjectRel` then requires

```text
ValueRel witness .object (.word32 taggedZero) (.object (.tagged 0))
```

which is intentionally uninhabited: `.object` relates only mapped heap
locations, while `.tagged` and `.tobject` admit tagged values.

## Exact commands

```text
lean-beam sync Fir/Wasm/Concrete/ResetReuseCorrectness.lean +full
```

Attempt the unique reset `LiveHeapRel` preservation theorem after the W6.3ab
tagged/non-unique theorems. The target-cell obligation fails at the cleared
field clause described above.

## Expected semantics

Reset is a protocol transition. Its returned token grants the following
`reuse` operation access to the same allocation, and cleared references must
be released only after the parent slots no longer retain them. A correctness
relation must represent this temporary state without making the reset object
look like an arbitrary normal constructor value.

## Actual behavior

The executable semantic and concrete reset operations agree on control flow,
slot clearing, child-release order, and token encoding. However,
`LiveHeapRel` requires every semantically live cell to satisfy the normal
typed `LiveCellRel`, so it is not closed under this intermediate reset state
for all ABI-admissible constructor descriptors.

## Proof or differential evidence

`ConstructorObjectRel.objectFields` requires the original descriptor kind at
every semantic field. After reset, a cleared `.object` field contains tagged
zero; no constructor of `ValueRel` can prove the required relation. Weakening
global `.object` values to admit tagged words would erase the frozen ABI split
and make unrelated operation theorems unsound.

## Semantic impact

The current W6 proof cannot compose unique reset with in-place reuse under the
normal whole-heap relation. Executable reset/reuse examples continue to agree,
and generated well-formed code is expected to consume the token immediately,
but that protocol restriction is not represented by the current state
relation.

## Classification and triage

This is provisionally a Wasm refinement-model defect, not an observed Lean
compiler miscompilation. The likely repair is a protocol-indexed reset-cell
relation (or an equivalent reset-to-reuse composed theorem) that preserves
the strict normal `ValueRel`. We still need to audit whether FIR well-formedness
guarantees immediate token consumption strongly enough for composition.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
