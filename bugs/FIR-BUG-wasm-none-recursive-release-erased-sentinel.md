---
id: FIR-BUG-wasm-none-recursive-release-erased-sentinel
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 6d3cf715dac1b858f69b6bf4408638999ead1b78
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/Runtime.lean
regression: Fir/Wasm/Concrete/Examples.lean
---

# Summary

Recursive constructor release faults on an erased object field encoded by the
zero sentinel, although FIR semantic release skips erased owned values.

## Minimal reproduction

Allocate a one-object-slot constructor whose field word is `Word32.zero`, the
canonical `.erased` representation, at reference count one. Calling
`decrementReferenceOnce state object true` first releases the parent, reads the
zero field, and then returns `.error (.source .expectedObject)` while visiting
that child.

The repository ABI admits this program: `AbiKind.isObjectField .erased` is
true, and constructor well-formedness accepts erased object fields.

## Exact commands

At the first-seen revision, use Lean Beam on
`Fir/Wasm/Concrete/Examples.lean` to check this command inside the
`Fir.Wasm.Concrete` namespace:

```lean
#guard match (do
    let (state, object) ← allocateConstructor MemoryState.initial
      mixedConstructorInfo #[Word32.zero]
    decrementReferenceOnce state object true :
      Except ConcreteError MemoryState) with
  | .error (.source .expectedObject) => true
  | _ => false
```

`lean-beam run-at` accepts the guard, demonstrating the unexpected error.

## Expected semantics

`HeapObject.ownedValues` contains the semantic `.erased` field, but
`decLocationFuel` recurses only for `.object (.heap child)` and returns the
threaded runtime unchanged for every other value. The concrete recursive fold
must likewise ignore the erased sentinel when its internal `check` flag is
true.

## Actual behavior

`decrementReferenceOnceFuel` treats immediates as checked no-ops, but combines
`.sentinel` with `.invalid` and unconditionally returns
`.source .expectedObject`. Thus the already-released parent is followed by a
spurious failure on its erased field.

## Proof or differential evidence

The recursive constructor refinement cannot relate the concrete child fold to
the semantic `ownedValues` fold for a `ValueRel.erased`: the concrete word is
zero, semantic execution takes the no-op branch, and concrete execution takes
the error branch. The accepted guard above evaluates that mismatch directly.

## Semantic impact

Any reference-count-one constructor containing an erased field can fail during
recursive release. This affects valid FIR programs and blocks a total W6.3
recursive-release correctness theorem.

## Classification and triage

The discrepancy is local to the concrete Wasm runtime model. The ABI and FIR
semantic runtime agree that erased constructor fields are valid and carry no
owned heap reference.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in W6.3o by splitting the concrete `.sentinel` and `.invalid`
branches. A checked sentinel decrement now returns the threaded state
unchanged, matching the recursive semantic fold, while unchecked public use
still reports `.source .expectedObject` and invalid words remain errors.
`releasedErasedFieldConstructor` permanently allocates and releases a
constructor with a zero/erased field and checks the parent's canonical freed
header. `decrementReferenceOnceFuel_sentinel` records the exact checked and
unchecked control-flow equation used by the recursive proof.
