---
id: FIR-BUG-wasm-none-saturated-candidate-arbitrary-address
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 791f2ac1c0ae89237e279df32cddeabd4a3c5722
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-31
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

`SaturatedClosureCandidateResolutionInduction` requires a list of executable
`ClosureCandidateCase`s for every `Word32` address. Each case contains a
successful concrete `closureMatchesStep` equation at that address. Arbitrary
words need not point to a live closure object, so the quantified family is in
general uninhabited even when the actual source closure is represented
correctly.

## Minimal reproduction

The current conclusion starts with:

```text
∃ candidates : ∀ address : Word32, List (ClosureCandidateCase ... address),
  ...
```

but `ClosureCandidateCase.operation` requires:

```text
closureMatchesStep function arity fixed initial
  [.i32 (UInt32.ofNat address.value)] =
    .Return [.i32 matched] (clearFailure initial)
```

Choose an address that is unmapped, outside the allocated heap, or contains a
non-closure object. The concrete matcher faults instead of returning a bit.

## Exact commands

```text
rg -n "def SaturatedClosureCandidateResolutionInduction|structure ClosureCandidateCase" \
  integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean \
  integration/talos/FirTalos/ConcreteClosureDispatch.lean
rg -n "def closureMatchesStep|closureMatchesStep_of_refines" \
  integration/talos/FirTalos/ConcreteRuntime.lean
```

## Expected semantics

The canonical state relation should first resolve the semantic closure local
to its one mapped concrete address. Compiler candidate construction and
matcher execution should then be required only at that derived address.
Static enumeration remains address-independent; executable matcher cases do
not.

## Actual behavior

The proof boundary asks the recursive compiler induction to manufacture
successful matcher executions at all wasm32 words before the cache frame
selects the actual mapped address.

## Proof or differential evidence

`PhysicalValueRel.heapAddress` already derives the actual mapped word from the
related source local. `closureMatchesStep_of_refines` proves matcher success
at that word from the live source closure cell and immutable closure-table
agreement. Neither theorem supports an unrelated arbitrary address.

## Semantic impact

No runtime mismatch is known. The over-strong proof interface blocks
construction of the recursive generated-declaration theorem and could only be
satisfied by postulating impossible target executions.

## Classification and triage

This is a W6 proof-interface error. The repair must reorder constructive
reasoning: derive the mapped address from `ConcreteReuseCapacityCacheFrame`,
then instantiate the compiler candidate family at that address. It must not
weaken concrete decoding or add a target execution certificate.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ConcreteReuseCapacityCacheFrame.resolveClosureAddress` now derives the local
word and refinement-witness mapping before executable candidate construction.
`SaturatedClosureCandidateResolutionInduction` is instantiated only at that
address, and its `toSelection` theorem derives first-match selection from the
resulting candidate list. The contract example in
`ConcreteCompilerCorrectnessContract.lean` guards canonical address recovery;
the source module itself checks the reordered induction and selection theorem.
