---
id: FIR-BUG-wasm-none-release-fuel-preempts-nonheap-noop
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 2e55e8cfef1660ebd71f0b98647b8610515f3228
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/Runtime.lean
regression: Fir/Wasm/Concrete/Examples.lean
---

# Summary

Concrete recursive release reports fuel exhaustion before classifying a
checked tagged or erased child that semantic release skips without recursion.

## Minimal reproduction

Call `decrementReferenceOnceFuel 0 state Word32.zero true`. The zero word is
the canonical erased-field sentinel. Semantic ownership traversal matches the
corresponding `.erased` value and returns the threaded runtime unchanged, but
the concrete function returns `.target .releaseFuelExhausted` before examining
the word or its checked no-op behavior.

## Exact commands

At the first-seen revision, use Lean Beam on
`Fir/Wasm/Concrete/Examples.lean` to check this command inside the
`Fir.Wasm.Concrete` namespace:

```lean
#guard match decrementReferenceOnceFuel 0 MemoryState.initial Word32.zero true with
  | .error (.target .releaseFuelExhausted) => true
  | _ => false
```

The guard succeeds and records that fuel exhaustion preempts the erased-field
no-op.

## Expected semantics

`HeapObject.ownedValues` recurses only for `.object (.heap child)`. Tagged and
erased fields do not consume recursive depth, so the corresponding checked
concrete words must return the current memory state even when no heap-recursion
fuel remains. Unchecked public non-object use must retain its existing source
faults, and an actual heap word at fuel zero must still exhaust fuel.

## Actual behavior

`decrementReferenceOnceFuel` matches fuel before `Word32.classify`. Its
zero-fuel equation therefore faults uniformly for heap references, immediate
tags, promoted tags, erased sentinels, and invalid words.

## Proof or differential evidence

The paired ownership-fold proof reaches a non-heap semantic value at zero
remaining child fuel. The semantic fold has the unchanged-runtime equation,
while the related concrete word has the fuel-exhaustion equation, so the
inductive refinement step is false.

## Semantic impact

The public heap-derived bound normally supplies spare depth, but the primitive
does not implement its documented per-object fuel policy and blocks a local,
compositional proof of recursive constructor release. Any direct zero-fuel
checked use also observes a spurious target fault on a non-owning value.

## Classification and triage

This is local to the concrete Wasm runtime model. FIR semantic ownership and
the frozen ABI agree that only heap references own recursively released
locations; tagged and erased representations are non-owning.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved across W6.3t–W6.3u by distinguishing non-owning representations
before ordinary heap recursion consults fuel. Checked immediate and sentinel
words return the threaded state for every fuel value; a heap-addressed
promoted tag is decoded and takes the same all-fuel no-op path; invalid and
unchecked words keep their source faults; and an ordinary heap word at zero
fuel still returns `.target .releaseFuelExhausted`. Permanent example guards
cover zero-fuel erased, immediate, and promoted no-ops plus zero-fuel ordinary
heap exhaustion. `decrementReferenceOnceFuel_sentinel` and
`LiveHeapRel.decrementReferenceOnceFuel_tagged` expose the equations used by
the ownership-fold proof.
