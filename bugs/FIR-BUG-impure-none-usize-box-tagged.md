---
id: FIR-BUG-impure-none-usize-box-tagged
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: impure
pass: none
discovered-by: invariant-check
first-seen: 2026-08-26
reproduction: Fir/LeanIR/Runtime.lean
regression: Fir/Validation/Corpus.lean
---

# Summary

FIR tags small final-LCNF `box USize` values even though Lean's
`lean_box_usize` always allocates a heap constructor.

## Minimal reproduction

`boxUsesTaggedRepresentation LCNF.ImpureType.usize 41` returns true, so
`Runtime.box` produces `.object (.tagged 41)`. Lean 4.33's
`lean_box_usize 41` instead calls `lean_alloc_ctor` and stores the `size_t`
payload in that object. A generic owned argument can therefore release Lean's
box with unchecked `dec[ref]`, while FIR's tagged substitute is not a heap
reference.

## Exact commands

```sh
sed -n '2850,2890p' \
  ~/.elan/toolchains/leanprover--lean4---v4.33.0/include/lean/lean.h
sed -n '720,785p' Fir/LeanIR/Runtime.lean
```

## Expected semantics

Every boxed `USize` is a heap object, independent of payload and target word
width. `unbox USize` reads the stored `size_t` payload and rejects a physical
tagged word.

## Actual behavior

The semantic runtime uses the generic payload-threshold branch for `USize`.
Small values become tagged words, and semantic `unbox USize` accepts those
words through `scalarFromType`.

## Proof or differential evidence

The upstream API is unconditional: both the 32-bit and 64-bit definitions of
`lean_box_usize` allocate, and `lean_unbox_usize` always calls
`lean_ctor_get_usize`. FIR's current guard and match branches encode the
opposite representation for payloads at or below `maxTaggedPayload`. The
source-generated generic release regression is still to be added with the
contract repair.

## Semantic impact

Compiler-generated code can perform a valid unchecked reference decrement on
a boxed `USize`. FIR's LCNF interpreter and resident Wasm can fault on the
corresponding small value, and generic containers can observe a representation
that upstream Lean never produces.

## Classification and triage

This is a shared representation contract bug spanning the impure runtime, W6
concrete boxing proofs, W7 resident scalar helpers, semantic hosts, and
validation fixtures. Isolate the contract change and land it through the
integration owner before dependent proof and generation changes.

## Workaround

Do not substitute another source type for a genuine `USize`. Unrelated generic
fixtures may avoid `USize` only until the representation contract is repaired.

## Upstream tracking

none

## Resolution and regression

The integrated contract makes `USize` heap-only in the semantic runtime,
rejects tagged `USize` unboxing, and adds source-generated small and maximal
owned-release cases. W7's zero-import resident box/unbox helpers use the same
40-byte owned layout, and the LCNF ElimDead and W6 concrete-runtime proofs have
been adapted to the heap-only policy. The complete stack is linked on `main`
through exact checkpoint `de7c03ab`; the focused and full native/LCNF/V8
triangles, Talos cone, and deterministic artifact gate pass.
