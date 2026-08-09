---
id: FIR-BUG-wasm-none-resident-float-scalar-setter
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-09
reproduction: integration/illuminate-player/IlluminateFirNative/SelectionCompile.lean
regression: integration/talos/artifact/resident-setter-client.mjs
---

# Summary

The resident mutation linker rejects Lean's ordinary packed `Float` setter,
blocking a constructor-specific `PlayerEvent.tick` entry from becoming a
self-contained Wasm module.

## Minimal reproduction

Capture a function that constructs an inductive with one `Float` scalar field,
then link its final-LCNF closure with the closed-application resident policy.
The constructor emits `.scalarSet 0 0 .float`.

## Exact commands

From `integration/illuminate-player` with the Illuminate source view present:

```sh
lake --keep-toolchain \
  -KilluminateRoot=/home/egallego/lean/illuminate/.worktrees/vir-performance \
  env lean SelectionEmit.lean
```

## Expected semantics

The generic resident setter should accept every packed scalar kind supported
by FIR's Wasm ABI. For `Float`, it should preserve the incoming binary64 bits
and write eight bytes at the compiler-provided scalar coordinate.

## Actual behavior

Resident linking fails before Wasm emission with
`ResidentMutation.LinkError.unsupportedScalarKind AbiKind.float`.

## Proof or differential evidence

The source closure lowers successfully and reaches resident setter linking;
the linker's `scalarBytes` and `scalarStore` functions cover only unsigned
integer lanes.

## Semantic impact

Any closed application that constructs or mutates a packed `Float` field
cannot use the zero-import resident-runtime path, including the scalar-tick
Illuminate experiment.

## Classification and triage

This is a Wasm adapter coverage gap. FIR already has typed Float ABI lanes,
bit-preserving reinterpret instructions, and checked eight-byte stores, so no
new semantic or physical-memory contract is required.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ResidentMutation` now accepts `Float32` and `Float`, reinterprets their
physical lanes to `UInt32`/`UInt64`, and uses the existing checked integer
stores. The standalone zero-import setter artifact verifies Float32 and exact
negative-zero binary64 bytes in an external Wasm engine; the Illuminate
selection package permanently exercises the Float path through its scalar
tick entry.
