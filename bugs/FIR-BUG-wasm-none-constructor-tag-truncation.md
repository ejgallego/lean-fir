---
id: FIR-BUG-wasm-none-constructor-tag-truncation
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-16
reproduction: Fir/Wasm/Lower.lean#compileCaseChain
regression: Fir/Wasm/Examples.lean#oversizedTagCaseProgram
---

# Summary

FIR case dispatch compares source `Nat` constructor tags after silently
truncating alternative tags to `UInt32`, without a supported-fragment bound
that makes the conversion injective.

## Minimal reproduction

Construct a heap-backed constructor and matching case alternative whose
`CtorInfo.cidx` is `UInt32.size`. The source runtime stores and compares that
tag as `Nat`, while `compileCaseChain` emits `UInt32.ofNat info.cidx`, which is
zero. A second alternative at tag zero is therefore indistinguishable in the
generated Wasm comparison.

## Exact commands

From the repository root:

```sh
rg -n "UInt32.ofNat info.cidx|info.cidx == tag" Fir/Wasm/Lower.lean Fir/LeanIR/Interpreter.lean
lake build Fir.Wasm.Examples
```

The source and target conversions are visible in those definitions; the
current Wasm example suite has no rejecting out-of-range regression.

## Expected semantics

Every program accepted by `WasmSupported` and `lowerSupported` should preserve
constructor-case selection. Either the ABI must carry the full source tag or
the supported fragment must prove every compared tag fits in `UInt32`.

## Actual behavior

`supportedAlt` accepts every `CtorInfo.cidx`. Lowering then emits an `i32`
constant with `UInt32.ofNat`, and the semantic `getTag` host also returns a
`UInt32`. Tags that differ by `UInt32.size` collide in target case dispatch.

## Proof or differential evidence

The case-simulation obligation requires recovering equality of source `Nat`
tags from equality of their `UInt32.ofNat` images. No such implication is
provable without a range premise, and neither `supportedCode` nor
`compileCaseChain` currently provides one.

## Semantic impact

The unrestricted symbolic lowerer can miscompile case selection. The initial
W4 correctness theorem also cannot soundly claim all programs currently
accepted by `WasmSupported`.

## Classification and triage

This is classified as `wasm-adapter`: FIR source evaluation is internally
consistent for heap-backed constructor tags, while the semantic-Wasm boundary
narrows them without validation. Compiler-produced tags are expected to be
small, but that expectation is not yet an executable invariant.

## Workaround

The supported fragment and the general lowerer reject case alternatives whose
tag does not fit the semantic `i32` tag lane.

## Upstream tracking

none

## Resolution and regression

`constructorTagFitsI32` is now an executable invariant. `supportedAlt` excludes
out-of-range alternatives, `compileCaseChain` rejects them even outside the
proof fragment, and `oversizedTagCaseProgram` guards both paths.
