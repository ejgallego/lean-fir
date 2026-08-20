---
id: FIR-BUG-wasm-none-usize-target-width-contract
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-20
reproduction: Fir/Wasm/Emit/ResidentPlatform.lean
regression: none
---

# Summary

FIR's explicit `wasm32-lean64` contract returns 64-bit `USize` and platform
semantics, while upstream Lean's native wasm32 runtime uses target-native
32-bit `size_t`; the previous FIR comment incorrectly claimed the results
matched.

## Minimal reproduction

Generate and run FIR's resident platform helper. It returns the immediate Nat
encoding of 64 (`129`) and its manifest names the target `wasm32-lean64`.
Separately, upstream Lean 4.33's `lean_usize_to_nat` accepts C++ `size_t`, and
`runtime/platform.cpp` derives `System.Platform.numBits` from pointer size. On
`wasm32-wasip1`, VIR's upstream-runtime probe observes 32 bits and truncates
`UInt64.toUSize 4294967296` to zero.

## Exact commands

```sh
lake exe fir-wasm-artifact resident-platform _build/resident-platform.wasm
node integration/talos/artifact/run-resident-platform.mjs _build/resident-platform.wasm
```

Inspect the selected toolchain's `include/lean/lean.h` implementation of
`lean_usize_to_nat` and the upstream Wasm result recorded by VIR PR #136.

## Expected semantics

A backend claiming equivalence with Lean's native wasm32 runtime must use
32-bit `USize`, return 32 from `System.Platform.getNumBits`, and apply
modulo-`2^32` fixed-width operations and conversions.

FIR may instead transport the 64-bit scalar semantics of final-impure LCNF
captured by its x86_64 toolchain, but that target must remain explicitly named
`wasm32-lean64` and must not be described as Lean's native Wasm runtime.

## Actual behavior

FIR currently chooses the second contract coherently: `.usize` uses an `i64`
ABI lane, W6 concrete layout records 64 semantic bits and eight-byte scalar
slots, resident conversions use modulo `2^64`, the validation corpus expects
64-bit results, and the platform helper returns 64. Only the native-Wasm
equivalence claim was false.

## Proof or differential evidence

VIR's `wasm32-wasip1` execution observes `System.Platform.numBits = 32` and
`UInt64.toUSize 4294967296 = 0`. FIR's resident-platform external-engine
fixture instead requires encoded 64, and FIR's `USize.ofNat`, `USize.toNat`,
and fixed-width corpus intentionally exercise values through `2^64 - 1`.

## Semantic impact

FIR packages are faithful to captured Lean64 final LCNF, but they are not yet
drop-in semantic equivalents of code compiled by Lean's target-native wasm32
pipeline when programs observe `USize`, `ISize`, platform width, pointer-sized
arithmetic, or layout decisions derived from them.

## Classification and triage

The current behavior is a documented FIR semantic target rather than a local
helper bug. A target-native migration is a shared-contract change affecting
source runtime values, constant folding and capture, literal/conversion
lowering, resident USize/ISize/platform helpers, the semantic ABI, concrete
layout and refinement relations, validation codecs/corpus, W6/W7 proofs, and
consumer package metadata.

The accepted W6/W7 modulo-`2^64` stack remains valid evidence for
`wasm32-lean64`; it becomes migration input rather than being silently
reinterpreted.

## Workaround

none

## Upstream tracking

VIR PR #136 records the executable upstream wasm32 observations. No Lean
upstream bug is alleged.

## Resolution and regression

Unresolved. Correct the inaccurate comment immediately. Before changing
executable semantics, choose and name a target-native FIR contract, isolate
the shared surface change, and add paired `wasm32-lean64`/native-wasm32
regressions or explicitly retire the former.
