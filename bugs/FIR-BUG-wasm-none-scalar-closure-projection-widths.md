---
id: FIR-BUG-wasm-none-scalar-closure-projection-widths
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/talos/artifact/resident-closure-projections-client.mjs
---

# Summary

The generic resident closure-projection linker rejects `UInt16`, `UInt64`,
and `USize` captures even though the closure layout and typed loader already
support their physical `i32` and `i64` lanes.

## Minimal reproduction

Capture and lower `Zip.Wasm.compressLevel1`, then apply the generic resident
policy. The linked module retains 50 `closureProj` operations: 35 returning
`USize` and 15 returning `UInt64`.

## Exact commands

Run the `ProbeLevel1.lean` command documented by
`integration/lean-zip/README.md` and inspect
`integration/lean-zip/_build/level1-probe.json`.

## Expected semantics

Every scalar ABI kind supported by closure allocation can be projected from
the same descriptor-indexed eight-byte slot. `UInt16` uses an `i32` load;
`UInt64` and `USize` use bit-preserving `i64` loads.

## Actual behavior

`closureProjectionSuffix?` names only `UInt8`, `UInt32`, `Float32`, and
`Float`. The generic linker therefore leaves the other scalar projection
operations unresolved despite `closureProjectionFunction` already selecting
the correct load from `AbiKind.valueType`.

## Proof or differential evidence

The real Level-1 source closure captures 391 declarations with no unsupported
declarations and lowers successfully. After all other available resident
families link, these 50 operations are the dominant residual runtime frontier.

## Semantic impact

Ordinary Lean collection and bitstream loops that capture native word lanes
cannot become self-contained Wasm modules. This blocks the Level-1 lean-zip
package before declaration-helper closure can be audited.

## Classification and triage

W7 executable-resident-helper capability omission. It does not change the
closure layout, semantic Wasm ABI, or helper signature; W6 still owns the
implementation-to-concrete-runtime refinement theorem.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The resident projection catalog now admits `UInt16`, `UInt64`, and `USize` and
selects the already-generic typed load from the ABI value type. Raw-layout and
concrete-host V8 checks preserve the complete 32/64-bit payloads. The real
Level-1 probe eliminates all 50 scalar closure projections and ultimately
reaches zero remaining runtime operations.
