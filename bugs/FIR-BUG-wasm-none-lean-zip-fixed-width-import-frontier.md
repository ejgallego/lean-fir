---
id: FIR-BUG-wasm-none-lean-zip-fixed-width-import-frontier
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/talos/artifact/resident-fixed-width-client.mjs
---

# Summary

The generic resident linker closes the complete runtime-operation frontier of
the real `Zip.Wasm.compressLevel1` final-LCNF closure, but retains 55 ordinary
fixed-width and `USize` declaration imports. The current resident fixed-width
family contains only five `UInt16` helpers, while the source closure uses the
generic `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize` APIs.

## Minimal reproduction

Capture and resident-link `Zip.Wasm.compressLevel1`, then inspect
`remainingImports` in `integration/lean-zip/_build/level1-probe.json`. The
inventory contains 16 `UInt32`, 14 `UInt64`, 13 `USize`, seven `UInt8`, and
five `UInt16` declarations.

## Exact commands

Run the `ProbeLevel1.lean` command documented by
`integration/lean-zip/README.md` and inspect the generated JSON inventory.

## Expected semantics

Lean fixed-width externs compile to their exact scalar lanes. Arithmetic wraps
at the source width, shift counts are masked by that width, decisions return a
`UInt8` Boolean, conversions preserve low bits, and `toNat`/`ofNat` cross the
resident natural representation without host code.

## Actual behavior

The source is otherwise fully lowerable and has zero unresolved runtime
operations, but the listed fixed-width calls remain imports. Therefore the
production Level-1 package is not self-contained.

## Proof or differential evidence

The concrete validation host already defines the generic fixed-width family.
The first W7 repair slice will add a zero-import standalone Wasm regression for
the operations expressible through the accepted symbolic instruction surface,
then rerun the real Level-1 inventory. Operations needing new physical Wasm
instructions remain an explicit shared-contract follow-up rather than being
approximated.

## Semantic impact

Packed binary applications can capture and lower successfully but cannot be
published as complete runtime packages.

## Classification and triage

W7 owns the executable resident helper family. W6 owns its eventual
implementation-to-concrete-runtime refinement. Any extension of the shared
symbolic Wasm instruction surface must be isolated and landed by the
integration owner before W7 consumes it.

## Workaround

none

## Upstream tracking

none

## Current checkpoint

The first W7 capability slice internalizes 30 imports through the accepted
symbolic instruction surface: all seven required `UInt8` operations, three
additional `UInt16` conversions, thirteen `UInt32` operations, and seven
`UInt64` conversions/shifts/decisions. The exact Lean 4.33 final-LCNF boundary
returns `tagged` from `UInt8.toNat` and `UInt16.toNat`, but `tobject` from
`UInt32.toNat`; the executable helper and external-engine regression preserve
that distinction.

The real 391-declaration Level-1 probe now links 1,696 functions with 47
imports and zero runtime operations, down from 77 imports. The remaining
fixed-width frontier is 13 `USize`, seven `UInt64`, three `UInt32`, and two
`UInt16` declarations. Container, Nat, List, String, and platform imports are
separate resident-family slices. This card stays active until the generic
fixed-width/`USize` frontier is closed.

## Resolution and regression

Unresolved. The first 30-import capability slice is guarded by the
zero-import external-engine fixture in
`integration/talos/artifact/resident-fixed-width-client.mjs` and by the exact
real-source inventory in `integration/lean-zip/ProbeLevel1.lean`. The card can
move to `fixed` only when the remaining generic fixed-width and `USize`
declarations have executable resident coverage.
