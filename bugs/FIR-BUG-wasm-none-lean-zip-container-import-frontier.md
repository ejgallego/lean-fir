---
id: FIR-BUG-wasm-none-lean-zip-container-import-frontier
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/lean-zip/ProbeLevel1.lean
---

# Summary

After closing the complete scalar and runtime-operation frontiers, the real
`Zip.Wasm.compressLevel1` closure initially retained 22 ordinary imports
across generic Array, ByteArray, Nat, List, String, and platform APIs. The
first Array slice internalizes owned lookup, Nat-indexed update, checked
update, and swap, leaving 18 imports. The platform and Array/List conversion
slices remove three more, leaving 15 imports.

## Minimal reproduction

Capture and resident-link `Zip.Wasm.compressLevel1` through
`integration/lean-zip/ProbeLevel1.lean`, then inspect `remainingImports` in
`_build/level1-probe.json`.

## Exact commands

From `integration/lean-zip`, run the configured source-view build followed by
`lake env lean ProbeLevel1.lean`, as documented in `README.md`.

## Exact frontier

- eight ByteArray operations: unchecked little-endian 32/64-bit loads and
  stores, `get`, `uget`, `push`, and `pushUInt64LE`;
- four Nat operations: `mul`, `pow`, `land`, and `div`;
- two specialized List loops: Array append-list fold and List zip;
- `String.ofList`.

## Expected semantics

The generic closed-application linker should internalize these standard Lean
operations over the accepted resident layouts, retain Lean ownership and
unique-update behavior, and leave no host import.

## Actual behavior

The linked module after the platform and Array conversion slices has 1,730
functions, zero runtime operations, and exactly these 15 declaration imports.
It therefore
cannot yet be published as a self-contained Level-1 package.

## Semantic impact

Packed binary applications reach final-LCNF and lower completely but still
need host functions for standard container and numeric operations.

## Proof or differential evidence

The exact production inventory is generated from the real Lean 4.33
final-LCNF closure. Each repair slice must additionally pass its zero-import
standalone external-engine fixture before the inventory is ratcheted.

## Classification and triage

W7 owns executable resident helpers and package acceptance. W6 owns later
implementation-to-concrete-runtime refinement. Each family must keep exact
signatures, explicit layout capabilities, and external-engine differential
coverage; no JavaScript fallback is acceptable.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The Array mutation slice adds zero-import resident implementations of
`Array.getInternal`, `Array.set`, `Array.set!`, and `Array.swap`. Its external
engine checks cover owned-result retention, exclusive update, out-of-bounds
replacement consumption, exclusive swap, and shared copy-on-write swap. The
real production probe confirms that all four imports disappear.

The next slices add the exact wasm32/Lean64 `System.Platform.getNumBits`
result and zero-import `Array.mk`/`Array.toList` implementations over the
generic resident List constructor representation. Their external-engine
checks cover ordering, empty values, malformed inputs, unique spine
consumption, and shared/persistent ownership. The 391-declaration production
probe confirms that all three imports disappear: it now links 1,730 functions
with 15 imports and zero runtime operations (57,309 ms capture, 15,321 ms
lowering, 119,920 ms linking).

Unresolved. Ratchet the exact real-source inventory after coherent resident
family slices until `remainingImports` is empty.
