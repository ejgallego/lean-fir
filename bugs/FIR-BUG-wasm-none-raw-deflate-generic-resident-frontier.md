---
id: FIR-BUG-wasm-none-raw-deflate-generic-resident-frontier
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-13
reproduction: integration/lean-zip/ProbeRaw.lean
regression: Fir/Wasm/Emit/ResidentFixedWidth.lean
---

# Summary

The real `Zip.Wasm.compressRaw` closure captures and lowers without unsupported
declarations, but the generic closed-application resident linker retains 16
ordinary Lean scalar/Nat/Float imports and two `UInt64` boxing operations.

## Minimal reproduction

Compile the unmodified read-only lean-zip entry
`Zip.Wasm.compressRaw : ByteArray -> UInt8 -> ByteArray` through FIR's final-LCNF
source capture and `closedApplicationAvailablePolicy`.

## Exact commands

From `integration/lean-zip`, run:

```text
lake env lean ProbeRaw.lean
```

The checked inventory is written to `_build/raw-probe.json`.

## Expected semantics

The generic resident pipeline should internalize the standard fixed-width,
Natural, direct Float comparison, and scalar-box operations required by the
captured closure. `Float.ofNat`, `Float.ofScientific`, and `Float.log2` should
remain on FIR's reviewed standard-math frontier, then be closed by the
deterministic runtime link. The published result should have zero function
imports, zero runtime operations, module-owned memory, and the unchanged
structured source ABI.

## Actual behavior

Linking retains `UInt8.ofNatLT`, `Float.ofNat`, `Float.ofScientific`,
`Float.log2`, `Float.decLt`, `UInt8.decLe`, `UInt64.complement`,
`Nat.shiftLeft`, `Nat.log2`, `UInt32.ofNatLT`, `UInt32.log2Clz`,
`UInt8.shiftRight`, `UInt8.land`, `UInt8.lor`, `UInt64.decLt`, and
`UInt64.mul`, plus `box uint64 -> tobject` and `unbox tobject -> uint64`.

## Proof or differential evidence

The closure captures 702 declarations with 128 reviewed externals and zero
unsupported declarations. The failure is currently an admission frontier, so
the all-level native/Wasm differential suite cannot start.

## Semantic impact

Production closures using ordinary compiler-generated fixed-width, Natural,
boxed-UInt64, and floating operations cannot yet become self-contained Wasm
modules. The exact fixed-width/Nat operations have generic resident
implementations; the opaque Float/libm surface requires the checked standard
runtime link rather than approximate pure-Wasm substitutes.

## Classification and triage

This is W7 resident-runtime generation work. Extend the existing generic
fixed-width, Nat, direct Float comparison, and scalar-box families with exact
ABI checks and standalone real-engine regressions. Extend the standard math
runtime contract for `Float.log2`. Do not add lean-zip-specific helpers, host
callbacks, or numerically approximate replacements for Lean externals.

## Workaround

None.

## Upstream tracking

none

## Resolution and regression

Commit `f24934ff` adds the exact fixed-width, arbitrary-Nat, direct Float
comparison, and canonical UInt64 box/unbox resident support. The real raw probe
now captures 702 declarations with 128 reviewed externals and zero unsupported
declarations, then links to exactly `Float.ofNat`, `Float.ofScientific`, and
`Float.log2` with zero runtime operations. The standard-runtime link closes
those three imports into a 1,757,944-byte zero-import module with the unchanged
seven-export surface. Persistent-cache eager forcing is tracked separately.
