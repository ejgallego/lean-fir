---
id: FIR-BUG-wasm-none-lean-zip-nat-arithmetic-import-frontier
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: lean-zip-level1-probe
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/talos/artifact/resident-nat-arithmetic-client.mjs
---

# Summary

The generic resident numeric closure does not internalize `Nat.mul`,
`Nat.pow`, `Nat.land`, or `Nat.div`. The real
`Zip.Wasm.compressLevel1` closure therefore retains four host imports after
the accepted arbitrary-precision Nat/Int layer is linked.

## Minimal reproduction

Capture and resident-link `Zip.Wasm.compressLevel1`, then inspect the remaining
ordinary imports in `_build/level1-probe.json`.

## Exact commands

```sh
cd integration/lean-zip
lake --keep-toolchain env lean ProbeLevel1.lean
jq '.remainingImports' _build/level1-probe.json

cd ../talos/artifact
lake exe fir-wasm-artifact resident-nat-arithmetic \
  _build/resident-nat-arithmetic.wasm
node run-resident-nat-arithmetic.mjs \
  _build/resident-nat-arithmetic.wasm
```

## Expected semantics

All four operations implement Lean's arbitrary-precision `Nat` behavior over
canonical immediate, promoted, and multi-limb resident values. Division by
zero and exponentiation corner cases match Lean exactly. The implementation
must be stack-safe and must not narrow values to a wasm32 host integer.

## Actual behavior

The four declarations remain in the external import frontier.

## Proof or differential evidence

Before the repair, the production Level-1 inventory retained all four
declarations. The standalone module now validates in Lean and V8 with zero
imports and no runtime operations. Its differential client compares immediate,
promoted, and multi-limb multiplication, exponentiation, bitwise intersection,
and division with JavaScript `BigInt`, including `5 / 0 = 0`, `0 ^ 0 = 1`,
32-bit boundary values, and 521-bit division. The production probe no longer
lists any Nat operation among its two remaining generated List imports.

## Semantic impact

Level-1 compression cannot satisfy the self-contained zero-import package
contract. A bounded scalar replacement would also miscompile valid Lean
programs whose intermediate naturals exceed the wasm32 input size.

## Classification and triage

This is a W7 resident-runtime coverage defect. The repair should reuse the
accepted arbitrary-precision numeric layout rather than introduce a second
Nat representation.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ResidentNatArithmetic` now internalizes all four declarations over the
canonical arbitrary-precision resident Nat representation. Multiplication
uses a direct 32-bit fast path and a structured multi-limb bit walker;
exponentiation uses squaring; `land` walks resident limbs directly; and
division uses stack-safe binary long division. The generic resident linker
selects this family after `ResidentBigNumeric`.

The standalone artifact has module-owned memory, zero imports, no residual
runtime operations, deterministic encoding, and external-engine coverage for
immediate, promoted, and multi-limb inputs, including division by zero,
`0 ^ 0`, values around the 32-bit boundary, and borrowed-input ownership.
