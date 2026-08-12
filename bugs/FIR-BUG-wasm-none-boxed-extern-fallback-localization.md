---
id: FIR-BUG-wasm-none-boxed-extern-fallback-localization
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: external-engine-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/lean-zip/ProbeLevel1.lean
---

# Summary

Final-LCNF capture correctly asks Lean to compile a raw extern so upstream's
explicit-boxing pass can generate its `_boxed` adapter, but then incorrectly
retains the extern's Lean fallback body as local application code.

## Minimal reproduction

Capture a higher-order use of `UInt32.ofNat`. The captured program contains the
required `UInt32.ofNat._boxed` adapter, but also localizes raw `UInt32.ofNat`
and subsequently `BitVec.ofNat`.

## Exact commands

From `integration/lean-zip`, after the source-view setup documented in its
README:

```sh
lake env lean ProbeLevel1.lean
```

Before the repair, the lean-zip Level-1 external-engine smoke additionally
reaches generic `Nat.pow` through this localized fixed-width fallback and
eventually traps in the monotonic arena allocator.

## Expected semantics

Lean's ordinary explicit-boxing pass owns construction of `_boxed` adapters.
The generated adapter remains local, while the original `@[extern]`
declaration remains an extern call handled by the resident runtime.

## Actual behavior

Both the generated adapter and the raw extern's Lean fallback implementation
remain local. Recursive capture therefore treats the fallback's dependencies
as application source and expands an unnecessary generic numeric closure.

## Proof or differential evidence

The Level-1 closure probe now enumerates every captured declaration, rejects
any environment extern classified as local code, and still proves that the
linked module has zero imports and zero remaining runtime operations. Native
and Wasm outputs agree for 256-byte and 4 KiB repeated-byte inputs.

## Semantic impact

Programs remain extensionally correct for small inputs, but fixed-width calls
allocate arbitrary-precision naturals and can exhaust an instance-lifetime
arena under production workloads. The captured declaration inventory also no
longer reflects the native runtime boundary.

## Classification and triage

This is a generic final-capture boundary error, not a lean-zip or UInt32
special case. It applies to every compiled `@[extern]` used only to derive an
upstream boxed adapter.

## Workaround

None.

## Upstream tracking

none

## Resolution and regression

After captured declarations have passed through Lean's ordinary final-LCNF
pipeline, FIR restores every original environment extern to an extern stub.
Lean-generated adapters remain local, so their exact upstream ABI policy is
preserved without internalizing the raw fallback body. The Level-1 regression
rejects every environment extern that capture has incorrectly classified as a
local declaration, then retains the existing zero-import linked-artifact
ratchet. Fixed-width linking validates the restored `UInt8.toNat` import
against its captured `tobject` result ABI while retaining the resident
helper's sound, stricter `tagged` result.
