---
id: FIR-BUG-wasm-none-level1-resident-nat-mod-trap
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/talos/artifact/resident-nat-arithmetic-client.mjs
regression: integration/talos/artifact/resident-nat-arithmetic-client.mjs
---

# Summary

The zero-import `Zip.Wasm.compressLevel1` artifact traps in the resident
`Nat.mod` helper on the first empty-input differential case, while the native
Lean entry returns normally.

## Minimal reproduction

Generate `_build/lean-zip-level1.wasm` with `Emit.lean`, then run:

```sh
node level1-smoke.mjs
```

The first call `compressLevel1(new Uint8Array())` reaches Wasm function 1845,
which the emitted inventory identifies as `fir_ext_Nat_mod`, and executes
`unreachable`.

## Exact commands

```sh
cd integration/talos/artifact
lake exe fir-wasm-artifact resident-nat-arithmetic _build/resident-nat-arithmetic.wasm
node run-resident-nat-arithmetic.mjs _build/resident-nat-arithmetic.wasm
```

## Expected semantics

The Wasm entry returns exactly the native result of
`Zip.Wasm.compressLevel1` for the same transferred `ByteArray`.

## Actual behavior

V8 reports `RuntimeError: unreachable`. The source closure has zero imports,
zero runtime operations, and zero unsupported declarations, so this is a
resident execution discrepancy rather than an unresolved frontier.

## Proof or differential evidence

The standalone V8 client compares small, 64-bit, multi-limb, and zero-divisor
remainders against JavaScript `BigInt` arithmetic. The real Level-1 artifact
then passes the zero-import closure probe and native/Wasm differential.

## Semantic impact

Level-1 publication is blocked: a zero-import artifact that traps on a valid
input cannot be admitted even though capture, lowering, linking, and encoding
succeed.

## Classification and triage

This is a Wasm-resident helper implementation gap. Source capture and lowering
preserve the real `Nat.mod` call and its object-family ABI correctly.

## Workaround

None. Do not skip empty inputs or replace the real source entry.

## Upstream tracking

none

## Resolution and regression

Level-1 reaches canonical Naturals wider than the bounded helper's declared
32-bit capability. `Nat.mod` now belongs to the arbitrary-precision Nat
arithmetic family and shares its structured long-division walker, returning
the walker remainder while releasing the quotient. The zero-divisor branch
implements Lean's `n % 0 = n` and increments a borrowed heap input before
returning it.

The standalone resident Nat arithmetic artifact covers small, 64-bit, and
multi-limb remainders plus the zero-divisor rule. The Level-1 native/Wasm
differential is the source-closure regression.
