---
id: FIR-BUG-wasm-none-byte-array-unique-update
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: resident-runtime-test
first-seen: 2026-08-11
reproduction: integration/talos/artifact/run-resident-byte-array.mjs
regression: integration/talos/artifact/resident-byte-array-client.mjs
---

# Summary

The first packed resident `ByteArray` implementation allocates every value as
live persistent with reference count zero. Consequently
`ByteArray.copySlice` always allocates and copies, even when its consumed
destination is exclusive and already has sufficient capacity.

## Minimal reproduction

Create a resident `ByteArray.emptyWithCapacity 10`, record the heap frontier,
and copy two bytes into it without exceeding its capacity. The returned object
must be the original destination and the heap frontier must not move.

## Exact commands

```sh
lake exe fir-wasm-artifact resident-byte-arrays \
  integration/talos/artifact/_build/resident-byte-arrays.wasm
node integration/talos/artifact/run-resident-byte-array.mjs \
  integration/talos/artifact/_build/resident-byte-arrays.wasm
```

## Expected semantics

Lean's `lean_byte_array_copy_slice` applies `lean_sarray_ensure_capacity` and
then `lean_sarray_ensure_exclusive`. A live, nonpersistent destination with
reference count one and enough capacity is mutated in place. A persistent or
multiply referenced destination is copied, and an exclusive destination that
must grow is also copied to the requested capacity.

## Actual behavior

Resident allocation writes the persistent flag and reference count zero.
`copySlice` unconditionally allocates a new packed object, copies the old
destination, applies the slice, and returns the new address.

## Proof or differential evidence

Before the repair, the resident real-engine regression failed with
`emptyWithCapacity unique flags: expected 2, got 3`. The repaired helper is
also exercised through the real `Zip.Wasm.compressStored` closure, whose Wasm
output agrees byte-for-byte with the native Lean oracle on ten cases through
one MiB.

## Semantic impact

Lean's uniqueness discipline is part of the compiled runtime contract. Losing
the exclusive path changes allocation/reclamation behavior from amortized
buffer construction to repeated copying and can make otherwise viable Lean
programs impractical after compilation.

## Classification and triage

This is a resident-runtime compiler defect. The source program and Lean's
native runtime both carry the correct consumed-destination contract; the first
Wasm helper replaced it with an always-persistent arena shortcut.

## Workaround

None. Host-side mutation or treating `ByteArray` as `Array UInt8` would bypass
the compiled Lean ownership contract and is not acceptable.

## Upstream tracking

none

## Resolution and regression

Resident ByteArray allocation now creates live nonpersistent objects with
reference count one. `copySlice` retains the destination exactly when its
capacity suffices and its reference count is one. Otherwise it allocates with
Lean's exact/geometric capacity rule, copies the destination, consumes one
ordinary destination reference, and leaves persistent values untouched.

The resident regression checks exclusive identity and a stationary frontier,
growth replacement and release, shared copy-on-write with one reference
consumed, persistent copy-on-write, capacity preservation, and the existing
byte-level results. The package boundary remains borrowed persistent input and
copied output, and advertises layout/ownership v2.
