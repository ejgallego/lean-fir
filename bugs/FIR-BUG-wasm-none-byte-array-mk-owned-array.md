---
id: FIR-BUG-wasm-none-byte-array-mk-owned-array
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: resident-runtime-test
first-seen: 2026-08-12
reproduction: integration/talos/artifact/run-resident-byte-array.mjs
regression: integration/talos/artifact/resident-byte-array-client.mjs
---

# Summary

The resident `ByteArray.mk` helper accepts only the old persistent Array
boundary shape and never consumes its owned `Array UInt8` input. Ordinary
live Arrays produced by compiled Lean therefore trap at the conversion
boundary, while persistent inputs hide an ownership leak.

## Minimal reproduction

Allocate a valid live Array with reference count one and immediate UInt8
elements, then call `ByteArray.mk`. The resident helper traps while checking
for the persistent flag instead of producing a packed ByteArray and consuming
the Array.

## Exact commands

```sh
cd integration/talos/artifact
lake exe fir-wasm-artifact resident-byte-arrays _build/resident-byte-arrays.wasm
node run-resident-byte-array.mjs _build/resident-byte-arrays.wasm
```

## Expected semantics

`ByteArray.mk` accepts a valid ordinary or persistent `Array UInt8`, copies
the scalar bytes, and consumes its owned Array reference. An exclusive Array
is released; a shared Array loses one reference; a persistent boundary Array
is unchanged.

## Actual behavior

The helper requires `live + persistent` flags and returns without releasing
the input graph.

## Proof or differential evidence

The real-engine resident ByteArray fixture supplies a valid live Array. Before
repair the call traps before decoding any result.

## Semantic impact

After restoring ordinary Array ownership, compiled code cannot cross the
standard `Array UInt8` to `ByteArray` conversion. Persistent test inputs also
mask leaked intermediate Arrays.

## Classification and triage

This is a resident-runtime compiler defect at the boundary between two
generic Lean container families.

## Workaround

None. Forcing all Arrays persistent would reintroduce the uniqueness defect.

## Upstream tracking

none

## Resolution and regression

`ByteArray.mk` now accepts either an ordinary live Array with a positive
reference count or a persistent boundary Array with reference count zero.
After packing all UInt8 elements it consumes the owned Array through the same
generic recursive release helper used by compiled code. The real-engine
fixture verifies that an exclusive Array is retired, a shared Array loses one
reference, and the existing persistent boundary input remains accepted and
unchanged.
