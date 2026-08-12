---
id: FIR-BUG-wasm-none-lean-zip-byte-array-import-frontier
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: lean-zip-level1-probe
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/talos/artifact/resident-byte-array-client.mjs
---

# Summary

The resident ByteArray family does not internalize eight ordinary operations
used by the real `Zip.Wasm.compressLevel1` final-LCNF closure. Generated Wasm
therefore retains host imports for packed reads, little-endian reads and
writes, and capacity-aware appends.

## Minimal reproduction

Compile `Zip.Wasm.compressLevel1` through the generic final-LCNF source path
and apply the available resident helper families. The remaining import
inventory includes `ByteArray.get`, `ByteArray.uget`, `ByteArray.push`, the
32/64-bit little-endian operations, and `ByteArray.pushUInt64LE`.

## Exact commands

```sh
cd integration/lean-zip
lake --keep-toolchain --reconfigure \
  -KleanZipRoot=/tmp/fir-lean-zip-30737 \
  -KzipCommonRoot=/tmp/fir-zip-common-4425 \
  build LeanZipFir.Compile
lake --keep-toolchain env lean ProbeLevel1.lean
```

## Expected semantics

The helpers operate over FIR's packed resident ByteArray layout, preserve
Wasm's little-endian scalar bits, reject invalid bounds, mutate an exclusive
value in place when capacity permits, and otherwise copy while consuming one
ordinary input reference. No host fallback observes a Lean object address.

## Actual behavior

The linker recognizes only `copySlice`, `size`, `mk`, and
`emptyWithCapacity`. The Level-1 artifact therefore cannot satisfy the
zero-import package contract.

## Proof or differential evidence

The production closure inventory reports the eight declarations in its
remaining import frontier. The standalone closed-module regression confirms
that this slice internalizes the complete eight-operation family with zero
function or memory imports; the full Level-1 production probe is deferred
until the scalar prerequisite is accepted on `main`.

## Semantic impact

Leaving these operations imported prevents self-contained Wasm publication.
Implementing them without Lean's uniqueness discipline would also turn hot
compression loops into repeated allocation and copying, so a host shim or an
always-copy helper is not an acceptable repair.

## Classification and triage

This is a resident-runtime compiler coverage defect. It does not require a
new ByteArray representation or a shared symbolic-Wasm contract change.

## Workaround

None. Host callbacks and duplicated compressor logic are outside the native
package contract.

## Upstream tracking

none

## Resolution and regression

`ResidentByteArray` now internalizes all eight declarations with their exact
final-LCNF signatures. Nat and USize reads perform checked bounds handling
before addressing the Wasm32 heap; wide loads and stores preserve little-
endian scalar bits. Consuming writes and appends reuse an exclusive input when
capacity permits, otherwise allocate a packed copy and consume one ordinary
reference while leaving persistent boundary values unchanged.

The zero-import standalone external-engine fixture checks ordinary and wide
reads, unaligned little-endian loads, exclusive and shared 32/64-bit stores,
capacity-preserving byte append, append growth, shared append, zero- through
eight-byte `pushUInt64LE`, upper-bound traps, and counts above eight. It also
ratchets identity and heap-frontier stability for the exclusive paths.
