---
id: FIR-BUG-wasm-none-packed-scalar-projection-kinds
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/talos/artifact/resident-read-projections-client.mjs
---

# Summary

Resident constructor projection internalizes packed `UInt8` fields only. The
same compiler/runtime surface admits all scalar ABI kinds, and real Level-1
lean-zip retains a packed `UInt64` projection as a host operation.

## Minimal reproduction

Capture and resident-link `Zip.Wasm.compressLevel1`. After closure projection
and integer boxing coverage lands, `.scalarProj 1 0 .uint64` is one of only two
remaining runtime operations.

## Exact commands

Run the `ProbeLevel1.lean` command documented by
`integration/lean-zip/README.md` and inspect
`integration/lean-zip/_build/level1-probe.json`.

## Expected semantics

Packed scalar projection computes
`headerBytes + semanticSlotBytes * width + byteOffset` and performs the typed
load selected by the result ABI. Narrow integers are zero-extended; 64-bit and
floating lanes preserve their exact bits.

## Actual behavior

`readProjectionName?` and `readProjectionFunction` recognize only `UInt8`, so
the generic resident linker retains every other packed scalar projection.

## Proof or differential evidence

The concrete host already implements typed packed-scalar reads for `UInt8`,
`UInt16`, `UInt32`, `UInt64`, `Float32`, and `Float`. The symbolic Wasm surface
already has the required narrow, 32-bit, 64-bit, and reinterpret loads.

## Semantic impact

Structures with packed fixed-width fields cannot become self-contained Wasm;
the gap directly blocks the real ByteArray/bitstream closure.

## Classification and triage

W7 executable helper coverage over an existing ABI and concrete layout. W6
owns the helper refinement theorem and packed-coordinate preconditions.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Projection naming and typed loads now cover every scalar ABI kind. The real
`.scalarProj 1 0 .uint64` coordinate passes raw-layout and concrete-host V8
checks with its exact 64-bit payload, and the Level-1 closure reaches zero
remaining runtime operations.
