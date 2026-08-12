---
id: FIR-BUG-wasm-none-integer-box-kind-coverage
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/talos/artifact/resident-scalar-box-client.mjs
---

# Summary

The resident integer box family implements only the scalar operations needed
by prettyM. Real Lean collection code additionally emits `UInt16` unboxing and
`UInt16`/`UInt32` boxing to `tobject`, which remain unresolved.

## Minimal reproduction

Capture, lower, and resident-link `Zip.Wasm.compressLevel1`. After closure
projection support is complete, three of the five remaining runtime operations
are `.unbox .uint16`, `.box .uint16 .tobject`, and
`.box .uint32 .tobject`.

## Exact commands

Run the `ProbeLevel1.lean` command documented by
`integration/lean-zip/README.md` and inspect
`integration/lean-zip/_build/level1-probe.json`.

## Expected semantics

The helper follows Lean's generic integer box path. `UInt16` always fits a
tagged wasm32 immediate. `UInt32` values through `0x7fffffff` are immediate;
larger values retain their tagged semantics through FIR's persistent promoted
natural representation. Unboxing accepts those canonical representations and
preserves the exact scalar bits.

## Actual behavior

`ResidentScalarBox.runtimeName?` recognizes only `UInt8` boxing/unboxing and
`UInt32` unboxing. The generic resident linker therefore retains all three
operations as host imports.

## Proof or differential evidence

The real Level-1 closure has zero unsupported declarations and reaches a
five-operation post-link frontier. These operations are emitted by the real
final LCNF rather than a handwritten Wasm fixture.

## Semantic impact

Pure Lean APIs using fixed-width collections cannot become self-contained
resident Wasm even though the concrete runtime already models the tagged and
promoted representations.

## Classification and triage

W7 executable helper coverage. The implementation reuses the resident
allocator and the established promoted-natural layout; W6 owns the associated
boxing refinement theorem.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The resident family now boxes/unboxes `UInt16` and boxes `UInt32` to `tobject`.
Its import-free V8 guard exhausts all 65,536 `UInt16` values and checks both
sides of the `UInt32` immediate/promoted boundary, exact headers and payloads,
frontier growth, and invalid traps. The real Level-1 probe consumes all three
operations and ultimately reaches zero remaining runtime operations.
