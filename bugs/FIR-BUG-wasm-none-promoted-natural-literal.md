---
id: FIR-BUG-wasm-none-promoted-natural-literal
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/talos/artifact/resident-literal-client.mjs
---

# Summary

Resident natural literals stop at the narrower wasm32 immediate payload even
when Lean's semantic result is still tagged. The Level-1 zip closure therefore
retains the ordinary constant `4294967296` as its last runtime import.

## Minimal reproduction

Capture and resident-link `Zip.Wasm.compressLevel1`. Once closure, boxing, and
packed projection families are complete, the only remaining runtime operation
is `.literal (.nat 4294967296) .tagged`.

## Exact commands

Run the `ProbeLevel1.lean` command documented by
`integration/lean-zip/README.md` and inspect
`integration/lean-zip/_build/level1-probe.json`.

## Expected semantics

Natural literals through Lean's 63-bit tagged payload limit preserve semantic
tagging. Values above FIR's wasm32 immediate limit use the established
persistent promoted-natural representation with the exact 64-bit payload.

## Actual behavior

`ResidentLiteral.isImmediateNatural` rejects values above `0x7fffffff`, and no
promoted-natural literal family consumes the residual operation.

## Proof or differential evidence

The concrete runtime's `encodeTagged` already specifies and tests this split.
The Level-1 source closure reaches one residual operation with zero unsupported
declarations, confirming this is the final resident-generation boundary.

## Semantic impact

Pure Lean programs containing ordinary powers-of-two or masks above 31 bits
cannot become self-contained wasm32 artifacts despite remaining semantically
tagged in Lean.

## Classification and triage

W7 executable literal coverage using the existing allocator and promoted-tag
layout. W6 owns the `encodeTagged` refinement theorem for the generated helper.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The literal linker now follows the immediate/promoted split through Lean's
semantic tagged limit. Its import-free V8 guard freezes the promoted header,
64-bit payload, allocation extent, concrete-host decoding, and scratch
restoration. The real `4294967296` literal is consumed and the Level-1 closure
reaches zero remaining runtime operations.
