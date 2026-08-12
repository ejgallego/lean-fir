---
id: FIR-BUG-wasm-none-lean-zip-string-of-list-import-frontier
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: lean-zip-level1-probe
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: integration/talos/artifact/resident-string-client.mjs
---

# Summary

The generic resident String family does not internalize `String.ofList`, so
the real `Zip.Wasm.compressLevel1` closure retains a host function import even
though its `List Char` input and UTF-8 String result both use already accepted
resident layouts.

## Minimal reproduction

Capture and resident-link `Zip.Wasm.compressLevel1`, then inspect the remaining
ordinary imports in `_build/level1-probe.json`.

## Exact commands

```sh
cd integration/lean-zip
lake --keep-toolchain env lean ProbeLevel1.lean
jq '.remainingImports' _build/level1-probe.json

cd ../talos/artifact
lake exe fir-wasm-artifact resident-string _build/resident-string.wasm
node run-resident-string.mjs _build/resident-string.wasm --require-of-list
```

## Expected semantics

The helper consumes an arbitrary valid resident `List Char`, preserves every
Unicode scalar exactly, allocates one exact-sized UTF-8 String, and handles
ordinary, shared, and persistent list spines using Lean reference-counting
semantics. It must not use a host callback.

## Actual behavior

`String.ofList` remains in the external import frontier.

## Proof or differential evidence

Before the repair, the production Level-1 inventory retained
`String.ofList`. After internalization, the zero-import standalone artifact
passes Node/V8 comparisons for empty, ASCII, BMP, and supplementary Unicode
inputs. It also checks that unique spines are reclaimed and shared spines
consume exactly one reference. The production probe no longer lists
`String.ofList` among its two remaining generated List imports.

## Semantic impact

Level-1 compression cannot satisfy the self-contained zero-import package
contract. A host implementation would expose resident object addresses and
split ownership semantics across the Wasm/JavaScript boundary.

## Classification and triage

This is a W7 resident-runtime coverage defect. It requires no new concrete
layout or symbolic-Wasm contract.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ResidentString` now recognizes the exact `tobject -> object` final-LCNF
signature and installs the required generic UInt32 unbox and increment helpers
when the captured source did not otherwise request them. The implementation
walks the list once to validate Unicode scalars and compute the checked UTF-8
extent, allocates one exact-sized String, then walks it again to encode bytes
while consuming the owned spine with the accepted recursive release protocol.

The zero-import external-engine fixture covers empty and mixed one- through
four-byte Unicode strings, unique-spine reclamation, and exact one-reference
consumption of a shared spine.
