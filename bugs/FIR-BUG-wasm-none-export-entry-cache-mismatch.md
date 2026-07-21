---
id: FIR-BUG-wasm-none-export-entry-cache-mismatch
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-21
reproduction: integration/talos/FirTalos/Differential.lean
regression: integration/talos/artifact/check.sh
---

# Summary

The Talos differential harness evaluates its FIR oracle by invoking the entry
as a declaration, while the generated Wasm export enters the declaration body
directly. For a zero-argument declaration, only the former installs a lazy
cache frame.

## Minimal reproduction

Run the `string-heap` artifact fixture after cached heap values are marked
persistent. The FIR side returns a persistent string because `runProgram`
caches `main`; the Wasm side returns the ordinary allocation produced by the
exported `main` body.

## Exact commands

```sh
integration/talos/artifact/check.sh
```

## Expected semantics

The differential source boundary for an exported Wasm function should match
the proof-facing `sourceCodeState`: bind the export parameters and execute its
body without adding the internal zero-argument declaration cache protocol.

## Actual behavior

`runDifferential` calls `Fir.LeanIR.Impure.runProgram`, whose initial
`invokeName` control pushes a `.cache main` frame for a nullary declaration.
The target runner invokes the lowered function index directly. The mismatch
was previously hidden because cache insertion did not change reachable heap
metadata.

## Proof or differential evidence

The artifact oracle reports the same returned string and location on both
sides, but the FIR cell is `rc = 0, persistent = true` while the target cell is
`rc = 1, persistent = false`. Existing W4 program proofs already relate the
generated function to direct `sourceCodeState` evaluation rather than an
`invokeName` entry frame.

## Semantic impact

Heap ownership metadata in the Talos differential oracle can disagree with
the compiled export even when the exported body is translated correctly.
This obscures cache-persistence regressions and makes successful heap-returning
entry fixtures depend on an unrelated declaration-call convention.

## Classification and triage

This is a Wasm differential-adapter boundary defect. It does not change FIR's
internal declaration-call semantics or the generated lazy-cache protocol.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. The differential harness should execute the selected code export
with exact parameter binding, matching `sourceCodeState` and the generated
function entry. The full artifact check is the permanent regression.
