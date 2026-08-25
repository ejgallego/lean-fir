---
id: FIR-BUG-wasm-none-repeated-final-capture-code-shape
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-25
reproduction: integration/lean-zip/EmitRaw.lean
regression: none
---

# Summary

Capturing and lowering the same final-LCNF raw lean-zip closure twice inside
one Lean process produces a different optimized code shape on the second run,
so the former package accidentally selected its frontier from a redundant
second compilation.

## Minimal reproduction

In one `run_cmd`, call `LeanZipFir.Compile.compileRawBase` and then
`LeanZipFir.Compile.compileRaw`. The base comes from the first
`captureRaw`/lower pass and the linked frontier from a second pass. Compare
that result with linking the immutable first `ModuleArtifact` through
`LeanZipFir.Compile.linkRawArtifact`.

## Exact commands

From `integration/lean-zip` on FIR `b52710d2`, run the former two-compilation
`EmitRaw.lean`, then run the single-capture candidate and inspect:

```text
sha256sum _build/lean-zip-raw-base.wasm \
  _build/lean-zip-raw-frontier.wasm \
  _build/lean-zip-raw.wasm \
  _build/lean-zip-raw.wasm.functions.json
```

The separately named `node check-raw-determinism.mjs` gate confirms that two
fresh single-capture generator processes reproduce the selected artifact
byte-for-byte.

## Expected semantics

`captureRaw` resets FIR's final-impure capture state and relevant generated
compiler mappings. Repeating it for the same source environment and options
should therefore produce the same source program and final code shape.
Independent consumers should not observe whether another capture ran earlier
in the process.

## Actual behavior

The former second-capture release is 367,201 bytes. Linking the immutable
first captured/lowered artifact produces a 366,826-byte complete module. The
501 final function names, origins, indices, direct callees, source inventory,
resident inventory, imports, exports, and ABI remain unchanged, but 16
optimized function bodies have different byte lengths. The source-only base
changes from 444,470 to 444,465 bytes and the resident frontier from 818,888
to 818,893 bytes.

## Proof or differential evidence

Both artifacts pass all five raw input families at levels 1 through 10 against
native Lean and independent inflate. Both retain zero final imports, the exact
public surface, cache-aware scratch rewind, and the same 630 source functions
plus 830 resident helpers. The strict function-sidecar ratchet is what exposed
the 16 body-shape differences.

## Semantic impact

No execution mismatch is known. The defect makes artifact code shape depend
on earlier compilation work in the same process and caused ordinary package
generation to pay for a second capture/lower merely to select the historical
release shape. Other multi-entry tooling that repeats fresh final-LCNF capture
inside one process may observe similar drift.

## Classification and triage

This is classified as a compiler/capture reproducibility defect. The raw
package repair does not require repeated capture: it serializes the base and
derives the linked frontier from one immutable `ModuleArtifact`. A separate
future minimization should identify which compiler cache survives
`resetCompilerCaches`; broad cache clearing is outside this build-path slice.

## Workaround

Use one captured/lowered artifact per package build and derive all downstream
images from that value. This removes the order dependence instead of selecting
the second-run shape deliberately.

## Upstream tracking

none

## Resolution and regression

Unresolved for the generic repeated-capture API. The lean-zip package no
longer depends on repeated capture; its opt-in determinism gate verifies the
single-capture release across fresh generator processes.
