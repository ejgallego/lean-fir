---
id: FIR-BUG-wasm-none-external-runtime-link-multivalue
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-13
reproduction: integration/lean-zip/EmitRaw.lean
regression: integration/wasm-runtime/link-runtime.mjs
---

# Summary

The shared external-runtime linker rejects a valid FIR frontier containing
multivalue functions because its Binaryen invocations omit the multivalue
feature.

## Minimal reproduction

Emit the real `Zip.Wasm.compressRaw` frontier, compile the standard math
runtime, and pass both modules to `integration/wasm-runtime/link-runtime.mjs`.
The frontier validates in JavaScript and contains two reachable five-result
functions, but `wasm-merge` rejects their tuple/block types.

## Exact commands

From the repository root, run:

```text
FIR_ALLOW_DIRTY_PACKAGE=1 \
FIR_RAW_PACKAGE_PREVIEW_DIR=/tmp/fir-lean-zip-raw-preview \
node integration/lean-zip/package-raw.mjs
```

## Expected semantics

The deterministic standard-runtime link preserves every Wasm feature already
used by the validated FIR frontier, closes its reviewed math imports, and
returns a zero-import module with exactly the frontier exports.

## Actual behavior

Binaryen reports `Tuples are not allowed unless multivalue is enabled` and
`Multivalue function results (multivalue is not enabled)` for functions 5825
and 5827. Linking stops before application execution.

## Proof or differential evidence

The 3,268,554-byte frontier is accepted by `WebAssembly.Module`, has exactly
the three reviewed Float imports, seven intended exports, and zero runtime
operations. Failure occurs only when the shared linker invokes Binaryen with a
narrower feature set.

## Semantic impact

Any otherwise supported application closure using a multivalue final-LCNF
function cannot be combined with FIR's standard runtime, even though both the
browser engine and FIR emitter accept the module.

## Classification and triage

This is a generic standard-runtime linker configuration bug. Enable
multivalue consistently for the Binaryen pipeline so intermediate validation
cannot use a narrower feature set than the input frontier.

## Workaround

None. Rewriting multivalue source functions would change the compiler boundary
merely to accommodate the packaging tool.

## Upstream tracking

none

## Resolution and regression

The shared linker now passes `--enable-multivalue` consistently through its
Binaryen assembly, merge, meta-DCE, and optimization stages. The real
lean-zip raw frontier links successfully to a 1,757,944-byte complete module
with zero imports and exactly the seven frontier exports.
