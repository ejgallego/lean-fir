---
id: FIR-BUG-wasm-none-external-runtime-link-wat-size
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

The shared external-runtime linker converts the merged application to WAT and
loads the complete text into one JavaScript string solely to remove private
runtime exports. A valid 3.27 MB FIR frontier expands beyond Node's maximum
string length and cannot be linked.

## Minimal reproduction

Link the emitted `Zip.Wasm.compressRaw` frontier with the standard math
runtime after enabling the multivalue feature. `wasm-merge` succeeds, then the
linker disassembles the merged binary and calls `readFileSync(..., "utf8")`.

## Exact commands

From the repository root, run:

```text
FIR_ALLOW_DIRTY_PACKAGE=1 \
FIR_RAW_PACKAGE_PREVIEW_DIR=/tmp/fir-lean-zip-raw-preview \
node integration/lean-zip/package-raw.mjs
```

## Expected semantics

Runtime-only exports are hidden with a binary transformation whose memory use
scales with the Wasm module, and the final zero-import module preserves exactly
the frontier export inventory.

## Actual behavior

The intermediate WAT is 441,912,031 bytes. Node raises
`ERR_STRING_TOO_LONG: Cannot create a string longer than 0x1fffffe8
characters` before export removal or optimization.

## Proof or differential evidence

A binary-only `wasm-metadce` graph retaining the seven frontier exports
produces a 2,583,891-byte private module. The existing O3 pass then produces a
1,757,944-byte module with zero imports and exactly those seven exports.

## Semantic impact

Larger otherwise-supported Lean closures cannot consume FIR's standard
runtime package, independent of application correctness or available memory.

## Classification and triage

Replace the WAT regex roundtrip with a generated `wasm-metadce` reachability
graph. Root exactly the frontier export `(name, kind)` inventory, leave every
runtime-only export unrooted, validate the private binary, then optimize it.

## Workaround

None. Raising process memory limits cannot bypass Node's maximum string length
and would retain a structurally unscalable linker design.

## Upstream tracking

none

## Resolution and regression

The linker now builds a binary `wasm-metadce` reachability graph from the
merged export inventory, roots exactly the frontier `(name, kind)` exports,
and verifies the private binary before optimization. The lean-zip regression
reduces the 3,268,554-byte frontier to a 2,583,891-byte private module and a
1,757,944-byte complete module without constructing the 441,912,031-byte WAT
string. The result has zero imports and exactly the seven frontier exports.
