---
id: FIR-BUG-wasm-none-cache-probe-fixed-width-closure-abi
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-13
reproduction: Fir/Wasm/Emit/ResidentFixedWidth.lean
regression: Fir/Wasm/Emit/ResidentFixedWidth.lean
---

# Summary

The focused production lazy-cache probe captures and lowers successfully, but
resident linking rejects `UInt8.toNat` as an incompatible fixed-width external
when the conversion occurs inside `ByteArray.foldl`'s generated closure.

## Minimal reproduction

Compile the unmodified read-only lean-zip diagnostic entry
`Zip.Wasm.distanceCodeCacheProbe : ByteArray -> ByteArray` from source revision
`74e4826cee362d815a11c213894f072ced5e6b0a`. The entry calls the real
`distCodeWordBytesImpl` table accessor once per input byte.

## Exact commands

Configure `integration/lean-zip` with lean-zip's `vir-fir-wasm-port` source
worktree and compile the entry through
`compileEntriesFinalCapturedInternalized`, followed by
the then-current eager persistent-cache arena linker.

## Expected semantics

The conversion should use Lean's ordinary ExplicitBoxing-generated closure
adapter and then the existing signature-checked resident `UInt8.toNat`
implementation. No named application or probe shim is required.

## Actual behavior

The source closure lowers, but the fixed-width resident step reports:

```text
ResidentFixedWidth.LinkError.incompatibleExternal `UInt8.toNat
```

The complete `Zip.Wasm.compressLevel1` closure at the pinned package revision
still links with zero imports and executes correctly, so this is a narrower
closure/wrapper presentation difference exposed by the focused root.

## Proof or differential evidence

The native `zip-wasm-oracle cache-probe` entry is available in the same dirty
read-only lean-zip worktree. FIR execution is blocked before Wasm emission, so
no differential result is published yet.

## Semantic impact

Generic isolated functions using fixed-width conversions inside higher-order
ByteArray traversals may fail self-contained Wasm admission even though the
same raw resident operation and boxed-wrapper generation are supported.

## Classification and triage

This is W7 capture/link selection work. Inspect the captured raw and boxed
signatures and align selection with Lean's ExplicitBoxing presentation. Do not
add a declaration-specific shim or rewrite the lean-zip diagnostic entry.

## Workaround

None.

## Upstream tracking

none

## Resolution and regression

Fixed-width provider validation now compares the actual stricter resident
helper signature with either provider presentation through FIR's directional
ABI refinement relation. Thus the tagged `UInt8.toNat` helper implements both
a precise tagged import and Lean's coarser `tobject` object-family boundary;
parameter kinds remain exact and unrelated result lanes remain rejected. A
symbolic regression covers the precise external presentation while the prior
complete fixed-width artifact continues covering the coarser presentation.

The unmodified `Zip.Wasm.distanceCodeCacheProbe` now captures 61 declarations,
links 232 functions into a 47,587-byte module with zero imports, and agrees
byte-for-byte with `zip-wasm-oracle cache-probe` on empty, repeated 83-byte,
all-byte, and 4,096-byte repeated inputs. Every case passes twice, the
production cache initializes once below the checkpoint, and both executions
rewind to that exact checkpoint.
