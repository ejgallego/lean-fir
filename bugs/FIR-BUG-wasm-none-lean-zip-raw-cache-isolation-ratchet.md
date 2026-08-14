---
id: FIR-BUG-wasm-none-lean-zip-raw-cache-isolation-ratchet
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: deterministic-package-gate
first-seen: 2026-08-14
reproduction: integration/lean-zip/package-raw.mjs
regression: integration/lean-zip/raw-closure-contract.json
---

# Summary

The accepted final-LCNF compiler-unit cache-isolation repair changes
lean-zip's regenerated source closure from 702 to 662 declarations, but the raw
package contract still ratchets the pre-repair closure and stops publication
after all differential and zero-import smoke checks pass.

## Minimal reproduction

Regenerate the production levels 1--10 raw package from accepted main after
`FIR-BUG-wasm-none-final-capture-imported-specialization-reuse` was fixed.
Capture succeeds with 662 declarations, 128 reviewed externals, and zero
unsupported declarations. The package runner later asserts that
`capturedDeclarations` is still 702.

## Exact commands

```sh
cd integration/lean-zip
LEAN_ZIP_ROOT=/tmp/fir-lean-zip-30737 \
ZIP_COMMON_ROOT=/tmp/fir-zip-common-4425 \
FIR_ALLOW_DIRTY_PACKAGE=1 \
FIR_RAW_PACKAGE_PREVIEW_DIR=/tmp/fir-array-upstream-raw \
node package-raw.mjs
```

## Expected semantics

An intentional final-LCNF cache-policy change must be followed by review and
an atomic update of every exact closure inventory it changes. The raw package
must either reproduce the accepted inventory or ratchet a reviewed new one
with unchanged native/Wasm results and deterministic bytes.

## Actual behavior

The regenerated artifact passes the native/Wasm dispatcher matrix for five
cases at all ten levels, its zero-import adapter, and persistent-cache/scratch
ownership checks. Publication then fails with `662 !== 702`. The new inventory
has 534 source functions and 2,598 resident helpers, versus 574 and 2,703 in
the accepted package.

## Proof or differential evidence

The declaration change occurs during source capture, before resident Array
linking, so it is independent of the proof-indexed Array hot-body update that
exposed the stale gate. Comparing retained function names gives 94 old-only
and 54 new-only generated declarations, primarily specialization numbering,
lambda/closed helpers, and the boxed wrappers intentionally regenerated under
the corrected compiler-unit cache policy. Reviewed externals remain 128,
unsupported declarations and runtime operations remain zero, and all executed
output digests agree with native Lean.

## Semantic impact

Accepted main cannot publish a fresh immutable lean-zip raw package through
its documented deterministic gate. Weakening only the declaration-count
assertion would risk accepting an unreviewed closure or stale metadata.

## Classification and triage

This is a stale package-inventory contract following an intentional generic
compiler correction. Review the complete source/resident/function and byte
inventories, then update the contract and package metadata atomically in a
standalone W7 commit before publishing any new canonical package.

## Workaround

Use the generated `_build` artifact only as local differential evidence. Do
not advance the canonical pointer or relax the exact contract.

## Upstream tracking

none

## Resolution and regression

Resolved by reviewing and ratcheting the complete post-isolation inventory
rather than weakening the declaration-count assertion. The accepted closure
has 662 declarations, 128 reviewed externals, 534 retained source functions,
2,598 resident helpers, and 3,132 complete functions. Base, frontier, and
complete Wasm are respectively 1,050,780, 1,570,637, and 902,411 bytes.

The 94 old-only and 54 new-only source names were audited as regenerated
specializations, lambda/closed helpers, and boxed-wrapper changes caused by
the corrected compiler-unit cache policy. Resident Array, ByteArray,
Nat/Int, String, and fixed-width/Float family counts are unchanged. Closure
allocator, matcher, projection, and cache helper counts follow the smaller
source closure; setter/release changes reflect the regenerated ownership
shapes. The external count stays 128, the exact frontier remains
`Float.ofNat`, `Float.ofScientific`, and `Float.log2`, and runtime operations
remain zero.

`raw-closure-contract.json` now also pins SHA-256 digests of the ordered
external, retained-source, resident-helper, and complete-function inventories.
This turns a future same-count name change into a deterministic package-gate
failure. Repeated complete generation, the five-case-by-ten-level native/Wasm
matrix, zero-import adapter, and persistent-cache/scratch reclamation checks
all pass before immutable publication.
