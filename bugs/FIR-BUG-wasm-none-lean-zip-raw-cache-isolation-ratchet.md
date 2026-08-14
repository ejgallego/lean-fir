---
id: FIR-BUG-wasm-none-lean-zip-raw-cache-isolation-ratchet
status: confirmed
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

unresolved
