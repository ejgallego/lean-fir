---
id: FIR-BUG-wasm-none-flat-source-view-stale-reconfiguration
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-11
reproduction: integration/verso-flat/check.sh
regression: integration/verso-flat/package.mjs
---

# Summary

Verso Flat publication can validate one source checkout and commit while its
nested Lake project reuses an olean previously built from a different source
root, producing dishonest package provenance.

## Minimal reproduction

Configure `integration/verso-flat` once against the unpublished
`e9ae2ed6` source view, then invoke `package.mjs` with `VERSO_ROOT` pointing at
published commit `fd46619` without first running the check script's explicit
Lake reconfiguration. Source validation reads `fd46619`, while capture retains
the private `joinChunks`/`renderedMonad` declarations that exist only in
`e9ae2ed6`.

## Exact commands

```sh
cd integration/verso-flat
FIR_ALLOW_DIRTY_PACKAGE=1 \
  VERSO_ROOT=/tmp/verso-flat-published node package.mjs
VERSO_ROOT=/tmp/verso-flat-published bash check.sh
```

## Expected semantics

The source commit and file digest recorded in `BUILD.json` must identify the
exact source module whose olean supplies the final-LCNF entry. Changing
`VERSO_ROOT` must either reconfigure and rebuild that source view or fail.

## Actual behavior

The direct package command produced a zero-import 154,635-byte module with a
90-declaration closure containing `joinChunks`, even though the validated
published source uses `String.join` and contains no such declaration. The
subsequent reconfigured gate rebuilt the real source and exposed a different
closure.

## Proof or differential evidence

The first generated inventory names
`_private.VersoSlides.Pretty.0.VersoSlides.Pretty.joinChunks`; `rg` over the
validated `fd46619` file has no `joinChunks`. After `lake --reconfigure`, the
base descriptor instead names `List.foldl`, `String.append`, and generic
`StateT` helpers.

## Semantic impact

An immutable package could claim a clean remotely reachable source revision
while containing code from a stale local source view. Checksums authenticate
the wrong binary and therefore do not repair the provenance claim.

## Classification and triage

This is a package-harness reconfiguration defect. The capture itself honestly
reports the olean it receives; the harness failed to bind that olean to the
source revision it validated.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`package.mjs` now passes `--reconfigure` on its own focused dependency-cone
build, so package publication cannot rely on the caller having configured the
nested project for the same `VERSO_ROOT`. Reconfiguring from published
`fd46619` back to the pinned `e9ae2ed6` source rebuilt
`VersoSlides.Pretty` and reproduced the exact expected 90-declaration,
154,635-byte provisional artifact.
