---
id: FIR-BUG-impure-none-generated-external-source-ancestor
status: candidate
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: invariant-check
first-seen: 2026-08-11
reproduction: integration/verso-flat/check.sh
regression: none
---

# Summary

Final-LCNF closure discovery stops at environment-visible generated helper
names instead of recompiling their source declarations, leaving ordinary Lean
`Id` and `StateT` implementations as unresolved Wasm externals.

## Minimal reproduction

Compile the published, compiler-neutral
`VersoSlides.Pretty.formatRenderedForRuntime` from commit `fd46619`. Its use of
ordinary `StateM` and `String.join` exposes generated names such as
`StateT.instMonad._redArg._lam_1`; closure discovery treats that generated name
as its own environment declaration rather than selecting the compilable
`StateT.instMonad` source ancestor.

## Exact commands

```sh
cd integration/verso-flat
VERSO_ROOT=/tmp/verso-flat-published lake --keep-toolchain --reconfigure \
  -KversoRoot=/tmp/verso-flat-published build VersoFirFlat.Examples
VERSO_ROOT=/tmp/verso-flat-published lake --keep-toolchain \
  -KversoRoot=/tmp/verso-flat-published env lean Emit.lean
```

## Expected semantics

The final-captured internalized closure should compile body-bearing Lean
source ancestors and leave only explicitly retained runtime primitives at the
Wasm frontier.

## Actual behavior

The base module retains generated `Id.instMonad` and `StateT` lambdas plus
`Array.toList`, `String.append`, and related source declarations as externals.
Resident String selection then sees a partial primitive frontier and fails at
the absent `String.Internal.append` declaration.

## Proof or differential evidence

`prettyM-flat-base.wasm.json` contains the unresolved generated monad helpers
and source declarations. Selecting source ancestors is not sufficient: the
imported environment already owns `Id.instMonad._lam_0` through `_lam_6`, so
recompiling `Id.instMonad` in either a synthetic or separately merged unit
produces `_lam_7` onward while the entry retains calls to the imported names.

## Semantic impact

Compiler-neutral functions that use ordinary polymorphic Lean APIs require
source rewrites or app-specific resident helpers even when their transitive
source bodies are available. This defeats generic isolated-function package
generation.

## Classification and triage

This is a FIR final-LCNF source-boundary limitation. Exact generated bodies
from a precompiled module are not stored as replayable final LCNF unless that
module was built with the postponed-compile source-view mechanism. The Wasm
lowerer and runtime correctly refuse the unresolved frontier; recompiling an
ancestor under different generated names is not a sound substitute.

## Workaround

The unpublished Verso probe rewrites the source to explicit specialized monad
and join helpers. That workaround must not be used for accepted publication.

## Upstream tracking

none

## Resolution and regression

unresolved
