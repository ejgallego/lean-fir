---
id: FIR-BUG-wasm-none-zero-arg-initializers
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-16
reproduction: Fir/Wasm/Lower.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

The symbolic lowerer classifies every zero-parameter function as an initializer, including ordinary entrypoints such as `main`.

## Minimal reproduction

Lower `Fir.Wasm.abiLiteralProgram`: its sole declaration is the explicitly invoked zero-argument function `main`, but the resulting symbolic module records `main` in `Module.initializers`.

## Exact commands

Run `lake build Fir.Wasm.Examples` from the repository root and inspect the guarded lowered literal module.

## Expected semantics

Initializer metadata should identify declarations whose initialization or lazy-global semantics must run implicitly. Parameter count alone does not establish that role.

## Actual behavior

`Fir.Wasm.lower` populates `initializers` by selecting every declaration with an empty parameter array, so normal zero-argument functions are indistinguishable from implicit initialization work.

## Proof or differential evidence

The W1 module checker must reject unsupported implicit initialization while continuing to accept explicitly invoked zero-argument constructor/case fixtures. The current metadata makes those requirements contradictory.

## Semantic impact

An adapter that interprets this metadata would spuriously execute ordinary functions as initializers; an adapter that rejects it cannot accept the first correctness corpus.

## Classification and triage

This is local to the provisional Wasm lowerer. Final impure `Decl` currently provides no checked initializer role used by this backend, so the heuristic cannot be repaired by refining the parameter-count test.

## Workaround

Emit no implicit initializers until an explicit initialization design and source marker are implemented. The W1 checker rejects hand-built symbolic modules with nonempty initializer metadata.

## Upstream tracking

none

## Resolution and regression

Resolved in W5.7 by replacing the parameter-count heuristic with a scan for
actual zero-argument calls. `Module.initializers` is now the ordered lazy-cache
registry: each entry gets a flag/value global pair, and ordinary uncalled
zero-argument functions such as `main` are not executed implicitly.

`FirTalos.DifferentialExamples.cachedExternalProgram` calls one zero-argument
external twice and checks that source and target both perform exactly one
external event and world update while retaining the semantic cached global.
`Fir.Wasm.Emit.Examples.abiCachedExternalProgram` checks that the corresponding
global-bearing standard Wasm binary encodes successfully.
