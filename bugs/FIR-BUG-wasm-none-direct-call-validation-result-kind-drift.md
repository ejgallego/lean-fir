---
id: FIR-BUG-wasm-none-direct-call-validation-result-kind-drift
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: fcd623cbb96f5846b11fb89368f417d04bb9715f
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-26
reproduction: integration/talos/FirTalos/ConcreteStructuredValidation.lean
regression: none
---

# Summary

Residual validation and `DirectInternalCallSite` disagree about the local kind
introduced by an internal named call when the callee result strictly refines
the public `let` annotation.

## Minimal reproduction

Take a supported `.fap` declaration whose public result is `tobject` and whose
selected internal callee has effective result `object` or `tagged`.
`supportedLetDeclKind?` inserts the effective callee result into the validator
row, while `DirectInternalCallSite.resultCompiled` records the destination
local at `resultKind`, the public annotation.

## Exact commands

Run Lean Beam synchronization on
`FirTalos/ConcreteStructuredValidation.lean` after requiring
`ConcreteStructuredAlignedValidationState` at call continuations.  Applying
`letContinuation` to a `DirectInternalCallSite` leaves the unprovable equation
between `site.calleeResultKind` and `site.resultKind`.

## Expected semantics

The proof-side call-site boundary should expose the exact compiler local kind
used by the generated continuation, with any public/effective result
compatibility retained separately for the call boundary.

## Actual behavior

The site exposes only the public destination equation.  Exact residual
validator/compiler agreement can currently be extended only when
`site.calleeResultKind = site.resultKind`.

## Proof or differential evidence

The general non-named `let` bridge closes direct values and saturated closure
calls.  The analogous named-call proof derives the validator kind as
`site.calleeResultKind`, but `site.resultCompiled` concludes a local-get at
`site.resultKind`; neither `refines` nor `leanCompatible` implies equality.

## Semantic impact

This blocks admission-free preservation of the aligned validated relation
across strictly refined internal named-call results.  Exact-result named calls,
all currently supported direct values, and saturated closure calls are not
affected.

## Classification and triage

This is a W6 proof-contract gap.  Repair should determine the authoritative
destination kind emitted by `refineNamedCallLocalKinds`, update the call-site
contract to carry that exact kind, and adapt the direct-call staging/resource
proofs without weakening unrelated mutation contracts.

## Workaround

The closed named-call staging theorem temporarily requires the explicit exact
result equality.  This premise is visible in its public statement and is not
inferred from compatibility.

## Upstream tracking

none

## Resolution and regression

Unresolved.  The aligned validated relation and exact-result named-call
staging theorem are the proof regression boundary.  A future fix must add a
strict-refinement positive regression before this card is marked fixed.
