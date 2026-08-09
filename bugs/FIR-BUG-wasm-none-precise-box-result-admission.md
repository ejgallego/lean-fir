---
id: FIR-BUG-wasm-none-precise-box-result-admission
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-09
reproduction: Fir/Wasm/WellFormed.lean
regression: none
---

# Summary

FIR rejects a compiler-produced scalar box when final LCNF already declares
the exact `boxResultKind` instead of the older generic `tobject` kind.

## Minimal reproduction

Capture the Lean 4.32 final-LCNF closure of
`VersoSlides.Pretty.formatRenderedForRuntime`. Its rendered event path boxes a
`UInt8` and declares the result as the exact `tagged` kind selected by
`boxResultKind`.

## Exact commands

Run final-LCNF capture followed by `Fir.Wasm.compileProgram` for
`VersoSlides.Pretty.formatRenderedForRuntime`. The support check rejects the
`.box` declaration because `supportedLetDeclKind?` requires the declared kind
to equal `tobject` even though `letValueKind` computes `tagged` for the same
box.

## Expected semantics

A supported scalar box should be admitted when its declared result is either
the generic `tobject` kind or the exact kind returned by `boxResultKind`. The
lowered result and physical representation are unchanged.

## Actual behavior

`supportedLetDeclKind?` accepts only `declared == .tobject`, while the same
module's lowering path intentionally refines `UInt8` boxes to `tagged`.

## Proof or differential evidence

Admitting `declared == .tobject || declared == boxResultKind type declared`
allows the exact closure to lower. With the generic resident UInt8 box helper,
all 256 UInt8 round trips pass in an external Wasm engine, malformed inputs
trap, and the closed Flat module matches native Lean on all nine focused
differential cases.

## Semantic impact

Final LCNF that preserves precise scalar-box result information is rejected,
blocking the Flat rendering closure and any analogous source closure.

## Classification and triage

This is a compiler admission inconsistency between the support checker and
the existing precise-kind lowering rule. The change is a shared contract and
requires integration/W6 review; the W7 resident helper proof remains a
separate generation-ready versus contract-proved handoff.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
