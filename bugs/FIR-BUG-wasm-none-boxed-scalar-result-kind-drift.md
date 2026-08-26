---
id: FIR-BUG-wasm-none-boxed-scalar-result-kind-drift
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-26
reproduction: Fir/Wasm/WellFormed.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

FIR rejects Lean-generated `_boxed` adapters whose exact result is `tagged`
for `UInt16` or `object` for `UInt64`.

## Minimal reproduction

Pass a no-inline `UInt16 -> UInt16` or `UInt64 -> UInt64` identity as a
first-class function through a generic application.  Lean 4.33 generates:

```text
def rawUInt16._boxed value : tagged :=
  let value.boxed := unbox value
  let res := rawUInt16 value.boxed
  let r := box res
  return r

def rawUInt64._boxed value : obj :=
  let value.boxed := unbox value
  dec[ref] value
  let res := rawUInt64 value.boxed
  let r := box res
  return r
```

`Fir.Wasm.Emit.Source.compileModule` rejects each generated declaration as
`ValidationError.unsupportedCode`.

## Exact commands

Inspect upstream's exact boxed-result mapping and FIR's admission rule:

```sh
sed -n '480,500p' \
  /home/egallego/.elan/toolchains/leanprover--lean4---v4.33.0/src/lean/Lean/Compiler/LCNF/Types.lean
sed -n '170,190p' Fir/Wasm/WellFormed.lean
sed -n '315,342p' Fir/Wasm/Emit/ResidentScalarBox.lean
```

The complete diagnostic and observed declarations are recorded in
`Fir/Wasm/Emit/SCALAR_BOXING_CONFORMANCE.md`.

## Expected semantics

Admission accepts the exact result returned by upstream `Lean.Expr.boxed` as
well as the wider `tobject` spelling used at generic cast sites.  The exact
kind must remain available to ownership and closure analysis.

## Actual behavior

`supportedLetDeclKind?` computes `boxResultKind type .tobject`.  That function
refines `UInt8` and floating boxes but leaves `UInt16` and `UInt64` as
`tobject`, so the exact `tagged` and `object` declarations are rejected.

The resident linker likewise recognizes only `.box .uint16 .tobject` and
`.box .uint64 .tobject`; after admission is fixed, exact-result aliases will
remain unresolved unless W7 reuses the corresponding physical helper bodies.

## Proof or differential evidence

The same probe admits and resident-links the generated `_boxed` adapters for
`UInt8`, `UInt32`, and `Float` with zero imports and zero remaining runtime
operations.  Only the two exact kinds above fail before Wasm generation.

The old fixed card `FIR-BUG-wasm-none-precise-box-result-admission` treated
`UInt64 -> object` as malformed.  That negative regression is stale after
FIR's Lean-4.33 upstream alignment made all `UInt64` boxes heap-only.

## Semantic impact

Valid pure Lean programs that use first-class monomorphic `UInt16` or
`UInt64` functions are outside FIR's admitted source fragment even though the
underlying scalar ABI and resident box bodies already exist.

## Classification and triage

This is an admission/result-kind coverage bug, not a boxing-policy change.
The shared checker/lowering repair belongs to integration/W6 review; W7 owns
the dependent resident aliases.  The repair must enumerate the exact upstream
result for each scalar rather than accepting every object-like kind.

## Workaround

none

## Upstream tracking

none; FIR is rejecting valid upstream final LCNF.

## Resolution and regression

The shared checker now derives the only legal exact result annotation from
upstream `Lean.Expr.boxed`, while retaining the existing generic `tobject`
path.  Exact `UInt16 -> tagged` and `UInt64 -> object` programs admit and lower;
`UInt16 -> object` and `UInt64 -> tagged` remain rejected.

W7 installs signature-specific aliases generated from the same physical-body
factories as the generic `UInt16` and `UInt64` helpers.  The standalone module
has module-owned memory and zero imports; exhaustive `UInt16` and boundary
`UInt64` round trips cover both generic and exact aliases.  The later
seven-family source-generated ratchet remains a coverage consolidation, not a
workaround or blocker for this fixed discrepancy.
