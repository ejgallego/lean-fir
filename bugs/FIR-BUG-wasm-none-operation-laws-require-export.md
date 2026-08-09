---
id: FIR-BUG-wasm-none-operation-laws-require-export
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 871619fb26983c7644cbcf2f49ca18a46d27ece5
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-09
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

The concrete operation-law theorems required `ConcreteSupportedExport`, even
though none of them used export-table membership. Recursive named calls target
ordinary generated internal functions, so their exact production rows could
not instantiate those laws.

## Minimal reproduction

Construct a `ConcreteGeneratedInternalDeclaration` for a source-selected
callee and try to apply the direct-operation theorem needed by
`DirectHereditaryGeneratedOperationLaws.direct`. The row contains the exact
symbolic and adapted functions, but correctly contains no proof that the
callee is exported by name.

## Exact commands

```text
make talos-setup
make talos-check
```

## Expected semantics

Compiler/runtime operation laws should require the static pipeline facts for
the generated function they execute. Only the final named module theorem
should additionally require export-table membership.

## Actual behavior

The reusable pipeline facts and the root export lookup were bundled in one
structure. This made a true internal-function theorem syntactically require a
generally false export proposition.

## Proof or differential evidence

The hereditary direct-call proof derives every function-specific fact from
the real `lowerSupported`/`adapt` row. Its operation-law field remains
unprovable solely because the callee has no `findExport` equation.

## Semantic impact

This is a proof-boundary overconstraint, not an executable compiler bug. It
blocked constructing recursive compiler correctness from the individual
runtime-operation theorems.

## Classification and triage

Factor a `ConcreteSupportedFunction` package containing the reusable static
pipeline facts. Let `ConcreteSupportedExport` extend it with only the export
lookup, and generalize operation laws to the parent package.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ConcreteSupportedFunction` now carries the reusable compiler, adapter,
resolver, and generated-body facts. Export correctness adds only named export
membership. A generated internal row can inherit module-wide facts from the
root pipeline while retaining its own exact function row, and the direct
operation theorem accepts that resulting internal-function package.
