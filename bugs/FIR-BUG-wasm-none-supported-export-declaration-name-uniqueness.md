---
id: FIR-BUG-wasm-none-supported-export-declaration-name-uniqueness
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: f0ee6857e6d175cf5bdf6c1be9342c9a3a51bdb4
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-09
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

`Fir.Wasm.lowerSupported` and `ConcreteSupportedExport` do not retain the
phase boundary's top-level `Program.NamesUnique` invariant. Without it, source
declaration lookup and generated Wasm named-call resolution can select
different declarations.

## Minimal reproduction

Construct a raw impure program containing an internal declaration followed by
an external declaration with the same name. `Program.findDecl?` selects the
first, internal declaration. Lowering puts internal functions after every
import, while `FirTalos.callIndex?` searches declaration imports before
internal functions, so the generated call selects the later external import.

## Exact commands

```text
make talos-setup
make talos-check
```

The compiler-correctness contract should separately guard exact production
call-index selection from a name-unique source program.

## Expected semantics

The supported lowering/correctness boundary should consume the existing
phase invariant that top-level declaration names are unique. Then source
`findDecl?`, symbolic lowering, and Wasm named-call resolution identify one
declaration and one generated function row.

## Actual behavior

`WasmSupported` validates declaration bodies, closure flow, and reuse safety,
but not `Program.NamesUnique`. `ConcreteSupportedExport` therefore cannot prove
that the numeric target recovered from an emitted named call is the exact
generated row selected for the source declaration.

## Proof or differential evidence

The certificate-free hereditary direct-call proof has the exact
`LoweredInternalDeclaration` row for the source-selected callee and the exact
numeric `callIndex?` result emitted by adaptation. Identifying those indices is
false for the internal-then-external duplicate-name program above.

## Semantic impact

The raw `lowerSupported` API can compile a named call to a different
declaration than source evaluation. Normal compiler inputs are expected to
originate from `CheckedImpureProgram`, whose `WellFormedAt.impure` constructor
already carries `Program.NamesUnique`, but the Wasm admission and correctness
surfaces currently discard that fact.

## Classification and triage

This is a compiler-admission and proof-contract defect. The repair should
retain `Program.NamesUnique` at the supported-export boundary and use it to
prove exact call-index selection. It should not weaken source lookup or treat
the numeric target as a call-site certificate.

## Workaround

Require `Program.NamesUnique` explicitly at generated-export construction and
the recursive program theorem until the shared supported-lowering API is made
phase-aware.

## Upstream tracking

none

## Resolution and regression

open
