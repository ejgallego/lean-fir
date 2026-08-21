---
id: FIR-BUG-wasm-none-local-binder-name-uniqueness
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 7fd2d2d97feb82ca7d905ec8db13e30c49aeab33
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-14
reproduction: Fir/Wasm/Lower.lean
regression: integration/talos/FirTalos/ConcreteStructuredValidation.lean
---

# Summary

`WasmSupported` checks declaration-parameter identity uniqueness but does not
retain the impure phase's body-binder hygiene invariant. Production local
collection replaces an earlier binding when a later body binder has the same
free-variable name, so the validator's current local kind need not equal the
kind attached to the surviving compiler slot.

## Minimal reproduction

Construct a raw impure declaration with two sequential `let` binders whose
`FVarId` names are equal but whose ABI kinds differ. `collectLocalsCore` inserts
the first binding, then `insertLocal` removes it when it inserts the second.
After reversal, both adapted `localSet` instructions select the single later
slot. At the first source node, `supportedCodeWithJoins` still validates against
the first binding's kind.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteStructuredValidation
```

Inspect `Fir.Wasm.collectLocalsCore`, `Fir.Wasm.insertLocal`,
`ConcreteStructuredValidationFocus.let_eq`, and
`CodeAdaptedWithSuffix.let_eq`.

## Expected semantics

The compiler-correctness domain should retain the ordinary impure-LCNF hygiene
invariant that body binder names are unique within a declaration. Then local
collection cannot replace the current `let` destination, and validator and
production compiler assign it the same ABI kind.

## Actual behavior

`supportedDecl` requires `declarationParameterIdsUnique` but has no body-binder
uniqueness guard. `ConcreteSupportedFunction` retains top-level declaration
name uniqueness, not `Program.ImpureHygienic` or an equivalent declaration-
local invariant. The universal admission proof can recover the destination
index from adaptation but cannot soundly identify its ABI kind.

## Proof or differential evidence

`CodeAdaptedWithSuffix.let_eq` proves that the destination name occurs in the
final `functionBindings` row. `ConcreteStructuredValidationFocus.let_eq` proves
the kind selected at the current source node. Equating the two is false for
the duplicate-binder raw program because the lowerer's final row retains only
the later insertion.

## Semantic impact

The raw supported-lowering API admits structurally invalid impure LCNF for
which source validation and generated local layout can disagree. Normal Lean
compiler output is expected to satisfy impure hygiene, but the current Wasm
correctness boundary discards that phase fact.

## Classification and triage

This is a compiler-admission and proof-contract defect. The repair should
retain or check the existing impure hygiene invariant and prove the collector
agreement theorem from it. It should not add a caller-supplied recursive local
certificate or weaken local-kind equality.

## Proof-interface dependency

Checking `Program.ImpureHygienic` at `WasmSupported` is necessary but is not by
itself a kernel-usable freshness proof. `ImpureHygiene.codeBinders` remains an
opaque `partial def`, so downstream code cannot invert the accepted binder
list to show that a later local cannot replace the current `let` destination.
The shared repair must therefore also expose a transparent structural
consequence (or totalize the existing traversal), as already tracked by
`FIR-BUG-impure-none-opaque-hygiene`. Defining a second Wasm-only binder
certificate would merely duplicate the phase invariant and is not the intended
resolution.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. W6 can continue admission for nodes that do not introduce new
locals. Direct `let`, call-frame suspension, and bind resumption require the
compiler-collector bridge after the hygiene boundary is made explicit.
