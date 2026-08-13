---
id: FIR-BUG-wasm-none-return-admission-refinement-direction
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 7fd2d2d97feb82ca7d905ec8db13e30c49aeab33
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-13
reproduction: integration/talos/FirTalos/ConcreteStructuredValidation.lean
regression: integration/talos/FirTalos/ConcreteStructuredSimulation.lean
---

# Summary

Production source validation accepts returns using `AbiKind.leanCompatible`,
while `ConcreteStructuredCodeStepAdmission.ret` requires the strictly
directional `AbiKind.refines` relation.

## Minimal reproduction

Take an active function result kind `.object` and a returned local tracked as
`.tobject`. The production validator accepts the node because both kinds use
Lean's object-family calling representation:

```text
AbiKind.tobject.leanCompatible AbiKind.object = true
```

The current proof admission constructor rejects the same node:

```text
AbiKind.tobject.refines AbiKind.object = false
```

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteResumableWasm
```

Inspect `ConcreteStructuredValidationFocus.return_eq` and
`ConcreteStructuredCodeStepAdmission.ret`.

## Expected semantics

Current-step admission should accept exactly the compiler-validated return
boundary. Object-family ABI kinds share one Lean/Wasm calling representation;
the proof contract may retain their precise semantic kinds without imposing a
direction that the compiler does not require.

## Actual behavior

The executable compiler domain is wider than the proof admission domain for
one orientation of compatible object-family returns. Root validation can
therefore derive `leanCompatible = true` but cannot construct the current
`.ret` admission constructor.

## Proof or differential evidence

`ConcreteStructuredValidationFocus.return_eq` is an exact inversion of the
total production validator. Its conclusion is `actual.leanCompatible expected
= true`. The corresponding admission constructor asks for
`actual.refines expected = true`; only the converse implication is available
in `Fir/Wasm/ABI.lean`.

## Semantic impact

The universal compiler-admission theorem would exclude a source function that
the production validator and lowering accept. This is a proof-contract
overstrengthening, not evidence that the generated physical return lane is
wrong.

## Classification and triage

Repair the admission and return-preservation contracts to use the production
compatibility relation, then retain directional refinement only at runtime
boundaries that genuinely need it. Re-run the full return/pop dependency cone.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. `ConcreteStructuredValidationFocus.return_eq` is the proof-side
regression that preserves the exact production compatibility judgment. The
next slice will adapt `.ret` admission and its return/pop dependency cone.
