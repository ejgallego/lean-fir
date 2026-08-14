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

Current-step admission should accept exactly the compiler-produced, well-typed
return boundary. Object-family ABI kinds share one Lean/Wasm calling
representation, but physical compatibility alone is not a semantic coercion:
specializing `.tobject` to `.object` additionally requires that the returned
semantic value is a heap reference, and specializing it to `.tagged` requires
that the value is tagged. The proof boundary must therefore retain either the
directional refinement already sufficient for `ValueRel.ofRefines`, or the
upstream typing/value-shape invariant that justifies the reverse orientation.

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
the production validator and lowering accept. This is a missing compiler-domain
invariant rather than evidence that the generated physical return lane is
wrong. Simply replacing directional refinement by `leanCompatible` in the
proof would be unsound for arbitrary raw LCNF: a `.tobject` relation may contain
a tagged reference that cannot be rebound to an `.object` caller local.

## Classification and triage

Retain the production `leanCompatible` equation, but do not use it directly as
a `ValueRel` transport. Add the smallest phase typing/value-shape invariant at
the supported-function boundary and derive either directional refinement or
the appropriate semantic narrowing at return/pop. Re-run the full return/pop
dependency cone.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. `ConcreteStructuredValidationFocus.return_eq` preserves the exact
production compatibility judgment. The attempted direct contract replacement
was rejected because `ConcreteStructuredYieldFocus.advance_pop_*` must call
`PhysicalValueRel.ofRefines` when rebinding the caller local. Resolution now
depends on making the upstream typing/value-shape fact proof-visible rather
than weakening that semantic transport.
