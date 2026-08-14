---
id: FIR-BUG-wasm-none-object-field-kind-admission
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 7fd2d2d97feb82ca7d905ec8db13e30c49aeab33
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-14
reproduction: Fir/Wasm/WellFormed.lean
regression: integration/talos/FirTalos/ConcreteStructuredValidation.lean
---

# Summary

Production validation checks that an `.oset` payload is an object-field ABI
kind, but does not check that this kind equals the selected constructor
descriptor slot. The concrete runtime and heap refinement correctly require
that alignment.

## Minimal reproduction

Construct otherwise supported raw impure LCNF that allocates a constructor
whose only object slot is classified `.erased`, then executes
`.oset objectId 0 (.fvar childId) continuation` with `childId` classified
`.object`. The `.oset` branch of `supportedCodeWithJoins` accepts both locals
because `.object.isObjectField = true`; it retains no constructor field-kind
vector for `objectId`.

The same mismatch can be formed in the other direction by writing `.erased`
to a descriptor slot classified `.object`.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteStructuredValidation
```

Inspect the `.oset` branch of `Fir.Wasm.supportedCodeWithJoins`,
`ObjectFieldFVarEffectSupported`, `ObjectFieldErasedEffectSupported`, and
`objectSetStep_of_refines_with_capacity`.

## Expected semantics

The supported compiler domain should establish that the selected constructor
descriptor slot has the same ABI kind as the payload selected by lowering.
This may be checked by production validation or derived from an explicit,
preserved source-LCNF typing invariant.

## Actual behavior

Validation checks only that the object local is `.object` and that the payload
kind satisfies `AbiKind.isObjectField`. It does not connect the numeric field
index to a constructor descriptor or field-kind vector.

## Proof or differential evidence

Residual validator inversion derives the object local, payload local, and
`isObjectField` guard. A successful source step derives the live constructor,
semantic update, and slot bound. Neither fact determines
`fieldKinds[index]? = some fieldKind`, which is the remaining premise of the
sound concrete mutation theorem.

`ConcreteObjectFieldKindAligned` in the regression module isolates exactly
this missing source-typing fact. With it, both FVar and erased current-step
admission are derivable without inspecting target execution.

## Semantic impact

The mismatch is ownership-relevant. If a descriptor classifies a slot erased
while raw accepted LCNF installs a heap object, source recursive ownership sees
the semantic child but target descriptor-driven ownership omits it. The
opposite mismatch can make the target interpret an erased zero as an owned
object slot. Upstream Lean-generated LCNF is expected to exclude these cases,
but FIR's accepted raw-LCNF domain currently does not state that restriction.

## Classification and triage

This is a compiler-admission defect. Prefer a clean source typing/provenance
invariant, or an equivalent executable validator analysis, over a per-step
translation certificate. Do not weaken ordinary object decoding or erase
descriptor distinctions merely because all object-field ABI kinds occupy an
i32 lane.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Pending. The proof-side `ConcreteObjectFieldKindAligned` boundary documents the
minimal missing invariant and unblocks refinement experiments that explicitly
assume well-typed source states; it does not fix production admission by
itself.
