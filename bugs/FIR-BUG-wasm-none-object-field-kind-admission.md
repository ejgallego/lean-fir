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

The 2026-08-28 source-invariant audit sharpened this boundary.  The current
predicate quantifies over every `RefinementWitness`, so a source environment
containing a heap reference cannot prove it: another otherwise valid witness
can map that location to a word carrying a conflicting proof-only constructor
descriptor.  The theorem
`concreteObjectFieldKindAligned_not_of_sourceLocation_alone` is the checked
counterexample.  A complete repair must retain constructor-schema provenance
in final-LCNF typing and connect that provenance to the active refinement
witness at the source/target relation boundary.  Treating the universal
witness predicate itself as a source-only `MachineState` invariant would only
rename the missing proof.

The proof-side bridge is now implemented without weakening that diagnosis.
`ConstructorSchema` retains the source allocation/reuse layout by semantic
location, `ConstructorSchema.WitnessAgrees` relates it to the active witness,
and `ConcreteObjectFieldKindAlignedAt.of_schema` derives the selected field ABI
for precisely that witness.  Fresh allocation and in-place reuse have separate
agreement-transport theorems.  This is infrastructure, not yet a production
fix: the schema/agreement pair still has to be threaded through the closed
validated simulation before the old universal effect-admission premise can be
removed.

Both local closed-successor proofs now consume the replacement boundary:
`advance_objectFieldFVar_of_schema_step` and
`advance_objectFieldErased_of_schema_step` derive alignment for the active
witness and reuse a common mutation transport. The remaining gap is global
state threading and dispatcher selection, not the concrete field writer.

The validated ordinary-code dispatcher now also consumes this boundary.
`ConcreteStructuredSchemaCodeStepAdmission` separates established admission
from the two source-schema field cases, and
`advance_of_schemaSourceReady` sends those cases to the active-witness
successors without the universal premise. The bug remains open because the
module-global validated relation does not yet retain and preserve the evolving
schema/agreement pair across its administrative and allocation transitions.

The module-global carrier is now explicit and sound under proof irrelevance:
the active witness is an index of
`ConcreteStructuredValidatedCodeGlobalOutcomeAt`, not data projected from the
old `Prop` proof. The schema-enriched relation existentially retains this index
and agreement, erases to the old validated relation, and is preserved by both
object-field successors. Remaining work is preservation across the other
administrative and witness-changing transitions; the card stays open.

The witness-preserving administrative cone is now separated from genuine
witness evolution. Direct and saturated entry, lazy hit/miss, external bind,
and return-pop successors close in
`ConcreteStructuredValidatedCodeGlobalOutcomeAt` at the same witness; the old
global dispatcher only forgets that index. A resolved external host call, by
contrast, returns a `nextWitness` and therefore belongs to the explicit
witness-extension proof. Constructor allocation/reuse and the resulting full
schema-global dispatcher remain outstanding, so this is still proof-side
infrastructure rather than resolution of production admission.

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
pointwise descriptor equality consumed by the existing runtime theorem, but
the checked counterexample shows that it is not yet the right derivable
source-invariant interface. The active-witness schema bridge now provides the
right replacement boundary and its allocation/reuse transports, but it is not
yet connected to the production dispatcher. It does not by itself fix
production admission or establish final-LCNF type soundness.
