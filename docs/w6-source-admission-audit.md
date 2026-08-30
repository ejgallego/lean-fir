# W6 source-admission audit

Status: **PA0 complete; PA1 theorem extraction is active.**

This document is the review surface for eliminating caller-provided source
readiness from the public final-LCNF-to-Wasm theorem. It inventories every
current-step target branch before any new invariant or proof relation is
introduced. The classification below was checked against the production
validator, the validated structured relation, the source-step inversion
lemmas, and the schema-aware dispatcher.

The audit is complete: every row has a primary A–E disposition, exact existing
dependencies, an exact missing boundary where applicable, an owner, and a
regression. No class-E semantic discrepancy was found.

## Scope and fixed boundary

The source-side classifiers are:

- `ConcreteStructuredSourceAdmissionSafeAt` — 17 source constructors;
- `ConcreteStructuredSchemaSourceAdmissionSafeAt` — the legacy-compatible
  source classifier plus two schema-specific object-field constructors; and
- `ConcreteStructuredCodeStepAdmission` — 20 exact current-step target
  branches after lazy-cache and case selection are split.

The existing bridges are:

- `ConcreteStructuredValidatedCodeCoreRel.admit_of_source_safe_step`; and
- `ConcreteStructuredValidatedCodeCoreRel.admitSchema_of_source_safe_step`.

PA0 audits the premise supplied as `sourceSafe` to those bridges. PA1 may add
focused semantic producer/provenance lemmas. PA2 derives current-step admission
from the guarded production relation. The audit does not redesign
`ConcreteStructuredValidatedCodeOutcome`, `ConstructorSchema`, the concrete
runtime relation, or the ranked trace simulator.

Only the W6 owner edits
`integration/talos/FirTalos/ConcreteResumableWasm.lean`. Audit and provenance
work uses this document or focused helper modules until an immutable handoff is
ready.

## Common guarded facts

Every row starts with the same guarded production context:

1. `spec : ConcreteSupportedFunction ...` for an actual generated function;
2. `activeResult : spec.sourceResultKind = functionResult`;
3. `related : ConcreteStructuredValidatedCodeOutcome ...`, including its
   validated core, aligned residual validation, validated suspended frames,
   and static/dynamic frame agreement;
4. `sourceStep : executeStep externals source = .next sourceAfter`;
5. the exact active source runtime, environment, code, compiler context, reuse
   facts, and remaining byte budget carried by `related`; and
6. on the schema path, the active `ConstructorSchema` and
   `schema.WitnessAgrees witness` for the same refinement witness.

These guards exclude arbitrary malformed machine states. A row may use facts
projected from them, but may not add a future source execution, target path,
caller-selected invariant, unrelated refinement witness, or program-specific
reachability certificate.

Finite runtime safety is audited separately from compiler admission:

- saturated closure calls may consume `ClosureRetainCapacity`;
- ordinary increment may consume concrete `UInt32` header headroom; and
- allocation-producing direct/external operations consume the separate
  current-frame address-space premise after their exact cost is derived.

## Gap classes

| Class | Meaning | Required disposition |
|---|---|---|
| A | Already derivable | Record the exact theorem composition and add at most a thin assembly lemma |
| B | Hidden interface | Export or factor an existing proved fact without strengthening the relation |
| C | Missing semantic provenance | Retain or derive the smallest producer/use-site fact; no client provenance map |
| D | Finite-resource premise | Keep it in finite-runtime or address-space safety, outside compiler admission |
| E | Semantic discrepancy | Create or reference a bug card before changing any proof or contract |

A row may have a compiler/provenance class and a separate D annotation. Class
D must not obscure whether the compiler-owned portion is A, B, C, or E.

## Settled PA2 theorem boundary

PA2 first derives schema source safety and then reuses the existing schema
admission bridge. This keeps compiler/source classification separate from the
source-step inversion that constructs target admission. The two exact new
interfaces are:

```lean
theorem ConcreteStructuredValidatedCodeOutcome.schemaSourceSafe_of_compiler
    (related : ConcreteStructuredValidatedCodeOutcome ...)
    (schemaAgrees : schema.WitnessAgrees witness)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (provenance : ConcreteStructuredCompilerProvenanceAt ... source) :
    ConcreteStructuredSchemaSourceAdmissionSafeAt schema context sourceModule
      externals functionResult facts sourceRuntime sourceEnv source sourceCode

theorem ConcreteStructuredValidatedCodeOutcome.currentStepAdmission_of_compiler
    (related : ConcreteStructuredValidatedCodeOutcome ...)
    (schemaAgrees : schema.WitnessAgrees witness)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (provenance : ConcreteStructuredCompilerProvenanceAt ... source)
    (finiteRuntimeSafe : ConcreteStructuredFiniteRuntimeSafeAt
      context sourceRuntime sourceEnv sourceCode) :
    ∃ requiredBytes,
      ConcreteStructuredSchemaCodeStepAdmission schema context sourceModule
        externals functionResult facts sourceRuntime sourceEnv requiredBytes
        sourceCode
```

`ConcreteStructuredCompilerProvenanceAt` is a working name for the minimal
PA1 bundle, not permission for a new caller premise. PA1 must construct and
preserve it from checked final-LCNF/compiler facts. The second theorem is a
one-line composition with
`ConcreteStructuredValidatedCodeCoreRel.admitSchema_of_source_safe_step`.
Neither theorem stores successor admission, a target path, or a future
execution.

## Complete current-step branch inventory

The primary class describes construction of the current branch. A B row may
still participate in the cross-branch result-preservation theorem described
below; that does not turn its current admission into a C gap. D annotations
are independent finite-resource overlays.

| # | Target branch | Source-safety constructor | Exact desired conclusion and cost | Exact dependency or missing boundary | Disposition | Class | Owner | Regression |
|---:|---|---|---|---|---|---|---|---|
| 1 | return | `.ret` | `.ret`; cost `0`; exact `SemanticValueAtAbi functionResult` | Existing: `ConcreteStructuredAlignedValidationState.admit_return`, `ConcreteStructuredReturnValueSafeAt.of_semanticBinding`. Missing: `CompilerProvenanceAt.returnBinding`. | Validation proves only carrier compatibility; the active result ABI needs use-site semantic typing. | C | W6-Results | `sumTo`; precise `.object`/`.tagged` negative fixture |
| 2 | direct let | `.directLet` | `.directLet`; cost `directLetAllocationCost decl`; `ReuseBudgetedDirectSupported` | Existing: `ConcreteStructuredValidationFocus.let_eq`, `supportedLetDeclKind?_effectiveLetValueKind`. Missing: `ReuseBudgetedDirectSupported.of_validated_step` from producer typing, reuse evidence, and the source step. | The reverse implication is absent; projection/unbox alignment and reuse provenance are semantic, not Boolean-validator facts. Allocation consumes address-space safety when cost is nonzero. | C + D(address) | W6-Results/Objects | complete direct-operation corpus |
| 3 | pure external | `.pureExternal` | `.pureExternal`; exact `stepCost`; `PureExternalSupported` | Existing: `PureExternalSupported.resultSemanticValueAtAbi`, `PureExternalSupported.bindResult_preservesSemanticEnvAtLocalKinds`. Missing: `PureExternalSupported.of_validated_step` under the named external contract. | Validation and a generic successful external step cannot prove that the response is the canonical Int/Nat/scalar response. Keep a named external semantic contract; derive exact cost/result from it. | C + D(address) | W6-Results | `sumTo`; pure Int/Nat/scalar corpus |
| 4 | direct call | `.directCall` | `.directCall`; cost `0`; `DirectInternalCallSite` | Existing: `supportedLetDeclKind?_effectiveLetValueKind`, `ConcreteStructuredValidatedCodeOutcome.advance_directCall_stage_of_step`. Missing export: `DirectInternalCallSite.of_validated_step`. | All site fields come from residual validation/program lookup plus the successful source step; no new invariant is needed for current admission. Result typing after return is the shared cross-branch PA1 obligation below. | B | W6-Results | `sumTo`; `direct-call` |
| 5 | saturated closure call | `.saturatedCall` | `.saturatedCall`; cost `0`; site, resolution, capture capacity | Existing: `ConcreteStructuredValidatedCodeOutcome.advance_saturatedCall_stage_of_step`, `ConcreteStructuredFiniteRuntimeSafeAt`. Missing: `SaturatedClosureCallSite.of_validated_step` and compiler-derived closed-ingress provenance for `SaturatedClosureCallResolution.closedIngressTarget`. | Static/site and dynamic heap fields are reconstructible, but candidate-table membership of a semantic closure requires closure-origin provenance. Capture retention remains a resource premise. | C + D(capture) | W6-Results | `captured-partial`; mixed closure captures |
| 6 | lazy-cache hit | `.lazyHit` | `.lazyHit`; cost `0`; call/generated environment/current global lookup | Existing: `ConcreteStructuredValidatedCodeOutcome.advance_lazy_stage_of_step`, `ConcreteStructuredLazyReadyAdmission.hit`. Missing export: `ConcreteStructuredLazyReadyAdmission.hit_of_validated_step`. | Compiler/cache identity and hit lookup are already present; factor them. Typing the cached value at `call.resultKind` belongs to the shared result-publication theorem below. | B | W6-Results | cached Nat/String/Array hit cases |
| 7 | lazy-cache miss | `.lazyMiss` | `.lazyMiss`; cost `0`; internal body, exact result class, exclusions, empty lookup | Existing: `LazyCacheInternalMissSupported`, `ConcreteStructuredLazyReadyAdmission.miss`, `ConcreteStructuredValidatedCodeOutcome.advance_lazy_stage_of_step`. Missing export: `ConcreteStructuredLazyReadyAdmission.miss_of_validated_step`. | Context cache generation, internal body, non-object result restriction, and empty lookup are reconstructible. Miss publication shares the result theorem below. | B | W6-Results | miss and first-publication cases |
| 8 | default-only case | `.defaultOnlyCase` | `.defaultOnlyCase`; cost `0`; selected default | Existing: `ConcreteStructuredCodeFocus.caseResult_of_step`, `ConcreteStructuredValidatedCodeCoreRel.productionCasesSupported_of_caseSafe`. Missing: final-phase `ConcreteStructuredCaseAltsNormalized`. | The step supplies selection; validation does not enforce the source selector-order invariant. | C | W6-Cases | default-only corpus |
| 9 | object constructor cases | `.objectCases` | `.objectCases`; cost `0`; `ObjectConstructorCasesSupported` | Existing: `ConcreteStructuredCaseAltsNormalized.objectSupported_of_validation`, `productionCasesSupported_of_caseSafe`. Missing: normalized alternatives, semantic discriminator typing, and reachable-constructor `objectTagsFit`. | Compiler mode/tag bounds are derived; source constructor/tag provenance is not. | C | W6-Cases/Objects | `branch-nat`; constructor cases |
| 10 | scalar UInt8 cases | `.scalarUInt8Cases` | `.scalarUInt8Cases`; cost `0`; `ScalarUInt8CasesSupported` | Existing: `ConcreteStructuredCaseAltsNormalized.scalarSupported_of_validation`, `productionCasesSupported_of_caseSafe`. Missing: normalized alternatives and `SemanticBindingAtAbi sourceEnv cases.discr .uint8`. | A physical `i32`/compatible local does not imply semantic `UInt8`. | C | W6-Cases/Results | `sumTo`; scalar enum cases |
| 11 | persistent increment | `.incPersistent` | `.incPersistent`; cost `0` | `ConcreteStructuredSourceAdmissionSafeAt.inc_of_any_persistence` → `ConcreteStructuredAlignedValidationState.admit_incPersistent` via `admit_of_source_safe_step`. | Closed now; syntax and residual validation suffice. | A | W6-Owner | persistent increment corpus |
| 12 | persistent decrement | `.decPersistent` | `.decPersistent`; cost `0` | `ConcreteStructuredSourceAdmissionSafeAt.dec_of_any_persistence` → `ConcreteStructuredAlignedValidationState.admit_decPersistent`. | Closed now; erased field count needs no additional semantic fact. | A | W6-Owner | persistent decrement/reset corpus |
| 13 | ordinary increment | `.ordinaryIncrement`; source `.incOrdinary` | `.ordinaryIncrement`; cost `0`; exact semantic update | `ConcreteStructuredAlignedValidationState.admit_incOrdinary_of_step`; resource overlay `ConcreteStructuredIncrementHeadroomAt`. | Validation plus source-step inversion closes admission; UInt32 header headroom stays explicit. | A + D(header) | W6-Owner | increment boundary cases |
| 14 | ordinary decrement | `.ordinaryDecrement`; source `.decOrdinary` | `.ordinaryDecrement`; cost `0`; exact release update | `ConcreteStructuredAlignedValidationState.admit_decOrdinary_of_step`. | Closed now; source-step inversion supplies lookup and recursive-release shape. | A | W6-Owner | decrement/recursive-release corpus |
| 15 | explicit delete | `.ordinaryDelete`; source `.del` | `.ordinaryDelete`; cost `0`; delete or erased-zero no-op | `ConcreteStructuredSourceAdmissionSafeAt.del_unconditional` → `ConcreteStructuredAlignedValidationState.admit_del_of_step`. | Closed now; ordinary decoding remains strict and physical zero is only the erased no-op. | A | W6-Owner | delete-erased and ordinary delete |
| 16 | constructor tag mutation | `.constructorTag`; source `.setTag` | `.constructorTag`; cost `0`; exact tag update | `ConcreteStructuredSourceAdmissionSafeAt.setTag_unconditional` → `ConcreteStructuredAlignedValidationState.admit_setTag_of_step`. | Closed now; successful semantic mutation supplies live constructor and tag bound. Schema transition is handled by the existing schema dispatcher. | A | W6-Owner | tag-bound and reuse-tag cases |
| 17 | object-field FVar mutation | schema `.objectFieldFVar` | schema FVar branch; cost `0`; `schema.ObjectFieldFVarTyped` | Existing: `ConcreteObjectFieldKindAlignedAt.of_schema`, schema dispatcher, `admitSchema_of_source_safe_step`. Missing: producer-preserved `schema.ObjectFieldFVarTyped`. | Witness agreement converts schema slot typing to descriptor alignment, but cannot invent the source constructor slot kind. | C | W6-Objects | multi-object and closure-field writes |
| 18 | object-field erased mutation | schema `.objectFieldErased` | schema erased branch; cost `0`; `schema.ObjectFieldKindAt ... .erased` | Existing: `ConcreteObjectFieldKindAlignedAt.of_schema`, schema dispatcher. Missing: producer-preserved erased-slot schema fact. | Active witness agreement is sufficient only after source slot provenance is known. | C | W6-Objects | erased-field reset/delete fixtures |
| 19 | `USize` field mutation | `.usizeField` | `.usizeField`; cost `0`; successful `USizeFieldEffectSupported` | `ConcreteStructuredSourceAdmissionSafeAt.usizeField_unconditional` → `ConcreteStructuredAlignedValidationState.admit_uset_of_step`. | Closed now; validation fixes both lanes and the successful step supplies absolute slot bounds. | A | W6-Owner | packed USize project/update |
| 20 | packed scalar field mutation | `.scalarField` | `.scalarField`; cost `0`; successful `ScalarFieldEffectSupported` | Existing: `ConcreteStructuredAlignedValidationState.admit_sset_of_step`. Missing: producer/schema theorem yielding `ConcreteScalarFieldMutationTyped`. | Validation fixes scalar kind but deliberately provides no packed coordinate/extent/non-overlap fact. | C | W6-Objects | multi-scalar and packed-preserve cases |

## Cross-branch conclusions

1. PA2 derives `ConcreteStructuredSchemaSourceAdmissionSafeAt` first. The
   existing `admitSchema_of_source_safe_step` remains the sole assembly bridge.
2. The reusable result boundary is
   `SemanticBindingAtAbi env fvarId effectiveResultKind`, plus a use-site
   refinement theorem when a return expects `.object` or `.tagged` through a
   coarser public `.tobject` declaration. It is not a new descriptor record.
3. Direct producers each prove one exact `SemanticValueAtAbi` result theorem;
   `SemanticEnvAtLocalKinds.bind_insertLocal` is the single bind-preservation
   theorem. Calls, closure calls, externals, and lazy hit/miss reuse the same
   destination-binding boundary after their common return/publication step.
4. `ConstructorSchema.WitnessAgrees` closes only schema-to-descriptor
   alignment. Rows 17 and 18 still need source producer provenance for the
   schema slot. `concreteObjectFieldKindAligned_not_of_sourceLocation_alone`
   proves that the stronger fact cannot be manufactured from heap location.
5. PA1 needs three negative regressions: precise object/tagged return through
   a coarse carrier, scalar case discrimination through an arbitrary `i32`,
   and object-field mutation with a mismatched schema slot. Existing dynamic
   operation and artifact corpora remain the positive regressions.

Although rows 4, 6, and 7 are class B for current admission, PA1 must also
prove the shared result-publication preservation theorem for direct calls,
saturated calls, pure externals, and lazy hit/miss. This theorem is what makes
compiler provenance inductive; it is not an extra premise of their admission
constructors.

## PA0 completion record

- Inventory: 17 source-safety constructors, 20 target admission branches.
- Primary classes: 7 A, 3 B, 10 C, 0 E.
- Resource overlays: direct-let/external address headroom, saturated-capture
  retention, and ordinary-increment header headroom.
- PA1 result module: return use-site precision, direct producer results,
  external contracts, and call/cache result publication.
- PA1 object module: constructor-schema slot preservation, closure ingress,
  and packed-scalar layout.
- PA1 case module: final-phase alternative normalization plus semantic
  discriminator/tag provenance.
- No class-E bug card was opened. The existing
  `FIR-BUG-impure-case-table-selector-determinism` records the missing phase
  interface behind case normalization; it is not a discovered W6 semantic
  mismatch.
- PA2 constructs schema source safety first and composes the existing schema
  admission bridge, as specified above.
- First PA1 slice: `SemanticValueAtAbi.ofRefines`,
  `SemanticBindingAtAbi.ofRefines`, and
  `SemanticEnvAtLocalKinds.returnValueSafe_ofRefines` close every directional
  return edge. `semanticTObject_not_subtype_object` and
  `semanticTObject_not_subtype_tagged` formally isolate the remaining reverse
  object-family provenance obligation.
- Focused proof cones for PA1/PA2:
  `FirTalos.ConcreteFinalLcnfTyping`,
  `FirTalos.ConcreteStructuredValidation`, and
  `FirTalos.ConcreteResumableWasm`; full exit gates remain `make check`,
  `make talos-check`, `git diff --check`, trust/source-hash gates, and
  `#print axioms` for the public PA3 endpoint.
