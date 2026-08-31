# W6 source-admission audit

Status: **PA0 complete; PA1 theorem extraction is active; case admission is
compiler-derived.**

This document is the review surface for eliminating caller-provided source
readiness from the public final-LCNF-to-Wasm theorem. It inventories every
current-step target branch before any new invariant or proof relation is
introduced. The classification below was checked against the production
validator, the validated structured relation, the source-step inversion
lemmas, and the schema-aware dispatcher.

The audit is complete: every row has a primary A–E disposition, exact existing
dependencies, an exact missing boundary where applicable, an owner, and a
regression. Subsequent PA1 extraction found one class-E discrepancy in the
object-case runtime ABI and one previously hidden directional compiler-policy
decision at named-call boundaries; both are recorded below rather than hidden
inside a site constructor.

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

The PA2 framework now enforces that boundary in its theorem type:
`ConcreteStructuredCompilerCurrentStepAdmission.code` consumes the exact
`ConcreteStructuredValidatedCodeOutcome`, rather than an arbitrary
admission-free `ConcreteStructuredCodeCoreRel`. Its finite-prefix packaging
preserves the validated global relation. Residual validator facts are
therefore compiler-transported inputs to admission, not a caller invariant and
not something the operational core is incorrectly expected to reconstruct.

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
| 1 | return | `.ret` | `.ret`; cost `0`; exact `SemanticValueAtAbi functionResult` | Existing: `ConcreteStructuredAlignedValidationState.admit_return`, `ConcreteStructuredAlignedValidationState.returnSemantic_ofUseSite`, and `ConcreteStructuredReturnUseSiteProvenanceAt`. Missing: construct the latter from the precise producer origin on non-directional object-family edges. | `SemanticEnvAtLocalKinds.ofStateRelated` derives ordinary local typing from the live relation. Validation still proves only carrier compatibility at a non-directional use, so the precise producer-origin fact remains genuinely semantic. | C | W6-Results | `sumTo`; precise `.object`/`.tagged` negative fixture |
| 2 | direct let | `.directLet` | `.directLet`; cost `directLetAllocationCost decl`; `ReuseBudgetedDirectSupported` | Existing: `ConcreteStructuredValidationFocus.let_eq`, `supportedLetDeclKind?_effectiveLetValueKind`. Missing: `ReuseBudgetedDirectSupported.of_validated_step` from producer typing, reuse evidence, and the source step. | The reverse implication is absent; projection/unbox alignment and reuse provenance are semantic, not Boolean-validator facts. Allocation consumes address-space safety when cost is nonzero. | C + D(address) | W6-Results/Objects | complete direct-operation corpus |
| 3 | pure external | `.pureExternal` | `.pureExternal`; exact `stepCost`; `PureExternalSupported` | Existing: `PureExternalSupported.resultSemanticValueAtAbi`, `PureExternalSupported.bindResult_preservesSemanticEnvAtLocalKinds`. Missing: `PureExternalSupported.of_validated_step` under the named external contract. | Validation and a generic successful external step cannot prove that the response is the canonical Int/Nat/scalar response. Keep a named external semantic contract; derive exact cost/result from it. | C + D(address) | W6-Results | `sumTo`; pure Int/Nat/scalar corpus |
| 4 | direct call | `.directCall` | `.directCall`; cost `0`; `DirectInternalCallSite` | Existing: `supportedNamedCall_internal_facts`, `effectiveDeclarationResultKind?_declared_refines`, `ConcreteStructuredAlignedValidationState.directInternalCallBoundary`, `ConcreteStructuredValidationLocalsAgree.compileArgs_of_supported`, and `DirectInternalCallCompilerAdmission.toSite_of_step` reconstruct the result direction, exact destination local, and operational site. Missing: semantic ingress for carrier-compatible arguments whose compiler row is `tobject` but whose parameter requires `object`. | Production now requires the effective callee result to directionally refine the source `let` result for non-cached calls. Across W7's 11,487 result edges no product edge was rejected; the full validation corpus additionally preserves a legitimate compatible reverse object-family result for the separate nullary-cache lane. All 158 non-refining argument edges are exactly `tobject -> object`, so argument provenance is the sole remaining ordinary direct-call gap. | C(arguments only) | W6-Results | `sumTo`; `direct-call`; reverse result negative fixture; `tobject -> object` argument fixtures |
| 5 | saturated closure call | `.saturatedCall` | `.saturatedCall`; cost `0`; site, resolution, capture capacity | Existing: `ConcreteStructuredValidatedCodeOutcome.advance_saturatedCall_stage_of_step`, `ConcreteStructuredFiniteRuntimeSafeAt`. Missing: `SaturatedClosureCallSite.of_validated_step` and compiler-derived closed-ingress provenance for `SaturatedClosureCallResolution.closedIngressTarget`. | Static/site and dynamic heap fields are reconstructible, but candidate-table membership of a semantic closure requires closure-origin provenance. Capture retention remains a resource premise. | C + D(capture) | W6-Results | `captured-partial`; mixed closure captures |
| 6 | lazy-cache hit | `.lazyHit` | `.lazyHit`; cost `0`; call/generated environment/current global lookup | `ConcreteStructuredValidatedCodeOutcome.admit_lazyHit_of_compiler` derives the declaration, effective and annotation result lanes, nullary arity, destination local, generated cache environment, and exact hit admission from the current validated outcome. `ConcreteSupportedFunction.residualLocalAlignment` constructs the root row; aligned validation retains it through lets, unchanged-layout continuations, selected case alternatives, and suspended callers. | Crossed PA2 without a cache-specific invariant: the only dynamic fact is the actual semantic global lookup, and it is not chosen by the client. | A | W6-Results | cached Nat/String/Array hit cases |
| 7 | lazy-cache miss | `.lazyMiss` | `.lazyMiss`; cost `0`; initializer execution and empty lookup | `ConcreteStructuredValidatedCodeOutcome.admit_lazy_of_compiler` performs runtime branch selection and derives every shared compiler/cache fact. Its sole additional premise is the named `ConcreteStructuredLazyMissBackendCoverageAt` boundary. | Internal non-object misses are implemented. External initializers and `.object`/`.tobject` result publication are accepted by lowering but not yet covered by this simulator branch; they must be implemented and then delete the backend-coverage premise rather than hiding it in a universal source invariant. | C(backend coverage) | W6-Results | miss and first-publication cases; external/object miss fixtures |
| 8 | default-only case | `.defaultOnlyCase` | `.defaultOnlyCase`; cost `0`; selected default | `ConcreteStructuredValidatedCodeCoreRel.productionCasesSupported_of_validation` and `admit_cases_of_validated_step`. | The source step supplies selection and production validation supplies normalized order; no source-side case classifier remains. | A | W6-Cases | default-only corpus; default-before-constructor rejection |
| 9 | object constructor cases | `.objectCases` | `.objectCases`; cost `0`; `ObjectConstructorCasesSupported` | `ConcreteStructuredValidatedCodeCoreRel.productionCasesSupported_of_validation` derives normalized order, exact object mode, compiled discriminator, directional `.tobject` refinement, and static alternative bounds. Exact `UInt64` object-tag lowering and `LiveHeapRel.tobjectTag_lt_uint64` discharge the dynamic representation boundary internally. | Closed after the non-truncating i64 ABI repair. `ConcreteStructuredValidatedCodeCoreRel.admit_cases_of_validated_step` now constructs zero-cost admission from residual validation and the successful source selection, with no case-safety premise. | A | W6-Cases | promoted tag `UInt32.size`; constructor cases |
| 10 | scalar UInt8 cases | `.scalarUInt8Cases` | `.scalarUInt8Cases`; cost `0`; `ScalarUInt8CasesSupported` | `ConcreteStructuredCaseAltsNormalized.scalarSupported_of_validation`, `productionCasesSupported_of_validation`, and `admit_cases_of_validated_step`. | Production validation derives normalized order, exact `.uint8` mode, compiled local, and every compared-tag bound. | A | W6-Cases/Results | `sumTo`; scalar enum cases |
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

1. PA2 derives `ConcreteStructuredSchemaSourceAdmissionSafeAt` for the
   provenance-dependent families and reuses
   `admitSchema_of_source_safe_step` as their assembly bridge. Case admission
   now bypasses that classifier entirely through
   `admit_cases_of_validated_step`.
2. The reusable result boundary is
   `SemanticBindingAtAbi env fvarId effectiveResultKind`, plus
   `SemanticBindingAtUseSite` only when the actual ABI does not directionally
   refine the use-site ABI. `SemanticEnvAtLocalKinds.ofStateRelated` derives
   the ordinary environment fact from the existing physical state relation;
   it is not a new field of the central relation or a descriptor record.
3. Direct producers each prove one exact `SemanticValueAtAbi` result theorem;
   `SemanticEnvAtLocalKinds.publishResult` is the single source
   bind-preservation theorem. Calls, closure calls, and lazy hit/miss reuse
   `publishPhysicalResult_ofRefines`; pure externals reuse its semantic form.
   Thus hit/miss and call-family publication are closed without a new
   operation-specific invariant.
4. `ConstructorSchema.WitnessAgrees` closes only schema-to-descriptor
   alignment. Rows 17 and 18 still need source producer provenance for the
   schema slot. `concreteObjectFieldKindAligned_not_of_sourceLocation_alone`
   proves that the stronger fact cannot be manufactured from heap location.
5. PA1 needs three negative regressions: precise object/tagged return through
   a coarse carrier, scalar case discrimination through an arbitrary `i32`,
   and object-field mutation with a mismatched schema slot. The case-order
   boundary additionally retains a whole-program default-before-constructor
   rejection. Existing dynamic operation and artifact corpora remain the
   positive regressions.

Rows 6 and 7 have crossed from the original class-B audit into explicit PA2
interfaces: hit admission is closed, while miss admission exposes only named
backend coverage. Row 4's dynamic construction, exact destination, and
non-cached result direction are now compiler-derived. Its sole remaining
ordinary-call gap is directional argument ingress. The nullary cache exception
is separate: it retains the exact `leanCompatible` rule already consumed by
the cache simulator and does not weaken ordinary direct-call admission.

## PA0 completion record

- Inventory: 17 source-safety constructors, 20 target admission branches.
- Initial PA0 classes: 9 A, 3 B, 8 C, 0 E. PA1 extraction reclassified direct
  calls from B to C and object cases from C to E for the exact reasons above.
- Resource overlays: direct-let/external address headroom, saturated-capture
  retention, and ordinary-increment header headroom.
- PA1 result module: return use-site precision, direct producer results,
  external contracts, and call/cache result publication.
- PA1 object module: constructor-schema slot preservation, closure ingress,
  and packed-scalar layout.
- PA1 case module: semantic discriminator/tag provenance. Final-phase
  constructor-prefix/optional-final-default normalization is now enforced by
  `WasmSupported` and derived from residual validation.
- The initial audit opened no class-E card. PA1's exact-tag proof subsequently
  exposed `FIR-BUG-wasm-none-object-case-actual-tag-truncation`. The older
  `FIR-BUG-impure-case-table-selector-determinism` remains a phase-interface
  issue behind case normalization, not this runtime discrepancy.
- PA2 constructs schema source safety first and composes the existing schema
  admission bridge, as specified above.
- First PA1 slice: `SemanticValueAtAbi.ofRefines`,
  `SemanticBindingAtAbi.ofRefines`, and
  `SemanticEnvAtLocalKinds.returnValueSafe_ofRefines` close every directional
  return edge. `semanticTObject_not_subtype_object` and
  `semanticTObject_not_subtype_tagged` formally isolate the remaining reverse
  object-family provenance obligation.
- Second PA1 result slice: `SemanticEnvAtLocalKinds.ofStateRelated` proves that
  the established physical state relation and compiler layout already type
  every residual validator local. `SemanticBindingAtUseSite` and
  `ConcreteStructuredReturnUseSiteProvenanceAt` retain only the exact
  non-directional use-site fact, while
  `ConcreteStructuredAlignedValidationState.returnSemantic_ofUseSite` feeds it
  directly to the existing return simulator. The common
  `publishPhysicalResult_ofRefines` theorem closes direct-call,
  saturated-closure, and lazy hit/miss publication at one boundary.
- Third PA1 result slice factors direct-call construction. Successful source
  staging now yields the evaluated argument array; residual validation plus
  compiler-local agreement yields the exact production `compileArgs`; and
  equal arity constructs the callee environment. The resulting
  `DirectInternalCallCompilerAdmission.toSite_of_step` initially isolated
  exact destination-local selection and the two directional argument/result
  checks.
- Fourth PA1 result slice closes the ordinary direct-call result half.
  Production `supportedNamedCall` now requires directional result refinement
  for non-cached calls, while retaining carrier compatibility for arguments.
  The 11,487 named-call result edges in current prettyM and lean-zip products
  all satisfy that rule. A full-corpus regression exposed one legitimate
  reverse object-family result for a nullary cached declaration, so that
  semantically separate lane deliberately retains `leanCompatible`.
  `effectiveDeclarationResultKind?_declared_refines` proves the general
  selector property, and
  `ConcreteStructuredAlignedValidationState.directInternalCallBoundary`
  derives declaration classification, result refinement, and exact
  destination-local selection from residual validation. Its conclusion
  exposes only the exact `kindsRefine` argument-ingress obligation.
- First PA1 case slice: `WASM-NORMALIZED-CASE-TABLE-ADMISSION` made normalized
  alternative order a production validator fact;
  `ConcreteStructuredCaseAltsNormalized.of_caseAltsNormalized` projects it.
- Second PA1 case slice introduced a temporary default/scalar/object source
  classifier to isolate the then-remaining object-tag premise. The final PA2
  slice deleted that classifier after exact i64 lowering made it redundant.
- Third PA1 case slice: `ObjectCaseDiscriminatorSupported` preserves the exact
  validated object-family kind and widens its related physical lane only at
  the concrete `getTag` boundary. Exact range lemmas prove that mapped heap
  tags fit `UInt32` and every related `tobject` tag fits `UInt64`; they also
  exposed the runtime's unsound low-`UInt32` truncation for promoted tags.
  W7 owns the exact i64 comparison repair, after which W6 removes the live-tag
  premise rather than preserving it as provenance.
- Final PA1/PA2 case slice: non-truncating i64 object-tag comparison landed.
  `productionCasesSupported_of_validation` derives all default, scalar, and
  object branches from residual validation and the successful source
  selection. `admit_cases_of_validated_step` exposes the zero-allocation PA2
  boundary, and `ConcreteStructuredSourceAdmissionSafeAt.cases` stores no
  semantic classifier.
- Lazy-cache validator slice: the production validator now exposes
  initializer-name uniqueness and singleton-result signature accessors.
  `lazyCacheValidatorSound` derives `LazyCacheValidationFacts` uniformly, and
  the supported-pipeline constructors no longer accept validator soundness as
  a premise.
- Lazy-cache result-lane slice: exact signature theorems cover both generated
  internal functions and generated external imports.
  `LazyCacheResultKindsAligned.ofSupportedPipeline` now derives the complete
  result-lane relation from source-name uniqueness and successful lowering;
  `LazyCacheGeneratedEnvironment.ofCanonicalSupportedPipeline` accepts no
  cache-specific client premise. The runtime lookup now selects hit/miss and
  residual validation derives the exact compatibility condition without a
  directional refinement assumption. `ConcreteResidualLocalAlignment` now
  derives arbitrary residual destination lanes from production's own
  effective-update traversal, with a compiler-root theorem and shared `let`
  projections. It still needs to be carried through the validated global
  relation. The audit also corrected an earlier overclassification:
  external/object-result misses are genuine backend-coverage boundaries, not
  merely hidden hit/miss exports.
- Focused proof cones for PA1/PA2:
  `FirTalos.ConcreteFinalLcnfTyping`,
  `FirTalos.ConcreteStructuredValidation`, and
  `FirTalos.ConcreteResumableWasm`; full exit gates remain `make check`,
  `make talos-check`, `git diff --check`, trust/source-hash gates, and
  `#print axioms` for the public PA3 endpoint.
