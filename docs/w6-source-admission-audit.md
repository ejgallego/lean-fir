# W6 source-admission audit

Status: **PA0 scaffold; classification has not started.**

This document is the review surface for eliminating caller-provided source
readiness from the public final-LCNF-to-Wasm theorem. It inventories every
current-step target branch before any new invariant or proof relation is
introduced. The next action is to review this surface, then fill every A–E
classification with exact dependencies.

The audit is complete only when no row contains an unclassified dependency,
an approximate theorem reference, or an unresolved owner/regression decision.

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

## Candidate PA2 theorem boundary

The branch audit targets a schema-aware theorem of approximately this shape;
PA0 will settle its exact home and arguments before implementation:

```lean
theorem currentStepAdmission_of_validated
    (related : ConcreteStructuredValidatedCodeOutcome ...)
    (schemaAgrees : schema.WitnessAgrees witness)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (finiteRuntimeSafe : ConcreteStructuredFiniteRuntimeSafeAt
      context sourceRuntime sourceEnv sourceCode) :
    ∃ requiredBytes,
      ConcreteStructuredSchemaCodeStepAdmission schema context sourceModule
        externals functionResult facts sourceRuntime sourceEnv requiredBytes
        sourceCode
```

The production wrapper then constructs the current-step classifier used by
the existing ranked finite-prefix package. It does not store successor
admission or a future execution.

## Complete current-step branch inventory

The “starting bridge” column records existing machinery, not an A–E decision.
The “facts to enumerate” and “class” columns deliberately remain open until
the review following this scaffold.

| # | Target branch | Source-safety constructor | Exact desired conclusion and cost | Starting bridge or theorem | Facts to enumerate in PA0 | Class | Proposed owner | Regression candidate |
|---:|---|---|---|---|---|---|---|---|
| 1 | return | `.ret` | `.ret`; cost `0`; compiled local, compatible result kind, and `SemanticValueAtAbi functionResult` | `ConcreteStructuredAlignedValidationState.admit_return`; `ConcreteStructuredSourceAdmissionSafeAt.ret_of_semanticBinding` | precise active-result provenance versus coarse local carrier | — | W6-Results | compiled `sumTo`; precise object/tagged negative fixture |
| 2 | direct let | `.directLet` | `.directLet`; cost `directLetAllocationCost decl`; `ReuseBudgetedDirectSupported` | `ConcreteStructuredValidatedCodeCoreRel.admit_of_source_safe_step` direct-let arm | residual validation fields for every direct-operation family | — | W6-Audit | existing direct-operation corpus |
| 3 | pure external | `.pureExternal` | `.pureExternal`; exact `stepCost`; `PureExternalSupported` | source-safety pure-external arm; installed pure Integer/Natural/scalar refinements | exact result kind/value and next-runtime facts available after one step | — | W6-Results | `sumTo` Nat externals; pure Int/String cases |
| 4 | direct call | `.directCall` | `.directCall`; cost `0`; `DirectInternalCallSite` | source-safety direct-call arm | declaration lookup, evaluated arguments, effective callee result kind, caller continuation result | — | W6-Results | `sumTo`; `direct-call` |
| 5 | saturated closure call | `.saturatedCall` | `.saturatedCall`; cost `0`; site, runtime resolution, and capture capacity | source-safety saturated-call arm; `ConcreteStructuredFiniteRuntimeSafeAt` | precise callee/caller result and capture provenance; separate D capacity | — + D review | W6-Results | `captured-partial`; mixed closure captures |
| 6 | lazy-cache hit | `.lazyHit` | `.lazyHit`; cost `0`; call shape, generated environment, exact cached value lookup | `.lazy` plus `ConcreteStructuredLazyReadyAdmission.hit` | cached value result precision and agreement with generated declaration | — | W6-Results | cached Natural/String/Array hit cases |
| 7 | lazy-cache miss | `.lazyMiss` | `.lazyMiss`; cost `0`; internal miss, result classification, object exclusions, empty lookup | `.lazy` plus `ConcreteStructuredLazyReadyAdmission.miss` | callee result provenance and identical publication type across miss/return | — | W6-Results | cached miss and first-publication cases |
| 8 | default-only case | `.defaultOnlyCase` | `.defaultOnlyCase`; cost `0`; selected default | `ConcreteStructuredValidatedCodeCoreRel.productionCasesSupported_of_caseSafe` | normalized alternatives and source-step selected-arm evidence | — | W6-Audit | default-only case corpus |
| 9 | object constructor cases | `.objectCases` | `.objectCases`; cost `0`; `ObjectConstructorCasesSupported` | `ConcreteStructuredValidatedCodeCoreRel.productionCasesSupported_of_caseSafe` object arm | discriminator object shape, tags, normalization, and selected alternative | — | W6-Objects | `branch-nat`; constructor cases |
| 10 | scalar UInt8 cases | `.scalarUInt8Cases` | `.scalarUInt8Cases`; cost `0`; `ScalarUInt8CasesSupported` | `ConcreteStructuredValidatedCodeCoreRel.productionCasesSupported_of_caseSafe` scalar arm | precise UInt8 discriminator rather than Wasm `i32` compatibility | — | W6-Results | `sumTo`; scalar-enum cases |
| 11 | persistent increment | `.incPersistent` | `.incPersistent`; cost `0` | `ConcreteStructuredAlignedValidationState.admit_incPersistent`; `ConcreteStructuredSourceAdmissionSafeAt.inc_of_any_persistence` | persistence-independent compiler facts | — | W6-Audit | persistent increment corpus |
| 12 | persistent decrement | `.decPersistent` | `.decPersistent`; cost `0` | `ConcreteStructuredAlignedValidationState.admit_decPersistent`; `ConcreteStructuredSourceAdmissionSafeAt.dec_of_any_persistence` | persistence-independent compiler facts and erased fields | — | W6-Audit | persistent decrement/reset corpus |
| 13 | ordinary increment | `.ordinaryIncrement`; source `.incOrdinary` | `.ordinaryIncrement`; cost `0`; exact semantic update | `ConcreteStructuredAlignedValidationState.admit_incOrdinary_of_step` | object lookup/kind from validation and step; separate D header headroom | — + D review | W6-Objects | ordinary increment boundary cases |
| 14 | ordinary decrement | `.ordinaryDecrement`; source `.decOrdinary` | `.ordinaryDecrement`; cost `0`; exact semantic release update | `ConcreteStructuredAlignedValidationState.admit_decOrdinary_of_step` | object lookup/kind and recursive-release shape | — | W6-Objects | decrement and recursive-release corpus |
| 15 | explicit delete | `.ordinaryDelete`; source `.del` | `.ordinaryDelete`; cost `0`; exact delete/no-op update | `ConcreteStructuredAlignedValidationState.admit_del_of_step`; `ConcreteStructuredSourceAdmissionSafeAt.del_unconditional` | erased-zero versus ordinary object decoding remains exact | — | W6-Objects | delete-erased and ordinary delete cases |
| 16 | constructor tag mutation | `.constructorTag`; source `.setTag` | `.constructorTag`; cost `0`; live object and exact semantic tag update | `ConcreteStructuredAlignedValidationState.admit_setTag_of_step`; `ConcreteStructuredSourceAdmissionSafeAt.setTag_unconditional` | live constructor, `UInt32` tag bound, active schema transition | — | W6-Objects | setTag bound and reuse-tag cases |
| 17 | object-field FVar mutation | schema `.objectFieldFVar` | schema object-field FVar branch; cost `0`; `schema.ObjectFieldFVarTyped` | `ConcreteStructuredValidatedCodeCoreRel.admitSchema_of_source_safe_step`; active schema/witness dispatcher | source local precision, object location/schema slot, active descriptor agreement | — | W6-Objects | multi-object and closure-field writes |
| 18 | object-field erased mutation | schema `.objectFieldErased` | schema erased-field branch; cost `0`; `schema.ObjectFieldKindAt ... .erased` | `ConcreteStructuredValidatedCodeCoreRel.admitSchema_of_source_safe_step`; active schema/witness dispatcher | erased slot provenance and active descriptor agreement | — | W6-Objects | erased-field reset/delete fixtures |
| 19 | `USize` field mutation | `.usizeField` | `.usizeField`; cost `0`; exact successful `USizeFieldEffectSupported` | `ConcreteStructuredAlignedValidationState.admit_uset_of_step`; `ConcreteStructuredSourceAdmissionSafeAt.usizeField_unconditional` | exact source `USize` lane and absolute slot bounds | — | W6-Objects | packed-project/update USize cases |
| 20 | packed scalar field mutation | `.scalarField` | `.scalarField`; cost `0`; exact successful `ScalarFieldEffectSupported` | `ConcreteStructuredAlignedValidationState.admit_sset_of_step` | precise scalar kind, slot/byte offset, and layout safety | — | W6-Objects | multi-scalar and packed-preserve cases |

## Cross-branch questions for the review

1. Should PA2 derive `ConcreteStructuredSchemaCodeStepAdmission` directly, or
   first derive `ConcreteStructuredSchemaSourceAdmissionSafeAt` and retain the
   current bridge as the sole assembly theorem?
2. Which result fact is genuinely common to return, direct call, closure call,
   external result, and lazy hit/miss without becoming a pervasive descriptor
   redesign?
3. Can direct-let result typing be factored once at the successful producer to
   environment-binding boundary, with operation families supplying only the
   producer lemma?
4. Does the existing schema/witness relation already close both object-field
   branches, leaving only exported interface lemmas, or is source producer
   provenance missing?
5. Which existing regressions assert semantic shape, and which rows need a
   negative compiler-acceptance fixture to prevent carrier-only reasoning?

## PA0 completion record

This section stays empty until the review above is resolved. The completed
record will include:

- the exact theorem dependency for all 20 rows;
- one A–E class plus any separate D premise for every row;
- the minimal PA1 helper-module split, if class-C rows exist;
- bug-card references for every class-E row;
- exact focused build cones and full gates; and
- the agreed target theorem name/signature for PA2.
