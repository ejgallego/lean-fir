# W6 observable contract and compiled trust audit

Review follow-up, 2026-09-09. Baseline: W6 `7affa1d2`, which includes the
conservative W7 recycler source at `e488c816`. The external review inspected
ancestor `a5449905`. The first checkpoint adds proof tests and audit tooling;
its successor adds the structured terminal-return bridge below. Neither
changes runtime behavior or a shared semantic relation.
The following terminal-extraction slice recovers the bridge inputs from the
unchanged validated global relation.
The precise-return successor retains the exact active-function result kind
at the two producer interfaces that previously hid it existentially.
The terminal-simulation successor then removes the separately supplied target
prefix by composing the existing classifier's ranked simulation.

## Destination and current evidence

The intended compiler guarantee includes finite external-event prefixes,
returned values, and semantic faults. A terminating source execution must
produce a corresponding target result under the explicit entry, runtime, and
resource contracts. No theorem needs to establish that every source program
terminates. Linking, encoding, and the application/session adapter remain
separate composition obligations before a claim about deployed bytes.

`ConcreteFiniteTraceCorrect` currently exposes only world and external-event
trace agreement. `finiteTraceCorrect_of_terminal_prefix` now formally exhibits
its limit: a terminal source and a stopped target satisfy the package whenever
their prefix observations agree. No target terminal result is constrained.
This is a test of the public interface, not a counterexample to the actual
compiler simulation relation.

The existing `RefinedReturnPost` and `RefinedFaultPost` are stronger. New
reusable lemmas in `ConcreteObservationSensitivity.lean` establish:

- `ConcreteExportTerminatesWith.postconditions_overlap`: two successful
  specifications of one invocation hold of one common `Wasm.run` result.
- `ConcreteExportTerminatesWith.uint64_result_unique`: those specifications
  cannot describe different returned UInt64 values, even with different
  existential heap witnesses or final source runtimes.
- `ConcreteExportTerminatesWith.not_trapsWith`: the same invocation cannot
  satisfy both success and trap specifications.
- `ObservationSensitivity.prettyObservation_injective`: observing the actual
  generated facade's text and reversed `eventsRev` retains all result
  information. Equal text with different styling is distinguished.

The first three lemmas use deterministic executable Talos semantics at a common
sufficient fuel. They require no extra determinism assumption. The pretty
lemma exercises the real facade type but does not prove its Wasm decoder or
its compilation. Resource exhaustion still has no general matching-failure
theorem; current resource preconditions remain explicit. This slice does not
change the schema, source/target relation, compiler admission, or runtime ABI.

## Structured return bridge

`ConcreteTerminalCorrectness.lean` now connects the already represented result
to actual Talos execution. Its main assembly helper is
`ConcreteSupportedExport.terminatesWith_of_structuredYield`:

```text
supported export + exact entry-argument count
  + finite structured prefix from that export's entry
  + existing yielded-value relation and checked frame stack
  + no remaining source continuation
  => executable export termination with RefinedReturnPost
```

This is an internal assembly lemma, not the closed compiler theorem. The
ranked simulation must produce the target prefix; clients must not be asked
to prove it. No new simulation, invariant, or certificate is introduced.

The reusable proof derives rather than assumes:

- terminal target label unwinding from
  `ConcreteStructuredSupportedFrameStack.returning_halts`;
- full heap/world/trace/value refinement and a clear failure channel from
  `ConcreteStructuredYieldFocus.refinedReturnPost`;
- a finite path to the exact halted store and stack from
  `ConcreteStructuredYieldFocus.finitePath_halted`;
- loop-arity safety from successful adaptation, using the existing
  `StructuredWasmStep.finitePath_run_of_adapt`;
- one sufficient fuel bound, singleton result selection, and caller-tail
  restoration. The function form supports an arbitrary caller operand tail;
  the export form specializes it to empty.

The yielding function's context is deliberately independent of the entry
function's context. Execution adequacy needs the actual target prefix, not an
extra equality between these compiler identities.

## Terminal extraction from the global relation

`ConcreteTerminalExtraction.lean` removes the separately supplied yielded-value
relation and checked-frame arguments from the assembly boundary:

```text
supported export + exact entry-argument count + finite target prefix
  + existing validated global relation
  + successful final source step returning v
  => there exists a represented kind k such that executable Wasm returns v
     with RefinedReturnPost at k
```

`sourceCoreReturned_terminal` and `sourceExecReturned_terminal` show that a
successful final observation can arise only from a yielded value with no
remaining source continuation. An external response resumes execution rather
than creating a successful terminal observation. The source observation is
also identified exactly, including its heap, world and external-event trace.

`ConcreteStructuredValidatedCodeGlobalOutcome.terminalYield_of_control`
recovers the existing yielded-value relation and supported frame stack. A
staged external result cannot be mistaken for a terminal return: it still has
its bind frame. All other non-return branches have different source control.
The function and export `terminatesWith_of_validatedReturn` corollaries then
apply the reviewed executable return bridge, including arbitrary caller-tail
restoration for the function form.

The result kind remains existential. This slice does **not** establish that
it equals the root export's selected ABI, and does not weaken that remaining
goal. The finite target prefix is still an internal simulation assembly input,
not a new application-client certificate. No admission predicate, simulation
relation, runtime behavior, or trusted axiom was added or changed.

## Precise return producers

The return rule already proves the exact active-function result ABI. The new
`ConcreteStructuredCodePointwiseRel.advance_return_precise` exposes that fact
instead of existentially hiding the result kind. It uses the same current-node
admission and successful source step as `advance_return`; the old theorem is
now a compatibility wrapper around the precise one.

`ConcreteStructuredValidatedCodeOutcome.advance_returnPrecise_of_step`
transports the same precision through suspended-frame validation. Its returned
outcome has both its `functionResult` and its represented `kind` indexed by the
same active-function result. It also exposes the unchanged source/target frame
equalities. The existing `advance_returnAt_of_step` keeps its public signature
by packaging this stronger local outcome into the witness-indexed global
relation.

This is a hidden-interface repair, not a new provenance assumption: no premise
was added, and the existing source-semantic return admission is still required.
In particular, physical lane compatibility alone is not treated as semantic
result refinement. The new producer lemmas do not change the global relation,
which can still hide the precise kind, or establish that the active function
is the root export. Retaining those facts across the whole simulation remains
the next obligation.

## Source termination through the compiler simulation

`ConcreteTerminalSimulation.lean` closes the target-prefix assembly boundary:

```text
supported export + universal current-step classifier
  + ordinary concrete entry contracts + correct argument count
  + successful source evaluation returning v
  => executable Wasm export termination with RefinedReturnPost for v
     at some represented kind k
```

`ConcreteSupportedFunction.terminatesWith_of_classifiedExecSteps` obtains the
target prefix and terminal related state from the existing
`ConcreteRankedTraceSimulation.execSteps`, then applies terminal extraction.
It preserves arbitrary caller operand tails. The export-facing
`terminatesWith_of_classifiedExecEvaluates` constructs the initial relation
from production validation and the concrete entry frame; its caller supplies
neither a simulation relation nor a target path. It also identifies the source
observation exactly as `ReturnedObservation resultRuntime value`, retaining
heap, world, and external trace alongside the represented value.
`terminatesWith_of_classifiedRun` accepts an ordinary successful executable
interpreter run via the existing `run_done_sound` theorem. Target execution
and a sufficient target fuel bound are derived, not assumed.

These are conditional result theorems, not the closed PA3 endpoint. The
universal `ConcreteStructuredCurrentStepClassifier` remains a compiler-proof
obligation. Its general derivation still depends on unfinished admission work
and explicit runtime/resource safety. No caller-chosen source invariant or
per-program execution certificate is added, and source evaluation is simply
the antecedent of partial correctness, not a termination claim for all inputs.
The result kind is still existential; the theorem does not yet justify
decoding at the root export's selected ABI. Global root-kind provenance and
trap semantics remain separate. No existing relation is redesigned.

### Root-result boundary from the existing caller spine

`ConcreteRootResult.lean` reuses the non-proof caller ABI spine already indexed
by `ConcreteStructuredValidatedStackAgreement`. Its oldest caller identifies
the root result kind; with no callers, the active function is the root.
`concreteStructuredRootResultKind_push` is the same push/pop equation for direct,
saturated closure, and lazy initializer calls, including calls whose callee
result kind differs from the caller's. Target-only case labels and ordinary
frame reindexing retain the index without introducing runtime state.

The internal relation `ConcreteStructuredValidationAgreesAtRoot` retains this
one root index while existentially hiding the existing checked spine. It is
not an application-supplied invariant. In particular,
`ConcreteSupportedExport.validatedCodeRoot_rootResult` constructs it from the
actual supported export entry with precisely the existing runtime premises.
`ConcreteStructuredValidationAgreesAtRoot.functionResult_eq_of_empty` recovers
the exact selected root ABI at a source terminal continuation, even if target
case labels remain. `ConcreteStructuredValidatedReturnedOutcome.yieldAtRoot_of_empty`
connects that fact to the preceding slice's precise local return evidence.

This checkpoint establishes the entry and terminal boundaries, not global
preservation. The call equation alone is not a dispatcher preservation theorem.
The successor must retain this index and exact producer kind through every
global branch and its push/pop transitions, then use the strengthened relation
in the existing finite-prefix and terminal assembly. The public classified
terminal theorem still has an existential result kind until that wiring is
proved; the rooted-stack premise must not be exported to clients instead.
The heterogeneous-call regression distinguishes a `UInt64` root from its
`UInt8` nested helper. All ten new lemmas are in the exact compiled trust
inventory: two are axiom-free, and eight use only the standard three axioms.

### Root-preserving return transition

`ConcreteStructuredValidatedCodeOutcome.advance_returnPreciseAtRoot_of_step`
retains the compiler-owned root index through one successful source return.
It composes `advance_returnPrecise_of_step` with
`ConcreteStructuredValidationAgreesAtRoot.reindex`, reusing the exact two-step
target path, the current witness, and the unchanged source/target frame
equations. The returned outcome still represents its value at `functionResult`,
not a fresh existential kind. A dependent existential names that precise
returned proof so its root agreement remains available to the consumer.

`advance_returnYieldAtRoot_of_step` exercises the producer at an empty source
continuation and derives the yield at exactly `rootResult`. Neither theorem
asks for a final-client equality between root and active result kinds. The
regression is sensitive to losing either the represented-kind precision or the
root index. The negative same-lane regression also distinguishes an `.object`
root from `.tobject`; an i32 carrier alone cannot identify these semantic kinds.
Both new theorems have exactly the three standard axioms and no generated
native-evaluation dependency in the compiled inventory.

This closes the local return transition, not the global preservation theorem.
The rooted premise is internal proof metadata established by the actual export
entry; it must next be retained through ordinary code and caller push/pop and
administrative transitions. Current-node return admission, the universal
classifier, and the public existential result-kind boundary remain unchanged.
No shared relation, runtime semantics, W7 source or client contract is changed.

### Root-preserving ordinary direct-let transition

`ConcreteStructuredValidatedCodeOutcome.advance_directLetWithFrames_of_step`
exposes the source/target frame equations already proved by the existing
direct-let rule. The original `advance_directLet_of_step` remains a wrapper
with its unchanged signature, so existing dispatchers need no adaptation.

`advance_directLetAtRoot_of_step` uses those equations and the existing
`ConcreteStructuredValidationAgreesAtRoot.reindex` lemma to retain the same
root index on the named successor relation. It preserves the exact active and
caller result indices, next witness and locals, positive target path, and
`remainingBytes - directLetAllocationCost decl` budget. The source `let` binds
its result and continues with the original continuation. An empty-stack
regression derives `functionResult = rootResult` from this successor; that
equality is not an added premise.

This is local transport over the existing `ReuseBudgetedDirectSupported`,
allocation-headroom and successful-source-step premises, not a new admission
theorem or a client-supplied invariant. Other local families, calls, caller
push/pop, administrative transitions and global assembly remain open.

All three direct-let endpoints have the same exact dependency set as the
original validated direct-let proof: three standard axioms and 54 existing
generated native-evaluation axioms. `TrustInventory.directLetNativeDebt`
records their individual names and audits the compatibility wrapper as well
as the two new endpoints. This slice adds no axiom and does not discharge the
existing native-evaluation debt.

### Root-preserving zero-step default-only case

`ConcreteStructuredValidatedCodeOutcome.advance_defaultOnlyCaseWithFrames_of_step`
retains the source-frame equation already derived by the original default-only
case rule. Its old `advance_defaultOnlyCase_of_step` API remains an unchanged
compatibility projection.

`advance_defaultOnlyCaseAtRoot_of_step` reindexes the compiler-owned root
agreement onto the named validated successor. The target state stays exactly
the same, with a `FinitePath` of length zero; the source control rank strictly
decreases. This is the existing progress argument for compiler-erased control,
not a termination assumption. Runtime, witness, locals, environment, budget
and active/caller result indices remain unchanged. Only the source code
advances to the selected default branch.

The kernel regression obtains exact active/root result equality from the
successor at an empty source continuation, together with the zero-step path
and strict rank result. Existing `DefaultOnlyCaseSupported` and successful
source-step premises remain; no global relation, admission or client contract
changes. The original rule's measured axiom set and all three resulting
endpoints are exactly `propext`, `Classical.choice` and `Quot.sound`.
No generated dependency or new axiom is introduced.

The tested-case successor below extends this boundary; other local families,
caller push/pop and global root-preserving assembly remain open.

### Root-preserving tested object and UInt8 cases

`advance_objectCasesWithFrames_of_step` and
`advance_scalarUInt8CasesWithFrames_of_step` expose the source branch selection,
unchanged source frames, and the precise target-only case-label suffix already
proved by their original producers. The old signatures remain compatibility
projections. The two `AtRoot_of_step` counterparts in `ConcreteRootResult`
apply the established rooted `case` and `reindex` facts to a named successor.
There is no new common relation or generic transport framework.

The exact path lengths remain `5 * testCount` for objects and `4 * testCount`
for UInt8. Both retain `List.replicate testCount none ++ labels`, the same
runtime/witness/budget and active/caller result kinds, and the strict rank
decrease conditional on a zero path count. Source caller frames do not grow;
target case labels do. Their correspondence is not frame-list equality.

Each kernel regression uses its actual rooted producer at an empty source
continuation. It recovers exact active/root equality from the successor;
zero tests imply an unchanged target and strict source-rank decrease; nonempty
tests give exactly the inner labels followed by the outer suffix-saving label.
These are conditional shapes of the produced path, not new assumptions that
force a particular number of tests or enumerate program executions.

The original object rule and its new endpoints use the three standard axioms.
The original UInt8 rule and its new endpoints additionally use exactly the two
named dependencies in `TrustInventory.scalarCaseNativeDebt`. Those existing
local-value/tag-comparison native axioms are recorded, not newly approved or
discharged. All six endpoints are audited. No admission/client/runtime/W7
contract changed. Global assembly, other local families and caller transitions
remain open; W7 source-equation work remains independent.

### Root-preserving validation-derived case dispatcher

`ConcreteStructuredValidatedCodeOutcome.advance_casesAtRoot_of_validated_step`
composes the three accepted case families. The successful source step gives
the dynamic branch; `productionCasesSupported_of_validation` derives the
default-only/object/UInt8 admission from existing production validation.
No caller-supplied classifier, selected branch, target path or result-kind
equality is introduced. Root agreement remains compiler-internal metadata.

The uniform existential target-step presentation matches the existing
`advance_cases_of_validated_step`; the specialized rules keep their exact
zero/5*n/4*n costs. A named validated successor retains the original root,
active/caller result indices, runtime, witness and budget at its successor
label context. The theorem also exposes the selected `SourceCaseResult`,
unchanged source frames and strict rank decrease when the target path is empty.
Its kernel regression recovers exact active/root precision from this produced
successor with no source caller, plus an unchanged target and strict source
progress for zero target steps. It supplies no extra case-admission premise.

The original dispatcher file/API is unchanged. Its measured axiom set and
that of the rooted composition agree exactly: the three standard axioms and
the two existing names in `scalarCaseNativeDebt`. Both endpoints are included
in the exact inventory. No new axiom or trust approval. This closes one
validation-derived local dispatcher, not global root preservation, caller
push/pop, other local families, universal compiler admission or public
result-kind closure. Later closure-footprint and W72 obligations stay separate.

### Root-preserving reference-count transitions

`advance_incPersistentAtRoot_of_step` and `advance_decPersistentAtRoot_of_step`
retain the root on named successors using the existing persistent producers
and `ConcreteStructuredValidationAgreesAtRoot.reindex`. They derive rather
than assume current-node admission, preserve source frames, leave the target,
runtime, witness and budget unchanged, take zero target steps and strictly
decrease source rank. Their original producer APIs/bodies are unchanged.

`advance_ordinaryIncrementWithFrames_of_step` and
`advance_ordinaryDecrementWithFrames_of_step` expose the source/target frame
equations already present in the pointwise/`advanceCode` composition. They use
the existing validated `withSuccessor` attachment; the old APIs remain exact
compatibility wrappers. No generic transport framework is added.
`advance_ordinaryIncrementAtRoot_of_step` and
`advance_ordinaryDecrementAtRoot_of_step` then reindex the same root onto those
named successors. They keep `OrdinaryIncrementEffectSupported` and
`OrdinaryDecrementEffectSupported`, their exact two-step target path,
runtime/store evolution, witness and budget. This adds no refcount, release,
allocation or ownership refinement and weakens no resource bound.

Four kernel regressions invoke the actual rooted producers and recover exact
active/root equality from the produced successor when the source caller stack
is empty. The persistent regressions retain derived admission, zero steps and
strict source progress; the ordinary regressions retain two steps and both
frame equations. Neither assumes the result-kind equality being established.

Original/helper/rooted axiom sets agree exactly, measured before transport at
`2baabade`. Persistent endpoints use the three standard axioms. Ordinary
endpoints additionally use the one existing byte-assembly dependency named in
`TrustInventory.referenceCountNativeDebt`. All ten endpoints are included in
the initial 70-endpoint inventory; there is no new axiom or trust approval.

### Validation-derived rooted ownership transitions

`advance_ordinaryIncrementAtRoot_of_validated_step`,
`advance_ordinaryDecrementAtRoot_of_validated_step` and
`advance_ordinaryDeleteAtRoot_of_validated_step` now mirror the existing
validation-derived rules while naming successors that retain the original
root. Compiler local/refinement facts come from retained production validation;
the semantic effect comes from the successful source step. The increment and
decrement rules reuse their accepted rooted effect producers. Explicit delete
adds only `advance_ordinaryDeleteWithFrames_of_step` and
`advance_ordinaryDeleteAtRoot_of_step` over the existing pointwise proof,
preserving the old delete API and effect contract.

The only extra increment premise is exactly the existing condition that any
looked-up heap cell satisfies `cell.rc + amount < UInt32.size`. This is finite
target headroom, not a consequence of successful unbounded source execution.
Decrement and delete need no caller effect, admission or nonzero premise;
erased physical-zero deletion remains inside the existing delete rule.

All three rules preserve exact two-step target paths, named next runtime/store/
code, source environment, active/caller result indices, witness and budget.
They expose both frame equations and retain root evidence on the same named
successor. Three kernel regressions invoke these actual validation-derived
producers without caller-supplied effect facts and recover active/root equality
from their successors at an empty source caller stack.

Original/helper/rooted axiom sets agree with those measured at `97b25f06`:
the three standard axioms plus the single existing byte-assembly dependency in
`referenceCountNativeDebt`. Nine added entries bring the exact inventory to 79;
no new axiom or trust approval. This closes one bounded local composition, not
a new refcount/release/ownership proof. Other mutations, caller push/pop,
global root assembly, public result-kind/admission closure, trap semantics and
closure-footprint/tagged-result/W72 work remain separate.

### Root-preserving constructor-tag mutation

`advance_constructorTagWithFrames_of_step` exposes frame equations from the
existing pointwise mutation proof and attaches retained validation with the
unchanged `withSuccessor`. The old `advance_constructorTag_of_step` signature
is preserved as a compatibility wrapper. `advance_constructorTagAtRoot_of_step`
uses the established `reindex` lemma on that actual named successor.

`advance_constructorTagAtRoot_of_validated_step` reconstructs tag-width/local
facts via `setTag_compiler`, and heap-shape/effect facts via
`setTag_source_of_step`. It calls the rooted effect producer, adding no caller
effect, admission, width or heap-shape premise. Its old validation-derived
counterpart remains unchanged, including its proof body.

Both rooted producers retain exact two-step target paths, next runtime/store/
code, source environment, active/caller result indices, witness and budget,
plus both frame equations. A kernel regression invokes the actual validated
rooted producer without supplied effect facts, recovering active/root precision
from its successor when the source caller stack is empty.

All five original/helper/rooted tag endpoints have the same measured axiom set
as baseline `23bccf86`: the three standard axioms and the existing byte-assembly
dependency in `referenceCountNativeDebt`. Five added entries bring the exact
inventory to 84; no new axiom or trust approval. This is root transport over
the existing `ConstructorTagEffectSupported` contract, not a changed layout
or mutation semantics. Field mutation, other families, caller push/pop, global
assembly, public result-kind/admission closure and trap semantics stay open;
closure-footprint, whole-helper/tagged-result and W72 work remain separate.

### Root-preserving USize and packed-scalar field mutation

`advance_usizeFieldWithFrames_of_step` and
`advance_scalarFieldWithFrames_of_step` expose frame equations already proved
by the existing pointwise mutations, attaching validation with unchanged
`withSuccessor`. Their old effect-rule signatures remain exact compatibility
wrappers. The corresponding `AtRoot_of_step` rules reindex the same root on
the actual named successors; no generic framework is introduced.

`advance_usizeFieldAtRoot_of_validated_step` reconstructs compiled operands
and dynamic slot/heap facts through `uset_compiler` and `uset_source_of_step`.
It needs no additional source-layout, caller effect or admission premise.
`advance_scalarFieldAtRoot_of_validated_step` derives compiler/dynamic facts
through `sset_compiler` and `sset_source_of_step`, but retains EXACTLY:

```lean
fieldTyped : ConcreteScalarFieldMutationTyped context sourceRuntime sourceEnv
  objectId fieldId slotIndex byteOffset
```

This source descriptor-layout invariant is neither strengthened nor weakened,
and is not claimed to follow from validation or successful source execution.
Neither rooted rule adds a width, descriptor, effect or admission premise.
Both original validated declarations and proof bodies remain unchanged.

All rooted successors retain exact three-step target paths, next runtime/
store/code, source environment, active/caller result indices, witness, budget
and both frame equations. Two kernel regressions invoke the actual validated
rooted producers with only their existing premises, recovering active/root
precision from their successors at an empty source caller stack.

All ten original/helper/rooted axiom sets equal baseline `c42bc5d2`. USize
retains three standard axioms plus the existing byte32-assembly dependency;
packed-scalar retains the standard three plus the existing byte16/byte32 pair,
individually named in `packedScalarFieldNativeDebt`. The exact inventory now
has 94 endpoints, with no new axiom or trust approval. This is root transport,
not new mutation/layout refinement. Object-reference/erased fields, schema
bridges, other families, caller push/pop, global assembly, public result-kind/
admission closure and trap semantics remain separate. Closure-footprint,
whole-helper/tagged-result and W72 obligations are unchanged.

### Root-preserving active-witness object-field mutations

`advance_objectFieldFVarAtWithFrames_of_step` and
`advance_objectFieldErasedAtWithFrames_of_step` expose the frame equations
already proved by the active-witness core effects, attaching retained
validation with unchanged `withSuccessor`. They do not pass through the older
arbitrary-witness admission wrappers. Both old At effect signatures remain
exact compatibility wrappers. Their `AtRoot_of_step` successors retain the
same root with the existing `reindex` lemma.

`advance_objectFieldFVarAtRoot_of_schema_step` and
`advance_objectFieldErasedAtRoot_of_schema_step` reconstruct compiler and
dynamic source facts just as the original schema producers do. They use the
unchanged `ConcreteObjectFieldKindAlignedAt.of_schema` bridge at the current
witness. Their premise boundary remains exactly:

```lean
schemaAgrees : schema.WitnessAgrees witness
-- FVar producer:
fieldTyped : schema.ObjectFieldFVarTyped context sourceEnv objectId fieldId index
-- Erased producer:
fieldTyped : schema.ObjectFieldKindAt sourceEnv objectId index .erased
```

Source typing and schema agreement are not claimed to follow from validation
or successful source execution. No arbitrary-witness, caller effect or
admission premise is added. The original schema declarations and proof bodies,
older arbitrary-witness wrappers, and schema bridge are unchanged. The effect
rules retain `ObjectFieldFVarEffectSupportedAt` and
`ObjectFieldErasedEffectSupportedAt`; erased writes preserve their existing
physical-zero behavior.

Each rooted rule names its actual successor, retaining the exact three-step
target path, next runtime/store/code, source environment, active/caller result
indices, witness, budget and both frame equations. Two kernel regressions
invoke the actual rooted schema producers with only the original schema
premises and recover root precision from the successors at an empty source
caller stack. Neither supplies effect facts nor assumes result-kind equality.

All ten original/helper/rooted axiom sets equal those measured at `e5ea3914`:
the standard three plus the existing byte32-assembly dependency recorded in
`referenceCountNativeDebt`. The exact inventory expands to 104 endpoints,
with no new axiom or trust approval. This is root transport, not new field
ownership/layout refinement. Arbitrary-witness wrappers, global schema
dispatch, other local families, caller push/pop, global root/precision
assembly, universal compiler admission and traps remain separate. Closure
footprint, whole-helper/tagged-result and all 14 W72 obligations are unchanged.

### Root-preserving named direct-call staging

`ConcreteStructuredValidatedCodeOutcome.advance_directCall_stageAtRoot_of_step`
calls the original `advance_directCall_stage_of_step` unchanged, then applies
the existing `ConcreteStructuredValidationAgreesAtRoot.reindex` to that exact
named `ConcreteStructuredValidatedDirectCallReadyOutcome`. Its `agrees` and
`frames.validation` retain the original caller/root ABI. The ready outcome
already exposes the saved caller frame indices, so no additional frame helper
or central staging edit is needed.

The old `activeResult` and `DirectInternalCallSite` premises are unchanged.
The rule retains the selected generated row and callee context/function,
physical arguments, result index, target argument prefix/rest, exact
`targetArguments.length` path and strict source control-rank decrease. Its
ready payload still holds caller continuation validation, saved source/target
frames, active/caller result indices, runtime/store, witness and resource
budget. No callee entry or caller push occurs here; there is no equality
between caller and callee result kinds, or a new client/classifier premise.

A kernel regression invokes the actual rooted producer and derives caller/
root precision from its saved empty caller stack. It retains the exact path
and unconditional rank decrease, including when an empty argument prefix
implies an unchanged target. No result-kind equality is assumed.

Baseline `07b34775` and both original/rooted endpoints have exactly the three
standard axioms; the exact inventory expands to 106 endpoints. No new axiom,
generated dependency or trust approval. The original staging declaration and
body, ready relation and shared semantic/admission definitions are untouched.
This is one local staging boundary, not callee entry, caller push/pop, other
staging families or global root assembly. Footprint, whole-helper/tagged-result
and all 14 W72 obligations remain separate.

### Root-preserving saturated and lazy staging

`advance_saturatedCall_stageAtRoot_of_step` and
`advance_lazy_stageAtRoot_of_step` reuse the unchanged staging producers and
the existing `reindex` lemma directly. The original caller/root ABI is attached
to each actual named ready outcome's `agrees` and `frames.validation`, before
any callee entry, caller push or closure consumption. No extra helper or
central staging/ready-relation edit is needed.

Both producers keep exact zero-step target identity and unconditional strict
source control-rank decrease. Their ready payloads retain caller continuation
validation, saved source/target frames, active/caller result indices, runtime/
store, witness and budget. Saturated staging also retains the selected row/
callee, targetValue/rest and result index; lazy staging retains cacheIndex,
declarationId, cacheSetId, resultIndex and rest. Caller and callee result kinds
are not equated.

The original `activeResult`, saturated site/resolution and `sharedCapacity`
premises are unchanged. In particular, capacity remains required for every
`parentRuntime` obtained by successful `setCell` after decrementing
`resolution.cell.rc`, and is `ClosureRetainCapacity parentRuntime
resolution.captures.toList`. Finite retain capacity is not derived from source
execution. Lazy staging keeps `LazyCacheCallSupported`,
`LazyCacheGeneratedEnvironment` and the exact `ConcreteStructuredLazyReadyAdmission`
path. Hits retain semantic lookup; misses retain the internal initializer,
classified result, non-object/non-tobject restrictions and empty lookup. Root
transport neither derives admission nor broadens supported result kinds.

Two kernel regressions invoke the actual rooted producers and recover caller/
root precision from their saved empty caller stacks while keeping zero target
steps and strict source progress. The lazy regression accepts an arbitrary
existing admission path, covering both hit and miss without a hit-only premise.
No result-kind equality or new client/classifier premise is supplied.

Both originals at baseline `7529041f` and all four final original/rooted
endpoints have exactly the three standard axioms. The inventory now checks 110
endpoints; no generated dependency, new axiom or trust approval. The entire
original staging file is unchanged. Saturated entry/closure consumption, lazy
hit execution or miss entry/cache write, caller push/pop, external staging,
global root/schema assembly, universal compiler admission and traps remain
separate. Footprint, whole-helper/tagged-result and all 14 W72 obligations are
unchanged.

### Root-preserving pure-external staging

`ConcreteStructuredValidatedCodeOutcome.advance_pureExternal_stageAtRoot`
reuses the unchanged `advance_pureExternal_stage` and existing `reindex`
lemma on its saved caller indices. The original caller/root ABI is attached
to the actual named `ConcreteStructuredValidatedExternalCallReadyOutcome`'s
`agrees` and `frames.validation`. No helper or central staging/ready-relation
edit is needed.

Its premises remain exactly `activeResult`, `PureExternalSupported context
externals sourceRuntime sourceEnv decl continuation nextRuntime sourceValue
stepCost`, `budget : stepCost ≤ remainingBytes` and a successful source step,
alongside compiler-internal root evidence. Supported-call and finite allocation
headroom are not inferred from execution. No classifier, import-closure, ABI
equality or final-client premise is introduced.

The producer retains the selected `PureExternalCallShape`, physical arguments,
`ExternalOperation`, `resolvedResultKind`, `targetImport`, call/result indices,
argument prefix/rest and exact `targetArguments.length` path. Strict source
rank decreases unconditionally, including an empty prefix. Its ready payload
retains caller continuation validation, saved frames, active/caller result
indices, witness, budget and the exact runtime/store indices. The caller/root
ABI is not equated with the host operation's resolved result ABI.

A kernel regression invokes the actual rooted producer and derives caller/
root precision from the saved empty caller stack while retaining path/rank.
Its empty-prefix clause derives target identity; no result-kind equality is
supplied. Baseline `fd3fc701` and both original/rooted endpoints use exactly
the three standard axioms. The inventory expands to 112 endpoints, with no
generated dependency, new axiom or trust approval. The entire original staging
file and shared semantic/admission/runtime definitions remain unchanged.
Host-call execution, destination bind, callee entry, caller push/pop, lazy
cache writes, global root/schema assembly, universal compiler admission and
traps remain separate, as do footprint/whole-helper/tagged-result and all 14
W72 obligations.

### Root-preserving resolved host step

`ConcreteStructuredValidatedExternalCallReadyOutcome.advance_bind_of_step`
exposes the named `ConcreteStructuredValidatedExternalBindOutcome` already
constructed by the original host-step producer. `advance_of_step` keeps its
original signature as a compatibility wrapper. The ready/bind relations and
core host proof are unchanged.

`advance_bindAtRoot_of_step` attaches root evidence to that actual named bind's
`agrees` and `frames.validation`, using the existing saved-caller `reindex`
lemma. Its only premises are the original ready evidence and successful source
step, plus compiler-internal root evidence. It adds no host-correctness,
headroom, result-classification, final-client or caller/host ABI-equality premise.
This is transport over the existing host contract, not a new host refinement.

Both producers retain exactly one target step, `witness.Extends nextWitness`,
the same core-chosen `nextStore`, `nextWitness` and `physicalResult`,
`nextRuntime`, `sourceValue`, `remainingBytes - stepCost`, `site.resultKind`,
`resultIndex` and `decl.fvarId`. Caller environment/continuation/joins, saved
source/target frames, caller remainder/rest, active/caller result indices and
the exact resource payload persist. The root/caller ABI is not equated with
`site.resultKind` or `resolvedResultKind`.

The kernel regression calls the actual rooted producer, then recovers caller/
root precision from the produced bind's saved empty caller stack while retaining
its one-step path and witness extension. Baseline original at `a56c88ef`, final
compatibility wrapper, helper and rooted producer have the same exact four-axiom
set: the three standard axioms and the already-inventoried byte32 assembly
dependency. The inventory now covers 115 endpoints; this records inherited
debt, not new trust approval. No axiom or shared semantic/admission/runtime
definition is added or changed.

Destination binding, callee entry, caller push/pop, lazy execution/cache writes,
global root/schema assembly, universal compiler admission and traps remain
separate. Footprint/whole-helper/tagged-result and all 14 W72 obligations are
unchanged.

### Root-preserving external destination bind

`ConcreteStructuredValidatedExternalBindOutcome.advance_code_of_step` exposes
the original producer's named `ConcreteStructuredValidatedCodeOutcome`
(`nextActive`) and the actual `sourceAfter.frames = sourceFrames` and
`targetAfter.frames = targetFrames` equations. `advance_of_step` retains its
original signature as a compatibility wrapper. The core bind proof, complete
active-state construction and bind/code relations remain unchanged.

`advance_codeAtRoot_of_step` uses those exact frame equations with the existing
root `reindex` lemma, attaching evidence to the produced `nextActive.agrees`
and `nextActive.frames.validation`. The only premises are existing bind evidence
and a successful source step, plus compiler-internal root evidence. No semantic
typing, admission, capacity, host or final-client premise is added; the bound
value's `kind` is not equated with the caller/root result kind.

The step retains exactly one target `local.set`, core-chosen `resumedLocals`,
`bind callerEnv result sourceValue`, `continuation`/`targetRest` and
`eraseReuseCapacityFact facts result` (only the destination fact is erased).
`remainingBytes`, `sourceRuntime`, `targetStore`, `witness`, entry state,
active/caller result indices, caller remainder and joins remain as in the
original rule. There is no additional budget subtraction or witness extension.
This is transport over the existing bind semantics, not a new bind rule.

The actual-producer kernel regression derives caller/root precision from the
produced active successor and an empty saved caller stack, retaining the exact
one-step path and both frame equations. Baseline original at `552784cb` and
all three final original/helper/rooted endpoints have exactly `propext`,
`Classical.choice` and `Quot.sound`. The inventory expands to 118 endpoints;
no generated dependency, new axiom or trust approval is introduced. Existing
native-evaluation debt elsewhere remains open.

Callee entry, caller push/pop, lazy execution/cache writes, global root/schema
assembly, universal compiler admission and traps remain separate, as do
footprint/whole-helper/tagged-result and all 14 W72 obligations.

### Root-preserving lazy-cache hit and bind composition

`ConcreteStructuredValidatedLazyCallReadyOutcome.advance_hitAtRoot_of_step`
reuses `advance_hit_of_step` unchanged and attaches the root to the actual
named external-bind outcome's `agrees` and `frames.validation` through the
existing saved-caller `reindex`. No helper or ready/bind relation edit is needed.
The complete central producer file and accepted rooted destination-bind proof
remain unchanged.

Its only premises are existing ready evidence, explicit
`semanticFound : findGlobal? sourceRuntime.globals declaration = some sourceValue`
and a successful source step, plus compiler-internal root evidence. Semantic
lookup is not inferred; no value typing, ABI equality, capacity, admission or
final-client premise is added. The cached value's `resultKind` remains distinct
from the caller/root ABI.

The producer retains exactly four target steps, the original core-chosen
physical value and target successor, `sourceValue`/`decl.fvarId`, result kind/
index, caller locals/values/rest, continuation/joins, saved frames and all
active/caller result indices. Budget, runtime/store/witness and reuse facts are
unchanged at hit-to-bind. No cache write or initializer entry occurs on this hit.

One kernel regression invokes the actual rooted hit and recovers root precision
at an empty saved caller stack while retaining the four-step path. A second
invokes that hit followed by the accepted
`ConcreteStructuredValidatedExternalBindOutcome.advance_codeAtRoot_of_step`
for a second successful source step. `FinitePath.trans` composes exactly
`4 + 1 = 5` steps; the result retains the named active successor, its checked
root, recovered root precision, both frame equations, bound environment and
`eraseReuseCapacityFact facts decl.fvarId`. The existing bind proof is reused
unchanged; this is a focused composition test, not global simulation assembly.

Baseline original at `c5f80579` and both final original/rooted hit endpoints
have exactly `propext`, `Classical.choice` and `Quot.sound`. The inventory
expands to 120 endpoints with no generated dependency, new axiom or trust
approval. Existing native-evaluation debt elsewhere remains open. Lazy misses,
initializer entry/cache publication, callee entry/push/pop, global root/schema
assembly, compiler admission and traps remain separate, as do footprint/
whole-helper/tagged-result and all 14 W72 obligations.

### Original-root preservation through named direct entry

`ConcreteStructuredValidatedDirectCallReadyOutcome.advance_enterWithSpine_of_step`
exposes the actual named callee outcome and its checked pushed spine. Its spine
argument is already-checked internal metadata: the compatibility wrapper gets
it from `related.validationAgrees`, while the rooted producer gets the same
spine and alignment from the caller's internal root evidence. No application
client supplies a new spine, caller scope or resource proof.

`advance_enter_of_step` keeps its exact original signature. The production
core call, generated-row/callee-spec/core construction, checked caller scope,
stored argument locals and direct supported/resource frame construction are
unchanged. So is the reindexed callee-outcome construction. Only the existing
checked `.direct` agreement is named before hiding its spine; the focused
`ConcreteStructuredValidatedStackAgreement.reindex` preserves that index across
the same `entry.sourceFramesEq`/`entry.targetFramesEq`.

`advance_enterAtRoot_of_step` extracts the caller's checked spine, applies
`concreteStructuredRootResultKind_push`, and attaches root evidence to the
actual named callee's `agrees` and `frames.validation` using its reindexed
checked push. It also exposes the source caller alignment and pushed target
alignment on that same spine. It does not attach an unrelated existential
stack or assume the successor root.

The result retains one target step, the selected row/callee spec and code,
`row.targetFunction.toLocals physicalArgs` and body, saved caller continuation/
remainder, unchanged witness and remaining budget. Callee labels and reuse
facts are empty; active/expected results are exactly `site.calleeResultKind`
and `some site.calleeResultKind`. The callee entry snapshot is the current
source runtime/target store/witness; the prior caller entry snapshot and
resources are preserved in the checked direct frame, as in the original proof.
The exposed frame equations push a source `.bind` and target `.call` with its
saved `local.set` continuation; they are not unchanged-frame equations.

Only ready evidence and a successful source step plus compiler-internal root
evidence are public producer premises. No caller/callee result equality, scope,
resource, ABI classification, admission or final-client root premise is added.
The actual-producer regression assumes differing caller/callee result kinds
and an empty *saved caller* stack. It retains the one-step path, actual callee
and root, singleton checked caller spine and exact pushed-frame equations,
while proving that the callee's active result differs from the original root.
The empty-stack active/root corollary is used only for the original caller,
never for the nonempty post-push stack.

Baseline original at `debc463d`, final compatibility/helper/rooted entry and
indexed reindex all have exactly `propext`, `Classical.choice`, `Quot.sound`.
The inventory covers 124 endpoints; no generated dependency, new axiom or trust
approval is introduced. Other direct-return/pop, saturated/lazy entry,
cache publication, global root/schema assembly, admission and traps remain
separate, as do footprint/whole-helper/tagged-result and all 14 W72 obligations.

### Original-root preservation through named saturated entry

`ConcreteStructuredValidatedSaturatedCallReadyOutcome.advance_enterWithSpine_of_step`
exposes the production-selected callee spec and actual named code outcome,
retaining the same input checked caller spine through `.saturated` and the
accepted indexed `ConcreteStructuredValidatedStackAgreement.reindex`. The
compatibility `advance_enter_of_step` keeps its original public signature and
selects the spine from the already-validated caller agreement.

`advance_enterAtRoot_of_step` instead gets that same checked spine from internal
input root evidence and uses `concreteStructuredRootResultKind_push` to preserve
the original root on the actual callee. It adds no caller scope, layout,
capacity, ABI equality, admission, final-client or desired-successor premise.
Existing ready/code/stack relations and runtime semantics are unchanged.

The core entry call, generated row/spec, saved caller scope, frame/resource and
complete callee construction are retained. In particular:

- The target path has exactly `3 * (matcherCount + 1) + argumentCount + 1`
  steps, with strict positivity exposed.
- The source pushes the original bind continuation. The target pushes the
  saturated call frame with `callerLocals.values` as its remainder and only
  `[.localSet resultIndex]` as its call continuation, followed by the original
  replicated failed-matcher labels and selected-matcher label/rest. This is
  not the direct-call frame protocol.
- The core-selected `callRuntime` and `nextStore` become the callee entry
  snapshot, including closure consumption already justified by the old proof.
  Witness, remaining budget and physical argument locals/body are unchanged.
- Callee labels/facts are empty. Active result is
  `resolution.targetResultKind`; immediate expected result is
  `some site.resultKind`. Neither is identified with root. The original
  `resolution.targetResultRefines`, `related.sharedCapacity` and checked saved
  caller resources are retained exactly; refinement is not replaced by equality.

The actual-producer regression starts with saved empty caller frames and a
callee active kind different from the caller. It obtains the real named callee,
exact positive path, singleton checked caller spine, both pushed-frame equations
and original root, with the immediate expected index unchanged. Empty-stack
active=root is used only before the push, never for the nonempty callee stack.

Baseline original and all three final entry/interface endpoints have exactly
`propext`, `Classical.choice`, `Quot.sound` and the existing private
`LinearMemory.assembleByte32._native.bv_decide.ax_1_6` dependency. The expanded
127-endpoint audit records that inherited debt; it is not a new trust approval.
Lazy entry/cache publication, caller pop/return, global root/schema assembly,
closure-footprint and whole-helper/tagged-result obligations remain separate.

### Remaining terminal assembly obligations

| Obligation | Exact current evidence | Remaining work |
|---|---|---|
| Recover the terminal yield | `sourceExecReturned_terminal`, `ConcreteStructuredValidatedCodeGlobalOutcome.terminalYield_of_control`, and the function/export `terminatesWith_of_validatedReturn` lemmas | Discharged for the existing global relation and a successful final source step. |
| Preserve the export's selected result ABI | `validatedCodeRoot_rootResult` establishes root identity; `advance_returnPreciseAtRoot_of_step` preserves it through a precise return; `advance_returnYieldAtRoot_of_step` derives the exact root-ABI yield at an empty continuation | The general returned outcome still permits an independent `kind`; compatibility with no caller is only `True`. Preserve the root-indexed checked spine and producer precision through the remaining global branches and assembly, without adding a client assumption. |
| Connect source termination to executable return | `terminatesWith_of_classifiedExecSteps`, `terminatesWith_of_classifiedExecEvaluates`, and `terminatesWith_of_classifiedRun` compose the existing ranked prefix with terminal extraction and adequacy | Discharged conditional on the existing universal classifier and entry contracts, with existential represented kind. Compiler admission closure and root-kind provenance are not discharged. |
| Match faults | `StructuredWasmControl` has running/breaking/returning/halted states, and `StructuredWasmOutcome` describes successful control only | A trap-aware extension and its adequacy proof are a separately coordinated semantic change. Existing `ConcreteFaultSimulation` results do not automatically supply this missing structured-machine branch. |

These are interface obligations, not evidence of incorrect generated code.
In particular, the current return rule does produce the precise result kind;
the audit identifies where its general relation forgets that precision.
Resource exhaustion remains governed by explicit preconditions, not an
unproved general matching-failure claim.

## Measured trust budget

`TrustAudit.lean` is imported by the default `FirTalos` umbrella and compares
transitive compiled dependencies using Lean's `collectAxioms`. The inventory
is exact for each theorem, including removals: a changed set requires review.
There are no name-prefix allowlists, and `sorryAx` is rejected even if someone
adds it to an expected list. Missing or non-theorem endpoints are errors.

| Endpoint family | Standard axioms | Recorded generated axioms |
|---|---:|---:|
| `ConcreteRankedTraceSimulation.execSteps` | 3 | 0 |
| `precomposeStutteringPass` | 3 | 0 |
| `finiteTraceCorrect_of_sourceInvariant` | 3 | 57 |
| `finiteTraceCorrect_of_schemaSourceInvariant` | 3 | 57 |
| `ConcreteSupportedExport.correctReturn` | 3 | 0 |
| `ConcreteSupportedExport.faultCorrectOfSimulation` | 3 | 0 |
| `ResidentReplacement.externalLetStepSimulates_of_definedCall` | 3 | 0 |
| sampled `UInt64ObjectInstallation` termination theorem | 3 | 20 |
| concrete `abiLiteralMain_export_correct` | 3 | 27 |
| all ten new sensitivity lemmas | 0–3 | 0 |
| all five structured terminal-return bridge lemmas | 2–3 | 0 |
| all five terminal-extraction and validated-return lemmas | 3 | 0 |
| both precise-return producer lemmas | 3 | 0 |
| all three classified terminal-simulation lemmas | 3 | 0 |
| root-preserving return producer and exact-root yield corollary | 3 | 0 |
| original direct-let wrapper, frame-exposing helper and root-preserving successor | 3 | 54 |
| original and rooted validation-derived inc/dec/delete, plus delete helper/transport | 3 | 1 |
| original tag mutation/validated rules, frame helper and both rooted producers | 3 | 1 |
| original USize mutation/validated rules, frame helper and both rooted producers | 3 | 1 |
| original packed-scalar mutation/validated rules, frame helper and both rooted producers | 3 | 2 |
| original active-witness FVar/erased field effects and schema rules, frame helpers and rooted producers | 3 | 1 |
| original named direct-call staging and rooted ready-outcome producer | 3 | 0 |
| original saturated/lazy staging and rooted ready-outcome producers | 3 | 0 |
| original pure-external staging and rooted ready-outcome producer | 3 | 0 |
| original external-ready host step, named-bind helper and rooted bind producer | 3 | 1 |
| original external destination bind, named-active/frame helper and rooted active producer | 3 | 0 |
| original lazy-cache hit and rooted bind-outcome producer | 3 | 0 |
| indexed checked-spine reindex, original direct entry, spine helper and rooted callee producer | 3 | 0 |
| original saturated entry, checked-spine helper and rooted callee producer | 3 | 1 |
| original default-only case wrapper, frame-exposing helper and rooted successor | 3 | 0 |
| original object-case wrapper, frame-exposing helper and rooted successor | 3 | 0 |
| original UInt8-case wrapper, frame-exposing helper and rooted successor | 3 | 2 |
| original validation-derived case dispatcher and rooted composition | 3 | 2 |
| original persistent increment/decrement and rooted successors | 3 | 0 |
| original ordinary increment/decrement, frame helpers and rooted successors | 3 | 1 |

The standard set is `propext`, `Classical.choice`, and `Quot.sound`. The exact
generated names live in `TrustInventory.lean`. Most dependencies in the two
export theorems arise through fixed scalar/boxing facts; two arise through
byte-assembly `bv_decide` proofs. Imported axioms are counted only if the named
theorem actually depends on them.

The classified terminal theorems are generic in the existing classifier. Their
standard-only inventories do not remove the generated dependencies of a
particular classifier construction or application instance; such instances
must still receive their own exact audits.

This inventory records existing debt, not new approval of those assumptions.
`FIR-BUG-wasm-none-endpoint-native-axiom-audit` stays confirmed until that debt
is resolved. Source hashes remain useful upstream drift checks; their success
does not establish an axiom-free endpoint or prove the upstream alpha bridge.

## Validation commands and integration wiring

```sh
python3 integration/talos/test_proof_trust.py
python3 integration/talos/check-proof-trust.py
make check
make talos-check
git diff --check
```

The Python gate scans maintained Lean sources under `Fir/`, `Inspect/`, the
root and Talos umbrellas, and `integration/talos/FirTalos/`, using the existing
comment/string-aware lexer and explicit project-axiom registry. It then builds
the audit dependency cone and forces direct batch elaboration of the audit,
so a stale audit olean cannot bypass the check. Scratch is worktree-local.

The Lean rejection tests inspect actual native-evaluation dependencies, a
temporary compiled theorem depending on an unregistered axiom, and a temporary
theorem depending on `sorryAx`; the latter two restore the environment. Source
tests reject integration axioms/placeholders and accept comments/strings.

Integration at main `1121f917` wires the expanded source scan and its tests into
the shared root gate, and forces the compiled audit in `make talos-check`.
The endpoint checks also participate in the default Talos build through the
W6-owned umbrella. The root `Makefile`, source audit script, and repository-wide
roadmap remain integration-owned and are not edited by the terminal-proof slice.

## Next proof checkpoint

Retain PA1/PA2 compiler provenance as the admission work. For PA3's terminal
corollary, the maintained global relation now supplies the terminal yielded
state, and the local return producers now retain the exact active-function
result kind. The classifier's simulation now also supplies the complete target
prefix internally. The root-result foundation now supplies compiler-derived
entry evidence, a shared caller push/pop law, and exact terminal consumption.
Carry precise producer and root result identity through global simulation so
the new classified terminal corollaries can state the
root export's selected ABI, then discharge the universal compiler classifier
through the ongoing admission work.
Handle the trap-model extension separately.
Do not reintroduce a client source invariant, target path, or ABI-provenance
assumption in the final corollary.

Separately remove native-evaluation dependencies in small owner-scoped batches,
starting with the fixed scalar/boxing facts, and update the measured inventory
downward. New public endpoints must begin with a standard-axioms-only budget.
W7's cache-elimination admissibility and complete linker preservation remain
separate generation contracts; this slice changes no emitter or artifact.
