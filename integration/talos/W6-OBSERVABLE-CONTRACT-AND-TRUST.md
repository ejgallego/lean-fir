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
