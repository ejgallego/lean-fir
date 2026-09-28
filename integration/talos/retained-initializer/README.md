# Checked retained initializer: source execution and publication

This optional W6 proof cone consumes `RetainedRC2.program`, generated from the
immutable lean-zip source snapshot by the W7 checked-capture recipe. It does
not contain a copied initializer AST. `RetainedDeclarations` extracts the two
external declarations from that same definition with kernel-checked lookup
and body equations. Production ordinary/closed/resident lowering in the
unchanged `RetainedRC2` harness consumes the definition's readback too.

`RetainedInitializer.reaches_published` proves that the actual initializer
`Zip.Spec.DeflateStoredCorrect.deflateStoredPure._closed_0` reaches its exact
published source state in 12 steps from a cold cache. The runtime contains a
fresh singleton Array holding tagged zero, its cache publication, unchanged
world, and the original trace followed by exactly the `Array.mkEmpty` and
`Array.push` events. A thirteenth step returns.

`evaluates_and_preservesCaller` connects that reached state to historical
caller facts. It asks for the saved fact interpretation, witness transport
and current live-heap relation; it does not ask for a region, graph separation,
prefix preservation, body execution or target path. The caller environment
stays fixed. This remains pointwise saved-caller preservation, not recursive
suspended-stack reconstruction.

`reaches_published_withFrames` generalizes the execution to an arbitrary
suspended frame stack. `resumesCaller` derives the exact 13-step prefix through
destination binding, restoring the caller's environment, joins and remaining
frames, and discharges `ReuseTokenOrdinaryBindTransport` for that result.

`return_pop_preservesCaller` applies this to the existing concrete return/pop
consumer: the 13-step source prefix and the two target return/bind steps end
in related states with the full caller cache/ABI frame restored. Its premises
still include the target return focus, callee frame, witness/capacity transports,
historical caller scope and suspended tail. It does not establish the target
callee prefix or reconstruct the stronger hereditary resource stack.
`resumedCaller` is a transparent proof-only state description, not an extra
compiled executable or a replacement source program.

`evaluates_and_retainsCallers` additionally derives the new entry-indexed
`RetainedCallerTransport` law for every representable historical caller map,
not a caller-selected map. That law is the source component consumed by
`RetainedCacheEntryFrame.restoreCaller`, which composes the entry package
through return without blanket ordinaryness. The negative regression
`example_not_blanketOrdinary` shows why the distinction matters: the actual
fresh published Array violates the old all-location condition. The central
active/suspended resource stack now uses the replacement. The remaining
heap-result publication rule must derive its cumulative transport before
lifting object/tobject lazy-miss exclusions; this body theorem alone is not
that central admission result.

`reaches_publicationInput_withFrames` exposes the actual 11-step prefix with
the cache marker still pending. `executes_and_publishesCache` takes that source
publication step and derives the concrete cache host operation, post-runtime
refinement, and cumulative entry transport including the two global-update
store expressions. It derives the closed fresh graph from the checked body's
singleton-Array result. The concrete pre-cache relation, entry transport,
represented result and cache-slot facts remain explicit; no target prefix,
seven-instruction publication path, global-index alignment or full post-cache
stack relation is claimed by this endpoint.

`executes_and_restoresCallerScope` strengthens that result by recovering the
suspended caller's full entry-relative resource scope: represented facts,
ordinary saved tokens, cache-table agreement, external-handler contracts,
allocation headroom and closure ABI. It uses the same restoration theorem as
the central validated non-heap dispatcher. Its pre-publication callee scope and
represented result remain premises; it does not prove the target callee prefix,
destination bind, full stack assembly or central heap-result admission.

`executes_publicationSuffix` additionally proves the seven generated Wasm
steps from initializer return through cache host publication, value/flag writes,
conditional exit and value reload. The compiler-supported caller is for the
same `RetainedRC2.program`; import contract alignment and physical global-lane
existence are derived. The source publication step and restored caller scope
are retained. The target initializer prefix and following destination bind are
still outside this theorem, as is complete source/target stack assembly.

`publication_bind_resumesCode` closes that destination-bind suffix. It runs
the checked source initializer for thirteen steps under a waiting caller and
matches publication/binding with eight target steps, ending in the ordinary
`ConcreteStructuredCodeCoreRel`. The returned value is bound, the saved join
environment restored, and the original caller scope/suspended resource tail
retained; the overwritten destination's reuse fact is erased. The proof
constructs the intermediate bind relation rather than requiring it. The
pre-publication callee scope and represented result, compiler continuation/local
alignment, and suspended resource tail remain premises. Target callee execution,
production Array external refinement, residual validation and general heap-miss
admission are still separate obligations.

The two source external contracts are uniform primitive laws, not a
per-program invariant. `FreshArrayExternalContract` specifies empty allocation
and the fresh/non-full tagged-push branch. `freshArrayExternals_contract`
provides an executable consistency witness; other requests are rejected by
that deliberately limited model. This is **not** the production external
implementation. Its connection to concrete external admission and resident
helper execution remains to be proved. The generic
`mkEmptyExternalCallEvidence_of_budget` now derives concrete empty-allocation
call evidence from headroom, request refinement and an installed-handler law,
using this source contract. It derives allocation success and the full response
relation, not the installed law itself.
`pushFreshTaggedExternalCallEvidence` now supplies the matching fresh/non-full
push boundary, deriving mutation and exact singleton result while preserving
the witness and budget. It accepts any represented tagged payload and derives
the Array descriptor from heap refinement. Its installed-handler branch equation
also remains explicit. Composing the generated target callee prefix is next;
neither primitive endpoint by itself executes the initializer's generated code.
The shared `ExternalCallShape`/`ConcreteStructuredExternalCallControl` staging
and imported-call rules now accept those evidence constructors without forcing
the result into a Nat/Int/scalar family. `RetainedInitializer.mkEmptyCallShape`
in `RetainedArrayCalls.lean` now extracts the actual call from the
checked initializer and proves its compiler/source equations. It distinguishes
actual `#[erased, tagged]` arguments from declared `#[erased, tobject]` parameters:
directional refinement justifies this widening, not physical-lane compatibility.

`RetainedInitializer.mkEmpty_stage_call_bind` composes argument staging, concrete
empty allocation and destination binding: three source transitions match the
generated target prefix plus two target transitions. The conclusion is the
actual captured continuation with a related Array result, restored control
stacks and exact residual allocation budget. Required entry facts are a supported
compiler function, local alignment/current code focus, the two local-kind lookups
and capacity value. Source primitive laws, installed-handler conformance and
headroom remain explicit. The literal entry premises are discharged by the
composition below; the following push, hereditary resource-scope transport and
publication composition remain separate. The central admission policy has not
changed.

`RetainedInitializer.literals_mkEmpty_stage_call_bind` now starts at the checked
initializer **body** and composes both literal lets with that call. It derives
five source transitions and the generated argument prefix plus six target
transitions, with the same post-Array continuation and residual budget. The
capacity lookup is now a conclusion of literal execution, not a premise.
`advance_immediateLiteral` and `advance_smallTaggedNatural` are reusable rules:
they preserve the exact source runtime, target store and witness. The natural
rule requires the value to fit the wasm32 immediate payload; it does not coerce
arbitrary naturals to tagged values. Both use only standard Lean axioms.

`RetainedInitializer.body_returns` now connects **the complete captured body**:
two literals, `Array.mkEmpty`, UInt8 boxing, `Array.push`, and return. It derives
ten source transitions and a finite target execution ending in a precise
`.object` yield related to the singleton tagged-zero Array. Neither a source
execution nor a target path is a premise. The final heap retains the original
headroom minus the five-slot Array allocation; boxing and the selected fresh,
non-full push allocate nothing. Both control stacks and joins are preserved.

The reusable `advance_boxUInt8` leaves runtime/store/witness unchanged.
`arrayPushOperands` reconstructs the actual words from parameter refinement;
`advance_pushFreshTagged_bind` composes the existing primitive refinement with
call and destination binding. Allocation's unchanged external implementation is
now exposed, allowing one installed implementation to serve both Array calls.
The push handler law is restricted to states related to this fresh empty Array,
represented operands and the exact named request; it does not assume that all
Array pushes use the in-place branch.

The push block now uses `ConcreteRegionExternal` throughout: active code stages
to a region-indexed call, the actual host response produces a region-indexed
pre-bind state, and binding returns active code at the **original initializer
entry**. The generic host rule separates response refinement from preservation
of owned edges; the push producer derives the latter from its semantic response
and `HeapRegionClosed.pushFreshTagged`. Its budget comes from the input scope.
`body_returns` no longer reconstructs a scope/region after this block. The
empty-allocation block still uses blockwise transport; general nested lazy-frame
closure and production handler conformance remain open.

`RetainedInitializer.body_publishes_and_resumesCaller` now composes this body
with cache publication and the caller's destination bind. It derives twelve
source transitions and a matching target path, ending in ordinary caller code
with the full hereditary resource scope and suspended stack restored. The
post-body scope, represented publication value, closed fresh region, and both
execution paths are conclusions, not premises.

This uses the existing `RuntimeStepTransports` package, now composed and exposed
by the Array call/bind rules. `afterBody_withoutReuseFacts` reconstructs the
active scope for a region with no retained reuse-token facts from its entry
scope, transports, state relation, local alignment and residual budget. Arbitrary
older caller facts are preserved through the cumulative entry transport; they
are not erased. The new generic algebra uses only `propext` and `Quot.sound`.

`RetainedInitializer.lazyMiss_publishes_and_resumesCaller` now starts at the
staged cold-cache invocation and derives thirteen source transitions and the
whole matching target path back to caller code. The reusable `enterBody` rule
derives the initial body focus, empty callee resource frame and both installed
continuation stacks in one source / three target steps. It works for heap
results without using or weakening the central restricted lazy-stack rule.
The generated declaration row is now selected internally from the caller's
supported pipeline and checked initializer declaration. The callee's
supported-function package is inherited from that row, not supplied independently.

`initializer_bindingKinds` now derives all five binding-kind lookups from the
actual production collection/refinement equations. The reusable
`ConcreteGeneratedInternalDeclaration.loweredLocals` recovers those equations
for the same generated function using compiler-derived name uniqueness. The
cold-cache theorem consumes this result internally: none of the five lookups
is a caller premise. No new native evaluation or axiom is introduced.

`let_publishes_and_resumesCaller` additionally starts at the caller's actual
source let. The reusable `stageLazyCall` derives the source staging step and
recovers all numeric cache/call/destination indices and the target suffix from
compilation/adaptation. The complete theorem derives fourteen source steps and
matching Wasm execution to ordinary caller code, restoring the original joins
and continuation stacks. No staging step, invocation focus, generated callee
row, callee frame, installed stack, post-body scope or execution path is assumed.

`validatedLet_publishes_and_resumesCaller` now starts and ends with
`ConcreteStructuredValidatedCodeOutcome`. It derives lazy-call admission,
module-wide cache alignment, the current focus and caller resource stack from
that relation. The generic `ConcreteStructuredAlignedValidationState.afterLet`
recovers continuation validation from residual local alignment, while
`lazyCall_of_selected` identifies the compiler-selected declaration/result.
Existing frame agreement is transported through the completed execution, not
requested again from the client.

`rootedLet_publishes_and_resumesCaller` further returns the existing
`ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt` at the resumed caller,
with the original export result kind and the evolved heap witness. The proof
uses the unchanged outer source/target frame stacks to transport the existing
root agreement. The initializer's `.object` result does not replace the
caller's or export's ABI. Active-result/root evidence is the same evidence
already stored in the input rooted relation; no future return, target path or
new invariant is assumed. This makes the block's endpoint usable by the
existing rooted finite-prefix and terminal-result proofs, under their remaining
admission/resource premises. It does not establish the central relation at
every intermediate heap-result lazy frame.

The body now returns its construction-region evidence as well. The six-step
prefix establishes `HeapRegionClosed` when the empty Array is allocated;
`HeapRegionClosed.pushFreshTagged` preserves it through the actual in-place
push. `body_publishes_and_resumesCaller` consumes that evidence instead of
reconstructing closure by treating the final singleton Array as a new
allocation. This is internal producer evidence, not an added client premise.

The reusable `ConcreteRegionTransport` module also transports region closure
through ownership-graph-preserving updates and recursive cache persistence.
`RetainedCodeEntryTransports.publishFreshCache` now returns region closure
alongside the restored caller transport. Publication may change ordinary cells
to persistent cells: preserving owned edges is not blanket ordinaryness
preservation or proof that an arbitrary published root is fresh.

The generic publication suffix is now split at its real intermediate state.
`ConcreteStructuredResourceScope.publishFreshCache_step` proves one source
publication step and seven target steps to `ConcreteStructuredExternalBindCoreRel`,
including restored caller resources and surviving region closure. The existing
two-source-step publication/bind theorem composes that result with the ordinary
bind rule; retained executions therefore use the same factored transition.

`ConcreteStructuredValidatedCodeOutcome.publishFreshCacheAtRoot` attaches the
saved caller's continuation validation and checked stack/root agreement, yielding
the existing rooted global `.externalBind` outcome before destination binding.
This is a reusable proof-side boundary, not yet a new global constructor for
the pre-publication heap-return state.

`body_returns` now produces `ConcreteStructuredFreshYieldCore`: the represented
heap result, current resource scope at the original initializer entry, region
closure and fresh-root bound are retained together. The scope is derived from
the actual body transports and the entry frame already available to the caller.
The twelve-/fourteen-step consumers have no additional premises and use this
state directly. `ConcreteStructuredFreshYieldCore.publishAtRoot` consumes it
with the saved validated caller to derive publication into the existing rooted
global relation, starting at the actual related target state. The remaining
gap is general intermediate lazy-state closure, not another independent
publication or post-body resource premise.

The active-code companion is `ConcreteStructuredRegionCodeCore`. Cache-miss
`enterRegion` constructs it with the actual saved continuation frames and the
unchanged entry cutoff. The six-step allocation/boxing prefix and three-step
push block retain it, and `advance_return` turns it into the fresh-result
relation in one source/two target steps. No scope is reconstructed from scratch
at return. A negative check rejects re-anchoring the returned relation at the
current allocation frontier. The thirteen-/fourteen-step public signatures
are unchanged; internal body helpers now consume the active relation.
This does not yet relate each external staging/bind state inside those blocks
or supply a general nested heap-lazy suspended-frame constructor.

Remaining premises are the supported caller and its current validated relation,
the initializer call's identity, empty cache, source primitive contracts,
installed handler laws and finite headroom. No independent call-admission,
local-kind, cache-environment or continuation-validation premise remains.
Installed Array-handler conformance remains a separate runtime obligation.
Central heap-miss admission, resident linking and encoded-artifact correctness
remain separate; this is not a theorem for the whole lean-zip application.

## Reproduce

From the W6 worktree, with repositories containing the exact source objects:

```sh
bash integration/talos/retained-initializer/check.sh \
  /path/to/lean-zip /path/to/zip-common
```

The script archives lean-zip `273d0d6c` and zip-common `4425bab1` into the
worktree-local `.deps/retained-rc2`, copies maintained source templates, and
uses the worktree's official toolchain and Talos setup. It fetches no substitute
source revision and shares no mutable build state with W7. Lake may obtain its
pinned build dependencies if absent. Source/setup identity and the limitations
of capture are documented in `Fir/Compiler/LCNF/README.md`. Adding the Talos
proof dependency changes the private Lake setup identity, not the captured
source or initializer body.

The gate builds the consumer, imports the checked definition in a fresh
process, and forces direct batch elaboration with an exact per-endpoint axiom
audit. The source endpoint inherits the seven **existing** native-evaluation
axioms of `boxUsesTaggedRepresentation_boxedScalar`, due to upstream opaque
expression comparison. It introduces no new native evaluation or axiom.
The separate mkEmpty target consumer has its own exact audit: standard Lean
axioms, the existing byte-assembly dependency, and one new native-evaluation
dependency checking only the closed `Expr` ABI classifications for `lcErased`,
`tobj` and `obj`. No execution or heap assertion is established by native
evaluation. Its proof-only captured projections are noncomputable; the observed
upstream executable-projection failure is recorded in
`FIR-BUG-wasm-none-retained-projection-codegen`.
Forced batch checking can still print that compiler panic while exiting zero:
the accepted `b25df81ce` source and the fresh-result successor both reproduce
the same panic sites. The kernel endpoint audit passes; this is not a claim
that upstream native compilation is diagnostic-free.
The body-prefix endpoint additionally records one closed native check for the
UInt8/tagged literal ABI classifications. The full body additionally inherits
the existing seven scalar-box policy comparison axioms and UInt8 result-kind
comparison axiom; this slice adds no native evaluation. The maintained gate
audits all eleven retained target/static endpoints independently (twenty-five consumer
endpoints including the fourteen source/publication endpoints).
The captured program/body equations remain free of generated axioms. Generic
external-model and finite-prefix helper proofs use standard axioms and are
also in the ordinary Talos trust inventory.
The concrete publication endpoint additionally inherits the existing
`LinearMemory.assembleByte32` native bitvector axiom through recursive cache
persistence. Its separate exact audit records that dependency; the source-only
endpoints keep their narrower inventory. The full-scope consumer inherits the
same exact dependencies, as does the executable-suffix consumer. There are
fourteen consumer endpoints, including the publication/bind code-core result.
