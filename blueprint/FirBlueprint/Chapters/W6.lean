import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Notation
import FirBlueprint.Targets.Admission
import FirBlueprint.Targets.NatAdd
import FirBlueprint.Targets.NatAddAdmission
import FirTalos.ConcreteRootedTerminal
import FirTalos.ConcreteFaultCorrectness
import FirTalos.ConcreteFinalLcnfTyping
import FirTalos.ConcreteSupportedPipeline
import FirTalos.ConcreteRegionEntry
import FirTalos.ConcretePublicationValidation

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Formal reference catalog (W6)" =>
%%%
tag := "w6-formal-catalog"
%%%

The {ref "compiler-argument"}[compiler argument] develops the first-reading
account from a concrete call to the successful-return guarantee. This catalog
records its contracts, checked Lean associations and open obligations. Node
status describes the associated declaration or planned statement; the
{ref "proof-trust"}[trust account] records the separate axiom and contract
boundaries.

:::author "w6" (name := "FIR W6 proof lane")
:::
:::author "root" (name := "FIR integration owner")
:::

:::group "contracts"
Observable contracts
:::
:::group "compiler"
Compiler facts
:::
:::group "construction"
Heap construction
:::
:::group "execution"
Execution
:::
:::group "frontier"
Open obligations
:::

# Successful returns and the selected instance

:::definition "return-post" (parent := "contracts") (lean := "FirTalos.Concrete.RefinedReturnPost") (autoDeps := true)
A successful target return represents the exact source value at the specified
ABI kind. One refinement witness relates the live heap, globals, world and
ordered external trace, with no target runtime failure and the precise return
stack. The ABI is chosen by the export; existentially choosing a convenient
kind would weaken the contract.
:::

:::definition "successful-export-property" (parent := "contracts") (uses := "return-post")
For the supported program/package/export $`p,M,e` and its fixed result ABI
$`A`, every related allowed invocation and successful finite source evaluation
must yield actual target export termination with {bpref "return-post"}[] and
exact source observation identity. The {ref "w6-notation"}[full property]
spells out the entry/cache/arity and external/resource conditions, quantified
arguments and observation-facing existential runtime conclusion.

This expository definition adds no Lean declaration. The fixed Stored instance
and general compiler theorem remain open. {bpref "conditional-return"}[]
proves the conclusion from supplied uniform compiler current-step admission
and address-space safety; admission and reached-state preservation must be
derived for the desired compiler theorem.
:::

## First whole-program instance

:::theorem "stored-export-instance" (parent := "execution") (owner := "w6") (tags := "open, statement-review") (priority := "high") (uses := "successful-export-property")
For the actual captured final impure program with selected entry
`Zip.Wasm.compressStored`, prove $`\FirSuccess{p_{\mathrm{stored}}}`
after its production supported-export assembly. The source nomination is
lean-zip `273d0d6cd9cab77c7f3489b0b0b1f6e543315d21` with zip-common
`4425bab1f9522307d77e8d485bc536149ba31c36`. The compiled module and result ABI
must be those supplied by the selected export.

This rough instance theorem remains open. It quantifies every related admitted
input, entry runtime and successful finite source evaluation, with the same
observation and return postcondition as the general target. Source primitive
laws, installed implementation conformance and finite resources remain explicit
execution contracts. A finite smoke corpus supplies separate validation evidence.
The {ref "retained-example-boundary"}[concrete account] identifies existing
source application and initializer theorems, plus the further bridges needed
for a released-byte roundtrip.
:::
:::proof "stored-export-instance" (uses := "conditional-return")
The current independent route checks the actual captured declarations/body,
export/ABI and lowering/adaptation equations, then constructs the program's
semantic admission and maintained-invariant facts. Concrete initializer blocks
already derive source/target paths and caller preservation; complete operation
coverage, intermediate provenance and heap-miss admission still need proof.
Supply the resulting admission to the existing conditional return consumer.
Its current interface quantifies every supported function and recursively
validated current outcome of this program; proving only the initializer's
reached states does not discharge that uniform law. Static validator acceptance
alone cannot supply these semantic premises.

After {bpref "validated-return"}[] is complete, a future route may specialize
that general theorem and discharge this program's premises. That planned route
does not form a current proof dependency. The statement, quantified input scope
and retained conditions must stay the same when its proof route changes.
:::

# Contract and operation catalog

:::definition "fault-post" (parent := "contracts") (lean := "FirTalos.Concrete.RefinedFaultPost") (autoDeps := true)
A target trap represents the source's structured semantic fault under a common
heap/runtime witness. An unrelated target memory trap or ABI mismatch does not
satisfy this contract merely because both executions stopped.
:::

:::definition "prefix-contract" (parent := "contracts") (lean := "FirTalos.Concrete.ConcreteFiniteTraceCorrect") (autoDeps := true)
Every finite source execution prefix has a finite target path with matching
world and ordered external observations. This definition alone does not
constrain the terminal returned value. See {bpref "return-post"}[] for that
additional requirement.
:::

:::definition "admission-interface" (parent := "contracts") (lean := "FirTalos.Concrete.ConcreteStructuredCompilerCurrentStepAdmission") (autoDeps := true)
The step proof needs a semantic operation contract whenever validated source
code advances. Current-step admission supplies the representation and operation
facts together with the exact resource cost. Its uniform law covers every
supported function, recursively validated current outcome and successful source
step at that outcome. The compiler
correctness argument must construct this law from compiled code and the
maintained invariant.

:::

:::definition "address-space" (parent := "contracts") (lean := "FirTalos.Concrete.ConcreteStructuredCurrentStepAddressSpaceSafety") (autoDeps := true)
An admitted allocation still has to fit the physical wasm32 address space. This law
checks an admitted operation's recorded cost against the current frame's
remaining budget. It is an execution resource condition retained separately
from semantic admission.

:::

:::definition "finite-runtime" (parent := "contracts") (lean := "FirTalos.Concrete.ConcreteStructuredCurrentStepFiniteRuntimeSafety") (autoDeps := true)
Finite reference-count header headroom and saturated-closure capture capacity
at the selected validated step. This existing execution contract is retained,
separately from allocation address-space safety.
:::

:::definition "external-spec" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (priority := "high") (lean := "FirBlueprint.Targets.externalSpec") (autoDeps := true)
The primitive request/response semantics required of successful external calls.
Its Lean body remains an explicit specification hole. Specify the operation's
mathematical result from decoded arguments, its returned representation, heap
and location-cursor effects, and world effects. The interpreter adds the call
event exactly once after the response, using the staged waiting runtime.
The contract must not contain compiler admission or a future target path.
Until representation and supported-call coverage are settled, the endpoint
statement is provisional. See {bpref "external-realization"}[] for implementation
coverage and {bpref "external-admission"}[] for the compiler-side bridge.
:::

# Reviewing the external contract

The {ref "external-domains"}[external-domain chapter] gives the complete live
proposal: source request/response semantics, the eleven reviewed pure names,
metadata and decoding domains, Int representation alternatives, implementation
availability and the compiler admission boundary. Its source review revisions
and retained probe evidence are explicit.

The essential distinction is between specifying primitive behavior, showing
that the intended implementation provides it, and deriving compiler admission.
The checked Nat slice below illustrates all three boundaries. It does not
settle the global specification, Int mismatch or wider primitive coverage.

# First checked external clause: Nat addition

The first implementation-backed clause is independent of the Int representation
decision. It checks the actual validation dispatcher through its private
declarations. The clause and its realization are separate from the still-open
global specification.

:::definition "nat-add-contract" (parent := "contracts") (owner := "w6") (tags := "statement-review") (lean := "FirBlueprint.Targets.NatAddResponse") (autoDeps := true)
A request named {name}`Nat.add` has exactly two arguments that decode to natural
numbers in the incoming runtime. An argument may be a tagged payload or a live
heap cell containing a natural. The response is exactly the existing semantic
natural response for the sum, fixing value, heap, next location and world.
The domain uses no handler-success or compiler-admission hypothesis.

Metadata is unrestricted in this source-handler clause because the actual
handler ignores it. This is stronger handler coverage, not proof that arbitrary
metadata or every tagged payload is a valid compiler input. Compiler metadata,
ABI alignment and runtime validity remain with {bpref "external-admission"}[].
The formal definition is complete; adopting this clause in the global
{bpref "external-spec"}[] remains a specification-review decision.
:::

:::theorem "nat-add-realization" (parent := "execution") (owner := "w6") (lean := "FirBlueprint.Targets.validation_natAdd") (autoDeps := true)
For every request and runtime in the Nat-addition input domain, the actual
validation external dispatcher succeeds and returns the exact specified
response for the sum. The theorem includes the response-clause witness.
It covers tagged, heap and mixed inputs, and both tagged and allocating results,
with arbitrary request type metadata. This discharges availability and response
correctness for this source-handler slice without assuming a successful call.
It proves neither compiler admission nor execution of the resident Wasm helper.
:::

# Compiler-derived facts

:::definition "precise-local-semantics" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.SemanticEnvAtLocalKinds") (autoDeps := true)
Every binding selected by a local-kind row has the promised source ABI shape.
The predicate can describe the ordinary validator row or a more precise
compiler-produced row. Its definition does not construct either row or prove
that an analysis maintains it. See the {ref "provenance-design"}[provenance argument].
:::

:::definition "call-provenance-coverage" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.NonRefiningArgumentsCoveredBy") (autoDeps := true)
For each non-refining variable occurrence in the current argument/actual/expected
ABI row, the precise local row contains the expected ABI. Membership in that
exact argument row is required; unrelated locals impose no obligation here.
This is static coverage, separate from the semantic truth of the row.
:::

:::definition "return-provenance-coverage" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredReturnUseSiteCoveredBy") (autoDeps := true)
If the compiler-selected return ABI does not refine the expected result ABI,
the precise row records that expected kind for the returned variable.
Directional return edges require no extra provenance lookup.
:::

:::theorem "precise-call-entry" (parent := "compiler") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.SemanticValuesAtAbi.semanticEnv_of_bindParams") (autoDeps := true)
Binding semantically typed argument values to equally many parameters produces
the canonical parameter local row with its semantic interpretation. The actual
successful {name Fir.LeanIR.Impure.bindParams}`bindParams` operation and argument typing are hypotheses. This
checks the entry mechanism; callers still have to establish their arguments'
required shapes. It does not prove ordinary-step or join-flow preservation.
:::

:::theorem "nat-add-admission" (parent := "compiler") (owner := "w6") (tags := "conditional") (lean := "FirBlueprint.Targets.validation_natAdd_admission") (autoDeps := true)
The checked Nat-addition response supplies production natural-result admission
at the exact allocation cost of the sum. The existing call shape fixes the
compiled arguments, declaration metadata, successful source call, and resulting
runtime/value. Natural argument decoding, the {name Fir.Wasm.AbiKind.tobject}`tobject` result ABI, and equality
of parameter and argument ABI rows remain explicit inputs. The proof derives
the canonical response required by admission and transports the existing
runtime/result equations to it. Constructing the retained inputs is
{bpref "nat-add-site"}[]; this conditional theorem does not finish that task.
:::

:::theorem "supported-export" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteSupportedExport.exists_ofSupportedPipeline") (autoDeps := true)
The supported compilation pipeline constructs a concrete supported export from
its checked source and generated module. The closure-flow condition remains
explicit. This establishes static export identity and alignment, not dynamic
admission for all future states.
:::

:::definition "rooted-execution-relation" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt") (uses := "concrete-value-relation, concrete-heap-relation") (autoDeps := false)
For a fixed source program, compiled package and source external implementation, write
$`\FirRooted{A}{w}(\sigma,\tau)` for the rooted execution relation between
source state $`\sigma` and target state $`\tau`. Its original export ABI $`A`
stays fixed while its current representation witness $`w` can change.

The relation distinguishes seven current-control cases: ordinary code, staged
direct, saturated, lazy and external calls, an external result awaiting its
bind, and a returned value. Each case carries the validated continuation and
saved caller facts needed for its next transition. The active callee can have
its own result kind; root agreement connects its saved continuation to $`A`.
This is the relation explained in the
{ref "w6-rooted-relation"}[observation and representation argument].
:::

:::theorem "rooted-entry" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteSupportedExport.rootedPreciseCodeGlobalRoot") (uses := "rooted-execution-relation") (autoDeps := true)
A supported export constructs its initial rooted, precise relation from cache
alignment and the entry runtime invariant. It retains the export's selected
result kind. The caller supplies neither a new simulation invariant nor a
future target path.
:::

:::theorem "case-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeCoreRel.admit_cases_of_validated_step") (autoDeps := true)
A validated case node and successful source step yield exact case admission.
Normalization, discriminator selection and default/scalar/object branches are
compiler-derived. This theorem covers audit rows 8–10.
:::

:::theorem "schema-admission-bridge" (parent := "compiler") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeCoreRel.admitSchema_of_source_safe_step") (autoDeps := true)
Given schema source safety, the validated core, a successful source step and
finite-runtime safety, construct schema current-step admission at some exact
allocation cost. The bridge contains the branch dispatch and reuses existing
operation lemmas. Its source-safety input still contains the semantic obligations
listed in the Admission coverage chapter. A checked dispatcher does not prove
that input for every validated state.
:::

:::theorem "direct-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome.admit_directCall_of_compiler") (autoDeps := true)
A validated direct call yields zero-cost admission given its exact semantic
argument row at the compiler-selected ABI. Compiler local identities and call
site equations are derived. Non-directional object-family argument provenance
remains an input; see {bpref "provenance-closure"}[].
:::

:::theorem "return-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome.admit_return_of_compiler") (autoDeps := true)
Return admission is derived at cost zero from the validated outcome and its
use-site provenance. A genuinely non-directional object-family return still
requires the precise producer origin.
:::

:::definition "lazy-miss-boundary" (parent := "compiler") (lean := "FirTalos.Concrete.ConcreteStructuredLazyMissBackendCoverageAt") (autoDeps := true)
The present lazy-miss coverage boundary requires an internal supported
initializer and excludes {name Fir.Wasm.AbiKind.object}`object` and {name Fir.Wasm.AbiKind.tobject}`tobject` result kinds. This is a description
of the current restriction, not evidence that all supported source misses
satisfy it. General heap-result closure is {bpref "heap-miss-closure"}[].
:::

:::theorem "lazy-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome.admit_lazy_of_compiler") (autoDeps := true)
The runtime lookup chooses hit or miss. Validation constructs exact lazy-call
admission, conditional on the miss-only backend coverage boundary. Cache hits
need no such miss evidence. The {name Fir.Wasm.AbiKind.object}`object`/{name Fir.Wasm.AbiKind.tobject}`tobject` exclusions remain visible in
{bpref "lazy-miss-boundary"}[].
:::

:::theorem "lazy-hit-admission" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredValidatedCodeOutcome.admit_lazyHit_of_compiler") (autoDeps := true)
For an actual cache hit, the validated outcome constructs exact zero-cost
admission. The runtime lookup supplies the hit; the compiler supplies the call,
cache environment and result lanes. No miss-coverage premise is required.
This is audit row 6, including supported object-family cached results.
:::

# Constructing and publishing a fresh heap result

:::theorem "construction-entry" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredLazyCallReadyFocus.enterRegion") (autoDeps := true)
Actual lazy-miss entry establishes an active construction region at the
callee's entry cutoff. The original resource scope is retained throughout
construction. This node records the region-entry result. Accepted W6
`f6850d79f` additionally supplies `ConcreteStructuredFreshLazyFrame` retaining the
validated caller and generated continuation; that reviewed result is described
in the heap/caller chapter. General intermediate-state admission remains open.
:::

:::theorem "construction-return" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredRegionCodeCore.advance_return") (autoDeps := true)
An active construction region, aligned locals, returned heap lookup and fresh
root produce the exact source return, two target instructions, and a fresh
yield relation. Root freshness remains a hypothesis; ABI representation and
the execution path are derived.
:::

:::theorem "publication" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredFreshYieldCore.publishAtRoot") (uses := "rooted-execution-relation") (autoDeps := true)
Fresh yield evidence and the saved caller/publication premises reconnect cache
publication with the rooted global relation. This is an executable local
consumer of construction evidence. The general heap-miss dispatcher does not
yet derive all of its inputs automatically.
:::

# What the current endpoints establish

:::theorem "rooted-step-matching" (parent := "execution") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.advance_of_step") (uses := "rooted-execution-relation, admission-interface, address-space") (autoDeps := false)
Let $`M` be the fixed compiled package. Assume uniform current-step admission
and the separate address-space law. A successful source step from related
states has a finite target match:

$$`\begin{aligned}
&\FirRooted{A}{w}(\sigma,\tau)\ \land\ \sigma\FirSourceStep\sigma'\\
&\quad\Longrightarrow\exists m,\tau',w',\quad
\tau\FirTargetSteps{M}{m}\tau'\ \land\ \FirRooted{A}{w'}(\sigma',\tau').
\end{aligned}`

The theorem also gives $`m=0\Longrightarrow\kappa(\sigma')<\kappa(\sigma)`,
where $`\kappa` is the natural-valued source control rank. Ordinary code uses
the two supplied laws; staged-call, bind and return cases use their retained
validated evidence. This matches one step and preserves the root index; the
{ref "w6-proof-mechanism"}[finite execution argument] explains its composition.
:::

:::theorem "rooted-steps" (parent := "execution") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteSupportedExport.rootedExecSteps_of_currentStepAdmission") (uses := "rooted-execution-relation") (autoDeps := true)
Each finite successful source path from a related entry with cache alignment
has a matching finite target path when uniform
current-step admission and address-space safety are supplied. The
proof concatenates the operation segments and preserves the rooted relation,
including the original export ABI, world and ordered trace, along the path.

:::

:::proof "rooted-steps" (uses := "rooted-step-matching")
Induction on the finite source path concatenates the matching target segments.
:::

:::theorem "rooted-terminal-extraction" (parent := "execution") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.terminalYield_of_control") (uses := "rooted-execution-relation, concrete-value-relation") (autoDeps := false)
Suppose $`\FirRooted{A}{w}(\sigma,\tau)`, the source control has yielded $`v`,
and its source frame stack is empty. The theorem extracts a target yield focus
representing $`v` at the original ABI $`A`, under the same endpoint witness
$`w`, together with a supported target frame stack.

Target-only case labels may remain. Extraction identifies the terminal value
and the supported continuation; structured-return adequacy then handles those
labels and establishes executable return. No empty-target-stack premise is
needed.
:::

:::theorem "conditional-return" (parent := "execution") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.ConcreteSupportedExport.terminatesWith_of_rootedExecEvaluates") (autoDeps := true)
A finite successful source evaluation yields an actual executable return of
the selected compiled export. The represented result uses the export's original
ABI and reproduces the source observation. The proof obtains the target path
from rooted simulation, then uses terminal extraction and adequacy. Uniform
current-step admission, address-space safety and the entry/cache/arity
conditions remain its premises.

:::

:::proof "conditional-return" (uses := "rooted-steps, rooted-terminal-extraction")
The finite-prefix argument supplies related endpoint states. Terminal
extraction identifies the result at the root ABI, and structured-return
adequacy turns the target path and supported frames into executable return.
:::

:::theorem "conditional-fault" (parent := "execution") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.ConcreteSupportedExport.faultCorrectOfSimulation") (autoDeps := true)
A syntax-directed concrete fault simulation gives source evaluation to the
specified fault and an executable target trap satisfying the refined fault
postcondition. The simulation certificate is supplied. Constructing it for
general supported faulting executions is {bpref "fault-closure"}[].
:::

# Open proof frontier

These nodes are reviewed descriptions of missing results, with proposed
mathematical dependencies. They have no associated completed declaration.
Their exact contribution statements still need W6 review; a graph status of
"ready to formalize" is not authorization to publish them as immutable tasks.
The first formal slice now has explicit Lean holes: the external specification
and admission construction. Other targets remain prose statements. Every hole
reachable from a formal target must be represented by an incomplete node and a
dependency path. This is our authoring policy; status reporting belongs to VBP.

:::theorem "provenance-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (priority := "high")
Derive the exact non-directional call-argument and return producer facts from
the compiler-supported program and the internally maintained relation. Do not
introduce a caller-supplied universal provenance invariant.
:::
:::proof "provenance-closure" (uses := "provenance-analysis, provenance-preservation")
Proposed route: identify each producer/use boundary left by the directional
refinement lemmas, preserve the smallest semantic origin fact, and feed the
existing admission consumers {bpref "direct-admission"}[] and
{bpref "return-admission"}[]. These consumer links are not proof dependencies.
The precise statement is pending owner review. The current implementation has
already factored this into a canonical precise-local row, coverage of the
non-refining uses, and semantic preservation. Precise callee entry is supplied
by {name FirTalos.Concrete.SemanticValuesAtAbi.semanticEnv_of_bindParams}`SemanticValuesAtAbi.semanticEnv_of_bindParams`. The {ref "provenance-design"}[provenance chapter] documents proposed
construction and preservation transfers through ordinary producers, projections
and joins; their final maintained interface and proofs remain open. A fixed compiler-produced analysis or an equivalent checked-program
property are design alternatives; a caller-selected invariant is not closure.
The {ref "provenance-design"}[provenance chapter] records the exact static and
semantic interfaces and why both parts are needed. These are proposed proof
dependencies; no fixed global analysis interface has been chosen yet.
:::

:::theorem "provenance-analysis" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (uses := "call-provenance-coverage, return-provenance-coverage")
Construct a canonical precise-local analysis from the checked program and show
that its selected rows cover non-refining argument and return uses. Review
transfer and join rules, and whether existing support validation suffices or
needs an equivalent fixed representation-safety check. The intended output is
the coverage predicates already consumed by the call/return interfaces, not
a client-supplied map. This proposed static obligation has no formal signature yet.
:::
:::proof "provenance-analysis"
Inventory producer shapes and their projection/join transfers, choose a
deterministic analysis or checked-program property, and connect its rows to
the exact residual call and return sites. Define the interface jointly with
{bpref "provenance-preservation"}[]; the design relationship is not a circular
mathematical dependency. Statement review must identify any change to which
programs the endpoint covers.
:::

:::theorem "provenance-preservation" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (uses := "precise-local-semantics")
Establish and preserve the semantic truth of the chosen precise-local rows
through execution, including producer binding, projections, joins and the
relevant call/return boundaries. The rows must agree with the static coverage
argument. A precise entry row alone does not supply preservation for all future
states. The maintained relation and exact theorem signature remain under review.
:::
:::proof "provenance-preservation" (uses := "precise-call-entry")
Reuse the checked parameter-binding law at entries with typed arguments and
the existing {name FirTalos.Concrete.SemanticEnvAtLocalKinds.publishResult}`SemanticEnvAtLocalKinds.publishResult` and physical-result laws
at supported bindings. Identify the producer facts and join transport still
needed by each rule. Ordinary validator-local typing is already a projection
of the live relation; do not count it as the missing stronger analysis invariant.
:::

:::theorem "direct-let-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review")
At a guarded, validated direct-let step, derive {name FirTalos.Concrete.ReuseBudgetedDirectSupported}`ReuseBudgetedDirectSupported`
and the exact {name FirTalos.Concrete.directLetAllocationCost}`directLetAllocationCost` from the compiler facts and the
internally maintained producer/reuse evidence. Projection and unbox alignment,
and reuse provenance, must be derived rather than assumed from Boolean
validation. Address-space headroom remains a separate execution condition.
This is the proposed closure of audit row 2; its exact signature needs review.
:::
:::proof "direct-let-closure"
Use {name FirTalos.Concrete.ConcreteStructuredValidationFocus.let_eq}`ConcreteStructuredValidationFocus.let_eq` and
{name FirTalos.Concrete.supportedLetDeclKind?_effectiveLetValueKind}`supportedLetDeclKind?_effectiveLetValueKind` to recover the compiler boundary;
review each direct producer's semantic and reuse facts, then feed source safety
to {bpref "schema-admission-bridge"}[]. The {ref "admission-coverage"}[admission chapter] records the authored
producer-by-producer obligations. Their formal assembly is open; this proof
plan does not assert a checked reverse implication.
:::

:::theorem "closure-call-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review")
For the supported saturated-closure-call branch, reconstruct
{name FirTalos.Concrete.SaturatedClosureCallSite}`SaturatedClosureCallSite` and {name FirTalos.Concrete.SaturatedClosureCallResolution}`SaturatedClosureCallResolution` from the
validated state and source step. In particular, derive {name FirTalos.Concrete.SaturatedClosureCallResolution.closedIngressTarget}`closedIngressTarget`:
the resolved source declaration belongs to the compiler-selected candidate
table. State and preserve the precise closure-origin conditions internally;
do not supply a per-program reachability certificate. Capture-retention
capacity remains in finite-runtime safety. This is audit row 5.
:::
:::proof "closure-call-closure"
Separate compiler/evaluation equations from heap closure resolution and
candidate membership. The existing staged-call simulation consumes those
facts. Its membership field describes closed ingress (initial transferred
data, source closure allocation and host behavior); which conditions the
selected endpoint already enforces and which require statement revision still
need review. The resulting source safety feeds {bpref "schema-admission-bridge"}[].
:::

:::theorem "object-field-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review")
For validated object-field mutations, derive and preserve the source schema
slot facts: {name FirTalos.Concrete.ConstructorSchema.ObjectFieldFVarTyped}`schema.ObjectFieldFVarTyped` for an FVar write and
{name FirTalos.Concrete.ConstructorSchema.ObjectFieldKindAt}`schema.ObjectFieldKindAt` at {name Fir.Wasm.AbiKind.erased}`.erased` for an erased write. These are audit rows
17 and 18. The same active schema and refinement witness must agree; heap
location or carrier compatibility alone cannot establish the slot kind.
:::
:::proof "object-field-closure"
Track constructor allocation, reuse and mutation so the current source slot
has the required kind. {name FirTalos.Concrete.ConcreteObjectFieldKindAlignedAt.of_schema}`ConcreteObjectFieldKindAlignedAt.of_schema` converts
that evidence to descriptor alignment once witness agreement is available;
{bpref "schema-admission-bridge"}[] consumes it. The producer/preservation
statement remains under review, including its role in the maintained relation.
:::

:::theorem "scalar-field-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review")
Derive {name FirTalos.Concrete.ConcreteScalarFieldMutationTyped}`ConcreteScalarFieldMutationTyped` for a validated packed-scalar field
write from compiler-produced layout and its semantic preservation. Validation
fixes the scalar lane; it does not supply packed coordinates, extent or
non-overlap. This is audit row 20; its source-schema interface needs review.
:::
:::proof "scalar-field-closure"
Recover the producer's packed layout and preserve it through the permitted
updates. Supply the resulting typing evidence to
{name FirTalos.Concrete.ConcreteStructuredAlignedValidationState.admit_sset_of_step}`ConcreteStructuredAlignedValidationState.admit_sset_of_step`, which already
constructs zero-cost admission. This is distinct from the USize write in row
19, whose successful step and validated lanes suffice.
:::

:::theorem "heap-miss-closure" (parent := "frontier") (owner := "w6") (tags := "open, active-design, statement-review") (priority := "high")
Extend the internally maintained validated machine relation so supported heap
initializer misses carry construction evidence through intermediate states,
suspended callers, return, publication and bind. Derive admission for those
misses without excluding {name Fir.Wasm.AbiKind.object}`object`/{name Fir.Wasm.AbiKind.tobject}`tobject` results by assumption.

This is an evolving informal closure claim. The next contribution can refine
its maintained relation and result classification, then propose a formalization.
The {ref "heap-caller-invariant"}[heap/caller account] supplies the fresh,
persistent and ownership-preserving alternatives. Retain the saved caller,
outer cutoff, entry/runtime, external and finite-resource premises, and identify
the actual central admission consumer. The current
{bpref "lazy-miss-boundary"}[] restriction and conditional
{bpref "lazy-admission"}[] remain until closure supplies their required coverage.
:::
:::proof "heap-miss-closure" (uses := "construction-entry, construction-return, publication")
Compose fixed-entry construction with the accepted fresh saved validated caller
companion (`ConcreteStructuredFreshLazyFrame`, W6 `f6850d79f`). Preserve this companion
through the general intermediate-state dispatcher, classify persistent-result
alternatives and derive the actual central consumer inputs. Local entry,
construction and publication paths are ingredients; the general admission
assembly remains open. The saved fresh companion itself is no longer a
missing mathematical component in the reviewed accepted source.
:::

:::theorem "external-realization" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (priority := "high") (uses := "external-spec")
For a named intended external implementation, prove its successful responses
satisfy the external specification and that it succeeds on an explicitly stated
valid-request domain. The domain describes request semantics, including arity,
metadata, heap arguments and relevant resource preconditions. It must not be
defined by successful implementation calls or by compiler admission. Specify
which workload requests are covered. This is a proposed adequacy obligation;
its implementation choice and exact formal statement are still under review.
:::
:::proof "external-realization" (uses := "nat-add-realization")
The Nat-addition handler has a checked realization. Continue with the executable
validation handlers as evidence, resolve the Int
representation mismatch, then establish response correctness and availability
for each selected family and assemble the reviewed global specification.
This authored edge records the partial implementation plan; it is not a claim
that the global realization is proved. A rejecting implementation is not coverage evidence.
This result supports specification review; it is not an additional premise of
{bpref "validated-return"}[] and does not prove resident implementation linking.
:::

:::theorem "external-admission" (parent := "frontier") (owner := "w6") (tags := "open, active-design") (priority := "high") (uses := "external-spec")
Derive external current-step admission and exact allocation cost from a supported
function, the recursively validated current outcome, a successful source step,
and the reviewed primitive response contract. Reconstruct compiler facts and
argument provenance internally. The present pure admission has only eleven
names and heap-only Int results; general supported externals and external
initializer misses require coverage work. The precise statement and any
necessary internal relation revisions remain open.
:::
:::proof "external-admission" (uses := "nat-add-site") (uses_intent := "auxiliary")
Use the Nat validation/admission slice as an auxiliary construction trial;
reusing its compiler facts for arbitrary contracted externals remains work.
Extract response semantics from the successful call and the implementation
contract; reconstruct the operation family, argument compilation/signature,
result ABI and exact cost required by the admission constructors. Their current
canonical-response equations are obligations to reconcile with implementations,
not a definition of the external semantics. Prove supported-call coverage rather
than making calls outside the current family impossible by specification.
:::

:::theorem "nat-add-site" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (priority := "high")
For a selected supported Nat-addition call and recursively validated current
outcome, reconstruct the production external call shape, decoded natural
arguments and {name Fir.Wasm.AbiKind.tobject}`tobject` result ABI, then obtain natural-result admission by
applying {bpref "nat-add-admission"}[].
Resolve its parameter/argument ABI-row equality requirement: the general call
shape supplies directional refinement, which does not imply equality.
Derive equality for an explicitly reviewed slice, or coordinate generalizing
the production admission consumer. Do not claim all supported calls are covered
by adding equality as an unexplained global precondition. The exact construction
statement still needs review; no caller-supplied future target path is permitted.
:::
:::proof "nat-add-site" (uses := "nat-add-admission")
Use the current-outcome validator and source step to recover the compiler call
equations; obtain natural decoding from the arguments and the maintained source
relation. Once these inputs are constructed, apply the checked admission
consumer at the exact natural-result allocation cost. This authored proof plan
does not establish the still-unwritten construction.
:::

:::theorem "admission-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (priority := "high") (lean := "FirBlueprint.Targets.admission_of_validation") (autoDeps := true)
Construct the current-step admission law from production validation and the
internal semantic relation for every successful guarded source step. Retain
finite runtime and external execution contracts explicitly. The associated
Lean theorem is admitted. Its type supplies the admission binder needed by
{bpref "conditional-return"}[], but the draft needs mathematical review as
schema provenance and heap-miss coverage evolve.
:::
:::proof "admission-closure" (uses := "case-admission, schema-admission-bridge, direct-admission, return-admission, lazy-admission, lazy-hit-admission, provenance-closure, heap-miss-closure, external-admission, direct-let-closure, closure-call-closure, object-field-closure, scalar-field-closure")
Assemble the 20 branches mapped in the {ref "admission-coverage"}[Admission coverage chapter]. The authored
plan now names direct-let, closure-call and field obligations as well as external,
call/return and cache work. The schema bridge supplies the existing dispatch.
Every audit row has an editorial mapping; that does not establish an exhaustive
kernel-checked decomposition or preservation of the needed invariant across
branches. Precise statements and maintained-relation design remain work.
:::

:::theorem "validated-return" (parent := "execution") (owner := "w6") (tags := "statement-review") (priority := "high") (uses := "successful-export-property") (lean := "FirBlueprint.Targets.return_of_validation") (autoDeps := true)
The general target for {bpref "successful-export-property"}[], with compiler admission supplied internally by
{bpref "admission-closure"}[]. This has a checked composition proof and incomplete
dependencies. It retains primitive external semantics, finite-runtime safety,
address-space safety, cache alignment, arity and the entry runtime relation.
Its observation-facing conclusion preserves the source observation and the
export-selected ABI; its proof constructs the result runtime from source evaluation.
The incomplete {bpref "external-spec"}[] makes this a provisional specification;
local formalization does not mean the compiler theorem is complete.
At accepted VBP `19451b009`, this node's green/local-proof status and the code
panel's “complete” badge do not certify dependency closure:
{bpref "external-spec"}[] and {bpref "admission-closure"}[] remain open.
The {ref "frontier-cases"}[frontier acceptance brief] explains the work this
selected goal should expose and the expected transitions when its prerequisites change.
:::

:::theorem "fault-closure" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (uses := "fault-post")
For a supported source execution ending in a semantic fault, derive the
corresponding executable target fault under explicit runtime/resource
contracts, without a client-supplied fault-simulation certificate. The target
must satisfy {bpref "fault-post"}[] for that exact source fault/runtime;
an unrelated ABI, memory, global or native trap is not corresponding evidence.
:::
:::proof "fault-closure" (uses := "conditional-fault")
Derive terminal fault leaves from validated code and the maintained relation,
then transport them through successful call, case, lazy and effect prefixes at
the evolving refinement witness. Review source/concrete external-failure
agreement: the successful-response external specification constrains no
`.error` result, while the concrete external-failure leaf needs the matching
installed call equation. The {ref "external-domains"}[external-domain account]
and {ref "fault-safety"}[fault/safety account] identify these retained contracts
and fault coverage boundaries.

Two interfaces remain possible: extend structured control/outcomes with
trap-aware paths and adequacy, or construct the existing fault simulation/code
weakest-precondition evidence internally and use its trap/export lifting.
The proved certificate-based {bpref "conditional-fault"}[] is the current
consumer. Either route must retain the same refined fault postcondition and
derive executable trap adequacy. The operation audit supplies an inventory;
return-only closure does not construct this general fault argument.
:::

:::theorem "closed-export" (parent := "frontier") (owner := "w6") (tags := "open") (priority := "high") (uses := "return-post, fault-post, prefix-contract, address-space")
A compiler-produced supported export has the broader property
$`P_{\mathrm{closed}}`: every finite source prefix has matching world and ordered
external observations; successful terminal evaluations satisfy
{bpref "return-post"}[] at the selected ABI; source semantic faults yield
executable traps satisfying {bpref "fault-post"}[]. Compiler-owned admission is
derived internally. Entry, external-runtime and finite-resource conditions
remain explicit. No caller-chosen future path or program simulation certificate
is accepted. Target-only failure exclusion (T4S) is a distinct claim to state
and justify when required by a selected endpoint.
:::
:::proof "closed-export" (uses := "supported-export, rooted-entry, rooted-steps, validated-return, fault-closure")
Supply compiler-derived admission to the existing rooted prefix/return chain
and compose the general fault counterpart, including external failure contracts
and trap adequacy. The {ref "frontier-cases"}[selected-goal account] identifies
these extra obligations beyond the successful-return property. This is the
pilot's top-level contracted-export target; resident linking is a further boundary.
:::

:::theorem "resident-linking" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (uses := "return-post, fault-post")
Replace the contracted resident operations used by the compiler theorem with
execution of their installed implementations, retaining explicit genuinely
external operations and finite resources. State the resulting linked execution
boundary precisely before claiming a theorem about encoded artifact bytes.
:::
:::proof "resident-linking" (uses := "closed-export")
Compose helper implementation refinements and installation/import closure
with the contracted compiler theorem. Generation tests and linked artifact
tests supply separate evidence; they do not discharge the semantic proof.
:::

# Source and graph reading boundaries
%%%
tag := "w6-source-boundary"
%%%

This chapter's original declaration narrative was reviewed at FIR `81bb0e2ab`.
The current package uses accepted VBP `19451b009` and Lean 4.34.1; its Lean
associations are checked against the current FIR checkout and official
worktree-local Talos overlay. Historical PR475 candidate evaluations retain
their separate revisions in the {ref "evaluation-findings"}[evaluation cases].
The accepted-main text review on 2026-10-05 uses FIR
`8f4222cb2`, including W6 checkpoint `f6850d79f`. Newer accepted results are
explained in the {ref "heap-caller-invariant"}[maintained heap/caller argument]
as reviewed source evidence. A source citation does not itself add a Lean
association. In particular, construction-step preservation and the
fresh saved validated caller have advanced; general heap-miss admission and
resident linking remain open. An absent association here is an artifact
boundary, not evidence that the accepted proof is missing.

The goal is to make assumptions and useful remaining contributions visible.
The {ref "documentation-migration"}[source and evidence boundaries] identify
the maintained argument and its production source/audit authorities.

*Reading the graph.* An arrow is a mathematical dependency. Existing nodes
use Lean dependency inference; open nodes have explicitly authored proof plans.
A proved conditional result and a theorem eliminating its premise are separate
nodes. The Blueprint is the specification and obligation map for these targets;
its draft statements and admitted proofs evolve together. Tags describe our editorial classification; they do not change
Blueprint's computed status. Resource contracts remain explicit execution
conditions. Integration and axiom evidence are discussed in the evaluation
chapter, separately from the graph's formalization colors.
