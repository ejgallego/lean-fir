import Verso
import VersoManual
import VersoBlueprint
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

#doc (Manual) "W6: from validated compiler output to execution" =>

The goal is a compiler guarantee: when a supported source program returns,
its compiled export executes and returns a related value at the export's
selected ABI, preserving the source observation. Some conditional ingredients
are proved; the whole-program instance and the general compiler theorem still
have open obligations. The statements below distinguish these claims before
explaining their proof.

Read the {ref "w6-theorem-menu"}[theorem menu], then the
{ref "w6-machines"}[two machines], their
{ref "w6-rooted-relation"}[rooted relation] and the
{ref "w6-proof-mechanism"}[step-to-return argument]. The later node catalog
expands the invariant and operation obligations in that argument. The
{ref "retained-example-boundary"}[lean-zip account] supplies the concrete source
and initializer theorems; {ref "development-roadmap"}[the roadmap] explains
how fixed-program proofs can lead to general correctness.

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

# Guarantees and target theorems
%%%
tag := "w6-theorem-menu"
%%%

The first goal is successful-return correctness, written
$`P_{\mathrm{success}}(p)`. Fixing $`p` fixes a program, not an input: a program
instance must cover every related admitted entry and input. The source
application theorem and the initializer proofs below are already useful
semantic examples, but have different conclusions from the whole-export goal.

:::table +header
*
  * Claim
  * Guarantee
  * Status and retained premises
*
  * Source stored-compression roundtrip, $`Q_{\mathrm{stored}}`
  * Decoding the compressed source bytes returns the original arbitrary byte array, with an explicit decoder output-size bound.
  * Reviewed theorem source at the pinned lean-zip revision; no fresh external build or Blueprint association. See the {ref "retained-example-boundary"}[source statement].
*
  * Captured initializer family, $`Q_{\mathrm{init}}`
  * A derived target path matches thirteen source steps and fresh-region publication; the fourteen-step companion restores the rooted validated caller.
  * Genuine local semantic proofs cited as reviewed source evidence. Primitive/handler laws, related callers, cold cache and finite headroom remain inputs; neither theorem proves the whole export. The {ref "worked-retained-initializer"}[worked proof] follows the actual states and lemma composition.
*
  * {bpref "rooted-steps"}[] and {bpref "conditional-return"}[]
  * Every finite source prefix has a matching target path; a successful source evaluation yields an actual export return with the selected ABI and exact observation.
  * Proved conditional theorems. Uniform compiler admission, address-space safety and the existing entry/cache/arity conditions are supplied.
*
  * {bpref "stored-export-instance"}[]
  * $`P_{\mathrm{success}}(p_{\mathrm{stored}})` for the selected captured program, universally over its allowed inputs.
  * Open. First construct this program's semantic facts and use the proved conditional consumer; the unfinished general theorem is not a prerequisite.
*
  * {bpref "validated-return"}[]
  * Eventually, $`\forall p,\ H(p)\Longrightarrow P_{\mathrm{success}}(p)` for supported compiled exports.
  * Local composition is checked, but the external specification and admission construction are explicit holes. $`H` is static supported-export/compilation evidence; compiler-owned admission must be derived.
*
  * Faults, closed exports and resident linking
  * {bpref "conditional-fault"}[] proves a refined executable trap from a supplied certificate. {bpref "closed-export"}[] would combine prefixes, returns and faults; {bpref "resident-linking"}[] adds installed implementations.
  * The certificate consumer is proved; general fault construction and both extensions are open. Linking and released-byte correctness require their own bridges.
:::

## The successful-export property

:::definition "return-post" (parent := "contracts") (lean := "FirTalos.Concrete.RefinedReturnPost") (autoDeps := true)
A successful target return represents the exact source value at the specified
ABI kind. One refinement witness relates the live heap, globals, world and
ordered external trace, with no target runtime failure and the precise return
stack. The ABI is chosen by the export; existentially choosing a convenient
kind would weaken the contract.
:::

:::definition "successful-export-property" (parent := "contracts") (uses := "return-post")
Fix an impure program, its selected source/export entry, compiler-produced
contracted module, adapted module, resolved hosts and export-selected result
ABI. Write $`P_{\mathrm{success}}(p)` for the following property, using the
observation-facing conclusion of {bpref "conditional-return"}[]. For every
related source entry/runtime/environment, concrete initial store and parameter
row satisfying the retained external-runtime and finite-resource contracts,
and every successful finite source evaluation with observation $`o` and
returned value $`v`, there exists a source result runtime $`r` such that

$$`\begin{aligned}
&o=\operatorname{ReturnedObservation}(r,v)\\
&\land\operatorname{ConcreteExportTerminatesWith}\\
&\qquad\bigl(\operatorname{RefinedReturnPost}(r,v,\mathrm{selectedABI},[])\bigr).
\end{aligned}`

The omitted export arguments are those fixed by the compiled module and
invocation. The empty list is the exported invocation's caller operand tail.
One terminal refinement witness relates the result representation and the
complete source/concrete runtime, including heap, globals, world and ordered
trace; the witness can evolve from entry. Cache alignment, parameter count and
the reviewed entry cache/reuse/closure ABI relation remain explicit entry
conditions. Current-step admission, reached-state provenance and heap-miss
preservation are compiler obligations to construct internally.

This fixes a partial-correctness property over all related admitted inputs;
it claims target termination whenever the finite source run returns. In the
existing proof, $`r` is constructed from that source execution's final runtime.
The public observation equality itself records value, heap, world and trace,
and does not determine globals or the location cursor. This rough definition
uses the exact wrapper conclusion at both instance and general levels; the
stronger path-resolved internal theorem supplies proof evidence.
:::

## First whole-program instance

:::theorem "stored-export-instance" (parent := "execution") (owner := "w6") (tags := "open, statement-review") (priority := "high") (uses := "successful-export-property")
For the actual captured final impure program with selected entry
`Zip.Wasm.compressStored`, prove $`P_{\mathrm{success}}(p_{\mathrm{stored}})`
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

## Eventual general theorem

The intended general statement is
$`\forall p,\ H(p)\Longrightarrow P_{\mathrm{success}}(p)`.
Here $`H(p)` is supported-export and static compilation, adaptation and
host-resolution evidence. The independent external/resource/entry contracts
still scope the invocations quantified in $`P_{\mathrm{success}}`;
compiler-owned admission, provenance and heap-miss preservation must be derived.
{bpref "validated-return"}[] is the checked local assembly for this target,
with unfinished {bpref "external-spec"}[] and {bpref "admission-closure"}[].
It is not a completed compiler theorem. The later catalog retains its formal
attachment and explicit native-status caveat.

# The two machines
%%%
tag := "w6-machines"
%%%

The source is FIR's final impure LCNF machine. The target is the structured
machine for the Wasm subset emitted by the adapter, executing ordinary
instructions and imported calls through Talos. It runs the contracted module
with resolved hosts; a theorem about resident-linked or released bytes is a
later boundary. Neither machine is native execution of the original Lean source.

:::table +header
*
  * Machine
  * Configuration and transition
  * Observable boundary
*
  * Source
  * {name Fir.LeanIR.Impure.MachineState}`MachineState` contains the program, current code or yielded/call control, environment, joins, continuation frames and runtime. {name Fir.LeanIR.Impure.executeStep}`executeStep` either advances, returns an observation or reports a semantic fault; {name Fir.LeanIR.Impure.ExecSteps}`ExecSteps` records a finite execution.
  * A return observation contains value, heap, world and ordered external trace. Globals and the location cursor belong to runtime state but are absent from this public observation.
*
  * Concrete target
  * {name FirTalos.Correctness.StructuredWasmState}`StructuredWasmState` contains the Talos store, running/branch/return/halted control and block/loop/call frames. {name FirTalos.Correctness.StructuredWasmStep}`StructuredWasmStep` exposes the emitted control flow while Talos executes atomic instructions and imported calls.
  * Physical values and memory must represent the source value/runtime. Finite structured paths are lifted to actual executable export termination at the fixed selected ABI.
:::

The source and target need not take equal numbers of steps. Interpreter fuel
is a bound on a runner, not a semantic fault or a shared clock. The return
property assumes a finite successful source evaluation and derives an adequate
target execution; it does not prove source termination for arbitrary inputs.

# The relation carried through execution
%%%
tag := "w6-rooted-relation"
%%%

Fix the program, compiled/adapted modules, resolved hosts, external
implementation and original export ABI $`A`. For this explanation only, write

$$`R_A(s,t)\;\equiv\;\exists w,\ \operatorname{Rooted}_A(w,s,t).`

Here $`\operatorname{Rooted}` abbreviates the existing
{name FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt}`ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt`
with those fixed arguments. This is expository notation, not a new Lean
invariant. It is the witness-hiding relation already used by
{name FirTalos.Concrete.ConcreteStructuredCompilerCurrentStepAdmission.toRootedTraceSimulation}`toRootedTraceSimulation`.

The relation records the validated current control and generated continuation,
precise value/ABI facts, related runtime and caches, and saved caller/root
information. The current callee's ABI may differ from $`A`; the saved rooted
facts retain the original export ABI until the final return. One witness $`w`
relates values and the live heap, globals, world and ordered trace at that
state. The next state may require a different witness. The argument does not
fix the entry witness forever or assume an arbitrary monotone extension law.

The entry contract relates the encoded parameters and source environment,
heap/runtime, reuse capacities and caches. The compiler constructs the rooted
control relation from that contract; callers do not supply a new whole-program
simulation or a future target path. The {ref "heap-caller-invariant"}[heap/caller
account] explains the detailed saved-frame and construction-region components.

# From one step to an executable return
%%%
tag := "w6-proof-mechanism"
%%%

The conditional proof has four stages. They explain what the invariant must
retain and where the missing compiler facts are consumed.

## 1. Establish the entry relation

Supported compilation fixes the entry/export, adapted function, hosts and
selected result kind. Cache alignment and the existing runtime/parameter
contract give $`R_A(s_0,t_0)` through the checked {bpref "rooted-entry"}[].

## 2. Match a successful source step

The proved
{name FirTalos.Concrete.ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.advance_of_step}`advance_of_step`
has the following schematic form under uniform current-step admission and
address-space safety. The successful source transition is an explicit premise:

$$`\begin{aligned}
&R_A(s,t)\land(s\leadsto s')\\
&\quad\Longrightarrow\exists m,t',\quad
 t\longrightarrow^{m}t'\ \land\ R_A(s',t')\\
&\qquad\land\bigl(m=0\Longrightarrow
\operatorname{rank}(s')<\operatorname{rank}(s)\bigr).
\end{aligned}`

The guards are real hypotheses, not conclusions of validator acceptance.
The rank is {name FirTalos.Concrete.compilerStructuredControlRank}`compilerStructuredControlRank`.
A source administrative step may take zero target steps; strict rank decrease
prevents an infinite sequence of zero-target-step matches. It gives no uniform
bound on finite stuttering bursts between positive target paths. Other steps
may require several target instructions. This theorem handles successful source
advancement, not the general fault case.

## 3. Compose a finite path

Induction concatenates the derived target paths and carries the relation at
each new witness, with the same original ABI. Its observation component gives
world and ordered-trace agreement at every finite prefix. No new entry
invariant is requested at intermediate states. The proved conditional
consumer is {bpref "rooted-steps"}[].

## 4. Extract the terminal value and use adequacy

A successful source endpoint has a yielded value and an empty source
continuation. The rooted relation identifies its representation at $`A`.
Target-only administrative labels may still need unwinding: terminal extraction
and executable adequacy derive the remaining target path and exported return.
The public conclusion is the observation-facing postcondition of
$`P_{\mathrm{success}}`, with the observation and {bpref "return-post"}[]
already stated above. This is the checked conclusion of
{bpref "conditional-return"}[].

The internal path theorem uses the actual source endpoint runtime. The public
wrapper constructs that runtime as its existential witness; equality of the
public observations alone does not identify globals or the location cursor.
Thus the path theorem is proof evidence for the wrapper, not a reason to
silently strengthen the stated property.

Faults require a separate terminal argument. The existing certificate
consumer {bpref "conditional-fault"}[] is proved, while {bpref "fault-closure"}[]
must construct its evidence and executable trap correspondence internally.

# Why these invariants are needed
%%%
tag := "w6-invariant-design"
%%%

The proof mechanism determines the invariant questions. To invoke the guarded
step theorem at each intermediate state, validated code must retain semantic
facts that static validation alone cannot recover.

:::table +header
*
  * Preservation question
  * Required information and destination
*
  * Does each value have the representation its next use expects?
  * Precise producer/use-site ABI facts, including non-directional object-family cases: {bpref "provenance-closure"}[] and the {ref "provenance-design"}[provenance account].
*
  * Can an allocation or mutation safely advance the related heap?
  * Live roots, reuse/capacity facts and finite resource guards. Fresh heap results need a construction region and publication back into the saved caller: {bpref "heap-miss-closure"}[] and the {ref "heap-caller-invariant"}[heap/caller account].
*
  * Does a call, cache lookup or external operation preserve the continuation and effects?
  * Exact argument/result ABI rows, saved frames/cache state and primitive/handler laws: {bpref "external-spec"}[], {bpref "external-admission"}[] and the {ref "admission-coverage"}[operation map].
:::

For a first program instance, prove the semantic facts from its actual code
and checked blocks, then discharge the conditional consumer's full admission
interface. These instance proofs can expose the right general invariant.
Later, {bpref "admission-closure"}[] must construct admission uniformly from
supported compilation and the maintained relation. That future result cannot
be a premise of the independent instance proof used to guide it.

The graph gives the mathematical dependencies among these obligations;
{bpref "closed-export"}[] and {bpref "resident-linking"}[] identify extensions
of the successful-return result. Prose navigation links describe the future
specialization route without making it a current proof edge. The node catalog
below expands the branches without changing the theorem menu's status claims.

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
For every supported function, recursively validated current outcome and
successful source step, recover current-node admission and its exact allocation
cost. This is a quantified compiler law. Having defined this structure does
not construct an inhabitant for every supported program.
:::

:::definition "address-space" (parent := "contracts") (lean := "FirTalos.Concrete.ConcreteStructuredCurrentStepAddressSpaceSafety") (autoDeps := true)
Allocation-producing steps have sufficient wasm32 address space at their
actual frame budget. This execution condition is deliberately retained. It is
not an open compiler lemma whose eventual proof promises unbounded memory.
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

:::theorem "rooted-entry" (parent := "compiler") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteSupportedExport.rootedPreciseCodeGlobalRoot") (autoDeps := true)
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

:::theorem "publication" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteStructuredFreshYieldCore.publishAtRoot") (autoDeps := true)
Fresh yield evidence and the saved caller/publication premises reconnect cache
publication with the rooted global relation. This is an executable local
consumer of construction evidence. The general heap-miss dispatcher does not
yet derive all of its inputs automatically.
:::

# What the current endpoints establish

:::theorem "rooted-steps" (parent := "execution") (owner := "w6") (lean := "FirTalos.Concrete.ConcreteSupportedExport.rootedExecSteps_of_currentStepAdmission") (autoDeps := true)
Given current-step admission, address-space safety and the entry contract,
every finite source execution produces a target path retaining the original
root ABI and matching prefix observations. The witness may evolve with
allocation; it is not fixed to the entry witness.
:::

:::theorem "conditional-return" (parent := "execution") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.ConcreteSupportedExport.terminatesWith_of_rootedExecEvaluates") (autoDeps := true)
Successful source evaluation yields actual export termination with the exact
source observation and result ABI. Current-step admission, address-space
safety, cache alignment, arity and the entry runtime relation remain explicit.
This theorem is proved. Closing its compiler-owned premise is the distinct
open target {bpref "admission-closure"}[].
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
