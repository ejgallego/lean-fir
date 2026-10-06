import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Proof architecture, observations and evidence boundaries" =>
%%%
tag := "proof-scope"
%%%

This chapter starts with concrete lean-zip programs and follows the
correctness property from a program instance to the general W6 theorem.
It also captures the surrounding proof, observation and implementation boundaries.
Sources were reviewed on 2026-10-05 at FIR `93c2e7ec7`, and compared read-only
with accepted main `8f4222cb2`. Several source documents describe historical
Lean 4.33 or 4.34.0-rc2 checkpoints; accepted main uses Lean 4.34.1. Their old
toolchain names, corpus counts and chronological “next” paragraphs do not define
current proof readiness. The retained-input boundary below includes the
accepted October successor; exact compiled inventories remain in their source
registries.

# From lean-zip programs to a general compiler theorem
%%%
tag := "retained-example-boundary"
%%%

The selected source function is `Zip.Wasm.compressStored : ByteArray → ByteArray`.
At the immutable lean-zip nomination `273d0d6cd9cab77c7f3489b0b0b1f6e543315d21`,
its [definition](https://github.com/kim-em/lean-zip/blob/273d0d6cd9cab77c7f3489b0b0b1f6e543315d21/Zip/Wasm/Stored.lean#L8)
calls `Zip.Spec.DeflateStoredCorrect.deflateStoredPure`. The
[source roundtrip theorem](https://github.com/kim-em/lean-zip/blob/273d0d6cd9cab77c7f3489b0b0b1f6e543315d21/Zip/Spec/DeflateStoredCorrect.lean#L751)
proves the application property $`Q_{\mathrm{stored}}`:

$$`\begin{aligned}
&\forall a,M,\quad |a|\le M\Longrightarrow\\
&\operatorname{inflateReference}(\operatorname{compressStored}(a),M)
=\operatorname{ok}(a).
\end{aligned}`

This is a theorem over arbitrary source byte arrays with the decoder's explicit
output-size bound. Its Lean 4.33 source was reviewed on 2026-10-05; no fresh
build, transitive-axiom audit or Blueprint association is claimed here.
The pinned zip-common source is `4425bab1f9522307d77e8d485bc536149ba31c36`.

FIR captures this program's actual final impure LCNF. Kernel quotation installs
[`RetainedRC2.program`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/Fir/Compiler/LCNF/retained-example/RetainedRC2.lean.in#L10),
a closed {name Fir.LeanIR.ImpureProgram}`ImpureProgram`; checked lookup/body equations identify the
real initializer. Production lowering reads back that same definition.
Constructor re-quotation and fresh-process readback establish structural capture
identity. Lean-source-to-LCNF semantic correspondence is a further bridge.
Embedded expressions remain data and unsupported metadata is rejected.
Historical oleans and diagnostic JSON remain provenance evidence; a newer
toolchain requires its recorded capture/setup identity.

There are already genuine concrete FIR semantic proofs for a block of this
captured program. Accepted W6 `f6850d79f`, reviewed at main `04ae5ccd3` on
2026-10-05, supplies
[`RetainedInitializer.rootedLet_publishesAtBind`](https://github.com/ejgallego/lean-fir/blob/f6850d79ff5a530ffa8bacbf804b6dfe95969912/integration/talos/retained-initializer/RetainedArrayCalls.lean#L1016)
and its fourteen-step resumed-caller counterpart. This family of local
conclusions, $`Q_{\mathrm{init}}`, derives source and target paths: the thirteen-step
theorem exposes fresh-region closure at publication, and the fourteen-step
theorem restores the rooted validated caller, joins and frames after binding.
External primitive laws, installed handler conformance, a related
rooted caller, cold cache and finite headroom remain explicit inputs. The
{ref "heap-caller-invariant"}[heap/caller account] gives the maintained relations
and source boundaries. These results are cited as reviewed source evidence;
the local initializer theorems are not added as Blueprint Lean associations.

The whole-export compiler property is {bpref "successful-export-property"}[],
written $`P_{\mathrm{success}}(p)`. It quantifies successful finite source runs
from every related admitted entry/input. Its exact observation-facing conclusion
is actual target termination with {bpref "return-post"}[] at the export-selected
ABI and a result runtime reproducing the source observation. The existing proof
constructs that runtime from the source execution. Observation equality alone
does not determine its globals or location cursor; the rough property preserves
the existing public wrapper at both levels.

:::table +header
*
  * Development step
  * Claim and current proof route
*
  * Define the property
  * {bpref "successful-export-property"}[] fixes the return relation, entry scope and retained execution conditions used at both levels.
*
  * Prove concrete program instances
  * {bpref "stored-export-instance"}[] is an open theorem for the captured stored-compression export over all admitted inputs. Its independent plan constructs the program's admission/preservation facts from the checked body and semantic blocks, including $`Q_{\mathrm{init}}`, then uses {bpref "conditional-return"}[].
*
  * Prove the general compiler theorem
  * {bpref "validated-return"}[] has checked composition with incomplete specification/admission dependencies. Its intended claim is $`\forall p,\ H(p)\Longrightarrow P_{\mathrm{success}}(p)`; compiler-owned admission is constructed internally.
:::

Here $`H(p)` is production supported-export and static compilation, adaptation
and host-resolution evidence. Independent external/resource/entry contracts
scope the quantified invocations in $`P_{\mathrm{success}}(p)`. Reached-state
admission, provenance and heap-miss preservation remain compiler obligations
to derive internally.

The independent instance proof can shape the maintained invariant and general
admission plan. Its current proof dependencies do not include the unfinished
general theorem. Once that theorem is proved, the same instance statement can
instead follow by specialization and discharge of its premises. Closed static
equations about the captured body, export, ABI and successful compilation may
be computational. Primitive behavior, related ByteArray entry states, finite
resource conditions and semantic preservation still need proofs or explicitly
retained execution contracts. {tactic}`cbv` can discharge only premises whose
content is computational; validator acceptance alone does not prove this property.

$`Q_{\mathrm{stored}}` and the stronger local $`Q_{\mathrm{init}}` keep their own
statements and proofs. A future released-output roundtrip would compose
$`Q_{\mathrm{stored}}` with the compiler instance, source/capture semantic
correspondence and the following implementation bridges:

:::table +header
*
  * Boundary
  * Required correspondence
*
  * Contracted compiled export
  * The selected captured program, production supported-export assembly and encoded-entry/decoded-result ByteArray refinement. The lean-zip closed-closure compiler route needs explicit correspondence with W6 lowering/adaptation wherever they differ.
*
  * Resident-linked module
  * Installed helper-to-host refinement, external availability/failure contracts and semantic link preservation; W7 implementation/signature and engine acceptance supply separate evidence.
*
  * Exact released bytes
  * Encoding and release-transform preservation for the digest-pinned artifact, followed by its execution/decoded-byte bridge.
:::

The compiler property has a successful-source-run antecedent. Totality or
coverage of every failure would require further arguments. A finite regression
input range does not restrict the universal instance statement, and stored
compression does not certify Level-1 or arbitrary DEFLATE.

# Compiler phases and pass composition
%%%
tag := "compiler-phases"
%%%

The intended chain is earlier LCNF, final impure LCNF, contracted Wasm, then
resident-linked executable Wasm. Lean's normal C emitter also consumes final
impure LCNF directly; {name Lean.IR.toIR}`Lean.IR.toIR` is a parallel metadata/interpreter/LLVM
branch, not an intermediate C-emission phase. FIR's impure interpreter defines
the semantic boundary at which backward pass proofs and forward Wasm proofs
meet.

:::table +header
*
  * LCNF phase
  * Syntax and phase invariant
*
  * Base
  * Pure syntax; polymorphism and source type structure remain.
*
  * Mono
  * Pure syntax; polymorphism has been eliminated.
*
  * Impure
  * Impure syntax; representation, mutation, ownership and runtime operations are explicit.
:::

{name Fir.LeanIR.Program}`Program` $`phase` keeps base and mono theorem inputs distinct despite their shared
purity index. {name Fir.LeanIR.CheckedProgram}`CheckedProgram` $`phase` adds the phase invariant; the AST is not
duplicated. The `Pipeline` module checks pass keys, occurrences and phase transitions
against the pinned compiler. {name Fir.LeanIR.reverseProofCampaign}`reverseProofCampaign` derives the reverse order:
final impure passes, late mono/impure, SCC/early mono, then base/frontend.
The historical exact pass list stays in `docs/lcnf-to-c.md` and
`docs/pass-correctness-history.md` as versioned compiler evidence.

For an original entry $`e`, arguments $`a` and observation $`o`, same-phase
correctness has the form

$$`e\in E\Longrightarrow
\bigl(\operatorname{Eval}(P,e,a,o)\iff\operatorname{Eval}(P',e,a,o)\bigr).`

Introduced helper declarations do not become additional source entries.
Cross-phase lowering instead relates source and target values and observations:

$$`e\in E\land R_V(a,a')\land\operatorname{Eval}(P,e,a,o)
\Longrightarrow\exists o',\ \operatorname{Eval}(P',e,a',o')\land R_O(o,o').`

Here $`R_V` is lifted pointwise over the argument row. These equations summarize
{name Fir.LeanIR.SamePhaseCorrect}`SamePhaseCorrect` and {name Fir.LeanIR.LoweringCorrect}`LoweringCorrect`; restricted entry interfaces retain
their real admissibility hypotheses. A semantic transformation kernel is one
layer. Conformance of the actual {name Lean.Compiler.LCNF.CompilerM}`CompilerM` implementation, including names,
declaration groups and environment updates, is another.

For `simpCase`, transparent recursive traversal and alpha-renaming soundness
support a whole-program semantic result. Agreement with private upstream
traversal is source-hash-guarded executable evidence, while the compiler-facing
alpha specialization retains the isolated upstream correspondence axiom.
Its removal requires an upstream equation or proof-facing API and a proof of
`UpstreamBridge`
([source](https://github.com/ejgallego/lean-fir/blob/340f4612ac622aa39d6a870528f96d6b827d97b8/Fir/LeanIR/Passes/AlphaEqvLocal.lean#L165)). The exact source boundary is
`bugs/FIR-BUG-impure-simpCase-private-proof-interface.md`.

For `elimDeadVars`, deleted allocations demand a relation over reachable heaps
with partial address renaming; retained/deleted instructions may take different
numbers of steps. The exact compiler graph and ownership ledger must construct
and preserve readiness for arbitrary checked entry states. The dated history
records the intermediate hereditary-readiness premise; the live repository
plan identifies general source-only allocation, mapped ownership and reset/reuse
interfaces as the next generalization. Finite fixture enumeration cannot
establish the arbitrary-entry endpoint.

Three semantic boundaries remain explicit: effectful nullary full applications
are conservatively excluded unless constant purity or stuttering is established;
foreign semantics must respect the heap renaming; retained reuse tokens need
reachable ownership. Their minimized evidence is respectively
`bugs/FIR-BUG-impure-elimDeadVars-nullary-fap-effects.md`,
`bugs/FIR-BUG-impure-none-external-spec-address-parametricity.md` and
`bugs/FIR-BUG-impure-elimDeadVars-reuse-token-root-gap.md`.

Finite-stuttering and observable weak simulations compose through the common
interface. The next compiler-chain test is one already-proved backward pass
composed with {bpref "closed-export"}[], after compiler-owned admission closes.
The earlier pass retains its own semantic and well-formedness conditions;
composition must not relocate W6's unfinished admission into a renamed premise.
Resident linking is the separate {bpref "resident-linking"}[] layer.

# Observations and terminal correctness
%%%
tag := "observable-contract"
%%%

The impure machine has an exhaustive relational {name Fir.LeanIR.Impure.Step}`Step` and an executable runner
over the same core transition. Runner soundness produces relational execution.
A returned value or runtime fault is source behavior; exhausted interpreter
fuel is a backend limit. The legacy evaluator remains a differential fixture,
while ordinary native Lean execution is validation's source-language oracle.

For observations $`o,o'`, {name Fir.LeanIR.Impure.ObservationRel}`ObservationRel` requires a partial address renaming
$`\rho` such that

$$`R_{\mathrm{outcome}}(\rho,o,o')\land o.\mathrm{world}=o'.\mathrm{world}
\land R_{\mathrm{trace}}(\rho,o,o')\land R_{\mathrm{heap}}(\rho,o,o').`

Trace order and argument/result values are preserved. Heap agreement is only
over roots reachable from returned values and external-event arguments/results;
unreachable garbage may differ. Outcomes cannot swap return and fault, and
address-bearing dead-object/underflow diagnostics are preserved exactly or
related through $`\rho`.
Raw heap equality would obstruct the intended allocation/reuse pass theorems.

The public {name FirTalos.Concrete.ConcreteFiniteTraceCorrect}`ConcreteFiniteTraceCorrect` interface exposes world and external
trace agreement. Its sensitivity theorem
`finiteTraceCorrect_of_terminal_prefix`
([source](https://github.com/ejgallego/lean-fir/blob/340f4612ac622aa39d6a870528f96d6b827d97b8/integration/talos/FirTalos/ConcreteObservationSensitivity.lean#L52)) shows that this alone permits a stopped
target without constraining its terminal result. This is a limit of the
interface, not a counterexample to the actual compiler relation. Finite prefixes
also remain meaningful for executions that never terminate.

{name FirTalos.Concrete.RefinedReturnPost}`RefinedReturnPost` preserves the exact source observation, represented result
at the selected root ABI, target runtime state, singleton return and restored
caller operand tail, with a clear structured failure channel. {name FirTalos.Concrete.RefinedFaultPost}`RefinedFaultPost`
relates the exact source fault to a source-classified concrete failure.
The successful-return chain is entry validation, rooted simulation, terminal
yield extraction and Talos execution adequacy. The existing conditional
{bpref "conditional-return"}[] derives its target path and sufficient target
fuel from source evaluation. Its general admission and resource inputs still
need the construction documented in {bpref "admission-closure"}[]; clients
must not supply a future target path or simulation certificate.

Deterministic Talos execution supports common-result overlap, uniqueness of
returned UInt64 values and incompatibility of success with trap for one
invocation. The pretty observation theorem retains text and ordered styling
events, so identical text with different styles remains distinguishable.
It exercises the generated facade type; it does not prove the Wasm decoder or
the facade's compilation. Terminal root-kind transport is explained at
{bpref "rooted-steps"}[]; maintained caller transport is in
{ref "heap-caller-invariant"}[the heap and caller argument].

# Source faults and target safety
%%%
tag := "fault-safety"
%%%

The fault audit separates T4 from T4S. T4 starts with a source fault and requires
an executable target trap satisfying {bpref "fault-post"}[]. Its concrete error
relation accepts source and address-related source errors. Malformed target
memory, ABI-shape failures, native Wasm traps and global failures cannot serve
as the corresponding source fault.

T4S instead excludes target-only failure for an admitted related operation:

$$`\operatorname{Related}(s,t)\land\operatorname{Admitted}(s,t)
\land\operatorname{Resources}(t)\Longrightarrow
\neg\operatorname{TargetOnlyFailure}(t).`

This is the audit's intended theorem shape. Concrete runtime/resolver
invariants must rule out malformed headers, padding, missing closure metadata
and invalid globals. Allocation additionally needs wasm32 headroom; in-place
reuse needs retained capacity. The unbounded semantic heap cannot supply these
finite-machine facts automatically.

The audited matrix covers allocation, object/USize/scalar projection and
mutation, cases/tag lookup, sharing and reference counts, deletion, boxing,
reset/reuse, partial/closure application, externals and explicit unreachable.
Exact terminal leaves exist for many runtime failures, including arbitrary
external source failure. Lookup/control errors are intended to be ruled out
by validation and reachability. The matrix is an operation inventory, not a
closed compiler-fault theorem.

Four dated discrepancy cases remain discoverable from the audit:
`bugs/FIR-BUG-wasm-none-unreachable-fault-classification.md` (unreachable and
missing alternatives collapse to an unclassified native trap),
`bugs/FIR-BUG-wasm-none-uninitialized-scalar-projection.md` (missing semantic
coordinate versus zero-filled storage),
`bugs/FIR-BUG-wasm-none-constructor-arity-fault-classification.md` (malformed
allocation classification), and
`bugs/FIR-BUG-wasm-none-reset-erased-child-release.md` (erased ownership slot).
These are historical reproducer identities; current status belongs to each
card and accepted source. The general {bpref "fault-closure"}[] also needs
trap-aware structured-machine transport and adequacy. Return-only closure
does not discharge that obligation.

# Trust and theorem-contract evidence
%%%
tag := "proof-trust"
%%%

Three questions are independent: whether a proof is kernel-checked, which
axioms its transitive compiled proof uses, and whether its public statement
preserves the intended contract. FIR's maintained source scan sees textual
axioms/placeholders; it cannot measure opaque imported/generated dependencies.
Lean's {name Lean.collectAxioms}`collectAxioms` supplies the compiled endpoint footprint.

`TrustInventory.lean` records exact axiom sets per endpoint, including removals.
Missing/non-theorem endpoints, changed sets and {name sorryAx}`sorryAx` are rejected.
Standard logical axioms are {name propext}`propext`, {name Classical.choice}`Classical.choice` and {name Quot.sound}`Quot.sound`.
The observation/trust report records the two legacy source-invariant export
endpoints with 57 generated dependencies each, a sampled UInt64 endpoint with
twenty and a literal endpoint with twenty-seven. Those are the report's dated
measurements, not a fresh October audit or acceptance of that debt. Generic
standard-only simulation/return assembly does not remove generated axioms
in its actual classifier or application instance. The authoritative current
sets live in the source inventory. The unresolved debt is tracked by
`bugs/FIR-BUG-wasm-none-endpoint-native-axiom-audit.md`.

`ConcreteExportContractTests.lean` independently states rooted evaluation/run,
fault and admission-prefix contracts. Ten same-axiom weakening mutations must
be rejected, including lost exact ABI/source-observation identity or an added
false premise. Separate kernel clients extract actual target execution,
represented results, faults, state and ordered traces. A strengthening or
changed statement also requires explicit fixture review; matching an old
axiom set does not establish theorem adequacy.

The gate forces direct elaboration of the audit after building the official
Talos overlay; stale audit oleans cannot establish acceptance. Source hashes
authenticate the pinned upstream alpha-checker input but do not prove its
correspondence axiom. The retained initializer has separate exact inventories.
Existing fixed scalar/boxing and byte-assembly debt should be removed in owner
slices; new public endpoints start with the standard-logical-axiom budget.
Blueprint presents these reports alongside completion, without maintaining a
second gate or approval database.

# Runtime generation and validation boundaries
%%%
tag := "runtime-generation-boundary"
%%%

FIR-native symbolic lowering and compiler-native C/Emscripten share final LCNF
but have different lowering, runtime, ABI, manifests and loaders. The first is
the subject of W6/W7 simulation/refinement; the second supplies executable
coverage and differential/performance evidence. Their common logical prettyM
facade does not identify the raw artifact boundaries.

For resident Arrays, trusted representation and erased index proofs are
independent facts. Closed typed calls may omit repeated header checks; only
proof-indexed APIs omit index/bounds validation. Dynamic APIs retain their
source failure behavior, and public foreign helpers validate malformed input.
W6 must derive the representation and index premises, ownership, copy-on-write
and result relation; generation-shape tests do not establish those proofs.

Scalar boxing conformance covers seven final-LCNF scalar families and exact
upstream `_boxed` result annotations as well as generic tobject paths.
The named wasm32-lean64 contract carries Lean64 semantics through wasm32
addresses, including promoted tags. Historical scalar conformance claims are
versioned; native wasm32 layout is a different contract. Exact alias generation,
zero imports and bit-transport tests remain distinct from helper refinement.

The resident-runtime audit at FIR `631fe8e1e3cbb8e2b4893db24231011b5ac78091`,
2026-08-25, makes the remaining semantic boundary concrete. A reachable generic
inhabited fallback cannot be replaced by an unreachable trap; checked Array
out-of-bounds behavior must retain the recoverable panic observation; semantic
Nat reference counts need finite-header headroom. Its corresponding cards are
`bugs/FIR-BUG-wasm-none-generic-inhabited-fallback-trap.md`,
`bugs/FIR-BUG-wasm-none-array-panic-observation.md` and
`bugs/FIR-BUG-wasm-none-finite-trace-refcount-overflow.md`.
The retained-token ordinaryness/result-kind and tagged partial-application
cases are in `bugs/FIR-BUG-wasm-none-reuse-retained-token-ordinary.md`,
`bugs/FIR-BUG-wasm-none-reuse-retained-result-kind.md` and
`bugs/FIR-BUG-wasm-none-partial-apply-tagged-result.md`.
The {ref "heap-caller-invariant"}[maintained heap/reuse account] and
{ref "provenance-design"}[provenance account] explain their invariant boundaries;
the dated audit is not a fresh claim that its historical statuses still hold.

Trusted Array coverage must include all helpers selected by production policy,
and trusted ByteArray behavior needs direct executable coverage beyond the
checked-only fixture. The Array history explains the checked/public versus
trusted/typed policy and rejects mixed selection; its timing experiments do
not derive the trusted representation or erased-proof premises. Resident
runtime closure requires helper implementation refinement, exact failures,
target safety, compiler-derived trusted premises and import-closure composition.
Zero imports establishes only the syntactic frontier.

The {ref "resident-observation-bridge"}[resident observation bridge] records the
accepted host-versus-resident execution boundary: the unchanged
`ResidentReplacement` post-{name FirTalos.Concrete.StateRelated}`StateRelated` premise, current negative boundary
tests and the proposed ghost-execution versus product-observation projections.
Its source discrepancy is
`bugs/FIR-BUG-wasm-none-resident-host-observation-boundary.md`.
The bridge alternatives and their resident-linking consumer remain a shared
semantic decision; rendered choice documentation does not prove either bridge.

## Resident numeric helpers and their admission consumers
%%%
tag := "resident-numeric-helper-boundary"
%%%

This migrates the final numeric/typed-Array account in
`integration/talos/W6-THEOREM-ROADMAP.md`, compared with accepted source
`8f4222cb2` on 2026-10-05. Its old scratch-cast descriptions and “next”
BigNumeric/heap-sum instructions are historical. Accepted source already has
the accessor and heap-addition results below; the following dated source
account adds no new Lean association or stub.

Let $`B` be `maxImmediatePayload`. A canonical immediate natural $`n\le B`
has word $`E(n)=2n+1`. `ImmediateNaturalPairRel` supplies source references,
payloads and exact encodings; successful adaptation and installation at the
non-import indices supply the actual defined helper bodies.

:::table +header
*
  * Numeric slice and checked body result
  * Premises and extent
*
  * {name Nat.mod}`Nat.mod`: divisor zero returns the left word, matching $`n\bmod0=n`. Nonzero division decodes payloads, executes unsigned remainder and calls adapted immediate makeNatural.
  * `terminatesWith_modFunctionImmediate_of_adapted` joins both immediate paths. Exact local writes and the result bridge preserve store and caller tail; the nonzero path retains needed scratch availability/restoration facts. The adapted checked fallback remains present but unexecuted under the immediate-pair premise.
*
  * Bounded {name Nat.add}`Nat.add`: the generic 64-bit sum chain proves low addition, carry, both high-word overflow guards, constructor-call composition and exact store threading.
  * $`x+y\le B` derives no-carry facts in the adapted naturalSum/makeNatural chain. `terminatesWith_natAddFunctionImmediate_of_adapted` returns $`E(x+y)`, preserving store/tail. Its accepted typed result roundtrip is scratch-free; the physical helper layer retains semantic result validity instead of treating an arbitrary i32 as a Nat.
*
  * {name Nat.decEq}`Nat.decEq`, {name Nat.decLt}`Nat.decLt`, {name Nat.decLe}`Nat.decLe`: encoded-word equality and unsigned order equal payload equality/order.
  * The three wasmWords correspondence laws feed `terminatesWith_decisionFunctionImmediate_of_adapted`. It returns exactly the source decision byte through the accepted scratch-free i32-to-i64-to-UInt8 suffix. The complete checked fallback for non-immediate/mixed/arbitrary-limb inputs is retained, without a correctness claim for that branch from this immediate theorem.
*
  * {name USize.ofNat}`USize.ofNat`, {name USize.ofNatLT}`USize.ofNatLT`: immediate decode/extension returns the exact USize word; ofNatLT's generated erased parameter is accounted for.
  * The checked arm validates before zero-index high/low reads and uses a restored scratch cast. `ResidentUSize.CheckedNaturalCalls` requires these calls to preserve store/tail and to recombine to UInt64.ofNat of the source natural. The valid-input theorem retains the original invalid-representation failure path.
:::

The decision laws and USize recombination can be read as

$$`\begin{aligned}
E(x)=E(y)&\iff x=y,\\
E(x)<_uE(y)&\iff x<y,\\
E(x)\le_uE(y)&\iff x\le y.
\end{aligned}`

$$`2^{32}h+\ell\equiv n\pmod{2^{64}}.`

The precise USize interface uses UInt64 shift/or and `UInt64.ofNat n`, so its
result is the source natural modulo $`2^{64}`. It does not require all natural
values to fit 64 bits.

Accepted source has advanced beyond the roadmap's old accessor task.
`terminatesWith_validateNatural_of_naturalAdmission` derives installed
validator execution from `NaturalValidatorAdmission` and `ResidentMemoryRel`,
including header, ownership and top-limb checks. Installed low/high helpers
execute at arbitrary in-range indices; natural-flavor magnitude count/read
helpers provide exact words or out-of-range zero padding. The USize bridge
`NaturalObjectRel.checkedNaturalCalls_of_validate` constructs the zero-index
package for a related ordinary heap natural above {name Fir.LeanIR.Impure.maxTaggedPayload}`maxTaggedPayload`, retaining
a validator call. `NaturalValidatorAdmission.heapBacked` supplies that strict
bound when canonical validator admission is available; the validator theorem
supplies the call when its admission and installation premises hold. This is not blanket promoted/mixed-representation coverage.

Checked heap/heap addition likewise has actual allocator/header/writer and
one-limb/multiple-limb producer composition, culminating in
`NaturalAddInstallation.terminatesWith_heap_of_admissions`. It retains both
`NaturalObjectRel` and `NaturalValidatorAdmission` operand rows, frontier
validity, `ResidentAllocatorRel`, `LiveHeapRel` and
`CheckedNaturalAddProducerResources`. That branch-indexed package records
actual allocation/constructor execution or multiple-limb allocation/count/
frontier/memory-capacity facts, rather than trusted compiler admission.
The conclusion carries exact semantic sum, typed return, live-heap refinement,
witness extension and restored caller tail. These accepted body/producer results
must not be described as missing because an older plan called them “next.”

The shared consumer is `ResidentPrimitives.wp_definedCallResultSet`, the
host-polymorphic termination bridge, then
`ResidentReplacement.externalLetStepSimulates_of_definedCall`.
The replacement still takes a successful source external step, initial and
*post* {name FirTalos.Concrete.StateRelated}`StateRelated`, physical argument readiness, exact helper termination
and checked destination write. Helper execution supplies one input; it does
not derive the operation's post-StateRelated, compiler argument/provenance
admission or global resource headroom. Operation-specific successor refinement
and the {ref "resident-observation-bridge"}[observation bridge] remain the actual
integration obligations for {bpref "resident-linking"}[]. The unchanged
pure-scalar source external and admission contracts retain their own premises.

Typed Arrays have the analogous compiler obligation: transport the erased
bound and canonical Nat/USize operand from validation/lowering to
`ProofIndexedResidentArrayNatAdmission` or its USize counterpart. The live
`ResidentArrayObjectRel` supplies checked header, exact size, capacity and
related elements; its wasm32 extent bounds the immediate Nat index and makes
USize narrowing exact. General checked Array bounds-fault semantics remain
unchanged. Neither numeric execution nor a typed Array proof manufactures
compiler provenance or finite-machine headroom.

The focused Nat multiplication diagnostic records a concrete arithmetic design
to refine: 32-bit digits inside 64-bit limbs, with accumulator bound

$$`(2^{32}-1)^2+2(2^{32}-1)=2^{64}-1.`

For nonzero canonical operands with $`m` and $`n` 64-bit limbs, the product
needs $`m+n-1` or $`m+n` limbs. The $`m+n` upper-bound allocation therefore has
at most one leading zero limb, so canonicalization needs at most one
exact-extent copy. It publishes no unfinished natural buffer and retires
through the ordinary recycler. Borrowed inputs and
persistent promoted values keep their ownership contracts. BigInt differentials
and poisoned-reuse plateau checks are executable evidence for this design;
the general multiplication refinement remains W6 work.

Source-prose correction, 2026-10-05 at accepted `8f4222cb2`:
`Fir/Wasm/Emit/Tests/README.md` says nonzero operands need “at most one fewer”
limb than the sum. That wording is incorrect: two maximal one-limb values
produce a two-limb product, $`(2^{64}-1)^2`, with $`m=n=1`.
`ResidentNatMultiplication` allocates $`m+n`; its `finish` handles at most
one leading zero under the nonzero canonical operand conditions. This is a
mathematical source-text correction; it changes no runtime and claims no
fresh execution test. The owner README remains owner-maintained evidence.

The shared external runtime closes remaining externs through exact names and
signatures and preserves the frontier export inventory. Source-compiled
{name Float.ofNat}`Float.ofNat` and {name Float.ofScientific}`Float.ofScientific` use Lean's exposed definitions and the
complete resident arbitrary-precision Nat/Int/BitVec/Float model path; they are
not left at the C-provider frontier. The six genuine platform-libm externals
instead use the separate binary64-only C runtime, with its stated special-value/
bit-transport checks and platform-dependent finite libc results.
Only packages that actually link that provider reserve 65536 low-memory bytes
for its C data and stack and advance the FIR heap frontier past them.
Provider-free resident modules retain their separate closed-module route.
Linker and Binaryen rejection/determinism checks are executable evidence; full
semantic linking/optimization preservation remains a theorem boundary.
Instruction provenance binds origins to exact encoded offsets and distinguishes
mapped, deleted, unknown and ambiguous transformed code. A debug companion
whose stripped bytes differ cannot certify the canonical release; profiling
origin transport is separate from semantic correctness.
The provenance-cost report's opt-in, regenerable origin table remains separate
from exact-release final-function profiling. Caller attribution identifies
workload-specific allocation/release locations, not a universal List-only cost
or an ownership theorem. Its proposed generic release fast path and constructor
consolidation need the same stable carrier/provenance contracts as other
generation changes.

The render-core v0 host-binding profile is a draft synchronous adapter contract:
exact import/export descriptors, checked scalars/UTF-8 and live opaque resource
tokens with borrow/take/return ownership. Retained callbacks, effects, hooks,
RPC and async require separate reviewed profiles. Adapter conformance does not
prove React lifecycle or rendered-output correctness.

Validation compares portable observations from native Lean, final-LCNF
interpretation and real Wasm engines on the admitted corpus. Source-produced
and handwritten direct-machine cases retain distinct provenance. Static form
presence, executed forms/counts/ordered traces and semantic observations answer
different coverage questions. Exact-zero requirements detect a branch that
must not execute; set membership alone cannot. Product digests, contracts and
case bindings prove which bytes were supplied; file-access tracing establishes
that the engine/runner process tree opened them, not which process instruction
executed which case. None of these finite checks proves universal correctness.

The semantic-fidelity portfolio covers ownership/memory, calls/control,
effects/termination, floating computation, aggregates/erasure/initialization
and real-engine promotion. Protocol observations distinguish returned results,
exceptions, exits, runtime faults and controlled divergence from timeout/crash/
unsupported/fuel failures. Its historical source/native/V8 adapters' returned
observations do not establish coverage of every protocol constructor.
Counts and floors are regression evidence, not a theorem-completeness metric.

# Source authorities
%%%
tag := "source-disposition-inventory"
%%%

The statements above use FIR's production definitions and the following
owner-maintained evidence:

* `docs/pass-correctness-plan.md` and `pass-correctness-history.md` retain the
  pass-proof inventory and its reviewed compiler versions.
* `integration/talos/PLAN.md`, `W6-THEOREM-ROADMAP.md`, `W6-COVERAGE.md`,
  `W6-OBSERVABLE-CONTRACT-AND-TRUST.md` and `W6-FAULT-AUDIT.md` retain W6's
  implementation plan, exact theorem/trust inventories and fault classifications.
* `docs/w6-source-admission-audit.md` and
  `docs/wasm-object-carrier-provenance-plan.md` retain the source census and
  provenance design inputs to the admission and invariant chapters.
* The retained-initializer source and artifact/package READMEs retain exact
  capture, release and executable-validation identities. Tooling and build
  instructions remain with their owning integrations and `AGENTS.md`.

Review these sources when their definitions or evidence change. The Blueprint
maintains the argument and its consumers; the completed migration census and
historical editorial dispositions remain in Git history.
