import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6
import FirBlueprint.Chapters.HeapInvariant

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Admission coverage" =>
%%%
tag := "admission-coverage"
%%%

This chapter maps every row of `docs/w6-source-admission-audit.md` to the
Blueprint argument. Reviewed against source base FIR `93c2e7ec7`: the audit,
`ConcreteFinalLcnfTyping`, `ConcreteStructuredValidation`,
`ConcreteStructuredSimulation` and the closure-call interfaces in
`ConcreteReuseCapacityCacheCorrectness`. This is source review and documentation
of existing results, not a new proof of admission closure.

The 2026-10-05 source review at accepted main `8f4222cb2` includes
`f6850d79f`'s stepwise initializer/saved-caller successor, described in the
{ref "heap-caller-invariant"}[heap chapter]. It leaves the twenty-branch
admission inventory and its central heap-miss restriction unchanged. The
operation subfamilies below migrate `integration/talos/W6-COVERAGE.md` and
the structural runtime/work-order argument in `W6-THEOREM-ROADMAP.md`;
their exact fixtures, runtime symbol inventories and chronological gate
records remain in those source files.

The selected endpoint is {bpref "validated-return"}[]. Its missing admission
proof is {bpref "admission-closure"}[]. The table makes that proof plan's
coverage reviewable: a graph node can cover several branches, and one branch
can require several obligations. All twenty rows are represented here; the
decomposition remains an authored plan until its statements and assembly are
checked. Cross-branch preservation remains additional work.

# Common boundary

Every row starts from an actual supported compiled function, its exact result
ABI, a recursively validated current outcome, and the applicable source step.
That outcome retains the runtime/environment, residual validation, suspended
frames, reuse facts and byte budget. These guards must be reconstructed or
projected from the production relation, rather than supplied as a new arbitrary
client invariant.

For schema operations, preserve the source constructor schema and its agreement
with the same active refinement witness. Schema source safety is converted to
schema admission by {bpref "schema-admission-bridge"}[]; descriptor alignment
is used by the subsequent schema-aware simulation. The old and schema field
branches are alternative interfaces to the same two operations, not four
independent source obligations.

The audit distinguishes facts already derivable, hidden interfaces, semantic
provenance, finite resources and semantic discrepancies. In this chapter,
“available” means branch admission has existing ingredients at the stated
guards. It does not mean the full endpoint, its trust policy or its integration
is complete. “Open” identifies the semantic or coverage obligation still to
construct. Resource conditions are listed separately.

# All twenty branches

:::table +header
*
  * Row
  * Branch
  * Blueprint location
  * Remaining work / cost
*
  * 1
  * Return
  * {bpref "return-admission"}[], {bpref "provenance-closure"}[]
  * Open precise-row construction/preservation and non-refining use coverage; cost 0.
*
  * 2
  * Direct let
  * {bpref "direct-let-closure"}[]
  * Open producer/reuse evidence; exact {name FirTalos.Concrete.directLetAllocationCost}`directLetAllocationCost`, with address headroom.
*
  * 3
  * Pure external
  * {bpref "external-admission"}[], {bpref "external-spec"}[]
  * Open primitive contract and compiler bridge; derive exact cost, retain address headroom.
*
  * 4
  * Direct call
  * {bpref "direct-admission"}[], {bpref "provenance-closure"}[]
  * Open non-refining current-argument provenance; compiler site/result facts are derived; cost 0.
*
  * 5
  * Saturated closure call
  * {bpref "closure-call-closure"}[]
  * Open site/resolution and closure-origin evidence; retain capture capacity; cost 0.
*
  * 6
  * Lazy-cache hit
  * {bpref "lazy-hit-admission"}[]
  * Available from validated call and actual lookup; no miss restriction; cost 0.
*
  * 7
  * Lazy-cache miss
  * {bpref "lazy-admission"}[], {bpref "heap-miss-closure"}[], {bpref "external-admission"}[]
  * Open general intermediate object/tobject closure and external initializer coverage; saved validated fresh caller/publication path is accepted; current entry cost 0.
*
  * 8
  * Default-only case
  * {bpref "case-admission"}[]
  * Available from normalized validation and selected source branch; cost 0.
*
  * 9
  * Object constructor cases
  * {bpref "case-admission"}[]
  * Available with exact UInt64 tag handling; the truncation repair removed the former gap; cost 0.
*
  * 10
  * Scalar UInt8 cases
  * {bpref "case-admission"}[]
  * Available from validated mode, normalized alternatives and tag bounds; cost 0.
*
  * 11
  * Persistent increment
  * {bpref "schema-admission-bridge"}[]
  * Available from syntax/residual validation; cost 0.
*
  * 12
  * Persistent decrement
  * {bpref "schema-admission-bridge"}[]
  * Available from syntax/residual validation; cost 0.
*
  * 13
  * Ordinary increment
  * {bpref "schema-admission-bridge"}[], {bpref "finite-runtime"}[]
  * Available at explicit UInt32 header headroom; cost 0.
*
  * 14
  * Ordinary decrement
  * {bpref "schema-admission-bridge"}[]
  * Available from successful release-step inversion; cost 0.
*
  * 15
  * Explicit delete
  * {bpref "schema-admission-bridge"}[]
  * Available for ordinary delete or erased-zero no-op; cost 0.
*
  * 16
  * Constructor tag mutation
  * {bpref "schema-admission-bridge"}[]
  * Available from live-constructor/tag facts in the successful mutation; cost 0.
*
  * 17
  * Object-field FVar mutation
  * {bpref "object-field-closure"}[]
  * Open source slot typing/preservation, followed by schema-to-descriptor alignment; cost 0.
*
  * 18
  * Object-field erased mutation
  * {bpref "object-field-closure"}[]
  * Open erased-slot kind/preservation, followed by schema-to-descriptor alignment; cost 0.
*
  * 19
  * USize field mutation
  * {bpref "schema-admission-bridge"}[]
  * Available from validated lanes and successful-step bounds; cost 0.
*
  * 20
  * Packed scalar field mutation
  * {bpref "scalar-field-closure"}[]
  * Open packed coordinate/extent/non-overlap evidence; scalar lane alone is insufficient; cost 0.
:::

For rows 11–16 and 19, the existing operation lemmas live under
{name FirTalos.Concrete.ConcreteStructuredAlignedValidationState}`ConcreteStructuredAlignedValidationState` in `ConcreteStructuredValidation`:
{name FirTalos.Concrete.ConcreteStructuredAlignedValidationState.admit_incPersistent}`admit_incPersistent`, {name FirTalos.Concrete.ConcreteStructuredAlignedValidationState.admit_decPersistent}`admit_decPersistent`, {name FirTalos.Concrete.ConcreteStructuredAlignedValidationState.admit_incOrdinary_of_step}`admit_incOrdinary_of_step`,
{name FirTalos.Concrete.ConcreteStructuredAlignedValidationState.admit_decOrdinary_of_step}`admit_decOrdinary_of_step`, {name FirTalos.Concrete.ConcreteStructuredAlignedValidationState.admit_del_of_step}`admit_del_of_step`, {name FirTalos.Concrete.ConcreteStructuredAlignedValidationState.admit_setTag_of_step}`admit_setTag_of_step` and
{name FirTalos.Concrete.ConcreteStructuredAlignedValidationState.admit_uset_of_step}`admit_uset_of_step`. The source-safety dispatcher composes these facts; its
associated Blueprint node exposes the checked bridge. We have not introduced
a separate task node for every already-available operation.

Address headroom is {bpref "address-space"}[]; header and capture bounds are
{bpref "finite-runtime"}[]. A zero current-step allocation cost does not mean
an entire call or initializer uses no memory. These are retained resource
conditions, not requests to prove unbounded executions safe.

# Direct-let subfamilies and source schemas

Row 2 is a family, not a single heap operation. {name FirTalos.Concrete.BudgetedDirectSupported}`BudgetedDirectSupported`
combines aliases, immediate integer/{name USize}`USize` literals, arbitrary Nat literals,
object/{name USize}`USize`/packed projections, supported integer boxing/unboxing, sharing,
UTF-8 String literals and nonempty constructors.
{name FirTalos.Concrete.OwnershipBudgetedDirectSupported}`OwnershipBudgetedDirectSupported` adds successful reset under the immutable
descriptor agreement. {name FirTalos.Concrete.ReuseBudgetedDirectSupported}`ReuseBudgetedDirectSupported` is the facts-indexed
extension admitting retained/fresh reuse with its constructor/box/read-only
families. These are checked predicates consumed by structural theorems; their
existence does not prove that every validated declaration satisfies them.

:::table +header
*
  * Subfamily / concrete operation
  * Existing executable/refinement argument
  * Remaining compiler-wide obligation or exclusion
*
  * Alias and immediate scalar/{name USize}`USize` literal
  * Production inversion and aligned locals derive the read/write; runtime, witness and allocation budget are unchanged.
  * Preserve the precise source binding when the physical row is weaker; reconstruct {name FirTalos.Concrete.LocalAliasSupported}`LocalAliasSupported`/{name FirTalos.Concrete.ImmediateLiteralSupported}`ImmediateLiteralSupported` from the guarded node.
*
  * {name Fir.Wasm.RuntimeOp.literal}`literal`: arbitrary Nat
  * Source value chooses immediate, promoted-tag or limb-object representation; frontier and budget construct allocation and exact result/witness growth.
  * Derive the exact effective result kind and retain the representation-sensitive source cost. A precise tagged immediate rule has its payload bound; it does not cover every Nat by that rule.
*
  * {name Fir.Wasm.RuntimeOp.literal}`literal`: UTF-8 String
  * Exact UTF-8 payload, header, witness extension, generated call/local write and finite String-spine/export composition.
  * Derive producer kind and closure/ownership effects from the same literal invariant; byte capacity remains explicit.
*
  * {name Fir.Wasm.RuntimeOp.allocCtor}`allocCtor`
  * Empty constructors are semantically tagged, represented immediately or by a persistent promoted tag; mixed nonempty allocation derives field arguments, descriptor and exact residual budget with arbitrary continuation.
  * Preserve source constructor-schema field kinds and active-witness agreement. Invalid-arity fault classification stays at `FIR-BUG-wasm-none-constructor-arity-fault-classification`.
*
  * {name Fir.Wasm.RuntimeOp.objectProj}`objectProj`
  * Live/stale mapped heap refinement; production/resolver inversion supplies descriptor existence, physical receiver and destination.
  * Derive selected-field ABI-kind agreement from the preserved source schema; heap location alone does not state the field kind.
*
  * {name Fir.Wasm.RuntimeOp.usizeProj}`usizeProj`
  * The successful source step and heap relation derive constructor descriptor, absolute bounds, i64 result and generated write.
  * Maintain source/compiler lane agreement; no extra successful-heap-shape certificate is needed.
*
  * {name Fir.Wasm.RuntimeOp.scalarProj}`scalarProj`
  * Six packed scalar kinds have concrete reads and raw-bit float refinement; compiler/adaptor execution retains a read/layout obligation.
  * Derive packed coordinates, initialized extent and overlap policy from producer/schema evidence. `FIR-BUG-wasm-none-uninitialized-scalar-projection` and `FIR-BUG-wasm-none-scalar-slot-layout-contract` remain visible.
*
  * {name Fir.Wasm.RuntimeOp.box}`box`
  * Five integer/{name USize}`USize` kinds construct immediate/promoted/heap output from source typing and a one-slot reservation; generated unary call and result binding compose.
  * Prove the actual representation policy supplies the exact effective result information. Float32/Float boxing is outside this implemented family.
*
  * {name Fir.Wasm.RuntimeOp.unbox}`unbox`
  * Source scalar-kind compatibility plus the relation derives descriptor/read, actual call and exact i32/i64 lane.
  * Construct the scalar-kind compatibility fact from preserved producer evidence. Float32/Float unboxing is outside this implemented family.
*
  * {name Fir.Wasm.RuntimeOp.isShared}`isShared`
  * Immediate, promoted, live/stale mapped heap cases; compiler-local typing and current relation derive successful call and result.
  * Any branch refinement of the tested binding needs its semantic guard theorem. The UInt8 result alone cannot rewrite unrelated object provenance.
*
  * {name Fir.Wasm.RuntimeOp.reset}`reset`
  * Tagged, persistent/nonunique and unique-constructor branches are derived from the source step; frontier/witness/descriptors transport under ownership agreement.
  * Preserve the resulting retained-token origin and capacity. Recursive closure release uses the immutable capture descriptors.
*
  * {name Fir.Wasm.RuntimeOp.reuse}`reuse`
  * Facts and fitting extent derive empty/fresh/in-place branch, compiled arguments, descriptor transport, result write and exact budget remainder.
  * Compiler-wide capacity/ordinaryness and retained empty-layout result provenance remain at `FIR-BUG-wasm-none-reuse-retained-token-ordinary` and `FIR-BUG-wasm-none-reuse-retained-result-kind`.
:::

The source cost $`C(d)=\operatorname{directLetAllocationCost}(d)` is selected
from the declaration $`d`: constructor layout extent, representation-sensitive
fresh reuse reservation, Nat representation extent, aligned UTF-8 String
extent, one-slot integer-box reservation, or zero for the other forms. With
current remaining budget $`B`, admission derives $`C(d)` and the resource law
supplies $`C(d)\le B`; the successor receives $`B-C(d)`. Retained in-place
reuse or immediate boxing can leave some physical reservation unused while
respecting that logical bound. This is a resource accounting rule for the
finite execution, not a proof that every allocating source prefix fits wasm32.

The checked {name FirTalos.Concrete.ReuseBudgetedDirectSupported.schema_cases}`ReuseBudgetedDirectSupported.schema_cases` separates constructor/
reuse schema-changing operations from the monotone schema-preserving family.
{name FirTalos.Concrete.ConstructorSchema.SourceStep}`ConstructorSchema.SourceStep` records actual compiled-layout allocation/reuse
evolution and rules out unchanged schema replay at those nodes. Preserve that
transition through administrative call/bind/cache states with the same active
witness, then construct the source slot facts needed by rows 17, 18 and 20.

# Effects, cases, calls and caches

The operation matrix has a different granularity from the admission inventory.
An operation proof relates a host/runtime transition; a current-step branch
must also recover its compiler prefix, locals, continuation and maintained
frame. The following groups account for the remaining {name Fir.Wasm.RuntimeOp}`RuntimeOp` rows without
making each tested instruction sequence a separate mathematical task.

:::table +header
*
  * Operation / inventory rows
  * Composition and preservation argument
  * Boundary retained
*
  * {name Fir.Wasm.RuntimeOp.inc}`inc`, {name Fir.Wasm.RuntimeOp.dec}`dec`, {name Fir.Wasm.RuntimeOp.delete}`delete`; rows 11–15
  * Persistent effects erase to zero target steps; ordinary ownership derives the generated unary call and successor. Recursive decrement handles constructor/closure children, repetition, shared/persistent/no-op paths and canonical release; delete includes erased zero.
  * Ordinary increment needs UInt32 header headroom. Closure release uses descriptor-table identity. General fault closure is separate from the successful branch proofs.
*
  * {name Fir.Wasm.RuntimeOp.setTag}`setTag`, {name Fir.Wasm.RuntimeOp.objectSet}`objectSet`, {name Fir.Wasm.RuntimeOp.usizeSet}`usizeSet`, {name Fir.Wasm.RuntimeOp.scalarSet}`scalarSet`; rows 16–20
  * Exact unary/binary prefixes, local/constant erased writes, frontier framing and ownership transport compose in the mixed facts-indexed theorem. Scalar writes cover six kinds with raw-bit float relations.
  * Object source-slot kinds and packed coordinate/extent/non-overlap remain producer preservation obligations; {name USize}`USize` successful bounds and validated lanes already suffice. Tag fit is explicit.
*
  * {name Fir.Wasm.RuntimeOp.getTag}`getTag`; rows 8–10
  * Default-only erasure uses strict rank descent; ordered object and UInt8 chains follow the source-selected hit/miss/default path under nested target labels. Exact UInt64 object-tag handling avoids truncation.
  * Missing-alternative fault transport remains `FIR-BUG-wasm-none-unreachable-fault-classification`; default normalization and semantic discriminator mode must stay compiler-derived.
*
  * Direct call; row 4
  * Production residual validation derives the site, numeric target, parameter/result rows, local identities and zero-cost entry. Effective noncached results directionally refine the source let result.
  * Non-refining {name Fir.Wasm.AbiKind.tobject}`tobject` argument ingress still needs the precise semantic row. The nullary-cache result compatibility exception is a separate policy.
*
  * {name Fir.Wasm.RuntimeOp.partialApply}`partialApply`, {name Fir.Wasm.RuntimeOp.closureMatches}`closureMatches`, {name Fir.Wasm.RuntimeOp.closureProj}`closureProj`, generated closure dispatch; row 5 and direct producers
  * Allocation retains module-derived descriptors; the candidate fold skips nonmatches, projects typed captures and either underapplies or executes a direct defined call. Host callbacks do not execute the target.
  * Closed-ingress target membership, precise captured kinds and finite capture retention; the tagged partial-result gap is `FIR-BUG-wasm-none-partial-apply-tagged-result`.
*
  * {name Fir.Wasm.RuntimeOp.cacheSet}`cacheSet`; rows 6–7
  * Typed globals and recursive graph persistence cover represented nonheap and constructor/closure/box/Nat/String graphs. Compiler-derived hit/miss controls, declaration bodies, publication writes/reload and destination binding compose.
  * Hit admission is derived; general heap-miss intermediate closure remains open despite the actual fresh Array consumer. Other declaration-body/initializer families and external provenance need their own composition.
*
  * Numeric and other externals; row 3 and heap initializer bodies
  * Uniform Int/Nat/scalar implementation laws reconstruct exact response, value relation, event, witness and cost; representation-independent staging/call/bind accepts general concrete evidence such as Array allocation/push.
  * Named mathematical contract, meaningful request domain, installed implementation and branch provenance are required; see the {ref "external-domains"}[external contract chapter].
:::

The successful structural theorem permits arbitrary finite mixed spines,
cases and ownership/mutation effects within its stated supported families.
Uniform runtime laws and structural induction hypotheses have a different
role from a per-program target execution certificate: production inversion
constructs the plumbing and a successful source step selects its semantics.
Those existing finite-return and budgeted composition results are useful
ingredients for {bpref "admission-closure"}[], without establishing the
validator-wide reverse implication themselves.

For resident typed Array reads, {name Fir.Wasm.Concrete.ResidentArrayObjectRel}`ResidentArrayObjectRel` supplies checked
header, logical size, capacity and related elements. The complete wasm32
extent proves that logical size fits the canonical immediate-Nat range.
{name Fir.Wasm.Concrete.ProofIndexedResidentArrayNatAdmission}`ProofIndexedResidentArrayNatAdmission` then retains the erased source bound
and canonical Nat operand; its USize companion proves exact narrowing and
selects the same element. The validator/lowerer must transport that erased
proof to the generated unchecked call. General checked Array bounds faults
and semantics retain their own rules.

# What branch coverage does not settle

## The invariant must survive the whole execution

The {ref "provenance-design"}[provenance chapter] now expands the shared
call/return argument and its static-coverage/semantic-preservation split.

Current-node admission and preservation of its inputs are separate arguments.
The canonical precise-local row must be constructed and maintained through
producers, projections, joins and call boundaries. Constructor schema, reuse
and packed layout facts must survive the operations that consume them. A branch
with available admission may still participate in that preservation proof.

The existing result boundary uses {name FirTalos.Concrete.SemanticBindingAtAbi}`SemanticBindingAtAbi`, with stronger use-site
evidence only on non-refining edges. {name FirTalos.Concrete.SemanticEnvAtLocalKinds.ofStateRelated}`SemanticEnvAtLocalKinds.ofStateRelated`
already derives the ordinary validator row from the live physical relation.
{name FirTalos.Concrete.SemanticValuesAtAbi.semanticEnv_of_bindParams}`SemanticValuesAtAbi.semanticEnv_of_bindParams` establishes precise call entry;
publication lemmas handle result binding. Those ingredients do not construct
the remaining precise producer analysis by themselves.

The design choice recorded in the audit is to derive a canonical compiler
analysis and prove its preservation, or establish an equivalent fixed property
at the checked-program boundary. Changing that boundary revises the theorem
statement and needs owner review. Adding a caller-selected provenance map does
not complete {bpref "provenance-closure"}[].

## Coverage boundaries may require statement changes

{bpref "lazy-miss-boundary"}[] currently excludes external initializers and
object/tobject misses. Covering those accepted source operations may require
extending the simulator and maintained relation. Closure candidate membership
also needs a precise account of initial data and external closure ingress.
These are design obligations; no claim is made that the current admitted
signature can be proved without revision.

The {ref "heap-caller-invariant"}[heap/caller chapter] makes the current
relation choice explicit: active construction carries its original cutoff,
entry-indexed transports and dynamic region evidence; the accepted saved lazy
frame retains the validated caller and generated continuation. The wider
dispatcher must preserve that pair through nested/intermediate states. Fresh
result publication, an already persistent older result, and arbitrary external
ingress are distinct cases. A theorem covering only the first case does not
justify excluding the others from an accepted-source claim.

This inventory covers the current admission constructors. It does not prove
that they cover every operation accepted by lowering, nor does it finish the
general direct-let admission/preservation proof. Its subfamilies and intended
schema transfers are documented above. The successful-return goal also leaves
{bpref "fault-closure"}[] and {bpref "resident-linking"}[] as separate endpoints.

# VBP case: explain the scope of a decomposition

Existing associations, groups, authored proof dependencies, `bpref` links and
ordinary Verso section references express this map. The admission proof plan
links directly to this chapter. Four new open family nodes prevent the selected graph from
silently omitting known obligations. The table records the many-to-many
relationship between audit rows and proof nodes without turning every row
into an independent theorem task.

The remaining product question is whether those existing links suffice for
readers and agents to recover the scope and evidence of that map. Dependency
origin and intent do not state whether
an authored plan covers an enumerated inventory or whether Lean has checked
its exhaustive assembly. A complete inventory of twenty rows also says nothing
about the completeness of the inventory's source-language boundary.

Acceptance case: from {bpref "admission-closure"}[], a reader should find the
reviewed inventory, distinguish branch coverage from invariant preservation,
and see which decomposition claims are editorial versus checked. Adding a
new branch should prompt review of that coverage claim. For now the chapter
states this explicitly; whether VBP needs a core feature, a documentation
pattern or a queryable evidence link remains open. The
{ref "bp-fir-11"}[branch-coverage acceptance case] retains this authoring question;
no new completeness algorithm is proposed.
