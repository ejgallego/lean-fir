import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6
import FirBlueprint.Chapters.HeapInvariant

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The provenance argument" =>
%%%
tag := "provenance-design"
%%%

This is the shared argument behind admission audit rows 1 and 4: returns and
ordinary direct calls. It migrates the cross-branch conclusions and PA1/PA2
provenance narrative from `docs/w6-source-admission-audit.md` and the whole
design in `docs/wasm-object-carrier-provenance-plan.md`. Interfaces were reviewed
against `ConcreteFinalLcnfTyping.lean` at source base FIR `93c2e7ec7`; the
October 5 review of main `8f4222cb2` leaves these interfaces unchanged. The
chapter specifies the evidence flow and unresolved choices. It adds no
production analysis, proof or public invariant.

# Annotation, carrier and semantic evidence

Final LCNF's {name Lean.Compiler.LCNF.ImpureType.object}`object`,
{name Lean.Compiler.LCNF.ImpureType.tagged}`tagged` and
{name Lean.Compiler.LCNF.ImpureType.tobject}`tobject` annotations share an object-word
`i32` carrier at ordinary call, return, join and partial-capture boundaries.
Their semantic claims differ: heap object, source tagged value, and the union
of those representations. {name Lean.Compiler.LCNF.ImpureType.erased}`erased` and reuse tokens also occupy `i32`, but
carry different semantic obligations. Small integer lanes remain distinct
scalar kinds; {name UInt64}`UInt64` and semantic {name USize}`USize` use `i64`, {name Float32}`Float32` uses `f32`, and
{name Float}`Float` uses `f64`. Equality of physical Wasm types does not justify an
arbitrary scalar/object transfer.

{name Fir.Wasm.AbiKind.refines}`AbiKind.refines` is the accepted directional semantic relation;
{name Fir.Wasm.AbiKind.leanCompatible}`AbiKind.leanCompatible` also accepts symmetric object-family carriers at
ordinary transfers. The latter repair permits actual compiler-produced calls
and joins. {name Fir.Wasm.effectiveDeclarationResultKind?}`effectiveDeclarationResultKind?` conservatively preserves exact
heap/tagged result information through supported straight-line named calls and
lazy caches, including the HitScene regressions. It remains the implementation
while a better evidence interface is considered.

The preferred wider descriptor design separates three axes. Schematic names,
not committed API declarations, are

$$`\operatorname{ValueInfo}(v)
 = (\operatorname{annotation}(v),\operatorname{carrier}(v),
    \operatorname{provenance}(v))`.

`carrierCompatible` would be a symmetric physical transfer check;
`provenanceRefines` would be directional semantic evidence; `operationAccepts`
would compare an operation's semantic requirement with that evidence. The
{ref "heap-caller-invariant"}[concrete value relation] erases sound evidence to
the actual concrete lane without confusing a promoted source tag with a heap
source value. No new client ABI or second object encoding is proposed.

# Why the ordinary compiler row is insufficient

A physical object-family lane may describe either a tagged value or a heap
reference. In particular, {name Fir.Wasm.AbiKind.tobject}`.tobject` does not imply {name Fir.Wasm.AbiKind.object}`.object`. A call may accept
carrier-compatible lanes while its parameter requires the more precise shape.
Likewise, a return use may need a stronger result shape than its local lane
records. Successful source evaluation alone does not add that shape check.

When the actual ABI directionally refines the expected ABI, existing refinement
lemmas already supply the required semantic typing. Extra provenance is needed
only at non-refining uses. The audit's measured `tobject -> object` argument
examples motivate this boundary; their count is historical evidence, not the
definition or a complete list of programs the theorem must handle.

The ordinary row is already semantically typed by
{name FirTalos.Concrete.SemanticEnvAtLocalKinds.ofStateRelated}`SemanticEnvAtLocalKinds.ofStateRelated`, using compiler-local agreement, layout
alignment and the live source/target relation. Re-proving that fact would leave
the stronger non-refining use obligation untouched.

# Two pieces of evidence for the same precise row

The physical lowering row and a compiler-produced precise row may differ.
For example, lowering can store a value in a {name Fir.Wasm.AbiKind.tobject}`.tobject` lane while the precise
row records that this particular binding is a heap object. The representation
and target address do not change merely because more source information is known.

Let $`P` be a compiler-produced precise row, $`E` the current source environment,
and $`k` a semantic ABI kind. The settled semantic interface is

$$`\operatorname{Typed}(P,E)
 \quad\Longleftrightarrow\quad
 \forall x,k,\;P[x]=k\ \Longrightarrow\
 \operatorname{SemanticBindingAtAbi}(E,x,k)`.

For argument syntax $`A`, physical kinds $`K` and required kinds $`R`, static
coverage is over exact occurrences in their zipped rows:

$$`((x,k),r)\in(A\mathbin{\mathrm{zip}}K)
                  \mathbin{\mathrm{zip}}R\ \land\
 k\not\preceq r\quad\Longrightarrow\quad P[x]=r`.

Here $`k\preceq r` abbreviates `k.refines r = true`, and $`x` is an FVar
argument. This is the meaning of {name FirTalos.Concrete.NonRefiningArgumentsCoveredBy}`NonRefiningArgumentsCoveredBy`, not a newly
chosen analysis. Return coverage makes the analogous selected-local claim.
Coverage together with $`\operatorname{Typed}(P,E)` supplies the exact semantic
binding on each non-refining edge. The common use-site predicate itself is

$$`\operatorname{Use}(E,x,k,r)
 \quad\Longleftrightarrow\quad k\preceq r\ \lor\
 \operatorname{SemanticBindingAtAbi}(E,x,r)`.

:::table +header
*
  * Evidence
  * Existing interface
  * What must still be established
*
  * Static coverage of call uses
  * {bpref "call-provenance-coverage"}[]
  * The chosen analysis row contains the required kind for each non-refining occurrence in this call.
*
  * Static coverage of return uses
  * {bpref "return-provenance-coverage"}[]
  * The same analysis supplies the required kind at a non-refining return.
*
  * Semantic truth of the row
  * {bpref "precise-local-semantics"}[]
  * Each recorded kind is true of the current binding, and stays justified through execution.
:::

Coverage alone is a claim about entries in a list. Semantic typing alone does
not show that the row contains the entries needed by a particular consumer.
The checked {name FirTalos.Concrete.SemanticEnvAtLocalKinds.nonRefiningArgumentsAt}`SemanticEnvAtLocalKinds.nonRefiningArgumentsAt` combines them for
the exact current argument occurrences. The return counterpart is
{name FirTalos.Concrete.ConcreteStructuredReturnUseSiteProvenanceAt.ofCoverage}`ConcreteStructuredReturnUseSiteProvenanceAt.ofCoverage`.

These observations separate {bpref "provenance-analysis"}[] from
{bpref "provenance-preservation"}[]. Their signatures must be designed together
so they describe the same rows. The current graph records a proposed argument,
not two independent, stable contributor tasks.

# How the consumers use the evidence

For a direct call, production residual validation constructs
{name FirTalos.Concrete.DirectInternalCallCompilerAdmission}`DirectInternalCallCompilerAdmission`, including its actual and parameter ABI
rows. {name FirTalos.Concrete.ConcreteDirectCallArgumentProvenanceAt}`ConcreteDirectCallArgumentProvenanceAt` asks only for semantic typing of
the non-refining members of that chosen row. The source step supplies argument
evaluation; {bpref "direct-admission"}[] then constructs the dynamic site and
zero-cost current admission. The compiler-selected result direction and local
identities are already derived.

For a return, {bpref "return-admission"}[] explicitly consumes semantic typing
of a provenance row and {name FirTalos.Concrete.ConcreteStructuredReturnUseSiteCoveredBy}`ConcreteStructuredReturnUseSiteCoveredBy`. Together
they yield the exact result binding required by the existing simulator. This
is why a checked conditional return-admission theorem does not complete
{bpref "provenance-closure"}[].

Both paths feed {bpref "admission-closure"}[], which is used by
{bpref "validated-return"}[]. These consumer paths explain the contribution's
purpose without treating a conditional lemma as a new universal assumption.

# What entry and publication already provide

{bpref "precise-call-entry"}[] establishes the canonical parameter row after
actual parameter binding, provided the supplied values have the required ABI
shapes. The row follows the same replacement/shadowing discipline as the source
binder. This mechanism can be reused at named calls, closure calls and joins;
each invocation must still establish its prerequisites.

{name FirTalos.Concrete.SemanticEnvAtLocalKinds.publishResult}`SemanticEnvAtLocalKinds.publishResult` extends a typed row when a producer
supplies a value of its promised kind. {name FirTalos.Concrete.SemanticEnvAtLocalKinds.publishPhysicalResult}`publishPhysicalResult` obtains that
semantic fact from an existing physical result relation. Their refinement
variants retain the producer's precise kind while supporting a weaker use.
They are reusable binding lemmas, not a proof that every producer supplies the
fact needed by a new analysis.

:::theorem "precise-result-publication" (parent := "compiler") (owner := "w6") (tags := "conditional") (lean := "FirTalos.Concrete.SemanticEnvAtLocalKinds.publishResult") (autoDeps := true)
If $`\operatorname{Typed}(P,E)` and a producer supplies a value $`v` of exact
kind $`k`, binding it at $`x` preserves the precise row:

$$`\operatorname{Typed}(\operatorname{insert}(P,x,k),
                        \operatorname{bind}(E,x,v))`.

Both source binding and row insertion replace the same named binding. The
physical-result and directional-refinement variants recover the semantic fact
from an already proved result relation and expose weaker uses while retaining
the exact producer kind.
:::

Remaining preservation work includes the precise information supplied by
projections, rules for joining control-flow information, and transporting the
chosen rows across the relevant current and suspended execution contexts.
The exact decomposition needs owner review. Object-field schema typing,
packed layout and closure candidate membership have their own obligations in
the {ref "admission-coverage"}[coverage map]; this local-kind argument does not
silently discharge those richer invariants.

# Producer and transfer obligations

The following is the proposed semantic transfer plan. The ordinary exact
producer result laws and {bpref "precise-result-publication"}[] exist; the table
does not claim an implemented canonical analysis for the stronger row.
Each rule must establish truth of the information it adds, preserve unaffected
bindings, and agree with the row selected by static coverage.

:::table +header
*
  * Producer or boundary
  * Information and preservation argument
*
  * Local alias
  * Copy the source binding's proved semantic kind, including any stronger use-site fact. The target lane and object identity are unchanged; replacement/shadowing erases obsolete destination information.
*
  * Literal
  * Retain the literal's established semantic invariant. Natural immediates may have immediate or promoted concrete representations; UTF-8 Strings have heap provenance. Scalar literals retain their exact scalar kind.
*
  * Constructor
  * Nullary constructors produce semantic tagged information, with immediate or persistent promoted-tag physical representation; allocated nonempty constructors produce heap information. Preserve source field-schema kinds and their active-witness agreement separately from the local result row.
*
  * Object, {name USize}`USize` and packed scalar projection
  * Use the producer-preserved source schema and concrete descriptor/read theorem to establish the selected field's semantic kind. An object receiver or successful read alone does not reconstruct an arbitrary field kind or packed coordinate.
*
  * Boxing and unboxing
  * Apply the toolchain's exact scalar representation policy. Supported integer/{name USize}`USize` boxing can have immediate, promoted or heap physical output. Typed unboxing needs source scalar-kind compatibility; it cannot derive a scalar type from an object carrier.
*
  * Reset and retained reuse
  * Preserve token origin, ordinaryness and fitting physical extent through the facts-indexed protocol. Fresh, retained and empty-layout results need their actual branch-sensitive semantic kind; retained empty-layout results cannot be classified only from constructor arity.
*
  * Sharing test
  * A guard on the exact tested value may refine its semantic provenance only after proving the guard's interpretation. The proposed `isShared == false` heap refinement is a use of that semantic theorem, not an unconditional Boolean-to-pointer cast.
*
  * Named call
  * At ingress prove argument shapes at parameter kinds; derive precise parameter entry by {bpref "precise-call-entry"}[]. At result binding retain the callee's proved effective result and use its directional weakening for the caller's declared lane.
*
  * Partial application and closure capture
  * Store carrier and known provenance for each capture; erased captures keep their specified behavior. A capture's `i32` storage does not prove heap shape. Track target identity/arity and the compiler descriptor independently.
*
  * Saturated closure call
  * Recover candidate membership from closed-ingress origin, transport capture/argument semantic kinds, enter the chosen callee and publish its exact result. {bpref "closure-call-closure"}[] also needs the finite capture-retention contract.
*
  * Lazy cache hit and miss
  * Store the compiler-selected result carrier and preserve the same effective result evidence on both paths. A hit retrieves the existing physical result relation; a miss obtains it from the callee. Heap persistence/caller separation is the separate {ref "heap-caller-invariant"}[publication argument].
*
  * Contracted external
  * Obtain the result's semantic kind and heap/world behavior from the named primitive clause. A scalar/Nat/Int result-shape classifier alone does not establish the mathematical operation or arbitrary object/closure ingress provenance.
*
  * Branch selection
  * Preserve facts valid for the selected source branch and justify any branch-specific refinement of the discriminator. Object tags and UInt8 scalar cases retain different semantic and range arguments.
*
  * Join/jump
  * Bind actual incoming arguments to join parameters and combine information conservatively across every supported incoming edge. A precise fact may survive only when all incoming values establish it; unknown {name Fir.Wasm.AbiKind.tobject}`tobject` remains unknown.
*
  * Return and suspended callers
  * Check the exact active result use, then transport the result through the saved destination and restore the caller's row. Preserve root-function, active-join and caller contexts distinctly while the heap witness evolves.
:::

For a future provenance lattice, the conservative join rule would select a
sound common weakening. If incoming evidence is $`p_1,p_2` and the merged
evidence is $`p`, the intended soundness conditions are
$`p_1\preceq p` and $`p_2\preceq p`. This is a proposed analysis rule;
there is no associated lattice or fixpoint theorem in the current source.
A recursive declaration analysis must choose how summaries are computed and
prove their coverage and semantic soundness, rather than silently extend the
straight-line recognizer to arbitrary recursion.

Heap operation admission requires more than this local row. Projection,
mutation, deletion, ownership and reuse each state their semantic operand
requirement; helper signatures retain those semantic operands before erasure
to Wasm types. {name FirTalos.Concrete.ConstructorSchema.WitnessAgrees}`ConstructorSchema.WitnessAgrees` converts a known source slot
kind to the active concrete descriptor. It does not create that source slot
kind from a location. Packed mutation additionally needs coordinate, extent
and non-overlap preservation. These are {bpref "object-field-closure"}[] and
{bpref "scalar-field-closure"}[], with detailed subfamilies in the
{ref "admission-coverage"}[coverage map].

# Choosing the maintained interface

One route derives a canonical analysis from the currently checked program and
proves that its coverage and transfer laws suffice. Another makes the equivalent
fixed representation-safety property part of the compiler-produced checked
boundary. The latter requires explaining any change to accepted programs and
to the endpoint statement. The current carrier compatibility test alone does
not prove precise heap shape.

Neither route is a caller-selected provenance map, a future target execution,
or a certificate enumerating only the measured workload. We retain these
alternatives in the Blueprint before choosing formal stub signatures. A checked
proof of a revised endpoint must be reviewed as a statement revision.

The full three-axis descriptor is justified when several independent consumers
need it. The immediate consumer audit first checks whether residual validation,
successful source-step inversion, the current value relation, witness and
constructor schema already prove each branch. It introduces the smallest
missing producer/use fact only where there is a real gap. A single precise
return fact does not justify replacing every local and emitted descriptor.
Initialization must come from actual export-entry ABI/refinement data;
preservation must remain internal to the maintained relation. The finite-prefix
theorem ultimately quantifies over neither a caller-chosen provenance row nor
an arbitrary source invariant.

# Planned implementation slices and acceptance

The source plan's six slices remain a proposed implementation order, not
completed results or independent graph dependencies:

:::table +header
*
  * Slice
  * Reviewable completion criterion
*
  * Freeze transfer behavior
  * Cover all nine ordinary {name Fir.Wasm.AbiKind.object}`object`/{name Fir.Wasm.AbiKind.tagged}`tagged`/{name Fir.Wasm.AbiKind.tobject}`tobject` transfer combinations, retain negative unknown/tagged heap-operation cases, and preserve the HitScene boxed-Float partial capture and tagged-Nat cache regressions.
*
  * Introduce descriptors
  * Add the smallest carrier/provenance definitions alongside {name Fir.Wasm.AbiKind}`AbiKind`, with executable correspondences and elementary soundness laws. Compiler output is unchanged at this boundary.
*
  * Thread evidence
  * Replace internal local-kind use where needed at call/return/join/capture/dispatch boundaries; justify each summary and conservative merge. Preserve symbolic output and artifact digests where behavior is unchanged.
*
  * Move operation gates
  * Heap-sensitive gates consume explicit semantic requirements instead of ad hoc object-family compatibility checks.
*
  * Adapt W6
  * After the shared descriptor/signature contract lands, prove sound erasure and preservation through cache, closure, projection, ownership and reuse. The same producer/use rows feed {bpref "provenance-analysis"}[] and {bpref "provenance-preservation"}[].
*
  * Retire duplicated checks
  * Express result recovery as evidence, remove redundant refinement/carrier choices, and run HitScene, Flat, PrettyFormat, root, Talos and deterministic artifact gates on the final implementation.
:::

Acceptance requires explicit evidence before treating {name Fir.Wasm.AbiKind.tobject}`tobject` as heap;
ordinary compiler transfers compatible with upstream generic C calls; exact
heap/tagged information across named calls, captures, dispatch and lazy caches;
rejection of malformed scalar/object crossings; and unchanged successful
external-engine differentials. These are criteria for the proposed refactor,
not a claim that the current global provenance closure is proved.

The audit's source census, PA0 extraction history and exact negative/positive
fixtures remain in `docs/w6-source-admission-audit.md`. The carrier plan's
problem, model, evidence flow, W6 role, boundary rules, six slices and acceptance
conditions are all represented here. What remains open is the mathematics and
chosen maintained interface: canonical summary construction, recursive and join
soundness, richer source schema preservation and closed-ingress coverage.
Those open choices belong to the Blueprint argument, not an unfinished prose
migration.
