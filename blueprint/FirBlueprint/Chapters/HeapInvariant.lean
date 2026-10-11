import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Notation
import FirBlueprint.Chapters.W6
import FirTalos.ConcreteRetainedTransports
import FirTalos.ConcreteRegionTransport
import Fir.Wasm.Concrete.ReleasedBlockReuseCorrectness

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Heap construction and suspended callers" =>
%%%
tag := "heap-caller-invariant"
%%%

A call can allocate an object without disturbing the caller's values, yet its
return can change which objects the caller is allowed to reuse. A lazy
initializer illustrates the problem: caching its result makes the result's
owned graph persistent, while the suspended caller may retain a token for an
older ordinary cell. The heap invariant must justify both the new persistent
graph and the old token. This chapter explains how concrete representation,
historical caller facts and fresh-region separation fit together.

The associated declarations below use the accepted checkout and its official
Talos overlay. The saved-caller and stepwise construction successor at
`f6850d79f` is also described through cited source evidence. The
{ref "source-disposition-inventory"}[supporting evidence] records the exact
source contracts and dated implementation history behind this argument.

# The representation that the invariant maintains

There are three implementation layers: final impure LCNF execution, symbolic
Wasm lowering with a semantic runtime, and concrete linear memory. The
lowering argument chooses the control flow and semantic operands. Runtime
refinement then proves that concrete operations implement those operands.
Resident helper linking and binary encoding add later implementation arrows.
The selected successful-return contract is {bpref "return-post"}[] at the
export's exact ABI kind; construction of a heap-valued initializer does not
change that root index.

The original opaque-handle host interns semantic object-like values behind an
`i32` handle table, preserves aliases, reserves a sentinel and records a
structured fault. Its exhaustion is a target resource failure. W6's concrete
target instead relates source locations to linear-memory addresses through
proof-only metadata. The handle implementation remains a semantic comparison
layer; the concrete theorem must account for the memory representation itself.

The frozen concrete target is `wasm32-lean64`: addresses and object-like function
lanes are `i32`, while semantic {name USize}`USize` is `i64`. The source capture uses Lean's
64-bit data model. Changing its word semantics requires a different source
capture. Each constructor object or {name USize}`USize` slot occupies eight bytes; an
object word uses the low four bytes with zero upper bytes. Packed scalars start
after those slots. For object count $`o`, {name USize}`USize` count $`u` and source byte
offset $`b`, the scalar byte coordinate is

$$`32 + 8(o+u) + b`.

Every allocation has a 32-byte header: kind, flags, reference count and retained
allocation extent occupy its first four words; four auxiliary words describe
the object. Constructors retain tag and field counts; closures retain dispatch,
arity, capture count and capture-descriptor indices. Closure captures use
eight-byte slots with live bytes selected by their {name Fir.Wasm.AbiKind}`AbiKind`. Freed allocations
keep the canonical dead header so stale accesses produce structured faults.
`Fir/Wasm/Concrete/Layout.lean` remains the executable authority for offsets.

Zero is the erased or empty-token sentinel. Odd object words encode a 31-bit
immediate payload. Nonzero aligned words denote heap addresses. Larger source
tags can have persistent heap representations: their semantic value is still
tagged, and ownership must preserve tagged behavior. Pointer shape and source
heap provenance are therefore distinct.

:::definition "concrete-value-relation" (parent := "contracts") (owner := "w6") (lean := "Fir.Wasm.Concrete.ValueRel") (autoDeps := true)
For witness $`w`, ABI kind $`k`, physical Wasm value $`q` and source value $`v`,
$`V_w(k,q,v)` denotes the existing {name Fir.Wasm.Concrete.ValueRel}`ValueRel`. It fixes both representation and
semantic shape at the selected kind. Scalars retain their exact kind even if
two kinds share one Wasm lane; floating-point lanes relate raw bits. A generic
object-word carrier cannot supply the heap-sensitive fact needed by a
projection, mutation or retained reuse token.
:::

:::definition "concrete-heap-relation" (parent := "contracts") (owner := "w6") (lean := "Fir.Wasm.Concrete.LiveHeapRel") (autoDeps := true)
Write $`\mathcal H_w(m,r)` for {name Fir.Wasm.Concrete.LiveHeapRel}`LiveHeapRel` between concrete memory state $`m`, witness
$`w` and source runtime $`r`. Every source cell has a mapped concrete cell, and
every mapped source location exists. Live payload and canonical dead-cell
relations are distinct. Promoted tags have a separate relation.

The witness is well formed; source locations lie below {name Fir.LeanIR.Impure.RuntimeState.nextLocation}`nextLocation`;
descriptor intervals are readable, complete, aligned and pairwise disjoint
below the concrete frontier. The frontier supplies allocation and release-fuel
bounds. Descriptor ownership covers the full retained extent, not just the
header, so an ownership write can frame other decoded objects.
:::

{name Fir.Wasm.Concrete.ConcreteRuntimeRel}`ConcreteRuntimeRel` adds typed globals, equal world and the ordered
{name Fir.Wasm.Concrete.ConcreteTraceRel}`ConcreteTraceRel` to $`\mathcal H_w`. {name FirTalos.Concrete.StateRelated}`StateRelated` adds compiler-local representation
and environment agreement. The witness carries semantic-location mappings,
promoted tags, allocation descriptors and immutable closure tables. Allocation
can extend it; historical values must remain representable under the evolved
witness. None of these ghost maps is a second object encoding or a public
client certificate.

# What must survive a call

When the caller suspends, its local values are represented using a particular
heap and witness. The callee can allocate, update memory and produce a new
witness before those locals are used again. Restoring the caller therefore
requires a link from its saved representation to the current one. Rechecking
only the callee's current values would lose the reason that a saved reuse token
still names a suitable cell.

Publication makes this link more delicate. A retained token requires its
tracked cell to remain ordinary, meaning nonpersistent whenever the cell is
found. The initializer's new Array, in contrast, becomes persistent when it is
cached. We cannot demand that every location ordinary at entry remain ordinary:
a location absent at entry satisfies that conditional statement vacuously and
may later contain the persistent Array. The counterexample
`RetainedInitializer.example_not_blanketOrdinary`
([source](https://github.com/ejgallego/lean-fir/blob/340f4612ac622aa39d6a870528f96d6b827d97b8/integration/talos/retained-initializer/RetainedInitializer.lean#L560))
exhibits exactly this situation.

The transport law instead protects reuse facts represented at the saved
caller's anchor. Combined with the related initializer-entry heap, the saved
token representation identifies an existing source cell below that entry's
cursor. Fresh allocation and publication may then affect the new region while
preserving the older tracked cells. The law quantifies over every representable
saved row, rather than asking a client to choose a convenient collection of
tokens.

:::definition "retained-caller-transport" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.RetainedCallerTransport") (autoDeps := true)
For entry witness $`w_e` and source runtimes $`r_0,r_1`, the existing retained
caller law quantifies over every saved fact row $`F`, binding table $`\mathcal B`, fixed
caller environment $`E`, saved locals $`L`, memory $`m_h` and witness $`w_h`:

$$`\begin{aligned}
&\operatorname{FactsRel}(F,\mathcal B,E,L,m_h,w_h)\\
&\quad\land\ \operatorname{WitnessTransport}(w_h,w_e)\\
&\quad\land\ \operatorname{Ordinary}(F,r_0,E)\\
&\qquad\Longrightarrow\ \operatorname{Ordinary}(F,r_1,E).
\end{aligned}`

The premise ties a row to its historical representation and connects that
representation to the fixed entry witness. The implication preserves the
row's ordinary-token facts as execution changes the runtime. It may protect
more representable rows than occur on the actual stack; it permits fresh
objects to become persistent without permitting arbitrary old token cells to
be published.
:::

Ordinaryness is only one part of the saved evidence. It does not establish
that a cell exists or is live, that its reference count permits reuse, or that
its concrete allocation has enough room. The live heap relation and
{name FirTalos.Concrete.ReuseCapacityFactsRel}`ReuseCapacityFactsRel` supply the representation and capacity facts;
header-capacity transport keeps the required extent valid across the call.
Keeping these obligations separate allows publication to change persistence
without pretending that memory allocation or payload preservation follows from
ordinaryness alone.

:::theorem "retained-caller-composition" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.RetainedCallerTransport.trans") (autoDeps := true)
Suppose the first retained transport is indexed by $`w_0`, the next by $`w_1`,
and $`\operatorname{WitnessTransport}(w_0,w_1)`. Their composition retains the
original index $`w_0`. For each historical saved row, its transport to $`w_0`
is composed with $`w_0\to w_1`; both ordinaryness implications then apply to
that same row.
The result carries the same fixed caller environment across nested calls.
:::

The active scope records the remaining byte budget $`B`, current reuse facts
and exact ABI, together with transports from its original entry. A suspended
scope retains the caller's environment, locals, continuation and destination.
The inner scope starts at the actual call boundary, which is the endpoint of
the outer scope; its entry does not replace the outer historical anchor.

{name FirTalos.Concrete.RetainedCodeEntryTransports}`RetainedCodeEntryTransports` adds physical header-capacity transport,
closure-allocation persistence, immutable dispatch and capture tables, witness
transport, and the unchanged installed external implementation. Its
composition reconstructs the whole entry package. {name FirTalos.Concrete.RetainedCodeEntryTransports.afterLegacyFrame}`afterLegacyFrame` imports
an existing local operation proof and composes its result with the historical
entry transport. The local proof's reflexive entry does not replace the saved
caller's entry.

The central active and suspended resource scopes use this package. Named,
closure and lazy entry begin an inner scope at the actual call boundary;
{name FirTalos.Concrete.ConcreteStructuredResourceScope.restoreCaller}`restoreCaller` and {name FirTalos.Concrete.ConcreteStructuredBindFrameFocus.advance_popResourceStack}`advance_popResourceStack` compose back to the outer entry.
Historical stack projection uses the transported witness and current related
state to recover the saved facts. Target-only labels introduced by case tests
are unwound before a return consumes the corresponding source caller. Older
whole-declaration interfaces retain their stronger all-location ordinaryness
law; the facts-indexed law above explains how fresh publication can be handled
without that restriction.

# The fresh-region separation argument

Let $`r_e` be the initializer entry runtime and $`c` its next source heap
location. The cutoff $`c` stays fixed as the heap grows. At entry every existing
cell lies below it, so the region at or above $`c` is empty. The local operation
laws establish closure of this region as new cells are added.

:::definition "construction-region" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.HeapRegionClosed") (autoDeps := true)
For heap $`h`, write $`\FirClosed{c}{h}` for the existing predicate.
For all parent locations $`j`, cells $`x` and owned heap children $`j'`,

$$`c\le j\ \land\ h[j]=x\ \land\ j'\in\operatorname{owned}(x)
  \ \Longrightarrow\ c\le j'`.

This constrains outgoing owned edges of cells in the region. It makes no claim
about edges from older cells, future returned roots, or arbitrary initializer
programs. Entry initializes it because every existing source heap cell lies
strictly below $`c`.
:::

:::theorem "construction-region-reachability" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.HeapRegionClosed.reachable") (autoDeps := true)
If $`\FirClosed{c}{h}` and each heap root in a root list lies at or
above $`c`, every location reachable along owned edges from those roots also
lies at or above $`c`. The proof follows reachability induction. Sharing and
cycles are allowed; no acyclicity or traversal-fuel hypothesis is required.
:::

Allocation preserves closure when its new immediate owned children stay in the
region. A cell replacement requires that condition only when its target is in
the region. Array push needs the condition only for the appended owned value;
the old elements are already bounded. Metadata-only ownership updates reuse
{name Fir.LeanIR.Passes.ElimDead.HeapOwnershipFrame}`HeapOwnershipFrame`. Recursive persistence and {name Fir.LeanIR.Impure.RuntimeState.setGlobal}`setGlobal` preserve owned
edges, so they preserve any existing region cutoff.

These are producer obligations. ABI typing, ordinaryness transport and heap
representation alone do not prove that a new cell's children lie in the fresh
region. Tagged elements and a fresh empty Array give the required leaf/edge
facts in the checked initializer. A fixture with a shared String graph proves
reachability separation; it does not prove full reference-count accounting or
compiled execution of that fixture.

:::theorem "fresh-publication-separation" (parent := "construction") (owner := "w6") (lean := "FirTalos.Concrete.ReuseTokenPublicationDisjoint.of_freshRegion_of_witness") (autoDeps := true)
Let a saved caller's facts be represented under $`w_h`, and transport that
witness to the initializer entry witness $`w_e`. The related entry heap puts
each saved retained-token location $`\ell` below $`c`. Let $`h` be the
post-construction source heap. The value $`\FirHeap{\ell_0}` refers to the
returned source location $`\ell_0`, and $`\FirOwnedReach{h}{v}` follows owned
edges from $`v`, including its heap root. If $`\FirClosed{c}{h}` and
$`c\le\ell_0`, then

$$`\ell<c\le j\quad
  \text{for every }j\in\FirOwnedReach{h}{\FirHeap{\ell_0}}`.

Thus no tracked token location is reachable from the published result. The
proof derives publication disjointness from historical representation and
local construction; it does not ask the caller for a graph-separation
certificate, current capacity frame or re-created caller state.
:::

{name FirTalos.Concrete.RetainedCallerTransport.setGlobal_of_freshRegion}`RetainedCallerTransport.setGlobal_of_freshRegion` turns that separation into
the saved-fact transport. {name FirTalos.Concrete.RetainedCodeEntryTransports.publishFreshCache}`RetainedCodeEntryTransports.publishFreshCache`
combines concrete cache correctness, runtime/value refinement, capacity
transport and the surviving region with it. Its two global updates are store
expressions; executing their generated instructions is a further step.
The original entry witness must remain the publication index. Re-anchoring at
the current witness would protect the fresh result itself against persistence,
defeating the construction argument.

# From active construction to restored caller code

The active {name FirTalos.Concrete.ConcreteStructuredRegionCodeCore}`ConcreteStructuredRegionCodeCore` stores code focus, the resource
scope at the fixed entry and region closure. It chooses no future result root.
{bpref "construction-entry"}[] derives it from the real cache-miss entry and
installs the exact source cache/bind frames and target call/label continuation.
External staging and pre-bind states carry the same entry index through
[ConcreteStructuredRegionExternalCall](https://github.com/ejgallego/lean-fir/blob/340f4612ac622aa39d6a870528f96d6b827d97b8/integration/talos/FirTalos/ConcreteRegionExternal.lean#L9) and
[ConcreteStructuredRegionExternalBind](https://github.com/ejgallego/lean-fir/blob/340f4612ac622aa39d6a870528f96d6b827d97b8/integration/talos/FirTalos/ConcreteRegionExternal.lean#L34): argument staging leaves the heap
unchanged; host execution uses response refinement *and* a separate producer
region-preservation law; binding erases only the overwritten destination's
reuse fact and returns to active code.

At return, {name FirTalos.Concrete.ConcreteStructuredFreshYieldCore}`ConcreteStructuredFreshYieldCore` holds the represented heap
result, current entry-relative resource scope, region closure and fresh-root
bound. {bpref "construction-return"}[] derives the source return and the two
target instructions. Freshness remains a separate producer fact; an object
ABI alone does not show that its root was allocated by this initializer.
{name FirTalos.Concrete.ConcreteStructuredFreshYieldCore.of_body}`of_body` assembles the scope from actual operation transports and the entry
scope, rather than assuming a post-body scope.

Publication executes one source step and seven target steps: initializer
return, concrete {name Fir.Wasm.RuntimeOp.cacheSet}`cacheSet`, value/flag global writes, conditional exit and
value reload. {name FirTalos.Concrete.LazyCacheGlobalsRel.publicationFinitePath_of_compiler}`LazyCacheGlobalsRel.publicationFinitePath_of_compiler` derives
that path from the actual compiler/import/cache alignment for any result kind.
{name FirTalos.Concrete.ConcreteStructuredResourceScope.afterCachePublication}`afterCachePublication` restores saved facts, cache tables, external contracts,
remaining allocation budget and closure ABI. {bpref "publication"}[] attaches
saved residual validation and the original export result index to reach the
existing rooted global pre-bind outcome. The final source bind and target
`local.set` restore caller environment, joins, continuation and suspended tail;
only the destination's old reuse fact is removed.

The retained RC2 initializer is a useful complete consumer of these rules.
The {ref "worked-retained-initializer"}[worked proof] follows its caller,
construction and publication states, with exact retained premises and the
separate thirteen- and fourteen-step conclusions.
Its actual body is two literals, empty Array allocation, UInt8 boxing,
fresh non-full tagged push and return. `body_returns` ([source](https://github.com/ejgallego/lean-fir/blob/340f4612ac622aa39d6a870528f96d6b827d97b8/integration/talos/retained-initializer/RetainedArrayCalls.lean#L620)) derives ten source
steps and the corresponding target path. The complete validated/rooted let
theorem derives fourteen source steps through staging, cold entry,
construction, publication and destination binding back to caller code.
Allocation is the five-slot Array extent; UInt8 boxing and this push branch
consume zero physical bytes. Neither source execution, target path, callee
package, post-body scope nor the five binding-kind lookups is a client premise.

Its remaining inputs are the supported caller/current relation, actual
initializer identity, cold cache, uniform source Array primitive laws,
installed handler conformance and finite headroom. The handler laws describe
the canonical concrete allocator and fresh/non-full push branch. They do not
execute a W7 resident helper or establish production JavaScript conformance.
[RetainedRC2.program](https://github.com/ejgallego/lean-fir/blob/340f4612ac622aa39d6a870528f96d6b827d97b8/integration/talos/retained-initializer/check.sh) is kernel-retained input from exact source objects; it is
not a copied AST, old olean or substituted capture. The reproduce script and
per-endpoint trust inventories stay with `integration/talos/retained-initializer/`.

## Keeping the caller through construction

Local binding must preserve the construction region and the facts saved at
the original caller anchor. The reviewed successor at `f6850d79f`, included
in source checkpoint `8f4222cb2`, makes literals and UInt8 boxing use
[ConcreteStructuredRegionCodeCore.afterLocalBind](https://github.com/ejgallego/lean-fir/blob/8f4222cb2/integration/talos/FirTalos/ConcreteRegionCode.lean#L47) and gives empty allocation,
push staging, host execution and binding explicit region-indexed intermediate
states. Generic local binding supports arbitrary retained fact rows at the
original anchor. This removes the need to reconstruct closure/scope after the
six-step prefix or either Array block.

[ConcreteStructuredFreshLazyFrame](https://github.com/ejgallego/lean-fir/blob/8f4222cb2/integration/talos/FirTalos/ConcreteFreshLazyFrame.lean#L30) now packages the saved validated caller,
root agreement and generated publication continuation. Staging creates it;
cold entry pairs it with active construction; fresh return and publication
consume the same frame. The actual source cache/bind and target call/label
stack equations are evidence about the installed continuation. The frame
contains no promise that all future callee results will be fresh.
`rootedLet_publishesAtBind` ([source](https://github.com/ejgallego/lean-fir/blob/8f4222cb2/integration/talos/retained-initializer/RetainedArrayCalls.lean#L1016)) exercises this path in thirteen source steps and
rejoins the rooted global relation at the pending destination bind. These
results are cited source evidence; their names are not new associations in
this Blueprint's accepted import environment.

The saved caller now stays with the construction through each push phase.
Local source `eab5934684a9252f797b73b0c83e87da67d749de`, reviewed on
2026-10-11 and awaiting integration into FIR, replaces the lifted push
block in `framed_body_returns` with explicit staging, host-call and bind states.
`stageExternal`, `pushFreshTaggedEvidence`, the zero-cost `advance_call` and
`bind.advance` retain the same saved validated caller, original export ABI and
original construction anchor. The body's ten-step conclusion and client
premises are unchanged. This is cited local source evidence, not a new
association in the Blueprint's accepted import environment.

The thirteen-step `rootedLet_publishesAtBind` proof consumes this revised
framed body. The fourteen-step `rootedLet_publishes_and_resumesCaller` theorem
retains its legacy `validatedLet` proof route and unchanged conclusion, with
no separate closure conjunct. The new generic push evidence uses the standard
axioms and the existing byte-assembly axiom dependency. The retained
framed-body consumer keeps its prior exact inventory of standard axioms plus
eleven generated axioms. This local result does not close resident linking or correctness of
the whole Stored export.

The central object/tobject restriction in {bpref "lazy-miss-boundary"}[] is
still present. {bpref "heap-miss-closure"}[] must carry the saved frame and
active construction evidence through the *general* intermediate-state
dispatcher, including nested calls, then derive current admission at the
actual consumer. A completed block endpoint does not establish that closure
at every intermediate state.

## Freshness is one publication policy

The fresh-region argument is sufficient, not necessary. A legitimate
initializer can return an older persistent value. General admission therefore
needs an explicit result classification: fresh closed graph with its original
cutoff, already persistent represented result, or another supported producer
whose ownership/publication law proves preservation of saved tokens.
An arbitrary older ordinary object can reach a saved token, so it needs a real
ownership/separation argument. External object results need explicit result
provenance and region/ownership effects from the primitive contract.

Nested calls must preserve the outer construction evidence at the outer
cutoff while tracking their own entry scopes. Capturing a future result
assertion in every saved frame would assume the behavior being proved.
The open choice is the smallest maintained relation/result classification that
covers accepted heap initializers without rejecting older persistent sharing.
This is a theorem-interface design obligation, not permission to remove the
backend exclusions ahead of their closure proof.

# Released physical blocks and witness retirement

Retained constructor {name Fir.Wasm.RuntimeOp.reset}`reset`/{name Fir.Wasm.RuntimeOp.reuse}`reuse` and allocator released-block reuse have
different witness obligations. The former keeps a represented retained token
and checks its fitting layout. The latter returns a canonically released
physical address for a new source location. Its generic allocator contract
exists, but whole-machine attachment remains open.

:::definition "released-block-contract" (parent := "construction") (owner := "w6") (lean := "Fir.Wasm.Concrete.ReleasedBlock.Valid") (autoDeps := true)
A reusable block $`(a,n)` is a complete canonical dead allocation with exact
retained extent $`n` and $`a+n` below the frontier. Its header has freed kind,
nonpersistent/nonlive flags and zero reference count. Payload bytes are
unconstrained while dead. A valid abstract index has unique entries and
pairwise disjoint extents.
:::

The abstract allocator takes the first exact aligned-size match, unlinks it
once, and preserves valid disjoint remainder; absence of a match follows the
existing bump/grow/overflow path. Rewind clears the index or filters complete
extents below its effective checkpoint, after applying the persistent-cache
floor. {name Fir.Wasm.Concrete.MemoryState.allocateReusing_spec}`allocateReusing_spec`, {name Fir.Wasm.Concrete.ReleasedBlockIndex.TakesExact.remainingValid}`TakesExact.remainingValid`, rewind filtering,
{name Fir.Wasm.Concrete.MemoryState.ReusableAllocatePost.addressSpaceBudget}`ReusableAllocatePost.addressSpaceBudget` and initialization of a released
block provide the generic proofs. Rewound memory has a weaker allocator
invariant than the monotone zero-suffix {name Fir.Wasm.Concrete.MemoryState.FrontierInvariant}`FrontierInvariant`: reused or rewound
allocations must initialize every logically readable payload component before
source-visible exposure.

The W7 implementation contract is six source-shape facts: offer only after
canonical release; select an exact extent and unlink uniquely; keep list
metadata private in ignored dead payload; initialize before exposure; invalidate
on rewind; and preserve the fallback and ABI. List heads, buckets, link encoding
and search details stay implementation choices. The production attachment
module `ConcreteResidentReleasedBlockReuse` records generated source equations
and semantic extents. Its legacy [ResidentAllocatorRel](https://github.com/ejgallego/lean-fir/blob/340f4612ac622aa39d6a870528f96d6b827d97b8/integration/talos/FirTalos/ConcreteResidentAllocator.lean#L25) describes the empty
reuse-index bump subrelation because it equates every memory byte. A nonempty
index needs an indexed/masked representation and an instruction-execution
proof, even when generated source shapes already match.

:::theorem "released-address-retirement" (parent := "frontier") (owner := "w6") (tags := "open, statement-review") (uses := "concrete-heap-relation, released-block-contract")
Construct a structured-runtime witness transition that retires an unreachable
canonical dead, zero-reference source location before rebinding its physical
address to a distinct new location. Unreachability must cover environments,
globals, live owned fields, suspended frames and foreign roots. Preserve the
public stale-reference fault theorem for arbitrary source states.
:::
:::proof "released-address-retirement"
The checked {name Fir.Wasm.Concrete.RefinementWitness.WellFormed.reusedAddress_requires_sameLocation}`RefinementWitness.WellFormed.reusedAddress_requires_sameLocation`
states that two mappings to one physical address in the same well-formed
witness imply equal source locations. Keeping the old dead mapping while
binding a new source location is therefore impossible. Derive unreachability
from ownership, remove only the justified dead mapping, then prove the heap
and value relations after full initialization. A generation-aware relation is
an alternative design; the smaller proposed route matches source ownership.
The retirement transition and its historical-witness transport policy remain
to be specified. In particular, current {name FirTalos.Concrete.WitnessTransport}`WitnessTransport` quantifies over
*every* represented value, not only the live values reachable from actual
frames. Removing a remembered dead mapping does not automatically preserve
that universal law. A retirement-aware simulation would need a justified
transport restricted to its live/retained roots, or a generation policy that
distinguishes the old address interpretation from the new one. Either route
must prove that each active and historical consumer still receives the
representation transport it needs. This is an open relation choice; weakening
the arbitrary-state stale-reference contract would not resolve it.
:::

`FIR-BUG-wasm-none-resident-arena-released-block-reuse` records this boundary.
Generation readiness, generic allocator correctness, generated-helper
execution and structured witness retirement are separate claims. After W7's
exact helper checkpoint, W6 relates release/selection/unlink/initialization/
rewind/fallback bodies, proves retirement and rebinding, then integration
composes them with the consumer theorem and artifact checks.

# Scope and source dispositions

The early PLAN work breakdown is the implementation history behind the current
argument. Its obligations are retained by topic:

:::table +header
*
  * Source topic
  * Blueprint destination and disposition
*
  * W0 ABI; two-level types; wasm32-lean64 layout
  * Representation above and the {ref "provenance-design"}[provenance argument]; executable layout/signature code remains authoritative.
*
  * W1 checker and adapter; validation ownership
  * {bpref "supported-export"}[] and the {ref "admission-coverage"}[branch inventory]. FIR checks its generated subset, including names, locals, labels, stack kinds, calls/imports, initializers and return shape; Talos validation is an additional executable check.
*
  * W2 host codec/handles; W3 differential harness
  * Semantic comparison host above; lowering/runtime claims stay distinct from empirical engine checks. Corpora, repros and transcripts remain source evidence.
*
  * W4 lowering; W5 closures and lazy caching
  * {bpref "rooted-steps"}[], the {ref "admission-coverage"}[call/case/cache families] and the caller/publication argument here. Proof histories remain historical.
*
  * A0 artifacts; W7 generation/linking milestones
  * {bpref "resident-linking"}[] and later encoding/import closure; deterministic artifacts and engine gates remain executable evidence, not semantic proof nodes.
*
  * W6 runtime slices; W6.7 completion ladder
  * Heap/value/caller invariants here, {ref "admission-coverage"}[operation subfamilies], and {bpref "admission-closure"}[] to {bpref "closed-export"}[]. The long dated slice record is retained chronology.
*
  * Current frontier and next meaningful result
  * Fixed-entry construction, accepted saved lazy frame, publication policies and the explicit {bpref "heap-miss-closure"}[] gap above; newer main review is dated separately.
*
  * Released-block contract and production order
  * {bpref "released-block-contract"}[] and {bpref "released-address-retirement"}[]. The source contract retains exact implementation/source-shape evidence.
:::

Closures use a generated Wasm trampoline: metadata tests choose a statically
enumerated target, typed projections load captures, underapplication allocates
more captures, and saturation executes an ordinary direct Wasm call. Host
callbacks cannot invoke the Wasm-defined target, and delegating to the source
interpreter would assume lowering correctness. Closed-ingress candidate
membership, including initial data and external closure ingress, remains part
of {bpref "closure-call-closure"}[]; capture retention also has finite capacity.

Lazy globals belong only to called zero-argument declarations: one mutable
flag and one result lane per declaration. Misses evaluate then publish; hits
reload. There is no eager-start proof obligation hidden in this argument.

# Resident memory and observations
%%%
tag := "resident-observation-bridge"
%%%

The October 5 source review at main `8f4222cb2` includes the resident boundary
identified in `f6850d79f`. The current {name FirTalos.Concrete.StateRelated}`StateRelated` and successful-return
simulation read `store.host.runtime`; helper body proofs instead use
[ResidentMemoryRel](https://github.com/ejgallego/lean-fir/blob/8f4222cb2/integration/talos/FirTalos/ConcreteResidentMemory.lean#L23) to relate the concrete model heap to `store.mem`. Proving
the helper's memory/result behavior does not replace the former relation with
the latter. `ResidentReplacement.externalLetStepSimulates_of_definedCall` ([source](https://github.com/ejgallego/lean-fir/blob/8f4222cb2/integration/talos/FirTalos/ConcreteResidentReplacement.lean#L53))
still requires the post-state {name FirTalos.Concrete.StateRelated}`StateRelated` premise, so its conditional
defined-call theorem does not discharge this representation bridge.

Source Array external resumption appends an event. Any resident execution that
preserves `store.host` retains its old trace length, while the source trace is
one longer. [ConcreteResidentBoundaryTests](https://github.com/ejgallego/lean-fir/blob/8f4222cb2/integration/talos/FirTalos/ConcreteResidentBoundaryTests.lean) proves that the required successor
state relation and exact prefix-observation relation are then impossible,
even with a different witness, independently of heap/result representation.
The negative proofs do not execute or postulate any particular helper.
`FIR-BUG-wasm-none-resident-host-observation-boundary` records the exact
obstruction and reproductions. These tests are cited as reviewed source
evidence, rather than fresh execution receipts for this documentation build.

Two open shared-semantic designs are erased ghost instrumentation with a
proved execution projection to deployed Wasm, or an explicit product-observation
projection with its corresponding simulation. Either requires memory
refinement as well as an account of observable events. Ghost host updates
cannot be assumed to occur in actual instructions, and the source events or
{name Fir.Wasm.Concrete.ConcreteTraceRel}`ConcreteTraceRel` cannot be weakened locally to remove this boundary.
Actual empty-Array allocation and non-full unique-push helper body proofs can
advance independently; they still cannot establish the unchanged host
post-state premise for this trace-producing source call. The bridge is a
consumer obligation of {bpref "resident-linking"}[]. Binary encoding, exact
artifact identity and application decoding remain separate later arrows.
