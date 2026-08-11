# Interpreter semantic-fidelity roadmap

This roadmap turns the validation lane's broad interpreter-validation goal into
a prioritized semantic portfolio. Lean's logical memory lifecycle remains the
dominant near-term track, but calls and control, effects and termination,
floating-point computation, and aggregate/initialization behavior are explicit
tracks rather than unmeasured future work. Lean native execution remains the
semantic oracle, final LCNF provides the compiler-path witness, the LCNF
interpreter provides exact dynamic execution evidence, and compiler-generated
Wasm runs in a real engine when the corresponding W7 surface is linked.

The memory track validates logical allocation, ownership, and release. It does
not compare physical allocator addresses or require native, LCNF, and Wasm to
use the same heap layout. The adjacent tracks likewise compare portable Lean
observations, not backend accidents such as native stack addresses, JavaScript
exception text, or allocator identity.

## Portfolio

| Track | State | Scope | Immediate move |
| --- | --- | --- | --- |
| A Memory fidelity | active, primary | Allocation, retain/release, alias topology, mutation, copy-on-write, reuse, and persistence | Start S5 recursive release/reuse from the landed S4 transfer baseline |
| B Calls and control | active through A/B bridge | Application shapes, tail calls, recursion, branch topology, and depth behavior | Schedule B2 application shapes while preserving S4/B1 |
| C Effects and termination | queued | Ordered external effects, output, caught/uncaught exceptions, runtime faults, exits, and controlled divergence | Add an ordered-effect boundary pair, then queue the shared source-error contract |
| D Floating semantics | contract-blocked | Bit-exact entry/result transport, arithmetic, comparison, conversion, NaNs, infinities, subnormals, and signed zero | Resolve `FIR-BUG-wasm-none-float-runtime-gap` in the shared runtime before execution fixtures |
| E Aggregates, erasure, and initialization | queued | Inductive shapes, erased fields, polymorphic dictionaries, arrays, constants, caches, and initialization order | Add a compact source-generated aggregate/erasure pair without duplicating direct-machine reset tests |
| X Evidence and real-engine promotion | continuous | Exact traces/counts, semantic domains, native attestations, retained products, and V8 execution | Promote a representative pair from every eligible track |

Memory remains the default source of new fixture slices. The other tracks enter
the queue when they close a structurally different blind spot, not to construct
another exhaustive scalar matrix.

## Coverage gap snapshot

At the current 651-case source checkpoint, case counts are concentrated in
scalar and pure-external behavior: 413 cases are tagged `scalar`, 302 `signed`,
305 `external`, and 146 `arithmetic`. In contrast, only 25 are tagged
`constructor`, 12 `control-flow`, three `effect`, five `recursion`, three
`tail-control`, two `tail-ownership`, and one `polymorphism`. The two float-tagged cases preserve
captured `Float32`/`Float` words but return non-floating observations; they do
not validate floating computation.

The semantic protocol can represent returned values, exceptions, exits,
runtime faults, and divergence, but the native and V8 source adapters currently
produce only returned observations. Overapplication is covered by two
direct-machine cases rather than a source-generated native/LCNF/V8 triangle,
and `reset`/`reuse` execution is likewise confined to the direct-machine tier.
These are portfolio gaps even though all current instruction-form, tag, and
conjunctive-domain floors are green.

## Executable plan map

| Plan | Role | Selection invariant |
| --- | --- | --- |
| `native-lcnf.json` | Primary source/native-oracle comparison | Every source case, including cases not yet admitted to Wasm |
| `direct-lcnf.json` | Source-unreachable machine-state comparison | Handwritten direct cases only; `direct-native` is its machine oracle |
| `native-lcnf-v8-scalars.json` | Real-engine triangle | Every case not tagged `wasm-generation-pending`; all three native/LCNF/V8 edges are retained |
| `native-oracle-attestations.json` | Offline oracle policy | Complete equal `native -> lcnf` and `native -> v8` edges over the same selected case set |
| `coverage-index.json` | Cross-tier regression ratchet | Exact tier, aggregate, machine, tag, and conjunctive-domain floors |

The `-scalars` suffix on the V8 plan and its provider/adapter files is
historical: the plan currently selects all 651 eligible cases, not a scalar
subset. Rename those root-wired assets through the integration owner rather
than creating a second semantically identical plan in this lane.

Every admitted slice updates its executable ratchets atomically:

1. Add the cases, exact final-LCNF obligations, and executed traces/counts.
2. Raise tier, aggregate, interpreter-step, and native-oracle case floors for
   every newly eligible case.
3. Add a tag floor and at least one conjunctive domain for the distinguishing
   semantic claim; case-count growth alone is not acceptance.
4. Add matching source and V8 domains in the same slice when the W7 surface is
   linked. Otherwise retain the explicit pending fence without claiming V8
   coverage.
5. Do not add a policy floor for a contract-blocked track until the contract
   and its first witness case land together.

The initial domain vocabulary for the next slices is fixed here to prevent
near-synonym drift:

| Slice | Distinguishing tags | Required initial domains |
| --- | --- | --- |
| S2 | `closure-ownership`, `multiplicity`, `zero-use`, `three-use`, `unique-final-application`, `shared-intermediate-application` | `closure-ownership-zero-use`, `closure-ownership-three-use`, `closure-ownership-unique-final`, `closure-ownership-shared-intermediate` |
| S3 | `capture-alias-topology`, `repeated-capture`, `outside-alias`, plus the consumer action | `capture-topology-repeated`, `capture-topology-outside-alias`, and one action-sensitive domain |
| S4/B1 | `tail-control`, `tail-ownership`, `unique-transfer`, `shared-retain` | `tail-ownership-unique-transfer`, `tail-ownership-shared-retain` |
| S5 | `release-fidelity`, `recursive-release`, `repeated-child-alias`, plus the release stop boundary | `recursive-release-repeated-child`, `recursive-release-repeated-child-unique`, `recursive-release-repeated-child-shared-owner` |
| B2 | `application-shape` plus `nullary`, `underapplication`, `overapplication`, or `returned-closure` | One domain per admitted application shape |
| C1 | `effect`, `ordered-effect`, `call-boundary`, `alias-across-effect` | `effect-call-order`, `effect-alias-retention` |
| E1 | `aggregate`, `erasure`, and the exercised construction/case/projection action | `aggregate-erasure` and one result-shape domain |

## Track A: memory-fidelity progress

| Milestone | State | Current checkpoint | Next acceptance step |
| --- | --- | --- | --- |
| M0 Mixed closure baseline | landed | `mixed-closure-capture-once` and `mixed-closure-capture-twice` pin 36 and 62 interpreter transitions and pass the native/LCNF/V8 triangle | Maintain the landed baseline while later slices reuse its mixed capture shape |
| M1 Ownership coverage ledger | active | Existing coverage distinguishes unique/shared, copy-on-write, recursive release, and closure multiplicity | Add lifetime-operation, alias-shape, and observation-strength domains with each fixture slice |
| M2 Closure/capture ownership | landed | S2, S3a, and S3b are on `main`; S3b adds ByteArray and allocated constructor/String ignore-versus-read pairs with repeated captures and outside aliases, pinning 24/30 and 36/44 transitions | Carry the landed alias shapes into S4 tail-call ownership |
| M3 Tail-call ownership (A/B bridge) | landed | `local-tail` supplies the control baseline; S4 adds a nested ByteArray owner whose unique path executes three in-place outer updates while its outside-aliased path allocates once and then reuses twice, with exact 121/126-step traces | Maintain the landed pair while S5 varies recursive release/reuse |
| M4 Allocation and reuse | active through S5 | Constructor, String, ByteArray, reset/reuse, growth, and copy-on-write fixtures already provide a base | Use the first S5 pair to distinguish post-release constructor reuse from shared-path allocation |
| M5 Recursive release | active, primary | S5a and S5b are landed; repeated-child-alias unique release versus shared-owner stopping complements the direct LCNF anchors for repeated aliases and persistent owners | Use the coverage model to choose the smallest undominated retained-capacity or grow/delete pair |
| M6 Nonlocal control | queued | External yield/bind and ordered effects are observable | Carry owned aliases across an external suspension; add caught exceptions only after their shared protocol lands |
| M7 Real-engine promotion | continuous | Scalar closures, the complete zero/one/two/three-use matrix, and all returned/consumed/ignored/read capture-topology pairs run through native/LCNF/V8 | Promote at least one representative pair per ownership domain whenever W7 support is linked |

States are `queued`, `active`, `prepared`, `landed`, `parked`, or
`contract-blocked`. A prepared slice is committed and locally validated but
still waits at a named cross-lane boundary. A contract-blocked track has no
fixture or coverage-floor work in flight. A milestone becomes landed only
after its fixture commit is on `main` and every eligible case has passed its
required backend triangle.

## Coverage model

Use the existing case tags and conjunctive coverage domains to cover a compact
cross-product of these axes. Do not construct the full Cartesian product.

- Lifetime operation: allocate, retain, release, reuse, and persist.
- Owner state: unique, shared, and persistent.
- Alias graph: one owner, an independently retained alias, the same child in
  multiple fields or captures, a nested chain, and a shared DAG.
- Consumer behavior: ignore/drop, borrow/read, return/transfer, and
  consume/mutate.
- Boundary: closure application, tail call, constructor reset/reuse, external
  yield/effect, return, and eventually caught exception.
- Heap kind: constructor, String, ByteArray, large Nat/Int, and floating box.
- Observation: surviving-alias contents, copy-on-write, returned aliases,
  ordered effects, exact ownership facts, exact dynamic form counts, and exact
  execution traces.

Prefer pairs in which one program takes an ownership-sensitive path and the
other avoids it. Use pairwise coverage to vary one or two axes at a time, and
add a coverage requirement for the distinguishing conjunction.

## Per-fixture acceptance

Every source-generated semantic-fidelity fixture must satisfy the applicable
requirements below.

1. Native Lean supplies the result, ordered effects, failure, and output
   observation. No expected semantic result is substituted for the oracle.
2. The source and dependency list are small enough that the targeted semantic
   path is identifiable in final LCNF.
3. Required final-LCNF forms prove the compiler retained the intended path.
4. Exact executed form/external traces and exact relevant multiplicities prove
   the interpreter executed the control, allocation, call, ownership, effect,
   termination, or aggregate operations being claimed.
5. The returned value, termination, output, or ordered effect makes the
   semantic mistake observable. Copy-on-write and retained aliases remain the
   preferred memory observations.
6. Native ownership or compiler-fact attestations are added when generated
   facts, rather than only semantic behavior, form part of the claim.
7. The case runs in V8 after the W7 compiler surface and W6 contract for that
   feature are linked. Until then it carries the existing explicit pending
   fence and does not inflate V8 coverage.
8. The same slice raises the executable case/step/oracle ratchets and adds a
   tag floor plus a conjunctive domain for its distinguishing claim.
9. A new value, result schema, effect, or termination kind consumes a linked
   shared contract; it is never approximated by an existing observation.
10. Any semantic discrepancy receives a bug card before a workaround or model
    accommodation is introduced.

## Planned fixture slices

### S1: outside-alias ByteArray capture

State: `landed` and real-engine validated on `main`.

Pair a closure that borrows a captured ByteArray with a closure that consumes
and mutates it through `ByteArray.set!`. Both retain the original ByteArray
outside the closure. The mutation case must therefore allocate a copy and
return both the unchanged outside alias and the updated result. Pin `pap`,
closure invocation, capture projection, increment/decrement, external dispatch,
constructor return, and exact ordered traces.

Both cases pass native Lean, the LCNF interpreter, and V8. Concrete-product
execution remains outside this fixture slice because the concrete consumer
still treats initial-runtime ByteArray layout and the `ByteArray.get!`/
`ByteArray.set!` external registrations as blocked.

This slice uses the existing ByteArray protocol and does not depend on argument
alias materialization or the effect-wrapper contracts.

### S2: closure-use multiplicity

State: `landed` and real-engine validated on `main` at `c9b80cd7`.

The same-closure matrix now covers zero, one, two, and three uses. Final LCNF
retains a real four-box `pap` in the zero-use case and releases it without
executing any closure-body unbox/constructor/write form. The three-use case
executes two shared intermediate applications and one unique final application.
Exact traces pin 14, 36, 62, and 87 interpreter transitions across the matrix;
matching source and V8 tag/domain floors prevent any use-count or ownership
path from disappearing. All four cases pass native Lean, LCNF, and real V8.

### S3: capture alias topology

State: S3a is `landed` and real-engine validated on `main` at `eacdd3bd`;
S3b is `landed` and real-engine validated on `main` at `f997949f`.

Compare one captured heap object with the same object captured in multiple
slots, then retain an independent alias outside the closure. Cover callees that
ignore, read, return, and consume/mutate the capture. Use constructor, String,
ByteArray, large Nat/Int, and floating boxes as pairwise representatives rather
than repeating a scalar matrix.

The first vertical slice uses one closure with the same `ByteArray` in two
capture slots and a third alias retained by its caller. A Boolean-controlled
pair returns both captures unchanged on one path and consumes/mutates the
second capture on the other. Both observations return the outside alias, the
first captured alias, and the second result, so an incorrect retain, release,
or copy-on-write decision is visible. Exact final-LCNF traces must prove the
repeated capture, partial application, branch choice, returned-alias path, and
consuming external path actually execute. The already-landed single-capture
outside-alias mutation remains the one-slot comparison point.

The landed pair passes native Lean, the LCNF interpreter, and real V8. The
returned path pins 22 interpreter transitions and zero `ByteArray.set!`
dispatches; the consumed path pins 27 transitions and exactly one dispatch.
Both execute a real `pap`, `fvar` closure invocation, Boolean branch, and two
result constructors.

S3b adds two ignore-versus-read pairs without widening a shared contract. The
first partially applies the same `ByteArray` into two fixed slots while its
caller retains a third alias. One branch returns the first capture and drops
the second; the other borrows the second through `ByteArray.get!` and returns
the observation beside both surviving aliases. The second pair constructs a
small two-object-field constructor containing a large `Nat` and a `String`,
repeats it across the same capture/outside shape, and distinguishes dropping
the second capture from projecting its `Nat` field. Exact traces retain and
execute real `pap`/`fvar` closure paths, the ignored-capture release, and the
read-specific external or projection.

The ByteArray ignored/read cases pin 24 and 30 transitions respectively. The
ignored path executes one `dec` and no external; the read path executes
`ByteArray.get!` and `UInt8.toNat` exactly once each. The allocated constructor
ignored/read cases pin 36 and 44 transitions. Both construct and retain the
nested object, while only the read path executes `oproj`, `isShared`, and its
join/jump ownership branch. All four agree across native Lean, LCNF, and real
V8. The 645-case snapshot raises the aggregate floor to 654 unique cases,
1,944 comparisons, 6,184 interpreter steps, 98 tag floors, and 209 conjunctive
domains, with no finding.

### S4: tail-call ownership

State: `landed` and real-engine validated through functional head `2f93f54e`;
consumes the landed S3 alias vocabulary and changes no shared contract.

The existing `local-tail` fixture proves that a compact source-level
tail-recursive list worker agrees across native Lean, final LCNF interpretation,
and real V8.  It pins four calls, four case selections, six projections, and an
exact 31-step interpreter trace.  This is control-flow coverage, not yet
memory-fidelity coverage: final LCNF executes ordinary `fap`/return frames, the
fixture carries no ownership-sensitive heap accumulator, and the coverage
policy has no tail-ownership domain.

The first slice uses a two-object-field owner containing a `ByteArray` and a
`String`. A three-iteration tail-recursive worker updates ByteArray positions
two, one, and zero through `ByteArray.set!`, then transfers the updated owner
directly into the next self call. The unique entry returns only the final owner.
The shared entry retains the original owner outside the worker and returns it
beside the final owner, forcing copy-on-write on the first update while later
iterations may reuse the transferred replacement. Native results expose the
unchanged outside alias and final bytes. Pin exact call, increment, decrement,
projection, mutation, allocation/reuse, branch, external, and return counts,
and require dedicated `tail-control`, `tail-ownership`, `unique-transfer`, and
`shared-retain` coverage domains.

The compact pair is admitted through native Lean, the final-LCNF interpreter,
and real V8 with no finding. Both paths execute 19 applications, three
`isShared` decisions, and exactly three ordered `ByteArray.set!` calls. The
unique-transfer path pins 121 interpreter transitions, one `inc`, four `dec`,
one `ctor`, and three `oset` updates. The shared-retain path pins 126
transitions, four `inc`, five `dec`, three `ctor`, and two `oset` updates: its
first update allocates the replacement while the next two reuse the transferred
owner. Exact complete form and external traces retain all four termination
checks and three recursive decrements as well as the ownership distinction.
The coverage snapshot rises to 647 source cases, 656 aggregate unique cases,
1,950 comparisons, 6,431 interpreter steps, 106 tag floors, and 215 semantic
domains.

Keep semantic validation and the W7 transform claim distinct.  The compact
pair runs through native/LCNF/real-V8 using the ordinary validation provider.
A separate large-depth artifact probe checks that W7's optional direct
self-tail-call rewrite actually ran, remains stack-safe, reinitializes locals,
and preserves the same native observation.  Mutual tail recursion and effects
before a tail call are later extensions; the latter belongs with S6 nonlocal
control.

### S5: recursive release and reuse

State: S5b landed on `main` through `e47139b6`; changes no shared contract.

Cover repeated child aliases, nested unique release, shared-child recursion
stopping, persistent owners, erased/scalar neighbors, same-size reuse, retained
capacity, and grow/delete/allocation. Make release order observable through a
surviving alias, later copy-on-write, or a reuse decision, and pin exact
`project-dec`, `dec`, `reset`, `reuse`, `del`, `oset`, and `setTag` counts.

The first compact pair mirrors—but does not duplicate—the audited direct-machine
nested-reset law. Source construction creates an owner with an erased proof
field, a unique child, and a retained leaf. Replacing the owner must recursively
release the unique child, decrement the retained leaf to exclusive ownership,
and let a later leaf update reuse its storage. The paired program retains the
child outside the owner, so owner release must stop at that shared child;
returning the child while updating its leaf then forces allocation and preserves
the original leaf contents. Both return the owner replacement so the compiler
cannot discard the release-producing call.

Require final-LCNF execution evidence for owner reuse, recursive decrement,
the shared stop boundary, and the later reuse-versus-allocation decision. The
returned replacement, surviving child, and updated leaf make over-release or
incorrect copy-on-write observable. The exact dynamic path catches a leaked
reference even when allocation identity is not part of portable Lean results.
The existing opt-in direct native-IR attestations remain the native ownership
fact anchor; this fixture slice adds no orchestration or recorder surface.

The compact pair now passes native Lean versus final LCNF and the full
native/LCNF/real-V8 triangle with no finding. The unique case pins a complete
63-step trace with two increments, two decrements, four constructors, and two
reuse writes. The shared-stop case pins a complete 69-step trace with five
increments, three decrements, six constructors, and one reuse write: the leaf
update takes the allocation branch while the returned child preserves its
original leaf. Both execute exactly one ordered `Nat.add` external. The
coverage snapshot advances to 649 source cases, 658 aggregate unique cases,
1,956 comparisons, 6,563 interpreter steps, 116 tag floors, and 221 semantic
domains.

#### Coverage-guided narrowing

Treat adversarial ownership fixtures as a small covering problem rather than a
cartesian-product corpus. Candidate shapes are classified along these factors:

| Factor | Values retained in the search space |
| --- | --- |
| Alias multiplicity | one, two, or three owner slots naming the same object |
| Release stop boundary | no stop, owner, child, or leaf |
| Surviving alias | none, leaf, child, owner, or independent sibling |
| Continuation | ignore, read, return, same-size update, consume/mutate, or grow/change-tag |
| Neighbor shape | erased, scalar, distinct heap field, or repeated heap field |
| Control boundary | direct return, tail call, ordered external effect, suspension, or caught exception |

Require pairwise coverage for the general factors and three-way coverage for
`(alias multiplicity, release stop boundary, surviving alias)`, because that
interaction determines how many decrements execute before reuse becomes legal.
Rank candidates by new coverage, then by observation strength: a surviving
alias plus a subsequent mutation outranks a result-only scalar. After compiling
a candidate, use the tuple of portable observation, complete executed LCNF form
trace/counts, administrative kinds, and external trace as its path signature.
Discard a larger candidate when a smaller one has the same signature and covers
the same factor interactions. A discrepancy is minimized by removing factor
values while preserving the mismatch before its bug card is filed.

This is a design/search discipline over the existing corpus and retained
telemetry, not a new generator or orchestration layer. It keeps compiler source
shapes explicit and reviewable while making case selection systematic.

S5b covers the next missing three-way interaction: the same leaf occurs in two
owner fields and also survives outside. The unique-owner case must release both
fields, making the leaf exclusive before its update and therefore reusable. The
paired case retains the owner itself; replacement must stop at that shared
owner, preserve both original leaf fields, and force the outside leaf update to
allocate. Exact decrement, increment, constructor, projection, branch, and
reuse counts distinguish the paths, while returned aliases make under-release
and over-release observable.

That pair now passes native Lean versus final LCNF and the complete
native/LCNF/real-V8 triangle with no finding. The unique-owner path pins 62
interpreter steps, four increments, three decrements, three constructors, five
projections, and three `oset` writes; two consecutive `oproj`/`dec` sequences
prove that both repeated fields were released before the surviving leaf was
reused. The shared-owner path pins 64 steps, eight increments, three
decrements, six constructors, three projections, and exactly zero `oset`
writes, proving that release stopped before traversing either owner field and
that both the replacement and updated leaf allocated. Both execute exactly one
ordered `Nat.add`. The resulting snapshot is 651 source cases, 660 aggregate
unique cases, 1,311 tier cases, 1,962 comparisons, 6,689 interpreter steps,
122 tag floors, and 227 semantic domains.

### S6: nonlocal ownership boundaries

Apply a closure, cross an external suspension or ordered effect, then reuse a
different alias. Admit the captured aliased-ByteArray taken/skipped pair only
after argument-alias materialization and the boxed effect protocol are linked.
Add caught exceptions after the source-entry/error contract is accepted by all
participating backends.

## Track B: calls and control

The scalar closure matrix gives broad ABI coverage, but most closures execute
once and return a scalar. Control coverage is similarly shallow: `local-tail`
uses four calls, recursion has three tagged cases, and source compilation does
not yet cover overapplication.

### B1: tail ownership bridge

S4 is landed as the first B-track slice. Keep the compact semantic pair
separate from the large-depth W7 transform probe so agreement with native Lean
and stack-safe rewrite execution remain independently attributable claims.

### B2: application shapes

Add compact source-generated pairs for nullary application, underapplication
followed by later saturation, overapplication, and a closure returned and then
applied internally. Vary result shape once between tagged/scalar and heap
results; do not repeat the scalar ABI matrix. Pin exact `pap`, `fap`, closure
projection, return, and ownership counts. Effectful nullary application waits
in Track C behind the compiler-admissibility question already recorded by
`FIR-BUG-impure-elimDeadVars-nullary-fap-effects`.

### B3: recursion and depth

Compare non-tail recursion, direct self-tail recursion, and mutual recursion on
the same compact observation. Carry one representative heap value so control
and ownership interact without multiplying the matrix. Use separate bounded
semantic fixtures and large-depth artifact probes; stack safety is not inferred
from a four-step semantic example.

## Track C: effects and termination

Three controlled-effect cases establish the protocol, including one ByteArray
snapshot, but they do not cover calls or ownership crossing an effect, output,
or source-level abnormal termination.

### C1: ordered-effect boundaries

Add pairs that perform an effect before versus after closure application,
retain an alias across the effect, and ignore versus consume the effectful
call's result. Observe exact event order and event-time heap snapshots as well
as the returned value. Include an effectful nullary call only after the shared
compiler-admissibility contract is settled; do not normalize away the known
semantic discrepancy.

### C2: semantic termination

Extend the shared source-entry/error contract so native, LCNF, and V8 can all
produce comparable `exception`, `runtimeFault`, and `exited` observations.
Then add returned-versus-thrown and caught-versus-uncaught pairs, including an
ordered effect before termination. Keep semantic faults distinct from harness
timeouts, engine crashes, unsupported cases, and malformed protocol output.

### C3: controlled divergence and resource probes

Admit semantic divergence only through a deterministic shared contract. Fuel
exhaustion and timeout remain harness/backend statuses rather than substitutes
for Lean source behavior. Large-depth and stack probes are acceptance artifacts
attached to a compact native-oracle case, not new semantic outcomes invented by
one backend.

## Track D: floating semantics

The current mixed-closure pair proves bit-exact storage and capture transport
for a NaN payload and negative zero, but FIR's shared abstract runtime still
lacks executable `Float32` and `Float` scalar values. This track therefore
starts at a shared-contract boundary rather than in a fixture-only branch.

### D0: shared value and observation contract

Resolve `FIR-BUG-wasm-none-float-runtime-gap` through the integration owner.
Define bit-preserving protocol values and result decoding for both widths, and
rebase LCNF, W6, W7, and fixture consumers before dependent work continues.

### D1: bit-exact transport

Once D0 lands, cover entry, return, closure capture, aggregate fields, and
effect payloads for positive/negative zero, infinities, representative normal
and subnormal values, quiet NaNs, and signaling-NaN inputs where Lean exposes a
stable observation. Compare words when payload preservation is the claim;
never replace it with JavaScript numeric equality.

### D2: computation

Add a compact matrix for arithmetic, comparison, conversion, and special-value
propagation. Separate Lean-defined semantic results from platform-sensitive
payload details, and retain V8 engine/version provenance for every real-engine
claim.

## Track E: aggregates, erasure, and initialization

### E1: aggregate and erased shapes

Cover `Option`, `Sum`, small arrays, nested inductives, erased/proof fields, and
mixed object/scalar structures using pairwise representative shapes. Require
final-LCNF and executed-form evidence that erasure, construction, case
selection, projection, and return actually ran. Add a schema contract through
integration when the current observation vocabulary cannot express a result;
do not flatten a structure merely to avoid that boundary.

### E2: polymorphic and dictionary traffic

Exercise a polymorphic function at multiple runtime shapes, a captured
typeclass dictionary, and a higher-order dictionary method. The claim is
runtime representation and call fidelity, not elaborator or proof irrelevance.

### E3: constants, caches, and initialization

Add native-oracle cases for zero-argument constants, initialization order,
cached heap results, repeated entry calls, and persistence across resident
invocations. Coordinate with W7 for executable resident helpers and with W6
for refinement, while the fixture lane owns only corpus cases, observations,
and coverage requirements.

## Portfolio cadence

1. Execute S4/B1 tail-call ownership as the memory/control bridge.
2. Extend capture topology only when a new heap kind or boundary adds distinct
   ownership signal.
3. Take one compact C1 ordered-effect slice and one E1 aggregate/erasure slice
   before returning to S5 recursive release and reuse.
4. Queue D0 and C2 as shared contracts, but do not overlap the integration,
   W6, or W7 implementation work while they are unresolved.
5. Promote at least one pair from each executable track to real V8 and add a
   conjunctive coverage domain for the precise semantic intersection claimed.

Fixed-width integer boundaries, Nat/Int arithmetic and conversions, pure
numeric externals, Unicode string operations, and the scalar ABI are maintenance
domains. Raise their floors when existing cases grow, but do not spend the
near-term fixture budget expanding those matrices unless a discrepancy or new
compiler surface gives a specific reason.

## Lane boundaries

The validation lane owns source fixtures, validation projections, exact traces,
coverage requirements, evidence, validation documentation, and discrepancy
cards. It does not modify shared interpreter semantics or protocol termination,
pass proofs, the W6 concrete heap/runtime or its refinement, or W7 generation
and artifact adapters. Float values, source-error entry behavior, result-schema
extensions, effectful nullary-call admissibility, and resident-helper signatures
are shared contracts. A fixture that exposes one is parked behind a coordination
handoff rather than locally weakening or duplicating that contract.
