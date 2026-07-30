---
id: FIR-BUG-wasm-none-reuse-retained-token-ordinary
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 3407f806ee122cc550913ba60c12e0e4ddbbdc6f
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-29
reproduction: Fir/Wasm/WellFormed.lean
regression: integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean
---

# Summary

The concrete in-place reuse protocol requires a nonzero reuse token to name an
ordinary allocation. A successful unique reset establishes that property, but
`reuseCapacitySafeCode` preserves its retained-capacity fact across every
intervening effect without tracking whether the same allocation is made
persistent. The original object name remains in scope after reset, so the
current supported domain can admit such an invalidating mutation before reuse.

## Minimal reproduction

Construct a unique ordinary constructor `object`, reset it to a nonzero token,
then use the still-bound `object` name in a persistent increment before reusing
the token:

```text
let token := reset n object
inc object 1 checked persistent
let result := reuse token replacement fields
```

The capacity transfer keeps the token's `retainedAtLeast` fact across `inc`,
and the ordinary supported-code validator accepts the individual operations.

## Exact commands

```text
lake -d integration/talos env lean \
  FirTalos/ConcreteReuseCapacityCorrectness.lean
make talos-check
```

The proof-level witness is the threaded `ReuseTokenOrdinaryRel` consumed by
`reuseLetStep_of_capacity`. The successful reuse theorem now re-establishes
that relation for its authoritative successor facts; it still cannot derive
the input relation from `ReuseCapacityStateRelated`, because the latter tracks
the retained concrete header extent but not the source cell's persistence bit.

## Expected semantics

Every nonzero token admitted at a reuse site must still denote the ordinary
allocation produced by the unique-reset protocol. Validation may enforce
single-use/adjacency, invalidate the fact when an alias can mutate ownership
metadata, or carry a semantic ordinary-token invariant that all intervening
operations preserve.

## Actual behavior

`reuseCapacitySafeCode` threads facts unchanged through `inc`, `dec`, mutation,
delete, and other effects. In the example above, semantic reuse preserves the
now-persistent source cell metadata because it updates only `cell.object`.
Concrete reuse deliberately installs `persistent := false` in the replacement
header. The ordinary heap relation therefore cannot be re-established.

## Proof or differential evidence

`ReuseCapacityValueRel.retainedToken` proves only the physical address mapping
and retained allocation extent. The in-place branch of
`reuseStep_of_capacityEvidence` additionally needs the source cell equation
`persistent = false`; neither fitting evidence nor mapped-header transport
implies it.

## Semantic impact

The accepted compiler fragment can contain a successful source reuse whose
concrete result disagrees on ownership metadata after an invalidating
intervening effect. The facts-indexed reuse-only whole-export theorem is
available when its threaded ordinary-token invariant holds.
`OrdinaryPersistenceTransport` now isolates the exact condition for an
intervening operation. Local aliases, immediate literals, all successful
read-only projection families, typed unboxing, and `isShared` satisfy it.
Fresh ordinary allocation, `allocCtor`, and all integer-boxing representation
branches satisfy it too. The generic literal theorem additionally covers
immediate, Natural, and String results, yielding a whole-export theorem for
the complete current direct family plus reuse. Compiler-erased persistent
ownership effects also compose because they are runtime identities. Successful
ordinary increments compose through `incValue_ordinaryPersistenceTransport`,
which proves the update preserves every cell's persistence bit. Successful
recursive decrement composes through the fuel-indexed
`decLocationFuel_ordinaryPersistenceTransport`, including releases of owned
constructor fields and closure captures. Explicit deletion composes through
`deleteValue_ordinaryPersistenceTransport`; its erased sentinel is an identity
and its ordinary branch preserves the deleted cell's persistence bit.
Constructor-tag mutation composes through the generic
`modifyConstructor_ordinaryPersistenceTransport`, which covers any successful
constructor-payload rewrite that retains the decoded cell's ownership
metadata. FVar and compiler-erased object-field writes now compose through the
same theorem and a shared facts-indexed target-effect transport. Typed `USize`
and packed `UInt8`/`UInt16`/`UInt32`/`UInt64` slot writes use corresponding
specializations and now compose as well. This bug still blocks validator-wide
admission of effects that can create persistent aliases or otherwise fail
that transport. Selected default-only cases compose without an additional
ordinary-persistence obligation because branch entry changes neither the
runtime nor the authoritative facts. The existing object-constructor and
scalar-`UInt8` case-runtime laws are now instantiated under the same
facts-indexed frame.

## Classification and triage

This is a shared reset/reuse protocol-validation gap. The concrete runtime's
ordinary replacement header is intentional and should not be weakened.

## Workaround

W6 compiler composition threads `ReuseTokenOrdinaryRel` and proves successful
reuse preserves it. Structural composition must still preserve or invalidate
that relation at every unrelated intervening effect until the authoritative
supported-domain validator establishes a stable reset-token protocol.
Lazy-cache miss publication is now a concrete additional instance: it
recursively marks the returned graph persistent, so any retained token whose
location is reachable from that result must be invalidated. W6 proves that
publication preserves heap frontier and mapped allocation extents, but
correctly does not claim all-location `OrdinaryPersistenceTransport` for this
ownership-changing step. The lazy-step boundary now uses
`ReuseTokenOrdinaryBindTransport`, indexed by the actual fact map and result
binding, so it requires ordinaryness only for retained facts that survive
destination erasure. Existing all-location transport theorems remain
sufficient adapters for genuinely ordinary-preserving operations; an empty
fact map discharges the publication boundary unconditionally.
`markPersistentLocationFuel_findCell_eq_of_not_reachable` now proves that
recursive publication leaves every cell outside the original ownership
closure unchanged. `ReuseTokenPublicationDisjoint` specializes that theorem
to the tracked token locations, and the executable budgeted miss theorem
derives its facts-aware ordinary frame from this condition and the exact
semantic `setGlobal` post-state. Non-heap publications are disjoint
constructively.

## Upstream tracking

none

## Resolution and regression

Confirmed and narrowed. Successful reuse now has source-level ordinary-cell
preservation and authoritative fact-insertion transfer. Add reset-token
validity invalidation/preservation to every other shared validator transfer,
then derive the input ordinary source-cell fact compositionally in the
certificate-free compiler state relation. Lazy cache composition no longer
assumes the false all-location publication property; its remaining obligation
is now executable and precise: generated-environment composition must prove
the source publication equation plus reachability disjointness for each
retained fact, or the shared validator must invalidate facts that cannot meet
that condition.

The subsequent cache-hit boundary is now explicit as well.
`PopulatedLazyCacheSlotRel` relates the semantic cache entry to the initialized
Wasm flag/value globals and its checked physical-value refinement. Exact miss
publication constructs this relation, and the compiler-anchored hit theorem
consumes it to derive the destination write and post-binding state relation.
This removes another opaque hit premise without weakening the runtime.
`LazyCacheGlobalsRel` now threads empty/populated state across the complete
generated table, establishes the adapted empty initial state, transports
through operations that preserve both global tables, and lets the generated
hit theorem recover its populated physical lane from the table. Semantic
absence selects the empty slot and its zero flag; exact source/Wasm
publication replaces it with the populated relation, while initializer
uniqueness and paired-index arithmetic preserve all other slots. The updated
table and budgeted miss are packaged at the same post-state. The remaining
bug-specific obligation is unchanged: generated source execution must supply
the publication equation and prove retained-token reachability disjointness,
or shared validation must invalidate the affected facts.

The cache table now lives in `ConcreteReuseCapacityCacheFrame`, and the
uniform lazy implementation returns its successor together with the budgeted
step. This closes invariant threading at the generic runtime-law boundary;
it does not discharge the bug-specific publication/disjointness fact above.
