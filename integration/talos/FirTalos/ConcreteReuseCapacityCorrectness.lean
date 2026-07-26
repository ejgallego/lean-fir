import FirTalos.ConcreteRuntime
import Fir.Wasm.WellFormed

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- Heap transitions preserve reuse capacity when every related, previously
owned allocation header remains readable with the same physical extent.
Payload and ownership metadata may change freely. -/
abbrev HeaderCapacityTransport := MappedHeaderCapacityTransport

theorem HeaderCapacityTransport.refl
    (heap : MemoryState) (witness : RefinementWitness) :
    HeaderCapacityTransport heap heap witness := by
  intro address location header mapped headerRead owned
  exact ⟨header, headerRead, rfl, owned⟩

/-- Fresh allocation is the common capacity-preserving heap transition: every
previously owned header remains byte-for-byte readable below the extended
frontier. -/
theorem HeaderCapacityTransport.ofPrefixExtension
    {before after : MemoryState}
    (witness : RefinementWitness)
    (extension : before.PrefixExtension after) :
    HeaderCapacityTransport before after witness :=
  MappedHeaderCapacityTransport.ofPrefixExtension witness extension

theorem valueRel_heapObject_mapped
    {witness : RefinementWitness} {kind : AbiKind}
    {address : Word32} {location : Location}
    (related :
      ValueRel witness kind (.word32 address)
        (.object (.heap location))) :
    witness.locations.lookup? location = some address := by
  cases related with
  | object heapRelated =>
      cases heapRelated with
      | mapped found => exact found
  | tobject objectRelated =>
      cases objectRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped found => exact found

theorem valueRel_reuseToken_some_mapped
    {witness : RefinementWitness} {address : Word32} {location : Location}
    (related :
      ValueRel witness .reuseToken (.word32 address)
        (.reuseToken (some location))) :
    witness.locations.lookup? location = some address := by
  cases related with
  | reuseSome heapRelated =>
      cases heapRelated with
      | mapped found => exact found

/-- Nonempty constructor allocation instantiates the generic header-capacity
transport boundary from its existing fresh-prefix theorem. -/
theorem HeaderCapacityTransport.allocateConstructor_nonempty
    (state result : MemoryState) (witness : RefinementWitness)
    (info : LCNF.CtorInfo) (fields : Array Word32) (address : Word32)
    (valid : state.FrontierInvariant)
    (arity : fields.size = info.size)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (allocated :
      allocateConstructor state info fields = .ok (result, address)) :
    HeaderCapacityTransport state result witness :=
  .ofPrefixExtension witness
    (allocateConstructor_nonempty_prefixExtension state result info fields
      address valid arity nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit allocated)

/-- Empty-token reuse of a nonempty constructor is the same fresh allocation,
so it preserves every previously tracked retained extent. -/
theorem HeaderCapacityTransport.reuseObject_none_nonempty
    (state result : MemoryState) (witness : RefinementWitness)
    (info : LCNF.CtorInfo) (updateHeader : Bool)
    (fields : Array Word32) (address : Word32)
    (valid : state.FrontierInvariant)
    (arity : fields.size = info.size)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (reused :
      reuseObject state Word32.zero info updateHeader fields =
        .ok (result, address)) :
    HeaderCapacityTransport state result witness := by
  have allocated :
      allocateConstructor state info fields = .ok (result, address) := by
    unfold reuseObject at reused
    rw [if_pos (by decide)] at reused
    exact reused
  exact .allocateConstructor_nonempty state result witness info fields address
    valid arity nonempty tagFits objectFieldsFit usizeFieldsFit scalarBytesFit
    allocated

/--
Dynamic meaning of the validator's reset/reuse capacity evidence.

The relation deliberately covers both sides of `reset`: constructor results
are ordinary object lanes, while reset results are reuse-token lanes. A
definitely empty constructor is tagged and therefore resets to physical zero.
Retained evidence permits reset to return zero for a shared or persistent
object; when the value names a heap allocation, its concrete header carries
the validated lower bound. Raw header readability is intentional: ownership
may mark an allocation dead without changing its retained extent.
-/
inductive ReuseCapacityValueRel
    (heap : MemoryState) (witness : RefinementWitness) :
    ReuseCapacityEvidence → AbiKind → LaneValue → Value → Prop where
  | emptyObject
      (related :
        ValueRel witness kind (.word32 word)
          (.object (.tagged payload))) :
      ReuseCapacityValueRel heap witness .emptyToken kind (.word32 word)
        (.object (.tagged payload))
  | emptyToken :
      ReuseCapacityValueRel heap witness .emptyToken .reuseToken
        (.word32 Word32.zero) (.reuseToken none)
  | retainedObject
      (related :
        ValueRel witness kind (.word32 address)
          (.object (.heap location)))
      (headerRead : Header.read heap.memory address = .ok header)
      (headerOwned : address.value + headerBytes ≤ heap.heapCursor)
      (minimum : available ≤ header.allocationBytes.toNat) :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available) kind
        (.word32 address) (.object (.heap location))
  | retainedEmptyToken :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available)
        .reuseToken (.word32 Word32.zero) (.reuseToken none)
  | retainedToken
      (related :
        ValueRel witness .reuseToken (.word32 address)
          (.reuseToken (some location)))
      (headerRead : Header.read heap.memory address = .ok header)
      (headerOwned : address.value + headerBytes ≤ heap.heapCursor)
      (minimum : available ≤ header.allocationBytes.toNat) :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available)
        .reuseToken (.word32 address) (.reuseToken (some location))

/-- Capacity evidence survives any representation-witness transition and heap
step that preserves already allocated header extents. -/
theorem ReuseCapacityValueRel.transport
    {before after : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    {evidence : ReuseCapacityEvidence} {kind : AbiKind}
    {lane : LaneValue} {semantic : Value}
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport before after beforeWitness)
    (related :
      ReuseCapacityValueRel before beforeWitness evidence kind lane semantic) :
    ReuseCapacityValueRel after afterWitness evidence kind lane semantic := by
  cases related with
  | emptyObject valueRelated =>
      exact .emptyObject (witnessTransport valueRelated)
  | emptyToken => exact .emptyToken
  | retainedObject valueRelated headerRead headerOwned minimum =>
      obtain ⟨nextHeader, nextHeaderRead, sameExtent, nextHeaderOwned⟩ :=
        capacityTransport _ _ _ (valueRel_heapObject_mapped valueRelated) headerRead
          headerOwned
      exact .retainedObject (witnessTransport valueRelated) nextHeaderRead
        nextHeaderOwned (by simpa [sameExtent] using minimum)
  | retainedEmptyToken => exact .retainedEmptyToken
  | retainedToken valueRelated headerRead headerOwned minimum =>
      obtain ⟨nextHeader, nextHeaderRead, sameExtent, nextHeaderOwned⟩ :=
        capacityTransport _ _ _ (valueRel_reuseToken_some_mapped valueRelated)
          headerRead
          headerOwned
      exact .retainedToken (witnessTransport valueRelated) nextHeaderRead
        nextHeaderOwned (by simpa [sameExtent] using minimum)

/-- Capacity tracking strengthens, but never replaces, the ordinary
ABI-indexed value relation. -/
theorem ReuseCapacityValueRel.valueRelated
    {heap : MemoryState} {witness : RefinementWitness}
    {evidence : ReuseCapacityEvidence} {kind : AbiKind}
    {lane : LaneValue} {semantic : Value}
    (related :
      ReuseCapacityValueRel heap witness evidence kind lane semantic) :
    ValueRel witness kind lane semantic := by
  cases related with
  | emptyObject valueRelated => exact valueRelated
  | emptyToken => exact .reuseNone
  | retainedObject valueRelated _ _ _ => exact valueRelated
  | retainedEmptyToken => exact .reuseNone
  | retainedToken valueRelated _ _ _ => exact valueRelated

/-- Erasing one tracked name does not affect lookup of a different name. -/
theorem findReuseCapacityEvidence?_erase_other
    (facts : ReuseCapacityFacts) (erased query : FVarId)
    (different : erased.name ≠ query.name) :
    findReuseCapacityEvidence? (eraseReuseCapacityFact facts erased) query =
      findReuseCapacityEvidence? facts query := by
  induction facts with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨candidate, evidence⟩
      by_cases erasedCandidate : candidate.name = erased.name
      · have candidateQuery : candidate.name ≠ query.name := by
          intro equal
          exact different (erasedCandidate.symm.trans equal)
        have filterEq :
            List.filter (fun entry : FVarId × ReuseCapacityEvidence =>
              entry.1.name != erased.name) ((candidate, evidence) :: rest) =
              List.filter (fun entry : FVarId × ReuseCapacityEvidence =>
                entry.1.name != erased.name) rest := by
          simp [erasedCandidate]
        unfold eraseReuseCapacityFact
        rw [filterEq]
        change findReuseCapacityEvidence?
            (eraseReuseCapacityFact rest erased) query =
          findReuseCapacityEvidence? ((candidate, evidence) :: rest) query
        rw [ih]
        simp [findReuseCapacityEvidence?, candidateQuery]
      · have filterEq :
            List.filter (fun entry : FVarId × ReuseCapacityEvidence =>
              entry.1.name != erased.name) ((candidate, evidence) :: rest) =
              (candidate, evidence) ::
                List.filter (fun entry : FVarId × ReuseCapacityEvidence =>
                  entry.1.name != erased.name) rest := by
          simp [erasedCandidate]
        unfold eraseReuseCapacityFact
        rw [filterEq]
        change findReuseCapacityEvidence?
            ((candidate, evidence) ::
              eraseReuseCapacityFact rest erased) query =
          findReuseCapacityEvidence? ((candidate, evidence) :: rest) query
        by_cases candidateQuery : candidate.name = query.name
        · simp [findReuseCapacityEvidence?, candidateQuery]
        · simpa [findReuseCapacityEvidence?, candidateQuery] using ih

/-- Inserting a fact leaves lookup of every differently named binding
unchanged. -/
theorem findReuseCapacityEvidence?_insert_other
    (facts : ReuseCapacityFacts) (inserted query : FVarId)
    (evidence : ReuseCapacityEvidence)
    (different : inserted.name ≠ query.name) :
    findReuseCapacityEvidence?
        (insertReuseCapacityFact facts inserted evidence) query =
      findReuseCapacityEvidence? facts query := by
  simp [insertReuseCapacityFact, findReuseCapacityEvidence?, different,
    findReuseCapacityEvidence?_erase_other facts inserted query different]

/-- Dynamic interpretation of every fact carried by the static analysis.
Each tracked source binding is resolved at the compiler-assigned local and
related to the current concrete heap by `ReuseCapacityValueRel`. -/
def ReuseCapacityFactsRel
    (facts : ReuseCapacityFacts)
    (bindings : List (FVarId × AbiKind)) (sourceEnv : Env)
    (targetLocals : Wasm.Locals) (heap : MemoryState)
    (witness : RefinementWitness) : Prop :=
  ∀ fvarId evidence,
    findReuseCapacityEvidence? facts fvarId = some evidence →
    ∃ index kind lane semantic,
      lookup sourceEnv fvarId = some semantic ∧
      findFVar? bindings fvarId = some index ∧
      bindings[index]?.map Prod.snd = some kind ∧
      targetLocals.get index = some (physicalOfLane lane) ∧
      ReuseCapacityValueRel heap witness evidence kind lane semantic

theorem ReuseCapacityFactsRel.resolve
    {facts : ReuseCapacityFacts}
    {bindings : List (FVarId × AbiKind)} {sourceEnv : Env}
    {targetLocals : Wasm.Locals} {heap : MemoryState}
    {witness : RefinementWitness} {fvarId : FVarId}
    {evidence : ReuseCapacityEvidence}
    (related :
      ReuseCapacityFactsRel facts bindings sourceEnv targetLocals heap witness)
    (found : findReuseCapacityEvidence? facts fvarId = some evidence) :
    ∃ index kind lane semantic,
      lookup sourceEnv fvarId = some semantic ∧
      findFVar? bindings fvarId = some index ∧
      bindings[index]?.map Prod.snd = some kind ∧
      targetLocals.get index = some (physicalOfLane lane) ∧
      ReuseCapacityValueRel heap witness evidence kind lane semantic :=
  related fvarId evidence found

/-- All existing facts survive a heap/witness transition that preserves
allocation extents. Source bindings and concrete locals are unchanged. -/
theorem ReuseCapacityFactsRel.transport
    {facts : ReuseCapacityFacts}
    {bindings : List (FVarId × AbiKind)} {sourceEnv : Env}
    {targetLocals : Wasm.Locals} {before after : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport before after beforeWitness)
    (related :
      ReuseCapacityFactsRel facts bindings sourceEnv targetLocals before
        beforeWitness) :
    ReuseCapacityFactsRel facts bindings sourceEnv targetLocals after
      afterWitness := by
  intro fvarId evidence found
  obtain ⟨index, kind, lane, semantic, sourceLookup, localFound, kindAt,
      targetLookup, valueRelated⟩ := related.resolve found
  exact ⟨index, kind, lane, semantic, sourceLookup, localFound, kindAt,
    targetLookup, valueRelated.transport witnessTransport capacityTransport⟩

/-- Bind a newly tracked result while preserving every differently named old
fact through the heap, witness, environment, and local transitions. -/
theorem ReuseCapacityFactsRel.bind
    {facts : ReuseCapacityFacts}
    {bindings : List (FVarId × AbiKind)} {sourceEnv : Env}
    {targetLocals updatedLocals : Wasm.Locals}
    {before after : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    {result : FVarId} {resultIndex : Nat} {kind : AbiKind}
    {lane : LaneValue} {semantic : Value}
    {evidence : ReuseCapacityEvidence}
    (related :
      ReuseCapacityFactsRel facts bindings sourceEnv targetLocals before
        beforeWitness)
    (resultFound : findFVar? bindings result = some resultIndex)
    (kindAt : bindings[resultIndex]?.map Prod.snd = some kind)
    (localUpdate : FirTalos.Correctness.LocalUpdate targetLocals updatedLocals
      resultIndex (physicalOfLane lane))
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport before after beforeWitness)
    (valueRelated :
      ReuseCapacityValueRel after afterWitness evidence kind lane semantic) :
    ReuseCapacityFactsRel
      (insertReuseCapacityFact facts result evidence) bindings
      (Fir.LeanIR.Impure.bind sourceEnv result semantic) updatedLocals after
      afterWitness := by
  intro fvarId actualEvidence found
  by_cases sameName : result.name = fvarId.name
  · have found' : some evidence = some actualEvidence := by
      simpa [insertReuseCapacityFact, findReuseCapacityEvidence?, sameName]
        using found
    have evidenceEq := Option.some.inj found'
    subst actualEvidence
    have sameFind :=
      FirTalos.Correctness.findFVar?_eq_of_name_eq bindings sameName
    have actualResultFound :
        findFVar? bindings fvarId = some resultIndex := by
      rw [← sameFind]
      exact resultFound
    have sourceLookup :
        lookup (Fir.LeanIR.Impure.bind sourceEnv result semantic) fvarId =
          some semantic := by
      simp [Fir.LeanIR.Impure.bind, lookup, sameName]
    exact ⟨resultIndex, kind, lane, semantic, sourceLookup, actualResultFound,
      kindAt, localUpdate.1, valueRelated⟩
  · have oldFound :
        findReuseCapacityEvidence? facts fvarId = some actualEvidence := by
      rw [← findReuseCapacityEvidence?_insert_other facts result fvarId
        evidence sameName]
      exact found
    obtain ⟨index, oldKind, oldLane, oldSemantic, sourceLookup, localFound,
        oldKindAt, targetLookup, oldValueRelated⟩ :=
      related.resolve oldFound
    have differentIndex :=
      FirTalos.Correctness.findFVar?_ne_of_name_ne bindings sameName
        resultFound localFound
    have boundSourceLookup :
        lookup (Fir.LeanIR.Impure.bind sourceEnv result semantic) fvarId =
          some oldSemantic := by
      simpa [Fir.LeanIR.Impure.bind, lookup, sameName] using sourceLookup
    have updatedLookup :
        updatedLocals.get index = some (physicalOfLane oldLane) :=
      (localUpdate.2 differentIndex.symm).trans targetLookup
    exact ⟨index, oldKind, oldLane, oldSemantic, boundSourceLookup, localFound,
      oldKindAt, updatedLookup,
      oldValueRelated.transport witnessTransport capacityTransport⟩

/-- Resolve a fitting static token fact to the exact dynamic lane at the
compiler-assigned reuse-token local. -/
theorem ReuseCapacityFactsRel.resolveFittingToken
    {facts : ReuseCapacityFacts}
    {bindings : List (FVarId × AbiKind)} {sourceEnv : Env}
    {targetLocals : Wasm.Locals} {heap : MemoryState}
    {witness : RefinementWitness} {tokenId : FVarId}
    {info : LCNF.CtorInfo} {evidence : ReuseCapacityEvidence}
    {tokenIndex : Nat} {sourceToken : Value}
    (related :
      ReuseCapacityFactsRel facts bindings sourceEnv targetLocals heap witness)
    (fitting :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
    (sourceLookup : lookup sourceEnv tokenId = some sourceToken)
    (localFound : findFVar? bindings tokenId = some tokenIndex)
    (kindAt :
      bindings[tokenIndex]?.map Prod.snd = some .reuseToken) :
    ∃ lane,
      targetLocals.get tokenIndex = some (physicalOfLane lane) ∧
      ReuseCapacityValueRel heap witness evidence .reuseToken lane
        sourceToken := by
  have tracked :=
    (findFittingReuseCapacityEvidence?_eq_some facts tokenId info evidence
      fitting).1
  obtain ⟨index, kind, lane, semantic, actualSourceLookup, actualLocalFound,
      actualKindAt, targetLookup, capacityRelated⟩ :=
    related.resolve tracked
  rw [sourceLookup] at actualSourceLookup
  have semanticEq := Option.some.inj actualSourceLookup
  subst semantic
  rw [localFound] at actualLocalFound
  have indexEq := Option.some.inj actualLocalFound
  subst index
  rw [kindAt] at actualKindAt
  have kindEq := Option.some.inj actualKindAt
  subst kind
  exact ⟨lane, targetLookup, capacityRelated⟩

/-- Strengthening of W6's ordinary concrete state invariant with the dynamic
meaning of the static capacity-analysis state at the current code node. -/
def ReuseCapacityStateRelated
    (facts : ReuseCapacityFacts) (sourceFunction : Fir.Wasm.Function)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    ReuseCapacityFactsRel facts (functionBindings sourceFunction) sourceEnv
      targetLocals targetStore.host.runtime.heap witness

theorem ReuseCapacityStateRelated.stateRelated
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness) :
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness :=
  related.1

/-- A successful concrete transition lifts the ordinary final state relation
to the strengthened capacity invariant whenever it transports witnesses and
preserves the allocation extent of every previously mapped location. Source
bindings and concrete locals are unchanged by this generic no-result rule. -/
theorem ReuseCapacityStateRelated.transport
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore nextStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {beforeWitness afterWitness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (finalRelated :
      StateRelated sourceFunction nextRuntime sourceEnv nextStore targetLocals
        afterWitness)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness) :
    ReuseCapacityStateRelated facts sourceFunction nextRuntime sourceEnv
      nextStore targetLocals afterWitness := by
  exact ⟨finalRelated,
    related.2.transport witnessTransport capacityTransport⟩

/-- Same-witness specialization used by ownership and mutation effects. -/
theorem ReuseCapacityStateRelated.transportSameWitness
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore nextStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (finalRelated :
      StateRelated sourceFunction nextRuntime sourceEnv nextStore targetLocals
        witness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap witness) :
    ReuseCapacityStateRelated facts sourceFunction nextRuntime sourceEnv
      nextStore targetLocals witness :=
  related.transport finalRelated (WitnessTransport.refl witness)
    capacityTransport

/-- Common concrete-host specialization: a heap-only operation with unchanged
source bindings, locals, and witness preserves the strengthened state exactly
when its operation theorem supplies mapped-header transport. -/
theorem ReuseCapacityStateRelated.replaceHeap
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {initial : Wasm.Store Host} {heap : MemoryState}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        initial targetLocals witness)
    (runtimeRelated :
      ConcreteRuntimeRel (FirTalos.Concrete.replaceHeap initial heap).host.runtime
        witness nextRuntime)
    (capacityTransport :
      HeaderCapacityTransport initial.host.runtime.heap heap witness) :
    ReuseCapacityStateRelated facts sourceFunction nextRuntime sourceEnv
      (FirTalos.Concrete.replaceHeap initial heap) targetLocals witness := by
  apply related.transportSameWitness
    ⟨runtimeRelated, by simp [FirTalos.Concrete.replaceHeap, clearFailure],
      related.1.2.2⟩
  simpa [FirTalos.Concrete.replaceHeap, clearFailure] using capacityTransport

/-- Capacity-aware syntax bridge for any already composed no-result effect.
The existing W6 effect simulation continues to own source control, lowering,
ordinary state refinement, and Wasm weakest preconditions; this lemma adds
only the static-capacity invariant required by T4S. -/
theorem ReuseCapacityStateRelated.ofEffectStep
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {code continuation : LCNF.Code .impure}
    {target targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {beforeWitness afterWitness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
        targetRest targetStore nextStore targetLocals beforeWitness
        afterWitness)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness) :
    ReuseCapacityStateRelated facts sourceFunction nextRuntime sourceEnv
      nextStore targetLocals afterWitness :=
  related.transport step.2.2.2.1 witnessTransport capacityTransport

/-- Same-witness concrete-host effect specialization. This is the direct
syntax-level consumer of every ownership and mutation theorem whose target
store is `replaceHeap initial heap`. -/
theorem ReuseCapacityStateRelated.ofReplaceHeapEffectStep
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {code continuation : LCNF.Code .impure}
    {target targetRest : Wasm.Program}
    {initial : Wasm.Store Host} {heap : MemoryState}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        initial targetLocals witness)
    (step :
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
        targetRest initial (FirTalos.Concrete.replaceHeap initial heap)
        targetLocals witness witness)
    (capacityTransport :
      HeaderCapacityTransport initial.host.runtime.heap heap witness) :
    ReuseCapacityStateRelated facts sourceFunction nextRuntime sourceEnv
      (FirTalos.Concrete.replaceHeap initial heap) targetLocals witness := by
  apply related.ofEffectStep step (WitnessTransport.refl witness)
  simpa [FirTalos.Concrete.replaceHeap, clearFailure] using capacityTransport

/-- Existential form matching the public `_with_capacity` effect theorems.
It packages both the unchanged W6 simulation certificate and the strengthened
state at its continuation node. -/
theorem ReuseCapacityStateRelated.ofReplaceHeapEffectResult
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {code continuation : LCNF.Code .impure}
    {target targetRest : Wasm.Program}
    {initial : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        initial targetLocals witness)
    (result :
      ∃ heap,
        EffectStepSimulates context sourceModule sourceFunction labels module
          hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
          targetRest initial (FirTalos.Concrete.replaceHeap initial heap)
          targetLocals witness witness ∧
        HeaderCapacityTransport initial.host.runtime.heap heap witness) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
        targetRest initial (FirTalos.Concrete.replaceHeap initial heap)
        targetLocals witness witness ∧
      ReuseCapacityStateRelated facts sourceFunction nextRuntime sourceEnv
        (FirTalos.Concrete.replaceHeap initial heap) targetLocals witness := by
  obtain ⟨heap, step, capacity⟩ := result
  exact ⟨heap, step, related.ofReplaceHeapEffectStep step capacity⟩

theorem ReuseCapacityStateRelated.resolveFittingToken
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {tokenId : FVarId}
    {info : LCNF.CtorInfo} {evidence : ReuseCapacityEvidence}
    {tokenIndex : Nat} {sourceToken : Value}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (fitting :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
    (sourceLookup : lookup sourceEnv tokenId = some sourceToken)
    (localFound :
      findFVar? (functionBindings sourceFunction) tokenId = some tokenIndex)
    (kindAt :
      (functionBindings sourceFunction)[tokenIndex]?.map Prod.snd =
        some .reuseToken) :
    ∃ lane,
      targetLocals.get tokenIndex = some (physicalOfLane lane) ∧
      ReuseCapacityValueRel targetStore.host.runtime.heap witness evidence
        .reuseToken lane sourceToken :=
  related.2.resolveFittingToken fitting sourceLookup localFound kindAt

/-- A decoded constructor relation supplies the exact dynamic lower bound
recorded when the validator sees its direct allocation. -/
theorem ReuseCapacityValueRel.retainedObject_of_constructor
    {heap : MemoryState} {witness : RefinementWitness}
    {address : Word32} {location : Location}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {object : ConstructorObject} {kind : AbiKind}
    (valueRelated :
      ValueRel witness kind (.word32 address)
        (.object (.heap location)))
    (objectRelated :
      ConstructorObjectRel heap witness address info fieldKinds object) :
    ReuseCapacityValueRel heap witness
      (.retainedAtLeast (ConstructorLayout.ofInfo info).allocationBytes)
      kind (.word32 address) (.object (.heap location)) := by
  obtain ⟨header, headerRead, _, allocationBytes, _, _, _, _⟩ :=
    objectRelated.header
  have rawHeaderRead :=
    (MemoryState.PrefixExtension.readLiveHeader_facts heap address header
      headerRead).2.1
  exact .retainedObject valueRelated rawHeaderRead objectRelated.headerOwned
    allocationBytes

/-- The static analysis records an empty-layout constructor as definitely
empty, and the concrete tagged result realizes that fact for any admitted
constructor result kind. -/
theorem allocCtorEmptyStep_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value} {heap : MemoryState} {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size)
    (decoded : decodeConstructorWords 0 physicalArgs = .ok fields)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (allocated : allocateConstructor initial.host.runtime.heap info fields.toArray =
      .ok (heap, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        runtime ∧
      ValueRel nextWitness resultKind (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat word.value))
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      ReuseCapacityValueRel heap nextWitness
        (constructorReuseCapacityEvidence info) resultKind (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  obtain ⟨nextWitness, extension, concreteStep, nextRuntimeRelated,
      valueRelated, physicalRelated, semanticStep, capacityTransport⟩ :=
    allocCtorEmptyStep_of_refines_with_capacity runtimeRelated argsLength decoded
      arity semanticArity empty tagFits resultRefines allocated
  have capacityValue :
      ReuseCapacityValueRel heap nextWitness .emptyToken resultKind
        (.word32 word) (.object (.tagged (UInt64.ofNat info.cidx))) := by
    exact .emptyObject valueRelated
  have evidenceEq :
      constructorReuseCapacityEvidence info = .emptyToken := by
    simp [constructorReuseCapacityEvidence, constructorAllocatesHeap,
      empty.1.1, empty.1.2, empty.2]
  exact ⟨nextWitness, extension, concreteStep, nextRuntimeRelated,
    valueRelated, physicalRelated, by simpa [evidenceEq] using capacityValue,
    capacityTransport, semanticStep⟩

/-- Empty-token reuse of an empty-layout constructor preserves old retained
facts and realizes the analysis result as another definitely-empty tagged
constructor value. -/
theorem reuseStep_none_empty_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : LCNF.CtorInfo}
    {updateHeader : Bool} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value} {heap : MemoryState} {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (Word32.zero, fields))
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (reused : reuseObject initial.host.runtime.heap Word32.zero info
      updateHeader fields.toArray = .ok (heap, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        runtime ∧
      ValueRel nextWitness resultKind (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat word.value))
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      ReuseCapacityValueRel heap nextWitness
        (constructorReuseCapacityEvidence info) resultKind (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      reuse runtime (.reuseToken none) info updateHeader semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  obtain ⟨nextWitness, extension, concreteStep, nextRuntimeRelated,
      valueRelated, physicalRelated, semanticStep, capacityTransport⟩ :=
    reuseStep_none_empty_of_refines_with_capacity runtimeRelated argsLength
      decoded arity semanticArity empty tagFits resultRefines reused
  have capacityValue :
      ReuseCapacityValueRel heap nextWitness .emptyToken resultKind
        (.word32 word) (.object (.tagged (UInt64.ofNat info.cidx))) := by
    exact .emptyObject valueRelated
  have evidenceEq :
      constructorReuseCapacityEvidence info = .emptyToken := by
    simp [constructorReuseCapacityEvidence, constructorAllocatesHeap,
      empty.1.1, empty.1.2, empty.2]
  exact ⟨nextWitness, extension, concreteStep, nextRuntimeRelated,
    valueRelated, physicalRelated, by simpa [evidenceEq] using capacityValue,
    capacityTransport, semanticStep⟩

/-- A unique reset changes an ordinary object lane into a reuse-token lane at
the same address. Header-capacity transport carries the retained lower bound
through prefix clearing and child ownership updates. -/
theorem ReuseCapacityValueRel.retainedToken_of_reset
    {before after : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    {available : Nat} {kind : AbiKind}
    {address : Word32} {location : Location}
    (objectRelated :
      ReuseCapacityValueRel before beforeWitness
        (.retainedAtLeast available) kind (.word32 address)
        (.object (.heap location)))
    (capacityTransport :
      HeaderCapacityTransport before after beforeWitness)
    (tokenRelated :
      ValueRel afterWitness .reuseToken (.word32 address)
        (.reuseToken (some location))) :
    ReuseCapacityValueRel after afterWitness (.retainedAtLeast available)
      .reuseToken (.word32 address) (.reuseToken (some location)) := by
  cases objectRelated with
  | retainedObject valueRelated headerRead headerOwned minimum =>
      obtain ⟨nextHeader, nextHeaderRead, sameExtent, nextHeaderOwned⟩ :=
        capacityTransport address location _
          (valueRel_heapObject_mapped valueRelated)
          headerRead headerOwned
      exact .retainedToken tokenRelated nextHeaderRead nextHeaderOwned
        (by simpa [sameExtent] using minimum)

/-- The unique-reset host theorem now closes the validator's retained-capacity
invariant directly: the concrete reset transports every mapped header, and
the returned nonempty token inherits the input object's exact lower bound. -/
theorem resetStep_unique_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {object : ConstructorObject}
    {count available : Nat} {kind : AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (capacityRelated :
      ReuseCapacityValueRel initial.host.runtime.heap witness
        (.retainedAtLeast available) kind (.word32 address)
        (.object (.heap location)))
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1) (constructor : cell.object = .ctor object)
    (countFits : count ≤ object.objectFields.size)
    (updated : reset runtime count (.object (.heap location)) =
      .ok (nextRuntime, .reuseToken (some location))) :
    ∃ heap info fieldKinds,
      let nextWitness :=
        witness.rebindConstructor address info
          (resetProtocolFieldKinds fieldKinds count)
      resetStep count initial [.i32 (UInt32.ofNat address.value)] =
          .Return [.i32 (UInt32.ofNat address.value)]
            (replaceHeap initial heap) ∧
        WitnessTransport witness nextWitness ∧
        ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
          nextRuntime ∧
        ReuseCapacityValueRel heap nextWitness (.retainedAtLeast available)
          .reuseToken (.word32 address) (.reuseToken (some location)) ∧
        ResetReuseProtocolRel initial.host.runtime.heap heap witness runtime
          nextRuntime location address cell object count := by
  obtain ⟨heap, info, fieldKinds, concreteReset, transport, nextRelated,
      tokenRelated, protocol, capacityTransport⟩ :=
    resetStep_unique_of_refines runtimeRelated descriptorsEq mapped found live
      ordinary unique constructor countFits updated
  let nextWitness :=
    witness.rebindConstructor address info
      (resetProtocolFieldKinds fieldKinds count)
  have nextCapacity :
      ReuseCapacityValueRel heap nextWitness (.retainedAtLeast available)
        .reuseToken (.word32 address) (.reuseToken (some location)) :=
    capacityRelated.retainedToken_of_reset capacityTransport tokenRelated
  exact ⟨heap, info, fieldKinds, concreteReset, transport, nextRelated,
    nextCapacity, protocol⟩

/-- At reuse-token kind, definitely-empty evidence fixes both the semantic
token and its physical word. -/
theorem ReuseCapacityValueRel.emptyToken_eq
    {heap : MemoryState} {witness : RefinementWitness}
    {lane : LaneValue} {token : Value}
    (related :
      ReuseCapacityValueRel heap witness .emptyToken .reuseToken lane token) :
    lane = .word32 Word32.zero ∧ token = .reuseToken none := by
  cases related with
  | emptyObject valueRelated => cases valueRelated
  | emptyToken => exact ⟨rfl, rfl⟩

/-- Retained evidence at reuse-token kind is either the zero fallback or a
nonzero mapped token whose header realizes the tracked capacity. -/
theorem ReuseCapacityValueRel.retainedToken_cases
    {heap : MemoryState} {witness : RefinementWitness}
    {available : Nat} {lane : LaneValue} {token : Value}
    (related :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available)
        .reuseToken lane token) :
    (lane = .word32 Word32.zero ∧ token = .reuseToken none) ∨
      ∃ location address header,
        lane = .word32 address ∧
        token = .reuseToken (some location) ∧
        ValueRel witness .reuseToken (.word32 address)
          (.reuseToken (some location)) ∧
        Header.read heap.memory address = .ok header ∧
        address.value + headerBytes ≤ heap.heapCursor ∧
        available ≤ header.allocationBytes.toNat := by
  cases related with
  | retainedObject valueRelated _ _ _ => cases valueRelated
  | retainedEmptyToken => exact .inl ⟨rfl, rfl⟩
  | retainedToken valueRelated headerRead headerOwned minimum =>
      exact .inr
        ⟨_, _, _, rfl, rfl, valueRelated, headerRead, headerOwned, minimum⟩

/--
The central W6.6dg bridge: static fitting evidence and its dynamic header
meaning imply the exact retained-layout premise used by concrete reuse.
-/
theorem ReuseCapacityValueRel.reuseToken_some_layoutFits
    {heap : MemoryState} {witness : RefinementWitness}
    {facts : ReuseCapacityFacts} {tokenId : FVarId}
    {info : LCNF.CtorInfo} {evidence : ReuseCapacityEvidence}
    {location : Location} {address : Word32} {header : Header}
    (related :
      ReuseCapacityValueRel heap witness evidence .reuseToken
        (.word32 address) (.reuseToken (some location)))
    (fitting :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
    (headerRead : heap.readLiveHeader address = .ok header) :
    (ConstructorLayout.ofInfo info).allocationBytes ≤
      header.allocationBytes.toNat := by
  cases related with
  | retainedToken _ relatedHeaderRead _ minimum =>
      have layoutMinimum :=
        findFittingReuseCapacityEvidence?_retained_layoutFits
          facts tokenId info _ fitting
      have rawHeaderRead :=
        (MemoryState.PrefixExtension.readLiveHeader_facts heap address header
          headerRead).2.1
      rw [rawHeaderRead] at relatedHeaderRead
      injection relatedHeaderRead with headerEq
      subst header
      exact Nat.le_trans layoutMinimum minimum

/--
Operation-level reuse refinement with no free `layoutFits` premise. The
validator supplies a fitting fact, and `ReuseCapacityValueRel` ties that fact
to the exact live header consumed by `reuseStep`.
-/
theorem reuseStep_some_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {oldInfo : LCNF.CtorInfo}
    {oldFieldKinds : Array AbiKind} {old : ConstructorObject}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {resultKind : AbiKind} {fields : List Word32}
    {semanticFields : Array Value} {updateHeader : Bool}
    {physicalArgs : List Wasm.Value} {header : Header}
    {facts : ReuseCapacityFacts} {tokenId : FVarId}
    {evidence : ReuseCapacityEvidence}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (address, fields))
    (capacityRelated :
      ReuseCapacityValueRel initial.host.runtime.heap witness evidence
        .reuseToken (.word32 address) (.reuseToken (some location)))
    (capacityFitting :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (descriptor : witness.descriptors.lookup? address =
      some (.constructor oldInfo oldFieldKinds))
    (objectEq : cell.object = .ctor old)
    (objectRelated : ConstructorObjectRel initial.host.runtime.heap witness
      address oldInfo oldFieldKinds old)
    (headerRead : initial.host.runtime.heap.readLiveHeader address = .ok header)
    (headerKind : header.kind = .constructor)
    (refCount : header.refCount.toNat = cell.rc)
    (persistent : header.persistent = cell.persistent)
    (ordinary : cell.persistent = false)
    (cellLive : cell.live = true)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields.toArray[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultKindSupported : resultKind = .object ∨ resultKind = .tobject) :
    ∃ heap nextRuntime,
      let nextWitness := witness.rebindConstructor address info fieldKinds
      reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)] (replaceHeap initial heap) ∧
      WitnessTransport witness nextWitness ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        nextRuntime ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value)) (.object (.heap location)) ∧
      HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      reuse runtime (.reuseToken (some location)) info updateHeader
          semanticFields = .ok (nextRuntime, .object (.heap location)) := by
  have layoutFits :=
    capacityRelated.reuseToken_some_layoutFits capacityFitting headerRead
  exact reuseStep_some_of_refines runtimeRelated argsLength decoded mapped found
    descriptor objectEq objectRelated headerRead headerKind refCount persistent
    ordinary cellLive layoutFits arity semanticArity fieldKindsSize
    fieldKindsValid fieldRelated tagFits objectFieldsFit usizeFieldsFit
    scalarBytesFit resultKindSupported

end FirTalos.Concrete
