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

theorem valueRel_taggedObject_related
    {witness : RefinementWitness} {kind : AbiKind}
    {word : Word32} {payload : UInt64}
    (related :
      ValueRel witness kind (.word32 word)
        (.object (.tagged payload))) :
    TaggedReferenceRel witness word payload := by
  cases related with
  | tagged taggedRelated => exact taggedRelated
  | tobject objectRelated =>
      cases objectRelated with
      | tagged taggedRelated => exact taggedRelated

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

/-- Boxing either encodes a tagged payload (immediate or promoted) or
allocates a fresh heap box. Both branches preserve all old mapped extents. -/
theorem HeaderCapacityTransport.boxScalar
    (state result : MemoryState) (witness : RefinementWitness)
    (scalar : BoxedScalar) (word : Word32)
    (valid : state.FrontierInvariant)
    (boxed : boxScalar state scalar = .ok (result, word)) :
    HeaderCapacityTransport state result witness := by
  by_cases tagged : scalar.payload.toNat ≤ maxTaggedPayload
  · have encoded :
        encodeTagged state scalar.payload = .ok (result, word) := by
      rw [← boxScalar_of_tagged state scalar tagged]
      exact boxed
    exact MappedHeaderCapacityTransport.encodeTagged state result witness
      scalar.payload word valid encoded
  · have large : maxTaggedPayload < scalar.payload.toNat :=
      Nat.lt_of_not_ge tagged
    have allocated :
        allocateBoxedScalar state scalar = .ok (result, word) := by
      rw [← boxScalar_of_heap state scalar large]
      exact boxed
    exact .ofPrefixExtension witness
      (allocateBoxedScalar_prefixExtension state result scalar word valid
        allocated)

/-- Natural literals use the same immediate/promoted tagged split below the
semantic limit and fresh limb allocation above it. -/
theorem HeaderCapacityTransport.allocateNatural
    (state result : MemoryState) (witness : RefinementWitness)
    (value : Nat) (word : Word32)
    (valid : state.FrontierInvariant)
    (allocated : Fir.Wasm.Concrete.allocateNatural state value =
      .ok (result, word)) :
    HeaderCapacityTransport state result witness := by
  by_cases tagged : value ≤ maxTaggedPayload
  · have encoded :
        encodeTagged state (UInt64.ofNat value) = .ok (result, word) := by
      simpa [Fir.Wasm.Concrete.allocateNatural, tagged] using allocated
    exact MappedHeaderCapacityTransport.encodeTagged state result witness
      (UInt64.ofNat value) word valid encoded
  · have large : maxTaggedPayload < value := Nat.lt_of_not_ge tagged
    exact .ofPrefixExtension witness
      (allocateNatural_heap_prefixExtension state result value word valid large
        allocated)

/-- String literals are fresh prefix extensions. -/
theorem HeaderCapacityTransport.allocateString
    (state result : MemoryState) (witness : RefinementWitness)
    (value : String) (word : Word32)
    (valid : state.FrontierInvariant)
    (allocated : Fir.Wasm.Concrete.allocateString state value =
      .ok (result, word)) :
    HeaderCapacityTransport state result witness :=
  .ofPrefixExtension witness
    (allocateString_prefixExtension state result value word valid allocated)

/-- Partial application allocates one fresh closure above the old frontier. -/
theorem HeaderCapacityTransport.allocateClosure
    (state result : MemoryState) (witness : RefinementWitness)
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (function : Lean.Name) (arity : Nat) (captureKinds : Array AbiKind)
    (captures : Array LaneValue) (address : Word32)
    (targetId descriptorId : UInt32)
    (valid : state.FrontierInvariant)
    (count : captureKinds.size = captures.size)
    (capturesLtArity : captures.size < arity)
    (targetIdEq : closureTargetId dispatch function = .ok targetId)
    (descriptorIdEq :
      closureDescriptorId descriptors captureKinds = .ok descriptorId)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.size < UInt32.size)
    (captureTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      captureKinds[index]? = some kind →
      captures[index]? = some lane →
      lane.valueType = kind.valueType)
    (allocated : Fir.Wasm.Concrete.allocateClosure state dispatch descriptors
      function arity captureKinds captures = .ok (result, address)) :
    HeaderCapacityTransport state result witness :=
  .ofPrefixExtension witness
    (allocateClosure_prefixExtension state result dispatch descriptors function
      arity captureKinds captures address targetId descriptorId valid count
      capturesLtArity targetIdEq descriptorIdEq arityFits fixedFits
      captureTyped allocated)

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

/-- Erasing a tracked name removes every occurrence with the same Lean name,
including shadowed entries left by an earlier binding. -/
theorem findReuseCapacityEvidence?_erase_same
    (facts : ReuseCapacityFacts) (erased query : FVarId)
    (same : erased.name = query.name) :
    findReuseCapacityEvidence? (eraseReuseCapacityFact facts erased) query =
      none := by
  induction facts with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨candidate, evidence⟩
      unfold eraseReuseCapacityFact at ih ⊢
      simp only [List.filter_cons]
      by_cases removed : candidate.name = erased.name
      · simp [removed]
        exact ih
      · have candidateQuery : candidate.name ≠ query.name := by
          intro equal
          exact removed (equal.trans same.symm)
        simp [removed, findReuseCapacityEvidence?, candidateQuery]
        exact ih

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

/-- The constructor head of the static validator passes its exact newly
inserted fact to the continuation. -/
theorem reuseCapacitySafeCode_constructor_head
    {facts : ReuseCapacityFacts} {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure} {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    (valueEq : decl.value = .ctor info args)
    (safe : reuseCapacitySafeCode facts (.let decl continuation) = true) :
    reuseCapacitySafeCode
      (insertReuseCapacityFact facts decl.fvarId
        (constructorReuseCapacityEvidence info))
      continuation = true := by
  apply reuseCapacitySafeCode_let_head facts _ decl continuation ?_ safe
  simp [reuseCapacityLetFacts?, valueEq]

/-- When reset's source is tracked, the validator transfers that same fact to
the result binding and checks the continuation under it. -/
theorem reuseCapacitySafeCode_reset_tracked_head
    {facts : ReuseCapacityFacts} {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure} {count : Nat}
    {objectId : FVarId} {evidence : ReuseCapacityEvidence}
    (valueEq : decl.value = .reset count objectId)
    (tracked :
      findReuseCapacityEvidence? facts objectId = some evidence)
    (safe : reuseCapacitySafeCode facts (.let decl continuation) = true) :
    reuseCapacitySafeCode
      (insertReuseCapacityFact facts decl.fvarId evidence) continuation =
        true := by
  apply reuseCapacitySafeCode_let_head facts _ decl continuation ?_ safe
  simp [reuseCapacityLetFacts?, valueEq, tracked]

/-- When reset's source is untracked, the validator erases any shadowed
destination fact before checking the continuation. -/
theorem reuseCapacitySafeCode_reset_untracked_head
    {facts : ReuseCapacityFacts} {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure} {count : Nat}
    {objectId : FVarId}
    (valueEq : decl.value = .reset count objectId)
    (untracked : findReuseCapacityEvidence? facts objectId = none)
    (safe : reuseCapacitySafeCode facts (.let decl continuation) = true) :
    reuseCapacitySafeCode
      (eraseReuseCapacityFact facts decl.fvarId) continuation = true := by
  apply reuseCapacitySafeCode_let_head facts _ decl continuation ?_ safe
  simp [reuseCapacityLetFacts?, valueEq, untracked]

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

/-- Resolve one tracked static fact against a known source binding and its
compiler-assigned local. This is the operation-independent lookup boundary
used by reset; fitting reuse is the reuse-token specialization below. -/
theorem ReuseCapacityFactsRel.resolveTracked
    {facts : ReuseCapacityFacts}
    {bindings : List (FVarId × AbiKind)} {sourceEnv : Env}
    {targetLocals : Wasm.Locals} {heap : MemoryState}
    {witness : RefinementWitness} {fvarId : FVarId}
    {evidence : ReuseCapacityEvidence} {index : Nat} {kind : AbiKind}
    {semantic : Value}
    (related :
      ReuseCapacityFactsRel facts bindings sourceEnv targetLocals heap witness)
    (tracked :
      findReuseCapacityEvidence? facts fvarId = some evidence)
    (sourceLookup : lookup sourceEnv fvarId = some semantic)
    (localFound : findFVar? bindings fvarId = some index)
    (kindAt : bindings[index]?.map Prod.snd = some kind) :
    ∃ lane,
      targetLocals.get index = some (physicalOfLane lane) ∧
      ReuseCapacityValueRel heap witness evidence kind lane semantic := by
  obtain ⟨actualIndex, actualKind, lane, actualSemantic,
      actualSourceLookup, actualLocalFound, actualKindAt, targetLookup,
      capacityRelated⟩ := related.resolve tracked
  rw [sourceLookup] at actualSourceLookup
  have semanticEq := Option.some.inj actualSourceLookup
  subst actualSemantic
  rw [localFound] at actualLocalFound
  have indexEq := Option.some.inj actualLocalFound
  subst actualIndex
  rw [kindAt] at actualKindAt
  have kindEq := Option.some.inj actualKindAt
  subst actualKind
  exact ⟨lane, targetLookup, capacityRelated⟩

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

/-- Bind an ordinary result while erasing any stale capacity fact for its
destination. Every differently named fact survives the heap and witness
transition, and the checked local write frames its compiler-assigned local. -/
theorem ReuseCapacityFactsRel.eraseBind
    {facts : ReuseCapacityFacts}
    {bindings : List (FVarId × AbiKind)} {sourceEnv : Env}
    {targetLocals updatedLocals : Wasm.Locals}
    {before after : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    {result : FVarId} {resultIndex : Nat} {semantic : Value}
    (related :
      ReuseCapacityFactsRel facts bindings sourceEnv targetLocals before
        beforeWitness)
    (resultFound : findFVar? bindings result = some resultIndex)
    (localUpdate :
      FirTalos.Correctness.LocalUpdate targetLocals updatedLocals resultIndex
        value)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport before after beforeWitness) :
    ReuseCapacityFactsRel (eraseReuseCapacityFact facts result) bindings
      (Fir.LeanIR.Impure.bind sourceEnv result semantic) updatedLocals after
      afterWitness := by
  intro fvarId evidence found
  have different : result.name ≠ fvarId.name := by
    intro same
    have erasedNone :=
      findReuseCapacityEvidence?_erase_same facts result fvarId same
    rw [erasedNone] at found
    contradiction
  have oldFound :
      findReuseCapacityEvidence? facts fvarId = some evidence := by
    rw [← findReuseCapacityEvidence?_erase_other facts result fvarId different]
    exact found
  obtain ⟨index, kind, lane, oldSemantic, sourceLookup, localFound, kindAt,
      targetLookup, valueRelated⟩ := related.resolve oldFound
  have differentIndex :=
    FirTalos.Correctness.findFVar?_ne_of_name_ne bindings different
      resultFound localFound
  have boundSourceLookup :
      lookup (Fir.LeanIR.Impure.bind sourceEnv result semantic) fvarId =
        some oldSemantic := by
    simpa [Fir.LeanIR.Impure.bind, lookup, different] using sourceLookup
  have updatedLookup :
      updatedLocals.get index = some (physicalOfLane lane) :=
    (localUpdate.2 differentIndex.symm).trans targetLookup
  exact ⟨index, kind, lane, oldSemantic, boundSourceLookup, localFound, kindAt,
    updatedLookup,
    valueRelated.transport witnessTransport capacityTransport⟩

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
  exact related.resolveTracked tracked sourceLookup localFound kindAt

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

/-- Resolve a tracked source binding from the strengthened state. -/
theorem ReuseCapacityStateRelated.resolveTracked
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {fvarId : FVarId}
    {evidence : ReuseCapacityEvidence} {index : Nat} {kind : AbiKind}
    {semantic : Value}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (tracked :
      findReuseCapacityEvidence? facts fvarId = some evidence)
    (sourceLookup : lookup sourceEnv fvarId = some semantic)
    (localFound :
      findFVar? (functionBindings sourceFunction) fvarId = some index)
    (kindAt :
      (functionBindings sourceFunction)[index]?.map Prod.snd = some kind) :
    ∃ lane,
      targetLocals.get index = some (physicalOfLane lane) ∧
      ReuseCapacityValueRel targetStore.host.runtime.heap witness evidence kind
        lane semantic :=
  related.2.resolveTracked tracked sourceLookup localFound kindAt

/-- Bind a result whose capacity evidence is known. This is the generic
result-producing counterpart of `transport`: the ordinary state theorem owns
the semantic/runtime transition, while the fact relation owns the checked
destination-local write and the new evidence. -/
theorem ReuseCapacityStateRelated.bindResult
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {beforeWitness afterWitness : RefinementWitness}
    {result : FVarId} {resultIndex : Nat} {kind : AbiKind}
    {lane : LaneValue} {semantic : Value}
    {evidence : ReuseCapacityEvidence}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (finalRelated :
      StateRelated sourceFunction nextRuntime
        (Fir.LeanIR.Impure.bind sourceEnv result semantic) nextStore nextLocals
        afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (localUpdate :
      FirTalos.Correctness.LocalUpdate targetLocals nextLocals resultIndex
        (physicalOfLane lane))
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness)
    (valueRelated :
      ReuseCapacityValueRel nextStore.host.runtime.heap afterWitness evidence
        kind lane semantic) :
    ReuseCapacityStateRelated (insertReuseCapacityFact facts result evidence)
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv result semantic) nextStore nextLocals
      afterWitness := by
  exact ⟨finalRelated, related.2.bind resultFound kindAt localUpdate
    witnessTransport capacityTransport valueRelated⟩

/-- Bind an ordinary result while dropping any capacity evidence shadowed by
its destination. The operation still has to transport all old headers, but no
capacity claim is made for the new value. -/
theorem ReuseCapacityStateRelated.eraseResult
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {beforeWitness afterWitness : RefinementWitness}
    {result : FVarId} {resultIndex : Nat} {semantic : Value}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (finalRelated :
      StateRelated sourceFunction nextRuntime
        (Fir.LeanIR.Impure.bind sourceEnv result semantic) nextStore nextLocals
        afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (localUpdate :
      FirTalos.Correctness.LocalUpdate targetLocals nextLocals resultIndex
        value)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness) :
    ReuseCapacityStateRelated (eraseReuseCapacityFact facts result)
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv result semantic) nextStore nextLocals
      afterWitness := by
  exact ⟨finalRelated, related.2.eraseBind resultFound localUpdate
    witnessTransport capacityTransport⟩

/-- Add one tracked result to the strengthened state produced by an existing
direct-`let` simulation. Source evaluation, compiler adaptation, ordinary
state refinement, and Wasm weakest preconditions remain owned by
`LetStepSimulates`. -/
theorem ReuseCapacityStateRelated.ofLetStepBind
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {kind : AbiKind} {lane : LaneValue}
    {evidence : ReuseCapacityEvidence}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (localUpdate :
      FirTalos.Correctness.LocalUpdate targetLocals nextLocals resultIndex
        (physicalOfLane lane))
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness)
    (valueRelated :
      ReuseCapacityValueRel nextStore.host.runtime.heap afterWitness evidence
        kind lane sourceValue) :
    ReuseCapacityStateRelated
      (insertReuseCapacityFact facts decl.fvarId evidence) sourceFunction
      nextRuntime (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue)
      nextStore nextLocals afterWitness :=
  related.bindResult step.2.2.1 resultFound kindAt localUpdate
    witnessTransport capacityTransport valueRelated

/-- Erase a direct `let` destination's stale fact while transporting every
other fact across the already proved source/target step. -/
theorem ReuseCapacityStateRelated.ofLetStepErase
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (localUpdate :
      FirTalos.Correctness.LocalUpdate targetLocals nextLocals resultIndex
        value)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness) :
    ReuseCapacityStateRelated (eraseReuseCapacityFact facts decl.fvarId)
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue) nextStore
      nextLocals afterWitness :=
  related.eraseResult step.2.2.1 resultFound localUpdate witnessTransport
    capacityTransport

/-- The checked `localSet` form used by constructor, reset, and reuse results.
All three operations return a wasm32 lane, so this packages their common
syntax-level capacity continuation rule. -/
theorem ReuseCapacityStateRelated.ofWord32LetStepBind
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {kind : AbiKind} {word : Word32} {evidence : ReuseCapacityEvidence}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (targetSet :
      targetLocals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
        some nextLocals)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness)
    (valueRelated :
      ReuseCapacityValueRel nextStore.host.runtime.heap afterWitness evidence
        kind (.word32 word) sourceValue) :
    ReuseCapacityStateRelated
      (insertReuseCapacityFact facts decl.fvarId evidence) sourceFunction
      nextRuntime (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue)
      nextStore nextLocals afterWitness := by
  apply related.ofLetStepBind step resultFound kindAt
      (witnessTransport := witnessTransport)
      (capacityTransport := capacityTransport)
      (valueRelated := valueRelated)
  simpa [physicalOfLane] using
    FirTalos.Correctness.localUpdate_of_set? targetSet

/-- Checked-local-write specialization for ordinary result-producing lets.
The destination fact is erased while all differently named facts are
transported. -/
theorem ReuseCapacityStateRelated.ofLetStepEraseOfSet
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness} {physical : Wasm.Value}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (targetSet :
      targetLocals.set? resultIndex physical = some nextLocals)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness) :
    ReuseCapacityStateRelated (eraseReuseCapacityFact facts decl.fvarId)
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue) nextStore
      nextLocals afterWitness :=
  related.ofLetStepErase step resultFound
    (FirTalos.Correctness.localUpdate_of_set? targetSet) witnessTransport
    capacityTransport

/-- Direct constructor-result specialization. Its fact is exactly the one
inserted by `reuseCapacitySafeCode`, independently of whether the concrete
representation is immediate, promoted, or an ordinary heap object. -/
theorem ReuseCapacityStateRelated.ofConstructorLetStep
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {info : LCNF.CtorInfo}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {kind : AbiKind} {word : Word32}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (targetSet :
      targetLocals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
        some nextLocals)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness)
    (valueRelated :
      ReuseCapacityValueRel nextStore.host.runtime.heap afterWitness
        (constructorReuseCapacityEvidence info) kind (.word32 word)
        sourceValue) :
    ReuseCapacityStateRelated
      (insertReuseCapacityFact facts decl.fvarId
        (constructorReuseCapacityEvidence info))
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue) nextStore
      nextLocals afterWitness :=
  related.ofWord32LetStepBind step resultFound kindAt targetSet
    witnessTransport capacityTransport valueRelated

/-- Direct reset-result specialization. Static reset transfers the source
fact unchanged to the reuse-token destination. -/
theorem ReuseCapacityStateRelated.ofResetLetStep
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceToken : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {word : Word32} {evidence : ReuseCapacityEvidence}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceToken targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .reuseToken)
    (targetSet :
      targetLocals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
        some nextLocals)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness)
    (valueRelated :
      ReuseCapacityValueRel nextStore.host.runtime.heap afterWitness evidence
        .reuseToken (.word32 word) sourceToken) :
    ReuseCapacityStateRelated
      (insertReuseCapacityFact facts decl.fvarId evidence)
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceToken) nextStore
      nextLocals afterWitness :=
  related.ofWord32LetStepBind step resultFound kindAt targetSet
    witnessTransport capacityTransport valueRelated

/-- Direct reuse-result specialization. Static reuse records the replacement
layout selected by `ReuseCapacityEvidence.afterReuse`. -/
theorem ReuseCapacityStateRelated.ofReuseLetStep
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {info : LCNF.CtorInfo}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {kind : AbiKind} {word : Word32}
    {evidence : ReuseCapacityEvidence}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (targetSet :
      targetLocals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
        some nextLocals)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness)
    (valueRelated :
      ReuseCapacityValueRel nextStore.host.runtime.heap afterWitness
        (evidence.afterReuse info) kind (.word32 word) sourceValue) :
    ReuseCapacityStateRelated
      (insertReuseCapacityFact facts decl.fvarId
        (evidence.afterReuse info))
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue) nextStore
      nextLocals afterWitness :=
  related.ofWord32LetStepBind step resultFound kindAt targetSet
    witnessTransport capacityTransport valueRelated

/-- Ordinary heap-preserving result operations erase the destination fact and
transport every other fact reflexively. This covers projections, unboxing,
sharing tests, and every scalar result whose concrete host leaves the heap
unchanged. -/
theorem ReuseCapacityStateRelated.ofHeapPreservingLetStepErase
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {physical : Wasm.Value}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (targetSet :
      targetLocals.set? resultIndex physical = some nextLocals)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (heapEq :
      nextStore.host.runtime.heap = targetStore.host.runtime.heap) :
    ReuseCapacityStateRelated (eraseReuseCapacityFact facts decl.fvarId)
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue) nextStore
      nextLocals afterWitness := by
  apply related.ofLetStepEraseOfSet step resultFound targetSet
    witnessTransport
  rw [heapEq]
  exact .refl _ beforeWitness

/-- Ordinary allocating result operations erase the destination fact while
transporting all older facts through their fresh-prefix heap extension. This
covers boxing, literals, and closure allocation. -/
theorem ReuseCapacityStateRelated.ofPrefixExtendingLetStepErase
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {physical : Wasm.Value}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (targetSet :
      targetLocals.set? resultIndex physical = some nextLocals)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (heapExtension :
      targetStore.host.runtime.heap.PrefixExtension
        nextStore.host.runtime.heap) :
    ReuseCapacityStateRelated (eraseReuseCapacityFact facts decl.fvarId)
      sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue) nextStore
      nextLocals afterWitness :=
  related.ofLetStepEraseOfSet step resultFound targetSet witnessTransport
    (.ofPrefixExtension beforeWitness heapExtension)

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

/-- Shared fresh-allocation boundary for nonempty constructor and zero-token
reuse. It records the exact new header bound independently of the generated
host-call instruction sequence. -/
theorem ConcreteRuntimeRel.nonemptyConstructorCapacityEvidence
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {resultKind : AbiKind} {fields : Array Word32}
    {semanticFields : Array Value} {address : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (allocated :
      allocateConstructor concrete.heap info fields = .ok (result, address)) :
    let nextWitness :=
      witness.bindConstructor runtime.nextLocation address info fieldKinds
    witness.Extends nextWitness ∧
      ValueRel nextWitness resultKind (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      ReuseCapacityValueRel result nextWitness
        (constructorReuseCapacityEvidence info) resultKind (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      HeaderCapacityTransport concrete.heap result witness := by
  dsimp only
  obtain ⟨extension, _, exactRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorNonempty related
      arity semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty
      tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have valueRelated :=
    objectConstructorResult_of_refines nonempty resultRefines exactRelated
  have objectFacts :=
    allocateConstructor_nonempty_objectRel concrete.heap result witness info
      fieldKinds fields semanticFields address related.heap.frontier arity
      semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty tagFits
      objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  rcases objectFacts with ⟨_, objectRelated, _⟩
  have heapExtension :=
    allocateConstructor_nonempty_prefixExtension concrete.heap result info
      fields address related.heap.frontier arity nonempty tagFits
      objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have capacityValue :=
    ReuseCapacityValueRel.retainedObject_of_constructor valueRelated
      (objectRelated.witnessExtension extension)
  have evidenceEq :
      constructorReuseCapacityEvidence info =
        .retainedAtLeast
          (ConstructorLayout.ofInfo info).allocationBytes := by
    simp [constructorReuseCapacityEvidence, constructorAllocatesHeap]
    tauto
  exact ⟨extension, valueRelated, by simpa [evidenceEq] using capacityValue,
    HeaderCapacityTransport.ofPrefixExtension witness heapExtension⟩

/-- Nonempty constructor allocation realizes the validator's exact fresh
allocation bound and preserves every capacity fact owned by the old heap. -/
theorem allocCtorNonemptyStep_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value} {heap : MemoryState} {address : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size)
    (decoded : decodeConstructorWords 0 physicalArgs = .ok fields)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields.toArray[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (allocated :
      allocateConstructor initial.host.runtime.heap info fields.toArray =
        .ok (heap, address)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)]
          (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value))
        (.object (.heap runtime.nextLocation)) ∧
      ReuseCapacityValueRel heap nextWitness
        (constructorReuseCapacityEvidence info) resultKind (.word32 address)
        (.object (.heap runtime.nextLocation)) ∧
      HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      allocCtor runtime info semanticFields =
        .ok (semanticConstructorResult runtime info semanticFields,
          .object (.heap runtime.nextLocation)) := by
  obtain ⟨extension, concreteStep, nextRuntimeRelated, physicalRelated,
      semanticStep⟩ :=
    allocCtorNonemptyStep_of_refines runtimeRelated argsLength decoded arity
      semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty
      tagFits objectFieldsFit usizeFieldsFit scalarBytesFit resultRefines
      allocated
  have objectFacts :=
    allocateConstructor_nonempty_objectRel initial.host.runtime.heap heap
      witness info fieldKinds fields.toArray semanticFields address
      runtimeRelated.heap.frontier arity semanticArity fieldKindsSize
      fieldKindsValid fieldRelated nonempty tagFits objectFieldsFit
      usizeFieldsFit scalarBytesFit allocated
  rcases objectFacts with ⟨_, objectRelated, _⟩
  have heapExtension :=
    allocateConstructor_nonempty_prefixExtension initial.host.runtime.heap heap
      info fields.toArray address runtimeRelated.heap.frontier arity nonempty
      tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  obtain ⟨lane, decodedLane, valueRelated⟩ :=
    decodePhysicalLane_of_related physicalRelated
  have decodedAddress :
      decodePhysicalLane resultKind (.i32 (UInt32.ofNat address.value)) =
        .ok (.word32 address) := by
    cases resultKind <;>
      simp [decodePhysicalLane, AbiKind.valueType, constructorKind, nonempty,
        AbiKind.refines, Word32.ofUInt32_ofNat_value] at resultRefines ⊢
  rw [decodedAddress] at decodedLane
  have laneEq := Except.ok.inj decodedLane
  subst lane
  have capacityValue :=
    ReuseCapacityValueRel.retainedObject_of_constructor valueRelated
      (objectRelated.witnessExtension extension)
  have evidenceEq :
      constructorReuseCapacityEvidence info =
        .retainedAtLeast
          (ConstructorLayout.ofInfo info).allocationBytes := by
    simp [constructorReuseCapacityEvidence, constructorAllocatesHeap]
    tauto
  have nextCapacity :
      ReuseCapacityValueRel heap
        (witness.bindConstructor runtime.nextLocation address info fieldKinds)
        (constructorReuseCapacityEvidence info) resultKind (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
    simpa [evidenceEq] using capacityValue
  refine ⟨_, extension, concreteStep, nextRuntimeRelated, physicalRelated,
    nextCapacity, ?_, semanticStep⟩
  exact HeaderCapacityTransport.ofPrefixExtension witness heapExtension

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

/-- Empty-token reuse of a nonempty constructor follows the shared fresh
allocation boundary and realizes `afterReuse` as the replacement layout's
exact lower bound. -/
theorem reuseStep_none_nonempty_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : LCNF.CtorInfo}
    {updateHeader : Bool} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value} {heap : MemoryState} {address : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (Word32.zero, fields))
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields.toArray[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (reused :
      reuseObject initial.host.runtime.heap Word32.zero info updateHeader
        fields.toArray = .ok (heap, address)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)]
          (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value))
        (.object (.heap runtime.nextLocation)) ∧
      ReuseCapacityValueRel heap nextWitness
        (ReuseCapacityEvidence.afterReuse .emptyToken info) resultKind
        (.word32 address) (.object (.heap runtime.nextLocation)) ∧
      HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      reuse runtime (.reuseToken none) info updateHeader semanticFields =
        .ok (semanticConstructorResult runtime info semanticFields,
          .object (.heap runtime.nextLocation)) := by
  obtain ⟨extension, concreteStep, nextRuntimeRelated, physicalRelated,
      semanticStep⟩ :=
    reuseStep_none_nonempty_of_refines runtimeRelated argsLength decoded arity
      semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty
      tagFits objectFieldsFit usizeFieldsFit scalarBytesFit resultRefines reused
  have allocated :
      allocateConstructor initial.host.runtime.heap info fields.toArray =
        .ok (heap, address) := by
    unfold reuseObject at reused
    rw [if_pos (by decide)] at reused
    exact reused
  obtain ⟨_, _, capacityValue, capacityTransport⟩ :=
    ConcreteRuntimeRel.nonemptyConstructorCapacityEvidence runtimeRelated arity
      semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty
      tagFits objectFieldsFit usizeFieldsFit scalarBytesFit resultRefines
      allocated
  exact ⟨_, extension, concreteStep, nextRuntimeRelated, physicalRelated,
    by simpa [ReuseCapacityEvidence.afterReuse] using capacityValue,
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

/-- Definitely-empty reset evidence identifies the tagged reset branch. The
operation is a concrete heap no-op and produces the exact empty-token fact
inserted for its result binding. -/
theorem resetStep_tagged_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {payload : UInt64} {word : Word32}
    {kind : AbiKind} {count : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (capacityRelated :
      ReuseCapacityValueRel initial.host.runtime.heap witness .emptyToken kind
        (.word32 word) (.object (.tagged payload))) :
    resetStep count initial [.i32 (UInt32.ofNat word.value)] =
        .Return [.i32 (UInt32.ofNat Word32.zero.value)]
          (replaceHeap initial initial.host.runtime.heap) ∧
      ConcreteRuntimeRel
        (replaceHeap initial initial.host.runtime.heap).host.runtime witness
          runtime ∧
      ReuseCapacityValueRel initial.host.runtime.heap witness .emptyToken
        .reuseToken (.word32 Word32.zero) (.reuseToken none) ∧
      HeaderCapacityTransport initial.host.runtime.heap
        initial.host.runtime.heap witness ∧
      reset runtime count (.object (.tagged payload)) =
        .ok (runtime, .reuseToken none) := by
  have tagged :=
    valueRel_taggedObject_related capacityRelated.valueRelated
  obtain ⟨concreteReset, nextRelated, _⟩ :=
    resetStep_tagged_of_refines runtimeRelated descriptorsEq tagged count
  exact ⟨concreteReset, nextRelated, .emptyToken, .refl _ _, rfl⟩

/-- A nonunique retained object returns the empty token while keeping the
same static lower bound. The strengthened host theorem supplies the
mapped-header transport needed to preserve all other tracked facts. -/
theorem resetStep_nonunique_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {count available : Nat}
    {kind : AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (capacityRelated :
      ReuseCapacityValueRel initial.host.runtime.heap witness
        (.retainedAtLeast available) kind (.word32 address)
        (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (notUnique : cell.rc ≠ 1)
    (updated : reset runtime count (.object (.heap location)) =
      .ok (nextRuntime, .reuseToken none)) :
    ∃ heap,
      resetStep count initial [.i32 (UInt32.ofNat address.value)] =
          .Return [.i32 (UInt32.ofNat Word32.zero.value)]
            (replaceHeap initial heap) ∧
        ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
          nextRuntime ∧
        ReuseCapacityValueRel heap witness (.retainedAtLeast available)
          .reuseToken (.word32 Word32.zero) (.reuseToken none) ∧
        HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
        reset runtime count (.object (.heap location)) =
          .ok (nextRuntime, .reuseToken none) := by
  have mapped :=
    valueRel_heapObject_mapped capacityRelated.valueRelated
  obtain ⟨heap, concreteReset, nextRelated, _, capacityTransport⟩ :=
    resetStep_nonunique_of_refines_with_capacity runtimeRelated descriptorsEq
      mapped found live notUnique updated
  exact ⟨heap, concreteReset, nextRelated, .retainedEmptyToken,
    capacityTransport, updated⟩

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
        HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
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
    nextCapacity, capacityTransport, protocol⟩

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

/-- Successful in-place reuse turns a fitting retained-token bound into the
replacement constructor's exact `afterReuse` bound. The target address is
unchanged and mapped-header transport preserves its physical allocation
extent. -/
theorem ReuseCapacityValueRel.retainedObject_afterReuse
    {facts : ReuseCapacityFacts} {tokenId : FVarId}
    {info : LCNF.CtorInfo} {available : Nat}
    {before after : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    {address : Word32} {location : Location} {kind : AbiKind}
    (tokenRelated :
      ReuseCapacityValueRel before beforeWitness
        (.retainedAtLeast available) .reuseToken (.word32 address)
        (.reuseToken (some location)))
    (fitting :
      findFittingReuseCapacityEvidence? facts tokenId info =
        some (.retainedAtLeast available))
    (capacityTransport :
      HeaderCapacityTransport before after beforeWitness)
    (resultRelated :
      ValueRel afterWitness kind (.word32 address)
        (.object (.heap location))) :
    ReuseCapacityValueRel after afterWitness
      (ReuseCapacityEvidence.afterReuse (.retainedAtLeast available) info)
      kind (.word32 address) (.object (.heap location)) := by
  cases tokenRelated with
  | retainedToken valueRelated headerRead headerOwned minimum =>
      have layoutMinimum :=
        findFittingReuseCapacityEvidence?_retained_layoutFits
          facts tokenId info available fitting
      obtain ⟨nextHeader, nextHeaderRead, sameExtent, nextHeaderOwned⟩ :=
        capacityTransport address location _
          (valueRel_reuseToken_some_mapped valueRelated) headerRead headerOwned
      have nextMinimum :
          (ConstructorLayout.ofInfo info).allocationBytes ≤
            nextHeader.allocationBytes.toNat := by
        simpa [sameExtent] using Nat.le_trans layoutMinimum minimum
      have resultCapacity :
          ReuseCapacityValueRel after afterWitness
            (.retainedAtLeast
              (ConstructorLayout.ofInfo info).allocationBytes)
            kind (.word32 address) (.object (.heap location)) :=
        .retainedObject resultRelated nextHeaderRead nextHeaderOwned nextMinimum
      simpa [ReuseCapacityEvidence.afterReuse] using resultCapacity

/-- Evidence-polymorphic form used by the reuse operation theorem. A nonzero
semantic token rules out `.emptyToken`; the retained case is exactly
`retainedObject_afterReuse`. -/
theorem ReuseCapacityValueRel.object_afterReuse
    {facts : ReuseCapacityFacts} {tokenId : FVarId}
    {info : LCNF.CtorInfo} {evidence : ReuseCapacityEvidence}
    {before after : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    {address : Word32} {location : Location} {kind : AbiKind}
    (tokenRelated :
      ReuseCapacityValueRel before beforeWitness evidence .reuseToken
        (.word32 address) (.reuseToken (some location)))
    (fitting :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
    (capacityTransport :
      HeaderCapacityTransport before after beforeWitness)
    (resultRelated :
      ValueRel afterWitness kind (.word32 address)
        (.object (.heap location))) :
    ReuseCapacityValueRel after afterWitness (evidence.afterReuse info) kind
      (.word32 address) (.object (.heap location)) := by
  cases evidence with
  | emptyToken => cases tokenRelated
  | retainedAtLeast available =>
      exact tokenRelated.retainedObject_afterReuse fitting capacityTransport
        resultRelated

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
      ReuseCapacityValueRel heap nextWitness (evidence.afterReuse info)
        resultKind (.word32 address) (.object (.heap location)) ∧
      HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      reuse runtime (.reuseToken (some location)) info updateHeader
          semanticFields = .ok (nextRuntime, .object (.heap location)) := by
  have layoutFits :=
    capacityRelated.reuseToken_some_layoutFits capacityFitting headerRead
  obtain ⟨heap, nextRuntime, concreteStep, witnessTransport,
      nextRuntimeRelated, physicalRelated, capacityTransport, semanticStep⟩ :=
    reuseStep_some_of_refines runtimeRelated argsLength decoded mapped found
      descriptor objectEq objectRelated headerRead headerKind refCount
      persistent ordinary cellLive layoutFits arity semanticArity
      fieldKindsSize fieldKindsValid fieldRelated tagFits objectFieldsFit
      usizeFieldsFit scalarBytesFit resultKindSupported
  obtain ⟨lane, decodedLane, resultRelated⟩ :=
    decodePhysicalLane_of_related physicalRelated
  have decodedAddress :
      decodePhysicalLane resultKind (.i32 (UInt32.ofNat address.value)) =
        .ok (.word32 address) := by
    rcases resultKindSupported with rfl | rfl <;>
      simp [decodePhysicalLane, AbiKind.valueType,
        Word32.ofUInt32_ofNat_value]
  rw [decodedAddress] at decodedLane
  have laneEq := Except.ok.inj decodedLane
  subst lane
  have resultCapacity :=
    capacityRelated.object_afterReuse capacityFitting capacityTransport
      resultRelated
  exact ⟨heap, nextRuntime, concreteStep, witnessTransport,
    nextRuntimeRelated, physicalRelated, resultCapacity, capacityTransport,
    semanticStep⟩

end FirTalos.Concrete
