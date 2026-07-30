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

/-- Representation transport composes across successive concrete steps. -/
theorem WitnessTransport.trans
    {first second third : RefinementWitness}
    (firstSecond : WitnessTransport first second)
    (secondThird : WitnessTransport second third) :
    WitnessTransport first third := by
  intro kind lane semantic related
  exact secondThird (firstSecond related)

/-- The value-polymorphic witness transport in particular preserves every
previously mapped semantic heap location. -/
theorem WitnessTransport.location
    {before after : RefinementWitness}
    (transport : WitnessTransport before after)
    {location : Location} {address : Word32}
    (found : before.locations.lookup? location = some address) :
    after.locations.lookup? location = some address := by
  have beforeRelated :
      ValueRel before .object (.word32 address)
        (.object (.heap location)) :=
    .object (.mapped found)
  have afterRelated := transport beforeRelated
  cases afterRelated with
  | object related =>
      cases related with
      | mapped nextFound => exact nextFound

/-- Header-capacity transport composes even when the intermediate operation
extends or rebinds proof-only representation metadata. -/
theorem HeaderCapacityTransport.transAcross
    {first second third : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    (firstSecond :
      HeaderCapacityTransport first second beforeWitness)
    (witnessTransport :
      WitnessTransport beforeWitness afterWitness)
    (secondThird :
      HeaderCapacityTransport second third afterWitness) :
    HeaderCapacityTransport first third beforeWitness := by
  intro address location header mapped headerRead owned
  obtain ⟨middleHeader, middleRead, middleExtent, middleOwned⟩ :=
    firstSecond address location header mapped headerRead owned
  have middleMapped := witnessTransport.location mapped
  obtain ⟨finalHeader, finalRead, finalExtent, finalOwned⟩ :=
    secondThird address location middleHeader middleMapped middleRead
      middleOwned
  exact ⟨finalHeader, finalRead, finalExtent.trans middleExtent, finalOwned⟩

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
Partial application is a complete capacity-preserving allocation boundary.

The existing concrete refinement theorem supplies the new closure witness,
semantic runtime, result relation, and executable host step. The same checked
allocation supplies the fresh-prefix theorem used to retain every old
capacity fact. This package is shared by direct `.pap` lets and selected
underapplication candidates in closure dispatch.
-/
theorem partialApplyStep_of_capacityPreservingRefines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {function : Lean.Name} {arity fixed : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {captures : List LaneValue}
    {semantic : Array Value} {heap : MemoryState} {address : Word32}
    {targetId descriptorId : UInt32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (resultKindSupported : resultKind = .object ∨ resultKind = .tobject)
    (fixedArgs : physicalArgs.length = fixed)
    (decoded : decodePhysicalLanes 0 fieldKinds.toList physicalArgs =
      .ok captures)
    (count : fieldKinds.size = captures.toArray.size)
    (semanticCount : semantic.size = captures.toArray.size)
    (capturesLtArity : captures.toArray.size < arity)
    (targetIdEq : closureTargetId initial.host.closureDispatch function =
      .ok targetId)
    (targetLookup :
      initial.host.closureDispatch.lookup? targetId = some function)
    (descriptorIdEq : closureDescriptorId initial.host.closureDescriptors
      fieldKinds = .ok descriptorId)
    (descriptorLookup :
      initial.host.closureDescriptors.lookup? descriptorId = some fieldKinds)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq : witness.closureDescriptors =
      initial.host.closureDescriptors)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.toArray.size < UInt32.size)
    (captureTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      fieldKinds[index]? = some kind →
      captures.toArray[index]? = some lane →
      lane.valueType = kind.valueType)
    (captureRelated : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue)
        (value : Value),
      fieldKinds[index]? = some kind →
      captures.toArray[index]? = some lane →
      semantic[index]? = some value →
      ValueRel witness kind lane value)
    (allocated : allocateClosure initial.host.runtime.heap
      initial.host.closureDispatch initial.host.closureDescriptors function
      arity fieldKinds captures.toArray = .ok (heap, address)) :
    let nextWitness := witness.bindClosure runtime.nextLocation address function
      arity fieldKinds
    witness.Extends nextWitness ∧
      partialApplyStep function arity fixed fieldKinds resultKind initial
          physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)]
          (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (semanticClosureResult runtime function arity semantic) ∧
      (replaceHeap initial heap).host.failure? = none ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value))
        (.object (.heap runtime.nextLocation)) ∧
      HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      alloc runtime (.closure function arity semantic) =
        (semanticClosureResult runtime function arity semantic,
          .heap runtime.nextLocation) := by
  dsimp only
  obtain ⟨extension, operation, nextRuntimeRelated, valueRelated,
      semanticStep⟩ :=
    partialApplyStep_of_refines runtimeRelated resultKindSupported fixedArgs
      decoded count semanticCount capturesLtArity targetIdEq targetLookup
      descriptorIdEq descriptorLookup dispatchEq descriptorsEq arityFits
      fixedFits captureTyped captureRelated allocated
  have failureClear :
      (replaceHeap initial heap).host.failure? = none := by
    simp [replaceHeap, clearFailure]
  have capacityTransport :
      HeaderCapacityTransport initial.host.runtime.heap heap witness :=
    HeaderCapacityTransport.allocateClosure initial.host.runtime.heap heap
      witness initial.host.closureDispatch initial.host.closureDescriptors
      function arity fieldKinds captures.toArray address targetId descriptorId
      runtimeRelated.heap.frontier count capturesLtArity targetIdEq
      descriptorIdEq arityFits fixedFits captureTyped allocated
  exact ⟨extension, operation, nextRuntimeRelated, failureClear, valueRelated,
    capacityTransport, semanticStep⟩

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
  | retainedTaggedObject
      (related :
        ValueRel witness kind (.word32 word)
          (.object (.tagged payload))) :
      ReuseCapacityValueRel heap witness (.retainedAtLeast available) kind
        (.word32 word) (.object (.tagged payload))
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
  | retainedTaggedObject valueRelated =>
      exact .retainedTaggedObject (witnessTransport valueRelated)
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
  | retainedTaggedObject valueRelated => exact valueRelated
  | retainedEmptyToken => exact .reuseNone
  | retainedToken valueRelated _ _ _ => exact valueRelated

/-- Every tracked reuse-token value occupies the canonical wasm32 word lane. -/
theorem ReuseCapacityValueRel.reuseTokenWord
    {heap : MemoryState} {witness : RefinementWitness}
    {evidence : ReuseCapacityEvidence} {lane : LaneValue}
    {semantic : Value}
    (related :
      ReuseCapacityValueRel heap witness evidence .reuseToken lane semantic) :
    ∃ word, lane = .word32 word := by
  cases related with
  | emptyObject valueRelated => cases valueRelated
  | emptyToken => exact ⟨Word32.zero, rfl⟩
  | retainedObject valueRelated => cases valueRelated
  | retainedTaggedObject valueRelated => cases valueRelated
  | retainedEmptyToken => exact ⟨Word32.zero, rfl⟩
  | retainedToken => exact ⟨_, rfl⟩

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

/--
Semantic ownership side condition for retained reset tokens.

Capacity alone constrains only the physical allocation extent. In-place reuse
also requires a nonzero token to keep denoting an ordinary source cell. This
separate relation names that obligation while the shared validator protocol
tracked by `FIR-BUG-wasm-none-reuse-retained-token-ordinary` remains open.
-/
def ReuseTokenOrdinaryRel (facts : ReuseCapacityFacts)
    (sourceRuntime : RuntimeState) (sourceEnv : Env) : Prop :=
  ∀ (tokenId : FVarId) (available : Nat) (location : Location)
      (cell : HeapCell),
    findReuseCapacityEvidence? facts tokenId =
        some (.retainedAtLeast available) →
      lookup sourceEnv tokenId = some (.reuseToken (some location)) →
      findCell? sourceRuntime.heap location = some cell →
      cell.persistent = false

/--
The exact source-runtime condition needed to retain ordinary-token facts
across an unrelated operation.

For every cell visible after the step, if all matching cells visible before
the step were ordinary, the final cell is ordinary too. The quantified
premise deliberately covers fresh allocation: when the location was absent,
an admitted transition must still prove that any newly introduced cell is
non-persistent.
-/
def OrdinaryPersistenceTransport (before after : RuntimeState) : Prop :=
  ∀ (location : Location) (afterCell : HeapCell),
    findCell? after.heap location = some afterCell →
      (∀ beforeCell,
        findCell? before.heap location = some beforeCell →
          beforeCell.persistent = false) →
      afterCell.persistent = false

/-- Heap identity is an ordinary-persistence transport. -/
theorem OrdinaryPersistenceTransport.refl (runtime : RuntimeState) :
    OrdinaryPersistenceTransport runtime runtime := by
  intro location cell found ordinary
  exact ordinary cell found

/-- Ordinary-persistence transports compose across sequential source steps. -/
theorem OrdinaryPersistenceTransport.trans
    {first middle last : RuntimeState}
    (left : OrdinaryPersistenceTransport first middle)
    (right : OrdinaryPersistenceTransport middle last) :
    OrdinaryPersistenceTransport first last := by
  intro location lastCell lastFound firstOrdinary
  apply right location lastCell lastFound
  intro middleCell middleFound
  exact left location middleCell middleFound firstOrdinary

/-- Retain every ordinary-token fact across a source-runtime transport. -/
theorem ReuseTokenOrdinaryRel.transport
    {facts : ReuseCapacityFacts} {before after : RuntimeState}
    {sourceEnv : Env}
    (ordinary : ReuseTokenOrdinaryRel facts before sourceEnv)
    (transport : OrdinaryPersistenceTransport before after) :
    ReuseTokenOrdinaryRel facts after sourceEnv := by
  intro tokenId available location cell tracked tokenLookup found
  exact transport location cell found fun beforeCell beforeFound =>
    ordinary tokenId available location beforeCell tracked tokenLookup
      beforeFound

/--
Bind an ordinary result and erase its shadowed capacity fact while retaining
every differently named ordinary-token fact across the exact source-runtime
transport condition.
-/
theorem ReuseTokenOrdinaryRel.eraseBind
    {facts : ReuseCapacityFacts} {resultId : FVarId}
    {before after : RuntimeState} {sourceEnv : Env} {result : Value}
    (ordinary : ReuseTokenOrdinaryRel facts before sourceEnv)
    (transport : OrdinaryPersistenceTransport before after) :
    ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts resultId) after
      (Fir.LeanIR.Impure.bind sourceEnv resultId result) := by
  intro tokenId available location cell tracked tokenLookup found
  have different : resultId.name ≠ tokenId.name := by
    intro same
    have erasedNone :=
      findReuseCapacityEvidence?_erase_same facts resultId tokenId same
    rw [erasedNone] at tracked
    contradiction
  have oldTracked :
      findReuseCapacityEvidence? facts tokenId =
        some (.retainedAtLeast available) := by
    rw [← findReuseCapacityEvidence?_erase_other facts resultId tokenId
      different]
    exact tracked
  have oldLookup :
      lookup sourceEnv tokenId = some (.reuseToken (some location)) := by
    simpa [Fir.LeanIR.Impure.bind, lookup, different] using tokenLookup
  exact transport location cell found fun beforeCell beforeFound =>
    ordinary tokenId available location beforeCell oldTracked oldLookup
      beforeFound

private theorem alloc_ordinary_preserves_persistent_false
    {before after : RuntimeState} {object : HeapObject}
    {reference : ObjectRef} {location : Location}
    {beforeCell afterCell : HeapCell}
    (operation : alloc before object false = (after, reference))
    (beforeFound : findCell? before.heap location = some beforeCell)
    (beforeOrdinary : beforeCell.persistent = false)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  unfold alloc at operation
  have afterEq :
      ({ before with
        heap :=
          (before.nextLocation,
            { object := object, rc := 1, persistent := false, live := true }) ::
            before.heap
        nextLocation := before.nextLocation + 1 } : RuntimeState) =
        after :=
    congrArg Prod.fst operation
  subst after
  by_cases same : before.nextLocation = location
  · subst location
    simp [findCell?] at afterFound
    subst afterCell
    rfl
  · simp [findCell?, same, beforeFound] at afterFound
    subst afterCell
    exact beforeOrdinary

/-- Fresh ordinary allocation preserves ordinaryness at every visible source
heap location, including the newly allocated location. -/
theorem alloc_ordinaryPersistenceTransport
    {before after : RuntimeState} {object : HeapObject}
    {reference : ObjectRef}
    (operation : alloc before object false = (after, reference)) :
    OrdinaryPersistenceTransport before after := by
  intro location afterCell afterFound beforeOrdinary
  cases beforeFound : findCell? before.heap location with
  | some beforeCell =>
      exact alloc_ordinary_preserves_persistent_false operation beforeFound
        (beforeOrdinary beforeCell beforeFound) afterFound
  | none =>
      unfold alloc at operation
      have afterEq :
          ({ before with
            heap :=
              (before.nextLocation,
                { object := object, rc := 1, persistent := false,
                  live := true }) ::
                before.heap
            nextLocation := before.nextLocation + 1 } : RuntimeState) =
            after :=
        congrArg Prod.fst operation
      subst after
      by_cases same : before.nextLocation = location
      · subst location
        simp [findCell?] at afterFound
        subst afterCell
        rfl
      · simp [findCell?, same, beforeFound] at afterFound

/-- Semantic scalar boxing either leaves the source heap unchanged for a
tagged result or appends one fresh ordinary boxed cell. -/
theorem box_ordinaryPersistenceTransport
    {before after : RuntimeState} {type : Expr} {value result : Value}
    (operation : box before type value = .ok (after, result)) :
    OrdinaryPersistenceTransport before after := by
  unfold box at operation
  simp only [Bind.bind, Except.bind] at operation
  cases value with
  | scalar scalar =>
      simp only at operation
      by_cases tagged : scalar.toUInt64.toNat ≤ maxTaggedPayload
      · rw [if_pos tagged] at operation
        simp only [pure, Except.pure] at operation
        have pairEq := Except.ok.inj operation
        have afterEq : before = after := congrArg Prod.fst pairEq
        subst after
        exact OrdinaryPersistenceTransport.refl before
      · rw [if_neg tagged] at operation
        simp only [pure, Except.pure] at operation
        have pairEq := Except.ok.inj operation
        have afterEq :
            (alloc before (.boxed type (.scalar scalar))).1 = after :=
          congrArg Prod.fst pairEq
        subst after
        exact alloc_ordinaryPersistenceTransport
          (before := before)
          (after := (alloc before (.boxed type (.scalar scalar))).1)
          (object := .boxed type (.scalar scalar))
          (reference := (alloc before (.boxed type (.scalar scalar))).2)
          (operation := rfl)
  | usize value =>
      simp only at operation
      by_cases tagged : value.toNat ≤ maxTaggedPayload
      · rw [if_pos tagged] at operation
        simp only [pure, Except.pure] at operation
        have pairEq := Except.ok.inj operation
        have afterEq : before = after := congrArg Prod.fst pairEq
        subst after
        exact OrdinaryPersistenceTransport.refl before
      · rw [if_neg tagged] at operation
        simp only [pure, Except.pure] at operation
        have pairEq := Except.ok.inj operation
        have afterEq :
            (alloc before (.boxed type (.usize value))).1 = after :=
          congrArg Prod.fst pairEq
        subst after
        exact alloc_ordinaryPersistenceTransport
          (before := before)
          (after := (alloc before (.boxed type (.usize value))).1)
          (object := .boxed type (.usize value))
          (reference := (alloc before (.boxed type (.usize value))).2)
          (operation := rfl)
  | object reference => simp at operation
  | erased => simp at operation
  | reuseToken token => simp at operation

/-- Every semantic literal transition preserves ordinary persistence.
Immediate literals leave the heap unchanged; large naturals and strings append
one fresh ordinary cell. -/
theorem literal_ordinaryPersistenceTransport
    (before : RuntimeState) (lit : LCNF.LitValue) :
    OrdinaryPersistenceTransport before (literal before lit).1 := by
  cases lit with
  | nat value =>
      by_cases tagged : value ≤ maxTaggedPayload
      · simpa [literal, tagged] using
          OrdinaryPersistenceTransport.refl before
      · simpa [literal, tagged] using
          (alloc_ordinaryPersistenceTransport
            (before := before) (after := (alloc before (.natural value)).1)
            (object := .natural value)
            (reference := (alloc before (.natural value)).2)
            (operation := rfl))
  | str value =>
      change
        OrdinaryPersistenceTransport before
          (alloc before (.string value)).1
      exact alloc_ordinaryPersistenceTransport
        (before := before) (after := (alloc before (.string value)).1)
        (object := .string value)
        (reference := (alloc before (.string value)).2)
        (operation := rfl)
  | uint8 value => exact OrdinaryPersistenceTransport.refl before
  | uint16 value => exact OrdinaryPersistenceTransport.refl before
  | uint32 value => exact OrdinaryPersistenceTransport.refl before
  | uint64 value => exact OrdinaryPersistenceTransport.refl before
  | usize value => exact OrdinaryPersistenceTransport.refl before

private theorem allocCtor_preserves_persistent_false
    {before after : RuntimeState} {info : LCNF.CtorInfo}
    {args : Array Value} {result : Value} {location : Location}
    {beforeCell afterCell : HeapCell}
    (operation : allocCtor before info args = .ok (after, result))
    (beforeFound : findCell? before.heap location = some beforeCell)
    (beforeOrdinary : beforeCell.persistent = false)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  unfold allocCtor at operation
  simp only [Bind.bind, Except.bind] at operation
  by_cases wrongArity : args.size != info.size
  · rw [if_pos wrongArity] at operation
    contradiction
  · rw [if_neg wrongArity] at operation
    by_cases empty :
        info.size == 0 && info.usize == 0 && info.ssize == 0
    · rw [if_pos empty] at operation
      simp only [pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      have afterEq : before = after := congrArg Prod.fst pairEq
      subst after
      rw [beforeFound] at afterFound
      have cellEq := Option.some.inj afterFound
      subst afterCell
      exact beforeOrdinary
    · rw [if_neg empty] at operation
      let object : ConstructorObject := {
        tag := info.cidx
        objectFields := args
        usizeFields := Array.replicate info.usize 0
        scalarFields := [] }
      simp only [pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      have afterEq : (alloc before (.ctor object)).1 = after :=
        congrArg Prod.fst pairEq
      rw [← afterEq] at afterFound
      exact alloc_ordinary_preserves_persistent_false
        (before := before) (after := (alloc before (.ctor object)).1)
        (object := .ctor object) (reference := (alloc before (.ctor object)).2)
        (operation := rfl) beforeFound beforeOrdinary afterFound

/-- Every successful constructor allocation is an ordinary-persistence
transport. Empty constructors leave the heap unchanged; nonempty constructors
use fresh ordinary allocation. -/
theorem allocCtor_ordinaryPersistenceTransport
    {before after : RuntimeState} {info : LCNF.CtorInfo}
    {args : Array Value} {result : Value}
    (operation : allocCtor before info args = .ok (after, result)) :
    OrdinaryPersistenceTransport before after := by
  unfold allocCtor at operation
  simp only [Bind.bind, Except.bind] at operation
  by_cases wrongArity : args.size != info.size
  · rw [if_pos wrongArity] at operation
    contradiction
  · rw [if_neg wrongArity] at operation
    by_cases empty :
        info.size == 0 && info.usize == 0 && info.ssize == 0
    · rw [if_pos empty] at operation
      simp only [pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      have afterEq : before = after := congrArg Prod.fst pairEq
      subst after
      exact OrdinaryPersistenceTransport.refl before
    · rw [if_neg empty] at operation
      let object : ConstructorObject := {
        tag := info.cidx
        objectFields := args
        usizeFields := Array.replicate info.usize 0
        scalarFields := [] }
      simp only [pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      have afterEq : (alloc before (.ctor object)).1 = after :=
        congrArg Prod.fst pairEq
      subst after
      exact alloc_ordinaryPersistenceTransport
        (before := before) (after := (alloc before (.ctor object)).1)
        (object := .ctor object) (reference := (alloc before (.ctor object)).2)
        (operation := rfl)

private theorem setCell_preserves_persistent_false
    {before after : RuntimeState} {target location : Location}
    {targetCell replacement beforeCell afterCell : HeapCell}
    (targetFound : findCell? before.heap target = some targetCell)
    (replacementPersistent :
      replacement.persistent = targetCell.persistent)
    (operation :
      setCell before target replacement = .ok after)
    (beforeFound : findCell? before.heap location = some beforeCell)
    (beforeOrdinary : beforeCell.persistent = false)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  obtain ⟨expected, expectedOperation, targetAfter, frame, _, _, _, _, _⟩ :=
    Fir.LeanIR.Impure.setCell_spec_of_find before target targetCell
      replacement targetFound
  rw [operation] at expectedOperation
  have stateEq := Except.ok.inj expectedOperation
  subst expected
  by_cases same : location = target
  · subst location
    rw [targetFound] at beforeFound
    have beforeCellEq := Option.some.inj beforeFound
    subst beforeCell
    rw [targetAfter] at afterFound
    have afterCellEq := Option.some.inj afterFound
    subst afterCell
    rw [replacementPersistent]
    exact beforeOrdinary
  · rw [frame location same] at afterFound
    rw [beforeFound] at afterFound
    have afterCellEq := Option.some.inj afterFound
    subst afterCell
    exact beforeOrdinary

/-- Updating one cell without changing its persistence bit preserves
ordinaryness at every source heap location. -/
theorem setCell_ordinaryPersistenceTransport
    {before after : RuntimeState} {target : Location}
    {targetCell replacement : HeapCell}
    (targetFound : findCell? before.heap target = some targetCell)
    (replacementPersistent :
      replacement.persistent = targetCell.persistent)
    (operation :
      setCell before target replacement = .ok after) :
    OrdinaryPersistenceTransport before after := by
  intro location afterCell afterFound beforeOrdinary
  cases beforeFound : findCell? before.heap location with
  | some beforeCell =>
      exact setCell_preserves_persistent_false targetFound
        replacementPersistent operation beforeFound
        (beforeOrdinary beforeCell beforeFound) afterFound
  | none =>
      obtain ⟨expected, expectedOperation, _targetAfter, frame, _, _, _, _, _⟩ :=
        Fir.LeanIR.Impure.setCell_spec_of_find before target targetCell
          replacement targetFound
      rw [operation] at expectedOperation
      have stateEq := Except.ok.inj expectedOperation
      subst expected
      by_cases same : location = target
      · subst location
        rw [targetFound] at beforeFound
        contradiction
      · rw [frame location same] at afterFound
        rw [beforeFound] at afterFound
        contradiction

/-- A successful semantic reference-count increment never changes a cell's
persistence bit and never allocates a new cell. -/
theorem incValue_ordinaryPersistenceTransport
    {before after : RuntimeState} {value : Value}
    {amount : Nat} {check : Bool}
    (operation : incValue before value amount check = .ok after) :
    OrdinaryPersistenceTransport before after := by
  cases value with
  | object reference =>
      cases reference with
      | tagged tag =>
          unfold incValue at operation
          cases check <;> simp at operation
          subst after
          exact OrdinaryPersistenceTransport.refl before
      | heap target =>
          unfold incValue incLocation at operation
          simp only [Bind.bind, Except.bind] at operation
          cases targetFound : findCell? before.heap target with
          | none =>
              simp [getLiveCell, targetFound] at operation
          | some targetCell =>
              by_cases live : targetCell.live = true
              · simp only [getLiveCell, targetFound, live, ↓reduceIte]
                  at operation
                by_cases persistent : targetCell.persistent = true
                · rw [if_pos persistent] at operation
                  have stateEq := Except.ok.inj operation
                  subst after
                  exact OrdinaryPersistenceTransport.refl before
                · rw [if_neg persistent] at operation
                  exact setCell_ordinaryPersistenceTransport targetFound
                    (by rfl) operation
              · have dead : targetCell.live = false :=
                  Bool.eq_false_of_not_eq_true live
                simp [getLiveCell, targetFound, dead] at operation
  | scalar scalar => simp [incValue] at operation
  | usize value => simp [incValue] at operation
  | erased => simp [incValue] at operation
  | reuseToken token => simp [incValue] at operation

/-- Successful explicit deletion changes only reference count and liveness of
one live heap cell; the erased reset sentinel is a runtime identity. -/
theorem deleteValue_ordinaryPersistenceTransport
    {before after : RuntimeState} {value : Value}
    (operation : deleteValue before value = .ok after) :
    OrdinaryPersistenceTransport before after := by
  cases value with
  | erased =>
      have runtimeEq := Except.ok.inj operation
      subst after
      exact OrdinaryPersistenceTransport.refl before
  | object reference =>
      cases reference with
      | tagged payload => simp [deleteValue] at operation
      | heap location =>
          unfold deleteValue at operation
          cases read : getLiveCell before location with
          | error failure =>
              simp only [read, Bind.bind, Except.bind] at operation
              contradiction
          | ok cell =>
              have targetFound :
                  findCell? before.heap location = some cell :=
                (Fir.LeanIR.Passes.ElimDead.getLiveCell_spec read).1
              simp only [read, Bind.bind, Except.bind] at operation
              exact setCell_ordinaryPersistenceTransport targetFound
                (by
                  cases cell
                  rfl)
                operation
  | scalar scalar => simp [deleteValue] at operation
  | usize value => simp [deleteValue] at operation
  | reuseToken token => simp [deleteValue] at operation

/-- A successful state-threading list fold composes ordinary-persistence
transports supplied by each successful step. -/
theorem List.foldlM_ordinaryPersistenceTransport
    {α : Type} {step : RuntimeState → α → Except RuntimeFault RuntimeState}
    (stepTransport : ∀ {before after item},
      step before item = .ok after →
        OrdinaryPersistenceTransport before after)
    {items : List α} {before after : RuntimeState}
    (operation : items.foldlM (init := before) step = .ok after) :
    OrdinaryPersistenceTransport before after := by
  induction items generalizing before with
  | nil =>
      simp only [List.foldlM_nil] at operation
      have runtimeEq := Except.ok.inj operation
      subst after
      exact OrdinaryPersistenceTransport.refl before
  | cons item items ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at operation
      cases head : step before item with
      | error failure =>
          rw [head] at operation
          contradiction
      | ok middle =>
          rw [head] at operation
          exact (stepTransport head).trans (ih operation)

/-- Array-fold form used by recursive release of constructor fields and
closure captures. -/
theorem Array.foldlM_ordinaryPersistenceTransport
    {α : Type} {step : RuntimeState → α → Except RuntimeFault RuntimeState}
    (stepTransport : ∀ {before after item},
      step before item = .ok after →
        OrdinaryPersistenceTransport before after)
    {items : Array α} {before after : RuntimeState}
    (operation : items.foldlM step before = .ok after) :
    OrdinaryPersistenceTransport before after := by
  have listOperation :
      items.toList.foldlM (init := before) step = .ok after := by
    simpa only [Array.foldlM_toList] using operation
  exact List.foldlM_ordinaryPersistenceTransport stepTransport listOperation

/-- Every successful recursive semantic release preserves ordinaryness at
every source heap location. The induction follows the explicit release fuel;
parent and child updates only change reference counts and liveness. -/
theorem decLocationFuel_ordinaryPersistenceTransport
    {fuel : Nat} {before after : RuntimeState} {location : Location}
    (operation : decLocationFuel fuel before location = .ok after) :
    OrdinaryPersistenceTransport before after := by
  induction fuel generalizing before after location with
  | zero => simp [decLocationFuel] at operation
  | succ fuel ih =>
      simp only [decLocationFuel] at operation
      cases read : getLiveCell before location with
      | error failure =>
          simp only [read, Bind.bind, Except.bind] at operation
          contradiction
      | ok cell =>
          have targetFound :
              findCell? before.heap location = some cell :=
            (Fir.LeanIR.Passes.ElimDead.getLiveCell_spec read).1
          simp only [read, Bind.bind, Except.bind] at operation
          cases persistent : cell.persistent with
          | true =>
              simp only [persistent, ↓reduceIte] at operation
              have runtimeEq := Except.ok.inj operation
              subst after
              exact OrdinaryPersistenceTransport.refl before
          | false =>
              simp only [persistent, Bool.false_eq_true, ↓reduceIte]
                at operation
              by_cases zero : cell.rc = 0
              · rw [if_pos zero] at operation
                contradiction
              · rw [if_neg zero] at operation
                by_cases aboveOne : cell.rc > 1
                · rw [if_pos aboveOne] at operation
                  exact setCell_ordinaryPersistenceTransport targetFound
                    (by simp [persistent]) operation
                · rw [if_neg aboveOne] at operation
                  cases parentOperation :
                      setCell before location
                        { object := cell.object, rc := 0, live := false } with
                  | error failure =>
                      rw [parentOperation] at operation
                      contradiction
                  | ok parent =>
                      rw [parentOperation] at operation
                      apply
                        (setCell_ordinaryPersistenceTransport targetFound
                          (by simp [persistent]) parentOperation).trans
                      apply Array.foldlM_ordinaryPersistenceTransport
                        (operation := operation)
                      intro childBefore childAfter value childOperation
                      cases value with
                      | object reference =>
                          cases reference with
                          | heap child => exact ih childOperation
                          | tagged payload =>
                              simp only at childOperation
                              have runtimeEq := Except.ok.inj childOperation
                              subst childAfter
                              exact
                                OrdinaryPersistenceTransport.refl childBefore
                      | usize value | scalar value | erased | reuseToken value =>
                          simp only at childOperation
                          have runtimeEq := Except.ok.inj childOperation
                          subst childAfter
                          exact OrdinaryPersistenceTransport.refl childBefore

/-- Public recursive-release specialization. -/
theorem decLocation_ordinaryPersistenceTransport
    {before after : RuntimeState} {location : Location}
    (operation : decLocation before location = .ok after) :
    OrdinaryPersistenceTransport before after :=
  decLocationFuel_ordinaryPersistenceTransport operation

/-- One semantic decrement preserves ordinary persistence for heap operands
and is a runtime identity for checked tagged operands. -/
theorem decValueOnce_ordinaryPersistenceTransport
    {before after : RuntimeState} {value : Value} {check : Bool}
    (operation : decValueOnce before value check = .ok after) :
    OrdinaryPersistenceTransport before after := by
  cases value with
  | object reference =>
      cases reference with
      | heap location =>
          exact decLocation_ordinaryPersistenceTransport operation
      | tagged payload =>
          cases check <;> simp [decValueOnce] at operation
          subst after
          exact OrdinaryPersistenceTransport.refl before
  | usize value | scalar value | erased | reuseToken value =>
      simp [decValueOnce] at operation

/-- Repeated successful decrement composes the one-step transport across its
state-threading fold. -/
theorem decValue_ordinaryPersistenceTransport
    {before after : RuntimeState} {value : Value}
    {amount : Nat} {check : Bool}
    (operation : decValue before value amount check = .ok after) :
    OrdinaryPersistenceTransport before after := by
  apply List.foldlM_ordinaryPersistenceTransport (operation := operation)
  exact fun stepOperation =>
    decValueOnce_ordinaryPersistenceTransport stepOperation

private theorem except_bind_pure_pair_eq_ok
    {ε α β : Type} {action : Except ε α}
    {output actual : β} {result : α}
    (operation :
      (do
        let value ← action
        pure (value, output)) = .ok (result, actual)) :
    ∃ value, action = .ok value ∧ value = result ∧ output = actual := by
  cases action with
  | error failure =>
      simp only [Bind.bind, Except.bind] at operation
      contradiction
  | ok value =>
      simp only [Bind.bind, Except.bind, pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      exact ⟨value, rfl, congrArg Prod.fst pairEq,
        congrArg Prod.snd pairEq⟩

/--
Successful semantic constructor reuse never turns an ordinary pre-existing
cell persistent. Fresh reuse either leaves the heap unchanged or prepends a
new ordinary cell; retained reuse changes only the target object payload and
keeps its ownership metadata.
-/
theorem reuse_preserves_persistent_false
    {before after : RuntimeState} {token result : Value}
    {info : LCNF.CtorInfo} {updateHeader : Bool} {args : Array Value}
    {location : Location} {beforeCell afterCell : HeapCell}
    (operation :
      reuse before token info updateHeader args = .ok (after, result))
    (beforeFound : findCell? before.heap location = some beforeCell)
    (beforeOrdinary : beforeCell.persistent = false)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  cases token with
  | object reference => simp [reuse] at operation
  | usize value => simp [reuse] at operation
  | scalar value => simp [reuse] at operation
  | erased => simp [reuse] at operation
  | reuseToken location? =>
      cases location? with
      | none =>
          unfold reuse at operation
          exact allocCtor_preserves_persistent_false operation beforeFound
            beforeOrdinary afterFound
      | some target =>
          unfold reuse at operation
          simp only [Bind.bind, Except.bind] at operation
          by_cases wrongArity : args.size != info.size
          · rw [if_pos wrongArity] at operation
            contradiction
          · rw [if_neg wrongArity] at operation
            cases targetFound : findCell? before.heap target with
            | none =>
                simp [getLiveCell, targetFound] at operation
            | some targetCell =>
                by_cases live : targetCell.live = true
                · simp only [getLiveCell, targetFound, live, ↓reduceIte]
                    at operation
                  cases objectEq : targetCell.object with
                  | ctor old =>
                      simp only [objectEq] at operation
                      obtain ⟨middle, setResult, afterEq, _⟩ :=
                        except_bind_pure_pair_eq_ok operation
                      subst middle
                      exact setCell_preserves_persistent_false targetFound
                        (by rfl) setResult beforeFound beforeOrdinary afterFound
                  | closure function arity fixed =>
                      simp [objectEq] at operation
                  | boxed type value =>
                      simp [objectEq] at operation
                  | string value =>
                      simp [objectEq] at operation
                  | natural value =>
                      simp [objectEq] at operation
                  | integer value =>
                      simp [objectEq] at operation
                  | byteArray value =>
                      simp [objectEq] at operation
                  | «opaque» typeName =>
                      simp [objectEq] at operation
                · have dead : targetCell.live = false :=
                    Bool.eq_false_of_not_eq_true live
                  simp [getLiveCell, targetFound, dead] at operation

theorem allocCtor_result_is_object
    {before after : RuntimeState} {info : LCNF.CtorInfo}
    {args : Array Value} {result : Value}
    (operation : allocCtor before info args = .ok (after, result)) :
    ∃ reference, result = .object reference := by
  unfold allocCtor at operation
  simp only [Bind.bind, Except.bind] at operation
  by_cases wrongArity : args.size != info.size
  · rw [if_pos wrongArity] at operation
    contradiction
  · rw [if_neg wrongArity] at operation
    by_cases empty :
        info.size == 0 && info.usize == 0 && info.ssize == 0
    · rw [if_pos empty] at operation
      simp only [pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      exact ⟨.tagged (UInt64.ofNat info.cidx),
        (congrArg Prod.snd pairEq).symm⟩
    · rw [if_neg empty] at operation
      simp only [pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      exact ⟨(alloc before
          (.ctor {
            tag := info.cidx
            objectFields := args
            usizeFields := Array.replicate info.usize 0
            scalarFields := [] })).2,
        (congrArg Prod.snd pairEq).symm⟩

/-- Every successful semantic reuse returns an ordinary object value, never a
new reuse token. This makes the validator's inserted result fact vacuous for
the source ordinary-token relation. -/
theorem reuse_result_is_object
    {before after : RuntimeState} {token result : Value}
    {info : LCNF.CtorInfo} {updateHeader : Bool} {args : Array Value}
    (operation :
      reuse before token info updateHeader args = .ok (after, result)) :
    ∃ reference, result = .object reference := by
  cases token with
  | object reference => simp [reuse] at operation
  | usize value => simp [reuse] at operation
  | scalar value => simp [reuse] at operation
  | erased => simp [reuse] at operation
  | reuseToken location? =>
      cases location? with
      | none =>
          unfold reuse at operation
          exact allocCtor_result_is_object operation
      | some target =>
          unfold reuse at operation
          simp only [Bind.bind, Except.bind] at operation
          by_cases wrongArity : args.size != info.size
          · rw [if_pos wrongArity] at operation
            contradiction
          · rw [if_neg wrongArity] at operation
            cases targetFound : findCell? before.heap target with
            | none =>
                simp [getLiveCell, targetFound] at operation
            | some targetCell =>
                by_cases live : targetCell.live = true
                · simp only [getLiveCell, targetFound, live, ↓reduceIte]
                    at operation
                  cases objectEq : targetCell.object with
                  | ctor old =>
                      simp only [objectEq] at operation
                      obtain ⟨_, _, _, resultEq⟩ :=
                        except_bind_pure_pair_eq_ok operation
                      exact ⟨.heap target, resultEq.symm⟩
                  | closure function arity fixed =>
                      simp [objectEq] at operation
                  | boxed type value =>
                      simp [objectEq] at operation
                  | string value =>
                      simp [objectEq] at operation
                  | natural value =>
                      simp [objectEq] at operation
                  | integer value =>
                      simp [objectEq] at operation
                  | byteArray value =>
                      simp [objectEq] at operation
                  | «opaque» typeName =>
                      simp [objectEq] at operation
                · have dead : targetCell.live = false :=
                    Bool.eq_false_of_not_eq_true live
                  simp [getLiveCell, targetFound, dead] at operation

private theorem alloc_missing_after_persistent_false
    {before after : RuntimeState} {object : HeapObject}
    {reference : ObjectRef} {location : Location} {afterCell : HeapCell}
    (operation : alloc before object false = (after, reference))
    (beforeMissing : findCell? before.heap location = none)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  unfold alloc at operation
  have afterEq :
      ({ before with
        heap :=
          (before.nextLocation,
            { object := object, rc := 1, persistent := false, live := true }) ::
            before.heap
        nextLocation := before.nextLocation + 1 } : RuntimeState) =
        after :=
    congrArg Prod.fst operation
  subst after
  by_cases same : before.nextLocation = location
  · subst location
    simp [findCell?] at afterFound
    subst afterCell
    rfl
  · simp [findCell?, same, beforeMissing] at afterFound

private theorem allocCtor_missing_after_persistent_false
    {before after : RuntimeState} {info : LCNF.CtorInfo}
    {args : Array Value} {result : Value} {location : Location}
    {afterCell : HeapCell}
    (operation : allocCtor before info args = .ok (after, result))
    (beforeMissing : findCell? before.heap location = none)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  unfold allocCtor at operation
  simp only [Bind.bind, Except.bind] at operation
  by_cases wrongArity : args.size != info.size
  · rw [if_pos wrongArity] at operation
    contradiction
  · rw [if_neg wrongArity] at operation
    by_cases empty :
        info.size == 0 && info.usize == 0 && info.ssize == 0
    · rw [if_pos empty] at operation
      simp only [pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      have afterEq : before = after := congrArg Prod.fst pairEq
      subst after
      rw [beforeMissing] at afterFound
      contradiction
    · rw [if_neg empty] at operation
      let object : ConstructorObject := {
        tag := info.cidx
        objectFields := args
        usizeFields := Array.replicate info.usize 0
        scalarFields := [] }
      simp only [pure, Except.pure] at operation
      have pairEq := Except.ok.inj operation
      have afterEq : (alloc before (.ctor object)).1 = after :=
        congrArg Prod.fst pairEq
      rw [← afterEq] at afterFound
      exact alloc_missing_after_persistent_false
        (before := before) (after := (alloc before (.ctor object)).1)
        (object := .ctor object) (reference := (alloc before (.ctor object)).2)
        (operation := rfl) beforeMissing afterFound

private theorem setCell_missing_after_persistent_false
    {before after : RuntimeState} {target location : Location}
    {targetCell replacement afterCell : HeapCell}
    (targetFound : findCell? before.heap target = some targetCell)
    (operation : setCell before target replacement = .ok after)
    (beforeMissing : findCell? before.heap location = none)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  obtain ⟨expected, expectedOperation, targetAfter, frame, _, _, _, _, _⟩ :=
    Fir.LeanIR.Impure.setCell_spec_of_find before target targetCell replacement
      targetFound
  rw [operation] at expectedOperation
  have stateEq := Except.ok.inj expectedOperation
  subst expected
  by_cases same : location = target
  · subst location
    rw [targetFound] at beforeMissing
    contradiction
  · rw [frame location same] at afterFound
    rw [beforeMissing] at afterFound
    contradiction

private theorem reuse_missing_after_persistent_false
    {before after : RuntimeState} {token result : Value}
    {info : LCNF.CtorInfo} {updateHeader : Bool} {args : Array Value}
    {location : Location} {afterCell : HeapCell}
    (operation :
      reuse before token info updateHeader args = .ok (after, result))
    (beforeMissing : findCell? before.heap location = none)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  cases token with
  | object reference => simp [reuse] at operation
  | usize value => simp [reuse] at operation
  | scalar value => simp [reuse] at operation
  | erased => simp [reuse] at operation
  | reuseToken location? =>
      cases location? with
      | none =>
          unfold reuse at operation
          exact allocCtor_missing_after_persistent_false operation
            beforeMissing afterFound
      | some target =>
          unfold reuse at operation
          simp only [Bind.bind, Except.bind] at operation
          by_cases wrongArity : args.size != info.size
          · rw [if_pos wrongArity] at operation
            contradiction
          · rw [if_neg wrongArity] at operation
            cases targetFound : findCell? before.heap target with
            | none =>
                simp [getLiveCell, targetFound] at operation
            | some targetCell =>
                by_cases live : targetCell.live = true
                · simp only [getLiveCell, targetFound, live, ↓reduceIte]
                    at operation
                  cases objectEq : targetCell.object with
                  | ctor old =>
                      simp only [objectEq] at operation
                      obtain ⟨middle, setResult, afterEq, _⟩ :=
                        except_bind_pure_pair_eq_ok operation
                      subst middle
                      exact setCell_missing_after_persistent_false targetFound
                        setResult beforeMissing afterFound
                  | closure function arity fixed =>
                      simp [objectEq] at operation
                  | boxed type value =>
                      simp [objectEq] at operation
                  | string value =>
                      simp [objectEq] at operation
                  | natural value =>
                      simp [objectEq] at operation
                  | integer value =>
                      simp [objectEq] at operation
                  | byteArray value =>
                      simp [objectEq] at operation
                  | «opaque» typeName =>
                      simp [objectEq] at operation
                · have dead : targetCell.live = false :=
                    Bool.eq_false_of_not_eq_true live
                  simp [getLiveCell, targetFound, dead] at operation

/--
Pointwise form used by fact-map transport: if the old lookup is present it
must be ordinary; if it is absent, successful reuse can only introduce it via
fresh ordinary allocation.
-/
theorem reuse_preserves_ordinary_lookup
    {before after : RuntimeState} {token result : Value}
    {info : LCNF.CtorInfo} {updateHeader : Bool} {args : Array Value}
    {location : Location} {afterCell : HeapCell}
    (operation :
      reuse before token info updateHeader args = .ok (after, result))
    (beforeOrdinary :
      ∀ beforeCell,
        findCell? before.heap location = some beforeCell →
        beforeCell.persistent = false)
    (afterFound : findCell? after.heap location = some afterCell) :
    afterCell.persistent = false := by
  cases beforeFound : findCell? before.heap location with
  | none =>
      exact reuse_missing_after_persistent_false operation beforeFound
        afterFound
  | some beforeCell =>
      exact reuse_preserves_persistent_false operation beforeFound
        (beforeOrdinary beforeCell beforeFound) afterFound

/-- Successful constructor reuse is an ordinary-persistence transport. -/
theorem reuse_ordinaryPersistenceTransport
    {before after : RuntimeState} {token result : Value}
    {info : LCNF.CtorInfo} {updateHeader : Bool} {args : Array Value}
    (operation :
      reuse before token info updateHeader args = .ok (after, result)) :
    OrdinaryPersistenceTransport before after := by
  intro location afterCell afterFound beforeOrdinary
  exact reuse_preserves_ordinary_lookup operation beforeOrdinary afterFound

/--
Bind a result known to be an object while inserting any capacity evidence.
The new fact cannot denote a reuse token, and every old fact crosses the
supplied ordinary-persistence transport.
-/
theorem ReuseTokenOrdinaryRel.bindObject
    {facts : ReuseCapacityFacts} {resultId : FVarId}
    {nextEvidence : ReuseCapacityEvidence}
    {before after : RuntimeState} {sourceEnv : Env}
    {result : Value}
    (ordinary : ReuseTokenOrdinaryRel facts before sourceEnv)
    (transport : OrdinaryPersistenceTransport before after)
    (resultObject : ∃ reference, result = .object reference) :
    ReuseTokenOrdinaryRel
      (insertReuseCapacityFact facts resultId nextEvidence) after
      (Fir.LeanIR.Impure.bind sourceEnv resultId result) := by
  intro tokenId available location cell tracked tokenLookup found
  by_cases sameName : resultId.name = tokenId.name
  · have resultLookup :
        lookup (Fir.LeanIR.Impure.bind sourceEnv resultId result) tokenId =
          some result := by
      simp [Fir.LeanIR.Impure.bind, lookup, sameName]
    rw [resultLookup] at tokenLookup
    have resultToken : result = .reuseToken (some location) :=
      Option.some.inj tokenLookup
    obtain ⟨reference, resultEq⟩ := resultObject
    rw [resultEq] at resultToken
    contradiction
  · have oldTracked :
        findReuseCapacityEvidence? facts tokenId =
          some (.retainedAtLeast available) := by
      rw [← findReuseCapacityEvidence?_insert_other facts resultId tokenId
        nextEvidence sameName]
      exact tracked
    have oldLookup :
        lookup sourceEnv tokenId = some (.reuseToken (some location)) := by
      simpa [Fir.LeanIR.Impure.bind, lookup, sameName] using tokenLookup
    exact transport location cell found fun beforeCell beforeFound =>
      ordinary tokenId available location beforeCell oldTracked oldLookup
        beforeFound

/--
The authoritative fact-map insertion performed after successful reuse
preserves the ordinary-token relation. The inserted result is an object, so
only differently named old token facts remain nonvacuous.
-/
theorem ReuseTokenOrdinaryRel.bindReuse
    {facts : ReuseCapacityFacts} {resultId : FVarId}
    {nextEvidence : ReuseCapacityEvidence}
    {before after : RuntimeState} {sourceEnv : Env}
    {token result : Value} {info : LCNF.CtorInfo}
    {updateHeader : Bool} {args : Array Value}
    (ordinary : ReuseTokenOrdinaryRel facts before sourceEnv)
    (operation :
      reuse before token info updateHeader args = .ok (after, result)) :
    ReuseTokenOrdinaryRel
      (insertReuseCapacityFact facts resultId nextEvidence) after
      (Fir.LeanIR.Impure.bind sourceEnv resultId result) := by
  exact ordinary.bindObject (reuse_ordinaryPersistenceTransport operation)
    (reuse_result_is_object operation)

/-- The empty validator fact map adds no obligation to W6's ordinary state
relation. This is the initial bridge for a validated function body. -/
theorem StateRelated.withEmptyReuseCapacity
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (related :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness) :
    ReuseCapacityStateRelated [] sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness := by
  refine ⟨related, ?_⟩
  intro fvarId evidence found
  simp [findReuseCapacityEvidence?] at found

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
  | retainedTaggedObject valueRelated => cases valueRelated
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
A successful zero-token reuse of an empty-layout constructor may return a
tagged object even when the token carried retained provenance.  Retained
evidence constrains only a later *nonzero* reset token, so the tagged result
satisfies that postcondition vacuously.
-/
theorem ReuseCapacityValueRel.taggedObject_afterReuse
    {info : LCNF.CtorInfo} {evidence : ReuseCapacityEvidence}
    {heap : MemoryState} {witness : RefinementWitness}
    {kind : AbiKind} {word : Word32} {payload : UInt64}
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (resultRelated :
      ValueRel witness kind (.word32 word) (.object (.tagged payload))) :
    ReuseCapacityValueRel heap witness (evidence.afterReuse info) kind
      (.word32 word) (.object (.tagged payload)) := by
  cases evidence with
  | emptyToken =>
      have evidenceEq :
          constructorReuseCapacityEvidence info = .emptyToken := by
        simp [constructorReuseCapacityEvidence, constructorAllocatesHeap,
          empty.1.1, empty.1.2, empty.2]
      simpa [ReuseCapacityEvidence.afterReuse, evidenceEq] using
        (ReuseCapacityValueRel.emptyObject (heap := heap) resultRelated)
  | retainedAtLeast available =>
      simpa [ReuseCapacityEvidence.afterReuse] using
        (ReuseCapacityValueRel.retainedTaggedObject
          (available := (ConstructorLayout.ofInfo info).allocationBytes)
          (heap := heap) resultRelated)

/--
For a nonempty replacement, `afterReuse` selects the exact fresh constructor
extent independently of whether the zero token was definitely empty or was a
fallback from retained provenance.
-/
theorem ReuseCapacityEvidence.afterReuse_eq_emptyToken_of_nonempty
    (evidence : ReuseCapacityEvidence) (info : LCNF.CtorInfo)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)) :
    evidence.afterReuse info =
      ReuseCapacityEvidence.emptyToken.afterReuse info := by
  have allocates : constructorAllocatesHeap info = true := by
    simp [constructorAllocatesHeap]
    tauto
  cases evidence <;>
    simp [ReuseCapacityEvidence.afterReuse,
      constructorReuseCapacityEvidence, allocates]

/--
A zero reuse token takes exactly the general constructor-allocation path.
The representation-sensitive constructor budget therefore constructs both
immediate/promoted empty results and ordinary nonempty heap results.
-/
theorem MemoryState.FrontierInvariant.reuseObject_zero_eq_ok_of_budget
    {state : MemoryState} (valid : state.FrontierInvariant)
    (info : LCNF.CtorInfo) (updateHeader : Bool) (fields : Array Word32)
    (arity : fields.size = info.size)
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    {remainingBytes : Nat}
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : constructorAllocationBytes info ≤ remainingBytes) :
    ∃ result word,
      reuseObject state Word32.zero info updateHeader fields =
          .ok (result, word) ∧
        result.AddressSpaceBudget
          (remainingBytes - constructorAllocationBytes info) := by
  obtain ⟨result, word, allocated, remaining⟩ :=
    valid.allocateConstructor_eq_ok_of_budget info fields arity tagFits
      objectFieldsFit usizeFieldsFit scalarBytesFit budget fits
  refine ⟨result, word, ?_, remaining⟩
  unfold reuseObject
  rw [if_pos (by decide)]
  exact allocated

/--
Branch-independent successful zero-token reuse refinement.

The empty/nonempty constructor representation is reconstructed internally.
The theorem returns the exact validator-selected post fact for either
definitely-empty or retained fallback provenance; no representation branch is
part of its interface.
-/
theorem reuseStep_none_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {info : LCNF.CtorInfo}
    {updateHeader : Bool} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value} {sourceValue : Value}
    {heap : MemoryState} {word : Word32}
    {evidence : ReuseCapacityEvidence}
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
      ∃ field, fields.toArray[index]? = some field ∧
        ValueRel witness kind (.word32 field) value)
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (reused :
      reuseObject initial.host.runtime.heap Word32.zero info updateHeader
        fields.toArray = .ok (heap, word))
    (semanticStep :
      reuse runtime (.reuseToken none) info updateHeader semanticFields =
        .ok (nextRuntime, sourceValue)) :
    ∃ nextWitness,
      reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
          .Return [.i32 (UInt32.ofNat word.value)]
            (replaceHeap initial heap) ∧
        WitnessTransport witness nextWitness ∧
        ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
          nextRuntime ∧
        PhysicalValueRel nextWitness resultKind
          (.i32 (UInt32.ofNat word.value)) sourceValue ∧
        ReuseCapacityValueRel heap nextWitness (evidence.afterReuse info)
          resultKind (.word32 word) sourceValue ∧
        nextWitness.closureDescriptors = witness.closureDescriptors ∧
        HeaderCapacityTransport initial.host.runtime.heap heap witness := by
  by_cases empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0
  · obtain ⟨nextWitness, extension, concreteStep, nextRuntimeRelated,
        valueRelated, physicalRelated, capacityValue, capacityTransport,
        semanticExpected⟩ :=
      reuseStep_none_empty_of_capacityEvidence runtimeRelated argsLength
        decoded arity semanticArity empty tagFits resultRefines reused
    rw [semanticStep] at semanticExpected
    have resultEq := Except.ok.inj semanticExpected
    have runtimeEq : nextRuntime = runtime :=
      congrArg Prod.fst resultEq
    have valueEq :
        sourceValue = .object (.tagged (UInt64.ofNat info.cidx)) :=
      congrArg Prod.snd resultEq
    subst nextRuntime
    subst sourceValue
    exact ⟨nextWitness, concreteStep, WitnessTransport.ofExtension extension,
      nextRuntimeRelated, physicalRelated,
      ReuseCapacityValueRel.taggedObject_afterReuse
        (evidence := evidence) empty valueRelated,
      extension.closureDescriptors,
      capacityTransport⟩
  · obtain ⟨nextWitness, extension, concreteStep, nextRuntimeRelated,
        physicalRelated, capacityValue, capacityTransport, semanticExpected⟩ :=
      reuseStep_none_nonempty_of_capacityEvidence runtimeRelated argsLength
        decoded arity semanticArity fieldKindsSize fieldKindsValid
        fieldRelated empty tagFits objectFieldsFit usizeFieldsFit
        scalarBytesFit resultRefines reused
    rw [semanticStep] at semanticExpected
    have resultEq := Except.ok.inj semanticExpected
    have runtimeEq :
        nextRuntime = semanticConstructorResult runtime info semanticFields :=
      congrArg Prod.fst resultEq
    have valueEq :
        sourceValue = .object (.heap runtime.nextLocation) :=
      congrArg Prod.snd resultEq
    subst nextRuntime
    subst sourceValue
    have evidenceEq :=
      FirTalos.Concrete.ReuseCapacityEvidence.afterReuse_eq_emptyToken_of_nonempty
        evidence info empty
    exact ⟨nextWitness, concreteStep, WitnessTransport.ofExtension extension,
      nextRuntimeRelated, physicalRelated, by
        simpa [evidenceEq] using capacityValue,
      extension.closureDescriptors, capacityTransport⟩

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
      heap.heapCursor = initial.host.runtime.heap.heapCursor ∧
      HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      reuse runtime (.reuseToken (some location)) info updateHeader
          semanticFields = .ok (nextRuntime, .object (.heap location)) := by
  have layoutFits :=
    capacityRelated.reuseToken_some_layoutFits capacityFitting headerRead
  obtain ⟨heap, nextRuntime, concreteStep, witnessTransport,
      nextRuntimeRelated, physicalRelated, cursor, capacityTransport,
      semanticStep⟩ :=
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
    nextRuntimeRelated, physicalRelated, resultCapacity, cursor,
    capacityTransport, semanticStep⟩

/--
Certificate-free successful reuse refinement across all runtime branches.

Static fitting evidence and its dynamic value interpretation determine whether
the physical token is zero or names a retained allocation.  The theorem then
selects fresh tagged allocation, fresh heap allocation, or checked in-place
reuse internally.  The caller supplies only the constructive fresh-allocation
boundary, the source ordinary-token invariant, and the provenance-sensitive
result-kind condition; none of those premises contains target instructions,
numeric import indices, or a per-program simulation derivation.
-/
theorem reuseStep_of_capacityEvidence
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState}
    {sourceToken sourceValue : Value} {tokenWord : Word32}
    {info : LCNF.CtorInfo} {updateHeader : Bool}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value}
    {facts : ReuseCapacityFacts} {tokenId : FVarId}
    {evidence : ReuseCapacityEvidence}
    {remainingBytes : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (tokenWord, fields))
    (capacityRelated :
      ReuseCapacityValueRel initial.host.runtime.heap witness evidence
        .reuseToken (.word32 tokenWord) sourceToken)
    (capacityFitting :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ field, fields.toArray[index]? = some field ∧
        ValueRel witness kind (.word32 field) value)
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (resultCompatible :
      evidence = .emptyToken ∨ resultKind = .tobject)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (freshAllocated :
      sourceToken = .reuseToken none →
        ∃ heap word,
          reuseObject initial.host.runtime.heap Word32.zero info updateHeader
            fields.toArray = .ok (heap, word) ∧
          heap.AddressSpaceBudget
            (remainingBytes - constructorAllocationBytes info))
    (tokenOrdinary :
      ∀ (location : Location) (cell : HeapCell),
        sourceToken = .reuseToken (some location) →
        findCell? runtime.heap location = some cell →
        cell.persistent = false)
    (semanticStep :
      reuse runtime sourceToken info updateHeader semanticFields =
        .ok (nextRuntime, sourceValue)) :
    ∃ heap word nextWitness,
      reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
          .Return [.i32 (UInt32.ofNat word.value)]
            (replaceHeap initial heap) ∧
        WitnessTransport witness nextWitness ∧
        ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
          nextRuntime ∧
        PhysicalValueRel nextWitness resultKind
          (.i32 (UInt32.ofNat word.value)) sourceValue ∧
        ReuseCapacityValueRel heap nextWitness (evidence.afterReuse info)
          resultKind (.word32 word) sourceValue ∧
        nextWitness.closureDescriptors = witness.closureDescriptors ∧
        HeaderCapacityTransport initial.host.runtime.heap heap witness ∧
        heap.AddressSpaceBudget
          (remainingBytes - constructorAllocationBytes info) := by
  cases evidence with
  | emptyToken =>
      obtain ⟨tokenWordEq, sourceTokenEq⟩ :=
        capacityRelated.emptyToken_eq
      injection tokenWordEq with tokenWordEq
      subst tokenWord
      subst sourceToken
      obtain ⟨heap, word, reused, remainingBudget⟩ := freshAllocated rfl
      obtain ⟨nextWitness, concreteStep, transport, nextRuntimeRelated,
          physicalRelated, nextCapacity, witnessDescriptors,
          capacityTransport⟩ :=
        reuseStep_none_of_capacityEvidence runtimeRelated argsLength decoded
          arity semanticArity fieldKindsSize fieldKindsValid fieldRelated
          tagFits objectFieldsFit usizeFieldsFit scalarBytesFit resultRefines
          reused semanticStep
      exact ⟨heap, word, nextWitness, concreteStep, transport,
        nextRuntimeRelated, physicalRelated, nextCapacity,
        witnessDescriptors, capacityTransport, remainingBudget⟩
  | retainedAtLeast available =>
      rcases capacityRelated.retainedToken_cases with zero | retained
      · obtain ⟨tokenWordEq, sourceTokenEq⟩ := zero
        injection tokenWordEq with tokenWordEq
        subst tokenWord
        subst sourceToken
        obtain ⟨heap, word, reused, remainingBudget⟩ := freshAllocated rfl
        obtain ⟨nextWitness, concreteStep, transport, nextRuntimeRelated,
            physicalRelated, nextCapacity, witnessDescriptors,
            capacityTransport⟩ :=
          reuseStep_none_of_capacityEvidence runtimeRelated argsLength decoded
            arity semanticArity fieldKindsSize fieldKindsValid fieldRelated
            tagFits objectFieldsFit usizeFieldsFit scalarBytesFit resultRefines
            reused semanticStep
        exact ⟨heap, word, nextWitness, concreteStep, transport,
          nextRuntimeRelated, physicalRelated, nextCapacity,
          witnessDescriptors, capacityTransport, remainingBudget⟩
      · obtain ⟨location, address, header, tokenWordEq, sourceTokenEq,
            tokenRelated, _rawHeaderRead, _headerOwned, _minimum⟩ :=
          retained
        injection tokenWordEq with tokenWordEq
        subst tokenWord
        subst sourceToken
        have resultKindEq : resultKind = .tobject := by
          rcases resultCompatible with impossible | resultKindEq
          · contradiction
          · exact resultKindEq
        have mapped := valueRel_reuseToken_some_mapped tokenRelated
        obtain ⟨cell, found, cellRelated⟩ :=
          runtimeRelated.heap.concreteToSemantic location address mapped
        have live : cell.live = true := by
          by_contra notLive
          have dead : cell.live = false :=
            Bool.eq_false_of_not_eq_true notLive
          have impossible := semanticStep
          simp [reuse, getLiveCell, found, dead, semanticArity, Bind.bind,
            Except.bind] at impossible
        have ordinary : cell.persistent = false :=
          tokenOrdinary location cell rfl found
        cases objectEq : cell.object with
        | ctor old =>
            have liveRelated := cellRelated.live_of_eq_true live
            cases liveRelated with
            | @constructor oldInfo oldFieldKinds semantic oldHeader _
                descriptor relatedObjectEq objectRelated headerRead headerKind
                refCount persistent cellLive =>
                rw [objectEq] at relatedObjectEq
                injection relatedObjectEq with semanticEq
                subst semantic
                obtain ⟨heap, actualRuntime, concreteStep, transport,
                    nextRuntimeRelated, physicalRelated, nextCapacity,
                    cursor, capacityTransport, semanticExpected⟩ :=
                  reuseStep_some_of_capacityEvidence runtimeRelated argsLength
                    decoded capacityRelated capacityFitting mapped found
                    descriptor objectEq objectRelated headerRead headerKind
                    refCount persistent ordinary cellLive arity semanticArity
                    fieldKindsSize fieldKindsValid fieldRelated tagFits
                    objectFieldsFit usizeFieldsFit scalarBytesFit
                    (.inr resultKindEq)
                rw [semanticStep] at semanticExpected
                have resultEq := Except.ok.inj semanticExpected
                have runtimeEq : nextRuntime = actualRuntime :=
                  congrArg Prod.fst resultEq
                have valueEq :
                    sourceValue = .object (.heap location) :=
                  congrArg Prod.snd resultEq
                subst actualRuntime
                subst sourceValue
                let nextWitness :=
                  witness.rebindConstructor address info fieldKinds
                have remainingBudget :
                    heap.AddressSpaceBudget
                      (remainingBytes - constructorAllocationBytes info) :=
                  MemoryState.AddressSpaceBudget.of_heapCursor_eq
                    (budget.weaken (Nat.sub_le remainingBytes
                      (constructorAllocationBytes info))) cursor
                exact ⟨heap, address, nextWitness, concreteStep, transport,
                  nextRuntimeRelated, physicalRelated, nextCapacity, by
                    simp [nextWitness,
                      RefinementWitness.rebindConstructor],
                  capacityTransport, remainingBudget⟩
            | boxed descriptor relatedObjectEq objectRelated refCount
                persistent cellLive =>
                rw [objectEq] at relatedObjectEq
                contradiction
            | natural descriptor relatedObjectEq headerRead headerKind marker
                extent limbsFit naturalRead refCount persistent cellLive =>
                rw [objectEq] at relatedObjectEq
                contradiction
            | integer descriptor relatedObjectEq objectRelated refCount
                persistent cellLive =>
                rw [objectEq] at relatedObjectEq
                contradiction
            | string descriptor relatedObjectEq objectRelated refCount
                persistent cellLive =>
                rw [objectEq] at relatedObjectEq
                contradiction
            | closure closureRelated =>
                obtain ⟨function, arity, captures, relatedObjectEq⟩ :=
                  closureRelated.objectEq
                rw [objectEq] at relatedObjectEq
                contradiction
        | boxed type value =>
            have impossible := semanticStep
            simp [reuse, getLiveCell, found, live, semanticArity] at impossible
            simp only [Bind.bind, Except.bind] at impossible
            rw [objectEq] at impossible
            contradiction
        | natural value =>
            have impossible := semanticStep
            simp [reuse, getLiveCell, found, live, semanticArity] at impossible
            simp only [Bind.bind, Except.bind] at impossible
            rw [objectEq] at impossible
            contradiction
        | integer value =>
            have impossible := semanticStep
            simp [reuse, getLiveCell, found, live, semanticArity] at impossible
            simp only [Bind.bind, Except.bind] at impossible
            rw [objectEq] at impossible
            contradiction
        | string value =>
            have impossible := semanticStep
            simp [reuse, getLiveCell, found, live, semanticArity] at impossible
            simp only [Bind.bind, Except.bind] at impossible
            rw [objectEq] at impossible
            contradiction
        | byteArray value =>
            have impossible := semanticStep
            simp [reuse, getLiveCell, found, live, semanticArity] at impossible
            simp only [Bind.bind, Except.bind] at impossible
            rw [objectEq] at impossible
            contradiction
        | closure function arity fixed =>
            have impossible := semanticStep
            simp [reuse, getLiveCell, found, live, semanticArity] at impossible
            simp only [Bind.bind, Except.bind] at impossible
            rw [objectEq] at impossible
            contradiction
        | «opaque» typeName =>
            have impossible := semanticStep
            simp [reuse, getLiveCell, found, live, semanticArity] at impossible
            simp only [Bind.bind, Except.bind] at impossible
            rw [objectEq] at impossible
            contradiction

end FirTalos.Concrete
