import FirTalos.Correctness.Semantics
import Fir.Wasm.Concrete
import Fir.Wasm.Concrete.StringHeapCorrectness
import Interpreter.Wasm.Spec.Termination

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- Lift W6's ABI-indexed concrete lane relation to Talos runtime values. The
four constructors are the only representation conversion performed at the
host boundary; object words remain exact wasm32 bit patterns. -/
inductive PhysicalValueRel (witness : RefinementWitness) :
    AbiKind → Wasm.Value → Value → Prop where
  | word32 (related : ValueRel witness kind (.word32 word) semantic) :
      PhysicalValueRel witness kind (.i32 (UInt32.ofNat word.value)) semantic
  | word64 (related : ValueRel witness kind (.word64 word) semantic) :
      PhysicalValueRel witness kind (.i64 word) semantic
  | float32Bits (related : ValueRel witness kind (.float32Bits bits) semantic) :
      PhysicalValueRel witness kind (.f32 bits) semantic
  | float64Bits (related : ValueRel witness kind (.float64Bits bits) semantic) :
      PhysicalValueRel witness kind (.f64 bits) semantic

/-- Every live FIR binding is represented in its compiler-assigned local by a
W6 concrete lane. Unlike W5's opaque-handle relation, this relation exposes
the exact address/tag word consumed by the concrete runtime. -/
def EnvLocalsRelated (witness : RefinementWitness)
    (bindings : List (Lean.FVarId × AbiKind)) (source : Env)
    (target : Wasm.Locals) : Prop :=
  ∀ {fvar : Lean.FVarId} {value : Value}, lookup source fvar = some value →
    ∃ index kind physical,
      findFVar? bindings fvar = some index ∧
      bindings[index]?.map Prod.snd = some kind ∧
      target.get index = some physical ∧
      PhysicalValueRel witness kind physical value

theorem PhysicalValueRel.witnessExtension
    {before after : RefinementWitness} (extension : before.Extends after)
    {kind : AbiKind} {physical : Wasm.Value} {semantic : Value}
    (related : PhysicalValueRel before kind physical semantic) :
    PhysicalValueRel after kind physical semantic := by
  cases related with
  | word32 valueRelated =>
      exact .word32 (valueRelated.witnessExtension extension)
  | word64 valueRelated =>
      exact .word64 (valueRelated.witnessExtension extension)
  | float32Bits valueRelated =>
      exact .float32Bits (valueRelated.witnessExtension extension)
  | float64Bits valueRelated =>
      exact .float64Bits (valueRelated.witnessExtension extension)

/-- A representation-witness transition transports every already-related
value without changing its physical lane or semantic identity. Extensions and
reset/reuse descriptor rebindings are the two concrete instances used by W6. -/
def WitnessTransport (before after : RefinementWitness) : Prop :=
  ∀ {kind : AbiKind} {lane : LaneValue} {semantic : Value},
    ValueRel before kind lane semantic → ValueRel after kind lane semantic

theorem WitnessTransport.refl (witness : RefinementWitness) :
    WitnessTransport witness witness := by
  intro kind lane semantic related
  exact related

theorem WitnessTransport.ofExtension
    {before after : RefinementWitness} (extension : before.Extends after) :
    WitnessTransport before after := by
  intro kind lane semantic related
  exact related.witnessExtension extension

theorem WitnessTransport.rebindConstructor
    (witness : RefinementWitness) (address : Word32)
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind) :
    WitnessTransport witness
      (witness.rebindConstructor address info fieldKinds) := by
  intro kind lane semantic related
  exact related.rebindConstructor address info fieldKinds

theorem PhysicalValueRel.witnessTransport
    {before after : RefinementWitness}
    (transport : WitnessTransport before after)
    {kind : AbiKind} {physical : Wasm.Value} {semantic : Value}
    (related : PhysicalValueRel before kind physical semantic) :
    PhysicalValueRel after kind physical semantic := by
  cases related with
  | word32 valueRelated => exact .word32 (transport valueRelated)
  | word64 valueRelated => exact .word64 (transport valueRelated)
  | float32Bits valueRelated => exact .float32Bits (transport valueRelated)
  | float64Bits valueRelated => exact .float64Bits (transport valueRelated)

theorem EnvLocalsRelated.witnessTransport
    {before after : RefinementWitness}
    {bindings : List (Lean.FVarId × AbiKind)} {source : Env}
    {target : Wasm.Locals}
    (transport : WitnessTransport before after)
    (related : EnvLocalsRelated before bindings source target) :
    EnvLocalsRelated after bindings source target := by
  intro fvar value sourceLookup
  obtain ⟨index, kind, physical, found, kindAt, targetLookup, valueRelated⟩ :=
    related sourceLookup
  exact ⟨index, kind, physical, found, kindAt, targetLookup,
    valueRelated.witnessTransport transport⟩

theorem ConcreteGlobalsRel.witnessTransport
    {before after : RefinementWitness} {concrete : ConcreteGlobals}
    {semantic : Globals} (transport : WitnessTransport before after)
    (related : ConcreteGlobalsRel before concrete semantic) :
    ConcreteGlobalsRel after concrete semantic := by
  constructor
  · intro name value found
    obtain ⟨slot, lane, slotFound, initialized, valueRelated⟩ :=
      related.semanticToConcrete name value found
    exact ⟨slot, lane, slotFound, initialized, transport valueRelated⟩
  · intro name slot lane slotFound initialized
    obtain ⟨value, found, valueRelated⟩ :=
      related.concreteToSemantic name slot lane slotFound initialized
    exact ⟨value, found, transport valueRelated⟩

theorem ConcreteExternalEventRel.witnessTransport
    {before after : RefinementWitness}
    {concrete : ConcreteExternalEvent} {semantic : ExternalEvent}
    (transport : WitnessTransport before after)
    (related : ConcreteExternalEventRel before concrete semantic) :
    ConcreteExternalEventRel after concrete semantic := {
  name := related.name
  paramKindsSize := related.paramKindsSize
  argsSize := related.argsSize
  arguments := by
    intro index kind lane value kindFound laneFound valueFound
    exact transport
      (related.arguments index kind lane value kindFound laneFound valueFound)
  result := transport related.result }

theorem ConcreteTraceRel.witnessTransport
    {before after : RefinementWitness}
    {concrete : Array ConcreteExternalEvent} {semantic : Array ExternalEvent}
    (transport : WitnessTransport before after)
    (related : ConcreteTraceRel before concrete semantic) :
    ConcreteTraceRel after concrete semantic := {
  size := related.size
  events := by
    intro index concreteEvent semanticEvent concreteFound semanticFound
    exact ConcreteExternalEventRel.witnessTransport transport
      (related.events index concreteEvent semanticEvent concreteFound semanticFound) }

/-- Any exact object-like ABI lane accepted by the compiler widens to the
runtime's representation-polymorphic `tobject` input without changing bits. -/
theorem PhysicalValueRel.toTObject
    {witness : RefinementWitness} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : PhysicalValueRel witness kind physical semantic)
    (refines : kind.refines .tobject = true) :
    PhysicalValueRel witness .tobject physical semantic := by
  cases related with
  | word32 valueRelated =>
      cases valueRelated with
      | object heapRelated => exact .word32 (.tobject (.heap heapRelated))
      | tagged taggedRelated => exact .word32 (.tobject (.tagged taggedRelated))
      | tobject objectRelated => exact .word32 (.tobject objectRelated)
      | erased => simp [AbiKind.refines] at refines
      | reuseNone => simp [AbiKind.refines] at refines
      | reuseSome heapRelated => simp [AbiKind.refines] at refines
      | uint8 encoded => simp [AbiKind.refines] at refines
      | uint16 encoded => simp [AbiKind.refines] at refines
      | uint32 encoded => simp [AbiKind.refines] at refines
  | word64 valueRelated =>
      cases valueRelated <;> simp [AbiKind.refines] at refines
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

/--
Transport a physical/semantic value relation along the compiler's complete
ABI refinement order.

Apart from equality, the only admitted refinement is an exact `.object` or
`.tagged` representation widened to `.tobject`; `toTObject` implements those
two cases without changing the physical lane.
-/
theorem PhysicalValueRel.ofRefines
    {witness : RefinementWitness} {actual expected : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : PhysicalValueRel witness actual physical semantic)
    (refines : actual.refines expected = true) :
    PhysicalValueRel witness expected physical semantic := by
  cases actual <;> cases expected <;>
    simp [AbiKind.refines] at refines <;>
    try { exact related } <;>
    exact related.toTObject (by simp [AbiKind.refines])

/-- A concrete local write binds its semantic result while preserving every
old binding under monotone proof-witness growth. -/
theorem EnvLocalsRelated.bind
    {before after : RefinementWitness}
    {bindings : List (Lean.FVarId × AbiKind)} {source : Env}
    {target updated : Wasm.Locals} {result : Lean.FVarId}
    {resultIndex : Nat} {kind : AbiKind} {semantic : Value}
    {physical : Wasm.Value}
    (related : EnvLocalsRelated before bindings source target)
    (resultFound : findFVar? bindings result = some resultIndex)
    (kindAt : bindings[resultIndex]?.map Prod.snd = some kind)
    (localUpdate : FirTalos.Correctness.LocalUpdate target updated resultIndex
      physical)
    (extension : before.Extends after)
    (physicalRelated : PhysicalValueRel after kind physical semantic) :
    EnvLocalsRelated after bindings
      (Fir.LeanIR.Impure.bind source result semantic) updated := by
  intro fvar value sourceLookup
  by_cases sameName : (result.name == fvar.name) = true
  · have names : result.name = fvar.name := LawfulBEq.eq_of_beq sameName
    have sameFind := findFVar?_eq_of_name_eq bindings names
    have found : findFVar? bindings fvar = some resultIndex := by
      rw [← sameFind]
      exact resultFound
    have valueEq : value = semantic := by
      simpa [Fir.LeanIR.Impure.bind, lookup, sameName] using sourceLookup.symm
    subst value
    exact ⟨resultIndex, kind, physical, found, kindAt, localUpdate.1,
      physicalRelated⟩
  · have oldLookup : lookup source fvar = some value := by
      simpa [Fir.LeanIR.Impure.bind, lookup, sameName] using sourceLookup
    rcases related oldLookup with
      ⟨index, oldKind, oldPhysical, found, oldKindAt, targetLookup,
        oldRelated⟩
    have names : result.name ≠ fvar.name := by
      intro equal
      apply sameName
      rw [equal]
      exact beq_self_eq_true _
    have different := findFVar?_ne_of_name_ne bindings names resultFound found
    exact ⟨index, oldKind, oldPhysical, found, oldKindAt,
      (localUpdate.2 different.symm).trans targetLookup,
      oldRelated.witnessExtension extension⟩

/-- Bind one result while transporting every pre-existing local through a
possibly non-monotone representation-witness transition such as constructor
descriptor rebinding after a successful unique reset. -/
theorem EnvLocalsRelated.bindTransport
    {before after : RefinementWitness}
    {bindings : List (Lean.FVarId × AbiKind)} {source : Env}
    {target updated : Wasm.Locals} {result : Lean.FVarId}
    {resultIndex : Nat} {kind : AbiKind} {semantic : Value}
    {physical : Wasm.Value}
    (related : EnvLocalsRelated before bindings source target)
    (resultFound : findFVar? bindings result = some resultIndex)
    (kindAt : bindings[resultIndex]?.map Prod.snd = some kind)
    (localUpdate : FirTalos.Correctness.LocalUpdate target updated resultIndex
      physical)
    (transport : WitnessTransport before after)
    (physicalRelated : PhysicalValueRel after kind physical semantic) :
    EnvLocalsRelated after bindings
      (Fir.LeanIR.Impure.bind source result semantic) updated := by
  exact EnvLocalsRelated.bind
    (related.witnessTransport transport) resultFound kindAt localUpdate
      (.refl after) physicalRelated

/-- Unified natural-literal refinement assembled after both the natural and
promoted-tag proof modules are available. -/
theorem allocateNatural_liveHeapRel_extends
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (value : Nat) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (allocated : allocateNatural state value = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      LiveHeapRel result nextWitness (literal runtime (.nat value)).1 ∧
      ValueRel nextWitness .tobject (.word32 word)
        (literal runtime (.nat value)).2 := by
  by_cases small : value ≤ maxTaggedPayload
  · have encoded : encodeTagged state (UInt64.ofNat value) =
        .ok (result, word) := by
      unfold allocateNatural at allocated
      rw [if_pos small] at allocated
      exact allocated
    obtain ⟨nextWitness, extension, heapRelated, valueRelated⟩ :=
      encodeTagged_liveHeapRel_extends state result witness runtime
        (UInt64.ofNat value) word related encoded
    have literalEq : literal runtime (.nat value) =
        (runtime, .object (.tagged (UInt64.ofNat value))) := by
      simp [literal, small]
    rw [literalEq]
    exact ⟨nextWitness, extension, heapRelated, valueRelated⟩
  · have large : maxTaggedPayload < value := Nat.lt_of_not_ge small
    obtain ⟨_, _, _, objectAllocation, _, _⟩ :=
      allocateNatural_heap_decompose state result value word large allocated
    have freshAddress := related.frontier.allocateObject_address objectAllocation
    have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
      cases found : witness.locations.lookup? runtime.nextLocation with
      | none => rfl
      | some oldAddress =>
          exfalso
          obtain ⟨cell, semanticFound, _⟩ :=
            related.concreteToSemantic runtime.nextLocation oldAddress found
          have beforeNext :=
            related.locationsBeforeNext runtime.nextLocation cell semanticFound
          exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
    have descriptorFresh : ∀ old descriptor,
        witness.descriptors.lookup? old = some descriptor →
        word.value ≠ old.value := by
      intro old descriptor found equal
      have owned := related.descriptorsOwned old descriptor found
      simp [headerBytes] at owned
      omega
    have extension := witness.bindNatural_extends runtime.nextLocation word value
      locationFresh descriptorFresh
    have refined := allocateNatural_heap_liveHeapRel state result witness runtime
      value word related large allocated
    rw [semanticLiteral_natural_heap_eq runtime value large]
    exact ⟨witness.bindNatural runtime.nextLocation word value, extension,
      refined.1, refined.2⟩

theorem ConcreteRuntimeRel.allocateNatural
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState} {value : Nat}
    {word : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (allocated : allocateNatural concrete.heap value = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness
        (literal runtime (.nat value)).1 ∧
      ValueRel nextWitness .tobject (.word32 word)
        (literal runtime (.nat value)).2 := by
  obtain ⟨nextWitness, extension, heapRelated, valueRelated⟩ :=
    allocateNatural_liveHeapRel_extends concrete.heap result witness runtime
      value word related.heap allocated
  have auxiliary :
      (literal runtime (.nat value)).1.globals = runtime.globals ∧
      (literal runtime (.nat value)).1.world = runtime.world ∧
      (literal runtime (.nat value)).1.trace = runtime.trace := by
    by_cases small : value ≤ maxTaggedPayload
    · simp [literal, small]
    · have large : maxTaggedPayload < value := Nat.lt_of_not_ge small
      rw [semanticLiteral_natural_heap_eq runtime value large]
      simp [semanticNaturalResult]
  refine ⟨nextWitness, extension, ?_, valueRelated⟩
  exact {
    heap := heapRelated
    globals := by
      rw [auxiliary.1]
      exact related.globals.witnessExtension extension
    world := by
      rw [auxiliary.2.1]
      exact related.world
    trace := by
      rw [auxiliary.2.2]
      exact related.trace.witnessExtension extension }

/--
Canonical concrete response for a pure external returning a `Nat`.

The result word is deliberately representation-polymorphic: it may be an
immediate tagged value, a promoted-tag address, or a limb-object address.
-/
def concreteNaturalExternalResponse
    (before : ConcreteRuntimeState) (result : MemoryState) (word : Word32) :
    ConcreteExternalResponse := {
  value := .word32 word
  heap := result
  world := before.world }

/--
Matching semantic response for a pure external returning a `Nat`.

Reusing `literal` makes this boundary agree definitionally with source
evaluation for all three natural representations.
-/
def semanticNaturalExternalResponse
    (before : RuntimeState) (value : Nat) : ExternalResponse :=
  let allocated := literal before (.nat value)
  {
    value := allocated.2
    heap := allocated.1.heap
    nextLocation := allocated.1.nextLocation
    world := before.world }

/--
A successful representation-polymorphic natural allocation establishes the
complete concrete/source response relation. The witness is existential
because an immediate keeps it unchanged, a promoted tag extends its
descriptor map, and a limb object binds a fresh semantic location.
-/
theorem ConcreteRuntimeRel.naturalExternalResponse
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (semanticRequest : ExternalRequest)
    (result : MemoryState) (word : Word32) (value : Nat)
    (allocated :
      Fir.Wasm.Concrete.allocateNatural concreteBefore.heap value =
        .ok (result, word)) :
    ∃ afterWitness,
      ConcreteExternalResponseRel beforeWitness afterWitness
        semanticRequest semanticBefore .tobject
        (concreteNaturalExternalResponse concreteBefore result word)
        (semanticNaturalExternalResponse semanticBefore value) := by
  obtain ⟨afterWitness, extension, nextRuntimeRelated, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateNatural runtimeRelated allocated
  refine ⟨afterWitness, {
    witnessExtension := extension
    heap := ?_
    value := ?_
    world := runtimeRelated.world }⟩
  · apply nextRuntimeRelated.heap.auxiliary
    · simp [semanticNaturalExternalResponse, semanticExternalRuntimeAfter]
    · simp [semanticNaturalExternalResponse, semanticExternalRuntimeAfter]
  · simpa [concreteNaturalExternalResponse,
      semanticNaturalExternalResponse] using valueRelated

/--
End-to-end pure-external refinement for a representation-polymorphic `Nat`
result. The caller supplies only the two call equations and the successful
canonical allocation; the representation-specific witness is constructed
internally.
-/
theorem ConcreteExternalImpl.invoke_pure_natural_result_refines
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {result : MemoryState} {word : Word32} {value : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (requestRelated : ConcreteExternalRequestRel beforeWitness
      concreteRequest semanticRequest)
    (resultKind : concreteRequest.resultKind = .tobject)
    (allocated :
      Fir.Wasm.Concrete.allocateNatural concreteBefore.heap value =
        .ok (result, word))
    (concreteCalled :
      concreteImplementation.call concreteRequest concreteBefore =
        .ok (concreteNaturalExternalResponse concreteBefore result word))
    (semanticCalled :
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticNaturalExternalResponse semanticBefore value)) :
    ∃ afterWitness,
      concreteImplementation.invoke concreteRequest concreteBefore =
          .ok (concreteBefore.applyExternalResponse concreteRequest
              (concreteNaturalExternalResponse concreteBefore result word),
            (concreteNaturalExternalResponse concreteBefore result word).value) ∧
        semanticImplementation.call semanticRequest semanticBefore =
          .ok (semanticNaturalExternalResponse semanticBefore value) ∧
        ConcretePureExternalPost concreteBefore beforeWitness afterWitness
          semanticBefore concreteRequest semanticRequest
          (concreteNaturalExternalResponse concreteBefore result word)
          (semanticNaturalExternalResponse semanticBefore value) := by
  obtain ⟨afterWitness, responseRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.naturalExternalResponse runtimeRelated
      semanticRequest result word value allocated
  have responseRelated' : ConcreteExternalResponseRel beforeWitness afterWitness
      semanticRequest semanticBefore concreteRequest.resultKind
      (concreteNaturalExternalResponse concreteBefore result word)
      (semanticNaturalExternalResponse semanticBefore value) := by
    rw [resultKind]
    exact responseRelated
  exact ⟨afterWitness,
    concreteImplementation.invoke_pure_result_refines runtimeRelated
      requestRelated concreteCalled semanticCalled responseRelated' (by rfl)⟩

/--
Operation-family correctness law for pure concrete handlers that return a
`Nat`. It constrains the implementation for every related request and every
successful source response, independently of which natural representation is
chosen.
-/
def ConcreteExternalImpl.NaturalResultRefines
    (concreteImplementation : ConcreteExternalImpl)
    (semanticImplementation : ExternalImpl) : Prop :=
  ∀ {concreteBefore : ConcreteRuntimeState}
      {beforeWitness : RefinementWitness}
      {semanticBefore : RuntimeState}
      {concreteRequest : ConcreteExternalRequest}
      {semanticRequest : ExternalRequest}
      {value : Nat} {result : MemoryState} {word : Word32},
    ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore →
      ConcreteExternalRequestRel beforeWitness concreteRequest semanticRequest →
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticNaturalExternalResponse semanticBefore value) →
      Fir.Wasm.Concrete.allocateNatural concreteBefore.heap value =
        .ok (result, word) →
      concreteImplementation.call concreteRequest concreteBefore =
        .ok (concreteNaturalExternalResponse concreteBefore result word)

/--
An exact path budget turns the natural-result implementation law into the
complete pure-external postcondition and residual budget. Allocation success,
the physical word, and the representation-specific witness are all
constructed internally.
-/
theorem ConcreteRuntimeRel.invoke_pure_natural_result_refines_of_budget
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {value : Nat} {remainingBytes : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (implementationRelated :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        concreteImplementation semanticImplementation)
    (requestRelated :
      ConcreteExternalRequestRel beforeWitness concreteRequest semanticRequest)
    (resultKind : concreteRequest.resultKind = .tobject)
    (semanticCalled :
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticNaturalExternalResponse semanticBefore value))
    (budget :
      concreteBefore.heap.AddressSpaceBudget remainingBytes)
    (fits : naturalAllocationBytes value ≤ remainingBytes) :
    ∃ result word afterWitness,
      Fir.Wasm.Concrete.allocateNatural concreteBefore.heap value =
        .ok (result, word) ∧
        concreteImplementation.invoke concreteRequest concreteBefore =
          .ok (concreteBefore.applyExternalResponse concreteRequest
              (concreteNaturalExternalResponse concreteBefore result word),
            (concreteNaturalExternalResponse concreteBefore result word).value) ∧
        semanticImplementation.call semanticRequest semanticBefore =
          .ok (semanticNaturalExternalResponse semanticBefore value) ∧
        ConcretePureExternalPost concreteBefore beforeWitness afterWitness
          semanticBefore concreteRequest semanticRequest
          (concreteNaturalExternalResponse concreteBefore result word)
          (semanticNaturalExternalResponse semanticBefore value) ∧
        result.AddressSpaceBudget
          (remainingBytes - naturalAllocationBytes value) := by
  obtain ⟨result, word, allocated, remainingBudget⟩ :=
    runtimeRelated.heap.frontier.allocateNatural_eq_ok_of_budget value budget fits
  have concreteCalled :=
    implementationRelated runtimeRelated requestRelated semanticCalled allocated
  obtain ⟨afterWitness, concreteInvoke, semanticInvoke, post⟩ :=
    FirTalos.Concrete.ConcreteExternalImpl.invoke_pure_natural_result_refines
      runtimeRelated requestRelated resultKind allocated concreteCalled
      semanticCalled
  exact ⟨result, word, afterWitness, allocated, concreteInvoke, semanticInvoke,
    post, remainingBudget⟩

/--
Canonical concrete response for a pure nonallocating scalar external.
`BoxedScalar` is reused here only as the ABI-indexed scalar vocabulary; no
heap box is allocated.
-/
def concreteScalarExternalResponse
    (before : ConcreteRuntimeState) (scalar : BoxedScalar) :
    ConcreteExternalResponse := {
  value := scalar.lane
  heap := before.heap
  world := before.world }

/-- Matching source response for a pure nonallocating scalar external. -/
def semanticScalarExternalResponse
    (before : RuntimeState) (scalar : BoxedScalar) : ExternalResponse := {
  value := scalar.semanticValue
  heap := before.heap
  nextLocation := before.nextLocation
  world := before.world }

/--
Nonallocating scalar responses preserve the witness and heap exactly while
returning the lane selected by the scalar's ABI kind.
-/
theorem ConcreteRuntimeRel.scalarExternalResponse
    {concreteBefore : ConcreteRuntimeState}
    {witness : RefinementWitness}
    {semanticBefore : RuntimeState}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore witness semanticBefore)
    (semanticRequest : ExternalRequest) (scalar : BoxedScalar) :
    ConcreteExternalResponseRel witness witness semanticRequest semanticBefore
      scalar.kind.abiKind
      (concreteScalarExternalResponse concreteBefore scalar)
      (semanticScalarExternalResponse semanticBefore scalar) := by
  exact {
    witnessExtension := .refl witness
    heap := runtimeRelated.heap.auxiliary
      (by simp [semanticExternalRuntimeAfter, semanticScalarExternalResponse])
      (by simp [semanticExternalRuntimeAfter, semanticScalarExternalResponse])
    value := scalar.valueRel witness
    world := runtimeRelated.world }

/--
End-to-end pure-external refinement for a nonallocating scalar result. No
allocation result or post-witness is needed: both are definitionally the
incoming state.
-/
theorem ConcreteExternalImpl.invoke_pure_scalar_result_refines
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {witness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {scalar : BoxedScalar}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore witness semanticBefore)
    (requestRelated : ConcreteExternalRequestRel witness
      concreteRequest semanticRequest)
    (resultKind : concreteRequest.resultKind = scalar.kind.abiKind)
    (concreteCalled :
      concreteImplementation.call concreteRequest concreteBefore =
        .ok (concreteScalarExternalResponse concreteBefore scalar))
    (semanticCalled :
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticScalarExternalResponse semanticBefore scalar)) :
    concreteImplementation.invoke concreteRequest concreteBefore =
        .ok (concreteBefore.applyExternalResponse concreteRequest
            (concreteScalarExternalResponse concreteBefore scalar),
          (concreteScalarExternalResponse concreteBefore scalar).value) ∧
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticScalarExternalResponse semanticBefore scalar) ∧
      ConcretePureExternalPost concreteBefore witness witness semanticBefore
        concreteRequest semanticRequest
        (concreteScalarExternalResponse concreteBefore scalar)
        (semanticScalarExternalResponse semanticBefore scalar) := by
  have responseRelated : ConcreteExternalResponseRel witness witness
      semanticRequest semanticBefore concreteRequest.resultKind
      (concreteScalarExternalResponse concreteBefore scalar)
      (semanticScalarExternalResponse semanticBefore scalar) := by
    rw [resultKind]
    exact FirTalos.Concrete.ConcreteRuntimeRel.scalarExternalResponse
      runtimeRelated semanticRequest scalar
  exact concreteImplementation.invoke_pure_result_refines runtimeRelated
    requestRelated concreteCalled semanticCalled responseRelated (by rfl)

/--
Reusable implementation law for pure scalar-result handlers. It applies to
all integer scalar widths and `USize`; a source-facing name family chooses the
operations admitted by compiler correctness.
-/
def ConcreteExternalImpl.ScalarResultRefines
    (concreteImplementation : ConcreteExternalImpl)
    (semanticImplementation : ExternalImpl) : Prop :=
  ∀ {concreteBefore : ConcreteRuntimeState}
      {witness : RefinementWitness}
      {semanticBefore : RuntimeState}
      {concreteRequest : ConcreteExternalRequest}
      {semanticRequest : ExternalRequest}
      {scalar : BoxedScalar},
    ConcreteRuntimeRel concreteBefore witness semanticBefore →
      ConcreteExternalRequestRel witness concreteRequest semanticRequest →
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticScalarExternalResponse semanticBefore scalar) →
      concreteImplementation.call concreteRequest concreteBefore =
        .ok (concreteScalarExternalResponse concreteBefore scalar)

/-- Fresh string allocation grows the proof witness exactly once and exposes
the compiler's precise `.object` result lane. -/
theorem allocateString_liveHeapRel_extends
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (value : String) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (allocated : allocateString state value = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      LiveHeapRel result nextWitness (literal runtime (.str value)).1 ∧
      ValueRel nextWitness .object (.word32 word)
        (literal runtime (.str value)).2 := by
  obtain ⟨_, _, _, objectAllocation, _, _⟩ :=
    allocateString_decompose state result value word allocated
  have freshAddress := related.frontier.allocateObject_address objectAllocation
  have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
    cases found : witness.locations.lookup? runtime.nextLocation with
    | none => rfl
    | some oldAddress =>
        exfalso
        obtain ⟨cell, semanticFound, _⟩ :=
          related.concreteToSemantic runtime.nextLocation oldAddress found
        have beforeNext :=
          related.locationsBeforeNext runtime.nextLocation cell semanticFound
        exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
  have descriptorFresh : ∀ old descriptor,
      witness.descriptors.lookup? old = some descriptor →
      word.value ≠ old.value := by
    intro old descriptor found equal
    have owned := related.descriptorsOwned old descriptor found
    simp [headerBytes] at owned
    omega
  have extension := witness.bindString_extends runtime.nextLocation word value
    locationFresh descriptorFresh
  have refined := allocateString_liveHeapRel state result witness runtime value
    word related allocated
  rw [semanticLiteral_string_eq runtime value]
  exact ⟨witness.bindString runtime.nextLocation word value, extension,
    refined.1, refined.2⟩

theorem ConcreteRuntimeRel.allocateString
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState} {value : String}
    {word : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (allocated : allocateString concrete.heap value = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness
        (literal runtime (.str value)).1 ∧
      ValueRel nextWitness .object (.word32 word)
        (literal runtime (.str value)).2 := by
  obtain ⟨nextWitness, extension, heapRelated, valueRelated⟩ :=
    allocateString_liveHeapRel_extends concrete.heap result witness runtime
      value word related.heap allocated
  have auxiliary :
      (literal runtime (.str value)).1.globals = runtime.globals ∧
      (literal runtime (.str value)).1.world = runtime.world ∧
      (literal runtime (.str value)).1.trace = runtime.trace := by
    rw [semanticLiteral_string_eq runtime value]
    simp [semanticStringResult]
  refine ⟨nextWitness, extension, ?_, valueRelated⟩
  exact {
    heap := heapRelated
    globals := by
      rw [auxiliary.1]
      exact related.globals.witnessExtension extension
    world := by
      rw [auxiliary.2.1]
      exact related.world
    trace := by
      rw [auxiliary.2.2]
      exact related.trace.witnessExtension extension }

/-- Empty constructor allocation preserves semantic runtime state while its
concrete tagged result may extend the heap with a promoted-tag object. -/
theorem ConcreteRuntimeRel.allocateConstructorEmpty
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState}
    {info : Lean.Compiler.LCNF.CtorInfo} {fields : Array Word32}
    {semanticFields : Array Value} {word : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (allocated : allocateConstructor concrete.heap info fields =
      .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness runtime ∧
      ValueRel nextWitness .tagged (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  obtain ⟨nextWitness, extension, heapRelated, valueRelated, semanticStep⟩ :=
    allocateConstructor_empty_liveHeapRel_extends concrete.heap result witness
      runtime info fields semanticFields word related.heap arity semanticArity
      empty tagFits allocated
  refine ⟨nextWitness, extension, ?_, valueRelated, semanticStep⟩
  exact {
    heap := heapRelated
    globals := related.globals.witnessExtension extension
    world := related.world
    trace := related.trace.witnessExtension extension }

/-- Capacity-preserving form of empty constructor allocation. The tagged
result may allocate a promoted representation, but every previously mapped
semantic allocation keeps its retained extent. -/
theorem ConcreteRuntimeRel.allocateConstructorEmpty_with_capacity
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState}
    {info : Lean.Compiler.LCNF.CtorInfo} {fields : Array Word32}
    {semanticFields : Array Value} {word : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (allocated : allocateConstructor concrete.heap info fields =
      .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness runtime ∧
      ValueRel nextWitness .tagged (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) ∧
      MappedHeaderCapacityTransport concrete.heap result witness := by
  obtain ⟨nextWitness, extension, heapRelated, valueRelated, semanticStep,
      capacityTransport⟩ :=
    allocateConstructor_empty_liveHeapRel_extends_with_capacity concrete.heap
      result witness runtime info fields semanticFields word related.heap arity
      semanticArity empty tagFits allocated
  refine ⟨nextWitness, extension, ?_, valueRelated, semanticStep,
    capacityTransport⟩
  exact {
    heap := heapRelated
    globals := related.globals.witnessExtension extension
    world := related.world
    trace := related.trace.witnessExtension extension }

/-- Nonempty constructor allocation grows both heaps by one related object and
preserves every auxiliary runtime component under the extended witness. -/
theorem ConcreteRuntimeRel.allocateConstructorNonempty
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {fields : Array Word32} {semanticFields : Array Value} {address : Word32}
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
    (allocated : allocateConstructor concrete.heap info fields =
      .ok (result, address)) :
    let nextWitness :=
      witness.bindConstructor runtime.nextLocation address info fieldKinds
    witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨extension, heapRelated, valueRelated⟩ :=
    allocateConstructor_nonempty_liveHeapRel_extends concrete.heap result witness
      runtime info fieldKinds fields semanticFields address related.heap arity
      semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty tagFits
      objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  refine ⟨extension, ?_, valueRelated⟩
  exact {
    heap := heapRelated
    globals := by
      simpa [semanticConstructorResult] using
        related.globals.witnessExtension extension
    world := by simpa [semanticConstructorResult] using related.world
    trace := by
      simpa [semanticConstructorResult] using
        related.trace.witnessExtension extension }

/-- Concrete integer boxing grows the proof witness exactly when its tagged or
heap representation allocates. The result packages the canonical semantic
step used by later source/compiler composition. -/
theorem ConcreteRuntimeRel.boxScalar
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState}
    {scalar : BoxedScalar} {word : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (boxed : boxScalar concrete.heap scalar = .ok (result, word)) :
    ∃ nextRuntime sourceValue nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness
        nextRuntime ∧
      ValueRel nextWitness .tobject (.word32 word) sourceValue ∧
      box runtime scalar.kind.semanticType scalar.semanticValue =
        .ok (nextRuntime, sourceValue) := by
  by_cases tagged : scalar.payload.toNat ≤ maxTaggedPayload
  · have encoded : encodeTagged concrete.heap scalar.payload =
        .ok (result, word) := by
      rw [← boxScalar_of_tagged concrete.heap scalar tagged]
      exact boxed
    obtain ⟨nextWitness, extension, heapRelated, valueRelated⟩ :=
      encodeTagged_liveHeapRel_extends concrete.heap result witness runtime
        scalar.payload word related.heap encoded
    refine ⟨runtime, .object (.tagged scalar.payload), nextWitness,
      extension, ?_, valueRelated, semanticBox_tagged_eq runtime scalar tagged⟩
    exact {
      heap := heapRelated
      globals := related.globals.witnessExtension extension
      world := related.world
      trace := related.trace.witnessExtension extension }
  · have large : maxTaggedPayload < scalar.payload.toNat :=
      Nat.lt_of_not_ge tagged
    have allocated : allocateBoxedScalar concrete.heap scalar =
        .ok (result, word) := by
      rw [← boxScalar_of_heap concrete.heap scalar large]
      exact boxed
    obtain ⟨_, objectAllocation, _, _⟩ :=
      allocateBoxedScalar_decompose concrete.heap result scalar word allocated
    have freshAddress :=
      related.heap.frontier.allocateObject_address objectAllocation
    have locationFresh :
        witness.locations.lookup? runtime.nextLocation = none := by
      cases found : witness.locations.lookup? runtime.nextLocation with
      | none => rfl
      | some oldAddress =>
          exfalso
          obtain ⟨cell, semanticFound, _⟩ :=
            related.heap.concreteToSemantic runtime.nextLocation oldAddress found
          have beforeNext := related.heap.locationsBeforeNext
            runtime.nextLocation cell semanticFound
          exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
    have descriptorFresh : ∀ old descriptor,
        witness.descriptors.lookup? old = some descriptor →
        word.value ≠ old.value := by
      intro old descriptor found equal
      have owned := related.heap.descriptorsOwned old descriptor found
      simp [headerBytes] at owned
      omega
    let nextWitness :=
      witness.bindBoxed runtime.nextLocation word scalar.kind
    have extension : witness.Extends nextWitness :=
      witness.bindBoxed_extends runtime.nextLocation word scalar.kind
        locationFresh descriptorFresh
    obtain ⟨semanticStep, heapRelated, valueRelated⟩ :=
      boxScalar_heap_liveHeapRel concrete.heap result witness runtime scalar word
        related.heap large boxed
    refine ⟨semanticBoxResult runtime scalar,
      .object (.heap runtime.nextLocation), nextWitness, extension, ?_,
      valueRelated, semanticStep⟩
    exact {
      heap := heapRelated
      globals := by
        simpa [semanticBoxResult] using
          related.globals.witnessExtension extension
      world := by simpa [semanticBoxResult] using related.world
      trace := by
        simpa [semanticBoxResult] using
          related.trace.witnessExtension extension }

/-- Failures at the concrete Talos host boundary retain either the exact W6
runtime trap or a Wasm ABI-shape error detected before the operation runs. -/
inductive HostFailure where
  | runtime (failure : ConcreteTrap)
  | arityMismatch (expected actual : Nat)
  | laneMismatch (index : Nat) (expected : Fir.Wasm.ValueType)
  | resultLaneMismatch (expected actual : Fir.Wasm.ValueType)
  | unsupportedScalarKind (kind : AbiKind)
  deriving Inhabited, BEq, Repr

/-- Safe executable default for modules whose caller has not installed a
concrete foreign-function implementation. The source-shaped failure is
retained by `ConcreteError.toTrap` at the Talos boundary. -/
def rejectExternalImpl : ConcreteExternalImpl where
  call request _ :=
    .error (.source (.externalFailure request.name
      "no concrete external implementation installed"))

/-- Host-owned concrete linear memory and its latest structured failure. The
semantic runtime is deliberately absent: it occurs only in the refinement
relation and cannot be consulted by executable concrete host functions. -/
structure Host where
  runtime : ConcreteRuntimeState := {}
  closureDispatch : ClosureDispatchTable := #[]
  closureDescriptors : ClosureDescriptorTable := #[]
  closureApplication? : Option ClosureApplication := none
  externals : ConcreteExternalImpl := rejectExternalImpl
  failure? : Option HostFailure := none
  deriving Inhabited

def clearFailure (store : Wasm.Store Host) : Wasm.Store Host :=
  { store with host := { store.host with failure? := none } }

def trap (store : Wasm.Store Host) (failure : HostFailure) :
    Wasm.HostResult Host :=
  .Trap { store with host := { store.host with failure? := some failure } }
    s!"FIR concrete host failure: {repr failure}"

/-- Executable concrete implementation of the W2 `getTag` import. It accepts
one wasm32 object word, runs the checked W6 decoder over host-owned linear
memory, and returns the low i32 tag lane used by generated case tests. -/
def getTagStep (store : Wasm.Store Host) (args : List Wasm.Value) :
    Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match readTag store.host.runtime.heap (Word32.ofUInt32 bits) with
      | .ok tag => .Return [.i32 (UInt32.ofNat tag.toNat)] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def getTagFn : Wasm.HostFn Host := {
  params := [.i32]
  results := [.i32]
  invoke := getTagStep }

/-- Exact proof-facing contract for the executable concrete tag host. -/
def getTagContract : Wasm.HostContract Host :=
  fun initial args result => result = getTagStep initial args

theorem getTagFn_satisfies_contract (initial args) :
    getTagContract initial args (getTagFn.invoke initial args) := by
  rfl

/-- Executable concrete sharing observation. The returned UInt8 is represented
directly in an i32 lane, matching Lean 4.32's final-impure ABI. -/
def isSharedStep (store : Wasm.Store Host) (args : List Wasm.Value) :
    Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match readIsShared store.host.runtime.heap (Word32.ofUInt32 bits) with
      | .ok shared => .Return [.i32 (UInt32.ofNat shared.toNat)] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def isSharedFn : Wasm.HostFn Host := {
  params := [.i32]
  results := [.i32]
  invoke := isSharedStep }

def isSharedContract : Wasm.HostContract Host :=
  fun initial args result => result = isSharedStep initial args

theorem isSharedFn_satisfies_contract (initial args) :
    isSharedContract initial args (isSharedFn.invoke initial args) := by
  rfl

/-- Executable concrete implementation of an object-field projection import.
The field index and result ABI are frozen in the import; the runtime reads one
full semantic slot and returns its exact wasm32 word. -/
def objectProjStep (index : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match readObjectField store.host.runtime.heap (Word32.ofUInt32 bits) index with
      | .ok word => .Return [.i32 (UInt32.ofNat word.value)] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def objectProjFn (index : Nat) : Wasm.HostFn Host := {
  params := [.i32]
  results := [.i32]
  invoke := objectProjStep index }

def objectProjContract (index : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = objectProjStep index initial args

theorem objectProjFn_satisfies_contract (index initial args) :
    objectProjContract index initial args
      ((objectProjFn index).invoke initial args) := by
  rfl

def usizeProjStep (index : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match readUSizeSlot store.host.runtime.heap (Word32.ofUInt32 bits) index with
      | .ok value => .Return [.i64 value] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def usizeProjFn (index : Nat) : Wasm.HostFn Host := {
  params := [.i32]
  results := [.i64]
  invoke := usizeProjStep index }

def usizeProjContract (index : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = usizeProjStep index initial args

theorem usizeProjFn_satisfies_contract (index initial args) :
    usizeProjContract index initial args
      ((usizeProjFn index).invoke initial args) := by
  rfl

def scalarProjStep (width offset : Nat) (kind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      let object := Word32.ofUInt32 bits
      match kind with
      | .uint8 =>
          match readScalarUInt8Field store.host.runtime.heap object width offset with
          | .ok value =>
              .Return [.i32 (UInt32.ofNat (Word32.ofUInt8 value).value)] store
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint16 =>
          match readScalarUInt16Field store.host.runtime.heap object width offset with
          | .ok value =>
              .Return [.i32 (UInt32.ofNat (Word32.ofUInt16 value).value)] store
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint32 =>
          match readScalarUInt32Field store.host.runtime.heap object width offset with
          | .ok value =>
              .Return [.i32 (UInt32.ofNat (Word32.ofUInt32 value).value)] store
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint64 =>
          match readScalarUInt64Field store.host.runtime.heap object width offset with
          | .ok value => .Return [.i64 value] store
          | .error failure => trap store (.runtime failure.toTrap)
      | other => trap store (.unsupportedScalarKind other)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def scalarProjFn (width offset : Nat) (kind : AbiKind) : Wasm.HostFn Host := {
  params := [.i32]
  results := [FirTalos.abiKind kind]
  invoke := scalarProjStep width offset kind }

def scalarProjContract (width offset : Nat) (kind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = scalarProjStep width offset kind initial args

theorem scalarProjFn_satisfies_contract (width offset kind initial args) :
    scalarProjContract width offset kind initial args
      ((scalarProjFn width offset kind).invoke initial args) := by
  rfl

def replaceHeap (store : Wasm.Store Host) (heap : MemoryState) :
    Wasm.Store Host :=
  let store := clearFailure store
  { store with host := { store.host with
      runtime := { store.host.runtime with heap } } }

def naturalLiteralStep (value : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [] =>
      match allocateNatural store.host.runtime.heap value with
      | .ok (heap, word) =>
          .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | args => trap store (.arityMismatch 0 args.length)

def naturalLiteralFn (value : Nat) : Wasm.HostFn Host := {
  params := []
  results := [.i32]
  invoke := naturalLiteralStep value }

def naturalLiteralContract (value : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = naturalLiteralStep value initial args

theorem naturalLiteralFn_satisfies_contract (value initial args) :
    naturalLiteralContract value initial args
      ((naturalLiteralFn value).invoke initial args) := by
  rfl

/-- Executable concrete string-literal import. The host allocates the frozen
UTF-8 object layout and returns its exact wasm32 address. -/
def stringLiteralStep (value : String) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [] =>
      match allocateString store.host.runtime.heap value with
      | .ok (heap, word) =>
          .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | args => trap store (.arityMismatch 0 args.length)

def stringLiteralFn (value : String) : Wasm.HostFn Host := {
  params := []
  results := [.i32]
  invoke := stringLiteralStep value }

def stringLiteralContract (value : String) : Wasm.HostContract Host :=
  fun initial args result => result = stringLiteralStep value initial args

theorem stringLiteralFn_satisfies_contract (value initial args) :
    stringLiteralContract value initial args
      ((stringLiteralFn value).invoke initial args) := by
  rfl

/-- Decode the i32-only physical fields accepted by constructor allocation.
The index is carried solely to produce a precise structured lane failure. -/
def decodeConstructorWords : Nat → List Wasm.Value → Except HostFailure (List Word32)
  | _, [] => .ok []
  | index, .i32 bits :: rest => do
      let tail ← decodeConstructorWords (index + 1) rest
      return Word32.ofUInt32 bits :: tail
  | index, _ :: _ => .error (.laneMismatch index .i32)

/-- Executable concrete implementation of the constructor-allocation import.
It decodes raw wasm32 fields, allocates in linear memory, and never consults
semantic values or a handle table. -/
def allocCtorStep (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (_resultKind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  if args.length = fieldKinds.size then
    match decodeConstructorWords 0 args with
    | .ok fields =>
        match allocateConstructor store.host.runtime.heap info fields.toArray with
        | .ok (heap, word) =>
            .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
        | .error failure => trap store (.runtime failure.toTrap)
    | .error failure => trap store failure
  else
    trap store (.arityMismatch fieldKinds.size args.length)

def allocCtorFn (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) : Wasm.HostFn Host := {
  params := fieldKinds.toList.map FirTalos.abiKind
  results := [FirTalos.abiKind resultKind]
  invoke := allocCtorStep info fieldKinds resultKind }

def allocCtorContract (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = allocCtorStep info fieldKinds resultKind initial args

theorem allocCtorFn_satisfies_contract (info fieldKinds resultKind initial args) :
    allocCtorContract info fieldKinds resultKind initial args
      ((allocCtorFn info fieldKinds resultKind).invoke initial args) := by
  rfl

def replaceRuntime (store : Wasm.Store Host) (runtime : ConcreteRuntimeState) :
    Wasm.Store Host :=
  let store := clearFailure store
  { store with host := { store.host with runtime } }

/-- Decode one physical Talos value into W6's ABI lane selected by its static
kind. This is a bit-preserving conversion, not a semantic value decoder. -/
def decodePhysicalLane (kind : AbiKind) (physical : Wasm.Value) :
    Except HostFailure LaneValue :=
  match kind.valueType, physical with
  | .i32, .i32 bits => .ok (.word32 (Word32.ofUInt32 bits))
  | .i64, .i64 word => .ok (.word64 word)
  | .f32, .f32 bits => .ok (.float32Bits bits)
  | .f64, .f64 bits => .ok (.float64Bits bits)
  | expected, _ => .error (.laneMismatch 0 expected)

/-- Executable concrete lazy-cache update. The physical value is returned
unchanged for the following generated `global.set`. -/
def cacheSetStep (declaration : Lean.Name) (kind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [physical] =>
      match decodePhysicalLane kind physical with
      | .ok lane =>
          match store.host.runtime.writeGlobal declaration kind lane
              store.host.closureDescriptors with
          | .ok runtime => .Return [physical] (replaceRuntime store runtime)
          | .error failure => trap store (.runtime failure.toTrap)
      | .error failure => trap store failure
  | args => trap store (.arityMismatch 1 args.length)

def cacheSetFn (declaration : Lean.Name) (kind : AbiKind) : Wasm.HostFn Host := {
  params := [FirTalos.abiKind kind]
  results := [FirTalos.abiKind kind]
  invoke := cacheSetStep declaration kind }

def cacheSetContract (declaration : Lean.Name) (kind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result => result = cacheSetStep declaration kind initial args

theorem cacheSetFn_satisfies_contract (declaration kind initial args) :
    cacheSetContract declaration kind initial args
      ((cacheSetFn declaration kind).invoke initial args) := by
  rfl

/-- Executable concrete reference-count increment. Tagged and promoted-tag
words retain their checked no-op behavior inside `incrementReference`; an
ordinary heap object updates only its checked common header. -/
def incrementStep (amount : Nat) (check : Bool) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match incrementReference store.host.runtime.heap (Word32.ofUInt32 bits)
          amount check with
      | .ok heap => .Return [] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def incrementFn (amount : Nat) (check : Bool) : Wasm.HostFn Host := {
  params := [.i32]
  results := []
  invoke := incrementStep amount check }

def incrementContract (amount : Nat) (check : Bool) :
    Wasm.HostContract Host :=
  fun initial args result => result = incrementStep amount check initial args

theorem incrementFn_satisfies_contract (amount check initial args) :
    incrementContract amount check initial args
      ((incrementFn amount check).invoke initial args) := by
  rfl

/-- Executable concrete recursive reference-count decrement. The optional
object-field count is part of the import identity but concrete ownership is
decoded from the checked header and closure descriptor table. -/
def decrementStep (amount : Nat) (check : Bool)
    (_objectFields? : Option Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match decrementReference store.host.runtime.heap (Word32.ofUInt32 bits)
          amount check store.host.closureDescriptors with
      | .ok heap => .Return [] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def decrementFn (amount : Nat) (check : Bool)
    (objectFields? : Option Nat) : Wasm.HostFn Host := {
  params := [.i32]
  results := []
  invoke := decrementStep amount check objectFields? }

def decrementContract (amount : Nat) (check : Bool)
    (objectFields? : Option Nat) : Wasm.HostContract Host :=
  fun initial args result =>
    result = decrementStep amount check objectFields? initial args

theorem decrementFn_satisfies_contract
    (amount check objectFields? initial args) :
    decrementContract amount check objectFields? initial args
      ((decrementFn amount check objectFields?).invoke initial args) := by
  rfl

/-- Executable concrete explicit deletion. Physical word zero is the shared
failed-reset erased sentinel and is an operation-specific no-op; ordinary heap
addresses receive the canonical freed header without releasing children. -/
def deleteStep (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match deleteObject store.host.runtime.heap (Word32.ofUInt32 bits) with
      | .ok heap => .Return [] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def deleteFn : Wasm.HostFn Host := {
  params := [.i32]
  results := []
  invoke := deleteStep }

def deleteContract : Wasm.HostContract Host :=
  fun initial args result => result = deleteStep initial args

theorem deleteFn_satisfies_contract (initial args) :
    deleteContract initial args (deleteFn.invoke initial args) := by
  rfl

/-- Executable concrete reset. Tagged values and fallback heap objects return
the empty token; a unique ordinary constructor returns its address after
clearing the requested ownership prefix. -/
def resetStep (count : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match resetObject store.host.runtime.heap count (Word32.ofUInt32 bits)
          store.host.closureDescriptors with
      | .ok (heap, token) =>
          .Return [.i32 (UInt32.ofNat token.value)] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def resetFn (count : Nat) : Wasm.HostFn Host := {
  params := [.i32]
  results := [.i32]
  invoke := resetStep count }

def resetContract (count : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = resetStep count initial args

theorem resetFn_satisfies_contract (count initial args) :
    resetContract count initial args ((resetFn count).invoke initial args) := by
  rfl

/-- Decode the token followed by the wasm32 constructor fields consumed by
concrete reuse. Field diagnostics retain their position in the complete host
argument list. -/
def decodeReuseWords : List Wasm.Value →
    Except HostFailure (Word32 × List Word32)
  | [] => .error (.arityMismatch 1 0)
  | .i32 bits :: rest => do
      let fields ← decodeConstructorWords 1 rest
      return (Word32.ofUInt32 bits, fields)
  | _ :: _ => .error (.laneMismatch 0 .i32)

/-- Executable concrete constructor reuse. Word zero selects fresh
allocation; a nonzero token consumes the reset protocol and rebuilds the
retained allocation in place. -/
def reuseStep (info : Lean.Compiler.LCNF.CtorInfo) (updateHeader : Bool)
    (fieldKinds : Array AbiKind) (_resultKind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  if args.length = fieldKinds.size + 1 then
    match decodeReuseWords args with
    | .ok (token, fields) =>
        match reuseObject store.host.runtime.heap token info updateHeader
            fields.toArray with
        | .ok (heap, word) =>
            .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
        | .error failure => trap store (.runtime failure.toTrap)
    | .error failure => trap store failure
  else
    trap store (.arityMismatch (fieldKinds.size + 1) args.length)

def reuseFn (info : Lean.Compiler.LCNF.CtorInfo) (updateHeader : Bool)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) : Wasm.HostFn Host := {
  params := .i32 :: fieldKinds.toList.map FirTalos.abiKind
  results := [FirTalos.abiKind resultKind]
  invoke := reuseStep info updateHeader fieldKinds resultKind }

def reuseContract (info : Lean.Compiler.LCNF.CtorInfo) (updateHeader : Bool)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = reuseStep info updateHeader fieldKinds resultKind initial args

theorem reuseFn_satisfies_contract
    (info updateHeader fieldKinds resultKind initial args) :
    reuseContract info updateHeader fieldKinds resultKind initial args
      ((reuseFn info updateHeader fieldKinds resultKind).invoke initial args) := by
  rfl

/-- Executable concrete constructor-tag mutation. The checked runtime rewrites
only the constructor header and rejects nonconstructor or out-of-range tags
through the structured concrete failure channel. -/
def setTagStep (tag : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match writeTag store.host.runtime.heap (Word32.ofUInt32 bits) tag with
      | .ok heap => .Return [] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def setTagFn (tag : Nat) : Wasm.HostFn Host := {
  params := [.i32]
  results := []
  invoke := setTagStep tag }

def setTagContract (tag : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = setTagStep tag initial args

theorem setTagFn_satisfies_contract (tag initial args) :
    setTagContract tag initial args ((setTagFn tag).invoke initial args) := by
  rfl

/-- Executable concrete object-slot mutation. Supported object fields are
wasm32 lanes; the checked writer validates the constructor, slot bounds, and
canonical padding before replacing only the low word of that semantic slot. -/
def objectSetStep (index : Nat) (_fieldKind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 objectBits, .i32 fieldBits] =>
      match writeObjectField store.host.runtime.heap
          (Word32.ofUInt32 objectBits) index (Word32.ofUInt32 fieldBits) with
      | .ok heap => .Return [] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | [.i32 _, _] => trap store (.laneMismatch 1 .i32)
  | [_, _] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 2 args.length)

def objectSetFn (index : Nat) (fieldKind : AbiKind) : Wasm.HostFn Host := {
  params := [.i32, FirTalos.abiKind fieldKind]
  results := []
  invoke := objectSetStep index fieldKind }

def objectSetContract (index : Nat) (fieldKind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = objectSetStep index fieldKind initial args

theorem objectSetFn_satisfies_contract (index fieldKind initial args) :
    objectSetContract index fieldKind initial args
      ((objectSetFn index fieldKind).invoke initial args) := by
  rfl

/-- Executable concrete `USize`-slot mutation. The Lean64 field remains an
exact i64 lane while the constructor address remains a wasm32 word. -/
def usizeSetStep (index : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 objectBits, .i64 field] =>
      match writeUSizeSlot store.host.runtime.heap
          (Word32.ofUInt32 objectBits) index field with
      | .ok heap => .Return [] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | [.i32 _, _] => trap store (.laneMismatch 1 .i64)
  | [_, _] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 2 args.length)

def usizeSetFn (index : Nat) : Wasm.HostFn Host := {
  params := [.i32, .i64]
  results := []
  invoke := usizeSetStep index }

def usizeSetContract (index : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = usizeSetStep index initial args

theorem usizeSetFn_satisfies_contract (index initial args) :
    usizeSetContract index initial args ((usizeSetFn index).invoke initial args) := by
  rfl

/-- Executable concrete packed-integer mutation dispatcher. The ABI kind fixes
both the physical field lane and the checked writer width; float kinds remain
an explicit structured fragment failure. -/
def scalarSetStep (slotIndex byteOffset : Nat) (kind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 objectBits, physical] =>
      let object := Word32.ofUInt32 objectBits
      match kind, physical with
      | .uint8, .i32 fieldBits =>
          match writeScalarUInt8Field store.host.runtime.heap object slotIndex
              byteOffset (UInt8.ofNat (Word32.ofUInt32 fieldBits).value) with
          | .ok heap => .Return [] (replaceHeap store heap)
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint16, .i32 fieldBits =>
          match writeScalarUInt16Field store.host.runtime.heap object slotIndex
              byteOffset (UInt16.ofNat (Word32.ofUInt32 fieldBits).value) with
          | .ok heap => .Return [] (replaceHeap store heap)
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint32, .i32 fieldBits =>
          match writeScalarUInt32Field store.host.runtime.heap object slotIndex
              byteOffset (UInt32.ofNat (Word32.ofUInt32 fieldBits).value) with
          | .ok heap => .Return [] (replaceHeap store heap)
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint64, .i64 field =>
          match writeScalarUInt64Field store.host.runtime.heap object slotIndex
              byteOffset field with
          | .ok heap => .Return [] (replaceHeap store heap)
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint8, _ | .uint16, _ | .uint32, _ =>
          trap store (.laneMismatch 1 .i32)
      | .uint64, _ => trap store (.laneMismatch 1 .i64)
      | other, _ => trap store (.unsupportedScalarKind other)
  | [_, _] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 2 args.length)

def scalarSetFn (slotIndex byteOffset : Nat) (kind : AbiKind) :
    Wasm.HostFn Host := {
  params := [.i32, FirTalos.abiKind kind]
  results := []
  invoke := scalarSetStep slotIndex byteOffset kind }

def scalarSetContract (slotIndex byteOffset : Nat) (kind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = scalarSetStep slotIndex byteOffset kind initial args

theorem scalarSetFn_satisfies_contract (slotIndex byteOffset kind initial args) :
    scalarSetContract slotIndex byteOffset kind initial args
      ((scalarSetFn slotIndex byteOffset kind).invoke initial args) := by
  rfl

def decodePhysicalLanes : Nat → List AbiKind → List Wasm.Value →
    Except HostFailure (List LaneValue)
  | _, [], [] => .ok []
  | index, kind :: kinds, physical :: physicals => do
      let lane ← match decodePhysicalLane kind physical with
        | .ok lane => .ok lane
        | .error (.laneMismatch _ expected) =>
            .error (.laneMismatch index expected)
        | .error failure => .error failure
      let tail ← decodePhysicalLanes (index + 1) kinds physicals
      return lane :: tail
  | _, kinds, physicals => .error (.arityMismatch kinds.length physicals.length)

def partialApplyStep (function : Lean.Name) (arity fixed : Nat)
    (fieldKinds : Array AbiKind) (_resultKind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  if args.length = fixed then
    match decodePhysicalLanes 0 fieldKinds.toList args with
    | .ok captures =>
        match allocateClosure store.host.runtime.heap store.host.closureDispatch
            store.host.closureDescriptors function arity fieldKinds
            captures.toArray with
        | .ok (heap, word) =>
            .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
        | .error failure => trap store (.runtime failure.toTrap)
    | .error failure => trap store failure
  else
    trap store (.arityMismatch fixed args.length)

def partialApplyFn (function : Lean.Name) (arity fixed : Nat)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) : Wasm.HostFn Host := {
  params := fieldKinds.toList.map FirTalos.abiKind
  results := [FirTalos.abiKind resultKind]
  invoke := partialApplyStep function arity fixed fieldKinds resultKind }

def partialApplyContract (function : Lean.Name) (arity fixed : Nat)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result => result =
    partialApplyStep function arity fixed fieldKinds resultKind initial args

theorem partialApplyFn_satisfies_contract
    (function arity fixed fieldKinds resultKind initial args) :
    partialApplyContract function arity fixed fieldKinds resultKind initial args
      ((partialApplyFn function arity fixed fieldKinds resultKind).invoke
        initial args) := by
  rfl

/-- Bit-preserving conversion from W6's concrete lane vocabulary to Talos's
operand-stack values. -/
def physicalOfLane : LaneValue → Wasm.Value
  | .word32 word => .i32 (UInt32.ofNat word.value)
  | .word64 word => .i64 word
  | .float32Bits bits => .f32 bits
  | .float64Bits bits => .f64 bits

/-- Construct the exact physical request carried by one resolved external
import. Source types come from the validated import and concrete lanes come
from the signature-directed Talos decoder. -/
def concreteExternalRequest (operation : ExternalOperation)
    (resultKind : AbiKind) (args : Array LaneValue) :
    ConcreteExternalRequest := {
  name := operation.name
  paramTypes := operation.paramTypes
  resultType := operation.resultType
  paramKinds := operation.signature.params
  resultKind
  args }

/-- Execute one resolved foreign import directly over concrete runtime state.
The host implementation may replace the heap and world token; the shared
external runtime layer appends the exact concrete event. -/
def externalStep (operation : ExternalOperation) (resultKind : AbiKind)
    (store : Wasm.Store Host) (physicalArgs : List Wasm.Value) :
    Wasm.HostResult Host :=
  match decodePhysicalLanes 0 operation.signature.params.toList physicalArgs with
  | .error failure => trap (clearFailure store) failure
  | .ok args =>
      let request := concreteExternalRequest operation resultKind args.toArray
      match store.host.externals.invoke request store.host.runtime with
      | .error failure => trap (clearFailure store) (.runtime failure.toTrap)
      | .ok (runtime, result) =>
          if result.valueType == resultKind.valueType then
            .Return [physicalOfLane result] (replaceRuntime store runtime)
          else
            trap (clearFailure store)
              (.resultLaneMismatch resultKind.valueType result.valueType)

def externalFn (operation : ExternalOperation) (resultKind : AbiKind) :
    Wasm.HostFn Host := {
  params := operation.signature.params.toList.map FirTalos.abiKind
  results := [FirTalos.abiKind resultKind]
  invoke := externalStep operation resultKind }

def externalContract (operation : ExternalOperation) (resultKind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = externalStep operation resultKind initial args

theorem externalFn_satisfies_contract
    (operation resultKind initial args) :
    externalContract operation resultKind initial args
      ((externalFn operation resultKind).invoke initial args) := by
  rfl

theorem physicalOfLane_related
    {witness : RefinementWitness} {kind : AbiKind} {lane : LaneValue}
    {semantic : Value} (related : ValueRel witness kind lane semantic) :
    PhysicalValueRel witness kind (physicalOfLane lane) semantic := by
  cases related with
  | object related => exact .word32 (.object related)
  | tagged related => exact .word32 (.tagged related)
  | tobject related => exact .word32 (.tobject related)
  | erased => exact .word32 .erased
  | reuseNone => exact .word32 .reuseNone
  | reuseSome related => exact .word32 (.reuseSome related)
  | uint8 encoded => exact .word32 (.uint8 encoded)
  | uint16 encoded => exact .word32 (.uint16 encoded)
  | uint32 encoded => exact .word32 (.uint32 encoded)
  | uint64 => exact .word64 .uint64
  | usize => exact .word64 .usize

theorem valueRel_physical_type_beq
    {witness : RefinementWitness} {kind : AbiKind} {lane : LaneValue}
    {semantic : Value} (related : ValueRel witness kind lane semantic) :
    (lane.valueType == kind.valueType) = true := by
  cases related <;> rfl

/-- A successful concrete external host call preserves the full W6 runtime
relation and returns the physical lane related to the source response. The
foreign-call equations stay explicit so resolver/code-WP composition cannot
substitute an unconstrained response. -/
theorem externalStep_of_refines
    (operation : ExternalOperation) (resultKind : AbiKind)
    (initial : Wasm.Store Host) (physicalArgs : List Wasm.Value)
    (concreteArgs : List LaneValue) (semanticArgs : Array Value)
    (witness : RefinementWitness) (semanticRuntime : RuntimeState)
    (semanticImplementation : ExternalImpl)
    (afterWitness : RefinementWitness)
    (concreteResponse : ConcreteExternalResponse)
    (semanticResponse : ExternalResponse)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness
      semanticRuntime)
    (requestRelated : ConcreteExternalRequestRel witness
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      (operation.request semanticArgs))
    (concreteCalled : initial.host.externals.call
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      initial.host.runtime = .ok concreteResponse)
    (semanticCalled : semanticImplementation.call
      (operation.request semanticArgs) semanticRuntime = .ok semanticResponse)
    (responseRelated : ConcreteExternalResponseRel witness afterWitness
      (operation.request semanticArgs) semanticRuntime resultKind
      concreteResponse semanticResponse) :
    externalStep operation resultKind initial physicalArgs =
        .Return [physicalOfLane concreteResponse.value]
          (replaceRuntime initial
            (initial.host.runtime.applyExternalResponse
              (concreteExternalRequest operation resultKind concreteArgs.toArray)
              concreteResponse)) ∧
      semanticImplementation.call (operation.request semanticArgs)
          semanticRuntime = .ok semanticResponse ∧
      ConcreteRuntimeRel
        (initial.host.runtime.applyExternalResponse
          (concreteExternalRequest operation resultKind concreteArgs.toArray)
          concreteResponse)
        afterWitness
        (semanticExternalRuntimeAfter (operation.request semanticArgs)
          semanticRuntime semanticResponse) ∧
      PhysicalValueRel afterWitness resultKind
        (physicalOfLane concreteResponse.value) semanticResponse.value := by
  have refined := ConcreteExternalImpl.invoke_refines runtimeRelated
    requestRelated concreteCalled semanticCalled responseRelated
  have resultLaneMatches :
      (concreteResponse.value.valueType == resultKind.valueType) = true := by
    exact valueRel_physical_type_beq refined.2.2.2
  refine ⟨?_, refined.2.1, refined.2.2.1,
    physicalOfLane_related refined.2.2.2⟩
  simp [externalStep, decoded, refined.1, resultLaneMatches]

/--
Constructive Talos host step for a pure external that returns one heap-backed
arbitrary-precision integer.

The source result fixes the exact allocation cost. One path budget constructs
the concrete allocation and handler invocation, then the ordinary generated
external host step returns the related wasm32 object lane and the exact
residual budget.
-/
theorem integerExternalStep_of_budget
    (operation : ExternalOperation) (resultKind : AbiKind)
    (initial : Wasm.Store Host) (physicalArgs : List Wasm.Value)
    (concreteArgs : List LaneValue) (semanticArgs : Array Value)
    (witness : RefinementWitness) (semanticRuntime : RuntimeState)
    (semanticImplementation : ExternalImpl)
    (value : Int) (remainingBytes : Nat)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness
      semanticRuntime)
    (requestRelated : ConcreteExternalRequestRel witness
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      (operation.request semanticArgs))
    (implementationRelated :
      initial.host.externals.IntegerResultRefines semanticImplementation)
    (resultKindEq : resultKind = .tobject)
    (semanticCalled :
      semanticImplementation.call (operation.request semanticArgs)
          semanticRuntime =
        .ok (semanticIntegerExternalResponse semanticRuntime value))
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits : integerAllocationBytes value ≤ remainingBytes) :
    ∃ result address,
      allocateInteger initial.host.runtime.heap value = .ok (result, address) ∧
        externalStep operation resultKind initial physicalArgs =
          .Return
            [physicalOfLane
              (concreteIntegerExternalResponse initial.host.runtime
                result address).value]
            (replaceRuntime initial
              (initial.host.runtime.applyExternalResponse
                (concreteExternalRequest operation resultKind
                  concreteArgs.toArray)
                (concreteIntegerExternalResponse initial.host.runtime
                  result address))) ∧
        semanticImplementation.call (operation.request semanticArgs)
            semanticRuntime =
          .ok (semanticIntegerExternalResponse semanticRuntime value) ∧
        witness.Extends
          (witness.bindInteger semanticRuntime.nextLocation address value) ∧
        ConcreteRuntimeRel
          (initial.host.runtime.applyExternalResponse
            (concreteExternalRequest operation resultKind concreteArgs.toArray)
            (concreteIntegerExternalResponse initial.host.runtime result address))
          (witness.bindInteger semanticRuntime.nextLocation address value)
          (semanticExternalRuntimeAfter (operation.request semanticArgs)
            semanticRuntime
            (semanticIntegerExternalResponse semanticRuntime value)) ∧
        PhysicalValueRel
          (witness.bindInteger semanticRuntime.nextLocation address value)
          resultKind
          (physicalOfLane
            (concreteIntegerExternalResponse initial.host.runtime
              result address).value)
          (semanticIntegerExternalResponse semanticRuntime value).value ∧
        result.AddressSpaceBudget
          (remainingBytes - integerAllocationBytes value) := by
  obtain ⟨result, address, allocated, concreteInvoke, semanticInvoke, post,
      remainingBudget⟩ :=
    runtimeRelated.invoke_pure_integer_result_refines_of_budget
      implementationRelated requestRelated
        (by simp [concreteExternalRequest, resultKindEq])
      semanticCalled budget fits
  have laneMatches :
      ((concreteIntegerExternalResponse initial.host.runtime result address).value.valueType ==
        resultKind.valueType) = true := by
    exact valueRel_physical_type_beq post.value
  have operationStep :
      externalStep operation resultKind initial physicalArgs =
        .Return
          [physicalOfLane
            (concreteIntegerExternalResponse initial.host.runtime
              result address).value]
          (replaceRuntime initial
            (initial.host.runtime.applyExternalResponse
              (concreteExternalRequest operation resultKind concreteArgs.toArray)
              (concreteIntegerExternalResponse initial.host.runtime
                result address))) := by
    simp [externalStep, decoded, concreteInvoke, laneMatches]
  exact ⟨result, address, allocated, operationStep, semanticInvoke,
    post.witnessExtension, post.runtime, physicalOfLane_related post.value,
    remainingBudget⟩

/--
Constructive Talos host step for a pure external returning one `Nat`.

The exact source result selects the allocation cost and concrete
representation. The theorem constructs the allocation word and refinement
witness, then exposes the ordinary external step, related continuation, and
exact residual budget without requiring a representation certificate.
-/
theorem naturalExternalStep_of_budget
    (operation : ExternalOperation) (resultKind : AbiKind)
    (initial : Wasm.Store Host) (physicalArgs : List Wasm.Value)
    (concreteArgs : List LaneValue) (semanticArgs : Array Value)
    (witness : RefinementWitness) (semanticRuntime : RuntimeState)
    (semanticImplementation : ExternalImpl)
    (value : Nat) (remainingBytes : Nat)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness
      semanticRuntime)
    (requestRelated : ConcreteExternalRequestRel witness
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      (operation.request semanticArgs))
    (implementationRelated :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals semanticImplementation)
    (resultKindEq : resultKind = .tobject)
    (semanticCalled :
      semanticImplementation.call (operation.request semanticArgs)
          semanticRuntime =
        .ok (semanticNaturalExternalResponse semanticRuntime value))
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits : naturalAllocationBytes value ≤ remainingBytes) :
    ∃ result word afterWitness,
      allocateNatural initial.host.runtime.heap value = .ok (result, word) ∧
        externalStep operation resultKind initial physicalArgs =
          .Return
            [physicalOfLane
              (concreteNaturalExternalResponse initial.host.runtime
                result word).value]
            (replaceRuntime initial
              (initial.host.runtime.applyExternalResponse
                (concreteExternalRequest operation resultKind
                  concreteArgs.toArray)
                (concreteNaturalExternalResponse initial.host.runtime
                  result word))) ∧
        semanticImplementation.call (operation.request semanticArgs)
            semanticRuntime =
          .ok (semanticNaturalExternalResponse semanticRuntime value) ∧
        witness.Extends afterWitness ∧
        ConcreteRuntimeRel
          (initial.host.runtime.applyExternalResponse
            (concreteExternalRequest operation resultKind concreteArgs.toArray)
            (concreteNaturalExternalResponse initial.host.runtime result word))
          afterWitness
          (semanticExternalRuntimeAfter (operation.request semanticArgs)
            semanticRuntime
            (semanticNaturalExternalResponse semanticRuntime value)) ∧
        PhysicalValueRel afterWitness resultKind
          (physicalOfLane
            (concreteNaturalExternalResponse initial.host.runtime
              result word).value)
          (semanticNaturalExternalResponse semanticRuntime value).value ∧
        result.AddressSpaceBudget
          (remainingBytes - naturalAllocationBytes value) := by
  obtain ⟨result, word, afterWitness, allocated, concreteInvoke,
      semanticInvoke, post, remainingBudget⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.invoke_pure_natural_result_refines_of_budget
      runtimeRelated
      implementationRelated requestRelated
      (by simp [concreteExternalRequest, resultKindEq])
      semanticCalled budget fits
  have laneMatches :
      ((concreteNaturalExternalResponse initial.host.runtime result word).value.valueType ==
        resultKind.valueType) = true := by
    exact valueRel_physical_type_beq post.value
  have operationStep :
      externalStep operation resultKind initial physicalArgs =
        .Return
          [physicalOfLane
            (concreteNaturalExternalResponse initial.host.runtime
              result word).value]
          (replaceRuntime initial
            (initial.host.runtime.applyExternalResponse
              (concreteExternalRequest operation resultKind concreteArgs.toArray)
              (concreteNaturalExternalResponse initial.host.runtime
                result word))) := by
    simp [externalStep, decoded, concreteInvoke, laneMatches]
  exact ⟨result, word, afterWitness, allocated, operationStep, semanticInvoke,
    post.witnessExtension, post.runtime, physicalOfLane_related post.value,
    remainingBudget⟩

/--
Constructive Talos host step for a pure nonallocating scalar external.
The source scalar fixes its ABI kind and exact lane; the heap, witness, and
available address-space budget remain unchanged.
-/
theorem scalarExternalStep
    (operation : ExternalOperation) (resultKind : AbiKind)
    (initial : Wasm.Store Host) (physicalArgs : List Wasm.Value)
    (concreteArgs : List LaneValue) (semanticArgs : Array Value)
    (witness : RefinementWitness) (semanticRuntime : RuntimeState)
    (semanticImplementation : ExternalImpl) (scalar : BoxedScalar)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness
      semanticRuntime)
    (requestRelated : ConcreteExternalRequestRel witness
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      (operation.request semanticArgs))
    (implementationRelated :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals semanticImplementation)
    (resultKindEq : resultKind = scalar.kind.abiKind)
    (semanticCalled :
      semanticImplementation.call (operation.request semanticArgs)
          semanticRuntime =
        .ok (semanticScalarExternalResponse semanticRuntime scalar)) :
    externalStep operation resultKind initial physicalArgs =
        .Return
          [physicalOfLane
            (concreteScalarExternalResponse initial.host.runtime scalar).value]
          (replaceRuntime initial
            (initial.host.runtime.applyExternalResponse
              (concreteExternalRequest operation resultKind concreteArgs.toArray)
              (concreteScalarExternalResponse initial.host.runtime scalar))) ∧
      semanticImplementation.call (operation.request semanticArgs)
          semanticRuntime =
        .ok (semanticScalarExternalResponse semanticRuntime scalar) ∧
      ConcreteRuntimeRel
        (initial.host.runtime.applyExternalResponse
          (concreteExternalRequest operation resultKind concreteArgs.toArray)
          (concreteScalarExternalResponse initial.host.runtime scalar))
        witness
        (semanticExternalRuntimeAfter (operation.request semanticArgs)
          semanticRuntime
          (semanticScalarExternalResponse semanticRuntime scalar)) ∧
      PhysicalValueRel witness resultKind
        (physicalOfLane
          (concreteScalarExternalResponse initial.host.runtime scalar).value)
        (semanticScalarExternalResponse semanticRuntime scalar).value := by
  have concreteCalled :=
    implementationRelated runtimeRelated requestRelated semanticCalled
  obtain ⟨concreteInvoke, semanticInvoke, post⟩ :=
    FirTalos.Concrete.ConcreteExternalImpl.invoke_pure_scalar_result_refines
      runtimeRelated requestRelated
      (by simpa [concreteExternalRequest] using resultKindEq)
      concreteCalled semanticCalled
  have laneMatches :
      ((concreteScalarExternalResponse initial.host.runtime scalar).value.valueType ==
        resultKind.valueType) = true := by
    exact valueRel_physical_type_beq post.value
  have operationStep :
      externalStep operation resultKind initial physicalArgs =
        .Return
          [physicalOfLane
            (concreteScalarExternalResponse initial.host.runtime scalar).value]
          (replaceRuntime initial
            (initial.host.runtime.applyExternalResponse
              (concreteExternalRequest operation resultKind concreteArgs.toArray)
              (concreteScalarExternalResponse initial.host.runtime scalar))) := by
    simp [externalStep, decoded, concreteInvoke, laneMatches]
  exact ⟨operationStep, semanticInvoke, post.runtime,
    physicalOfLane_related post.value⟩

/-- Decode one supported integer/USize operand into the concrete boxing
vocabulary while retaining ABI-shape failures at the Talos boundary. -/
def decodeBoxedScalar (kind : BoxedScalarKind) (physical : Wasm.Value) :
    Except HostFailure BoxedScalar :=
  match kind, physical with
  | .uint8, .i32 bits => .ok (.uint8 (UInt8.ofNat bits.toNat))
  | .uint16, .i32 bits => .ok (.uint16 (UInt16.ofNat bits.toNat))
  | .uint32, .i32 bits => .ok (.uint32 bits)
  | .uint64, .i64 value => .ok (.uint64 value)
  | .usize, .i64 value => .ok (.usize value)
  | kind, _ => .error (.laneMismatch 0 kind.abiKind.valueType)

@[simp] theorem decodeBoxedScalar_physicalOfLane (scalar : BoxedScalar) :
    decodeBoxedScalar scalar.kind (physicalOfLane scalar.lane) = .ok scalar := by
  cases scalar <;>
    simp [decodeBoxedScalar, physicalOfLane, BoxedScalar.kind,
      BoxedScalar.lane]

/-- Executable concrete integer boxing. The scalar kind and object-like result
kind are frozen in the import identity; the host owns all allocated memory. -/
def boxStep (kind : BoxedScalarKind) (_resultKind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [physical] =>
      match decodeBoxedScalar kind physical with
      | .ok scalar =>
          match boxScalar store.host.runtime.heap scalar with
          | .ok (heap, word) =>
              .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
          | .error failure => trap store (.runtime failure.toTrap)
      | .error failure => trap store failure
  | args => trap store (.arityMismatch 1 args.length)

def boxFn (kind : BoxedScalarKind) (resultKind : AbiKind) :
    Wasm.HostFn Host := {
  params := [FirTalos.abiKind kind.abiKind]
  results := [FirTalos.abiKind resultKind]
  invoke := boxStep kind resultKind }

def boxContract (kind : BoxedScalarKind) (resultKind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result => result = boxStep kind resultKind initial args

theorem boxFn_satisfies_contract (kind resultKind initial args) :
    boxContract kind resultKind initial args
      ((boxFn kind resultKind).invoke initial args) := by
  rfl

/-- A successful concrete box host step returns the exact object word together
with the grown runtime witness and canonical FIR allocation step. -/
theorem boxStep_of_refines
    {initial : Wasm.Store Host}
    {runtime nextHeap : RuntimeState} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {heap : MemoryState} {word : Word32}
    {sourceValue : Value} {nextWitness : RefinementWitness}
    (kindEq : scalar.kind = kind)
    (boxed : boxScalar initial.host.runtime.heap scalar = .ok (heap, word))
    (semanticStep : box runtime kind.semanticType scalar.semanticValue =
      .ok (nextHeap, sourceValue))
    (nextRelated : ConcreteRuntimeRel
      { initial.host.runtime with heap := heap } nextWitness nextHeap)
    (valueRelated : ValueRel nextWitness .tobject (.word32 word) sourceValue) :
    boxStep kind .tobject initial [physicalOfLane scalar.lane] =
        .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime
        nextWitness nextHeap ∧
      ValueRel nextWitness .tobject (.word32 word) sourceValue := by
  subst kind
  refine ⟨?_, ?_, valueRelated⟩
  · unfold boxStep
    simp only [decodeBoxedScalar_physicalOfLane]
    rw [show (clearFailure initial).host.runtime.heap =
        initial.host.runtime.heap by rfl, boxed]
    rfl
  simpa [replaceHeap, clearFailure] using nextRelated

/-- Representation-specific evidence needed by typed unboxing. Tagged values
are interpreted at the requested type; heap boxes are intentionally type-erased
by FIR, so their frozen descriptor must match the generated result kind. -/
inductive UnboxObjectRel (witness : RefinementWitness) (word : Word32)
    (kind : BoxedScalarKind) : Value → Prop where
  | heap (related : HeapReferenceRel witness word location)
      (descriptor : witness.descriptors.lookup? word = some (.boxed kind)) :
      UnboxObjectRel witness word kind (.object (.heap location))
  | tagged (related : TaggedReferenceRel witness word payload) :
      UnboxObjectRel witness word kind (.object (.tagged payload))

/-- Executable concrete typed unboxing. The requested kind fixes the import's
result lane; successful heap refinement separately proves that the stored box
descriptor agrees with it. -/
def unboxStep (kind : BoxedScalarKind) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match readBoxedScalar store.host.runtime.heap kind
          (Word32.ofUInt32 bits) with
      | .ok scalar => .Return [physicalOfLane scalar.lane] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def unboxFn (kind : BoxedScalarKind) : Wasm.HostFn Host := {
  params := [.i32]
  results := [FirTalos.abiKind kind.abiKind]
  invoke := unboxStep kind }

def unboxContract (kind : BoxedScalarKind) : Wasm.HostContract Host :=
  fun initial args result => result = unboxStep kind initial args

theorem unboxFn_satisfies_contract (kind initial args) :
    unboxContract kind initial args ((unboxFn kind).invoke initial args) := by
  rfl

/-- A successful checked unbox call returns the exact Talos lane related to
the FIR scalar, for either a typed live heap box or a tagged representation. -/
theorem unboxStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {kind : BoxedScalarKind}
    {sourceObject sourceValue : Value} {scalar : BoxedScalar}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : UnboxObjectRel witness word kind sourceObject)
    (unboxed : unbox runtime kind.semanticType sourceObject = .ok sourceValue)
    (concreteRead : readBoxedScalar initial.host.runtime.heap kind word =
      .ok scalar) :
    unboxStep kind initial [.i32 (UInt32.ofNat word.value)] =
        .Return [physicalOfLane scalar.lane] (clearFailure initial) ∧
      sourceValue = scalar.semanticValue ∧
      PhysicalValueRel witness kind.abiKind
        (physicalOfLane scalar.lane) sourceValue := by
  cases objectRelated with
  | heap heapRelated descriptor =>
      obtain ⟨actual, actualRead, valueEq, valueRelated⟩ :=
        runtimeRelated.heap.readBoxedScalar_heap_refines
          (by cases heapRelated with | mapped found => exact found)
          descriptor unboxed
      rw [concreteRead] at actualRead
      have scalarEq : scalar = actual := Except.ok.inj actualRead
      subst actual
      refine ⟨by simp [unboxStep, clearFailure,
          Word32.ofUInt32_ofNat_value, concreteRead], valueEq, ?_⟩
      exact physicalOfLane_related valueRelated
  | tagged taggedRelated =>
      obtain ⟨actualRead, semantic, valueRelated⟩ :=
        runtimeRelated.heap.readBoxedScalar_tagged_refines taggedRelated kind
      rw [concreteRead] at actualRead
      have scalarEq : scalar = BoxedScalar.ofPayload kind _ :=
        Except.ok.inj actualRead
      subst scalar
      have valueEq : sourceValue =
          (BoxedScalar.ofPayload kind _).semanticValue :=
        Except.ok.inj (unboxed.symm.trans semantic)
      subst sourceValue
      refine ⟨by simp [unboxStep, clearFailure,
          Word32.ofUInt32_ofNat_value, concreteRead], rfl, ?_⟩
      exact physicalOfLane_related valueRelated

/-- A stale mapped object faults at the common live-header gate before the
typed unbox decoder inspects boxed metadata or produces a result lane. -/
theorem unboxStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} (kind : BoxedScalarKind)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    unboxStep kind initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject word)))) ∧
      unbox runtime kind.semanticType (.object (.heap location)) =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject word)) (.deadObject location) := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.readBoxedScalar_deadObject heapRelated found
              dead kind
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [unboxStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- A related live non-box object rejected by FIR at typed unboxing produces
the exact source-classified concrete trap. Supported `BoxedScalarKind` values
exclude the unknown-type semantic fault, while tagged operands and live boxes
are eliminated by the source failure premise. -/
theorem unboxStep_expectedScalar_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {value : Value}
    (kind : BoxedScalarKind)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) value)
    (unboxFailed :
      unbox runtime kind.semanticType value = .error .expectedScalar) :
    unboxStep kind initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedScalar : ConcreteError).toTrap)) ∧
      unbox runtime kind.semanticType value = .error .expectedScalar ∧
      ConcreteErrorSourceRel witness
        (.source .expectedScalar) .expectedScalar := by
  have concrete :=
    runtimeRelated.heap.readBoxedScalar_expectedScalar_refines kind
      valueRelated unboxFailed
  refine ⟨?_, unboxFailed, .source .expectedScalar⟩
  simp [unboxStep, clearFailure, Word32.ofUInt32_ofNat_value, concrete,
    ConcreteError.toTrap]

/-- Concrete trampoline metadata test and application boundary. A mismatch is
a pure read. A match consumes one closure reference, transfers its captures,
and records the snapshot used by the selected candidate's projection prefix. -/
def closureMatchesStep (function : Lean.Name) (arity fixed : Nat)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match closureMatches store.host.runtime.heap store.host.closureDispatch
          store.host.closureDescriptors (Word32.ofUInt32 bits) function arity
          fixed with
      | .ok matched =>
          if matched == 0 then
            .Return [.i32 matched] store
          else
            match takeClosureApplication store.host.runtime.heap
                store.host.closureDispatch store.host.closureDescriptors
                (Word32.ofUInt32 bits) with
            | .ok (heap, application) =>
                let store := replaceHeap store heap
                .Return [.i32 matched] { store with host := {
                  store.host with closureApplication? := some application } }
            | .error failure => trap store (.runtime failure.toTrap)
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def closureMatchesFn (function : Lean.Name) (arity fixed : Nat) :
    Wasm.HostFn Host := {
  params := [.i32]
  results := [.i32]
  invoke := closureMatchesStep function arity fixed }

def closureMatchesContract (function : Lean.Name) (arity fixed : Nat) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = closureMatchesStep function arity fixed initial args

theorem closureMatchesFn_satisfies_contract
    (function arity fixed initial args) :
    closureMatchesContract function arity fixed initial args
      ((closureMatchesFn function arity fixed).invoke initial args) := by
  rfl

/-- Concrete typed capture projection used by the generated trampoline. The
lane comes from the successful match snapshot, so exclusive application may
project after the closure header has already been released. -/
def closureProjStep (function : Lean.Name) (arity fixed index : Nat)
    (resultKind : AbiKind) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match store.host.closureApplication? with
      | none =>
          trap store
            (.runtime
              ((Fir.Wasm.Concrete.ConcreteError.target
                .closureMetadataMismatch).toTrap))
      | some application =>
          match application.project (Word32.ofUInt32 bits) function arity fixed
              index resultKind with
          | .ok lane => .Return [physicalOfLane lane] store
          | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def closureProjFn (function : Lean.Name) (arity fixed index : Nat)
    (resultKind : AbiKind) : Wasm.HostFn Host := {
  params := [.i32]
  results := [FirTalos.abiKind resultKind]
  invoke := closureProjStep function arity fixed index resultKind }

def closureProjContract (function : Lean.Name) (arity fixed index : Nat)
    (resultKind : AbiKind) : Wasm.HostContract Host :=
  fun initial args result =>
    result = closureProjStep function arity fixed index resultKind initial args

theorem closureProjFn_satisfies_contract
    (function arity fixed index resultKind initial args) :
    closureProjContract function arity fixed index resultKind initial args
      ((closureProjFn function arity fixed index resultKind).invoke
        initial args) := by
  rfl

/-- A successful concrete sharing observation returns the exact direct UInt8
lane related to FIR's semantic result, for ordinary, immediate, and promoted
object representations. -/
theorem isSharedStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {shared : UInt8}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (evaluated : isShared runtime sourceObject =
      .ok (.scalar (.uint8 shared))) :
    isSharedStep initial [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [.i32 (UInt32.ofNat shared.toNat)] (clearFailure initial) ∧
      ValueRel witness .uint8 (.word32 (Word32.ofUInt8 shared))
        (.scalar (.uint8 shared)) := by
  obtain ⟨actual, read, semanticOperation, valueRelated⟩ :=
    runtimeRelated.heap.readIsShared_refines objectRelated ⟨_, evaluated⟩
  have scalarEq :
      (.scalar (.uint8 shared) : Value) = .scalar (.uint8 actual) :=
    Except.ok.inj (evaluated.symm.trans semanticOperation)
  have sharedEq : shared = actual := by
    injection scalarEq with scalarValueEq
    injection scalarValueEq
  subst actual
  exact ⟨by simp [isSharedStep, clearFailure,
      Word32.ofUInt32_ofNat_value, read], valueRelated⟩

/-- A stale mapped object preserves its exact source fault across all three
layers: FIR names the semantic location, W6 names its concrete wasm32 address,
and the Talos host traps with the corresponding address-indexed source
failure.  The final conjunct records the witness-indexed translation between
the two fault payloads. -/
theorem isSharedStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {location : Location}
    {cell : HeapCell}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    isSharedStep initial [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      isShared runtime (.object (.heap location)) =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.readIsShared_deadObject heapRelated found dead
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [isSharedStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/--
A successful semantic constructor decode at a related object address recovers
the constructor descriptor already carried by the whole-heap relation.

This removes descriptor existence from projection clients: the source
operation establishes that the object is a live constructor, while
`ConcreteRuntimeRel` supplies its concrete descriptor.  Object-field kind
agreement remains a separate compiler-typing obligation.
-/
theorem ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {location : Location} {cell : HeapCell} {object : ConstructorObject}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (decoded :
      getConstructor runtime sourceObject = .ok (location, cell, object)) :
    ∃ info fieldKinds,
      witness.descriptors.lookup? objectWord =
        some (.constructor info fieldKinds) := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getConstructor, getLiveCell] at decoded
      | heap heapRelated =>
          cases heapRelated with
          | mapped locationFound =>
              obtain ⟨semanticCell, semanticFound, cellRelated⟩ :=
                related.heap.concreteToSemantic _ _ locationFound
              cases liveEq : semanticCell.live with
              | false =>
                  simp only [getConstructor, getLiveCell, semanticFound,
                    liveEq, Bool.false_eq_true, if_false, Bind.bind,
                    Except.bind] at decoded
                  contradiction
              | true =>
                  have liveRelated := cellRelated.live_of_eq_true liveEq
                  cases liveRelated with
                  | constructor descriptor _ _ _ _ _ _ _ =>
                      exact ⟨_, _, descriptor⟩
                  | boxed _ objectEq _ _ _ _ =>
                      simp only [getConstructor, getLiveCell, semanticFound,
                        liveEq, ↓reduceIte, Bind.bind, Except.bind] at decoded
                      rw [objectEq] at decoded
                      contradiction
                  | natural _ objectEq _ _ _ _ _ _ _ _ _ =>
                      simp only [getConstructor, getLiveCell, semanticFound,
                        liveEq, ↓reduceIte, Bind.bind, Except.bind] at decoded
                      rw [objectEq] at decoded
                      contradiction
                  | integer _ objectEq _ _ _ _ =>
                      simp only [getConstructor, getLiveCell, semanticFound,
                        liveEq, ↓reduceIte, Bind.bind, Except.bind] at decoded
                      rw [objectEq] at decoded
                      contradiction
                  | string _ objectEq _ _ _ _ =>
                      simp only [getConstructor, getLiveCell, semanticFound,
                        liveEq, ↓reduceIte, Bind.bind, Except.bind] at decoded
                      rw [objectEq] at decoded
                      contradiction
                  | closure closureRelated =>
                      cases closureRelated with
                      | closure objectEq _ _ _ _ _ _ _ _ _ =>
                          simp only [getConstructor, getLiveCell, semanticFound,
                            liveEq, ↓reduceIte, Bind.bind, Except.bind] at decoded
                          rw [objectEq] at decoded
                          contradiction

/-- Successful object-field projection supplies the constructor decode needed
to recover its concrete descriptor. -/
theorem ConcreteRuntimeRel.constructorDescriptor_of_getObjectField
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject value : Value}
    {index : Nat}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getObjectField runtime sourceObject index = .ok value) :
    ∃ info fieldKinds,
      witness.descriptors.lookup? objectWord =
        some (.constructor info fieldKinds) := by
  unfold getObjectField at projected
  cases decoded : getConstructor runtime sourceObject with
  | error fault =>
      rw [decoded] at projected
      contradiction
  | ok result =>
      rcases result with ⟨location, cell, object⟩
      exact
        FirTalos.Concrete.ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
          related objectRelated decoded

/-- Successful absolute-slot `USize` projection likewise supplies the
constructor decode needed to recover its concrete descriptor. -/
theorem ConcreteRuntimeRel.constructorDescriptor_of_getUSizeSlot
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject value : Value}
    {slot : Nat}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getUSizeSlot runtime sourceObject slot = .ok value) :
    ∃ info fieldKinds,
      witness.descriptors.lookup? objectWord =
        some (.constructor info fieldKinds) := by
  unfold getUSizeSlot at projected
  cases decoded : getConstructor runtime sourceObject with
  | error fault =>
      rw [decoded] at projected
      contradiction
  | ok result =>
      rcases result with ⟨location, cell, object⟩
      exact
        FirTalos.Concrete.ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
          related objectRelated decoded

/-- Successful semantic projection identifies a mapped constructor and the
checked concrete read returns a field related at its static descriptor kind. -/
theorem ConcreteRuntimeRel.readObjectField_refines
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject value : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat} {kind : AbiKind}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (kindAt : fieldKinds[index]? = some kind)
    (projected : getObjectField runtime sourceObject index = .ok value) :
    ∃ word, readObjectField concrete.heap objectWord index = .ok word ∧
      ValueRel witness kind (.word32 word) value := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap mapped =>
          cases mapped with
          | mapped found =>
              exact related.heap.readObjectField_refines found descriptor kindAt
                projected
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getObjectField, getConstructor, Bind.bind, Except.bind] at projected

theorem ConcreteRuntimeRel.readUSizeField_refines
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat} {value : UInt64}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeField runtime sourceObject index = .ok (.usize value)) :
    readUSizeField concrete.heap objectWord index = .ok value ∧
      ValueRel witness .usize (.word64 value) (.usize value) := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap mapped =>
          cases mapped with
          | mapped found =>
              exact related.heap.readUSizeField_refines found descriptor projected
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getUSizeField, getConstructor, Bind.bind, Except.bind] at projected

theorem ConcreteRuntimeRel.readUSizeSlot_refines
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {slot : Nat} {value : UInt64}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeSlot runtime sourceObject slot = .ok (.usize value)) :
    readUSizeSlot concrete.heap objectWord slot = .ok value ∧
      ValueRel witness .usize (.word64 value) (.usize value) := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap mapped =>
          cases mapped with
          | mapped found =>
              exact related.heap.readUSizeSlot_refines found descriptor projected
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getUSizeSlot, getConstructor, Bind.bind, Except.bind] at projected

theorem ConcreteRuntimeRel.readObjectField_outOfBounds_refines
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getObjectField runtime sourceObject index =
      .error (.objectFieldOutOfBounds index info.size)) :
    readObjectField concrete.heap objectWord index =
      .error (.source (.objectFieldOutOfBounds index info.size)) := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap mapped =>
          cases mapped with
          | mapped found =>
              exact related.heap.readObjectField_outOfBounds_refines found
                descriptor projected
      | tagged taggedRelated =>
          cases taggedRelated
          <;> change Except.error RuntimeFault.expectedConstructor =
              Except.error (.objectFieldOutOfBounds index info.size) at projected
          <;> have faultEq := Except.error.inj projected
          <;> cases faultEq

theorem ConcreteRuntimeRel.readUSizeField_outOfBounds_refines
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeField runtime sourceObject index =
      .error (.usizeFieldOutOfBounds index info.usize)) :
    readUSizeField concrete.heap objectWord index =
      .error (.source (.usizeFieldOutOfBounds index info.usize)) := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap mapped =>
          cases mapped with
          | mapped found =>
              exact related.heap.readUSizeField_outOfBounds_refines found
                descriptor projected
      | tagged taggedRelated =>
          cases taggedRelated
          <;> change Except.error RuntimeFault.expectedConstructor =
              Except.error (.usizeFieldOutOfBounds index info.usize) at projected
          <;> have faultEq := Except.error.inj projected
          <;> cases faultEq

theorem ConcreteRuntimeRel.readUSizeSlot_outOfBounds_refines
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {slot : Nat}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeSlot runtime sourceObject slot =
      .error (.usizeFieldOutOfBounds slot (info.size + info.usize))) :
    readUSizeSlot concrete.heap objectWord slot =
      .error (.source (.usizeFieldOutOfBounds slot
        (info.size + info.usize))) := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap mapped =>
          cases mapped with
          | mapped found =>
              exact related.heap.readUSizeSlot_outOfBounds_refines found
                descriptor projected
      | tagged taggedRelated =>
          cases taggedRelated
          <;> change Except.error RuntimeFault.expectedConstructor =
              Except.error (.usizeFieldOutOfBounds slot
                (info.size + info.usize)) at projected
          <;> have faultEq := Except.error.inj projected
          <;> cases faultEq

theorem objectProjStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject value : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat} {kind : AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (kindAt : fieldKinds[index]? = some kind)
    (projected : getObjectField runtime sourceObject index = .ok value) :
    ∃ word,
      readObjectField initial.host.runtime.heap objectWord index = .ok word ∧
      objectProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [.i32 (UInt32.ofNat word.value)] (clearFailure initial) ∧
      ValueRel witness kind (.word32 word) value := by
  obtain ⟨word, read, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.readObjectField_refines runtimeRelated
      objectRelated descriptor kindAt projected
  refine ⟨word, read, ?_, valueRelated⟩
  simp [objectProjStep, clearFailure, read]

theorem usizeProjStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat} {value : UInt64}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeSlot runtime sourceObject index = .ok (.usize value)) :
    readUSizeSlot initial.host.runtime.heap objectWord index = .ok value ∧
      usizeProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [.i64 value] (clearFailure initial) ∧
      ValueRel witness .usize (.word64 value) (.usize value) := by
  obtain ⟨read, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.readUSizeSlot_refines runtimeRelated
      objectRelated descriptor projected
  refine ⟨read, ?_, valueRelated⟩
  simp [usizeProjStep, clearFailure, read]

/-- An object-field bounds fault crosses the concrete Talos host without
losing its FIR fault payload or its source classification. -/
theorem objectProjStep_outOfBounds_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getObjectField runtime sourceObject index =
      .error (.objectFieldOutOfBounds index info.size)) :
    objectProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
      trap (clearFailure initial) (.runtime (.source (.runtime
        (.objectFieldOutOfBounds index info.size)))) := by
  have read :=
    FirTalos.Concrete.ConcreteRuntimeRel.readObjectField_outOfBounds_refines
      runtimeRelated objectRelated descriptor projected
  simp [objectProjStep, clearFailure, read, ConcreteError.toTrap]

/-- A `USize`-field bounds fault crosses the concrete Talos host without
losing its FIR fault payload or its source classification. -/
theorem usizeProjStep_outOfBounds_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeSlot runtime sourceObject index =
      .error (.usizeFieldOutOfBounds index (info.size + info.usize))) :
    usizeProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
      trap (clearFailure initial) (.runtime (.source (.runtime
        (.usizeFieldOutOfBounds index (info.size + info.usize))))) := by
  have read :=
    FirTalos.Concrete.ConcreteRuntimeRel.readUSizeSlot_outOfBounds_refines
      runtimeRelated objectRelated descriptor projected
  simp [usizeProjStep, clearFailure, read, ConcreteError.toTrap]

/-- A stale object-field projection preserves the exact mapped dead-object
fault before any bounds or payload access. -/
theorem objectProjStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {location : Location}
    {cell : HeapCell} (index : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    objectProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      getObjectField runtime (.object (.heap location)) index =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.readObjectField_deadObject heapRelated found dead index
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [objectProjStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- The same stale-reference theorem for a `USize` projection. -/
theorem usizeProjStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {location : Location}
    {cell : HeapCell} (index : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    usizeProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      getUSizeSlot runtime (.object (.heap location)) index =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.readUSizeSlot_deadObject heapRelated found dead index
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [usizeProjStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- Every supported packed-integer projection rejects a stale mapped object at
the common live-header gate, before scalar-coordinate validation. -/
theorem scalarProjStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {location : Location}
    {cell : HeapCell} (width offset : Nat) (kind : AbiKind)
    (supported : kind = .uint8 ∨ kind = .uint16 ∨
      kind = .uint32 ∨ kind = .uint64)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    scalarProjStep width offset kind initial
        [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      getScalarField runtime (.object (.heap location)) width offset =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨read8, read16, read32, read64, semantic⟩ :=
            runtimeRelated.heap.readScalarFields_deadObject heapRelated found dead
              width offset
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          rcases supported with rfl | rfl | rfl | rfl <;>
            simp [scalarProjStep, clearFailure, Word32.ofUInt32_ofNat_value,
              read8, read16, read32, read64, ConcreteError.toTrap]

/-- A representation-polymorphic operand rejected by the semantic
constructor gateway is rejected by object projection with the same structured
source fault before index or payload decoding. -/
theorem objectProjStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    (index : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (constructorFailed :
      getConstructor runtime sourceObject = .error .expectedConstructor) :
    objectProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      getObjectField runtime sourceObject index =
        .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  have headerFailed :=
    runtimeRelated.heap.readConstructorHeader_expectedConstructor_refines
      objectRelated constructorFailed
  have readFailed :
      readObjectField initial.host.runtime.heap objectWord index =
        .error (.source .expectedConstructor) := by
    unfold readObjectField
    rw [headerFailed]
    rfl
  refine ⟨?_, ?_, .source .expectedConstructor⟩
  · simp [objectProjStep, clearFailure, Word32.ofUInt32_ofNat_value,
      readFailed, ConcreteError.toTrap]
  · unfold getObjectField
    rw [constructorFailed]
    rfl

/-- Absolute-slot `USize` projection crosses the same constructor gateway,
so a kind mismatch precedes slot arithmetic and retains the exact source
fault. -/
theorem usizeProjStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    (index : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (constructorFailed :
      getConstructor runtime sourceObject = .error .expectedConstructor) :
    usizeProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      getUSizeSlot runtime sourceObject index =
        .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  have headerFailed :=
    runtimeRelated.heap.readConstructorHeader_expectedConstructor_refines
      objectRelated constructorFailed
  have readFailed :
      readUSizeSlot initial.host.runtime.heap objectWord index =
        .error (.source .expectedConstructor) := by
    unfold readUSizeSlot
    rw [headerFailed]
    rfl
  refine ⟨?_, ?_, .source .expectedConstructor⟩
  · simp [usizeProjStep, clearFailure, Word32.ofUInt32_ofNat_value,
      readFailed, ConcreteError.toTrap]
  · unfold getUSizeSlot
    rw [constructorFailed]
    rfl

/-- Every supported packed-integer reader rejects a nonconstructor at the
shared header gate, before width-specific payload decoding. -/
theorem scalarProjStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    (width offset : Nat) (kind : AbiKind)
    (supported : kind = .uint8 ∨ kind = .uint16 ∨
      kind = .uint32 ∨ kind = .uint64)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (constructorFailed :
      getConstructor runtime sourceObject = .error .expectedConstructor) :
    scalarProjStep width offset kind initial
        [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      getScalarField runtime sourceObject width offset =
        .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  have headerFailed :=
    runtimeRelated.heap.readConstructorHeader_expectedConstructor_refines
      objectRelated constructorFailed
  have read8 :
      readScalarUInt8Field initial.host.runtime.heap objectWord width offset =
        .error (.source .expectedConstructor) := by
    unfold readScalarUInt8Field
    rw [headerFailed]
    rfl
  have read16 :
      readScalarUInt16Field initial.host.runtime.heap objectWord width offset =
        .error (.source .expectedConstructor) := by
    unfold readScalarUInt16Field
    rw [headerFailed]
    rfl
  have read32 :
      readScalarUInt32Field initial.host.runtime.heap objectWord width offset =
        .error (.source .expectedConstructor) := by
    unfold readScalarUInt32Field
    rw [headerFailed]
    rfl
  have read64 :
      readScalarUInt64Field initial.host.runtime.heap objectWord width offset =
        .error (.source .expectedConstructor) := by
    unfold readScalarUInt64Field
    rw [headerFailed]
    rfl
  refine ⟨?_, ?_, .source .expectedConstructor⟩
  · rcases supported with rfl | rfl | rfl | rfl <;>
      simp [scalarProjStep, clearFailure, Word32.ofUInt32_ofNat_value,
        read8, read16, read32, read64, ConcreteError.toTrap]
  · unfold getScalarField
    rw [constructorFailed]
    rfl

/--
The source scalar constructor agrees with the ABI lane selected by lowering.

This is a source-typing relation: it contains no concrete heap, address,
physical value, or executable-step witness.
-/
inductive ScalarValueKind : ScalarValue → AbiKind → Prop where
  | uint8 (value : UInt8) : ScalarValueKind (.uint8 value) .uint8
  | uint16 (value : UInt16) : ScalarValueKind (.uint16 value) .uint16
  | uint32 (value : UInt32) : ScalarValueKind (.uint32 value) .uint32
  | uint64 (value : UInt64) : ScalarValueKind (.uint64 value) .uint64

theorem scalarProjUInt8Step_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {value : UInt8}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar (.uint8 value))) :
    scalarProjStep width offset .uint8 initial
        [.i32 (UInt32.ofNat objectWord.value)] =
      .Return [.i32 (UInt32.ofNat (Word32.ofUInt8 value).value)]
        (clearFailure initial) ∧
      PhysicalValueRel witness .uint8
        (.i32 (UInt32.ofNat (Word32.ofUInt8 value).value))
        (.scalar (.uint8 value)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨read, valueRelated⟩ :=
                runtimeRelated.heap.readScalarUInt8Field_refines mapped projected
              exact ⟨by simp [scalarProjStep, clearFailure, read],
                .word32 valueRelated⟩
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getScalarField, getConstructor, Bind.bind, Except.bind]
              at projected

theorem scalarProjUInt16Step_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {value : UInt16}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar (.uint16 value))) :
    scalarProjStep width offset .uint16 initial
        [.i32 (UInt32.ofNat objectWord.value)] =
      .Return [.i32 (UInt32.ofNat (Word32.ofUInt16 value).value)]
        (clearFailure initial) ∧
      PhysicalValueRel witness .uint16
        (.i32 (UInt32.ofNat (Word32.ofUInt16 value).value))
        (.scalar (.uint16 value)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨read, valueRelated⟩ :=
                runtimeRelated.heap.readScalarUInt16Field_refines mapped projected
              exact ⟨by simp [scalarProjStep, clearFailure, read],
                .word32 valueRelated⟩
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getScalarField, getConstructor, Bind.bind, Except.bind]
              at projected

theorem scalarProjUInt32Step_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {value : UInt32}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar (.uint32 value))) :
    scalarProjStep width offset .uint32 initial
        [.i32 (UInt32.ofNat objectWord.value)] =
      .Return [.i32 (UInt32.ofNat (Word32.ofUInt32 value).value)]
        (clearFailure initial) ∧
      PhysicalValueRel witness .uint32
        (.i32 (UInt32.ofNat (Word32.ofUInt32 value).value))
        (.scalar (.uint32 value)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨read, valueRelated⟩ :=
                runtimeRelated.heap.readScalarUInt32Field_refines mapped projected
              exact ⟨by simp [scalarProjStep, clearFailure, read],
                .word32 valueRelated⟩
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getScalarField, getConstructor, Bind.bind, Except.bind]
              at projected

theorem scalarProjUInt64Step_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {value : UInt64}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar (.uint64 value))) :
    scalarProjStep width offset .uint64 initial
        [.i32 (UInt32.ofNat objectWord.value)] =
      .Return [.i64 value] (clearFailure initial) ∧
      PhysicalValueRel witness .uint64 (.i64 value)
        (.scalar (.uint64 value)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨read, valueRelated⟩ :=
                runtimeRelated.heap.readScalarUInt64Field_refines mapped projected
              exact ⟨by simp [scalarProjStep, clearFailure, read],
                .word64 valueRelated⟩
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getScalarField, getConstructor, Bind.bind, Except.bind]
              at projected

/--
Every successfully projected, ABI-aligned integer scalar has one matching
concrete host step and related physical result.

This unifies the four integer lanes used by the compiler. It is deliberately
a success theorem: it does not claim that a valid but semantically
uninitialized coordinate faults in the zero-filled concrete heap.
-/
theorem scalarProjStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {scalar : ScalarValue} {kind : AbiKind}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar scalar))
    (kindAligned : ScalarValueKind scalar kind) :
    ∃ physical,
      scalarProjStep width offset kind initial
          [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [physical] (clearFailure initial) ∧
      PhysicalValueRel witness kind physical (.scalar scalar) := by
  cases kindAligned with
  | uint8 value =>
      exact ⟨.i32 (UInt32.ofNat (Word32.ofUInt8 value).value),
        scalarProjUInt8Step_of_refines runtimeRelated objectRelated projected⟩
  | uint16 value =>
      exact ⟨.i32 (UInt32.ofNat (Word32.ofUInt16 value).value),
        scalarProjUInt16Step_of_refines runtimeRelated objectRelated projected⟩
  | uint32 value =>
      exact ⟨.i32 (UInt32.ofNat (Word32.ofUInt32 value).value),
        scalarProjUInt32Step_of_refines runtimeRelated objectRelated projected⟩
  | uint64 value =>
      exact ⟨.i64 value,
        scalarProjUInt64Step_of_refines runtimeRelated objectRelated projected⟩

theorem naturalLiteralStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {value : Nat} {heap : MemoryState}
    {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (allocated : allocateNatural initial.host.runtime.heap value =
      .ok (heap, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      naturalLiteralStep value initial [] =
        .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal runtime (.nat value)).1 ∧
      PhysicalValueRel nextWitness .tobject
        (.i32 (UInt32.ofNat word.value)) (literal runtime (.nat value)).2 := by
  obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateNatural runtimeRelated allocated
  refine ⟨nextWitness, extension, ?_, ?_, .word32 valueRelated⟩
  · simp [naturalLiteralStep, replaceHeap, clearFailure, allocated]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated

theorem stringLiteralStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {value : String} {heap : MemoryState}
    {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (allocated : allocateString initial.host.runtime.heap value =
      .ok (heap, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      stringLiteralStep value initial [] =
        .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal runtime (.str value)).1 ∧
      PhysicalValueRel nextWitness .object
        (.i32 (UInt32.ofNat word.value)) (literal runtime (.str value)).2 := by
  obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateString runtimeRelated allocated
  refine ⟨nextWitness, extension, ?_, ?_, .word32 valueRelated⟩
  · simp [stringLiteralStep, replaceHeap, clearFailure, allocated]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated

/-- The compiler may widen an exact tagged constructor result to `tobject`. -/
theorem taggedConstructorResult_of_refines
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {resultKind : AbiKind} {word : Word32}
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (related : ValueRel witness .tagged (.word32 word)
      (.object (.tagged (UInt64.ofNat info.cidx)))) :
    ValueRel witness resultKind (.word32 word)
      (.object (.tagged (UInt64.ofNat info.cidx))) := by
  cases resultKind <;>
    simp [constructorKind, empty.1.1, empty.1.2, empty.2, AbiKind.refines]
      at resultRefines
  · exact related
  · exact related.tagged_to_tobject

/-- The compiler may widen an exact heap constructor result to `tobject`. -/
theorem objectConstructorResult_of_refines
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {resultKind : AbiKind} {word : Word32} {location : Location}
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (resultRefines : (constructorKind info).refines resultKind = true)
    (related : ValueRel witness .object (.word32 word)
      (.object (.heap location))) :
    ValueRel witness resultKind (.word32 word) (.object (.heap location)) := by
  cases resultKind <;>
    simp [constructorKind, nonempty, AbiKind.refines] at resultRefines
  · exact related
  · exact related.object_to_tobject

/-- Executable/refinement boundary for an empty constructor. The returned word
is immediate when possible and otherwise a fresh promoted tag. -/
theorem allocCtorEmptyStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
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
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness runtime ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat word.value))
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  obtain ⟨nextWitness, extension, nextRuntimeRelated, exactRelated,
      semanticStep⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorEmpty runtimeRelated
      arity semanticArity empty tagFits allocated
  have valueRelated := taggedConstructorResult_of_refines empty resultRefines
    exactRelated
  refine ⟨nextWitness, extension, ?_, ?_, .word32 valueRelated,
    semanticStep⟩
  · simp [allocCtorStep, argsLength, decoded, allocated, replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated

/-- Empty constructor execution additionally exports mapped-header capacity
transport for the syntax-directed reuse-capacity invariant. -/
theorem allocCtorEmptyStep_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
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
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness runtime ∧
      ValueRel nextWitness resultKind (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat word.value))
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness := by
  obtain ⟨nextWitness, extension, nextRuntimeRelated, exactRelated,
      semanticStep, capacityTransport⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorEmpty_with_capacity
      runtimeRelated arity semanticArity empty tagFits allocated
  have valueRelated := taggedConstructorResult_of_refines empty resultRefines
    exactRelated
  refine ⟨nextWitness, extension, ?_, ?_, valueRelated, .word32 valueRelated,
    semanticStep, capacityTransport⟩
  · simp [allocCtorStep, argsLength, decoded, allocated, replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated

/-- Executable/refinement boundary for a nonempty constructor allocation. -/
theorem allocCtorNonemptyStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
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
    (allocated : allocateConstructor initial.host.runtime.heap info fields.toArray =
      .ok (heap, address)) :
    let nextWitness := witness.bindConstructor runtime.nextLocation address info
      fieldKinds
    witness.Extends nextWitness ∧
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value))
        (.object (.heap runtime.nextLocation)) ∧
      allocCtor runtime info semanticFields =
        .ok (semanticConstructorResult runtime info semanticFields,
          .object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨extension, nextRuntimeRelated, exactRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorNonempty runtimeRelated
      arity semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty
      tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have valueRelated := objectConstructorResult_of_refines nonempty resultRefines
    exactRelated
  refine ⟨extension, ?_, ?_, .word32 valueRelated,
    allocCtor_nonempty_eq runtime info semanticFields semanticArity nonempty⟩
  · simp [allocCtorStep, argsLength, decoded, allocated, replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated

/--
Capacity-driven executable/refinement boundary for a nonempty constructor.
The concrete heap and result address are constructed from the static layout
rather than supplied through an opaque successful-allocation equation.
-/
theorem allocCtorNonemptyStep_of_refines_of_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value}
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
    (capacity :
      initial.host.runtime.heap.AllocationCapacity
        (ConstructorLayout.ofInfo info).allocationBytes) :
    ∃ heap address,
      let nextWitness := witness.bindConstructor runtime.nextLocation address info
        fieldKinds
      witness.Extends nextWitness ∧
        allocCtorStep info fieldKinds resultKind initial physicalArgs =
          .Return [.i32 (UInt32.ofNat address.value)]
            (replaceHeap initial heap) ∧
        ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
          (semanticConstructorResult runtime info semanticFields) ∧
        PhysicalValueRel nextWitness resultKind
          (.i32 (UInt32.ofNat address.value))
          (.object (.heap runtime.nextLocation)) ∧
        allocCtor runtime info semanticFields =
          .ok (semanticConstructorResult runtime info semanticFields,
            .object (.heap runtime.nextLocation)) := by
  obtain ⟨heap, address, allocated⟩ :=
    MemoryState.FrontierInvariant.allocateConstructor_nonempty_eq_ok_of_capacity
      runtimeRelated.heap.frontier info fields.toArray arity nonempty tagFits
        objectFieldsFit usizeFieldsFit scalarBytesFit capacity
  exact ⟨heap, address,
    allocCtorNonemptyStep_of_refines runtimeRelated argsLength decoded arity
      semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty tagFits
      objectFieldsFit usizeFieldsFit scalarBytesFit resultRefines allocated⟩

/--
Budget-threaded nonempty constructor boundary. In addition to constructing the
host/source refinement step, it exports the exact residual wasm32 path budget.
-/
theorem allocCtorNonemptyStep_of_refines_of_budget
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value} {remainingBytes : Nat}
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
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits :
      (ConstructorLayout.ofInfo info).allocationBytes ≤ remainingBytes) :
    ∃ heap address,
      heap.AddressSpaceBudget
          (remainingBytes - (ConstructorLayout.ofInfo info).allocationBytes) ∧
        let nextWitness := witness.bindConstructor runtime.nextLocation address
          info fieldKinds
        witness.Extends nextWitness ∧
          allocCtorStep info fieldKinds resultKind initial physicalArgs =
            .Return [.i32 (UInt32.ofNat address.value)]
              (replaceHeap initial heap) ∧
          ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
            (semanticConstructorResult runtime info semanticFields) ∧
          PhysicalValueRel nextWitness resultKind
            (.i32 (UInt32.ofNat address.value))
            (.object (.heap runtime.nextLocation)) ∧
          allocCtor runtime info semanticFields =
            .ok (semanticConstructorResult runtime info semanticFields,
              .object (.heap runtime.nextLocation)) ∧
          allocateConstructor initial.host.runtime.heap info fields.toArray =
            .ok (heap, address) := by
  obtain ⟨heap, address, allocated, remainingBudget⟩ :=
    MemoryState.FrontierInvariant.allocateConstructor_nonempty_eq_ok_of_budget
      runtimeRelated.heap.frontier info fields.toArray arity nonempty tagFits
        objectFieldsFit usizeFieldsFit scalarBytesFit budget fits
  refine ⟨heap, address, remainingBudget, ?_⟩
  have core :=
    allocCtorNonemptyStep_of_refines runtimeRelated argsLength decoded arity
      semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty tagFits
      objectFieldsFit usizeFieldsFit scalarBytesFit resultRefines allocated
  exact ⟨core.1, core.2.1, core.2.2.1, core.2.2.2.1,
    core.2.2.2.2, allocated⟩

/-- A related physical value always decodes to the exact W6 lane witnessed by
`ValueRel`. -/
theorem decodePhysicalLane_of_related
    {witness : RefinementWitness} {kind : AbiKind} {physical : Wasm.Value}
    {semantic : Value}
    (related : PhysicalValueRel witness kind physical semantic) :
    ∃ lane,
      decodePhysicalLane kind physical = .ok lane ∧
      ValueRel witness kind lane semantic := by
  cases related with
  | word32 valueRelated =>
      refine ⟨_, ?_, valueRelated⟩
      cases valueRelated <;>
        simp [decodePhysicalLane, AbiKind.valueType]
  | word64 valueRelated =>
      refine ⟨_, ?_, valueRelated⟩
      cases valueRelated <;> rfl
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

/--
Every related physical value constructively drives the complete concrete
cache transition. Recursive persistence is discharged from `ValueRel`; the
caller supplies only the immutable host/witness descriptor-table identity.
The host returns the same physical lane for the generated Wasm global write.
-/
theorem cacheSetStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {declaration : Lean.Name} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value} {slot : ConcreteGlobalSlot}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated : PhysicalValueRel witness kind physical semantic)
    (found : initial.host.runtime.globals.find? declaration = some slot)
    (kindEq : slot.kind = kind)
    (descriptorsEq : initial.host.closureDescriptors =
      witness.closureDescriptors) :
    ∃ after,
      cacheSetStep declaration kind initial [physical] =
        .Return [physical] (replaceRuntime initial after) ∧
      ConcreteRuntimeRel (replaceRuntime initial after).host.runtime witness
        (runtime.setGlobal declaration semantic) ∧
      PhysicalValueRel witness kind physical semantic ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap after.heap
        witness := by
  obtain ⟨lane, decoded, laneRelated⟩ :=
    decodePhysicalLane_of_related valueRelated
  obtain ⟨after, operation, nextRuntimeRelated, capacity⟩ :=
    Fir.Wasm.Concrete.ConcreteRuntimeRel.writeGlobal_of_related runtimeRelated
      found kindEq laneRelated descriptorsEq
  refine ⟨after, ?_, ?_, valueRelated, capacity⟩
  · simp [cacheSetStep, clearFailure, decoded, operation, replaceRuntime]
  · simpa [replaceRuntime, clearFailure] using nextRuntimeRelated

/-- Executable/refinement boundary for partial-application closure allocation.
The `.tagged` result admitted by the current validator is deliberately absent;
see `FIR-BUG-wasm-none-partial-apply-tagged-result`. -/
theorem partialApplyStep_of_refines
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
    (targetLookup : initial.host.closureDispatch.lookup? targetId = some function)
    (descriptorIdEq : closureDescriptorId initial.host.closureDescriptors
      fieldKinds = .ok descriptorId)
    (descriptorLookup : initial.host.closureDescriptors.lookup? descriptorId =
      some fieldKinds)
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
      initial.host.closureDispatch initial.host.closureDescriptors function arity
      fieldKinds captures.toArray = .ok (heap, address)) :
    let nextWitness := witness.bindClosure runtime.nextLocation address function
      arity fieldKinds
    witness.Extends nextWitness ∧
      partialApplyStep function arity fixed fieldKinds resultKind initial
          physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (semanticClosureResult runtime function arity semantic) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value))
        (.object (.heap runtime.nextLocation)) ∧
      alloc runtime (.closure function arity semantic) =
        (semanticClosureResult runtime function arity semantic,
          .heap runtime.nextLocation) := by
  dsimp only
  obtain ⟨extension, heapRelated, objectRelated, tobjectRelated⟩ :=
    allocateClosure_liveHeapRel_extends initial.host.runtime.heap heap witness
      runtime initial.host.closureDispatch initial.host.closureDescriptors
      function arity fieldKinds captures.toArray semantic address targetId
      descriptorId runtimeRelated.heap count semanticCount capturesLtArity
      targetIdEq targetLookup descriptorIdEq descriptorLookup dispatchEq
      descriptorsEq arityFits fixedFits captureTyped captureRelated allocated
  have valueRelated : ValueRel
      (witness.bindClosure runtime.nextLocation address function arity fieldKinds)
      resultKind (.word32 address) (.object (.heap runtime.nextLocation)) := by
    rcases resultKindSupported with rfl | rfl
    · exact objectRelated
    · exact tobjectRelated
  refine ⟨extension, ?_, ?_, .word32 valueRelated,
    alloc_closure_eq runtime function arity semantic⟩
  · simp [partialApplyStep, fixedArgs, decoded, allocated, replaceHeap,
      clearFailure]
  · exact {
      heap := by simpa [replaceHeap, clearFailure] using heapRelated
      globals := by
        simpa [replaceHeap, clearFailure, semanticClosureResult] using
          runtimeRelated.globals.witnessExtension extension
      world := by
        simpa [replaceHeap, clearFailure, semanticClosureResult] using
          runtimeRelated.world
      trace := by
        simpa [replaceHeap, clearFailure, semanticClosureResult] using
          runtimeRelated.trace.witnessExtension extension }

/-- Any successful executable matcher return carries the exact semantic
identity bit. A nonmatching candidate is read-only; a matching candidate may
have taken ownership before returning, so the theorem intentionally exposes
the result independently of the post-store. -/
theorem closureMatchesStep_result_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {function : Lean.Name} {arity : Nat}
    {captures : Array Value} {expectedFunction : Lean.Name}
    {expectedArity expectedFixed : Nat} {results : List Wasm.Value}
    {next : Wasm.Store Host}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (operation :
      closureMatchesStep expectedFunction expectedArity expectedFixed initial
          [.i32 (UInt32.ofNat address.value)] = .Return results next) :
    results = [
      .i32 (if function == expectedFunction && arity == expectedArity &&
        captures.size == expectedFixed then 1 else 0)] ∧
      closureData runtime (.object (.heap location)) =
        .ok (function, arity, captures) := by
  have concreteMatch := runtimeRelated.heap.closureMatches_refines mapped found live
    objectEq expectedFunction expectedArity expectedFixed
  constructor
  · unfold closureMatchesStep at operation
    simp only [clearFailure] at operation
    rw [Word32.ofUInt32_ofNat_value, ← dispatchEq, ← descriptorsEq,
      concreteMatch] at operation
    by_cases identity :
        (function == expectedFunction && arity == expectedArity &&
          captures.size == expectedFixed) = true
    · simp only [identity, if_true] at operation ⊢
      cases taken : takeClosureApplication initial.host.runtime.heap
          witness.closureDispatch witness.closureDescriptors address with
      | error failure =>
          simp [taken, trap] at operation
      | ok result =>
          obtain ⟨heap, application⟩ := result
          simp [taken] at operation
          exact operation.1.symm
    · have identityFalse :
          (function == expectedFunction && arity == expectedArity &&
            captures.size == expectedFixed) = false :=
        Bool.eq_false_of_not_eq_true identity
      simp [identityFalse] at operation ⊢
      exact operation.1.symm
  · unfold closureData
    simp only [getLiveCell, found, live, if_true, Bind.bind, Except.bind]
    rw [objectEq]
    rfl

/-- A nonmatching candidate performs the exact read-only matcher return. -/
theorem closureMatchesStep_miss_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {function : Lean.Name} {arity : Nat}
    {captures : Array Value} {expectedFunction : Lean.Name}
    {expectedArity expectedFixed : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (identityFalse :
      (function == expectedFunction && arity == expectedArity &&
        captures.size == expectedFixed) = false) :
    closureMatchesStep expectedFunction expectedArity expectedFixed initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [.i32 0] (clearFailure initial) := by
  have concreteMatch := runtimeRelated.heap.closureMatches_refines mapped found live
    objectEq expectedFunction expectedArity expectedFixed
  unfold closureMatchesStep
  simp only [clearFailure]
  rw [Word32.ofUInt32_ofNat_value, ← dispatchEq, ← descriptorsEq,
    concreteMatch]
  simp [identityFalse]

/-- A matcher returning the zero bit cannot have crossed the ownership
boundary, so its post-store is exactly the failure-cleared input store. -/
theorem closureMatchesStep_zero_store
    {function : Lean.Name} {arity fixed : Nat}
    {initial next : Wasm.Store Host} {address : Word32}
    (operation :
      closureMatchesStep function arity fixed initial
          [.i32 (UInt32.ofNat address.value)] =
        .Return [.i32 0] next) :
    next = clearFailure initial := by
  unfold closureMatchesStep at operation
  simp only [clearFailure] at operation ⊢
  rw [Word32.ofUInt32_ofNat_value] at operation
  cases matched : closureMatches initial.host.runtime.heap
      initial.host.closureDispatch initial.host.closureDescriptors address
      function arity fixed with
  | error failure =>
      simp [matched, trap] at operation
  | ok result =>
      rw [matched] at operation
      by_cases resultZero : (result == 0) = true
      · simp [resultZero] at operation
        exact operation.2.symm
      · cases taken : takeClosureApplication initial.host.runtime.heap
            initial.host.closureDispatch initial.host.closureDescriptors address with
        | error failure =>
            simp [resultZero, taken, trap] at operation
        | ok application =>
            simp [resultZero, taken] at operation
            exact (resultZero (by simp [operation.1])).elim

/-- Executable typed capture projection returns the exact Talos lane related
to the selected semantic application snapshot and preserves the runtime
state. -/
theorem closureProjStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {application : ClosureApplication} {address : Word32}
    {function : Lean.Name} {arity fixed index : Nat}
    {captures : Array Value} {captureKinds : Array AbiKind}
    {kind : AbiKind} {value : Value}
    (applicationFound : initial.host.closureApplication? = some application)
    (applicationRelated : ClosureApplicationRel witness application address
      function arity captureKinds captures)
    (fixedSize : captures.size = fixed)
    (kindAt : captureKinds[index]? = some kind)
    (valueAt : captures[index]? = some value) :
    ∃ lane,
      closureProjStep function arity fixed index kind initial
          [.i32 (UInt32.ofNat address.value)] =
        .Return [physicalOfLane lane] (clearFailure initial) ∧
      PhysicalValueRel witness kind (physicalOfLane lane) value := by
  obtain ⟨lane, projected, valueRelated⟩ :=
    applicationRelated.project index kind value kindAt valueAt
  rw [fixedSize] at projected
  refine ⟨lane, ?_, physicalOfLane_related valueRelated⟩
  · unfold closureProjStep
    simp only [clearFailure]
    rw [applicationFound]
    simp only
    rw [Word32.ofUInt32_ofNat_value, projected]

/-- A successful semantic heap-cell replacement changes only the heap field. -/
theorem setCell_heapOnly
    {before after : RuntimeState} {location : Location} {cell : HeapCell}
    (updated : setCell before location cell = .ok after) :
    ∃ heap, after = { before with heap := heap } := by
  unfold setCell at updated
  split at updated
  · rename_i heap replaced
    exact ⟨heap, (Except.ok.inj updated).symm⟩
  · contradiction

/-- A successful semantic increment changes at most the heap field of the
runtime. This packages the auxiliary-state frame needed to lift a heap proof
to `ConcreteRuntimeRel`. -/
theorem incValue_heapOnly
    {before after : RuntimeState} {value : Value} {amount : Nat} {check : Bool}
    (updated : incValue before value amount check = .ok after) :
    ∃ heap, after = { before with heap := heap } := by
  cases value with
  | object reference =>
      cases reference with
      | tagged payload =>
          cases check <;> simp [incValue] at updated
          exact ⟨before.heap, updated.symm⟩
      | heap location =>
          simp only [incValue] at updated
          unfold incLocation at updated
          cases read : getLiveCell before location with
          | error failure =>
              simp only [read, Bind.bind, Except.bind] at updated
              cases updated
          | ok cell =>
              simp only [read, Bind.bind, Except.bind] at updated
              cases persistent : cell.persistent with
              | false =>
                  simp only [persistent, Bool.false_eq_true, ↓reduceIte] at updated
                  exact setCell_heapOnly updated
              | true =>
                  simp only [persistent, ↓reduceIte] at updated
                  have afterEq : before = after := Except.ok.inj updated
                  exact ⟨before.heap, by simpa using afterEq.symm⟩
  | usize value => simp [incValue] at updated
  | scalar value => simp [incValue] at updated
  | erased => simp [incValue] at updated
  | reuseToken location => simp [incValue] at updated

/-- The auxiliary semantic runtime components preserved by ownership changes.
Recursive decrement can update several heap cells, so an exact one-record
`heapOnly` equation is inconvenient; these are precisely the components that
the non-heap fields of `ConcreteRuntimeRel` observe. -/
structure RuntimeAuxEq (before after : RuntimeState) : Prop where
  globals : after.globals = before.globals
  world : after.world = before.world
  trace : after.trace = before.trace

theorem RuntimeAuxEq.refl (runtime : RuntimeState) :
    RuntimeAuxEq runtime runtime := by
  exact ⟨rfl, rfl, rfl⟩

theorem RuntimeAuxEq.trans
    {before middle after : RuntimeState}
    (first : RuntimeAuxEq before middle)
    (second : RuntimeAuxEq middle after) :
    RuntimeAuxEq before after := by
  exact ⟨second.globals.trans first.globals,
    second.world.trans first.world, second.trace.trans first.trace⟩

theorem setCell_runtimeAux
    {before after : RuntimeState} {location : Location} {cell : HeapCell}
    (updated : setCell before location cell = .ok after) :
    RuntimeAuxEq before after := by
  rcases setCell_heapOnly updated with ⟨heap, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

/-- A successful state-threading fold preserves auxiliary runtime state when
each successful step does. -/
theorem List.foldlM_runtimeAux
    {α : Type} {step : RuntimeState → α → Except RuntimeFault RuntimeState}
    (stepAux : ∀ {before after item},
      step before item = .ok after → RuntimeAuxEq before after)
    {items : List α} {before after : RuntimeState}
    (operation : items.foldlM (init := before) step = .ok after) :
    RuntimeAuxEq before after := by
  induction items generalizing before with
  | nil =>
      simp only [List.foldlM_nil] at operation
      have runtimeEq := Except.ok.inj operation
      subst after
      exact RuntimeAuxEq.refl _
  | cons item items ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at operation
      cases head : step before item with
      | error failure =>
          rw [head] at operation
          contradiction
      | ok middle =>
          rw [head] at operation
          exact (stepAux head).trans (ih operation)

theorem Array.foldlM_runtimeAux
    {α : Type} {step : RuntimeState → α → Except RuntimeFault RuntimeState}
    (stepAux : ∀ {before after item},
      step before item = .ok after → RuntimeAuxEq before after)
    {items : Array α} {before after : RuntimeState}
    (operation : items.foldlM step before = .ok after) :
    RuntimeAuxEq before after := by
  have listOperation :
      items.toList.foldlM (init := before) step = .ok after := by
    simpa only [Array.foldlM_toList] using operation
  exact List.foldlM_runtimeAux stepAux listOperation

theorem incLocation_runtimeAux
    {before after : RuntimeState} {location amount : Nat}
    (operation : incLocation before location amount = .ok after) :
    RuntimeAuxEq before after := by
  unfold incLocation at operation
  cases read : getLiveCell before location with
  | error failure =>
      simp only [read, Bind.bind, Except.bind] at operation
      contradiction
  | ok cell =>
      simp only [read, Bind.bind, Except.bind] at operation
      cases persistent : cell.persistent with
      | true =>
          simp only [persistent, if_true] at operation
          have runtimeEq := Except.ok.inj operation
          subst after
          exact RuntimeAuxEq.refl _
      | false =>
          simp only [persistent, Bool.false_eq_true, if_false] at operation
          exact setCell_runtimeAux operation

theorem retainOwnedValue_runtimeAux
    {before after : RuntimeState} {value : Value}
    (operation : retainOwnedValue before value = .ok after) :
    RuntimeAuxEq before after := by
  cases value with
  | object reference =>
      cases reference with
      | heap location => exact incLocation_runtimeAux operation
      | tagged payload =>
          have runtimeEq := Except.ok.inj operation
          subst after
          exact RuntimeAuxEq.refl _
  | usize value | scalar value | erased | reuseToken value =>
      have runtimeEq := Except.ok.inj operation
      subst after
      exact RuntimeAuxEq.refl _

/-- Taking a closure application changes only source heap ownership. Its
metadata result and capture snapshot do not affect globals, the external
world token, or the observable trace. -/
theorem takeClosureApplication_runtimeAux
    {before after : RuntimeState} {location : Location}
    {function : Lean.Name} {arity : Nat} {captures : Array Value}
    (operation : Fir.LeanIR.Impure.takeClosureApplication before location =
      .ok (after, function, arity, captures)) :
    RuntimeAuxEq before after := by
  unfold Fir.LeanIR.Impure.takeClosureApplication at operation
  cases read : getLiveCell before location with
  | error failure =>
      simp only [read, Bind.bind, Except.bind] at operation
      contradiction
  | ok cell =>
      simp only [read, Bind.bind, Except.bind] at operation
      cases objectEq : cell.object with
      | closure storedFunction storedArity storedCaptures =>
          simp only [objectEq] at operation
          cases persistent : cell.persistent with
          | true =>
              simp only [persistent, if_true] at operation
              have runtimeEq : before = after :=
                congrArg (fun result => result.1) (Except.ok.inj operation)
              subst after
              exact RuntimeAuxEq.refl _
          | false =>
              simp only [persistent, Bool.false_eq_true, if_false] at operation
              by_cases zero : cell.rc = 0
              · simp [zero] at operation
              · rw [if_neg zero] at operation
                by_cases one : cell.rc = 1
                · rw [if_pos one] at operation
                  cases changed : setCell before location
                      { object := .closure storedFunction storedArity
                          storedCaptures
                        rc := 0
                        live := false } with
                  | error failure =>
                      rw [changed] at operation
                      contradiction
                  | ok next =>
                      rw [changed] at operation
                      have runtimeEq : next = after :=
                        congrArg (fun result => result.1)
                          (Except.ok.inj operation)
                      subst after
                      exact setCell_runtimeAux changed
                · rw [if_neg one] at operation
                  cases changed : setCell before location
                      { object := .closure storedFunction storedArity
                          storedCaptures
                        rc := cell.rc - 1
                        live := cell.live } with
                  | error failure =>
                      rw [changed] at operation
                      contradiction
                  | ok parent =>
                      rw [changed] at operation
                      simp only [Bind.bind, Except.bind] at operation
                      cases retained : storedCaptures.foldlM retainOwnedValue
                          parent with
                      | error failure =>
                          rw [retained] at operation
                          contradiction
                      | ok final =>
                          rw [retained] at operation
                          have runtimeEq : final = after :=
                            congrArg (fun result => result.1)
                              (Except.ok.inj operation)
                          subst after
                          exact (setCell_runtimeAux changed).trans
                            (Array.foldlM_runtimeAux
                              (fun stepOperation =>
                                retainOwnedValue_runtimeAux stepOperation)
                              retained)
      | ctor info =>
          simp [objectEq] at operation
      | boxed type value =>
          simp [objectEq] at operation
      | natural value =>
          simp [objectEq] at operation
      | integer value =>
          simp [objectEq] at operation
      | string value =>
          simp [objectEq] at operation
      | byteArray bytes =>
          simp [objectEq] at operation
      | «opaque» name =>
          simp [objectEq] at operation

/-- Every successful recursive semantic release preserves globals, world, and
external trace, including all recursively released children. -/
theorem decLocationFuel_runtimeAux
    {fuel : Nat} {before after : RuntimeState} {location : Location}
    (operation : decLocationFuel fuel before location = .ok after) :
    RuntimeAuxEq before after := by
  induction fuel generalizing before after location with
  | zero => simp [decLocationFuel] at operation
  | succ fuel ih =>
      simp only [decLocationFuel] at operation
      cases read : getLiveCell before location with
      | error failure =>
          simp only [read, Bind.bind, Except.bind] at operation
          contradiction
      | ok cell =>
          simp only [read, Bind.bind, Except.bind] at operation
          cases persistent : cell.persistent with
          | true =>
              simp only [persistent, ↓reduceIte] at operation
              have runtimeEq := Except.ok.inj operation
              subst after
              exact RuntimeAuxEq.refl _
          | false =>
              simp only [persistent, Bool.false_eq_true, ↓reduceIte] at operation
              by_cases zero : cell.rc = 0
              · rw [if_pos zero] at operation
                contradiction
              · rw [if_neg zero] at operation
                by_cases aboveOne : cell.rc > 1
                · rw [if_pos aboveOne] at operation
                  exact setCell_runtimeAux operation
                · rw [if_neg aboveOne] at operation
                  cases parentOperation :
                      setCell before location
                        { object := cell.object, rc := 0, live := false } with
                  | error failure =>
                      rw [parentOperation] at operation
                      contradiction
                  | ok parent =>
                      rw [parentOperation] at operation
                      apply (setCell_runtimeAux parentOperation).trans
                      apply Array.foldlM_runtimeAux (operation := operation)
                      intro childBefore childAfter value childOperation
                      cases value with
                      | object reference =>
                          cases reference with
                          | heap child => exact ih childOperation
                          | tagged payload =>
                              simp only at childOperation
                              have runtimeEq := Except.ok.inj childOperation
                              subst childAfter
                              exact RuntimeAuxEq.refl _
                      | usize value | scalar value | erased | reuseToken value =>
                          simp only at childOperation
                          have runtimeEq := Except.ok.inj childOperation
                          subst childAfter
                          exact RuntimeAuxEq.refl _

theorem decLocation_runtimeAux
    {before after : RuntimeState} {location : Location}
    (operation : decLocation before location = .ok after) :
    RuntimeAuxEq before after := by
  exact decLocationFuel_runtimeAux operation

theorem decValueOnce_runtimeAux
    {before after : RuntimeState} {value : Value} {check : Bool}
    (operation : decValueOnce before value check = .ok after) :
    RuntimeAuxEq before after := by
  cases value with
  | object reference =>
      cases reference with
      | heap location =>
          exact decLocation_runtimeAux operation
      | tagged payload =>
          cases check <;> simp [decValueOnce] at operation
          subst after
          exact RuntimeAuxEq.refl _
  | usize value | scalar value | erased | reuseToken value =>
      simp [decValueOnce] at operation

theorem releaseResetField_runtimeAux
    {before after : RuntimeState} {value : Value}
    (operation : releaseResetField before value = .ok after) :
    RuntimeAuxEq before after := by
  cases value with
  | erased =>
      have runtimeEq : before = after := Except.ok.inj operation
      subst after
      exact RuntimeAuxEq.refl _
  | object reference | usize value | scalar value | reuseToken value =>
      exact decValueOnce_runtimeAux (by
        simpa [releaseResetField] using operation)

theorem decValue_runtimeAux
    {before after : RuntimeState} {value : Value} {amount : Nat} {check : Bool}
    (operation : decValue before value amount check = .ok after) :
    RuntimeAuxEq before after := by
  apply List.foldlM_runtimeAux (operation := operation)
  exact fun stepOperation => decValueOnce_runtimeAux stepOperation

/-- Successful explicit deletion changes only the semantic heap. The erased
reset sentinel is an identity, and an ordinary object deletion is one
`setCell` update. -/
theorem deleteValue_runtimeAux
    {before after : RuntimeState} {value : Value}
    (operation : deleteValue before value = .ok after) :
    RuntimeAuxEq before after := by
  cases value with
  | erased =>
      have runtimeEq : before = after := Except.ok.inj operation
      subst after
      exact RuntimeAuxEq.refl _
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
              simp only [read, Bind.bind, Except.bind] at operation
              exact setCell_runtimeAux operation
  | usize value | scalar value | reuseToken value =>
      simp [deleteValue] at operation

/-- Constructor allocation changes only the semantic heap and next-location
counter, so the auxiliary runtime observations are exact frames. -/
theorem allocCtor_runtimeAux
    {before after : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
    {fields : Array Value} {value : Value}
    (operation : allocCtor before info fields = .ok (after, value)) :
    RuntimeAuxEq before after := by
  by_cases arity : fields.size = info.size
  · by_cases empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0
    · rw [allocCtor_empty_eq before info fields arity empty] at operation
      have runtimeEq : before = after :=
        congrArg Prod.fst (Except.ok.inj operation)
      subst after
      exact RuntimeAuxEq.refl _
    · rw [allocCtor_nonempty_eq before info fields arity empty] at operation
      have runtimeEq : semanticConstructorResult before info fields = after :=
        congrArg Prod.fst (Except.ok.inj operation)
      subst after
      exact ⟨rfl, rfl, rfl⟩
  · have mismatch : (fields.size != info.size) = true := by simp [arity]
    unfold allocCtor at operation
    rw [if_pos mismatch] at operation
    contradiction

/-- Successful reuse, whether fresh or in place, preserves globals, world,
and the external trace exactly. -/
theorem reuse_runtimeAux
    {before after : RuntimeState} {token : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {updateHeader : Bool}
    {fields : Array Value} {value : Value}
    (operation : reuse before token info updateHeader fields =
      .ok (after, value)) : RuntimeAuxEq before after := by
  cases token with
  | reuseToken location? =>
      cases location? with
      | none =>
          exact allocCtor_runtimeAux operation
      | some location =>
          unfold reuse at operation
          simp only at operation
          by_cases arity : fields.size != info.size
          · rw [if_pos arity] at operation
            contradiction
          · rw [if_neg arity] at operation
            cases read : getLiveCell before location with
            | error failure =>
                rw [read] at operation
                contradiction
            | ok cell =>
                rw [read] at operation
                simp only [Bind.bind, Except.bind] at operation
                cases objectEq : cell.object with
                | ctor old =>
                    simp only [objectEq] at operation
                    cases changed : setCell before location
                        { cell with object := .ctor {
                            tag := if updateHeader then info.cidx else old.tag
                            objectFields := fields
                            usizeFields := Array.replicate info.usize 0
                            scalarFields := [] } } with
                    | error failure =>
                        rw [changed] at operation
                        contradiction
                    | ok next =>
                        rw [changed] at operation
                        have runtimeEq : next = after :=
                          congrArg Prod.fst (Except.ok.inj operation)
                        subst after
                        exact setCell_runtimeAux changed
                | _ => simp [objectEq] at operation
  | object reference | usize value | scalar value | erased =>
      simp [reuse] at operation

/-- Replace concrete memory after a heap-only source update while retaining
the already-related globals, world token, and external trace. -/
theorem ConcreteRuntimeRel.replaceHeap_of_heapOnly
    {initial : Wasm.Store Host} {heap : MemoryState}
    {witness : RefinementWitness} {before after : RuntimeState}
    (related : ConcreteRuntimeRel initial.host.runtime witness before)
    (heapRelated : LiveHeapRel heap witness after)
    (heapOnly : ∃ semanticHeap, after = { before with heap := semanticHeap }) :
    ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness after := by
  rcases heapOnly with ⟨semanticHeap, rfl⟩
  exact {
    heap := by simpa [replaceHeap, clearFailure] using heapRelated
    globals := by simpa [replaceHeap, clearFailure] using related.globals
    world := by simpa [replaceHeap, clearFailure] using related.world
    trace := by simpa [replaceHeap, clearFailure] using related.trace }

/-- Replace concrete memory after a heap-only source update while transporting
all auxiliary value relations through an arbitrary witness transition. -/
theorem ConcreteRuntimeRel.replaceHeap_of_transport
    {initial : Wasm.Store Host} {heap : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    {before after : RuntimeState}
    (related : ConcreteRuntimeRel initial.host.runtime beforeWitness before)
    (transport : WitnessTransport beforeWitness afterWitness)
    (heapRelated : LiveHeapRel heap afterWitness after)
    (heapOnly : ∃ semanticHeap, after = { before with heap := semanticHeap }) :
    ConcreteRuntimeRel (replaceHeap initial heap).host.runtime afterWitness after := by
  rcases heapOnly with ⟨semanticHeap, rfl⟩
  exact {
    heap := by simpa [replaceHeap, clearFailure] using heapRelated
    globals := by
      simpa [replaceHeap, clearFailure] using
        ConcreteGlobalsRel.witnessTransport transport related.globals
    world := by simpa [replaceHeap, clearFailure] using related.world
    trace := by
      simpa [replaceHeap, clearFailure] using
        ConcreteTraceRel.witnessTransport transport related.trace }

/-- Lift a recursively changed heap while reusing the explicitly framed
semantic runtime components. -/
theorem ConcreteRuntimeRel.replaceHeap_of_runtimeAux
    {initial : Wasm.Store Host} {heap : MemoryState}
    {witness : RefinementWitness} {before after : RuntimeState}
    (related : ConcreteRuntimeRel initial.host.runtime witness before)
    (heapRelated : LiveHeapRel heap witness after)
    (aux : RuntimeAuxEq before after) :
    ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness after := by
  exact {
    heap := by simpa [replaceHeap, clearFailure] using heapRelated
    globals := by
      rw [aux.globals]
      simpa [replaceHeap, clearFailure] using related.globals
    world := by
      rw [aux.world]
      simpa [replaceHeap, clearFailure] using related.world
    trace := by
      rw [aux.trace]
      simpa [replaceHeap, clearFailure] using related.trace }

/-- A successful concrete closure match crosses the same ownership boundary
as source application, records the exact typed capture snapshot used by the
projection prefix, and relates the resulting concrete store to the semantic
post-application runtime. -/
theorem closureMatchesStep_hit_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {function : Lean.Name} {arity : Nat}
    {captures : Array Value} {expectedFunction : Lean.Name}
    {expectedArity expectedFixed : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (identityTrue :
      (function == expectedFunction && arity == expectedArity &&
        captures.size == expectedFixed) = true)
    (sharedCapacity : ∀ parentRuntime,
      setCell runtime location { cell with rc := cell.rc - 1 } =
          .ok parentRuntime →
        ClosureRetainCapacity parentRuntime captures.toList)
    (semanticOperation :
      Fir.LeanIR.Impure.takeClosureApplication runtime location =
        .ok (nextRuntime, function, arity, captures)) :
    ∃ (next : Wasm.Store Host) (application : ClosureApplication)
        (captureKinds : Array AbiKind),
      closureMatchesStep expectedFunction expectedArity expectedFixed initial
          [.i32 (UInt32.ofNat address.value)] =
        .Return [.i32 1] next ∧
      next.host.closureApplication? = some application ∧
      ClosureApplicationRel witness application address function arity
        captureKinds captures ∧
      ConcreteRuntimeRel next.host.runtime witness nextRuntime := by
  obtain ⟨heap, application, captureKinds, concreteOperation,
      applicationRelated, heapRelated⟩ :=
    runtimeRelated.heap.takeClosureApplication_refines mapped found live
      objectEq sharedCapacity semanticOperation
  have concreteMatch := runtimeRelated.heap.closureMatches_refines mapped found
    live objectEq expectedFunction expectedArity expectedFixed
  have concreteOperationInitial :
      Fir.Wasm.Concrete.takeClosureApplication initial.host.runtime.heap
          initial.host.closureDispatch initial.host.closureDescriptors address =
        .ok (heap, application) := by
    simpa [dispatchEq, descriptorsEq] using concreteOperation
  let next : Wasm.Store Host :=
    let store := replaceHeap (clearFailure initial) heap
    { store with host := {
        store.host with closureApplication? := some application } }
  refine ⟨next, application, captureKinds, ?_, ?_, applicationRelated, ?_⟩
  · unfold closureMatchesStep
    simp only [clearFailure]
    rw [Word32.ofUInt32_ofNat_value, ← dispatchEq, ← descriptorsEq,
      concreteMatch]
    simp [identityTrue, concreteOperationInitial, next, replaceHeap,
      clearFailure, dispatchEq, descriptorsEq]
  · simp [next]
  · have runtimeAux := takeClosureApplication_runtimeAux semanticOperation
    have nextRuntimeRelated :=
      FirTalos.Concrete.ConcreteRuntimeRel.replaceHeap_of_runtimeAux
        runtimeRelated heapRelated runtimeAux
    simpa [next, replaceHeap, clearFailure] using nextRuntimeRelated

/-- Lift a recursively changed heap while transporting the auxiliary value
relations through a descriptor rebind. -/
theorem ConcreteRuntimeRel.replaceHeap_of_transportAux
    {initial : Wasm.Store Host} {heap : MemoryState}
    {beforeWitness afterWitness : RefinementWitness}
    {before after : RuntimeState}
    (related : ConcreteRuntimeRel initial.host.runtime beforeWitness before)
    (transport : WitnessTransport beforeWitness afterWitness)
    (heapRelated : LiveHeapRel heap afterWitness after)
    (aux : RuntimeAuxEq before after) :
    ConcreteRuntimeRel (replaceHeap initial heap).host.runtime afterWitness after := by
  exact {
    heap := by simpa [replaceHeap, clearFailure] using heapRelated
    globals := by
      rw [aux.globals]
      simpa [replaceHeap, clearFailure] using
        ConcreteGlobalsRel.witnessTransport transport related.globals
    world := by
      rw [aux.world]
      simpa [replaceHeap, clearFailure] using related.world
    trace := by
      rw [aux.trace]
      simpa [replaceHeap, clearFailure] using
        ConcreteTraceRel.witnessTransport transport related.trace }

/-- Successful concrete reference-count increment refines the exact semantic
operation for both ordinary heap objects and checked tagged/promoted-tag
values. `fits` is the wasm32 header-count side condition for the ordinary
branch and is vacuous for tagged values. Successful increments preserve the
heap frontier as well as every mapped allocation's physical capacity. -/
theorem incrementStep_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {sourceObject : Value}
    {word : Word32} {amount : Nat} {check : Bool}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 word) sourceObject)
    (updated : incValue runtime sourceObject amount check = .ok nextRuntime)
    (fits : ∀ (location : Location) (cell : HeapCell),
      sourceObject = .object (.heap location) →
      findCell? runtime.heap location = some cell →
      cell.rc + amount < UInt32.size) :
    ∃ heap,
      incrementStep amount check initial
          [.i32 (UInt32.ofNat word.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              rename_i location
              obtain ⟨cell, found, _⟩ :=
                runtimeRelated.heap.concreteToSemantic location word mapped
              have live : cell.live = true := by
                by_contra notLive
                have dead : cell.live = false := Bool.eq_false_of_not_eq_true notLive
                have readError : getLiveCell runtime location =
                    .error (.deadObject location) := by
                  simp [getLiveCell, found, dead]
                have impossible := updated
                simp only [incValue] at impossible
                unfold incLocation at impossible
                rw [readError] at impossible
                cases impossible
              have countFits := fits _ cell rfl found
              obtain ⟨heap, semanticAfter, concreteOperation,
                  semanticOperation, finalHeapRelated, cursor, capacity⟩ :=
                runtimeRelated.heap.incrementReference_refines_with_capacity
                  mapped found live amount countFits check
              rw [updated] at semanticOperation
              have afterEq := Except.ok.inj semanticOperation
              subst semanticAfter
              refine ⟨heap, ?_, ?_, cursor, capacity⟩
              · simp [incrementStep, clearFailure,
                  Word32.ofUInt32_ofNat_value, concreteOperation, replaceHeap]
              · exact ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
                  finalHeapRelated (incValue_heapOnly updated)
      | tagged taggedRelated =>
          have concreteOperation :=
            runtimeRelated.heap.incrementReference_tagged taggedRelated amount check
          have checked : check = true := by
            cases check
            · simp [incValue] at updated
            · rfl
          subst check
          have afterEq : nextRuntime = runtime := by
            simpa [incValue] using updated.symm
          subst nextRuntime
          refine ⟨initial.host.runtime.heap, ?_, ?_, rfl,
            .refl initial.host.runtime.heap witness⟩
          · simp [incrementStep, clearFailure,
              Word32.ofUInt32_ofNat_value, concreteOperation, replaceHeap]
          · simpa [replaceHeap, clearFailure] using runtimeRelated

theorem incrementStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {sourceObject : Value}
    {word : Word32} {amount : Nat} {check : Bool}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 word) sourceObject)
    (updated : incValue runtime sourceObject amount check = .ok nextRuntime)
    (fits : ∀ (location : Location) (cell : HeapCell),
      sourceObject = .object (.heap location) →
      findCell? runtime.heap location = some cell →
      cell.rc + amount < UInt32.size) :
    ∃ heap,
      incrementStep amount check initial
          [.i32 (UInt32.ofNat word.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    incrementStep_of_refines_with_capacity runtimeRelated objectRelated updated fits
  exact ⟨heap, concrete, finalRelated⟩

/-- A stale mapped increment reaches the Talos boundary as the exact
source-address dead-object fault before count arithmetic or a header write. -/
theorem incrementStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} {amount : Nat} {check : Bool}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .tobject (.word32 word)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    incrementStep amount check initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject word)))) ∧
      incValue runtime (.object (.heap location)) amount check =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject word)) (.deadObject location) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.incrementReference_deadObject heapRelated found
              dead amount check
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [incrementStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- An unchecked increment of either physical tagged representation preserves
the source `expectedHeapReference` fault through the concrete Talos host. -/
theorem incrementStep_tagged_unchecked_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {payload : UInt64}
    {amount : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .tobject (.word32 word)
      (.object (.tagged payload))) :
    incrementStep amount false initial
        [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.runtime .expectedHeapReference))) ∧
      incValue runtime (.object (.tagged payload)) amount false =
        .error .expectedHeapReference ∧
      ConcreteErrorSourceRel witness
        (.source .expectedHeapReference) .expectedHeapReference := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | tagged taggedRelated =>
          have concrete :=
            runtimeRelated.heap.incrementReference_tagged taggedRelated amount
              false
          refine ⟨?_, rfl, .source .expectedHeapReference⟩
          simp [incrementStep, clearFailure,
            Word32.ofUInt32_ofNat_value, concrete, ConcreteError.toTrap]

/-- Repeating a checked decrement on an immediate or promoted tag remains a
concrete no-op. -/
theorem decrementReference_tagged_checked
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload)
    (amount : Nat) (descriptors : ClosureDescriptorTable := #[]) :
    decrementReference state word amount true descriptors = .ok state := by
  induction amount with
  | zero => rfl
  | succ amount ih =>
      simp only [decrementReference, List.replicate_succ, List.foldlM_cons,
        Bind.bind, Except.bind]
      rw [related.decrementReferenceOnce_tagged tagged true descriptors]
      exact ih

theorem decValue_tagged_checked
    (runtime : RuntimeState) (payload : UInt64) (amount : Nat) :
    decValue runtime (.object (.tagged payload)) amount true = .ok runtime := by
  induction amount with
  | zero => rfl
  | succ amount ih =>
      simp only [decValue, List.replicate_succ, List.foldlM_cons,
        Bind.bind, Except.bind, decValueOnce]
      exact ih

/-- Every positive unchecked decrement of either tagged representation stops
at its first one-step ownership check. -/
theorem decrementReference_tagged_unchecked
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {payload : UInt64} {word : Word32}
    (related : LiveHeapRel state witness runtime)
    (tagged : TaggedReferenceRel witness word payload)
    (amount : Nat) (descriptors : ClosureDescriptorTable := #[]) :
    decrementReference state word (amount + 1) false descriptors =
      .error (.source .expectedHeapReference) := by
  simp only [decrementReference, List.replicate_succ, List.foldlM_cons,
    Bind.bind, Except.bind]
  rw [related.decrementReferenceOnce_tagged tagged false descriptors]
  rfl

/-- FIR selects the same first-step fault for every positive unchecked tagged
decrement. -/
theorem decValue_tagged_unchecked
    (runtime : RuntimeState) (payload : UInt64) (amount : Nat) :
    decValue runtime (.object (.tagged payload)) (amount + 1) false =
      .error .expectedHeapReference := by
  simp only [decValue, List.replicate_succ, List.foldlM_cons, Bind.bind,
    Except.bind, decValueOnce]
  rfl

/-- A positive unchecked tagged decrement crosses the Talos boundary as the
exact source-classified `expectedHeapReference` trap. -/
theorem decrementStep_tagged_unchecked_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {payload : UInt64}
    {amount : Nat} {objectFields? : Option Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .tobject (.word32 word)
      (.object (.tagged payload))) :
    decrementStep (amount + 1) false objectFields? initial
        [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.runtime .expectedHeapReference))) ∧
      decValue runtime (.object (.tagged payload)) (amount + 1) false =
        .error .expectedHeapReference ∧
      ConcreteErrorSourceRel witness
        (.source .expectedHeapReference) .expectedHeapReference := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | tagged taggedRelated =>
          have concrete :=
            decrementReference_tagged_unchecked runtimeRelated.heap taggedRelated
              amount initial.host.closureDescriptors
          refine ⟨?_, decValue_tagged_unchecked runtime payload amount,
            .source .expectedHeapReference⟩
          simp [decrementStep, clearFailure,
            Word32.ofUInt32_ofNat_value, concrete, ConcreteError.toTrap]

/-- Successful concrete decrement refines the exact semantic operation.
Ordinary objects may recursively release ownership trees for either check bit;
tagged and promoted-tag words are checked no-ops, while their only successful
unchecked operation is the amount-zero fold. The descriptor equality exposes
the frozen closure-layout contract needed to release typed captures. -/
theorem decrementStep_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {sourceObject : Value}
    {word : Word32} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 word) sourceObject)
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (updated : decValue runtime sourceObject amount check = .ok nextRuntime) :
    ∃ heap,
      decrementStep amount check objectFields? initial
          [.i32 (UInt32.ofNat word.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨heap, concreteOperation, finalHeapRelated, cursor,
                  capacity⟩ :=
                runtimeRelated.heap.decrementReference_refines_with_capacity
                  mapped check updated
              refine ⟨heap, ?_, ?_, cursor, capacity⟩
              · simp [decrementStep, clearFailure,
                  Word32.ofUInt32_ofNat_value, descriptorsEq,
                  concreteOperation, replaceHeap]
              · exact ConcreteRuntimeRel.replaceHeap_of_runtimeAux
                  runtimeRelated finalHeapRelated (decValue_runtimeAux updated)
      | tagged taggedRelated =>
          cases check with
          | false =>
              cases amount with
              | zero =>
                  have afterEq : nextRuntime = runtime := by
                    simpa [decValue] using (Except.ok.inj updated).symm
                  subst nextRuntime
                  refine ⟨initial.host.runtime.heap, ?_, ?_, rfl,
                    .refl initial.host.runtime.heap witness⟩
                  · simp [decrementStep, decrementReference, clearFailure,
                      Word32.ofUInt32_ofNat_value, replaceHeap, pure,
                      Except.pure]
                  · simpa [replaceHeap, clearFailure] using runtimeRelated
              | succ amount =>
                  simp only [decValue, List.replicate_succ, List.foldlM_cons,
                    Bind.bind, Except.bind, decValueOnce] at updated
                  simp at updated
          | true =>
              have concreteOperation :=
                decrementReference_tagged_checked runtimeRelated.heap taggedRelated
                  amount initial.host.closureDescriptors
              have afterEq : nextRuntime = runtime := by
                rw [decValue_tagged_checked] at updated
                exact (Except.ok.inj updated).symm
              subst nextRuntime
              refine ⟨initial.host.runtime.heap, ?_, ?_, rfl,
                .refl initial.host.runtime.heap witness⟩
              · simp [decrementStep, clearFailure,
                  Word32.ofUInt32_ofNat_value, concreteOperation, replaceHeap]
              · simpa [replaceHeap, clearFailure] using runtimeRelated

theorem decrementStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {sourceObject : Value}
    {word : Word32} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 word) sourceObject)
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (updated : decValue runtime sourceObject amount check = .ok nextRuntime) :
    ∃ heap,
      decrementStep amount check objectFields? initial
          [.i32 (UInt32.ofNat word.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    decrementStep_of_refines_with_capacity runtimeRelated objectRelated
      descriptorsEq updated
  exact ⟨heap, concrete, finalRelated⟩

/-- A positive stale decrement stops at its first released-header read and
preserves the exact source-address fault through the Talos host. -/
theorem decrementStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .tobject (.word32 word)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    decrementStep (amount + 1) check objectFields? initial
        [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject word)))) ∧
      decValue runtime (.object (.heap location)) (amount + 1) check =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject word)) (.deadObject location) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.decrementReference_deadObject heapRelated found
              dead amount check initial.host.closureDescriptors
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [decrementStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- A positive decrement of a mapped live, ordinary, zero-count object
reaches the exact related underflow fault before ownership metadata or
recursive children are inspected. -/
theorem decrementStep_underflow_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .tobject (.word32 word)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (zero : cell.rc = 0) :
    decrementStep (amount + 1) check objectFields? initial
        [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime
            (.source
              (.address (.referenceCountUnderflow word)))) ∧
      decValue runtime (.object (.heap location)) (amount + 1) check =
        .error (.referenceCountUnderflow location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.referenceCountUnderflow word))
        (.referenceCountUnderflow location) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.decrementReference_underflow heapRelated found
              live ordinary zero amount check initial.host.closureDescriptors
          refine ⟨?_, semantic,
            .sourceAddress (.referenceCountUnderflow heapRelated)⟩
          simp [decrementStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- Every admitted mapped-heap decrement fault, including one reached through
recursive constructor or closure release, crosses the Talos host as its exact
source-classified concrete error. Semantic release-fuel exhaustion remains
excluded because the concrete runtime classifies it as a target-safety fault. -/
theorem decrementStep_fault_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {amount : Nat} {check : Bool} {objectFields? : Option Nat}
    {fault : RuntimeFault}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .tobject (.word32 word)
      (.object (.heap location)))
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticFailure :
      decValue runtime (.object (.heap location)) amount check =
        .error fault) :
    ∃ failure,
      decrementStep amount check objectFields? initial
          [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial) (.runtime failure.toTrap) ∧
      ConcreteErrorSourceRel witness failure fault := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨failure, concrete, failureRelated⟩ :=
                runtimeRelated.heap.decrementReference_fault_refines mapped
                  check notFuel semanticFailure
              refine ⟨failure, ?_, failureRelated⟩
              simp [decrementStep, clearFailure,
                Word32.ofUInt32_ofNat_value, descriptorsEq, concrete,
                ConcreteError.toTrap]

/-- A generated mapped-heap decrement cannot cross the Talos host boundary
with the target-only recursive-release fuel trap. -/
theorem decrementStep_ne_releaseFuelExhausted_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {amount : Nat} {check : Bool} {objectFields? : Option Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .tobject (.word32 word)
      (.object (.heap location)))
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors) :
    decrementStep amount check objectFields? initial
        [.i32 (UInt32.ofNat word.value)] ≠
      trap (clearFailure initial)
        (.runtime
          ((.target .releaseFuelExhausted : ConcreteError).toTrap)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              have concreteSafe :=
                runtimeRelated.heap.decrementReference_ne_releaseFuelExhausted
                  (amount := amount) mapped check
              intro targetStep
              cases concreteOperation :
                  decrementReference initial.host.runtime.heap word amount check
                    initial.host.closureDescriptors with
              | ok heap =>
                  simp [decrementStep, clearFailure,
                    Word32.ofUInt32_ofNat_value, concreteOperation, trap]
                    at targetStep
              | error failure =>
                  have failureNotTarget :
                      failure ≠
                        (.target .releaseFuelExhausted : ConcreteError) := by
                    intro failureEq
                    subst failure
                    rw [descriptorsEq] at concreteOperation
                    exact concreteSafe concreteOperation
                  have storedFailureEq := congrArg
                    (fun result =>
                      match result with
                      | .Trap store _ => store.host.failure?
                      | .Return _ _ => none)
                    targetStep
                  have trapEq :
                      failure.toTrap =
                        (.target .releaseFuelExhausted : ConcreteError).toTrap := by
                    simpa [decrementStep, clearFailure,
                      Word32.ofUInt32_ofNat_value, concreteOperation, trap]
                      using storedFailureEq
                  exact failureNotTarget
                    (ConcreteError.toTrap_injective trapEq)

/-- Successful semantic deletion is heap-only for both the ordinary-object
transition and the erased failed-reset no-op. -/
theorem deleteValue_heapOnly
    {before after : RuntimeState} {value : Value}
    (updated : deleteValue before value = .ok after) :
    ∃ heap, after = { before with heap := heap } := by
  cases value with
  | object reference =>
      cases reference with
      | tagged payload => simp [deleteValue] at updated
      | heap location =>
          simp only [deleteValue] at updated
          cases read : getLiveCell before location with
          | error failure =>
              simp only [read, Bind.bind, Except.bind] at updated
              contradiction
          | ok cell =>
              simp only [read, Bind.bind, Except.bind] at updated
              exact setCell_heapOnly updated
  | erased =>
      simp [deleteValue] at updated
      exact ⟨before.heap, by simpa using updated.symm⟩
  | usize value | scalar value | reuseToken value =>
      simp [deleteValue] at updated

/-- Concrete explicit deletion refines every semantically successful physical
lane. This includes the operation-specific erased/zero no-op without creating
an ordinary object relation for zero. -/
theorem deleteStep_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {kind : AbiKind}
    {sourceObject : Value} {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated : ValueRel witness kind (.word32 word) sourceObject)
    (updated : deleteValue runtime sourceObject = .ok nextRuntime) :
    ∃ heap,
      deleteStep initial [.i32 (UInt32.ofNat word.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases valueRelated with
  | object heapRelated =>
      cases heapRelated with
      | mapped mapped =>
          obtain ⟨heap, concreteOperation, finalHeapRelated, capacity, cursor⟩ :=
            runtimeRelated.heap.deleteObject_refines_with_capacity mapped updated
          refine ⟨heap, ?_, ?_, capacity, cursor⟩
          · simp [deleteStep, clearFailure, Word32.ofUInt32_ofNat_value,
              concreteOperation, replaceHeap]
          · exact ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
              finalHeapRelated (deleteValue_heapOnly updated)
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨heap, concreteOperation, finalHeapRelated, capacity,
                  cursor⟩ :=
                runtimeRelated.heap.deleteObject_refines_with_capacity mapped
                  updated
              refine ⟨heap, ?_, ?_, capacity, cursor⟩
              · simp [deleteStep, clearFailure, Word32.ofUInt32_ofNat_value,
                  concreteOperation, replaceHeap]
              · exact ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
                  finalHeapRelated (deleteValue_heapOnly updated)
      | tagged taggedRelated => simp [deleteValue] at updated
  | erased =>
      obtain ⟨heap, concreteOperation, semanticOperation, finalHeapRelated,
          capacity, cursor⟩ :=
        runtimeRelated.heap.deleteObject_erased_refines_with_capacity
      have runtimeEq := Except.ok.inj (semanticOperation.symm.trans updated)
      subst nextRuntime
      refine ⟨heap, ?_, ?_, capacity, cursor⟩
      · simp [deleteStep, clearFailure, Word32.ofUInt32_ofNat_value,
          concreteOperation, replaceHeap]
      · exact ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
          finalHeapRelated (deleteValue_heapOnly updated)
  | tagged taggedRelated => simp [deleteValue] at updated
  | reuseNone => simp [deleteValue] at updated
  | reuseSome heapRelated => simp [deleteValue] at updated
  | uint8 encoded => simp [deleteValue] at updated
  | uint16 encoded => simp [deleteValue] at updated
  | uint32 encoded => simp [deleteValue] at updated

theorem deleteStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {kind : AbiKind}
    {sourceObject : Value} {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated : ValueRel witness kind (.word32 word) sourceObject)
    (updated : deleteValue runtime sourceObject = .ok nextRuntime) :
    ∃ heap,
      deleteStep initial [.i32 (UInt32.ofNat word.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    deleteStep_of_refines_with_capacity runtimeRelated valueRelated updated
  exact ⟨heap, concrete, finalRelated⟩

/-- Repeating explicit deletion on a stale mapped ordinary object preserves
the exact address/location dead-object fault and has no post-state. -/
theorem deleteStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 word)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    deleteStep initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject word)))) ∧
      deleteValue runtime (.object (.heap location)) =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject word)) (.deadObject location) := by
  cases objectRelated with
  | object heapRelated =>
      obtain ⟨concrete, semantic⟩ :=
        runtimeRelated.heap.deleteObject_deadObject heapRelated found dead
      refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
      simp [deleteStep, clearFailure, Word32.ofUInt32_ofNat_value,
        concrete, ConcreteError.toTrap]

/-- Reset of a stale mapped object faults at the common live-header gate and
preserves the exact address/location relation. -/
theorem resetStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} (count : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    resetStep count initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject word)))) ∧
      reset runtime count (.object (.heap location)) =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject word)) (.deadObject location) := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.resetObject_deadObject heapRelated found dead
              count initial.host.closureDescriptors
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [resetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- A related live, ordinary, uniquely owned nonconstructor reaches reset's
constructor-kind gate before bounds or child release and produces the exact
source-classified trap. -/
theorem resetStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} (count : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1)
    (notConstructor : ∀ object, cell.object ≠ .ctor object) :
    resetStep count initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      reset runtime count (.object (.heap location)) =
        .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.resetObject_expectedConstructor_refines
              heapRelated found live ordinary unique notConstructor count
              initial.host.closureDescriptors
          refine ⟨?_, semantic, .source .expectedConstructor⟩
          simp [resetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- A related live, ordinary, uniquely owned constructor with an oversized
reset prefix preserves the exact object-field-bounds fault before mutation or
child release. -/
theorem resetStep_outOfBounds_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} {object : ConstructorObject} (count : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1) (constructor : cell.object = .ctor object)
    (outOfBounds : object.objectFields.size < count) :
    resetStep count initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime
            ((.source
              (.objectFieldOutOfBounds count object.objectFields.size) :
                ConcreteError).toTrap)) ∧
      reset runtime count (.object (.heap location)) =
        .error (.objectFieldOutOfBounds count object.objectFields.size) ∧
      ConcreteErrorSourceRel witness
        (.source (.objectFieldOutOfBounds count object.objectFields.size))
        (.objectFieldOutOfBounds count object.objectFields.size) := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.resetObject_outOfBounds_refines heapRelated
              found live ordinary unique constructor count outOfBounds
              initial.host.closureDescriptors
          refine ⟨?_, semantic,
            .source (.objectFieldOutOfBounds count object.objectFields.size)⟩
          simp [resetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- A unique constructor reset preserves any recursively reached mapped-child
fault through the concrete host boundary. Erased children are exact no-ops;
release-fuel exhaustion remains target-classified. -/
theorem resetStep_unique_fault_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} {object : ConstructorObject} {count : Nat}
    {fault : RuntimeFault}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) (.object (.heap location)))
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (unique : cell.rc = 1) (constructor : cell.object = .ctor object)
    (countFits : count ≤ object.objectFields.size)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticFailure :
      reset runtime count (.object (.heap location)) = .error fault) :
    ∃ failure,
      resetStep count initial [.i32 (UInt32.ofNat word.value)] =
          trap (clearFailure initial) (.runtime failure.toTrap) ∧
        ConcreteErrorSourceRel witness failure fault := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨failure, concrete, failureRelated⟩ :=
                runtimeRelated.heap.resetObject_unique_fault_refines mapped
                  found live ordinary unique constructor countFits notFuel
                  semanticFailure
              refine ⟨failure, ?_, failureRelated⟩
              simp [resetStep, clearFailure, Word32.ofUInt32_ofNat_value,
                descriptorsEq, concrete, ConcreteError.toTrap]

/-- A nonunique reset preserves the exact fault produced by its delegated
public checked decrement. -/
theorem resetStep_nonunique_fault_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell} {count : Nat} {fault : RuntimeFault}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) (.object (.heap location)))
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (notUnique : cell.rc ≠ 1)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticFailure :
      reset runtime count (.object (.heap location)) = .error fault) :
    ∃ failure,
      resetStep count initial [.i32 (UInt32.ofNat word.value)] =
          trap (clearFailure initial) (.runtime failure.toTrap) ∧
        ConcreteErrorSourceRel witness failure fault := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨failure, concrete, failureRelated⟩ :=
                runtimeRelated.heap.resetObject_nonunique_fault_refines mapped
                  found live notUnique notFuel semanticFailure
              refine ⟨failure, ?_, failureRelated⟩
              simp [resetStep, clearFailure, Word32.ofUInt32_ofNat_value,
                descriptorsEq, concrete, ConcreteError.toTrap]

/-- A generated reset of a mapped heap object cannot cross the Talos host
boundary with the target-only recursive-release fuel trap. This statement
covers dead, fallback, constructor-kind, bounds, and in-bounds unique-prefix
branches uniformly. -/
theorem resetStep_ne_releaseFuelExhausted_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {count : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) (.object (.heap location)))
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors) :
    resetStep count initial [.i32 (UInt32.ofNat word.value)] ≠
      trap (clearFailure initial)
        (.runtime
          ((.target .releaseFuelExhausted : ConcreteError).toTrap)) := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              have concreteSafe :=
                runtimeRelated.heap.resetObject_ne_releaseFuelExhausted
                  mapped count
              intro targetStep
              cases concreteOperation :
                  resetObject initial.host.runtime.heap count word
                    initial.host.closureDescriptors with
              | ok result =>
                  simp [resetStep, clearFailure,
                    Word32.ofUInt32_ofNat_value, concreteOperation, trap]
                    at targetStep
              | error failure =>
                  have failureNotTarget :
                      failure ≠
                        (.target .releaseFuelExhausted : ConcreteError) := by
                    intro failureEq
                    subst failure
                    rw [descriptorsEq] at concreteOperation
                    exact concreteSafe concreteOperation
                  have storedFailureEq := congrArg
                    (fun result =>
                      match result with
                      | .Trap store _ => store.host.failure?
                      | .Return _ _ => none)
                    targetStep
                  have trapEq :
                      failure.toTrap =
                        (.target .releaseFuelExhausted : ConcreteError).toTrap := by
                    simpa [resetStep, clearFailure,
                      Word32.ofUInt32_ofNat_value, concreteOperation, trap]
                      using storedFailureEq
                  exact failureNotTarget
                    (ConcreteError.toTrap_injective trapEq)

/-- Tagged reset is an exact heap no-op and returns the empty reuse token. -/
theorem resetStep_tagged_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {payload : UInt64} {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (tagged : TaggedReferenceRel witness word payload) (count : Nat) :
    resetStep count initial [.i32 (UInt32.ofNat word.value)] =
        .Return [.i32 (UInt32.ofNat Word32.zero.value)]
          (replaceHeap initial initial.host.runtime.heap) ∧
      ConcreteRuntimeRel
        (replaceHeap initial initial.host.runtime.heap).host.runtime witness
          runtime ∧
      ValueRel witness .reuseToken (.word32 Word32.zero)
        (.reuseToken none) := by
  obtain ⟨concreteReset, _, tokenRelated⟩ :=
    runtimeRelated.heap.resetObject_refines_tagged tagged count
  refine ⟨?_, ?_, tokenRelated⟩
  · simp [resetStep, clearFailure, Word32.ofUInt32_ofNat_value,
      ← descriptorsEq, concreteReset, replaceHeap]
  · simpa [replaceHeap, clearFailure] using runtimeRelated

/--
A successful persistent-or-nonunique fallback reset follows the same public
decrement path in both runtimes and preserves every mapped allocation extent.
-/
theorem resetStep_fallback_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {count : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell) (live : cell.live = true)
    (fallbackSemantic : cell.persistent = true ∨ cell.rc ≠ 1)
    (updated : reset runtime count (.object (.heap location)) =
      .ok (nextRuntime, .reuseToken none)) :
    ∃ heap,
      resetStep count initial [.i32 (UInt32.ofNat address.value)] =
          .Return [.i32 (UInt32.ofNat Word32.zero.value)]
            (replaceHeap initial heap) ∧
        ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
          nextRuntime ∧
        ValueRel witness .reuseToken (.word32 Word32.zero)
          (.reuseToken none) ∧
        MappedHeaderCapacityTransport initial.host.runtime.heap heap
          witness ∧
        heap.heapCursor =
          initial.host.runtime.heap.heapCursor := by
  have fallbackSource :
      (cell.persistent || cell.rc != 1) = true := by
    rcases fallbackSemantic with semanticPersistent | notUnique
    · simp [semanticPersistent]
    · simp [notUnique]
  have semanticDec : decLocation runtime location = .ok nextRuntime := by
    unfold reset at updated
    simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
      at updated
    rw [if_pos fallbackSource] at updated
    cases decEq : decLocation runtime location with
    | error fault =>
        rw [decEq] at updated
        contradiction
    | ok middleRuntime =>
        rw [decEq] at updated
        have pairEq := Except.ok.inj updated
        have runtimeEq : middleRuntime = nextRuntime := congrArg Prod.fst pairEq
        subst middleRuntime
        rfl
  obtain ⟨heap, concreteReset, heapRelated, tokenRelated,
      capacityTransport⟩ :=
    runtimeRelated.heap.resetObject_refines_fallback_with_capacity mapped found
      live fallbackSemantic updated
  refine ⟨heap, ?_, ?_, tokenRelated, capacityTransport,
    resetObject_preserves_heapCursor concreteReset⟩
  · simp [resetStep, clearFailure, Word32.ofUInt32_ofNat_value,
      ← descriptorsEq, concreteReset, replaceHeap]
  · exact FirTalos.Concrete.ConcreteRuntimeRel.replaceHeap_of_runtimeAux
      runtimeRelated heapRelated (decLocation_runtimeAux semanticDec)

/-- A nonunique mapped heap object follows reset's decrement-and-empty-token
path in both runtimes while preserving the physical extent of every mapped
header. -/
theorem resetStep_nonunique_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {count : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
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
        ValueRel witness .reuseToken (.word32 Word32.zero)
          (.reuseToken none) ∧
        MappedHeaderCapacityTransport initial.host.runtime.heap heap
          witness := by
  obtain ⟨heap, operation, nextRelated, tokenRelated, capacity, _cursor⟩ :=
    resetStep_fallback_of_refines_with_capacity runtimeRelated descriptorsEq
      mapped found live (.inr notUnique) updated
  exact ⟨heap, operation, nextRelated, tokenRelated, capacity⟩

/-- Compatibility surface for clients that need only runtime and value
refinement from the nonunique reset branch. -/
theorem resetStep_nonunique_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {count : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
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
        ValueRel witness .reuseToken (.word32 Word32.zero)
          (.reuseToken none) := by
  obtain ⟨heap, concreteReset, finalRelated, tokenRelated, _⟩ :=
    resetStep_nonunique_of_refines_with_capacity runtimeRelated descriptorsEq
      mapped found live notUnique updated
  exact ⟨heap, concreteReset, finalRelated, tokenRelated⟩

/-- A unique ordinary constructor reset returns a nonempty token, rebinds the
active descriptor to the reset protocol, and transports every auxiliary
runtime value through that exact witness transition. -/
theorem resetStep_unique_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {address : Word32} {cell : HeapCell} {object : ConstructorObject}
    {count : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
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
        ValueRel nextWitness .reuseToken (.word32 address)
          (.reuseToken (some location)) ∧
        ResetReuseProtocolRel initial.host.runtime.heap heap witness runtime
          nextRuntime location address cell object count ∧
        MappedHeaderCapacityTransport initial.host.runtime.heap heap
          witness := by
  let replacement : HeapCell :=
    { cell with object := .ctor (resetProtocolObject object count) }
  obtain ⟨middleRuntime, semanticSet, _, _, _, _⟩ :=
    Fir.LeanIR.Impure.setCell_spec_of_find runtime location cell replacement found
  have semanticFold :
      (object.objectFields.extract 0 count).foldlM
          (fun next value => releaseResetField next value) middleRuntime =
        .ok nextRuntime := by
    unfold reset at updated
    simp only [getLiveCell, found, live, ↓reduceIte, Bind.bind, Except.bind]
      at updated
    rw [if_neg (by simp [ordinary, unique])] at updated
    rw [constructor] at updated
    simp only at updated
    rw [if_neg (Nat.not_lt.mpr countFits)] at updated
    have updated' : (do
        let next ← setCell runtime location replacement
        let next ← (object.objectFields.extract 0 count).foldlM
          (fun next value => releaseResetField next value) next
        return (next, Value.reuseToken (some location))) =
          .ok (nextRuntime, Value.reuseToken (some location)) := by
      simpa only [replacement, resetProtocolObject, live, Bind.bind, Except.bind]
        using updated
    rw [semanticSet] at updated'
    simp only [Bind.bind, Except.bind] at updated'
    cases foldEq : (object.objectFields.extract 0 count).foldlM
        (fun next value => releaseResetField next value) middleRuntime with
    | error fault =>
        rw [foldEq] at updated'
        contradiction
    | ok finalRuntime =>
        rw [foldEq] at updated'
        have pairEq := Except.ok.inj updated'
        have runtimeEq : finalRuntime = nextRuntime := congrArg Prod.fst pairEq
        subst finalRuntime
        rfl
  have aux : RuntimeAuxEq runtime nextRuntime :=
    (setCell_runtimeAux semanticSet).trans
      (Array.foldlM_runtimeAux
        (fun operation => releaseResetField_runtimeAux operation) semanticFold)
  obtain ⟨heap, info, fieldKinds, concreteReset, heapRelated, protocol,
      tokenRelated, capacity⟩ :=
    runtimeRelated.heap.resetObject_refines_unique mapped found live ordinary
      unique constructor countFits updated
  let nextWitness :=
    witness.rebindConstructor address info
      (resetProtocolFieldKinds fieldKinds count)
  have transport : WitnessTransport witness nextWitness :=
    WitnessTransport.rebindConstructor witness address info
      (resetProtocolFieldKinds fieldKinds count)
  have nextRelated : ConcreteRuntimeRel
      (replaceHeap initial heap).host.runtime nextWitness nextRuntime :=
    FirTalos.Concrete.ConcreteRuntimeRel.replaceHeap_of_transportAux
      runtimeRelated transport heapRelated aux
  refine ⟨heap, info, fieldKinds, ?_, transport, nextRelated, tokenRelated,
    protocol, capacity⟩
  simp [resetStep, clearFailure, Word32.ofUInt32_ofNat_value,
    ← descriptorsEq, concreteReset, replaceHeap]

/--
Every successful semantic reset of a represented `tobject` is implemented by
the concrete reset host, independently of the tagged, fallback, or unique
constructor branch selected at runtime.

The theorem derives branch facts from the successful source operation and
returns only the ordinary witness transport, value relation, mapped-header
transport, and exact frontier preservation needed by compiler composition.
-/
theorem resetStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {sourceObject sourceToken : Value}
    {word : Word32} {count : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (objectRelated :
      ValueRel witness .tobject (.word32 word) sourceObject)
    (updated :
      reset runtime count sourceObject = .ok (nextRuntime, sourceToken)) :
    ∃ heap nextWitness token,
      resetStep count initial [.i32 (UInt32.ofNat word.value)] =
          .Return [.i32 (UInt32.ofNat token.value)]
            (replaceHeap initial heap) ∧
        WitnessTransport witness nextWitness ∧
        ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
          nextRuntime ∧
        ValueRel nextWitness .reuseToken (.word32 token) sourceToken ∧
        nextWitness.closureDescriptors = witness.closureDescriptors ∧
        MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
        heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | tagged taggedRelated =>
          have pairEq :
              (runtime, .reuseToken none) = (nextRuntime, sourceToken) := by
            simpa [reset] using updated
          have runtimeEq : runtime = nextRuntime := congrArg Prod.fst pairEq
          have tokenEq : Value.reuseToken none = sourceToken :=
            congrArg Prod.snd pairEq
          subst nextRuntime
          subst sourceToken
          obtain ⟨operation, nextRelated, tokenRelated⟩ :=
            resetStep_tagged_of_refines runtimeRelated descriptorsEq
              taggedRelated count
          exact ⟨initial.host.runtime.heap, witness, Word32.zero, operation,
            WitnessTransport.refl witness, nextRelated, tokenRelated,
            rfl, MappedHeaderCapacityTransport.refl _ _, rfl⟩
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              rename_i location
              obtain ⟨cell, found, _cellRelated⟩ :=
                runtimeRelated.heap.concreteToSemantic location word mapped
              have live : cell.live = true := by
                by_contra notLive
                have dead : cell.live = false :=
                  Bool.eq_false_of_not_eq_true notLive
                have liveError :
                    getLiveCell runtime location =
                      .error (.deadObject location) := by
                  simp [getLiveCell, found, dead]
                have impossible := updated
                simp [reset, getLiveCell, found, dead] at impossible
                contradiction
              have liveGet : getLiveCell runtime location = .ok cell := by
                simp [getLiveCell, found, live]
              by_cases fallback : cell.persistent || cell.rc != 1
              · have fallbackSemantic :
                    cell.persistent = true ∨ cell.rc ≠ 1 := by
                  simpa using fallback
                have analyzed := updated
                simp only [reset, getLiveCell, found, live, ↓reduceIte,
                  Bind.bind, Except.bind] at analyzed
                rw [if_pos fallback] at analyzed
                cases decEq : decLocation runtime location with
                | error fault =>
                    rw [decEq] at analyzed
                    contradiction
                | ok middleRuntime =>
                    rw [decEq] at analyzed
                    have pairEq := Except.ok.inj analyzed
                    have runtimeEq : middleRuntime = nextRuntime :=
                      congrArg Prod.fst pairEq
                    have tokenEq : Value.reuseToken none = sourceToken :=
                      congrArg Prod.snd pairEq
                    subst nextRuntime
                    subst sourceToken
                    obtain ⟨heap, operation, nextRelated, tokenRelated,
                        capacity, cursor⟩ :=
                      resetStep_fallback_of_refines_with_capacity
                        runtimeRelated descriptorsEq mapped found live
                        fallbackSemantic updated
                    exact ⟨heap, witness, Word32.zero, operation,
                      WitnessTransport.refl witness, nextRelated, tokenRelated,
                      rfl, capacity, cursor⟩
              · have ordinary : cell.persistent = false := by
                  cases persistentEq : cell.persistent with
                  | false => rfl
                  | true => exact False.elim (fallback (by
                      simp [persistentEq]))
                have unique : cell.rc = 1 := by
                  by_contra notUnique
                  exact fallback (by simp [notUnique])
                cases objectEq : cell.object with
                | ctor object =>
                    by_cases countFits : count ≤ object.objectFields.size
                    · let replacement : HeapCell :=
                        { object := .ctor (resetProtocolObject object count)
                          rc := cell.rc
                          persistent := cell.persistent }
                      obtain ⟨middleRuntime, semanticSet, _, _, _, _⟩ :=
                        Fir.LeanIR.Impure.setCell_spec_of_find runtime location
                          cell replacement found
                      have analyzed := updated
                      simp only [reset, getLiveCell, found, live, ↓reduceIte,
                        Bind.bind, Except.bind] at analyzed
                      rw [if_neg fallback, objectEq] at analyzed
                      simp only at analyzed
                      rw [if_neg (Nat.not_lt.mpr countFits)] at analyzed
                      change (do
                          let next ← setCell runtime location replacement
                          let next ←
                            (object.objectFields.extract 0 count).foldlM
                              (fun next value =>
                                releaseResetField next value) next
                          pure
                            (next, Value.reuseToken (some location))) =
                            .ok (nextRuntime, sourceToken) at analyzed
                      rw [semanticSet] at analyzed
                      simp only [Bind.bind, Except.bind] at analyzed
                      cases foldEq :
                          (object.objectFields.extract 0 count).foldlM
                            (fun next value => releaseResetField next value)
                            middleRuntime with
                      | error fault =>
                          rw [foldEq] at analyzed
                          contradiction
                      | ok finalRuntime =>
                          rw [foldEq] at analyzed
                          have pairEq := Except.ok.inj analyzed
                          have runtimeEq : finalRuntime = nextRuntime :=
                            congrArg Prod.fst pairEq
                          have tokenEq :
                              Value.reuseToken (some location) = sourceToken :=
                            congrArg Prod.snd pairEq
                          subst nextRuntime
                          subst sourceToken
                          obtain ⟨heap, info, fieldKinds, operation, transport,
                              nextRelated, tokenRelated, protocol, capacity⟩ :=
                            resetStep_unique_of_refines runtimeRelated
                              descriptorsEq mapped found live ordinary unique
                              objectEq countFits updated
                          let nextWitness :=
                            witness.rebindConstructor word info
                              (resetProtocolFieldKinds fieldKinds count)
                          exact ⟨heap, nextWitness, word, operation, transport,
                            nextRelated, tokenRelated, by
                              simp [nextWitness,
                                RefinementWitness.rebindConstructor],
                            capacity,
                            resetObject_preserves_heapCursor
                              protocol.concreteReset⟩
                    · have impossible := updated
                      simp only [reset, getLiveCell, found, live, ↓reduceIte,
                        Bind.bind, Except.bind] at impossible
                      rw [if_neg fallback, objectEq] at impossible
                      simp only at impossible
                      rw [if_pos (Nat.lt_of_not_ge countFits)] at impossible
                      simp at impossible
                | boxed type value =>
                    have impossible := updated
                    simp only [reset, getLiveCell, found, live, ↓reduceIte,
                      Bind.bind, Except.bind] at impossible
                    rw [if_neg fallback, objectEq] at impossible
                    contradiction
                | natural value =>
                    have impossible := updated
                    simp only [reset, getLiveCell, found, live, ↓reduceIte,
                      Bind.bind, Except.bind] at impossible
                    rw [if_neg fallback, objectEq] at impossible
                    contradiction
                | integer value =>
                    have impossible := updated
                    simp only [reset, getLiveCell, found, live, ↓reduceIte,
                      Bind.bind, Except.bind] at impossible
                    rw [if_neg fallback, objectEq] at impossible
                    contradiction
                | string value =>
                    have impossible := updated
                    simp only [reset, getLiveCell, found, live, ↓reduceIte,
                      Bind.bind, Except.bind] at impossible
                    rw [if_neg fallback, objectEq] at impossible
                    contradiction
                | byteArray value =>
                    have impossible := updated
                    simp only [reset, getLiveCell, found, live, ↓reduceIte,
                      Bind.bind, Except.bind] at impossible
                    rw [if_neg fallback, objectEq] at impossible
                    contradiction
                | closure function arity fixed =>
                    have impossible := updated
                    simp only [reset, getLiveCell, found, live, ↓reduceIte,
                      Bind.bind, Except.bind] at impossible
                    rw [if_neg fallback, objectEq] at impossible
                    contradiction
                | «opaque» typeName =>
                    have impossible := updated
                    simp only [reset, getLiveCell, found, live, ↓reduceIte,
                      Bind.bind, Except.bind] at impossible
                    rw [if_neg fallback, objectEq] at impossible
                    contradiction

/-- A stale nonempty reuse token preserves the exact address/location
dead-object fault after host argument decoding and the aligned arity gate. -/
theorem reuseStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (address, fields))
    (tokenRelated :
      ValueRel witness .reuseToken (.word32 address)
        (.reuseToken (some location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size) :
    reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject address)))) ∧
      reuse runtime (.reuseToken (some location)) info updateHeader
          semanticFields =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject address)) (.deadObject location) := by
  cases tokenRelated with
  | reuseSome heapRelated =>
      obtain ⟨concrete, semantic⟩ :=
        runtimeRelated.heap.reuseObject_deadObject heapRelated found dead info
          updateHeader fields.toArray semanticFields arity semanticArity
      refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
      simp [reuseStep, argsLength, decoded, concrete, clearFailure,
        ConcreteError.toTrap]

/-- A live nonconstructor behind a nonempty reuse token produces the exact
source-classified fault before retained-capacity checks or any heap write. -/
theorem reuseStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (address, fields))
    (tokenRelated :
      ValueRel witness .reuseToken (.word32 address)
        (.reuseToken (some location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (notConstructor : ∀ object, cell.object ≠ .ctor object)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size) :
    reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      reuse runtime (.reuseToken (some location)) info updateHeader
          semanticFields =
        .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  cases tokenRelated with
  | reuseSome heapRelated =>
      obtain ⟨concrete, semantic⟩ :=
        runtimeRelated.heap.reuseObject_expectedConstructor_refines
          heapRelated found live notConstructor info updateHeader fields.toArray
          semanticFields arity semanticArity
      refine ⟨?_, semantic, .source .expectedConstructor⟩
      simp [reuseStep, argsLength, decoded, concrete, clearFailure,
        ConcreteError.toTrap]

/-- Empty-token reuse of an empty constructor follows the tagged allocation
path. The returned immediate or promoted word is widened only as permitted by
the compiler-selected constructor result kind. -/
theorem reuseStep_none_empty_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
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
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat word.value))
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      reuse runtime (.reuseToken none) info updateHeader semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  have allocated : allocateConstructor initial.host.runtime.heap info
      fields.toArray = .ok (heap, word) := by
    unfold reuseObject at reused
    rw [if_pos (by decide)] at reused
    exact reused
  obtain ⟨nextWitness, extension, nextRuntimeRelated, exactRelated,
      semanticAllocation⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorEmpty runtimeRelated
      arity semanticArity empty tagFits allocated
  have valueRelated := taggedConstructorResult_of_refines empty resultRefines
    exactRelated
  refine ⟨nextWitness, extension, ?_, ?_, .word32 valueRelated, ?_⟩
  · simp [reuseStep, argsLength, decoded, reused, replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated
  · simpa [reuse] using semanticAllocation

/-- Empty-token reuse of an empty constructor additionally preserves every
previously mapped allocation's retained capacity. -/
theorem reuseStep_none_empty_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
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
      reuse runtime (.reuseToken none) info updateHeader semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness := by
  have allocated : allocateConstructor initial.host.runtime.heap info
      fields.toArray = .ok (heap, word) := by
    unfold reuseObject at reused
    rw [if_pos (by decide)] at reused
    exact reused
  obtain ⟨nextWitness, extension, nextRuntimeRelated, exactRelated,
      semanticAllocation, capacityTransport⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorEmpty_with_capacity
      runtimeRelated arity semanticArity empty tagFits allocated
  have valueRelated := taggedConstructorResult_of_refines empty resultRefines
    exactRelated
  refine ⟨nextWitness, extension, ?_, ?_, valueRelated, .word32 valueRelated, ?_,
    capacityTransport⟩
  · simp [reuseStep, argsLength, decoded, reused, replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated
  · simpa [reuse] using semanticAllocation

/-- Empty-token reuse of a nonempty constructor is ordinary fresh allocation
and extends the witness with the new address and constructor descriptor. -/
theorem reuseStep_none_nonempty_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
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
    (reused : reuseObject initial.host.runtime.heap Word32.zero info
      updateHeader fields.toArray = .ok (heap, address)) :
    let nextWitness := witness.bindConstructor runtime.nextLocation address info
      fieldKinds
    witness.Extends nextWitness ∧
      reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value))
        (.object (.heap runtime.nextLocation)) ∧
      reuse runtime (.reuseToken none) info updateHeader semanticFields =
        .ok (semanticConstructorResult runtime info semanticFields,
          .object (.heap runtime.nextLocation)) := by
  dsimp only
  have allocated : allocateConstructor initial.host.runtime.heap info
      fields.toArray = .ok (heap, address) := by
    unfold reuseObject at reused
    rw [if_pos (by decide)] at reused
    exact reused
  obtain ⟨extension, nextRuntimeRelated, exactRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorNonempty
      runtimeRelated arity semanticArity fieldKindsSize fieldKindsValid
      fieldRelated nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit allocated
  have valueRelated := objectConstructorResult_of_refines nonempty resultRefines
    exactRelated
  refine ⟨extension, ?_, ?_, .word32 valueRelated, ?_⟩
  · simp [reuseStep, argsLength, decoded, reused, replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated
  · simpa [reuse] using
      allocCtor_nonempty_eq runtime info semanticFields semanticArity nonempty

/-- A nonempty token consumes the reset protocol and restores an ordinary
constructor descriptor at the same semantic/physical location. -/
theorem reuseStep_some_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {oldInfo : Lean.Compiler.LCNF.CtorInfo}
    {oldFieldKinds : Array AbiKind} {old : ConstructorObject}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {resultKind : AbiKind} {fields : List Word32}
    {semanticFields : Array Value} {updateHeader : Bool}
    {physicalArgs : List Wasm.Value} {header : Header}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (address, fields))
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
    (layoutFits : (ConstructorLayout.ofInfo info).allocationBytes ≤
      header.allocationBytes.toNat)
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
      heap.heapCursor = initial.host.runtime.heap.heapCursor ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      reuse runtime (.reuseToken (some location)) info updateHeader
          semanticFields = .ok (nextRuntime, .object (.heap location)) := by
  obtain ⟨heap, nextRuntime, concreteReuse, semanticReuse, heapRelated,
      exactRelated, capacityTransport⟩ :=
    Fir.Wasm.Concrete.LiveHeapRel.reuseObject_some_refines
      initial.host.runtime.heap witness runtime location address cell oldInfo
      oldFieldKinds old info fieldKinds fields.toArray semanticFields
      updateHeader header runtimeRelated.heap mapped found descriptor objectEq
      objectRelated headerRead headerKind refCount persistent ordinary cellLive
      layoutFits arity semanticArity fieldKindsSize fieldKindsValid fieldRelated
      tagFits objectFieldsFit usizeFieldsFit scalarBytesFit
  let nextWitness := witness.rebindConstructor address info fieldKinds
  have transport : WitnessTransport witness nextWitness :=
    WitnessTransport.rebindConstructor witness address info fieldKinds
  have nextRuntimeRelated : ConcreteRuntimeRel
      (replaceHeap initial heap).host.runtime nextWitness nextRuntime :=
    ConcreteRuntimeRel.replaceHeap_of_transportAux runtimeRelated transport
      heapRelated (reuse_runtimeAux semanticReuse)
  have valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat address.value)) (.object (.heap location)) := by
    rcases resultKindSupported with rfl | rfl
    · exact .word32 exactRelated
    · exact .word32 exactRelated.object_to_tobject
  obtain ⟨addressHeap, _, _, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts
      initial.host.runtime.heap address header headerRead
  have addressValueNeZero : address.value ≠ 0 := by
    intro equal
    have sentinel : address.classify = .sentinel := by
      simp [Word32.classify, equal]
    rw [sentinel] at addressHeap
    contradiction
  have addressZeroCheck : (address == Word32.zero) = false := by
    change (address.value == 0) = false
    simp [addressValueNeZero]
  have cursor :
      heap.heapCursor = initial.host.runtime.heap.heapCursor :=
    reuseObject_nonzero_preserves_heapCursor addressZeroCheck concreteReuse
  refine ⟨heap, nextRuntime, ?_, transport, nextRuntimeRelated, valueRelated,
    cursor, capacityTransport, semanticReuse⟩
  simp [reuseStep, argsLength, decoded, concreteReuse, replaceHeap, clearFailure]

/-- Constructor-tag mutation crosses the common checked-header gate before
encoding the replacement tag or writing the header. A related heap object
rejected by FIR as a nonconstructor therefore produces the exact same source
fault at the Talos boundary. -/
theorem setTagStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {location : Location}
    (tag : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (constructorFailed :
      getConstructor runtime (.object (.heap location)) =
        .error .expectedConstructor) :
    setTagStep tag initial [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      setTag runtime (.object (.heap location)) tag =
        .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  have headerFailed :=
    runtimeRelated.heap.readConstructorHeader_expectedConstructor_refines
      objectRelated.object_to_tobject constructorFailed
  have writeFailed :
      writeTag initial.host.runtime.heap objectWord tag =
        .error (.source .expectedConstructor) := by
    unfold writeTag
    rw [headerFailed]
    rfl
  refine ⟨?_, ?_, .source .expectedConstructor⟩
  · simp [setTagStep, clearFailure, Word32.ofUInt32_ofNat_value,
      writeFailed, ConcreteError.toTrap]
  · unfold setTag modifyConstructor
    rw [constructorFailed]
    rfl

/-- Object-slot mutation rejects a nonconstructor at the common header gate,
before bounds, padding, old-field decoding, or the payload write. -/
theorem objectSetStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord fieldWord : Word32}
    {location : Location} {fieldKind : AbiKind} {field : Value}
    (index : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (constructorFailed :
      getConstructor runtime (.object (.heap location)) =
        .error .expectedConstructor) :
    objectSetStep index fieldKind initial
        [.i32 (UInt32.ofNat objectWord.value),
          .i32 (UInt32.ofNat fieldWord.value)] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      setObjectField runtime (.object (.heap location)) index field =
        .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  have headerFailed :=
    runtimeRelated.heap.readConstructorHeader_expectedConstructor_refines
      objectRelated.object_to_tobject constructorFailed
  have readFailed :
      readObjectField initial.host.runtime.heap objectWord index =
        .error (.source .expectedConstructor) := by
    unfold readObjectField
    rw [headerFailed]
    rfl
  have writeFailed :
      writeObjectField initial.host.runtime.heap objectWord index fieldWord =
        .error (.source .expectedConstructor) := by
    unfold writeObjectField
    rw [readFailed]
    rfl
  refine ⟨?_, ?_, .source .expectedConstructor⟩
  · simp [objectSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
      writeFailed, ConcreteError.toTrap]
  · unfold setObjectField modifyConstructor
    rw [constructorFailed]
    rfl

/-- Absolute-slot `USize` mutation reaches the same constructor gate before
slot arithmetic or a memory write. -/
theorem usizeSetStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {field : UInt64}
    {location : Location}
    (index : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (constructorFailed :
      getConstructor runtime (.object (.heap location)) =
        .error .expectedConstructor) :
    usizeSetStep index initial
        [.i32 (UInt32.ofNat objectWord.value), .i64 field] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      setUSizeSlot runtime (.object (.heap location)) index (.usize field) =
        .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  have headerFailed :=
    runtimeRelated.heap.readConstructorHeader_expectedConstructor_refines
      objectRelated.object_to_tobject constructorFailed
  have writeFailed :
      writeUSizeSlot initial.host.runtime.heap objectWord index field =
        .error (.source .expectedConstructor) := by
    unfold writeUSizeSlot
    rw [headerFailed]
    rfl
  refine ⟨?_, ?_, .source .expectedConstructor⟩
  · simp [usizeSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
      writeFailed, ConcreteError.toTrap]
  · unfold setUSizeSlot
    unfold modifyConstructor
    rw [constructorFailed]
    rfl

/-- One kind-indexed theorem covers the four supported packed-integer
mutations. Each concrete writer and FIR's semantic mutation fail at the common
constructor gate before coordinate validation or a payload write. -/
theorem scalarSetStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32}
    {location : Location} {slotIndex byteOffset : Nat}
    {physicalField : Wasm.Value} {field : ScalarValue}
    {fieldKind : AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (fieldRelated :
      PhysicalValueRel witness fieldKind physicalField (.scalar field))
    (constructorFailed :
      getConstructor runtime (.object (.heap location)) =
        .error .expectedConstructor) :
    scalarSetStep slotIndex byteOffset fieldKind initial
        [.i32 (UInt32.ofNat objectWord.value), physicalField] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      setScalarField runtime (.object (.heap location)) slotIndex byteOffset
          (.scalar field) = .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  have headerFailed :=
    runtimeRelated.heap.readConstructorHeader_expectedConstructor_refines
      objectRelated.object_to_tobject constructorFailed
  have semanticFailure :
      setScalarField runtime (.object (.heap location)) slotIndex byteOffset
          (.scalar field) = .error .expectedConstructor := by
    unfold setScalarField
    unfold modifyConstructor
    rw [constructorFailed]
    rfl
  cases fieldRelated with
  | word32 fieldRelated =>
      cases fieldRelated with
      | uint8 encoded =>
          rename_i fieldWord fieldValue
          have writeFailed :
              writeScalarUInt8Field initial.host.runtime.heap objectWord
                  slotIndex byteOffset (UInt8.ofNat fieldWord.value) =
                .error (.source .expectedConstructor) := by
            unfold writeScalarUInt8Field
            rw [headerFailed]
            rfl
          refine ⟨?_, semanticFailure, .source .expectedConstructor⟩
          simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            writeFailed, ConcreteError.toTrap]
      | uint16 encoded =>
          rename_i fieldWord fieldValue
          have writeFailed :
              writeScalarUInt16Field initial.host.runtime.heap objectWord
                  slotIndex byteOffset (UInt16.ofNat fieldWord.value) =
                .error (.source .expectedConstructor) := by
            unfold writeScalarUInt16Field
            rw [headerFailed]
            rfl
          refine ⟨?_, semanticFailure, .source .expectedConstructor⟩
          simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            writeFailed, ConcreteError.toTrap]
      | uint32 encoded =>
          rename_i fieldWord fieldValue
          have writeFailed :
              writeScalarUInt32Field initial.host.runtime.heap objectWord
                  slotIndex byteOffset (UInt32.ofNat fieldWord.value) =
                .error (.source .expectedConstructor) := by
            unfold writeScalarUInt32Field
            rw [headerFailed]
            rfl
          refine ⟨?_, semanticFailure, .source .expectedConstructor⟩
          simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            writeFailed, ConcreteError.toTrap]
  | word64 fieldRelated =>
      cases fieldRelated with
      | uint64 =>
          rename_i fieldValue
          have writeFailed :
              writeScalarUInt64Field initial.host.runtime.heap objectWord
                  slotIndex byteOffset fieldValue =
                .error (.source .expectedConstructor) := by
            unfold writeScalarUInt64Field
            rw [headerFailed]
            rfl
          refine ⟨?_, semanticFailure, .source .expectedConstructor⟩
          simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            writeFailed, ConcreteError.toTrap]
  | float32Bits fieldRelated => cases fieldRelated
  | float64Bits fieldRelated => cases fieldRelated

/-- Every successful semantic constructor modification is heap-only. This is
shared by tag, object, USize, and packed-scalar mutation composition. -/
theorem modifyConstructor_heapOnly
    {before after : RuntimeState} {value : Value}
    {modify : ConstructorObject → Except RuntimeFault ConstructorObject}
    (updated : modifyConstructor before value modify = .ok after) :
    ∃ heap, after = { before with heap := heap } := by
  unfold modifyConstructor at updated
  cases read : getConstructor before value with
  | error failure =>
      simp only [read, Bind.bind, Except.bind] at updated
      cases updated
  | ok result =>
      rcases result with ⟨location, cell, object⟩
      simp only [read, Bind.bind, Except.bind] at updated
      cases changed : modify object with
      | error failure =>
          simp only [changed] at updated
          cases updated
      | ok nextObject =>
          simp only [changed] at updated
          exact setCell_heapOnly updated

/-- Constructor payload mutation preserves globals, world, and external trace. -/
theorem modifyConstructor_runtimeAux
    {before after : RuntimeState} {value : Value}
    {modify : ConstructorObject → Except RuntimeFault ConstructorObject}
    (updated : modifyConstructor before value modify = .ok after) :
    RuntimeAuxEq before after := by
  rcases modifyConstructor_heapOnly updated with ⟨heap, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

/-- Object-field mutation preserves every nonheap semantic runtime component. -/
theorem setObjectField_runtimeAux
    {before after : RuntimeState} {value field : Value} {index : Nat}
    (updated : setObjectField before value index field = .ok after) :
    RuntimeAuxEq before after := by
  unfold setObjectField at updated
  exact modifyConstructor_runtimeAux updated

/-- Constructor-tag mutation preserves every nonheap semantic runtime component. -/
theorem setTag_runtimeAux
    {before after : RuntimeState} {value : Value} {tag : Nat}
    (updated : setTag before value tag = .ok after) :
    RuntimeAuxEq before after := by
  unfold setTag at updated
  exact modifyConstructor_runtimeAux updated

/-- `USize`-slot mutation preserves every nonheap semantic runtime component. -/
theorem setUSizeSlot_runtimeAux
    {before after : RuntimeState} {value : Value}
    {slot : Nat} {field : UInt64}
    (updated :
      setUSizeSlot before value slot (.usize field) = .ok after) :
    RuntimeAuxEq before after := by
  unfold setUSizeSlot at updated
  exact modifyConstructor_runtimeAux updated

/-- Packed-scalar mutation preserves every nonheap semantic runtime component. -/
theorem setScalarField_runtimeAux
    {before after : RuntimeState} {value : Value}
    {width offset : Nat} {field : ScalarValue}
    (updated :
      setScalarField before value width offset (.scalar field) = .ok after) :
    RuntimeAuxEq before after := by
  unfold setScalarField at updated
  exact modifyConstructor_runtimeAux updated

/-- Successful concrete constructor-tag mutation refines the semantic heap
update and preserves all nonheap runtime components. -/
theorem setTagStep_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {word : Word32} {tag : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 word)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (updated : setTag runtime (.object (.heap location)) tag = .ok nextRuntime)
    (tagFits : tag < UInt32.size) :
    ∃ heap,
      setTagStep tag initial [.i32 (UInt32.ofNat word.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases objectRelated with
  | object heapRelated =>
      cases heapRelated with
      | mapped mapped =>
          obtain ⟨heap, semanticAfter, concreteOperation,
              semanticOperation, finalHeapRelated, capacity, cursor⟩ :=
            runtimeRelated.heap.writeTag_refines_with_capacity mapped found live
              objectEq tag tagFits
          rw [updated] at semanticOperation
          have afterEq := Except.ok.inj semanticOperation
          subst semanticAfter
          refine ⟨heap, ?_, ?_, capacity, cursor⟩
          · simp [setTagStep, clearFailure, Word32.ofUInt32_ofNat_value,
              concreteOperation, replaceHeap]
          · apply ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
              finalHeapRelated
            apply modifyConstructor_heapOnly
            simpa [setTag] using updated

theorem setTagStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {word : Word32} {tag : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 word)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (updated : setTag runtime (.object (.heap location)) tag = .ok nextRuntime)
    (tagFits : tag < UInt32.size) :
    ∃ heap,
      setTagStep tag initial [.i32 (UInt32.ofNat word.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    setTagStep_of_refines_with_capacity runtimeRelated objectRelated found live
      objectEq updated tagFits
  exact ⟨heap, concrete, finalRelated⟩

/-- Stale tag mutation preserves the exact mapped dead-object fault and has no
successor heap. -/
theorem setTagStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32}
    {location : Location} {cell : HeapCell} (tag : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    setTagStep tag initial [.i32 (UInt32.ofNat objectWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      setTag runtime (.object (.heap location)) tag =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases objectRelated with
  | object heapRelated =>
      obtain ⟨concrete, semantic⟩ :=
        runtimeRelated.heap.writeTag_deadObject heapRelated found dead tag
      refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
      simp [setTagStep, clearFailure, Word32.ofUInt32_ofNat_value,
        concrete, ConcreteError.toTrap]

/-- Successful concrete object-slot mutation refines the matching semantic
constructor update and preserves all nonheap runtime components. -/
theorem objectSetStep_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord fieldWord : Word32} {fieldKind : AbiKind} {field : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness fieldKind (.word32 fieldWord) field)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (indexValid : index < semantic.objectFields.size)
    (kindAt : fieldKinds[index]? = some fieldKind)
    (updated : setObjectField runtime (.object (.heap location)) index field =
      .ok nextRuntime) :
    ∃ heap,
      objectSetStep index fieldKind initial
          [.i32 (UInt32.ofNat objectWord.value),
            .i32 (UInt32.ofNat fieldWord.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases objectRelated with
  | object heapRelated =>
      cases heapRelated with
      | mapped mapped =>
          obtain ⟨heap, semanticAfter, concreteOperation,
              semanticOperation, finalHeapRelated, capacity, cursor⟩ :=
            runtimeRelated.heap.writeObjectField_refines_with_capacity mapped
              found live objectEq descriptorFound index fieldKind field fieldWord
              indexValid kindAt fieldRelated
          rw [updated] at semanticOperation
          have afterEq := Except.ok.inj semanticOperation
          subst semanticAfter
          refine ⟨heap, ?_, ?_, capacity, cursor⟩
          · simp [objectSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
              concreteOperation, replaceHeap]
          · apply ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
              finalHeapRelated
            apply modifyConstructor_heapOnly
            simpa [setObjectField] using updated

theorem objectSetStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord fieldWord : Word32} {fieldKind : AbiKind} {field : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness fieldKind (.word32 fieldWord) field)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (indexValid : index < semantic.objectFields.size)
    (kindAt : fieldKinds[index]? = some fieldKind)
    (updated : setObjectField runtime (.object (.heap location)) index field =
      .ok nextRuntime) :
    ∃ heap,
      objectSetStep index fieldKind initial
          [.i32 (UInt32.ofNat objectWord.value),
            .i32 (UInt32.ofNat fieldWord.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    objectSetStep_of_refines_with_capacity runtimeRelated objectRelated
      fieldRelated found live objectEq descriptorFound indexValid kindAt updated
  exact ⟨heap, concrete, finalRelated⟩

/-- Successful concrete `USize` mutation refines the matching semantic
constructor update and preserves all nonheap runtime components. -/
theorem usizeSetStep_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord : Word32} {field : UInt64} {index : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (slotStart : semantic.objectFields.size ≤ index)
    (slotEnd : index < semantic.objectFields.size + semantic.usizeFields.size)
    (updated : setUSizeSlot runtime (.object (.heap location)) index
      (.usize field) = .ok nextRuntime) :
    ∃ heap,
      usizeSetStep index initial
          [.i32 (UInt32.ofNat objectWord.value), .i64 field] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases objectRelated with
  | object heapRelated =>
      cases heapRelated with
      | mapped mapped =>
          obtain ⟨heap, semanticAfter, concreteOperation,
              semanticOperation, finalHeapRelated, capacity, cursor⟩ :=
            runtimeRelated.heap.writeUSizeSlot_refines_with_capacity mapped found
              live objectEq index field slotStart slotEnd
          rw [updated] at semanticOperation
          have afterEq := Except.ok.inj semanticOperation
          subst semanticAfter
          refine ⟨heap, ?_, ?_, capacity, cursor⟩
          · simp [usizeSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
              concreteOperation, replaceHeap]
          · apply ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
              finalHeapRelated
            apply modifyConstructor_heapOnly
            simpa [setUSizeSlot] using updated

theorem usizeSetStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord : Word32} {field : UInt64} {index : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (slotStart : semantic.objectFields.size ≤ index)
    (slotEnd : index < semantic.objectFields.size + semantic.usizeFields.size)
    (updated : setUSizeSlot runtime (.object (.heap location)) index
      (.usize field) = .ok nextRuntime) :
    ∃ heap,
      usizeSetStep index initial
          [.i32 (UInt32.ofNat objectWord.value), .i64 field] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    usizeSetStep_of_refines_with_capacity runtimeRelated objectRelated found live
      objectEq slotStart slotEnd updated
  exact ⟨heap, concrete, finalRelated⟩

/-- An out-of-bounds object-slot mutation reaches the Talos boundary as the
exact source-classified FIR bounds fault and leaves both runtimes unchanged. -/
theorem objectSetStep_outOfBounds_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {cell : HeapCell}
    {semantic : ConstructorObject} {objectWord fieldWord : Word32}
    {fieldKind : AbiKind} {field : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (outOfBounds : semantic.objectFields.size ≤ index) :
    objectSetStep index fieldKind initial
        [.i32 (UInt32.ofNat objectWord.value),
          .i32 (UInt32.ofNat fieldWord.value)] =
        trap (clearFailure initial) (.runtime (.source (.runtime
          (.objectFieldOutOfBounds index semantic.objectFields.size)))) ∧
      setObjectField runtime (.object (.heap location)) index field =
        .error (.objectFieldOutOfBounds index semantic.objectFields.size) := by
  cases objectRelated with
  | object heapRelated =>
      cases heapRelated with
      | mapped mapped =>
          obtain ⟨concreteFailure, semanticFailure⟩ :=
            runtimeRelated.heap.writeObjectField_outOfBounds_refines mapped
              found live objectEq descriptorFound field fieldWord outOfBounds
          constructor
          · simp [objectSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
              concreteFailure, ConcreteError.toTrap]
          · exact semanticFailure

/-- An out-of-bounds `USize` mutation reaches the Talos boundary as the exact
source-classified FIR bounds fault and leaves both runtimes unchanged. -/
theorem usizeSetStep_outOfBounds_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {cell : HeapCell}
    {semantic : ConstructorObject} {objectWord : Word32}
    {field : UInt64} {index : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (outOfBounds : index < semantic.objectFields.size ∨
      semantic.objectFields.size + semantic.usizeFields.size ≤ index) :
    usizeSetStep index initial
        [.i32 (UInt32.ofNat objectWord.value), .i64 field] =
        trap (clearFailure initial) (.runtime (.source (.runtime
          (.usizeFieldOutOfBounds index
            (semantic.objectFields.size + semantic.usizeFields.size))))) ∧
      setUSizeSlot runtime (.object (.heap location)) index (.usize field) =
        .error (.usizeFieldOutOfBounds index
          (semantic.objectFields.size + semantic.usizeFields.size)) := by
  cases objectRelated with
  | object heapRelated =>
      cases heapRelated with
      | mapped mapped =>
          obtain ⟨concreteFailure, semanticFailure⟩ :=
            runtimeRelated.heap.writeUSizeSlot_outOfBounds_refines mapped found
              live objectEq field outOfBounds
          constructor
          · simp [usizeSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
              concreteFailure, ConcreteError.toTrap]
          · exact semanticFailure

/-- A stale object-slot mutation traps before reading the old slot or writing
the replacement word. -/
theorem objectSetStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord fieldWord : Word32}
    {location : Location} {cell : HeapCell} {fieldKind : AbiKind}
    {field : Value} (index : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    objectSetStep index fieldKind initial
        [.i32 (UInt32.ofNat objectWord.value),
          .i32 (UInt32.ofNat fieldWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      setObjectField runtime (.object (.heap location)) index field =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases objectRelated with
  | object heapRelated =>
      obtain ⟨concrete, semantic⟩ :=
        runtimeRelated.heap.writeObjectField_deadObject (fieldWord := fieldWord)
          heapRelated found dead index field
      refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
      simp [objectSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
        concrete, ConcreteError.toTrap]

/-- A stale `USize` mutation has the identical no-post-state boundary. -/
theorem usizeSetStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32}
    {location : Location} {cell : HeapCell} {field : UInt64}
    (index : Nat)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    usizeSetStep index initial
        [.i32 (UInt32.ofNat objectWord.value), .i64 field] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      setUSizeSlot runtime (.object (.heap location)) index (.usize field) =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases objectRelated with
  | object heapRelated =>
      obtain ⟨concrete, semantic⟩ :=
        runtimeRelated.heap.writeUSizeSlot_deadObject heapRelated found dead
          index field
      refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
      simp [usizeSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
        concrete, ConcreteError.toTrap]

/-- A stale UInt64 scalar mutation preserves the exact source-address fault
through the Talos host and has no concrete or semantic post-state. -/
theorem scalarSetStep_uint64_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {field : UInt64}
    {location : Location} {cell : HeapCell} {slotIndex byteOffset : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint64 (.word64 field)
      (.scalar (.uint64 field)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    scalarSetStep slotIndex byteOffset .uint64 initial
        [.i32 (UInt32.ofNat objectWord.value), .i64 field] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      setScalarField runtime (.object (.heap location)) slotIndex byteOffset
          (.scalar (.uint64 field)) = .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases fieldRelated
  cases objectRelated with
  | object heapRelated =>
      obtain ⟨concrete, semantic⟩ :=
        runtimeRelated.heap.writeScalarUInt64Field_deadObject heapRelated found
          dead slotIndex byteOffset field
      refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
      simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
        concrete, ConcreteError.toTrap]

/-- The UInt32 scalar host has the same stale-reference boundary. -/
theorem scalarSetStep_uint32_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord fieldWord : Word32} {field : UInt32}
    {location : Location} {cell : HeapCell} {slotIndex byteOffset : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint32 (.word32 fieldWord)
      (.scalar (.uint32 field)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    scalarSetStep slotIndex byteOffset .uint32 initial
        [.i32 (UInt32.ofNat objectWord.value),
          .i32 (UInt32.ofNat fieldWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      setScalarField runtime (.object (.heap location)) slotIndex byteOffset
          (.scalar (.uint32 field)) = .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases fieldRelated with
  | uint32 encoded =>
      cases objectRelated with
      | object heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.writeScalarUInt32Field_deadObject heapRelated
              found dead slotIndex byteOffset field
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            encoded, concrete, ConcreteError.toTrap]

/-- The UInt16 scalar host has the same stale-reference boundary. -/
theorem scalarSetStep_uint16_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord fieldWord : Word32} {field : UInt16}
    {location : Location} {cell : HeapCell} {slotIndex byteOffset : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint16 (.word32 fieldWord)
      (.scalar (.uint16 field)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    scalarSetStep slotIndex byteOffset .uint16 initial
        [.i32 (UInt32.ofNat objectWord.value),
          .i32 (UInt32.ofNat fieldWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      setScalarField runtime (.object (.heap location)) slotIndex byteOffset
          (.scalar (.uint16 field)) = .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases fieldRelated with
  | uint16 encoded =>
      cases objectRelated with
      | object heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.writeScalarUInt16Field_deadObject heapRelated
              found dead slotIndex byteOffset field
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            encoded, concrete, ConcreteError.toTrap]

/-- The UInt8 scalar host has the same stale-reference boundary. -/
theorem scalarSetStep_uint8_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord fieldWord : Word32} {field : UInt8}
    {location : Location} {cell : HeapCell} {slotIndex byteOffset : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint8 (.word32 fieldWord)
      (.scalar (.uint8 field)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    scalarSetStep slotIndex byteOffset .uint8 initial
        [.i32 (UInt32.ofNat objectWord.value),
          .i32 (UInt32.ofNat fieldWord.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject objectWord)))) ∧
      setScalarField runtime (.object (.heap location)) slotIndex byteOffset
          (.scalar (.uint8 field)) = .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject objectWord)) (.deadObject location) := by
  cases fieldRelated with
  | uint8 encoded =>
      cases objectRelated with
      | object heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.writeScalarUInt8Field_deadObject heapRelated
              found dead slotIndex byteOffset field
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
            encoded, concrete, ConcreteError.toTrap]

theorem scalarSetStep_uint64_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord : Word32} {field : UInt64} {slotIndex byteOffset : Nat}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint64 (.word64 field)
      (.scalar (.uint64 field)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (retainedDisjoint : ∀ old ∈ semantic.scalarFields,
      old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
      old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
        byteOffset + 8 ≤ old.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 8 ≤ info.ssize)
    (updated : setScalarField runtime (.object (.heap location)) slotIndex
      byteOffset (.scalar (.uint64 field)) = .ok nextRuntime) :
    ∃ heap,
      scalarSetStep slotIndex byteOffset .uint64 initial
          [.i32 (UInt32.ofNat objectWord.value), .i64 field] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases fieldRelated
  cases objectRelated with
  | object heapRelated =>
      cases heapRelated with
      | mapped mapped =>
          obtain ⟨heap, semanticAfter, concreteOperation,
              semanticOperation, finalHeapRelated, capacity, cursor⟩ :=
            runtimeRelated.heap.writeScalarUInt64Field_refines_with_capacity
              mapped found live objectEq descriptorFound slotIndex byteOffset
              field retainedDisjoint slotIndexEq fieldFits
          rw [updated] at semanticOperation
          have afterEq := Except.ok.inj semanticOperation
          subst semanticAfter
          refine ⟨heap, ?_, ?_, capacity, cursor⟩
          · simp [scalarSetStep, clearFailure, Word32.ofUInt32_ofNat_value,
              concreteOperation, replaceHeap]
          · apply ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
              finalHeapRelated
            apply modifyConstructor_heapOnly
            simpa [setScalarField] using updated

theorem scalarSetStep_uint64_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord : Word32} {field : UInt64} {slotIndex byteOffset : Nat}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint64 (.word64 field)
      (.scalar (.uint64 field)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (retainedDisjoint : ∀ old ∈ semantic.scalarFields,
      old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
      old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
        byteOffset + 8 ≤ old.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 8 ≤ info.ssize)
    (updated : setScalarField runtime (.object (.heap location)) slotIndex
      byteOffset (.scalar (.uint64 field)) = .ok nextRuntime) :
    ∃ heap,
      scalarSetStep slotIndex byteOffset .uint64 initial
          [.i32 (UInt32.ofNat objectWord.value), .i64 field] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    scalarSetStep_uint64_of_refines_with_capacity runtimeRelated objectRelated
      fieldRelated found live objectEq descriptorFound retainedDisjoint
      slotIndexEq fieldFits updated
  exact ⟨heap, concrete, finalRelated⟩

theorem scalarSetStep_uint32_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord fieldWord : Word32} {field : UInt32}
    {slotIndex byteOffset : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint32 (.word32 fieldWord)
      (.scalar (.uint32 field)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (retainedDisjoint : ∀ old ∈ semantic.scalarFields,
      old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
      old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
        byteOffset + 4 ≤ old.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 4 ≤ info.ssize)
    (updated : setScalarField runtime (.object (.heap location)) slotIndex
      byteOffset (.scalar (.uint32 field)) = .ok nextRuntime) :
    ∃ heap,
      scalarSetStep slotIndex byteOffset .uint32 initial
          [.i32 (UInt32.ofNat objectWord.value),
            .i32 (UInt32.ofNat fieldWord.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases fieldRelated with
  | uint32 encoded =>
      cases objectRelated with
      | object heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨heap, semanticAfter, concreteOperation,
                  semanticOperation, finalHeapRelated, capacity, cursor⟩ :=
                runtimeRelated.heap.writeScalarUInt32Field_refines_with_capacity
                  mapped found live objectEq descriptorFound slotIndex byteOffset
                  field retainedDisjoint slotIndexEq fieldFits
              rw [updated] at semanticOperation
              have afterEq := Except.ok.inj semanticOperation
              subst semanticAfter
              refine ⟨heap, ?_, ?_, capacity, cursor⟩
              · simp [scalarSetStep, clearFailure,
                  Word32.ofUInt32_ofNat_value, encoded, concreteOperation,
                  replaceHeap]
              · apply ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
                  finalHeapRelated
                apply modifyConstructor_heapOnly
                simpa [setScalarField] using updated

theorem scalarSetStep_uint32_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord fieldWord : Word32} {field : UInt32}
    {slotIndex byteOffset : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint32 (.word32 fieldWord)
      (.scalar (.uint32 field)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (retainedDisjoint : ∀ old ∈ semantic.scalarFields,
      old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
      old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
        byteOffset + 4 ≤ old.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 4 ≤ info.ssize)
    (updated : setScalarField runtime (.object (.heap location)) slotIndex
      byteOffset (.scalar (.uint32 field)) = .ok nextRuntime) :
    ∃ heap,
      scalarSetStep slotIndex byteOffset .uint32 initial
          [.i32 (UInt32.ofNat objectWord.value),
            .i32 (UInt32.ofNat fieldWord.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    scalarSetStep_uint32_of_refines_with_capacity runtimeRelated objectRelated
      fieldRelated found live objectEq descriptorFound retainedDisjoint
      slotIndexEq fieldFits updated
  exact ⟨heap, concrete, finalRelated⟩

theorem scalarSetStep_uint16_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord fieldWord : Word32} {field : UInt16}
    {slotIndex byteOffset : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint16 (.word32 fieldWord)
      (.scalar (.uint16 field)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (retainedDisjoint : ∀ old ∈ semantic.scalarFields,
      old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
      old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
        byteOffset + 2 ≤ old.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 2 ≤ info.ssize)
    (updated : setScalarField runtime (.object (.heap location)) slotIndex
      byteOffset (.scalar (.uint16 field)) = .ok nextRuntime) :
    ∃ heap,
      scalarSetStep slotIndex byteOffset .uint16 initial
          [.i32 (UInt32.ofNat objectWord.value),
            .i32 (UInt32.ofNat fieldWord.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases fieldRelated with
  | uint16 encoded =>
      cases objectRelated with
      | object heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨heap, semanticAfter, concreteOperation,
                  semanticOperation, finalHeapRelated, capacity, cursor⟩ :=
                runtimeRelated.heap.writeScalarUInt16Field_refines_with_capacity
                  mapped found live objectEq descriptorFound slotIndex byteOffset
                  field retainedDisjoint slotIndexEq fieldFits
              rw [updated] at semanticOperation
              have afterEq := Except.ok.inj semanticOperation
              subst semanticAfter
              refine ⟨heap, ?_, ?_, capacity, cursor⟩
              · simp [scalarSetStep, clearFailure,
                  Word32.ofUInt32_ofNat_value, encoded, concreteOperation,
                  replaceHeap]
              · apply ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
                  finalHeapRelated
                apply modifyConstructor_heapOnly
                simpa [setScalarField] using updated

theorem scalarSetStep_uint16_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord fieldWord : Word32} {field : UInt16}
    {slotIndex byteOffset : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint16 (.word32 fieldWord)
      (.scalar (.uint16 field)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (retainedDisjoint : ∀ old ∈ semantic.scalarFields,
      old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
      old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
        byteOffset + 2 ≤ old.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 2 ≤ info.ssize)
    (updated : setScalarField runtime (.object (.heap location)) slotIndex
      byteOffset (.scalar (.uint16 field)) = .ok nextRuntime) :
    ∃ heap,
      scalarSetStep slotIndex byteOffset .uint16 initial
          [.i32 (UInt32.ofNat objectWord.value),
            .i32 (UInt32.ofNat fieldWord.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    scalarSetStep_uint16_of_refines_with_capacity runtimeRelated objectRelated
      fieldRelated found live objectEq descriptorFound retainedDisjoint
      slotIndexEq fieldFits updated
  exact ⟨heap, concrete, finalRelated⟩

theorem scalarSetStep_uint8_of_refines_with_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord fieldWord : Word32} {field : UInt8}
    {slotIndex byteOffset : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint8 (.word32 fieldWord)
      (.scalar (.uint8 field)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (retainedDisjoint : ∀ old ∈ semantic.scalarFields,
      old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
      old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
        byteOffset + 1 ≤ old.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 1 ≤ info.ssize)
    (updated : setScalarField runtime (.object (.heap location)) slotIndex
      byteOffset (.scalar (.uint8 field)) = .ok nextRuntime) :
    ∃ heap,
      scalarSetStep slotIndex byteOffset .uint8 initial
          [.i32 (UInt32.ofNat objectWord.value),
            .i32 (UInt32.ofNat fieldWord.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  cases fieldRelated with
  | uint8 encoded =>
      cases objectRelated with
      | object heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨heap, semanticAfter, concreteOperation,
                  semanticOperation, finalHeapRelated, capacity, cursor⟩ :=
                runtimeRelated.heap.writeScalarUInt8Field_refines_with_capacity
                  mapped found live objectEq descriptorFound slotIndex byteOffset
                  field retainedDisjoint slotIndexEq fieldFits
              rw [updated] at semanticOperation
              have afterEq := Except.ok.inj semanticOperation
              subst semanticAfter
              refine ⟨heap, ?_, ?_, capacity, cursor⟩
              · simp [scalarSetStep, clearFailure,
                  Word32.ofUInt32_ofNat_value, encoded, concreteOperation,
                  replaceHeap]
              · apply ConcreteRuntimeRel.replaceHeap_of_heapOnly runtimeRelated
                  finalHeapRelated
                apply modifyConstructor_heapOnly
                simpa [setScalarField] using updated

theorem scalarSetStep_uint8_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    {objectWord fieldWord : Word32} {field : UInt8}
    {slotIndex byteOffset : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (fieldRelated : ValueRel witness .uint8 (.word32 fieldWord)
      (.scalar (.uint8 field)))
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (retainedDisjoint : ∀ old ∈ semantic.scalarFields,
      old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
      old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
        byteOffset + 1 ≤ old.offset)
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : byteOffset + 1 ≤ info.ssize)
    (updated : setScalarField runtime (.object (.heap location)) slotIndex
      byteOffset (.scalar (.uint8 field)) = .ok nextRuntime) :
    ∃ heap,
      scalarSetStep slotIndex byteOffset .uint8 initial
          [.i32 (UInt32.ofNat objectWord.value),
            .i32 (UInt32.ofNat fieldWord.value)] =
        .Return [] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime witness
        nextRuntime := by
  obtain ⟨heap, concrete, finalRelated, _, _⟩ :=
    scalarSetStep_uint8_of_refines_with_capacity runtimeRelated objectRelated
      fieldRelated found live objectEq descriptorFound retainedDisjoint
      slotIndexEq fieldFits updated
  exact ⟨heap, concrete, finalRelated⟩

/-- The complete concrete state relation used by W6.6 composition: host-owned
memory/effects refine FIR runtime state, the failure channel is clear, and
compiler-assigned locals contain related W6 lanes. -/
def StateRelated (sourceFunction : Fir.Wasm.Function)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteRuntimeRel targetStore.host.runtime witness sourceRuntime ∧
    targetStore.host.failure? = none ∧
    EnvLocalsRelated witness (functionBindings sourceFunction) sourceEnv
      targetLocals

/-- Resolve one source binding to its exact concrete ABI lane at an already
known compiler-assigned local. -/
theorem StateRelated.resolve
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    {fvar : Lean.FVarId} {sourceValue : Value} {index : Nat} {kind : AbiKind}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (sourceLookup : lookup sourceEnv fvar = some sourceValue)
    (found : findFVar? (functionBindings sourceFunction) fvar = some index)
    (kindAt :
      (functionBindings sourceFunction)[index]?.map Prod.snd = some kind) :
    ∃ physical,
      targetLocals.get index = some physical ∧
      PhysicalValueRel witness kind physical sourceValue := by
  rcases related.2.2 sourceLookup with
    ⟨actualIndex, actualKind, physical, actualFound, actualKindAt,
      targetLookup, valueRelated⟩
  rw [found] at actualFound
  injection actualFound with indexEq
  subst actualIndex
  rw [kindAt] at actualKindAt
  injection actualKindAt with kindEq
  subst actualKind
  exact ⟨physical, targetLookup, valueRelated⟩

theorem StateRelated.clearFailure
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness) :
    clearFailure targetStore = targetStore := by
  rcases targetStore with
    ⟨globals, mem, extraMems, dataSegments, tables, elementSegments, exns,
      gcHeap, host⟩
  rcases host with
    ⟨runtime, closureDispatch, closureDescriptors, closureApplication,
      externals, failure⟩
  have failureEq : failure = none := related.2.1
  subst failure
  rfl

/-- A successful read-only concrete operation may bind its result without
changing the runtime witness. -/
theorem StateRelated.bindWord32
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals} {witness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {word : Word32} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : ValueRel witness kind (.word32 word) semantic)
    (targetSet :
      targetLocals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
        some updated) :
    StateRelated sourceFunction sourceRuntime (bind sourceEnv result semantic)
      (FirTalos.Concrete.clearFailure targetStore) updated witness := by
  rw [related.clearFailure]
  exact ⟨related.1, related.2.1,
    EnvLocalsRelated.bind related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) (.refl witness) (.word32 valueRelated)⟩

theorem StateRelated.bindWord64
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals} {witness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {word : UInt64} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : ValueRel witness kind (.word64 word) semantic)
    (targetSet : targetLocals.set? resultIndex (.i64 word) = some updated) :
    StateRelated sourceFunction sourceRuntime (bind sourceEnv result semantic)
      (FirTalos.Concrete.clearFailure targetStore) updated witness := by
  rw [related.clearFailure]
  exact ⟨related.1, related.2.1,
    EnvLocalsRelated.bind related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) (.refl witness) (.word64 valueRelated)⟩

theorem StateRelated.bindPhysical
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals} {witness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : PhysicalValueRel witness kind physical semantic)
    (targetSet : targetLocals.set? resultIndex physical = some updated) :
    StateRelated sourceFunction sourceRuntime (bind sourceEnv result semantic)
      (FirTalos.Concrete.clearFailure targetStore) updated witness := by
  rw [related.clearFailure]
  exact ⟨related.1, related.2.1,
    EnvLocalsRelated.bind related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) (.refl witness) valueRelated⟩

theorem StateRelated.bindAfter
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals}
    {witness nextWitness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (extension : witness.Extends nextWitness)
    (runtimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : PhysicalValueRel nextWitness kind physical semantic)
    (targetSet : targetLocals.set? resultIndex physical = some updated) :
    StateRelated sourceFunction nextRuntime (bind sourceEnv result semantic)
      nextStore updated nextWitness := by
  exact ⟨runtimeRelated, failureClear,
    EnvLocalsRelated.bind related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) extension valueRelated⟩

/-- Result binding after a general representation-witness transition. This is
the reset/reuse counterpart of `bindAfter`, whose monotone-extension premise
cannot express rebinding an already allocated constructor descriptor. -/
theorem StateRelated.bindAfterTransport
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals}
    {witness nextWitness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (transport : WitnessTransport witness nextWitness)
    (runtimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : PhysicalValueRel nextWitness kind physical semantic)
    (targetSet : targetLocals.set? resultIndex physical = some updated) :
    StateRelated sourceFunction nextRuntime (bind sourceEnv result semantic)
      nextStore updated nextWitness := by
  exact ⟨runtimeRelated, failureClear,
    EnvLocalsRelated.bindTransport related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) transport valueRelated⟩

/-- W6 proof judgment for generated code over the concrete host. It mirrors
W5's structural boundary while indexing both the target runtime and locals by
the representation witness. -/
def CodeWP (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (code : Lean.Compiler.LCNF.Code .impure) (target : Wasm.Program)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) (tail : List Wasm.Value)
    (Q : Wasm.Assertion Host) : Prop :=
  FirTalos.Correctness.CodeAdapted context sourceModule sourceFunction labels
      code target ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    Wasm.wp module target Q targetStore
      { targetLocals with values := tail } hostEnv

/-- Concrete semantic interface for one generated no-result effect prefix.
Separate witnesses support later reset/reuse effects that change concrete
representation metadata while preserving the source environment. -/
def EffectStepSimulates (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (code continuation : Lean.Compiler.LCNF.Code .impure)
    (target targetRest : Wasm.Program)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (witness nextWitness : RefinementWitness) : Prop :=
  SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
      continuation ∧
    CodeAdapted context sourceModule sourceFunction labels code target ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    StateRelated sourceFunction nextRuntime sourceEnv nextStore targetLocals
      nextWitness ∧
    ∀ (Q : Wasm.Assertion Host) (tail : List Wasm.Value),
      Wasm.wp module targetRest Q nextStore
          { targetLocals with values := tail } hostEnv →
        Wasm.wp module target Q targetStore
          { targetLocals with values := tail } hostEnv

/-- Recursive concrete `CodeWP` rule for a successful no-result source
effect followed by an already-composed continuation. -/
theorem codeWP_effect
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {code continuation : Lean.Compiler.LCNF.Code .impure}
    {target targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals} {witness nextWitness : RefinementWitness}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (step : EffectStepSimulates context sourceModule sourceFunction labels
      module hostEnv sourceRuntime nextRuntime sourceEnv code continuation
      target targetRest targetStore nextStore targetLocals witness nextWitness)
    (continued : CodeWP context sourceModule sourceFunction labels module
      hostEnv nextRuntime sourceEnv continuation targetRest nextStore
      targetLocals nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv code target targetStore targetLocals witness tail
      Q := by
  rcases step with ⟨_, adapted, initialRelated, _, stepWP⟩
  exact ⟨adapted, initialRelated, stepWP Q tail continued.2.2⟩

/-- Function-body postcondition over the concrete host. It retains the caller
operand remainder exactly as prescribed by Wasm's direct-call convention. -/
def ConcreteFunctionBodyPost (function : Wasm.Function)
    (args : List Wasm.Value)
    (Post : Wasm.Store Host → List Wasm.Value → Prop) :
    Wasm.Assertion Host :=
  fun continuation =>
    match continuation with
    | .Fallthrough targetStore targetLocals =>
        Post targetStore
          (targetLocals.values.take function.results.length ++
            args.drop function.numParams)
    | .Return targetStore values =>
        Post targetStore
          (values.take function.results.length ++ args.drop function.numParams)
    | _ => False

/-- Store-specific bridge from a concrete body WP to Talos's fuel-free public
function predicate. -/
theorem concreteTerminatesWith_of_wp_body_at
    {env : Wasm.HostEnv Host} {module : Wasm.Module}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial : Wasm.Store Host} {args : List Wasm.Value}
    {Post : Wasm.Store Host → List Wasm.Value → Prop}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (bodyWP :
      Wasm.wp module function.body
        (ConcreteFunctionBodyPost function args Post) initial
        (function.toLocals (args.take function.numParams).reverse) env) :
    Wasm.TerminatesWith env module functionIndex initial args Post := by
  unfold Wasm.wp at bodyWP
  rcases bodyWP with ⟨fuelBound, bodyWP⟩
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  have bodyPost := bodyWP fuel enoughFuel
  rw [Wasm.run_eq notImport]
  simp only [found]
  cases execution : Wasm.exec fuel module initial
      (function.toLocals (args.take function.numParams).reverse)
      function.body env with
  | Fallthrough final finalLocals =>
      rw [execution] at bodyPost
      exact ⟨finalLocals.values.take function.results.length ++
          args.drop function.numParams, final, rfl, bodyPost⟩
  | Return final values =>
      rw [execution] at bodyPost
      exact ⟨values.take function.results.length ++ args.drop function.numParams,
        final, rfl, bodyPost⟩
  | Break level final finalLocals =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Trap final message =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Invalid message =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | OutOfFuel =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | ReturnCall callee final values =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Throwing tag values final finalLocals =>
      rw [execution] at bodyPost
      exact bodyPost.elim

/-- A concrete semantic lowering proof for a callee body supplies the exact
fuel-free theorem consumed by `wp_directCall_let`. -/
theorem CodeWP.toConcreteTerminatesWith
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {code : Lean.Compiler.LCNF.Code .impure} {function : Wasm.Function}
    {functionIndex : Nat} {initial : Wasm.Store Host}
    {args : List Wasm.Value} {witness : RefinementWitness}
    {Post : Wasm.Store Host → List Wasm.Value → Prop}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code function.body initial
        (function.toLocals (args.take function.numParams).reverse) witness []
        (ConcreteFunctionBodyPost function args Post)) :
    Wasm.TerminatesWith hostEnv module functionIndex initial args Post := by
  apply concreteTerminatesWith_of_wp_body_at notImport found
  simpa [Wasm.Function.toLocals] using correct.2.2

/-- One direct source `let` step paired with its concrete host/local update.
Separate witnesses allow later allocation operations to grow ghost metadata. -/
def LetStepSimulates (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (witness nextWitness : RefinementWitness) : Prop :=
  FirTalos.Correctness.SourceLetResult context sourceRuntime sourceEnv decl
      nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion Host)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Witness-indexed interprocedural boundary for ordinary declaration calls
and generated closure trampolines over the concrete host. -/
def CallLetStepSimulates (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host) (externals : ExternalImpl)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (witness nextWitness : RefinementWitness) : Prop :=
  FirTalos.Correctness.SourceCallLetResult context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion Host)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Recursive concrete `CodeWP` rule for a terminating interprocedural call
prefix. The operation-specific proof may grow the representation witness. -/
theorem codeWP_callLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode = .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (step : CallLetStepSimulates context sourceFunction module hostEnv externals
      decl continuation targetValue sourceRuntime nextRuntime sourceEnv
      sourceValue targetStore nextStore targetLocals nextLocals resultIndex
      witness nextWitness)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetRest nextStore nextLocals nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals witness tail Q := by
  rcases step with ⟨_, initialRelated, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Witness-indexed concrete boundary for a generated external-call `let`.
The source side retains the interpreter's full three-step protocol, while the
target side executes the concrete foreign implementation and may extend the
heap representation witness. -/
def ExternalLetStepSimulates (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host) (externals : ExternalImpl)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (witness nextWitness : RefinementWitness) : Prop :=
  SourceExternalLetResult context externals sourceRuntime sourceEnv decl
      continuation nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion Host)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Recursive concrete `CodeWP` rule for a successful external-call `let` and
an arbitrary already-composed continuation. -/
theorem codeWP_externalLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode = .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (step : ExternalLetStepSimulates context sourceFunction module hostEnv
      externals decl continuation targetValue sourceRuntime nextRuntime sourceEnv
      sourceValue targetStore nextStore targetLocals nextLocals resultIndex
      witness nextWitness)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetRest nextStore nextLocals nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals witness tail Q := by
  rcases step with ⟨_, initialRelated, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Witness-indexed semantic boundary for either lazy zero-argument cache
path over the concrete host. -/
def LazyLetStepSimulates (path : LazyCachePath) (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host) (externals : ExternalImpl)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (witness nextWitness : RefinementWitness) : Prop :=
  SourceLazyLetResult path context externals sourceRuntime sourceEnv decl
      continuation nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion Host)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Miss-only block obligation. Direct-call and `cacheSet` rules discharge it
without reopening the surrounding flag conditional. -/
def LazyMissBodySimulates
    (module : Wasm.Module) (hostEnv : Wasm.HostEnv Host)
    (missBody : Wasm.Program) (valueIndex resultIndex : Nat)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) : Prop :=
  ∀ (rest : Wasm.Program) (Q : Wasm.Assertion Host)
      (tail : List Wasm.Value),
    Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
    Wasm.wp module missBody
      (fun continuation => match continuation with
        | .Fallthrough bodyStore bodyLocals =>
            Wasm.wp module
              (.globalGet valueIndex :: .localSet resultIndex :: rest)
              Q bodyStore { bodyLocals with values := tail } hostEnv
        | .Break 0 bodyStore bodyLocals =>
            Wasm.wp module
              (.globalGet valueIndex :: .localSet resultIndex :: rest)
              Q bodyStore { bodyLocals with values := tail } hostEnv
        | .Break (level + 1) bodyStore bodyLocals =>
            Q (.Break level bodyStore bodyLocals)
        | other => Q other)
      targetStore { targetLocals with values := tail } hostEnv

/-- Recursive concrete `CodeWP` rule shared by lazy hit and miss paths. -/
theorem codeWP_lazyLet
    {path : LazyCachePath} {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode = .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (step : LazyLetStepSimulates path context sourceFunction module hostEnv
      externals decl continuation targetValue sourceRuntime nextRuntime sourceEnv
      sourceValue targetStore nextStore targetLocals nextLocals resultIndex
      witness nextWitness)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetRest nextStore nextLocals nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals witness tail Q := by
  rcases step with ⟨_, initialRelated, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- A successful concrete tag read is the exact executable realization of the
semantic `getTag` result whenever the case tag satisfies the lowerer's checked
i32 range gate. -/
theorem getTagStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {semanticRuntime : RuntimeState} {word : Word32} {value : Value}
    {tag : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness semanticRuntime)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (tagged : getTag semanticRuntime value = .ok tag)
    (fits : tag < UInt32.size) :
    getTagStep initial [.i32 (UInt32.ofNat word.value)] =
      .Return [.i32 (UInt32.ofNat tag)] (clearFailure initial) := by
  have read := runtimeRelated.heap.readTag_tobject_refines valueRelated tagged
  have fits64 : tag < UInt64.size := by
    have sizeLe : UInt32.size ≤ UInt64.size := by native_decide
    exact lt_of_lt_of_le fits sizeLe
  have tagToNat : (UInt64.ofNat tag).toNat = tag :=
    UInt64.toNat_ofNat_of_lt' fits64
  unfold getTagStep
  simp only [clearFailure]
  rw [Word32.ofUInt32_ofNat_value, read]
  simp [tagToNat]

/-- A representation-polymorphic case discriminator rejected by FIR as a
nonconstructor produces the exact source-classified concrete trap before any
generated alternative comparison. -/
theorem getTagStep_expectedConstructor_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {value : Value}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) value)
    (tagFailed : getTag runtime value = .error .expectedConstructor) :
    getTagStep initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime ((.source .expectedConstructor : ConcreteError).toTrap)) ∧
      getTag runtime value = .error .expectedConstructor ∧
      ConcreteErrorSourceRel witness
        (.source .expectedConstructor) .expectedConstructor := by
  have readFailed :=
    runtimeRelated.heap.readTag_expectedConstructor_refines valueRelated
      tagFailed
  refine ⟨?_, tagFailed, .source .expectedConstructor⟩
  simp [getTagStep, clearFailure, Word32.ofUInt32_ofNat_value, readFailed,
    ConcreteError.toTrap]

/-- Stale tag observation preserves the exact witness-indexed source fault at
the Talos host boundary. -/
theorem getTagStep_deadObject_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {word : Word32} {location : Location}
    {cell : HeapCell}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated :
      ValueRel witness .tobject (.word32 word) (.object (.heap location)))
    (found : findCell? runtime.heap location = some cell)
    (dead : cell.live = false) :
    getTagStep initial [.i32 (UInt32.ofNat word.value)] =
        trap (clearFailure initial)
          (.runtime (.source (.address (.deadObject word)))) ∧
      getTag runtime (.object (.heap location)) =
        .error (.deadObject location) ∧
      ConcreteErrorSourceRel witness
        (.sourceAddress (.deadObject word)) (.deadObject location) := by
  cases valueRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          obtain ⟨concrete, semantic⟩ :=
            runtimeRelated.heap.readTag_deadObject heapRelated found dead
          refine ⟨?_, semantic, .sourceAddress (.deadObject heapRelated)⟩
          simp [getTagStep, clearFailure, Word32.ofUInt32_ofNat_value,
            concrete, ConcreteError.toTrap]

/-- Generic exact-contract lifting used by every W6.6 concrete host operation.
It is independent of FIR's semantic host type and therefore composes Talos WP
directly with a concrete resolver. -/
theorem wp_exact_host_call_of_return
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {spec : Wasm.HostSpec host} {id : Nat} {imp : Wasm.ImportDecl}
    {step : Wasm.Store host → List Wasm.Value → Wasm.HostResult host}
    {rest : Wasm.Program} {Q : Wasm.Assertion host}
    {initial final : Wasm.Store host} {locals : Wasm.Locals}
    {physicalArgs results : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hArgs :
      (locals.values.take imp.params.length).reverse = physicalArgs)
    (operation : step initial physicalArgs = .Return results final)
    (continued :
      Wasm.wp module rest Q final
        { locals with values := results.take imp.results.length ++
            locals.values.drop imp.params.length } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply Wasm.wp_call_host_contract hImp hSat hi hContract
  · intro actualResults actualFinal contract
    change Wasm.HostResult.Return actualResults actualFinal =
      step initial
        (locals.values.take imp.params.length).reverse at contract
    rw [hArgs, operation] at contract
    injection contract with resultsEq finalEq
    subst resultsEq
    subst finalEq
    exact continued
  · intro trapped message contract
    change Wasm.HostResult.Trap trapped message =
      step initial
        (locals.values.take imp.params.length).reverse at contract
    rw [hArgs, operation] at contract
    contradiction

/-- Host-polymorphic local-write rule used by concrete result-producing
imports. The semantic W5 rule is specialized to `RuntimeHost`; this is the
same Talos instruction fact over the W6 host. -/
theorem wp_localSet_of_set
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {rest : Wasm.Program} {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals updated : Wasm.Locals}
    {index : Nat} {value : Wasm.Value} {tail : List Wasm.Value}
    (hSet : locals.set? index value = some updated)
    (continued :
      Wasm.wp module rest Q store { updated with values := tail } env) :
    Wasm.wp module (.localSet index :: rest) Q store
      { locals with values := value :: tail } env := by
  have stackSet :
      ({ locals with values := value :: tail }.set? index value) =
        (locals.set? index value).map
          (fun next => { next with values := value :: tail }) := by
    simp only [Wasm.Locals.set?]
    split
    · rfl
    · split <;> rfl
  simp only [Wasm.wp_localSet_cons]
  rw [stackSet, hSet]
  exact continued

/-- Host-polymorphic generated `local.get` sequence. Constructor allocation is
the first concrete W6 operation with an arbitrary number of operands. -/
theorem wp_localGets
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {rest : Wasm.Program} {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {indices : List Nat} {values : List Wasm.Value}
    (tail : List Wasm.Value)
    (hGets :
      List.Forall₂ (fun index value => locals.get index = some value)
        indices values)
    (continued :
      Wasm.wp module rest Q store
        { locals with values := values.reverse ++ tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++ rest)
      Q store { locals with values := tail } env := by
  induction hGets generalizing tail with
  | nil => simpa using continued
  | cons hGet hGets ih =>
      rename_i index value indices values
      simp only [List.map_cons, List.cons_append, Wasm.wp_localGet_cons]
      have hGetNext :
          ({ locals with values := tail } : Wasm.Locals).get index =
            some value := by
        simpa [Wasm.Locals.get] using hGet
      rw [hGetNext]
      apply ih (tail := value :: tail)
      simpa [List.reverse_cons, List.append_assoc] using continued

/--
The target operand prefix emitted for constructor fields, together with the
physical operands that it places on the Wasm stack in source order.

This relation deliberately has only the two instruction shapes produced by
`compileArg`: a compiler-resolved local read and the canonical zero word for
an erased field.  It is an execution fact about compiler-derived code, not a
translation certificate.
-/
inductive ConstructorArgsReady (locals : Wasm.Locals) :
    Wasm.Program → List Wasm.Value → Prop where
  | nil : ConstructorArgsReady locals [] []
  | localGet
      {index : Nat} {physical : Wasm.Value}
      {target : Wasm.Program} {physicalArgs : List Wasm.Value}
      (found : locals.get index = some physical)
      (rest : ConstructorArgsReady locals target physicalArgs) :
      ConstructorArgsReady locals
        (.localGet index :: target) (physical :: physicalArgs)
  | erased
      {target : Wasm.Program} {physicalArgs : List Wasm.Value}
      (rest : ConstructorArgsReady locals target physicalArgs) :
      ConstructorArgsReady locals
        (.const 0 :: target) (.i32 0 :: physicalArgs)

/--
Every ready constructor-argument prefix pushes exactly its source-order
physical operands (reversed by the Wasm operand stack convention), preserves
the caller tail, and then hands control to an arbitrary continuation.
-/
theorem ConstructorArgsReady.wp
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {argumentCode rest : Wasm.Program} {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {physicalArgs tail : List Wasm.Value}
    (ready : ConstructorArgsReady locals argumentCode physicalArgs)
    (continued :
      Wasm.wp module rest Q store
        { locals with values := physicalArgs.reverse ++ tail } env) :
    Wasm.wp module (argumentCode ++ rest) Q store
      { locals with values := tail } env := by
  induction ready generalizing tail with
  | nil =>
      simpa using continued
  | localGet found ready ih =>
      rename_i index physical targetArgs remainingPhysical
      simp only [List.cons_append, Wasm.wp_localGet_cons]
      have foundNext :
          ({ locals with values := tail } : Wasm.Locals).get index =
            some physical := by
        simpa [Wasm.Locals.get] using found
      rw [foundNext]
      apply ih (tail := physical :: tail)
      simpa [List.reverse_cons, List.append_assoc] using continued
  | erased ready ih =>
      simp only [List.cons_append]
      rw [Wasm.wp_const_cons]
      apply ih (tail := .i32 0 :: tail)
      simpa [List.reverse_cons, List.append_assoc] using continued

/-- Host-polymorphic generated no-result effect prefix. Source-order local
loads are reversed into Wasm operand order, consumed by one exact-contract
host call, and the original operand tail is restored. -/
theorem wp_effect_localGets
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {spec : Wasm.HostSpec host} {id : Nat} {imp : Wasm.ImportDecl}
    {step : Wasm.Store host → List Wasm.Value → Wasm.HostResult host}
    {rest : Wasm.Program} {Q : Wasm.Assertion host}
    {initial final : Wasm.Store host} {locals : Wasm.Locals}
    {indices : List Nat} {physicalArgs tail : List Wasm.Value}
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 0)
    (operation : step initial physicalArgs = .Return [] final)
    (continued :
      Wasm.wp module rest Q final { locals with values := tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++ .call id :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_exact_host_call_of_return (physicalArgs := physicalArgs)
    (results := []) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using continued

/-- Generic unary concrete-host instance of the no-result effect boundary. -/
theorem effectStepSimulates_unaryHost
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {code continuation : Lean.Compiler.LCNF.Code .impure}
    {initial final : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {physicalObject : Wasm.Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness nextWitness : RefinementWitness}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    (sourceStep : SourceEffectResult context sourceRuntime nextRuntime sourceEnv
      code continuation)
    (adapted : CodeAdapted context sourceModule sourceFunction labels code
      ([.localGet objectIndex, .call id] ++ targetRest))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (finalRelated : StateRelated sourceFunction nextRuntime sourceEnv final
      locals nextWitness)
    (hObject : locals.get objectIndex = some physicalObject)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (operation : step initial [physicalObject] = .Return [] final) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      sourceRuntime nextRuntime sourceEnv code continuation
      ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial final
      locals witness nextWitness := by
  refine ⟨sourceStep, adapted, initialRelated, finalRelated, ?_⟩
  intro Q tail continued
  simpa using wp_effect_localGets
    (indices := [objectIndex]) (physicalArgs := [physicalObject])
    (tail := tail) (.cons hObject .nil) hImp hSat hi hContract hParams
    hResults operation continued

/-- Generic binary concrete-host instance of the no-result effect boundary. -/
theorem effectStepSimulates_binaryHost
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {code continuation : Lean.Compiler.LCNF.Code .impure}
    {initial final : Wasm.Store Host} {locals : Wasm.Locals}
    {firstIndex secondIndex : Nat} {physicalFirst physicalSecond : Wasm.Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness nextWitness : RefinementWitness}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    (sourceStep : SourceEffectResult context sourceRuntime nextRuntime sourceEnv
      code continuation)
    (adapted : CodeAdapted context sourceModule sourceFunction labels code
      ([.localGet firstIndex, .localGet secondIndex, .call id] ++ targetRest))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (finalRelated : StateRelated sourceFunction nextRuntime sourceEnv final
      locals nextWitness)
    (hFirst : locals.get firstIndex = some physicalFirst)
    (hSecond : locals.get secondIndex = some physicalSecond)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (operation : step initial [physicalFirst, physicalSecond] =
      .Return [] final) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      sourceRuntime nextRuntime sourceEnv code continuation
      ([.localGet firstIndex, .localGet secondIndex, .call id] ++ targetRest)
      targetRest initial final locals witness nextWitness := by
  refine ⟨sourceStep, adapted, initialRelated, finalRelated, ?_⟩
  intro Q tail continued
  simpa using wp_effect_localGets
    (indices := [firstIndex, secondIndex])
    (physicalArgs := [physicalFirst, physicalSecond]) (tail := tail)
    (.cons hFirst (.cons hSecond .nil)) hImp hSat hi hContract hParams
    hResults operation continued

/-- Generic concrete-host effect whose first operand is a local and whose
second operand is a compiler-produced wasm32 constant. This is the exact shape
of an erased object-field write. -/
theorem effectStepSimulates_localI32ConstHost
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {code continuation : Lean.Compiler.LCNF.Code .impure}
    {initial final : Wasm.Store Host} {locals : Wasm.Locals}
    {firstIndex : Nat} {physicalFirst : Wasm.Value} {constant : UInt32}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness nextWitness : RefinementWitness}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    (sourceStep : SourceEffectResult context sourceRuntime nextRuntime sourceEnv
      code continuation)
    (adapted : CodeAdapted context sourceModule sourceFunction labels code
      ([.localGet firstIndex, .const constant, .call id] ++ targetRest))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (finalRelated : StateRelated sourceFunction nextRuntime sourceEnv final
      locals nextWitness)
    (hFirst : locals.get firstIndex = some physicalFirst)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (operation : step initial [physicalFirst, .i32 constant] =
      .Return [] final) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      sourceRuntime nextRuntime sourceEnv code continuation
      ([.localGet firstIndex, .const constant, .call id] ++ targetRest)
      targetRest initial final locals witness nextWitness := by
  refine ⟨sourceStep, adapted, initialRelated, finalRelated, ?_⟩
  intro Q tail continued
  simp only [List.cons_append, Wasm.wp_localGet_cons]
  have hFirstNext :
      ({ locals with values := tail } : Wasm.Locals).get firstIndex =
        some physicalFirst := by
    simpa [Wasm.Locals.get] using hFirst
  rw [hFirstNext]
  simp only
  rw [Wasm.wp_const_cons]
  apply wp_exact_host_call_of_return
    (physicalArgs := [physicalFirst, .i32 constant]) (results := [])
    hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using continued

/-- A compiler-elided concrete source effect advances only source control. -/
theorem effectStepSimulates_elided
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceEnv : Env}
    {code continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {sourceRuntime : RuntimeState} {targetRest : Wasm.Program}
    {witness : RefinementWitness}
    (sourceStep : SourceEffectResult context sourceRuntime sourceRuntime
      sourceEnv code continuation)
    (adapted : CodeAdapted context sourceModule sourceFunction labels code
      targetRest)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceRuntime sourceEnv code continuation targetRest
      targetRest initial initial locals witness witness := by
  exact ⟨sourceStep, adapted, initialRelated, initialRelated,
    fun _ _ continued => continued⟩

/-- Nonpersistent source increment composed through the real compiler,
adapter, concrete runtime, and exact generated unary host-call prefix. The
returned frontier equation supports zero-cost budget transport. -/
theorem effectStepSimulates_inc_with_capacity
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectKind : AbiKind}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {sourceObject : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : incValue sourceRuntime sourceObject amount check = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, objectKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (kindAt : (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
      some objectKind)
    (objectRefines : objectKind.refines .tobject = true)
    (callFound : callIndex? sourceModule (.runtime (.inc amount check)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (incrementContract amount check))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (fits : ∀ (location : Location) (cell : HeapCell),
      sourceObject = .object (.heap location) →
      findCell? sourceRuntime.heap location = some cell →
      cell.rc + amount < UInt32.size) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.inc objectId amount check false continuation) continuation
        ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
        (replaceHeap initial heap) locals witness witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness := by
  have sourceLookup : lookup sourceEnv objectId = some sourceObject := by
    unfold lookupValue at objectLookup
    split at objectLookup
    · rename_i value found
      injection objectLookup with valueEq
      subst value
      exact found
    · contradiction
  obtain ⟨physical, hObject, physicalRelated⟩ :=
    initialRelated.resolve sourceLookup objectFound kindAt
  have tobjectRelated := physicalRelated.toTObject objectRefines
  cases tobjectRelated with
  | word32 objectRelated =>
      obtain ⟨heap, operation, runtimeRelated, cursor, capacity⟩ :=
        incrementStep_of_refines_with_capacity initialRelated.1 objectRelated
          updated fits
      refine ⟨heap, ?_, cursor, capacity⟩
      apply effectStepSimulates_unaryHost
        (step := incrementStep amount check)
      · intro externals
        simp [executeStep, coreStep, objectLookup, updated]
      · exact codeAdapted_inc objectCompiled objectFound callFound
          continuationAdapted
      · exact initialRelated
      · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
          initialRelated.2.2⟩
      · exact hObject
      · exact hImp
      · exact hSat
      · exact hi
      · exact hContract
      · exact hParams
      · exact hResults
      · exact operation
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

theorem effectStepSimulates_inc
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectKind : AbiKind}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {sourceObject : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : incValue sourceRuntime sourceObject amount check = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, objectKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (kindAt : (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
      some objectKind)
    (objectRefines : objectKind.refines .tobject = true)
    (callFound : callIndex? sourceModule (.runtime (.inc amount check)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (incrementContract amount check))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (fits : ∀ (location : Location) (cell : HeapCell),
      sourceObject = .object (.heap location) →
      findCell? sourceRuntime.heap location = some cell →
      cell.rc + amount < UInt32.size) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.inc objectId amount check false continuation) continuation
        ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
        (replaceHeap initial heap) locals witness witness := by
  obtain ⟨heap, step, _, _⟩ :=
    effectStepSimulates_inc_with_capacity objectLookup updated initialRelated
      objectCompiled objectFound kindAt objectRefines callFound
      continuationAdapted hImp hSat hi hContract hParams hResults fits
  exact ⟨heap, step⟩

/-- Persistent increments are source and concrete control-flow no-ops. -/
theorem effectStepSimulates_inc_persistent
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {sourceRuntime : RuntimeState} {targetRest : Wasm.Program}
    {witness : RefinementWitness}
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceRuntime sourceEnv
      (.inc objectId amount check true continuation) continuation targetRest
      targetRest initial initial locals witness witness := by
  apply effectStepSimulates_elided
  · intro externals
    simp [executeStep, coreStep]
  · exact codeAdapted_inc_persistent continuationAdapted
  · exact initialRelated

/-- Nonpersistent decrement composed through source evaluation, the real
compiler and adapter, concrete recursive ownership release, and the exact
generated unary host-call prefix. Both checked and unchecked ordinary heap
operations use this rule; representation refinement excludes successful
nonzero unchecked tagged releases. -/
theorem effectStepSimulates_dec_with_capacity
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    {objectKind : AbiKind}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {sourceObject : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : decValue sourceRuntime sourceObject amount check = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, objectKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (kindAt : (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
      some objectKind)
    (objectRefines : objectKind.refines .tobject = true)
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (callFound : callIndex? sourceModule
      (.runtime (.dec amount check objectFields?)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (decrementContract amount check objectFields?))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.dec objectId amount check false objectFields? continuation) continuation
        ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
        (replaceHeap initial heap) locals witness witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness := by
  have sourceLookup : lookup sourceEnv objectId = some sourceObject := by
    unfold lookupValue at objectLookup
    split at objectLookup
    · rename_i value found
      injection objectLookup with valueEq
      subst value
      exact found
    · contradiction
  obtain ⟨physical, hObject, physicalRelated⟩ :=
    initialRelated.resolve sourceLookup objectFound kindAt
  have tobjectRelated := physicalRelated.toTObject objectRefines
  cases tobjectRelated with
  | word32 objectRelated =>
      obtain ⟨heap, operation, runtimeRelated, cursor, capacity⟩ :=
        decrementStep_of_refines_with_capacity initialRelated.1 objectRelated
          descriptorsEq updated
      refine ⟨heap, ?_, cursor, capacity⟩
      apply effectStepSimulates_unaryHost
        (step := decrementStep amount check objectFields?)
      · intro externals
        simp [executeStep, coreStep, objectLookup, updated]
      · exact codeAdapted_dec objectCompiled objectFound callFound
          continuationAdapted
      · exact initialRelated
      · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
          initialRelated.2.2⟩
      · exact hObject
      · exact hImp
      · exact hSat
      · exact hi
      · exact hContract
      · exact hParams
      · exact hResults
      · exact operation
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

theorem effectStepSimulates_dec
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    {objectKind : AbiKind}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {sourceObject : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : decValue sourceRuntime sourceObject amount check = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, objectKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (kindAt : (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
      some objectKind)
    (objectRefines : objectKind.refines .tobject = true)
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (callFound : callIndex? sourceModule
      (.runtime (.dec amount check objectFields?)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (decrementContract amount check objectFields?))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.dec objectId amount check false objectFields? continuation) continuation
        ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
        (replaceHeap initial heap) locals witness witness := by
  obtain ⟨heap, step, _, _⟩ :=
    effectStepSimulates_dec_with_capacity objectLookup updated initialRelated
      objectCompiled objectFound kindAt objectRefines descriptorsEq callFound
      continuationAdapted hImp hSat hi hContract hParams hResults
  exact ⟨heap, step⟩

/-- Persistent decrements are source and concrete control-flow no-ops. -/
theorem effectStepSimulates_dec_persistent
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {sourceRuntime : RuntimeState} {targetRest : Wasm.Program}
    {witness : RefinementWitness}
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceRuntime sourceEnv
      (.dec objectId amount check true objectFields? continuation) continuation
      targetRest targetRest initial initial locals witness witness := by
  apply effectStepSimulates_elided
  · intro externals
    simp [executeStep, coreStep]
  · exact codeAdapted_dec_persistent continuationAdapted
  · exact initialRelated

/-- Explicit deletion composed through the source evaluator, compiler and
adapter, concrete canonical-header update, and generated unary host call. The
same theorem admits the erased/zero no-op only through its exact `.erased`
value relation. -/
theorem effectStepSimulates_delete_with_capacity
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {objectKind : AbiKind}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {sourceObject : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : deleteValue sourceRuntime sourceObject = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, objectKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (kindAt : (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
      some objectKind)
    (callFound : callIndex? sourceModule (.runtime .delete) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some deleteContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv (.del objectId continuation)
        continuation ([.localGet objectIndex, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  have sourceLookup : lookup sourceEnv objectId = some sourceObject := by
    unfold lookupValue at objectLookup
    split at objectLookup
    · rename_i value found
      injection objectLookup with valueEq
      subst value
      exact found
    · contradiction
  obtain ⟨physical, hObject, physicalRelated⟩ :=
    initialRelated.resolve sourceLookup objectFound kindAt
  cases physicalRelated with
  | word32 valueRelated =>
      obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
        deleteStep_of_refines_with_capacity initialRelated.1 valueRelated updated
      refine ⟨heap, ?_, capacity, cursor⟩
      apply effectStepSimulates_unaryHost (step := deleteStep)
      · intro externals
        simp [executeStep, coreStep, objectLookup, updated]
      · exact codeAdapted_delete objectCompiled objectFound callFound
          continuationAdapted
      · exact initialRelated
      · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
          initialRelated.2.2⟩
      · exact hObject
      · exact hImp
      · exact hSat
      · exact hi
      · exact hContract
      · exact hParams
      · exact hResults
      · exact operation
  | word64 valueRelated =>
      cases valueRelated <;> simp [deleteValue] at updated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

theorem effectStepSimulates_delete
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {objectKind : AbiKind}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {sourceObject : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : deleteValue sourceRuntime sourceObject = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, objectKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (kindAt : (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
      some objectKind)
    (callFound : callIndex? sourceModule (.runtime .delete) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some deleteContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv (.del objectId continuation)
        continuation ([.localGet objectIndex, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness := by
  obtain ⟨heap, step, _, _⟩ :=
    effectStepSimulates_delete_with_capacity objectLookup updated initialRelated
      objectCompiled objectFound kindAt callFound continuationAdapted hImp hSat hi
      hContract hParams hResults
  exact ⟨heap, step⟩

/-- Constructor-tag mutation composed through the source evaluator, real
compiler and adapter, concrete header writer, and exact unary host-call prefix.
The explicit live-constructor facts are precisely the semantic and concrete
decoder obligations needed by the complete-heap refinement theorem. -/
theorem effectStepSimulates_setTag_with_capacity
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {location : Location} {cell : HeapCell}
    {semantic : ConstructorObject}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (updated : setTag sourceRuntime (.object (.heap location)) tag =
      .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (kindAt : (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
      some .object)
    (callFound : callIndex? sourceModule (.runtime (.setTag tag)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (setTagContract tag))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (tagFits : tag < UInt32.size) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.setTag objectId tag continuation) continuation
        ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
        (replaceHeap initial heap) locals witness witness ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  have sourceLookup : lookup sourceEnv objectId =
      some (.object (.heap location)) := by
    unfold lookupValue at objectLookup
    split at objectLookup
    · rename_i value foundLookup
      injection objectLookup with valueEq
      subst value
      exact foundLookup
    · contradiction
  obtain ⟨physical, hObject, physicalRelated⟩ :=
    initialRelated.resolve sourceLookup objectFound kindAt
  cases physicalRelated with
  | word32 objectRelated =>
      obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
        setTagStep_of_refines_with_capacity initialRelated.1 objectRelated found
          live objectEq updated tagFits
      refine ⟨heap, ?_, capacity, cursor⟩
      apply effectStepSimulates_unaryHost (step := setTagStep tag)
      · intro externals
        simp [executeStep, coreStep, objectLookup, updated]
      · exact codeAdapted_setTag objectCompiled objectFound callFound
          continuationAdapted
      · exact initialRelated
      · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
          initialRelated.2.2⟩
      · exact hObject
      · exact hImp
      · exact hSat
      · exact hi
      · exact hContract
      · exact hParams
      · exact hResults
      · exact operation
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

theorem effectStepSimulates_setTag
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {location : Location} {cell : HeapCell}
    {semantic : ConstructorObject}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (updated : setTag sourceRuntime (.object (.heap location)) tag =
      .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (kindAt : (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
      some .object)
    (callFound : callIndex? sourceModule (.runtime (.setTag tag)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (setTagContract tag))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (tagFits : tag < UInt32.size) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.setTag objectId tag continuation) continuation
        ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
        (replaceHeap initial heap) locals witness witness := by
  obtain ⟨heap, step, _, _⟩ :=
    effectStepSimulates_setTag_with_capacity objectLookup updated initialRelated
      objectCompiled objectFound kindAt callFound continuationAdapted hImp hSat hi
      hContract hParams hResults found live objectEq tagFits
  exact ⟨heap, step⟩

/-- FVar object-field mutation composed through exact compiler-assigned i32
locals, the real compiler and adapter, the checked concrete slot writer, and
the generated binary host-call prefix. -/
theorem effectStepSimulates_objectSet_with_capacity
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {location : Location} {cell : HeapCell}
    {objectWord : Word32}
    {semantic : ConstructorObject} {field : Value} {fieldKind : AbiKind}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok field)
    (updated : setObjectField sourceRuntime (.object (.heap location)) index
      field = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.compileArg context (.fvar fieldId) =
      .ok ([.localGet fieldId], fieldKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (fieldLocalKindAt :
      (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd = some fieldKind)
    (fieldObjectKind : fieldKind.isObjectField = true)
    (callFound : callIndex? sourceModule
      (.runtime (.objectSet index fieldKind)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (objectSetContract index fieldKind))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (indexValid : index < semantic.objectFields.size)
    (fieldDescriptorKindAt : fieldKinds[index]? = some fieldKind) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.oset objectId index (.fvar fieldId) continuation) continuation
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  have fieldSourceLookup : lookup sourceEnv fieldId = some field := by
    unfold lookupValue at fieldLookup
    split at fieldLookup
    · rename_i value foundLookup
      injection fieldLookup with valueEq
      subst value
      exact foundLookup
    · contradiction
  obtain ⟨physicalField, hField, physicalFieldRelated⟩ :=
    initialRelated.resolve fieldSourceLookup fieldFound fieldLocalKindAt
  cases physicalFieldRelated with
  | word32 fieldRelated =>
      obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
        objectSetStep_of_refines_with_capacity initialRelated.1 objectRelated
          fieldRelated found live objectEq descriptorFound indexValid
          fieldDescriptorKindAt updated
      refine ⟨heap, ?_, capacity, cursor⟩
      apply effectStepSimulates_binaryHost
        (step := objectSetStep index fieldKind)
      · intro externals
        change evalArg sourceEnv (.fvar fieldId) = .ok field at fieldLookup
        simp [executeStep, coreStep, objectLookup, fieldLookup, updated]
      · apply codeAdapted_oset (targetField := [.localGet fieldIndex])
          objectCompiled fieldCompiled objectFound
        · apply instructions_localGets (fvarIds := [fieldId])
            (indices := [fieldIndex])
          exact .cons (by simpa [functionBindings] using fieldFound) .nil
        · exact callFound
        · exact continuationAdapted
      · exact initialRelated
      · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
          initialRelated.2.2⟩
      · exact hObject
      · exact hField
      · exact hImp
      · exact hSat
      · exact hi
      · exact hContract
      · exact hParams
      · exact hResults
      · exact operation
  | word64 fieldRelated =>
      cases fieldRelated <;> simp [AbiKind.isObjectField] at fieldObjectKind
  | float32Bits fieldRelated => cases fieldRelated
  | float64Bits fieldRelated => cases fieldRelated

theorem effectStepSimulates_objectSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {location : Location} {cell : HeapCell}
    {objectWord : Word32}
    {semantic : ConstructorObject} {field : Value} {fieldKind : AbiKind}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok field)
    (updated : setObjectField sourceRuntime (.object (.heap location)) index
      field = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.compileArg context (.fvar fieldId) =
      .ok ([.localGet fieldId], fieldKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (fieldLocalKindAt :
      (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd = some fieldKind)
    (fieldObjectKind : fieldKind.isObjectField = true)
    (callFound : callIndex? sourceModule
      (.runtime (.objectSet index fieldKind)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (objectSetContract index fieldKind))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (indexValid : index < semantic.objectFields.size)
    (fieldDescriptorKindAt : fieldKinds[index]? = some fieldKind) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.oset objectId index (.fvar fieldId) continuation) continuation
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness := by
  obtain ⟨heap, step, _, _⟩ :=
    effectStepSimulates_objectSet_with_capacity objectLookup fieldLookup updated
      initialRelated hObject objectRelated objectCompiled fieldCompiled
      objectFound fieldFound fieldLocalKindAt fieldObjectKind callFound
      continuationAdapted hImp hSat hi hContract hParams hResults found live
      objectEq descriptorFound indexValid fieldDescriptorKindAt
  exact ⟨heap, step⟩

/-- Erased object-field mutation composed through the compiler's canonical
wasm32 zero, the real adapter, the checked concrete slot writer, and the
generated local/constant host-call prefix. This closes the non-FVar branch of
`LCNF.Arg` without treating an ordinary object word as an erased sentinel. -/
theorem effectStepSimulates_objectSet_erased_with_capacity
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {location : Location} {cell : HeapCell}
    {objectWord : Word32} {semantic : ConstructorObject}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (updated : setObjectField sourceRuntime (.object (.heap location)) index
      .erased = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.objectSet index .erased)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (objectSetContract index .erased))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (indexValid : index < semantic.objectFields.size)
    (fieldDescriptorKindAt : fieldKinds[index]? = some .erased) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.oset objectId index .erased continuation) continuation
        ([.localGet objectIndex, .const 0, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  have fieldRelated :
      ValueRel witness .erased (.word32 Word32.zero) .erased := .erased
  obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
    objectSetStep_of_refines_with_capacity initialRelated.1 objectRelated
      fieldRelated found live objectEq descriptorFound indexValid
      fieldDescriptorKindAt updated
  refine ⟨heap, ?_, capacity, cursor⟩
  apply effectStepSimulates_localI32ConstHost
    (step := objectSetStep index .erased)
  · intro externals
    simp [executeStep, coreStep, evalArg, objectLookup, updated]
  · apply codeAdapted_oset
      (arg := .erased) (fieldCode := [.i32Const .erased 0])
      (targetField := [.const 0]) objectCompiled (by rfl) objectFound
    · simp [instructions, instruction, pure, Except.pure, Bind.bind,
        Except.bind]
    · exact callFound
    · exact continuationAdapted
  · exact initialRelated
  · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
      initialRelated.2.2⟩
  · exact hObject
  · exact hImp
  · exact hSat
  · exact hi
  · exact hContract
  · exact hParams
  · exact hResults
  · simpa [Word32.zero] using operation

theorem effectStepSimulates_objectSet_erased
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {location : Location} {cell : HeapCell}
    {objectWord : Word32} {semantic : ConstructorObject}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (updated : setObjectField sourceRuntime (.object (.heap location)) index
      .erased = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.objectSet index .erased)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (objectSetContract index .erased))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (indexValid : index < semantic.objectFields.size)
    (fieldDescriptorKindAt : fieldKinds[index]? = some .erased) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.oset objectId index .erased continuation) continuation
        ([.localGet objectIndex, .const 0, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness := by
  obtain ⟨heap, step, _, _⟩ :=
    effectStepSimulates_objectSet_erased_with_capacity objectLookup updated
      initialRelated hObject objectRelated objectCompiled objectFound callFound
      continuationAdapted hImp hSat hi hContract hParams hResults found live
      objectEq descriptorFound indexValid fieldDescriptorKindAt
  exact ⟨heap, step⟩

/-- `USize`-field mutation composed through exact compiler-assigned i32/i64
locals, the real compiler and adapter, checked concrete slot writer, and the
generated binary host-call prefix. -/
theorem effectStepSimulates_usizeSet_with_capacity
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {location : Location} {cell : HeapCell}
    {semantic : ConstructorObject} {field : UInt64}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.usize field))
    (updated : setUSizeSlot sourceRuntime (.object (.heap location)) index
      (.usize field) = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.getLocal context fieldId =
      .ok (.localGet fieldId, .usize))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (objectKindAt :
      (functionBindings sourceFunction)[objectIndex]?.map Prod.snd = some .object)
    (fieldKindAt :
      (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd = some .usize)
    (callFound : callIndex? sourceModule (.runtime (.usizeSet index)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (usizeSetContract index))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (slotStart : semantic.objectFields.size ≤ index)
    (slotEnd : index < semantic.objectFields.size + semantic.usizeFields.size) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.uset objectId index fieldId continuation) continuation
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  have objectSourceLookup : lookup sourceEnv objectId =
      some (.object (.heap location)) := by
    unfold lookupValue at objectLookup
    split at objectLookup
    · rename_i value foundLookup
      injection objectLookup with valueEq
      subst value
      exact foundLookup
    · contradiction
  have fieldSourceLookup : lookup sourceEnv fieldId = some (.usize field) := by
    unfold lookupValue at fieldLookup
    split at fieldLookup
    · rename_i value foundLookup
      injection fieldLookup with valueEq
      subst value
      exact foundLookup
    · contradiction
  obtain ⟨physicalObject, hObject, physicalObjectRelated⟩ :=
    initialRelated.resolve objectSourceLookup objectFound objectKindAt
  obtain ⟨physicalField, hField, physicalFieldRelated⟩ :=
    initialRelated.resolve fieldSourceLookup fieldFound fieldKindAt
  cases physicalObjectRelated with
  | word32 objectRelated =>
      cases physicalFieldRelated with
      | word64 fieldRelated =>
          cases fieldRelated with
          | usize =>
              obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
                usizeSetStep_of_refines_with_capacity initialRelated.1
                  objectRelated found live objectEq slotStart slotEnd updated
              refine ⟨heap, ?_, capacity, cursor⟩
              apply effectStepSimulates_binaryHost (step := usizeSetStep index)
              · intro externals
                simp [executeStep, coreStep, objectLookup, fieldLookup, updated]
              · exact codeAdapted_uset objectCompiled fieldCompiled objectFound
                  fieldFound callFound continuationAdapted
              · exact initialRelated
              · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
                  initialRelated.2.2⟩
              · exact hObject
              · exact hField
              · exact hImp
              · exact hSat
              · exact hi
              · exact hContract
              · exact hParams
              · exact hResults
              · exact operation
      | word32 fieldRelated => cases fieldRelated
      | float32Bits fieldRelated => cases fieldRelated
      | float64Bits fieldRelated => cases fieldRelated
  | word64 objectRelated => cases objectRelated
  | float32Bits objectRelated => cases objectRelated
  | float64Bits objectRelated => cases objectRelated

theorem effectStepSimulates_usizeSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {location : Location} {cell : HeapCell}
    {semantic : ConstructorObject} {field : UInt64}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.usize field))
    (updated : setUSizeSlot sourceRuntime (.object (.heap location)) index
      (.usize field) = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.getLocal context fieldId =
      .ok (.localGet fieldId, .usize))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (objectKindAt :
      (functionBindings sourceFunction)[objectIndex]?.map Prod.snd = some .object)
    (fieldKindAt :
      (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd = some .usize)
    (callFound : callIndex? sourceModule (.runtime (.usizeSet index)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (usizeSetContract index))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (slotStart : semantic.objectFields.size ≤ index)
    (slotEnd : index < semantic.objectFields.size + semantic.usizeFields.size) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.uset objectId index fieldId continuation) continuation
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness := by
  obtain ⟨heap, step, _, _⟩ :=
    effectStepSimulates_usizeSet_with_capacity objectLookup fieldLookup updated
      initialRelated objectCompiled fieldCompiled objectFound fieldFound
      objectKindAt fieldKindAt callFound continuationAdapted hImp hSat hi
      hContract hParams hResults found live objectEq slotStart slotEnd
  exact ⟨heap, step⟩

/-- Packed-integer field mutation composed through exact compiler-assigned
locals, the real compiler and adapter, the width-indexed concrete writer, and
the generated binary host-call prefix. Every supported packed-integer write
preserves each retained field whose byte interval is disjoint. -/
theorem effectStepSimulates_scalarSet_with_capacity
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr} {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {objectWord : Word32}
    {location : Location} {cell : HeapCell} {semantic : ConstructorObject}
    {field : ScalarValue} {fieldKind : AbiKind}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.scalar field))
    (updated : setScalarField sourceRuntime (.object (.heap location)) slotIndex
      byteOffset (.scalar field) = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.getLocal context fieldId =
      .ok (.localGet fieldId, fieldKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (fieldKindAt :
      (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd = some fieldKind)
    (callFound : callIndex? sourceModule
      (.runtime (.scalarSet slotIndex byteOffset fieldKind)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (scalarSetContract slotIndex byteOffset fieldKind))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (historySafe : match fieldKind with
      | .uint8 => ∀ old ∈ semantic.scalarFields,
          old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
          old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
            byteOffset + 1 ≤ old.offset
      | .uint16 => ∀ old ∈ semantic.scalarFields,
          old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
          old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
            byteOffset + 2 ≤ old.offset
      | .uint32 => ∀ old ∈ semantic.scalarFields,
          old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
          old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
            byteOffset + 4 ≤ old.offset
      | .uint64 => ∀ old ∈ semantic.scalarFields,
          old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
          old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
            byteOffset + 8 ≤ old.offset
      | _ => semantic.scalarFields.filter (fun old =>
          old.width != slotIndex || old.offset != byteOffset) = [])
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : match fieldKind with
      | .uint8 => byteOffset + 1 ≤ info.ssize
      | .uint16 => byteOffset + 2 ≤ info.ssize
      | .uint32 => byteOffset + 4 ≤ info.ssize
      | .uint64 => byteOffset + 8 ≤ info.ssize
      | _ => False) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.sset objectId slotIndex byteOffset fieldId type continuation)
        continuation
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness ∧
      MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
      heap.heapCursor = initial.host.runtime.heap.heapCursor := by
  have fieldSourceLookup : lookup sourceEnv fieldId = some (.scalar field) := by
    unfold lookupValue at fieldLookup
    split at fieldLookup
    · rename_i value foundLookup
      injection fieldLookup with valueEq
      subst value
      exact foundLookup
    · contradiction
  obtain ⟨physicalField, hField, physicalFieldRelated⟩ :=
    initialRelated.resolve fieldSourceLookup fieldFound fieldKindAt
  cases physicalFieldRelated with
  | word32 fieldRelated =>
      cases fieldRelated with
      | uint8 encoded =>
          obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
            scalarSetStep_uint8_of_refines_with_capacity initialRelated.1
              objectRelated (.uint8 encoded) found live objectEq descriptorFound
              (by simpa using historySafe) slotIndexEq
              (by simpa using fieldFits) updated
          refine ⟨heap, ?_, capacity, cursor⟩
          apply effectStepSimulates_binaryHost
            (step := scalarSetStep slotIndex byteOffset .uint8)
          · intro externals
            simp [executeStep, coreStep, objectLookup, fieldLookup, updated]
          · exact codeAdapted_sset objectCompiled fieldCompiled objectFound
              fieldFound callFound continuationAdapted
          · exact initialRelated
          · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              initialRelated.2.2⟩
          · exact hObject
          · exact hField
          · exact hImp
          · exact hSat
          · exact hi
          · exact hContract
          · exact hParams
          · exact hResults
          · exact operation
      | uint16 encoded =>
          obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
            scalarSetStep_uint16_of_refines_with_capacity initialRelated.1
              objectRelated (.uint16 encoded) found live objectEq descriptorFound
              (by simpa using historySafe) slotIndexEq
              (by simpa using fieldFits) updated
          refine ⟨heap, ?_, capacity, cursor⟩
          apply effectStepSimulates_binaryHost
            (step := scalarSetStep slotIndex byteOffset .uint16)
          · intro externals
            simp [executeStep, coreStep, objectLookup, fieldLookup, updated]
          · exact codeAdapted_sset objectCompiled fieldCompiled objectFound
              fieldFound callFound continuationAdapted
          · exact initialRelated
          · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              initialRelated.2.2⟩
          · exact hObject
          · exact hField
          · exact hImp
          · exact hSat
          · exact hi
          · exact hContract
          · exact hParams
          · exact hResults
          · exact operation
      | uint32 encoded =>
          obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
            scalarSetStep_uint32_of_refines_with_capacity initialRelated.1
              objectRelated (.uint32 encoded) found live objectEq descriptorFound
              (by simpa using historySafe) slotIndexEq
              (by simpa using fieldFits) updated
          refine ⟨heap, ?_, capacity, cursor⟩
          apply effectStepSimulates_binaryHost
            (step := scalarSetStep slotIndex byteOffset .uint32)
          · intro externals
            simp [executeStep, coreStep, objectLookup, fieldLookup, updated]
          · exact codeAdapted_sset objectCompiled fieldCompiled objectFound
              fieldFound callFound continuationAdapted
          · exact initialRelated
          · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              initialRelated.2.2⟩
          · exact hObject
          · exact hField
          · exact hImp
          · exact hSat
          · exact hi
          · exact hContract
          · exact hParams
          · exact hResults
          · exact operation
  | word64 fieldRelated =>
      cases fieldRelated with
      | uint64 =>
          obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
            scalarSetStep_uint64_of_refines_with_capacity initialRelated.1
              objectRelated .uint64 found live objectEq descriptorFound
              (by simpa using historySafe) slotIndexEq
              (by simpa using fieldFits) updated
          refine ⟨heap, ?_, capacity, cursor⟩
          apply effectStepSimulates_binaryHost
            (step := scalarSetStep slotIndex byteOffset .uint64)
          · intro externals
            simp [executeStep, coreStep, objectLookup, fieldLookup, updated]
          · exact codeAdapted_sset objectCompiled fieldCompiled objectFound
              fieldFound callFound continuationAdapted
          · exact initialRelated
          · exact ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              initialRelated.2.2⟩
          · exact hObject
          · exact hField
          · exact hImp
          · exact hSat
          · exact hi
          · exact hContract
          · exact hParams
          · exact hResults
          · exact operation
  | float32Bits fieldRelated => cases fieldRelated
  | float64Bits fieldRelated => cases fieldRelated

theorem effectStepSimulates_scalarSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr} {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {objectWord : Word32}
    {location : Location} {cell : HeapCell} {semantic : ConstructorObject}
    {field : ScalarValue} {fieldKind : AbiKind}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {sourceRuntime nextRuntime : RuntimeState}
    {targetRest : Wasm.Program} {witness : RefinementWitness}
    (objectLookup : lookupValue sourceEnv objectId =
      .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.scalar field))
    (updated : setScalarField sourceRuntime (.object (.heap location)) slotIndex
      byteOffset (.scalar field) = .ok nextRuntime)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated : ValueRel witness .object (.word32 objectWord)
      (.object (.heap location)))
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.getLocal context fieldId =
      .ok (.localGet fieldId, fieldKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (fieldKindAt :
      (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd = some fieldKind)
    (callFound : callIndex? sourceModule
      (.runtime (.scalarSet slotIndex byteOffset fieldKind)) = some id)
    (continuationAdapted : CodeAdapted context sourceModule sourceFunction labels
      continuation targetRest)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (scalarSetContract slotIndex byteOffset fieldKind))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (historySafe : match fieldKind with
      | .uint8 => ∀ old ∈ semantic.scalarFields,
          old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
          old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
            byteOffset + 1 ≤ old.offset
      | .uint16 => ∀ old ∈ semantic.scalarFields,
          old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
          old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
            byteOffset + 2 ≤ old.offset
      | .uint32 => ∀ old ∈ semantic.scalarFields,
          old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
          old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
            byteOffset + 4 ≤ old.offset
      | .uint64 => ∀ old ∈ semantic.scalarFields,
          old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
          old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
            byteOffset + 8 ≤ old.offset
      | _ => semantic.scalarFields.filter (fun old =>
          old.width != slotIndex || old.offset != byteOffset) = [])
    (slotIndexEq : slotIndex = info.size + info.usize)
    (fieldFits : match fieldKind with
      | .uint8 => byteOffset + 1 ≤ info.ssize
      | .uint16 => byteOffset + 2 ≤ info.ssize
      | .uint32 => byteOffset + 4 ≤ info.ssize
      | .uint64 => byteOffset + 8 ≤ info.ssize
      | _ => False) :
    ∃ heap,
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv
        (.sset objectId slotIndex byteOffset fieldId type continuation)
        continuation
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
        targetRest initial (replaceHeap initial heap) locals witness witness := by
  obtain ⟨heap, step, _, _⟩ :=
    effectStepSimulates_scalarSet_with_capacity objectLookup fieldLookup updated
      initialRelated hObject objectRelated objectCompiled fieldCompiled
      objectFound fieldFound fieldKindAt callFound continuationAdapted hImp hSat
      hi hContract hParams hResults found live objectEq descriptorFound
      historySafe slotIndexEq fieldFits
  exact ⟨heap, step⟩

/-- Concrete-host WP for generated reset and its reuse-token destination
local. The result word is zero on tagged/fallback paths and the original heap
address on the unique constructor path. -/
theorem wp_reset_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {count : Nat}
    {objectWord token : Word32} (tail : List Wasm.Value)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (resetContract count))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : resetStep count initial
      [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [.i32 (UInt32.ofNat token.value)] nextStore)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat token.value)) = some updated)
    (continued : Wasm.wp module rest Q nextStore
      { updated with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := resetStep count)
    (physicalArgs := [.i32 (UInt32.ofNat objectWord.value)])
    (results := [.i32 (UInt32.ofNat token.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) targetSet continued

/-- Concrete-host WP for the exact arbitrary-arity reuse sequence emitted by
the lowerer: token and fields are loaded in source order, followed by the host
call and result-local write. -/
theorem wp_reuse_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {word : Word32}
    (tail : List Wasm.Value)
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (reuseContract info updateHeader fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : reuseStep info updateHeader fieldKinds resultKind initial
      physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet : locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
      some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_exact_host_call_of_return
    (step := reuseStep info updateHeader fieldKinds resultKind)
    (physicalArgs := physicalArgs)
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/--
Concrete-host WP for the complete reuse operand prefix emitted by production
lowering: one token local followed by mixed local/erased constructor fields.
-/
theorem wp_reuse_ready_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest targetArguments : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {word : Word32}
    (tail : List Wasm.Value)
    (ready : ConstructorArgsReady locals targetArguments physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (reuseContract info updateHeader fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : reuseStep info updateHeader fieldKinds resultKind initial
      physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet : locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
      some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module
      (targetArguments ++ .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply ready.wp
  apply wp_exact_host_call_of_return
    (step := reuseStep info updateHeader fieldKinds resultKind)
    (physicalArgs := physicalArgs)
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- Concrete-host WP for generated integer boxing and its object destination
local. -/
theorem wp_box_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {scalarIndex resultIndex : Nat} {kind : BoxedScalarKind}
    {scalar : BoxedScalar} {heap : MemoryState} {word : Word32}
    (tail : List Wasm.Value)
    (hScalar : locals.get scalarIndex = some (physicalOfLane scalar.lane))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (boxContract kind .tobject))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : boxStep kind .tobject initial
      [physicalOfLane scalar.lane] =
        .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap initial heap))
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : Wasm.wp module rest Q (replaceHeap initial heap)
      { updated with values := tail } env) :
    Wasm.wp module
      (.localGet scalarIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  have hScalarTail :
      ({ locals with values := tail } : Wasm.Locals).get scalarIndex =
        some (physicalOfLane scalar.lane) := by
    simpa [Wasm.Locals.get] using hScalar
  rw [Wasm.wp_localGet_cons, hScalarTail]
  apply wp_exact_host_call_of_return
    (step := boxStep kind .tobject)
    (physicalArgs := [physicalOfLane scalar.lane])
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) targetSet continued

/-- Concrete-host WP for generated typed unboxing and its destination-local
write. -/
theorem wp_unbox_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {word : Word32}
    {kind : BoxedScalarKind} {scalar : BoxedScalar}
    {sourceObject : Value} {runtime : RuntimeState}
    {witness : RefinementWitness}
    (tail : List Wasm.Value)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat word.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (unboxContract kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      UnboxObjectRel witness word kind sourceObject)
    (unboxed : unbox runtime kind.semanticType sourceObject =
      .ok scalar.semanticValue)
    (concreteRead : readBoxedScalar initial.host.runtime.heap kind word =
      .ok scalar)
    (targetSet : locals.set? resultIndex (physicalOfLane scalar.lane) =
      some updated)
    (continued : Wasm.wp module rest Q (clearFailure initial)
      { updated with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  obtain ⟨operation, _, _⟩ :=
    unboxStep_of_refines runtimeRelated objectRelated unboxed concreteRead
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat word.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := unboxStep kind)
    (physicalArgs := [.i32 (UInt32.ofNat word.value)])
    (results := [physicalOfLane scalar.lane]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) targetSet continued

/-- Concrete-host WP for the generated sharing observation and direct UInt8
destination write. -/
theorem wp_isShared_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {witness : RefinementWitness} {runtime : RuntimeState}
    {sourceObject : Value} {shared : UInt8}
    (tail : List Wasm.Value)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some isSharedContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (evaluated : isShared runtime sourceObject =
      .ok (.scalar (.uint8 shared)))
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat shared.toNat)) = some updated)
    (continued : Wasm.wp module rest Q (clearFailure initial)
      { updated with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  obtain ⟨operation, _⟩ :=
    isSharedStep_of_refines runtimeRelated objectRelated evaluated
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := isSharedStep)
    (physicalArgs := [.i32 (UInt32.ofNat objectWord.value)])
    (results := [.i32 (UInt32.ofNat shared.toNat)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) targetSet continued

/-- Concrete-host WP for the generated object projection and destination
write. Both the input and result are physical wasm32 words; their meanings are
established only by `ValueRel` and the constructor descriptor. -/
theorem wp_objectProjection_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {witness : RefinementWitness} {runtime : RuntimeState}
    {sourceObject value : Value} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat} {kind : AbiKind}
    (tail : List Wasm.Value)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (fieldKind : fieldKinds[index]? = some kind)
    (projected : getObjectField runtime sourceObject index = .ok value)
    (hSet :
      ∀ word,
        readObjectField initial.host.runtime.heap objectWord index = .ok word →
        ValueRel witness kind (.word32 word) value →
        ∃ nextLocals,
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
            some nextLocals ∧
          Wasm.wp module rest Q (clearFailure initial)
            { nextLocals with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  obtain ⟨word, read, operation, valueRelated⟩ :=
    objectProjStep_of_refines runtimeRelated objectRelated descriptor fieldKind
      projected
  obtain ⟨nextLocals, targetSet, continued⟩ :=
    hSet word read valueRelated
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := objectProjStep index)
    (physicalArgs := [.i32 (UInt32.ofNat objectWord.value)])
    (results := [.i32 (UInt32.ofNat word.value)])
    hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) targetSet continued

theorem wp_usizeProjection_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {witness : RefinementWitness} {runtime : RuntimeState}
    {sourceObject : Value} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat} {value : UInt64}
    (tail : List Wasm.Value)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeSlot runtime sourceObject index = .ok (.usize value))
    (hSet : locals.set? resultIndex (.i64 value) = some updated)
    (continued :
      Wasm.wp module rest Q (clearFailure initial)
        { updated with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  obtain ⟨_, operation, _⟩ :=
    usizeProjStep_of_refines runtimeRelated objectRelated descriptor projected
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := usizeProjStep index)
    (physicalArgs := [.i32 (UInt32.ofNat objectWord.value)])
    (results := [.i64 value]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

theorem wp_scalarProjection_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {width offset : Nat} {kind : AbiKind} {physical : Wasm.Value}
    (tail : List Wasm.Value)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (scalarProjContract width offset kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation :
      scalarProjStep width offset kind initial
          [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [physical] (clearFailure initial))
    (hSet : locals.set? resultIndex physical = some updated)
    (continued :
      Wasm.wp module rest Q (clearFailure initial)
        { updated with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := scalarProjStep width offset kind)
    (physicalArgs := [.i32 (UInt32.ofNat objectWord.value)])
    (results := [physical]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

theorem wp_naturalLiteral_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : Nat} {word : Word32}
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (naturalLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (operation : naturalLiteralStep value initial [] =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module (.call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_exact_host_call_of_return
    (step := naturalLiteralStep value) (physicalArgs := [])
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

theorem wp_stringLiteral_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : String} {word : Word32}
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (stringLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (operation : stringLiteralStep value initial [] =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module (.call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_exact_host_call_of_return
    (step := stringLiteralStep value) (physicalArgs := [])
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- Concrete-host WP for the exact arbitrary-arity constructor sequence
emitted by the lowerer. -/
theorem wp_allocCtor_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind} {word : Word32}
    (tail : List Wasm.Value)
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet : locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
      some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_exact_host_call_of_return
    (step := allocCtorStep info fieldKinds resultKind)
    (physicalArgs := physicalArgs)
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- Concrete-host WP for the full mixed local/erased constructor prefix. -/
theorem wp_allocCtor_ready_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest targetArguments : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind} {word : Word32}
    (tail : List Wasm.Value)
    (ready : ConstructorArgsReady locals targetArguments physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet : locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
      some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module
      (targetArguments ++ .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply ready.wp
  apply wp_exact_host_call_of_return
    (step := allocCtorStep info fieldKinds resultKind)
    (physicalArgs := physicalArgs)
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- Concrete-host WP for the exact generated external-call sequence: load
every physical argument, invoke the resolved concrete foreign function, bind
its singleton result, and restore the caller's operand tail. -/
theorem wp_external_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {physicalResult : Wasm.Value}
    (operation : ExternalOperation) (resultKind : AbiKind)
    (tail : List Wasm.Value)
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (externalContract operation resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operationStep : externalStep operation resultKind initial physicalArgs =
      .Return [physicalResult] nextStore)
    (targetSet : locals.set? resultIndex physicalResult = some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_exact_host_call_of_return
    (step := externalStep operation resultKind)
    (physicalArgs := physicalArgs) (results := [physicalResult])
    hImp hSat hi hContract
  · simp [hParams]
  · exact operationStep
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) targetSet continued

/--
Concrete-host WP for the complete mixed local/erased argument prefix produced
by `compileArgs`, followed by one resolved external call and destination write.
-/
theorem wp_external_ready_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest targetArguments : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {physicalResult : Wasm.Value}
    (operation : ExternalOperation) (resultKind : AbiKind)
    (tail : List Wasm.Value)
    (ready : ConstructorArgsReady locals targetArguments physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (externalContract operation resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operationStep : externalStep operation resultKind initial physicalArgs =
      .Return [physicalResult] nextStore)
    (targetSet : locals.set? resultIndex physicalResult = some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module
      (targetArguments ++ .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply ready.wp
  apply wp_exact_host_call_of_return
    (step := externalStep operation resultKind)
    (physicalArgs := physicalArgs) (results := [physicalResult])
    hImp hSat hi hContract
  · simp [hParams]
  · exact operationStep
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) targetSet continued

/-- Compose one pair of related concrete/source foreign responses through the
generated external-call prefix and destination-local write. The source call,
concrete call, and response relation remain explicit contractual premises. -/
theorem externalLetStepSimulates_of_call
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {indices : List Nat}
    {witness afterWitness : RefinementWitness}
    (operation : ExternalOperation) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (concreteArgs : List LaneValue)
    (semanticArgs : Array Value)
    (semanticImplementation : ExternalImpl)
    (concreteResponse : ConcreteExternalResponse)
    (semanticResponse : ExternalResponse)
    (sourceStep : SourceExternalLetResult context semanticImplementation
      sourceRuntime sourceEnv decl continuation
      (semanticExternalRuntimeAfter (operation.request semanticArgs)
        sourceRuntime semanticResponse)
      semanticResponse.value)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (externalContract operation resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (requestRelated : ConcreteExternalRequestRel witness
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      (operation.request semanticArgs))
    (concreteCalled : initial.host.externals.call
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      initial.host.runtime = .ok concreteResponse)
    (semanticCalled : semanticImplementation.call
      (operation.request semanticArgs) sourceRuntime = .ok semanticResponse)
    (responseRelated : ConcreteExternalResponseRel witness afterWitness
      (operation.request semanticArgs) sourceRuntime resultKind
      concreteResponse semanticResponse)
    (targetSet : locals.set? resultIndex
      (physicalOfLane concreteResponse.value) = some updated) :
    ExternalLetStepSimulates context sourceFunction module hostEnv
      semanticImplementation decl continuation
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      sourceRuntime
      (semanticExternalRuntimeAfter (operation.request semanticArgs)
        sourceRuntime semanticResponse)
      sourceEnv semanticResponse.value initial
      (replaceRuntime initial
        (initial.host.runtime.applyExternalResponse
          (concreteExternalRequest operation resultKind concreteArgs.toArray)
          concreteResponse))
      locals updated resultIndex witness afterWitness := by
  obtain ⟨operationStep, _, nextRuntimeRelated, valueRelated⟩ :=
    externalStep_of_refines operation resultKind initial physicalArgs
      concreteArgs semanticArgs witness sourceRuntime semanticImplementation
      afterWitness concreteResponse semanticResponse decoded initialRelated.1
      requestRelated concreteCalled semanticCalled responseRelated
  have failureClear :
      (replaceRuntime initial
        (initial.host.runtime.applyExternalResponse
          (concreteExternalRequest operation resultKind concreteArgs.toArray)
          concreteResponse)).host.failure? = none := by
    simp [replaceRuntime, clearFailure]
  have nextState := initialRelated.bindAfter
    responseRelated.witnessExtension nextRuntimeRelated failureClear
    resultFound resultKindAt valueRelated targetSet
  refine ⟨sourceStep, initialRelated, nextState, ?_⟩
  intro rest Q tail continued
  simpa [List.append_assoc] using
    (wp_external_let operation resultKind tail hGets hImp hSat hi hContract
      hParams hResults operationStep targetSet continued)

/-- Concrete-host WP for the value-preserving cache update call. -/
theorem wp_cacheSet_call
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial after : Wasm.Store Host} {locals : Wasm.Locals}
    {declaration : Lean.Name} {kind : AbiKind} {physical : Wasm.Value}
    {tail : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (cacheSetContract declaration kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : cacheSetStep declaration kind initial [physical] =
      .Return [physical] after)
    (continued : Wasm.wp module rest Q after
      { locals with values := physical :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial
      { locals with values := physical :: tail } env := by
  apply wp_exact_host_call_of_return
    (step := cacheSetStep declaration kind) (physicalArgs := [physical])
    (results := [physical]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using continued

/-- Atomic store update performed by one generated Wasm `global.set`. -/
def writeWasmGlobal (store : Wasm.Store Host) (index : Nat)
    (value : Wasm.Value) : Wasm.Store Host :=
  { store with globals := { globals := store.globals.globals.set index value } }

/-- A generated `global.set` writes the selected, already allocated global. -/
theorem writeWasmGlobal_get_self
    {store : Wasm.Store Host} {index : Nat}
    {old value : Wasm.Value}
    (found : store.globals.globals[index]? = some old) :
    (writeWasmGlobal store index value).globals.globals[index]? = some value := by
  simp only [writeWasmGlobal]
  exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1

/-- A generated `global.set` preserves every distinct global. -/
theorem writeWasmGlobal_get_ne
    {store : Wasm.Store Host} {written read : Nat} {value : Wasm.Value}
    (different : written ≠ read) :
    (writeWasmGlobal store written value).globals.globals[read]? =
      store.globals.globals[read]? := by
  simp only [writeWasmGlobal]
  rw [List.getElem?_set_ne different]

/-- Exact generated cache-write suffix after a lazy declaration has left its
result on the operand stack. The host cache and the two physical Wasm globals
are updated in their distinct stores. -/
theorem wp_cacheSet_miss_suffix
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial afterCache valueStore : Wasm.Store Host} {locals : Wasm.Locals}
    {declaration : Lean.Name} {kind : AbiKind} {physical : Wasm.Value}
    {valueIndex flagIndex : Nat} {oldValue oldFlag : Wasm.Value}
    {tail : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (cacheSetContract declaration kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : cacheSetStep declaration kind initial [physical] =
      .Return [physical] afterCache)
    (hValue : afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq : valueStore = writeWasmGlobal afterCache valueIndex physical)
    (hFlag : valueStore.globals.globals[flagIndex]? = some oldFlag)
    (continued : Wasm.wp module rest Q
      (writeWasmGlobal valueStore flagIndex (.i32 1))
      { locals with values := tail } env) :
    Wasm.wp module
      (.call id :: .globalSet valueIndex :: .const 1 ::
        .globalSet flagIndex :: rest)
      Q initial { locals with values := physical :: tail } env := by
  subst valueStore
  apply wp_cacheSet_call hImp hSat hi hContract hParams hResults operation
  rw [Wasm.wp_globalSet_cons, hValue]
  change Wasm.wp module (.const 1 :: .globalSet flagIndex :: rest) Q
    (writeWasmGlobal afterCache valueIndex physical)
    { locals with values := tail } env
  rw [Wasm.wp_const_cons, Wasm.wp_globalSet_cons, hFlag]
  exact continued

/-- Assemble the exact generated lazy-miss block from a terminating
zero-argument declaration call, the concrete cache host call, and the two
physical Wasm global writes. The result-global write is preserved across the
distinct flag-global write before the surrounding cache path reloads it. -/
theorem lazyMissBodySimulates_of_call_cacheSet
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {declarationId cacheSetId : Nat} {imp : Wasm.ImportDecl}
    {declaration : Lean.Name} {kind : AbiKind}
    {targetStore afterCall afterCache valueStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {physical oldValue oldFlag : Wasm.Value}
    {valueIndex flagIndex resultIndex : Nat}
    (declarationCall : ∀ tail,
      Wasm.TerminatesWith env module declarationId targetStore tail
        (fun final results =>
          final = afterCall ∧ results = physical :: tail))
    (hImp : module.imports[cacheSetId]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : cacheSetId < module.imports.length)
    (hContract : spec.contracts[cacheSetId]? =
      some (cacheSetContract declaration kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : cacheSetStep declaration kind afterCall [physical] =
      .Return [physical] afterCache)
    (hValue : afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq : valueStore =
      writeWasmGlobal afterCache valueIndex physical)
    (hFlag : valueStore.globals.globals[flagIndex]? = some oldFlag)
    (different : valueIndex ≠ flagIndex)
    (hSet : targetLocals.set? resultIndex physical = some nextLocals) :
    LazyMissBodySimulates module env
      [.call declarationId, .call cacheSetId, .globalSet valueIndex,
        .const 1, .globalSet flagIndex]
      valueIndex resultIndex targetStore
      (writeWasmGlobal valueStore flagIndex (.i32 1))
      targetLocals nextLocals := by
  intro rest Q tail continued
  apply Wasm.wp_call_tw (declarationCall tail)
  intro final results callPost
  rcases callPost with ⟨rfl, rfl⟩
  apply wp_cacheSet_miss_suffix hImp hSat hi hContract hParams hResults
    operation hValue valueStoreEq hFlag
  rw [Wasm.wp_nil]
  have valueAtValueStore :
      valueStore.globals.globals[valueIndex]? = some physical := by
    rw [valueStoreEq]
    exact writeWasmGlobal_get_self hValue
  have valueAtFinal :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).globals.globals[valueIndex]? =
        some physical := by
    rw [writeWasmGlobal_get_ne different.symm]
    exact valueAtValueStore
  change Wasm.wp module
    (.globalGet valueIndex :: .localSet resultIndex :: rest) Q
    (writeWasmGlobal valueStore flagIndex (.i32 1))
    { targetLocals with values := tail } env
  rw [Wasm.wp_globalGet_cons, valueAtFinal]
  simpa using wp_localSet_of_set hSet continued

/-- Concrete-host lazy-cache hit: skip the miss block and load the populated
value global without changing host or Wasm state. -/
theorem wp_lazy_cache_hit
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {missBody rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {store : Wasm.Store Host} {locals : Wasm.Locals}
    {flagIndex valueIndex : Nat} {cached : Wasm.Value}
    {tail : List Wasm.Value}
    (hFlag : store.globals.globals[flagIndex]? = some (.i32 1))
    (hValue : store.globals.globals[valueIndex]? = some cached)
    (continued :
      Wasm.wp module rest Q store { locals with values := cached :: tail } env) :
    Wasm.wp module
      (.globalGet flagIndex :: .iff 0 0 [] missBody ::
        .globalGet valueIndex :: rest)
      Q store { locals with values := tail } env := by
  rw [Wasm.wp_globalGet_cons, hFlag]
  apply Wasm.wp_iff_cons (c := 1) (vs := tail) rfl
  simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp [hValue, continued]

/-- Concrete-host lazy-cache miss: select a supplied proof for the declaration
call/cache-write block, then load the newly populated value global. -/
theorem wp_lazy_cache_miss
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {missBody rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {store : Wasm.Store Host} {locals : Wasm.Locals}
    {flagIndex valueIndex : Nat} {tail : List Wasm.Value}
    (hFlag : store.globals.globals[flagIndex]? = some (.i32 0))
    (hBody :
      Wasm.wp module missBody
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module (.globalGet valueIndex :: rest) Q nextStore
                { nextLocals with values := tail } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module (.globalGet valueIndex :: rest) Q nextStore
                { nextLocals with values := tail } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        store { locals with values := tail } env) :
    Wasm.wp module
      (.globalGet flagIndex :: .iff 0 0 [] missBody ::
        .globalGet valueIndex :: rest)
      Q store { locals with values := tail } env := by
  rw [Wasm.wp_globalGet_cons, hFlag]
  apply Wasm.wp_iff_cons (c := 0) (vs := tail) rfl
  convert hBody using 1
  · simp
  · funext continuation
    cases continuation with
    | Break level nextStore nextLocals => cases level <;> rfl
    | _ => rfl

theorem lazyLetStepSimulates_hit
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {missBody : Wasm.Program} {flagIndex valueIndex resultIndex : Nat}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {cached : Wasm.Value}
    {witness nextWitness : RefinementWitness}
    (sourceStep : SourceLazyLetResult .hit context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue)
    (stateRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness)
    (hFlag : targetStore.globals.globals[flagIndex]? = some (.i32 1))
    (hValue : targetStore.globals.globals[valueIndex]? = some cached)
    (hSet : targetLocals.set? resultIndex cached = some nextLocals)
    (nextStoreEq : nextStore = targetStore)
    (nextStateRelated : StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness) :
    LazyLetStepSimulates .hit context sourceFunction module hostEnv externals
      decl continuation
      [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
      targetLocals nextLocals resultIndex witness nextWitness := by
  refine ⟨sourceStep, stateRelated, nextStateRelated, ?_⟩
  intro rest Q tail continued
  subst nextStore
  apply wp_lazy_cache_hit hFlag hValue
  apply wp_localSet_of_set hSet
  exact continued

theorem lazyLetStepSimulates_miss
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {missBody : Wasm.Program} {flagIndex valueIndex resultIndex : Nat}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {witness nextWitness : RefinementWitness}
    (sourceStep : SourceLazyLetResult .miss context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue)
    (stateRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness)
    (hFlag : targetStore.globals.globals[flagIndex]? = some (.i32 0))
    (missStep : LazyMissBodySimulates module hostEnv missBody valueIndex
      resultIndex targetStore nextStore targetLocals nextLocals)
    (nextStateRelated : StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness) :
    LazyLetStepSimulates .miss context sourceFunction module hostEnv externals
      decl continuation
      [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
      targetLocals nextLocals resultIndex witness nextWitness := by
  refine ⟨sourceStep, stateRelated, nextStateRelated, ?_⟩
  intro rest Q tail continued
  apply wp_lazy_cache_miss (rest := .localSet resultIndex :: rest) hFlag
  convert missStep rest Q tail continued using 1

/-- Concrete-host WP for the arbitrary-arity partial-application allocation
and destination-local write emitted by the lowerer. -/
theorem wp_partialApply_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {function : Lean.Name} {arity fixed : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind} {word : Word32}
    {tail : List Wasm.Value}
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (partialApplyContract function arity fixed fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : partialApplyStep function arity fixed fieldKinds resultKind
      initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet : locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
      some updated)
    (continued : Wasm.wp module rest Q nextStore
      { updated with values := tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_exact_host_call_of_return
    (step := partialApplyStep function arity fixed fieldKinds resultKind)
    (physicalArgs := physicalArgs)
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- Exact generated closure-matcher prefix. The returned i32 discriminator is
left on the operand stack for the following generated `if`. -/
theorem wp_closureMatches
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals : Wasm.Locals}
    {closureIndex : Nat} {address : Word32} {matched : UInt32}
    {function : Lean.Name} {arity fixed : Nat} {tail : List Wasm.Value}
    (hClosure : locals.get closureIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (closureMatchesContract function arity fixed))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : closureMatchesStep function arity fixed initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [.i32 matched] nextStore)
    (continued : Wasm.wp module rest Q nextStore
      { locals with values := .i32 matched :: tail } env) :
    Wasm.wp module (.localGet closureIndex :: .call id :: rest) Q initial
      { locals with values := tail } env := by
  have hClosureTail :
      ({ locals with values := tail } : Wasm.Locals).get closureIndex =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa [Wasm.Locals.get] using hClosure
  rw [Wasm.wp_localGet_cons, hClosureTail]
  apply wp_exact_host_call_of_return
    (step := closureMatchesStep function arity fixed)
    (physicalArgs := [.i32 (UInt32.ofNat address.value)])
    (results := [.i32 matched]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using continued

/-- One generated closure-dispatch candidate: execute the concrete matcher,
select the candidate body or remaining chain from its direct i32 result, and
reconnect normal block exit to the surrounding instruction suffix. -/
theorem wp_closureCandidate
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals : Wasm.Locals}
    {closureIndex : Nat} {address : Word32} {matched : UInt32}
    {function : Lean.Name} {arity fixed : Nat} {tail : List Wasm.Value}
    (hClosure : locals.get closureIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (closureMatchesContract function arity fixed))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : closureMatchesStep function arity fixed initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [.i32 matched] nextStore)
    (selected :
      Wasm.wp module (if matched != 0 then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := tail } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := tail } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        nextStore { locals with values := tail } env) :
    Wasm.wp module
      (.localGet closureIndex :: .call id ::
        .iff 0 0 thenBody elseBody :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_closureMatches hClosure hImp hSat hi hContract hParams hResults
    operation
  apply Wasm.wp_iff_cons (c := matched) (vs := tail) rfl
  convert selected using 1
  all_goals simp
  all_goals
    funext continuation
    cases continuation with
    | Break level nextStore nextLocals => cases level <;> rfl
    | _ => rfl

/-- Exact ordinary-Wasm direct-call and destination-local boundary. The
callee proof is fuel-free and store-specific, so recursive proofs may supply
their own well-founded specification without a semantic host callback. -/
theorem wp_directCall_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {functionIndex resultIndex : Nat} {rest : Wasm.Program}
    {Q : Wasm.Assertion Host} {initial nextStore : Wasm.Store Host}
    {locals updated : Wasm.Locals} {physicalArgs : List Wasm.Value}
    {physicalResult : Wasm.Value} {tail : List Wasm.Value}
    (called : Wasm.TerminatesWith env module functionIndex initial
      (physicalArgs.reverse ++ tail)
      (fun final results =>
        final = nextStore ∧ results = physicalResult :: tail))
    (targetSet : locals.set? resultIndex physicalResult = some updated)
    (continued : Wasm.wp module rest Q nextStore
      { updated with values := tail } env) :
    Wasm.wp module (.call functionIndex :: .localSet resultIndex :: rest) Q
      initial { locals with values := physicalArgs.reverse ++ tail } env := by
  apply Wasm.wp_call_tw called
  intro final results post
  rcases post with ⟨finalEq, resultsEq⟩
  subst final
  subst results
  change Wasm.wp module (.localSet resultIndex :: rest) Q nextStore
    { locals with values := physicalResult :: tail } env
  exact wp_localSet_of_set targetSet continued

/-- Exact generated typed-capture projection prefix. It leaves the projected
lane on the operand stack for the subsequent argument sequence/direct call. -/
theorem wp_closureProj
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {closureIndex : Nat} {address : Word32} {physical : Wasm.Value}
    {function : Lean.Name} {arity fixed index : Nat} {kind : AbiKind}
    {tail : List Wasm.Value}
    (hClosure : locals.get closureIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (closureProjContract function arity fixed index kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : closureProjStep function arity fixed index kind initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [physical] (clearFailure initial))
    (continued : Wasm.wp module rest Q (clearFailure initial)
      { locals with values := physical :: tail } env) :
    Wasm.wp module (.localGet closureIndex :: .call id :: rest) Q initial
      { locals with values := tail } env := by
  have hClosureTail :
      ({ locals with values := tail } : Wasm.Locals).get closureIndex =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa [Wasm.Locals.get] using hClosure
  rw [Wasm.wp_localGet_cons, hClosureTail]
  apply wp_exact_host_call_of_return
    (step := closureProjStep function arity fixed index kind)
    (physicalArgs := [.i32 (UInt32.ofNat address.value)])
    (results := [physical]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using continued

/-- Branch-independent reset instance of the concrete direct-`let` boundary.
The operation-specific tagged, fallback, and unique theorems provide the
result store and witness transport consumed here. -/
theorem letStepSimulates_reset
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId} {count : Nat}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord token : Word32}
    {sourceObject sourceToken : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {witness nextWitness : RefinementWitness}
    (valueEq : decl.value = .reset count objectId)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (updatedSource : reset sourceRuntime count sourceObject =
      .ok (nextRuntime, sourceToken))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (transport : WitnessTransport witness nextWitness)
    (nextRelated : ConcreteRuntimeRel nextStore.host.runtime nextWitness
      nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .reuseToken)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (tokenRelated : ValueRel nextWitness .reuseToken (.word32 token) sourceToken)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (resetContract count))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : resetStep count initial
      [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [.i32 (UInt32.ofNat token.value)] nextStore)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat token.value)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime nextRuntime sourceEnv sourceToken initial nextStore locals
      updated resultIndex witness nextWitness := by
  have physicalRelated : PhysicalValueRel nextWitness .reuseToken
      (.i32 (UInt32.ofNat token.value)) sourceToken := .word32 tokenRelated
  have nextState := initialRelated.bindAfterTransport transport nextRelated
    failureClear resultFound resultKindAt physicalRelated targetSet
  refine ⟨?_, initialRelated, nextState, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        reset sourceRuntime count sourceObject) =
      .ok (nextRuntime, .value sourceToken)
    rw [updatedSource]
    rfl
  · intro rest Q tail continued
    exact wp_reset_let tail hObject hImp hSat hi hContract hParams hResults
      operation targetSet continued

/-- Branch-independent reuse instance of the concrete direct-`let` boundary.
Fresh allocation uses witness extension while in-place reuse uses the exact
reset-protocol descriptor transition; both are exposed here as transport. -/
theorem letStepSimulates_reuse
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {tokenId : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {word : Word32}
    {sourceToken sourceValue : Value} {semanticFields : Array Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {witness nextWitness : RefinementWitness}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (tokenLookup : lookup sourceEnv tokenId = some sourceToken)
    (argumentsEvaluated : evalArgs sourceEnv args = .ok semanticFields)
    (semanticStep : reuse sourceRuntime sourceToken info updateHeader
      semanticFields = .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (transport : WitnessTransport witness nextWitness)
    (nextRelated : ConcreteRuntimeRel nextStore.host.runtime nextWitness
      nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (reuseContract info updateHeader fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : reuseStep info updateHeader fieldKinds resultKind initial
      physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore locals
      updated resultIndex witness nextWitness := by
  have nextState := initialRelated.bindAfterTransport transport nextRelated
    failureClear resultFound resultKindAt valueRelated targetSet
  refine ⟨?_, initialRelated, nextState, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have tokenLookupValue : lookupValue sourceEnv tokenId = .ok sourceToken := by
      simp [lookupValue, tokenLookup]
    rw [tokenLookupValue, argumentsEvaluated]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        reuse sourceRuntime sourceToken info updateHeader semanticFields) =
      .ok (nextRuntime, .value sourceValue)
    rw [semanticStep]
    rfl
  · intro rest Q tail continued
    simpa [List.append_assoc] using
      wp_reuse_let tail hGets hImp hSat hi hContract hParams hResults
        operation targetSet continued

/--
Branch-independent reuse simulation for the complete production operand
prefix: the token is a local read and constructor fields may be local reads or
canonical erased zeroes.
-/
theorem letStepSimulates_reuseArgs
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {tokenId : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {targetArguments : Wasm.Program} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {word : Word32}
    {sourceToken sourceValue : Value} {semanticFields : Array Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {witness nextWitness : RefinementWitness}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (tokenLookup : lookup sourceEnv tokenId = some sourceToken)
    (argumentsEvaluated : evalArgs sourceEnv args = .ok semanticFields)
    (semanticStep : reuse sourceRuntime sourceToken info updateHeader
      semanticFields = .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (transport : WitnessTransport witness nextWitness)
    (nextRelated : ConcreteRuntimeRel nextStore.host.runtime nextWitness
      nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (ready :
      ConstructorArgsReady locals targetArguments physicalArgs)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (reuseContract info updateHeader fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : reuseStep info updateHeader fieldKinds resultKind initial
      physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (targetArguments ++ [.call id])
      sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore locals
      updated resultIndex witness nextWitness := by
  have nextState := initialRelated.bindAfterTransport transport nextRelated
    failureClear resultFound resultKindAt valueRelated targetSet
  refine ⟨?_, initialRelated, nextState, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have tokenLookupValue : lookupValue sourceEnv tokenId = .ok sourceToken := by
      simp [lookupValue, tokenLookup]
    rw [tokenLookupValue, argumentsEvaluated]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        reuse sourceRuntime sourceToken info updateHeader semanticFields) =
      .ok (nextRuntime, .value sourceValue)
    rw [semanticStep]
    rfl
  · intro rest Q tail continued
    simpa [List.append_assoc] using
      wp_reuse_ready_let tail ready hImp hSat hi hContract hParams hResults
        operation targetSet continued

/-- Integer-boxing instance of the concrete direct-`let` boundary. Tagged
results preserve the witness; promoted tags and ordinary boxes extend it with
the concrete allocation that represents the source result. -/
theorem letStepSimulates_box
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {scalarId : Lean.FVarId} {kind : BoxedScalarKind}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {scalarIndex resultIndex : Nat} {scalar : BoxedScalar}
    {heap : MemoryState} {word : Word32}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    (kindEq : scalar.kind = kind)
    (valueEq : decl.value = .box kind.semanticType scalarId)
    (sourceLookup : lookup sourceEnv scalarId = some scalar.semanticValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .tobject)
    (hScalar : locals.get scalarIndex = some (physicalOfLane scalar.lane))
    (boxed : boxScalar initial.host.runtime.heap scalar = .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (boxContract kind .tobject))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated) :
    ∃ nextRuntime sourceValue nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        nextRuntime ∧
      PhysicalValueRel nextWitness .tobject
        (.i32 (UInt32.ofNat word.value)) sourceValue ∧
      LetStepSimulates context sourceFunction module hostEnv decl
        [.localGet scalarIndex, .call id]
        sourceRuntime nextRuntime sourceEnv sourceValue initial
        (replaceHeap initial heap) locals updated resultIndex witness
        nextWitness := by
  subst kind
  obtain ⟨nextRuntime, sourceValue, nextWitness, extension,
      nextRuntimeRelated, valueRelated, semanticStep⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.boxScalar initialRelated.1 boxed
  obtain ⟨operation, _, _⟩ :=
    boxStep_of_refines rfl boxed semanticStep nextRuntimeRelated valueRelated
  have physicalRelated : PhysicalValueRel nextWitness .tobject
      (.i32 (UInt32.ofNat word.value)) sourceValue :=
    .word32 valueRelated
  have failureClear : (replaceHeap initial heap).host.failure? = none := by
    simp [replaceHeap, clearFailure]
  have nextState := initialRelated.bindAfter extension nextRuntimeRelated
    failureClear resultFound resultKindAt physicalRelated targetSet
  refine ⟨nextRuntime, sourceValue, nextWitness, extension,
    nextRuntimeRelated, physicalRelated, ?_, initialRelated, nextState, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have scalarLookup : lookupValue sourceEnv scalarId =
        .ok scalar.semanticValue := by
      simp [lookupValue, sourceLookup]
    rw [scalarLookup]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        box sourceRuntime scalar.kind.semanticType scalar.semanticValue) =
      .ok (nextRuntime, .value sourceValue)
    rw [semanticStep]
    rfl
  · intro rest Q tail continued
    exact wp_box_let tail hScalar hImp hSat hi hContract hParams hResults
      operation targetSet continued

/-- W6.6 composition for generated reset through source evaluation, compiler
output, Talos adaptation, one of the three concrete reset branches,
reuse-token local write, and an arbitrary verified continuation. -/
theorem codeWP_reset_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId} {count : Nat}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord token : Word32}
    {sourceObject sourceToken : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {witness nextWitness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .reset count objectId)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.localGet objectId, .call (.runtime (.reset count))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound : callIndex? sourceModule (.runtime (.reset count)) = some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (updatedSource : reset sourceRuntime count sourceObject =
      .ok (nextRuntime, sourceToken))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (transport : WitnessTransport witness nextWitness)
    (nextRelated : ConcreteRuntimeRel nextStore.host.runtime nextWitness
      nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .reuseToken)
    (hObject : locals.get objectIndex =
      some (.i32 (UInt32.ofNat objectWord.value)))
    (tokenRelated : ValueRel nextWitness .reuseToken (.word32 token) sourceToken)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (resetContract count))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : resetStep count initial
      [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [.i32 (UInt32.ofNat token.value)] nextStore)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat token.value)) = some updated)
    (continued : CodeWP context sourceModule sourceFunction labels module hostEnv
      nextRuntime (bind sourceEnv decl.fvarId sourceToken) continuation
      targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.reset count))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_reset (context := context) valueEq sourceLookup
    updatedSource initialRelated transport nextRelated failureClear resultFound
    resultKindAt hObject tokenRelated hImp hSat hi hContract hParams hResults
    operation targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- W6.6 composition for generated reuse through source evaluation, compiler
output, Talos adaptation, fresh or in-place concrete reuse, result-local
write, and an arbitrary verified continuation. -/
theorem codeWP_reuse_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {tokenId : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {fvarIds : List Lean.FVarId} {indices : List Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {semanticFields : Array Value}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {word : Word32}
    {sourceToken sourceValue : Value}
    {sourceRuntime nextRuntime : RuntimeState}
    {witness nextWitness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok ((tokenId :: fvarIds).map Fir.Wasm.Instruction.localGet ++
        [.call (.runtime (.reuse info updateHeader fieldKinds resultKind))]))
    (argumentsFound : List.Forall₂
      (fun fvarId index =>
        findFVar? (functionBindings sourceFunction) fvarId = some index)
      (tokenId :: fvarIds) indices)
    (callFound : callIndex? sourceModule
      (.runtime (.reuse info updateHeader fieldKinds resultKind)) = some id)
    (tokenLookup : lookup sourceEnv tokenId = some sourceToken)
    (argumentsEvaluated : evalArgs sourceEnv args = .ok semanticFields)
    (semanticStep : reuse sourceRuntime sourceToken info updateHeader
      semanticFields = .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (transport : WitnessTransport witness nextWitness)
    (nextRelated : ConcreteRuntimeRel nextStore.host.runtime nextWitness
      nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (reuseContract info updateHeader fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : reuseStep info updateHeader fieldKinds resultKind initial
      physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : CodeWP context sourceModule sourceFunction labels module hostEnv
      nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
      targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have argumentsAdapted := FirTalos.Correctness.instructions_localGets
    (sourceModule := sourceModule) (sourceFunction := sourceFunction)
    (labels := labels) (found := by
      simpa [functionBindings] using argumentsFound)
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          ((tokenId :: fvarIds).map Fir.Wasm.Instruction.localGet ++
            [.call (.runtime
              (.reuse info updateHeader fieldKinds resultKind))]) =
        .ok (indices.map Wasm.Instruction.localGet ++ [.call id]) := by
    rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
    simp [instructions, instruction, callFound]
  have step := letStepSimulates_reuse (context := context) valueEq tokenLookup
    argumentsEvaluated semanticStep initialRelated transport nextRelated
    failureClear resultFound resultKindAt hGets valueRelated hImp hSat hi
    hContract hParams hResults operation targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  have adapted := codeAdapted_let valueCompiled valueAdapted resultFound
    continuationAdapted
  refine ⟨?_, stepInitial, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using adapted
  · simpa only [List.append_assoc, List.singleton_append] using
      stepWP targetRest Q tail continuedWP

/-- W6.6 composition for generated integer boxing through source evaluation,
compiler output, Talos adaptation, concrete allocation, destination-local
write, and an arbitrary verified continuation. -/
theorem codeWP_box_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {scalarId : Lean.FVarId} {kind : BoxedScalarKind}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {scalarIndex resultIndex : Nat} {scalar : BoxedScalar}
    {heap : MemoryState} {word : Word32}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (kindEq : scalar.kind = kind)
    (valueEq : decl.value = .box kind.semanticType scalarId)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.localGet scalarId,
        .call (.runtime (.box kind.abiKind .tobject))])
    (scalarFound :
      findFVar? (functionBindings sourceFunction) scalarId = some scalarIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.box kind.abiKind .tobject)) = some id)
    (sourceLookup : lookup sourceEnv scalarId = some scalar.semanticValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .tobject)
    (hScalar : locals.get scalarIndex = some (physicalOfLane scalar.lane))
    (boxed : boxScalar initial.host.runtime.heap scalar = .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (boxContract kind .tobject))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : ∀ nextRuntime sourceValue nextWitness,
      witness.Extends nextWitness →
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        nextRuntime →
      PhysicalValueRel nextWitness .tobject
        (.i32 (UInt32.ofNat word.value)) sourceValue →
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetRest (replaceHeap initial heap) updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet scalarIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet scalarId,
            .call (.runtime (.box kind.abiKind .tobject))] =
        .ok [.localGet scalarIndex, .call id] := by
    have scalarFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          scalarId = some scalarIndex := by
      simpa [functionBindings] using scalarFound
    simp [instructions, instruction, scalarFound', callFound]
    rfl
  obtain ⟨nextRuntime, sourceValue, nextWitness, extension,
      nextRuntimeRelated, valueRelated, step⟩ :=
    letStepSimulates_box (context := context) kindEq valueEq sourceLookup
      initialRelated resultFound resultKindAt hScalar boxed hImp hSat hi
      hContract hParams hResults targetSet
  have nextCode := continued nextRuntime sourceValue nextWitness extension
    nextRuntimeRelated valueRelated
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases nextCode with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Typed-unboxing instance of the concrete direct-`let` boundary. The
representation premise records why the generated result kind is valid for a
type-erased heap box while remaining automatic for tagged objects. -/
theorem letStepSimulates_unbox
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId} {kind : BoxedScalarKind}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {word : Word32}
    {sourceObject : Value} {scalar : BoxedScalar}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    (valueEq : decl.value = .unbox objectId)
    (resultTypeEq : decl.type = kind.semanticType)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (unboxed : unbox sourceRuntime kind.semanticType sourceObject =
      .ok scalar.semanticValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some kind.abiKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat word.value)))
    (objectRelated : UnboxObjectRel witness word kind sourceObject)
    (concreteRead : readBoxedScalar initial.host.runtime.heap kind word =
      .ok scalar)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (unboxContract kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex (physicalOfLane scalar.lane) =
      some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime sourceRuntime sourceEnv scalar.semanticValue initial
      (clearFailure initial) locals updated resultIndex witness witness := by
  obtain ⟨_, _, physicalRelated⟩ :=
    unboxStep_of_refines initialRelated.1 objectRelated unboxed concreteRead
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup, resultTypeEq]
    change ((fun result : Value =>
      (sourceRuntime, LetAction.value result)) <$>
        unbox sourceRuntime kind.semanticType sourceObject) =
      .ok (sourceRuntime, .value scalar.semanticValue)
    rw [unboxed]
    rfl
  · exact initialRelated.bindPhysical resultFound resultKindAt
      physicalRelated targetSet
  · intro rest Q tail continued
    exact wp_unbox_let tail hObject hImp hSat hi hContract hParams hResults
      initialRelated.1 objectRelated unboxed concreteRead targetSet continued

/-- W6.6 composition for generated unboxing through source evaluation,
compiler output, Talos adaptation, the concrete typed host, and continuation. -/
theorem codeWP_unbox_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId} {kind : BoxedScalarKind}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {word : Word32}
    {sourceObject : Value} {scalar : BoxedScalar}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .unbox objectId)
    (resultTypeEq : decl.type = kind.semanticType)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.localGet objectId, .call (.runtime (.unbox kind.abiKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound : callIndex? sourceModule (.runtime (.unbox kind.abiKind)) =
      some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (unboxed : unbox sourceRuntime kind.semanticType sourceObject =
      .ok scalar.semanticValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some kind.abiKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat word.value)))
    (objectRelated : UnboxObjectRel witness word kind sourceObject)
    (concreteRead : readBoxedScalar initial.host.runtime.heap kind word =
      .ok scalar)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (unboxContract kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex (physicalOfLane scalar.lane) =
      some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime (bind sourceEnv decl.fvarId scalar.semanticValue)
        continuation targetRest (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.unbox kind.abiKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_unbox (context := context)
    valueEq resultTypeEq sourceLookup unboxed initialRelated resultFound
    resultKindAt hObject objectRelated concreteRead hImp hSat hi hContract
    hParams hResults targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Concrete `isShared` instance of the direct-`let` boundary. It connects
the source read-only step to the concrete object representation, direct UInt8
result lane, destination local, and arbitrary Talos continuation. -/
theorem letStepSimulates_isShared
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject : Value} {shared : UInt8}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    (valueEq : decl.value = .isShared objectId)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (evaluated : isShared sourceRuntime sourceObject =
      .ok (.scalar (.uint8 shared)))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .uint8)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some isSharedContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat shared.toNat)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime sourceRuntime sourceEnv (.scalar (.uint8 shared)) initial
      (clearFailure initial) locals updated resultIndex witness witness := by
  obtain ⟨_, valueRelated⟩ :=
    isSharedStep_of_refines initialRelated.1 objectRelated evaluated
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup]
    change ((fun result : Value =>
      (sourceRuntime, LetAction.value result)) <$>
        isShared sourceRuntime sourceObject) =
      .ok (sourceRuntime, .value (.scalar (.uint8 shared)))
    rw [evaluated]
    rfl
  · simpa using initialRelated.bindWord32 resultFound resultKindAt
      valueRelated targetSet
  · intro rest Q tail continued
    exact wp_isShared_let tail hObject hImp hSat hi hContract hParams hResults
      initialRelated.1 objectRelated evaluated targetSet continued

/-- W6.6 composition for the generated `isShared` code emitted by the FIR
lowerer and Talos adapter, followed by any already-composed continuation. -/
theorem codeWP_isShared_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject : Value} {shared : UInt8}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .isShared objectId)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.localGet objectId, .call (.runtime .isShared)])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound : callIndex? sourceModule (.runtime .isShared) = some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (evaluated : isShared sourceRuntime sourceObject =
      .ok (.scalar (.uint8 shared)))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .uint8)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some isSharedContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat shared.toNat)) = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime
        (bind sourceEnv decl.fvarId (.scalar (.uint8 shared))) continuation
        targetRest (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime .isShared)] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_isShared (context := context)
    valueEq sourceLookup evaluated initialRelated resultFound resultKindAt
    hObject objectRelated hImp hSat hi hContract hParams hResults targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Object-projection instance of the concrete direct-`let` boundary. It
proves the source interpreter step, the result-local refinement, and a Talos
WP transformer for the generated read/call/write prefix. -/
theorem letStepSimulates_objectProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord resultWord : Word32}
    {sourceObject value : Value} {resultKind : AbiKind}
    {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (valueEq : decl.value = .oproj index objectId)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getObjectField sourceRuntime sourceObject index = .ok value)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (fieldKind : fieldKinds[index]? = some resultKind)
    (concreteRead :
      readObjectField initial.host.runtime.heap objectWord index = .ok resultWord)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat resultWord.value)) =
        some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime sourceRuntime sourceEnv value initial
      (clearFailure initial) locals updated resultIndex witness witness := by
  obtain ⟨actualWord, actualRead, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.readObjectField_refines
      initialRelated.1 objectRelated descriptor fieldKind projected
  rw [concreteRead] at actualRead
  have wordEq : resultWord = actualWord := Except.ok.inj actualRead
  subst actualWord
  refine ⟨?_, initialRelated,
    initialRelated.bindWord32 resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup]
    change ((fun projectedValue : Value =>
      (sourceRuntime, LetAction.value projectedValue)) <$>
        getObjectField sourceRuntime sourceObject index) =
      .ok (sourceRuntime, .value value)
    rw [projected]
    rfl
  · intro rest Q tail continued
    apply wp_objectProjection_let tail hObject hImp hSat hi hContract hParams
      hResults initialRelated.1 objectRelated descriptor fieldKind projected
    intro word read related
    rw [concreteRead] at read
    have equal : resultWord = word := Except.ok.inj read
    subst word
    exact ⟨updated, targetSet, continued⟩

/-- W6.6 composition for the actual object-projection code emitted by the FIR
lowerer and Talos adapter, followed by any already-composed continuation. -/
theorem codeWP_objectProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord resultWord : Word32}
    {sourceObject value : Value} {resultKind : AbiKind}
    {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {targetRest : Wasm.Program}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .oproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.objectProj index resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.objectProj index resultKind)) = some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getObjectField sourceRuntime sourceObject index = .ok value)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (fieldKind : fieldKinds[index]? = some resultKind)
    (concreteRead :
      readObjectField initial.host.runtime.heap objectWord index = .ok resultWord)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat resultWord.value)) =
        some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime (bind sourceEnv decl.fvarId value)
        continuation targetRest (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.objectProj index resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_objectProjection (context := context)
    valueEq sourceLookup projected initialRelated resultFound resultKindAt
    hObject objectRelated descriptor fieldKind concreteRead hImp hSat hi
    hContract hParams hResults targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

theorem letStepSimulates_usizeProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject : Value} {value : UInt64} {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (valueEq : decl.value = .uproj index objectId)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected : getUSizeSlot sourceRuntime sourceObject index =
      .ok (.usize value))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .usize)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex (.i64 value) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime sourceRuntime sourceEnv (.usize value) initial
      (clearFailure initial) locals updated resultIndex witness witness := by
  obtain ⟨_, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.readUSizeSlot_refines
      initialRelated.1 objectRelated descriptor projected
  refine ⟨?_, initialRelated,
    initialRelated.bindWord64 resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup]
    change ((fun projectedValue : Value =>
      (sourceRuntime, LetAction.value projectedValue)) <$>
        getUSizeSlot sourceRuntime sourceObject index) =
      .ok (sourceRuntime, .value (.usize value))
    rw [projected]
    rfl
  · intro rest Q tail continued
    exact wp_usizeProjection_let tail hObject hImp hSat hi hContract hParams
      hResults initialRelated.1 objectRelated descriptor projected targetSet
      continued

theorem codeWP_usizeProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject : Value} {value : UInt64} {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {targetRest : Wasm.Program}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .uproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.usizeProj index))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.usizeProj index)) = some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected : getUSizeSlot sourceRuntime sourceObject index =
      .ok (.usize value))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .usize)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex (.i64 value) = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime (bind sourceEnv decl.fvarId (.usize value)) continuation
        targetRest (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.usizeProj index))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_usizeProjection (context := context)
    valueEq sourceLookup projected initialRelated resultFound resultKindAt
    hObject objectRelated descriptor hImp hSat hi hContract hParams hResults
    targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

theorem letStepSimulates_scalarProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {width offset : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject sourceValue : Value} {resultKind : AbiKind}
    {physical : Wasm.Value} {sourceRuntime : RuntimeState}
    {witness : RefinementWitness}
    (valueEq : decl.value = .sproj width offset objectId)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected : getScalarField sourceRuntime sourceObject width offset =
      .ok sourceValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (physicalRelated :
      PhysicalValueRel witness resultKind physical sourceValue)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (scalarProjContract width offset resultKind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation :
      scalarProjStep width offset resultKind initial
          [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [physical] (clearFailure initial))
    (targetSet : locals.set? resultIndex physical = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime sourceRuntime sourceEnv sourceValue initial
      (clearFailure initial) locals updated resultIndex witness witness := by
  refine ⟨?_, initialRelated,
    initialRelated.bindPhysical resultFound resultKindAt physicalRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup]
    change ((fun projectedValue : Value =>
      (sourceRuntime, LetAction.value projectedValue)) <$>
        getScalarField sourceRuntime sourceObject width offset) =
      .ok (sourceRuntime, .value sourceValue)
    rw [projected]
    rfl
  · intro rest Q tail continued
    exact wp_scalarProjection_let tail hObject hImp hSat hi hContract hParams
      hResults operation targetSet continued

theorem codeWP_scalarProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {width offset : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject sourceValue : Value} {resultKind : AbiKind}
    {physical : Wasm.Value} {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {targetRest : Wasm.Program}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .sproj width offset objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.scalarProj width offset resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.scalarProj width offset resultKind)) = some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected : getScalarField sourceRuntime sourceObject width offset =
      .ok sourceValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (physicalRelated :
      PhysicalValueRel witness resultKind physical sourceValue)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (scalarProjContract width offset resultKind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation :
      scalarProjStep width offset resultKind initial
          [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [physical] (clearFailure initial))
    (targetSet : locals.set? resultIndex physical = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetRest (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.scalarProj width offset resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_scalarProjection (context := context)
    valueEq sourceLookup projected initialRelated resultFound resultKindAt
    hObject physicalRelated hImp hSat hi hContract hParams hResults operation
    targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Constructor-allocation instance of the concrete direct-`let` boundary.
The operation-specific refinement supplies the grown runtime witness; this
rule composes it with source evaluation, generated locals, and Talos WP. -/
theorem letStepSimulates_constructor
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value} {sourceRuntime nextRuntime : RuntimeState}
    {sourceValue : Value} {resultIndex : Nat} {word : Word32}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    (valueEq : decl.value = .ctor info args)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore
      locals updated resultIndex witness nextWitness := by
  refine ⟨?_, initialRelated,
    initialRelated.bindAfter extension nextRuntimeRelated failureClear
      resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq, evaluated]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        allocCtor sourceRuntime info semanticArgs) =
      .ok (nextRuntime, .value sourceValue)
    rw [semanticStep]
    rfl
  · intro rest Q tail continued
    simpa [List.append_assoc] using
      wp_allocCtor_let tail hGets hImp hSat hi hContract hParams hResults
        operation targetSet continued

/--
Constructor-allocation simulation for the complete mixed local/erased
argument prefix emitted by `compileArgs`.
-/
theorem letStepSimulates_constructorArgs
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {targetArguments : Wasm.Program} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value} {sourceRuntime nextRuntime : RuntimeState}
    {sourceValue : Value} {resultIndex : Nat} {word : Word32}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    (valueEq : decl.value = .ctor info args)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (ready : ConstructorArgsReady locals targetArguments physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (targetArguments ++ [.call id])
      sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore
      locals updated resultIndex witness nextWitness := by
  refine ⟨?_, initialRelated,
    initialRelated.bindAfter extension nextRuntimeRelated failureClear
      resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq, evaluated]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        allocCtor sourceRuntime info semanticArgs) =
      .ok (nextRuntime, .value sourceValue)
    rw [semanticStep]
    rfl
  · intro rest Q tail continued
    simpa [List.append_assoc] using
      wp_allocCtor_ready_let tail ready hImp hSat hi hContract hParams hResults
        operation targetSet continued

/-- Recursive source/compiler/Talos rule for arbitrary compiled constructor
arguments, including erased fields. -/
theorem codeWP_constructorArgs_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {argumentCode : List Fir.Wasm.Instruction}
    {targetArguments : Wasm.Program} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value}
    {sourceRuntime nextRuntime : RuntimeState} {sourceValue : Value}
    {resultIndex : Nat}
    {word : Word32} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .ctor info args)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok (argumentCode ++
        [.call (.runtime (.allocCtor info fieldKinds resultKind))]))
    (argumentsAdapted :
      instructions sourceModule sourceFunction labels argumentCode =
        .ok targetArguments)
    (callFound : callIndex? sourceModule
      (.runtime (.allocCtor info fieldKinds resultKind)) = some id)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep : allocCtor sourceRuntime info semanticArgs =
      .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (ready : ConstructorArgsReady locals targetArguments physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : CodeWP context sourceModule sourceFunction labels module hostEnv
      nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
      targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetArguments ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          (argumentCode ++
            [.call (.runtime (.allocCtor info fieldKinds resultKind))]) =
        .ok (targetArguments ++ [.call id]) := by
    rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
    simp [instructions, instruction, callFound]
  have step := letStepSimulates_constructorArgs (context := context) valueEq
    evaluated semanticStep initialRelated resultFound resultKindAt ready hImp
    hSat hi hContract hParams hResults operation extension nextRuntimeRelated
    failureClear valueRelated targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  have adapted := codeAdapted_let valueCompiled valueAdapted resultFound
    continuationAdapted
  refine ⟨?_, stepInitial, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using adapted
  · simpa only [List.append_assoc, List.singleton_append] using
      stepWP targetRest Q tail continuedWP

/-- Recursive source/compiler/Talos rule for a concrete constructor `let`. -/
theorem codeWP_constructor_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {fvarIds : List Lean.FVarId} {indices : List Nat}
    {physicalArgs : List Wasm.Value} {semanticArgs : Array Value}
    {sourceRuntime nextRuntime : RuntimeState} {sourceValue : Value}
    {resultIndex : Nat}
    {word : Word32} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .ctor info args)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok (fvarIds.map Fir.Wasm.Instruction.localGet ++
        [.call (.runtime (.allocCtor info fieldKinds resultKind))]))
    (argumentsFound : List.Forall₂
      (fun fvarId index =>
        findFVar? (functionBindings sourceFunction) fvarId = some index)
      fvarIds indices)
    (callFound : callIndex? sourceModule
      (.runtime (.allocCtor info fieldKinds resultKind)) = some id)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep : allocCtor sourceRuntime info semanticArgs =
      .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : CodeWP context sourceModule sourceFunction labels module hostEnv
      nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
      targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have argumentsAdapted := FirTalos.Correctness.instructions_localGets
    (sourceModule := sourceModule) (sourceFunction := sourceFunction)
    (labels := labels) (found := by
      simpa [functionBindings] using argumentsFound)
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          (fvarIds.map Fir.Wasm.Instruction.localGet ++
            [.call (.runtime (.allocCtor info fieldKinds resultKind))]) =
        .ok (indices.map Wasm.Instruction.localGet ++ [.call id]) := by
    rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
    simp [instructions, instruction, callFound]
  have step := letStepSimulates_constructor (context := context) valueEq
    evaluated semanticStep initialRelated resultFound resultKindAt hGets hImp
    hSat hi hContract hParams hResults operation extension nextRuntimeRelated
    failureClear valueRelated targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  have adapted := codeAdapted_let valueCompiled valueAdapted resultFound
    continuationAdapted
  refine ⟨?_, stepInitial, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using adapted
  · simpa only [List.append_assoc, List.singleton_append] using
      stepWP targetRest Q tail continuedWP

/-- Partial-application instance of the concrete direct-`let` boundary.  The
source interpreter and concrete runtime allocate the same closure at the next
semantic/physical heap locations, respectively; the operation refinement
supplies the grown witness relating those locations. -/
theorem letStepSimulates_partialApply
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {function : Lean.Name} {target : Lean.Compiler.LCNF.Decl .impure}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value} {sourceRuntime : RuntimeState}
    {resultIndex : Nat} {word : Word32}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    (valueEq : decl.value = .pap function args)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (targetFound : context.program.findDecl? function = some target)
    (semanticLt : semanticArgs.size < target.params.size)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (partialApplyContract function target.params.size args.size
        fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : partialApplyStep function target.params.size args.size
      fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness
        (semanticClosureResult sourceRuntime function target.params.size
          semanticArgs))
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value))
      (.object (.heap sourceRuntime.nextLocation)))
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      sourceRuntime
      (semanticClosureResult sourceRuntime function target.params.size
        semanticArgs)
      sourceEnv (.object (.heap sourceRuntime.nextLocation)) initial nextStore
      locals updated resultIndex witness nextWitness := by
  refine ⟨?_, initialRelated,
    initialRelated.bindAfter extension nextRuntimeRelated failureClear
      resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq, evaluated, targetFound,
      alloc_closure_eq]
    change (if target.params.size ≤ semanticArgs.size then _ else _) = _
    rw [if_neg (Nat.not_le.mpr semanticLt)]
    rfl
  · intro rest Q tail continued
    simpa [List.append_assoc] using
      wp_partialApply_let (tail := tail) hGets hImp hSat hi hContract hParams
        hResults operation targetSet continued

/-- Recursive source/compiler/Talos rule for closure allocation by partial
application.  `argumentsAdapted` keeps this rule independent of which
supported LCNF argument forms produced the physical capture lanes. -/
theorem codeWP_partialApply_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {function : Lean.Name} {target : Lean.Compiler.LCNF.Decl .impure}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {argumentCode : List Fir.Wasm.Instruction} {indices : List Nat}
    {physicalArgs : List Wasm.Value} {semanticArgs : Array Value}
    {sourceRuntime : RuntimeState} {resultIndex : Nat} {word : Word32}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .pap function args)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok (argumentCode ++ [
        .call (.runtime (.partialApply function target.params.size args.size
          fieldKinds resultKind))]))
    (argumentsAdapted :
      instructions sourceModule sourceFunction labels argumentCode =
        .ok (indices.map Wasm.Instruction.localGet))
    (callFound : callIndex? sourceModule
      (.runtime (.partialApply function target.params.size args.size
        fieldKinds resultKind)) = some id)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (targetFound : context.program.findDecl? function = some target)
    (semanticLt : semanticArgs.size < target.params.size)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (partialApplyContract function target.params.size args.size
        fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : partialApplyStep function target.params.size args.size
      fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness
        (semanticClosureResult sourceRuntime function target.params.size
          semanticArgs))
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value))
      (.object (.heap sourceRuntime.nextLocation)))
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : CodeWP context sourceModule sourceFunction labels module hostEnv
      (semanticClosureResult sourceRuntime function target.params.size
        semanticArgs)
      (bind sourceEnv decl.fvarId (.object (.heap sourceRuntime.nextLocation)))
      continuation targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          (argumentCode ++ [
            .call (.runtime (.partialApply function target.params.size args.size
              fieldKinds resultKind))]) =
        .ok (indices.map Wasm.Instruction.localGet ++ [.call id]) := by
    rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
    simp [instructions, instruction, callFound]
  have step := letStepSimulates_partialApply (context := context) valueEq
    evaluated targetFound semanticLt initialRelated resultFound resultKindAt
    hGets hImp hSat hi hContract hParams hResults operation extension
    nextRuntimeRelated failureClear valueRelated targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  have adapted := codeAdapted_let valueCompiled valueAdapted resultFound
    continuationAdapted
  refine ⟨?_, stepInitial, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using adapted
  · simpa only [List.append_assoc, List.singleton_append] using
      stepWP targetRest Q tail continuedWP

theorem letStepSimulates_naturalLiteral
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : Nat} {heap : MemoryState} {word : Word32}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    (valueEq : decl.value = .lit (.nat value))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .tobject)
    (allocated : allocateNatural initial.host.runtime.heap value =
      .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (naturalLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal sourceRuntime (.nat value)).1 ∧
      PhysicalValueRel nextWitness .tobject
        (.i32 (UInt32.ofNat word.value)) (literal sourceRuntime (.nat value)).2 ∧
      LetStepSimulates context sourceFunction module hostEnv decl [.call id]
        sourceRuntime (literal sourceRuntime (.nat value)).1 sourceEnv
        (literal sourceRuntime (.nat value)).2 initial (replaceHeap initial heap)
        locals updated resultIndex witness nextWitness := by
  obtain ⟨nextWitness, extension, operation, nextRuntimeRelated,
      valueRelated⟩ :=
    naturalLiteralStep_of_refines initialRelated.1 allocated
  have failureClear : (replaceHeap initial heap).host.failure? = none := by
    simp [replaceHeap, clearFailure]
  have nextState := initialRelated.bindAfter extension nextRuntimeRelated
    failureClear resultFound resultKindAt valueRelated targetSet
  refine ⟨nextWitness, extension, nextRuntimeRelated, valueRelated,
    ?_, initialRelated, nextState, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    rfl
  · intro rest Q tail continued
    exact wp_naturalLiteral_let tail hImp hSat hi hContract hParams hResults
      operation targetSet continued

theorem codeWP_naturalLiteral_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : Nat} {heap : MemoryState} {word : Word32}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .lit (.nat value))
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.call (.runtime (.literal (.nat value) .tobject))])
    (callFound : callIndex? sourceModule
      (.runtime (.literal (.nat value) .tobject)) = some id)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .tobject)
    (allocated : allocateNatural initial.host.runtime.heap value =
      .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (naturalLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : ∀ nextWitness,
      witness.Extends nextWitness →
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal sourceRuntime (.nat value)).1 →
      PhysicalValueRel nextWitness .tobject
        (.i32 (UInt32.ofNat word.value)) (literal sourceRuntime (.nat value)).2 →
      CodeWP context sourceModule sourceFunction labels module hostEnv
        (literal sourceRuntime (.nat value)).1
        (bind sourceEnv decl.fvarId (literal sourceRuntime (.nat value)).2)
        continuation targetRest (replaceHeap initial heap) updated nextWitness
        tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.call (.runtime (.literal (.nat value) .tobject))] =
        .ok [.call id] := by
    simp [instructions, instruction, callFound]
    rfl
  obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated, step⟩ :=
    letStepSimulates_naturalLiteral (context := context) valueEq initialRelated
      resultFound resultKindAt allocated hImp hSat hi hContract hParams hResults
      targetSet
  have nextCode := continued nextWitness extension nextRuntimeRelated valueRelated
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases nextCode with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

theorem letStepSimulates_stringLiteral
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : String} {heap : MemoryState} {word : Word32}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    (valueEq : decl.value = .lit (.str value))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .object)
    (allocated : allocateString initial.host.runtime.heap value =
      .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (stringLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal sourceRuntime (.str value)).1 ∧
      PhysicalValueRel nextWitness .object
        (.i32 (UInt32.ofNat word.value)) (literal sourceRuntime (.str value)).2 ∧
      LetStepSimulates context sourceFunction module hostEnv decl [.call id]
        sourceRuntime (literal sourceRuntime (.str value)).1 sourceEnv
        (literal sourceRuntime (.str value)).2 initial (replaceHeap initial heap)
        locals updated resultIndex witness nextWitness := by
  obtain ⟨nextWitness, extension, operation, nextRuntimeRelated,
      valueRelated⟩ :=
    stringLiteralStep_of_refines initialRelated.1 allocated
  have failureClear : (replaceHeap initial heap).host.failure? = none := by
    simp [replaceHeap, clearFailure]
  have nextState := initialRelated.bindAfter extension nextRuntimeRelated
    failureClear resultFound resultKindAt valueRelated targetSet
  refine ⟨nextWitness, extension, nextRuntimeRelated, valueRelated,
    ?_, initialRelated, nextState, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    rfl
  · intro rest Q tail continued
    exact wp_stringLiteral_let tail hImp hSat hi hContract hParams hResults
      operation targetSet continued

theorem codeWP_stringLiteral_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : String} {heap : MemoryState} {word : Word32}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .lit (.str value))
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.call (.runtime (.literal (.str value) .object))])
    (callFound : callIndex? sourceModule
      (.runtime (.literal (.str value) .object)) = some id)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .object)
    (allocated : allocateString initial.host.runtime.heap value =
      .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (stringLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : ∀ nextWitness,
      witness.Extends nextWitness →
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal sourceRuntime (.str value)).1 →
      PhysicalValueRel nextWitness .object
        (.i32 (UInt32.ofNat word.value)) (literal sourceRuntime (.str value)).2 →
      CodeWP context sourceModule sourceFunction labels module hostEnv
        (literal sourceRuntime (.str value)).1
        (bind sourceEnv decl.fvarId (literal sourceRuntime (.str value)).2)
        continuation targetRest (replaceHeap initial heap) updated nextWitness
        tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.call (.runtime (.literal (.str value) .object))] =
        .ok [.call id] := by
    simp [instructions, instruction, callFound]
    rfl
  obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated, step⟩ :=
    letStepSimulates_stringLiteral (context := context) valueEq initialRelated
      resultFound resultKindAt allocated hImp hSat hi hContract hParams hResults
      targetSet
  have nextCode := continued nextWitness extension nextRuntimeRelated valueRelated
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases nextCode with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Host-polymorphic form of W5's exact i32 compare/branch stack rule. W6
needs the same Wasm instruction fact for a concrete host state. -/
theorem wp_i32Eq_ifElse
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    (actual expected : UInt32)
    (hBody :
      Wasm.wp module (if actual = expected then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        store locals env) :
    Wasm.wp module
      (.const expected :: .eq :: .iff 0 0 thenBody elseBody :: rest)
      Q store { locals with values := .i32 actual :: locals.values } env := by
  rw [Wasm.wp_const_cons, Wasm.wp_eq_cons]
  apply Wasm.wp_iff_cons
    (c := if actual = expected then 1 else 0) (vs := locals.values) rfl
  have localsSelf : { locals with values := locals.values } = locals := by
    cases locals
    rfl
  rw [localsSelf]
  convert hBody using 1
  all_goals simp
  all_goals
    funext continuation
    cases continuation with
    | Break level nextStore nextLocals =>
        cases level <;> rfl
    | _ => rfl

/-- Host-polymorphic direct scalar-case dispatch. The generated code loads the
`UInt8` discriminator local, compares its exact i32 lane, and selects an arm
without a runtime import. -/
theorem wp_scalarUInt8_case_test
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    {localIndex : Nat} (actualTag expectedTag : Nat)
    (hLocal :
      locals.get localIndex = some (.i32 (UInt32.ofNat actualTag)))
    (actualFits : actualTag < UInt8.size)
    (expectedFits : expectedTag < UInt8.size)
    (hBody :
      Wasm.wp module (if actualTag = expectedTag then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        store { locals with values := locals.values } env) :
    Wasm.wp module
      (.localGet localIndex :: .const (UInt32.ofNat expectedTag) :: .eq ::
        .iff 0 0 thenBody elseBody :: rest)
      Q store locals env := by
  rw [Wasm.wp_localGet_cons, hLocal]
  apply wp_i32Eq_ifElse (UInt32.ofNat actualTag)
    (UInt32.ofNat expectedTag)
  simpa only [constructorTag_uint8_eq_iff actualFits expectedFits] using hBody

/-- Concrete-host WP for the exact tag-test instruction sequence emitted by
the lowerer. The source and concrete object representations meet only through
`ValueRel`; no opaque semantic handle is allocated or decoded. -/
theorem wp_getTag_case_test
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {localIndex : Nat} {word : Word32}
    {witness : RefinementWitness} {semanticRuntime : RuntimeState}
    {sourceObject : Value} {actualTag expectedTag : Nat}
    (hLocal :
      locals.get localIndex = some (.i32 (UInt32.ofNat word.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some getTagContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness semanticRuntime)
    (valueRelated : ValueRel witness .tobject (.word32 word) sourceObject)
    (tagged : getTag semanticRuntime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (expectedFits : expectedTag < UInt32.size)
    (hBody :
      Wasm.wp module
        (if actualTag = expectedTag then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        (clearFailure initial) locals env) :
    Wasm.wp module
      (.localGet localIndex :: .call id ::
        .const (UInt32.ofNat expectedTag) :: .eq ::
        .iff 0 0 thenBody elseBody :: rest)
      Q initial locals env := by
  rw [Wasm.wp_localGet_cons, hLocal]
  apply wp_exact_host_call_of_return
    (step := getTagStep)
    (physicalArgs := [.i32 (UInt32.ofNat word.value)])
    (results := [.i32 (UInt32.ofNat actualTag)])
    hImp hSat hi hContract
  · simp [hParams]
  · exact getTagStep_of_refines runtimeRelated valueRelated tagged actualFits
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_i32Eq_ifElse (host := Host) (locals := locals)
        (store := clearFailure initial) (UInt32.ofNat actualTag)
        (UInt32.ofNat expectedTag)
        (by
          by_cases equal : actualTag = expectedTag
          · have physicalEqual :
                UInt32.ofNat actualTag = UInt32.ofNat expectedTag :=
              congrArg UInt32.ofNat equal
            rw [if_pos physicalEqual]
            rw [if_pos equal] at hBody
            convert hBody using 1
            funext continuation
            cases continuation with
            | Break level nextStore nextLocals =>
                cases level <;> (apply propext; rfl)
            | _ => apply propext; rfl
          · have physicalDifferent :
                UInt32.ofNat actualTag ≠ UInt32.ofNat expectedTag := by
              intro physicalEqual
              exact equal <|
                (constructorTag_i32_eq_iff actualFits expectedFits).mp
                  physicalEqual
            rw [if_neg physicalDifferent]
            rw [if_neg equal] at hBody
            convert hBody using 1
            funext continuation
            cases continuation with
            | Break level nextStore nextLocals =>
                cases level <;> (apply propext; rfl)
            | _ => apply propext; rfl)

/-- Concrete-host analogue of W5's case resumption assertion. -/
def CaseResumePost (module : Wasm.Module) (hostEnv : Wasm.HostEnv Host)
    (rest : Wasm.Program) (Q : Wasm.Assertion Host)
    (tail : List Wasm.Value) : Wasm.Assertion Host :=
  fun continuation =>
    match continuation with
    | .Fallthrough nextStore nextLocals =>
        Wasm.wp module rest Q nextStore
          { nextLocals with values := tail } hostEnv
    | .Break 0 nextStore nextLocals =>
        Wasm.wp module rest Q nextStore
          { nextLocals with values := tail } hostEnv
    | .Break (level + 1) nextStore nextLocals =>
        Q (.Break level nextStore nextLocals)
    | other => Q other

/-- W6.6 proof boundary for a constructor-case suffix: the actual compiler and
adapter witness is paired with concrete runtime/local refinement and Talos WP. -/
def CaseChainWP (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (discr : Lean.FVarId) (alts : List (Lean.Compiler.LCNF.Alt .impure))
    (fallback : List Fir.Wasm.Instruction) (target : Wasm.Program)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) (tail : List Wasm.Value)
    (Q : Wasm.Assertion Host) : Prop :=
  FirTalos.Correctness.CaseChainAdapted context sourceModule sourceFunction
      labels discr alts fallback target ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    Wasm.wp module target Q targetStore
      { targetLocals with values := tail } hostEnv

/-- First end-to-end W6.6 composition rule. It reuses the W5 compiler/adapter
theorem but executes the generated object-case test against the concrete W6
host, deriving the exact physical discriminator word from related source and
target locals. -/
theorem caseChainWP_constructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {thenTarget elseTarget : Wasm.Program}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {witness : RefinementWitness} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    {discrIndex getTagIndex : Nat} {imp : Wasm.ImportDecl}
    {sourceObject : Value} {actualTag : Nat}
    (modeEq : Fir.Wasm.caseDiscriminatorMode context discr = .objectTag)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (thenAdapted :
      FirTalos.Correctness.CodeAdapted context sourceModule sourceFunction
        labels code thenTarget)
    (elseAdapted :
      FirTalos.Correctness.CaseChainAdapted context sourceModule sourceFunction
        labels discr alts fallback elseTarget)
    (discrFound :
      findFVar? (functionBindings sourceFunction) discr = some discrIndex)
    (discrKind :
      (functionBindings sourceFunction)[discrIndex]?.map Prod.snd =
        some .tobject)
    (getTagFound :
      callIndex? sourceModule (.runtime .getTag) = some getTagIndex)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (sourceLookup : lookup sourceEnv discr = some sourceObject)
    (hImp : module.imports[getTagIndex]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : getTagIndex < module.imports.length)
    (hContract : spec.contracts[getTagIndex]? = some getTagContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (tagged : getTag sourceRuntime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (expectedFits : info.cidx < UInt32.size)
    (selectedWP :
      Wasm.wp module
        (if actualTag = info.cidx then thenTarget else elseTarget)
        (CaseResumePost module hostEnv [] Q tail) initial
        { locals with values := tail } hostEnv) :
    CaseChainWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv discr (.ctorAlt info code :: alts) fallback
      [.localGet discrIndex, .call getTagIndex,
        .const (UInt32.ofNat info.cidx), .eq,
        .iff 0 0 thenTarget elseTarget]
      initial locals witness tail Q := by
  obtain ⟨index, kind, physical, found, kindAt, localValue,
      physicalRelated⟩ := stateRelated.2.2 sourceLookup
  rw [discrFound] at found
  have indexEq := Option.some.inj found
  subst index
  rw [discrKind] at kindAt
  have kindEq := Option.some.inj kindAt
  subst kind
  refine ⟨caseChainAdapted_constructor modeEq fits thenAdapted elseAdapted
    discrFound getTagFound, stateRelated, ?_⟩
  cases physicalRelated with
  | word32 valueRelated =>
      apply wp_getTag_case_test
        (spec := spec) (rest := [])
        (locals := { locals with values := tail })
        (by simpa [Wasm.Locals.get] using localValue)
        hImp hSat hi hContract hParams hResults stateRelated.1 valueRelated
          tagged actualFits expectedFits
      rw [stateRelated.clearFailure]
      exact selectedWP
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

/--
Concrete-host rule for a scalar `UInt8` constructor test.

`StateRelated` and the compiler's `.uint8` local kind recover the exact direct
i32 discriminator lane. The semantic `getTag` equation then identifies that
lane with the source-selected tag, so no host contract or runtime call is
needed.
-/
theorem caseChainWP_scalarUInt8_constructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {thenTarget elseTarget : Wasm.Program}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {witness : RefinementWitness} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    {discrIndex : Nat} {sourceValue : Value} {actualTag : Nat}
    (modeEq : Fir.Wasm.caseDiscriminatorMode context discr = .scalarUInt8)
    (fits : Fir.Wasm.constructorTagFitsUInt8 info = true)
    (thenAdapted :
      FirTalos.Correctness.CodeAdapted context sourceModule sourceFunction
        labels code thenTarget)
    (elseAdapted :
      FirTalos.Correctness.CaseChainAdapted context sourceModule sourceFunction
        labels discr alts fallback elseTarget)
    (discrFound :
      findFVar? (functionBindings sourceFunction) discr = some discrIndex)
    (discrKind :
      (functionBindings sourceFunction)[discrIndex]?.map Prod.snd =
        some .uint8)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (sourceLookup : lookup sourceEnv discr = some sourceValue)
    (tagged : getTag sourceRuntime sourceValue = .ok actualTag)
    (expectedFits : info.cidx < UInt8.size)
    (selectedWP :
      Wasm.wp module
        (if actualTag = info.cidx then thenTarget else elseTarget)
        (CaseResumePost module hostEnv [] Q tail) initial
        { locals with values := tail } hostEnv) :
    CaseChainWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv discr (.ctorAlt info code :: alts) fallback
      [.localGet discrIndex, .const (UInt32.ofNat info.cidx), .eq,
        .iff 0 0 thenTarget elseTarget]
      initial locals witness tail Q := by
  obtain ⟨index, kind, physical, found, kindAt, localValue,
      physicalRelated⟩ := stateRelated.2.2 sourceLookup
  rw [discrFound] at found
  have indexEq := Option.some.inj found
  subst index
  rw [discrKind] at kindAt
  have kindEq := Option.some.inj kindAt
  subst kind
  refine ⟨caseChainAdapted_scalarUInt8_constructor modeEq fits thenAdapted
    elseAdapted discrFound, stateRelated, ?_⟩
  cases physicalRelated with
  | word32 valueRelated =>
      cases valueRelated with
      | @uint8 word value encoded =>
          have fits64 : value.toNat < UInt64.size := by
            have sizeLe : UInt8.size ≤ UInt64.size := by native_decide
            exact lt_of_lt_of_le (UInt8.toNat_lt_size value) sizeLe
          have valueToNat :
              (UInt64.ofNat value.toNat).toNat = value.toNat :=
            UInt64.toNat_ofNat_of_lt' fits64
          have tagEq : actualTag = value.toNat := by
            simpa [getTag, ScalarValue.toUInt64, ScalarValue.rawBits,
              valueToNat] using tagged.symm
          subst actualTag
          apply wp_scalarUInt8_case_test (host := Host) (rest := [])
            value.toNat info.cidx
          · simpa [Wasm.Locals.get, encoded] using localValue
          · exact UInt8.toNat_lt_size value
          · exact expectedFits
          · convert selectedWP using 1
            funext continuation
            cases continuation with
            | Break level nextStore nextLocals =>
                cases level <;> (apply propext; rfl)
            | _ => apply propext; rfl
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

end FirTalos.Concrete
