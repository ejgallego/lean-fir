import Fir.Wasm.Concrete.HeapRefinement

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- One generated mutable value global. `none` is the exact logical form of
the companion initialization flag being zero; `some lane` means the flag is
one and the value global contains `lane`. -/
structure ConcreteGlobalSlot where
  name : Lean.Name
  kind : AbiKind
  value? : Option LaneValue := none

abbrev ConcreteGlobals := List ConcreteGlobalSlot

/-- Materialize the static generated-global declarations. Every companion
initialization flag starts clear, independently of the value lane's physical
zero initialization. -/
def ConcreteGlobals.declare
    (declarations : List (Lean.Name × AbiKind)) : ConcreteGlobals :=
  declarations.map fun (name, kind) => { name, kind }

def ConcreteGlobals.find? : ConcreteGlobals → Lean.Name → Option ConcreteGlobalSlot
  | [], _ => none
  | slot :: rest, name =>
      if slot.name = name then some slot else find? rest name

theorem ConcreteGlobals.find_declare_uninitialized
    {declarations : List (Lean.Name × AbiKind)} {name : Lean.Name}
    {slot : ConcreteGlobalSlot}
    (found : (ConcreteGlobals.declare declarations).find? name = some slot) :
    slot.value? = none := by
  induction declarations with
  | nil => simp [ConcreteGlobals.declare, ConcreteGlobals.find?] at found
  | cons declaration rest ih =>
      rcases declaration with ⟨declaredName, declaredKind⟩
      by_cases declared : declaredName = name
      · simp [ConcreteGlobals.declare, ConcreteGlobals.find?, declared] at found
        subst slot
        rfl
      · simp [ConcreteGlobals.declare, ConcreteGlobals.find?, declared] at found
        exact ih found

/-- Checked generated-global read. Unknown declarations, static ABI drift,
and reads before the flag is set remain distinct target failures. -/
def ConcreteGlobals.read (globals : ConcreteGlobals) (name : Lean.Name)
    (kind : AbiKind) : Except ConcreteError LaneValue := do
  let some slot := globals.find? name |
    throw (.targetGlobal (.unknownGlobal name))
  unless slot.kind == kind do
    throw (.targetGlobal (.kindMismatch name slot.kind kind))
  let some value := slot.value? |
    throw (.targetGlobal (.uninitializedGlobal name))
  return value

/-- Checked generated-global write. Static slots retain their declaration
order and ABI kind; only the initialization/value pair changes. -/
def ConcreteGlobals.write : ConcreteGlobals → Lean.Name → AbiKind → LaneValue →
    Except ConcreteError ConcreteGlobals
  | [], name, _, _ => .error (.targetGlobal (.unknownGlobal name))
  | slot :: rest, name, kind, value =>
      if slot.name = name then
        if slot.kind == kind then
          .ok ({ slot with value? := some value } :: rest)
        else
          .error (.targetGlobal (.kindMismatch name slot.kind kind))
      else do
        let rest ← write rest name kind value
        return slot :: rest

/-- A declared slot with the expected ABI kind makes the checked write
succeed, identifies the updated slot, and frames every other generated
global. -/
theorem ConcreteGlobals.write_of_find
    {globals : ConcreteGlobals} {name : Lean.Name}
    {kind : AbiKind} {value : LaneValue} {slot : ConcreteGlobalSlot}
    (found : globals.find? name = some slot)
    (kindEq : slot.kind = kind) :
    ∃ after,
      globals.write name kind value = .ok after ∧
      after.find? name = some { slot with value? := some value } ∧
      ∀ other, other ≠ name → after.find? other = globals.find? other := by
  induction globals generalizing slot with
  | nil => simp [ConcreteGlobals.find?] at found
  | cons head rest ih =>
      by_cases headName : head.name = name
      · simp [ConcreteGlobals.find?, headName] at found
        subst slot
        refine ⟨{ head with value? := some value } :: rest, ?_, ?_, ?_⟩
        · have kindSelf : (kind == kind) = true := by
            cases kind <;> decide
          simp [ConcreteGlobals.write, headName, kindEq, kindSelf]
        · simp [ConcreteGlobals.find?, headName]
        · intro other otherNe
          have nameOther : name ≠ other := Ne.symm otherNe
          simp [ConcreteGlobals.find?, headName, nameOther]
      · simp [ConcreteGlobals.find?, headName] at found
        obtain ⟨tailAfter, operation, updated, frame⟩ := ih found kindEq
        refine ⟨head :: tailAfter, ?_, ?_, ?_⟩
        · simp only [ConcreteGlobals.write, headName, if_false]
          rw [operation]
          rfl
        · simp [ConcreteGlobals.find?, headName, updated]
        · intro other otherNe
          by_cases otherHead : head.name = other
          · simp [ConcreteGlobals.find?, otherHead]
          · simp [ConcreteGlobals.find?, otherHead, frame other otherNe]

theorem ConcreteGlobals.read_of_find
    {globals : ConcreteGlobals} {name : Lean.Name} {kind : AbiKind}
    {value : LaneValue} {slot : ConcreteGlobalSlot}
    (found : globals.find? name = some slot)
    (kindEq : slot.kind = kind) (valueEq : slot.value? = some value) :
    globals.read name kind = .ok value := by
  have kindCheck : (slot.kind == kind) = true := by
    rw [kindEq]
    cases kind <;> decide
  simp [ConcreteGlobals.read, found, kindCheck, valueEq]
  rfl

/-- Pointwise refinement for the generated global table. Uninitialized
concrete slots deliberately have no semantic `Globals` entry; initialized
slots and semantic entries correspond in both directions. -/
structure ConcreteGlobalsRel (witness : RefinementWitness)
    (concrete : ConcreteGlobals) (semantic : Globals) : Prop where
  semanticToConcrete : ∀ name value,
    findGlobal? semantic name = some value →
    ∃ slot lane,
      concrete.find? name = some slot ∧ slot.value? = some lane ∧
        ValueRel witness slot.kind lane value
  concreteToSemantic : ∀ name slot lane,
    concrete.find? name = some slot → slot.value? = some lane →
    ∃ value,
      findGlobal? semantic name = some value ∧
        ValueRel witness slot.kind lane value

/-- Generated globals remain related when an allocation-producing operation
extends the proof witness. The physical table itself does not move. -/
theorem ConcreteGlobalsRel.witnessExtension
    {before after : RefinementWitness} {concrete : ConcreteGlobals}
    {semantic : Globals} (extension : before.Extends after)
    (related : ConcreteGlobalsRel before concrete semantic) :
    ConcreteGlobalsRel after concrete semantic := by
  constructor
  · intro name value found
    obtain ⟨slot, lane, slotFound, initialized, valueRelated⟩ :=
      related.semanticToConcrete name value found
    exact ⟨slot, lane, slotFound, initialized,
      valueRelated.witnessExtension extension⟩
  · intro name slot lane slotFound initialized
    obtain ⟨value, found, valueRelated⟩ :=
      related.concreteToSemantic name slot lane slotFound initialized
    exact ⟨value, found, valueRelated.witnessExtension extension⟩

/-- A freshly generated global table refines the empty semantic cache: every
declaration exists physically, but none is observable until its initialization
flag is set. -/
theorem ConcreteGlobalsRel.declared
    (witness : RefinementWitness)
    (declarations : List (Lean.Name × AbiKind)) :
    ConcreteGlobalsRel witness (ConcreteGlobals.declare declarations) [] := by
  constructor
  · intro name value found
    simp [findGlobal?] at found
  · intro name slot lane found initialized
    have uninitialized := ConcreteGlobals.find_declare_uninitialized found
    rw [uninitialized] at initialized
    contradiction

@[simp] theorem findGlobal_insert_self (globals : Globals) (name : Lean.Name)
    (value : Value) :
    findGlobal? (insertGlobal globals name value) name = some value := by
  simp [insertGlobal, findGlobal?]

private theorem findGlobal_filter_other (globals : Globals)
    (name other : Lean.Name) (different : other ≠ name) :
    findGlobal? (globals.filter fun entry => entry.fst != name) other =
      findGlobal? globals other := by
  induction globals with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨candidate, oldValue⟩
      by_cases candidateName : candidate = name
      · subst candidate
        have nameOther : name ≠ other := Ne.symm different
        simp [findGlobal?, nameOther, ih]
      · by_cases candidateOther : candidate = other
        · subst candidate
          simp [findGlobal?, candidateName]
        · simp [findGlobal?, candidateName, candidateOther, ih]

theorem findGlobal_insert_other (globals : Globals) (name other : Lean.Name)
    (value : Value) (different : other ≠ name) :
    findGlobal? (insertGlobal globals name value) other =
      findGlobal? globals other := by
  have nameOther : name ≠ other := Ne.symm different
  simp [insertGlobal, findGlobal?, nameOther,
    findGlobal_filter_other globals name other different]

/-- Writing a typed generated global refines FIR's semantic `insertGlobal`
update without changing any unrelated slot. -/
theorem ConcreteGlobalsRel.write
    {witness : RefinementWitness} {concrete : ConcreteGlobals}
    {semantic : Globals} {name : Lean.Name} {slot : ConcreteGlobalSlot}
    {kind : AbiKind} {lane : LaneValue} {value : Value}
    (related : ConcreteGlobalsRel witness concrete semantic)
    (found : concrete.find? name = some slot) (kindEq : slot.kind = kind)
    (valueRelated : ValueRel witness kind lane value) :
    ∃ after,
      concrete.write name kind lane = .ok after ∧
        ConcreteGlobalsRel witness after (insertGlobal semantic name value) := by
  obtain ⟨after, operation, updated, frame⟩ :=
    ConcreteGlobals.write_of_find found kindEq
  refine ⟨after, operation, ?_⟩
  constructor
  · intro query semanticValue semanticFound
    by_cases queryName : query = name
    · subst query
      rw [findGlobal_insert_self] at semanticFound
      have valueEq := Option.some.inj semanticFound
      subst semanticValue
      exact ⟨{ slot with value? := some lane }, lane, updated, rfl,
        by simpa [kindEq] using valueRelated⟩
    · rw [findGlobal_insert_other semantic name query value queryName]
        at semanticFound
      obtain ⟨oldSlot, oldLane, oldFound, oldValue, oldRelated⟩ :=
        related.semanticToConcrete query semanticValue semanticFound
      exact ⟨oldSlot, oldLane, by rw [frame query queryName]; exact oldFound,
        oldValue, oldRelated⟩
  · intro query querySlot queryLane queryFound laneFound
    by_cases queryName : query = name
    · subst query
      rw [updated] at queryFound
      have slotEq := Option.some.inj queryFound
      subst querySlot
      simp only at laneFound
      have laneEq := Option.some.inj laneFound
      subst queryLane
      exact ⟨value, findGlobal_insert_self semantic name value,
        by simpa [kindEq] using valueRelated⟩
    · have oldFound : concrete.find? query = some querySlot := by
        rw [← frame query queryName]
        exact queryFound
      obtain ⟨semanticValue, semanticFound, semanticRelated⟩ :=
        related.concreteToSemantic query querySlot queryLane oldFound laneFound
      exact ⟨semanticValue, by
        rw [findGlobal_insert_other semantic name query value queryName]
        exact semanticFound, semanticRelated⟩

/-- Concrete trace entries retain the static ABI metadata needed to relate
physical lanes to source-level external observations. -/
structure ConcreteExternalEvent where
  name : Lean.Name
  paramKinds : Array AbiKind
  args : Array LaneValue
  resultKind : AbiKind
  result : LaneValue

structure ConcreteExternalEventRel (witness : RefinementWitness)
    (concrete : ConcreteExternalEvent) (semantic : ExternalEvent) : Prop where
  name : concrete.name = semantic.name
  paramKindsSize : concrete.paramKinds.size = semantic.args.size
  argsSize : concrete.args.size = semantic.args.size
  arguments : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue) (value : Value),
    concrete.paramKinds[index]? = some kind →
    concrete.args[index]? = some lane →
    semantic.args[index]? = some value →
    ValueRel witness kind lane value
  result : ValueRel witness concrete.resultKind concrete.result semantic.result

theorem ConcreteExternalEventRel.witnessExtension
    {before after : RefinementWitness}
    {concrete : ConcreteExternalEvent} {semantic : ExternalEvent}
    (extension : before.Extends after)
    (related : ConcreteExternalEventRel before concrete semantic) :
    ConcreteExternalEventRel after concrete semantic := {
  name := related.name
  paramKindsSize := related.paramKindsSize
  argsSize := related.argsSize
  arguments := by
    intro index kind lane value kindFound laneFound valueFound
    exact (related.arguments index kind lane value kindFound laneFound valueFound).witnessExtension
      extension
  result := related.result.witnessExtension extension }

structure ConcreteTraceRel (witness : RefinementWitness)
    (concrete : Array ConcreteExternalEvent)
    (semantic : Array ExternalEvent) : Prop where
  size : concrete.size = semantic.size
  events : ∀ (index : Nat) (concreteEvent : ConcreteExternalEvent)
      (semanticEvent : ExternalEvent),
    concrete[index]? = some concreteEvent →
    semantic[index]? = some semanticEvent →
    ConcreteExternalEventRel witness concreteEvent semanticEvent

theorem ConcreteTraceRel.witnessExtension
    {before after : RefinementWitness}
    {concrete : Array ConcreteExternalEvent}
    {semantic : Array ExternalEvent}
    (extension : before.Extends after)
    (related : ConcreteTraceRel before concrete semantic) :
    ConcreteTraceRel after concrete semantic := {
  size := related.size
  events := by
    intro index concreteEvent semanticEvent concreteFound semanticFound
    exact (related.events index concreteEvent semanticEvent concreteFound semanticFound).witnessExtension
      extension }

theorem ConcreteTraceRel.push
    {witness : RefinementWitness}
    {concrete : Array ConcreteExternalEvent}
    {semantic : Array ExternalEvent}
    {concreteEvent : ConcreteExternalEvent}
    {semanticEvent : ExternalEvent}
    (related : ConcreteTraceRel witness concrete semantic)
    (eventRelated : ConcreteExternalEventRel witness concreteEvent semanticEvent) :
    ConcreteTraceRel witness (concrete.push concreteEvent)
      (semantic.push semanticEvent) := by
  constructor
  · simp [related.size]
  · intro index foundConcrete foundSemantic concreteFound semanticFound
    by_cases last : index = concrete.size
    · subst index
      have semanticLast : concrete.size = semantic.size := related.size
      rw [Array.getElem?_push, if_pos rfl] at concreteFound
      rw [Array.getElem?_push, if_pos semanticLast] at semanticFound
      cases Option.some.inj concreteFound
      cases Option.some.inj semanticFound
      exact eventRelated
    · have semanticNotLast : index ≠ semantic.size := by
        simpa [related.size] using last
      rw [Array.getElem?_push, if_neg last] at concreteFound
      rw [Array.getElem?_push, if_neg semanticNotLast] at semanticFound
      exact related.events index foundConcrete foundSemantic
        concreteFound semanticFound

theorem ConcreteTraceRel.empty (witness : RefinementWitness) :
    ConcreteTraceRel witness #[] #[] := by
  constructor
  · rfl
  · intro index concreteEvent semanticEvent concreteFound
    simp at concreteFound

/-- Full concrete runtime state layers generated globals and observable host
state over the already-proved linear-memory heap. -/
structure ConcreteRuntimeState where
  heap : MemoryState := {}
  globals : ConcreteGlobals := []
  world : Nat := 0
  trace : Array ConcreteExternalEvent := #[]

def ConcreteRuntimeState.readGlobal (state : ConcreteRuntimeState)
    (name : Lean.Name) (kind : AbiKind) : Except ConcreteError LaneValue :=
  state.globals.read name kind

def ConcreteRuntimeState.writeGlobal (state : ConcreteRuntimeState)
    (name : Lean.Name) (kind : AbiKind) (value : LaneValue) :
    Except ConcreteError ConcreteRuntimeState := do
  let globals ← state.globals.write name kind value
  return { state with globals }

/-- `LiveHeapRel` depends only on the semantic heap and allocation cursor;
globals, world, and trace can therefore change in the layered runtime without
replaying any memory proof. -/
theorem LiveHeapRel.auxiliary
    {state : MemoryState} {witness : RefinementWitness}
    {before after : RuntimeState}
    (related : LiveHeapRel state witness before)
    (heapEq : after.heap = before.heap)
    (nextLocationEq : after.nextLocation = before.nextLocation) :
    LiveHeapRel state witness after := by
  refine {
    frontier := related.frontier
    witnessWellFormed := related.witnessWellFormed
    locationsBeforeNext := ?_
    releaseFuelBound := ?_
    descriptorsOwned := related.descriptorsOwned
    descriptorRegion := related.descriptorRegion
    descriptorDisjoint := related.descriptorDisjoint
    semanticToConcrete := ?_
    concreteToSemantic := ?_
    promoted := related.promoted }
  · intro location cell found
    rw [heapEq] at found
    have bound := related.locationsBeforeNext location cell found
    simpa [nextLocationEq] using bound
  · simpa [heapEq] using related.releaseFuelBound
  · intro location cell found
    rw [heapEq] at found
    exact related.semanticToConcrete location cell found
  · intro location address mapped
    obtain ⟨cell, found, cellRelated⟩ :=
      related.concreteToSemantic location address mapped
    exact ⟨cell, by simpa [heapEq] using found, cellRelated⟩

structure ConcreteRuntimeRel (concrete : ConcreteRuntimeState)
    (witness : RefinementWitness) (semantic : RuntimeState) : Prop where
  heap : LiveHeapRel concrete.heap witness semantic
  globals : ConcreteGlobalsRel witness concrete.globals semantic.globals
  world : concrete.world = semantic.world
  trace : ConcreteTraceRel witness concrete.trace semantic.trace

/-- Once the heap relation is established, a concrete runtime with freshly
declared globals refines the same semantic heap with empty cache and trace and
the initial world token. -/
theorem ConcreteRuntimeRel.initial
    {heap : MemoryState} {witness : RefinementWitness}
    {semantic : RuntimeState}
    (heapRelated : LiveHeapRel heap witness semantic)
    (globalsEmpty : semantic.globals = [])
    (worldInitial : semantic.world = 0)
    (traceEmpty : semantic.trace = #[])
    (declarations : List (Lean.Name × AbiKind)) :
    ConcreteRuntimeRel
      { heap, globals := ConcreteGlobals.declare declarations }
      witness semantic := by
  exact {
    heap := heapRelated
    globals := by
      rw [globalsEmpty]
      exact ConcreteGlobalsRel.declared witness declarations
    world := worldInitial.symm
    trace := by
      rw [traceEmpty]
      exact ConcreteTraceRel.empty witness }

/-- Complete generated-module entry state: empty concrete memory and semantic
runtime, frozen closure tables, and declared-but-uninitialized globals. -/
theorem ConcreteRuntimeRel.moduleInitial
    (dispatch : ClosureDispatchTable) (descriptors : ClosureDescriptorTable)
    (declarations : List (Lean.Name × AbiKind)) :
    ConcreteRuntimeRel {
      heap := MemoryState.initial
      globals := ConcreteGlobals.declare declarations }
      (initialWitness dispatch descriptors) ({} : RuntimeState) := by
  exact ConcreteRuntimeRel.initial (LiveHeapRel.initial dispatch descriptors)
    rfl rfl rfl declarations

/-- A successful concrete cache write and FIR `setGlobal` remain related at
the full runtime-state boundary. -/
theorem ConcreteRuntimeRel.writeGlobal
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {semantic : RuntimeState} {name : Lean.Name} {slot : ConcreteGlobalSlot}
    {kind : AbiKind} {lane : LaneValue} {value : Value}
    (related : ConcreteRuntimeRel concrete witness semantic)
    (found : concrete.globals.find? name = some slot)
    (kindEq : slot.kind = kind)
    (valueRelated : ValueRel witness kind lane value) :
    ∃ after,
      concrete.writeGlobal name kind lane = .ok after ∧
        ConcreteRuntimeRel after witness (semantic.setGlobal name value) := by
  obtain ⟨globals, operation, globalsRelated⟩ :=
    related.globals.write found kindEq valueRelated
  let after : ConcreteRuntimeState := { concrete with globals }
  refine ⟨after, ?_, ?_⟩
  · unfold ConcreteRuntimeState.writeGlobal
    rw [operation]
    rfl
  · exact {
      heap := related.heap.auxiliary rfl rfl
      globals := by
        simpa [RuntimeState.setGlobal] using globalsRelated
      world := related.world
      trace := related.trace }

/-- Any initialized semantic global has a checked concrete lane read at its
retained static ABI kind. -/
theorem ConcreteRuntimeRel.readGlobal
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {semantic : RuntimeState} {name : Lean.Name} {value : Value}
    (related : ConcreteRuntimeRel concrete witness semantic)
    (found : findGlobal? semantic.globals name = some value) :
    ∃ kind lane,
      concrete.readGlobal name kind = .ok lane ∧
        ValueRel witness kind lane value := by
  obtain ⟨slot, lane, slotFound, initialized, valueRelated⟩ :=
    related.globals.semanticToConcrete name value found
  exact ⟨slot.kind, lane,
    ConcreteGlobals.read_of_find slotFound rfl initialized, valueRelated⟩

end Fir.Wasm.Concrete
