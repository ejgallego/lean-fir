import Fir.Wasm.Emit.ResidentArray
import Fir.Wasm.Concrete.ArrayMutationCorrectness
import FirTalos.ConcreteResidentBigNumeric
import FirTalos.ConcreteResidentPrimitives
import FirTalos.ConcreteResidentRelease

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete

/-!
# Resident trusted-Array refinement

This module connects W7's production trusted Array helpers to W6's concrete
heap relation.  The first boundary below isolates the optimization shared by
`Array.uset`, `Array.set`, and `Array.set!`: a valid live ordinary Array whose
semantic reference count is one has the exact physical header word `1`, so the
trusted helper takes its in-place replacement arm and returns before the
deferred capacity load.
-/

namespace ResidentArray

/-- Talos spelling of W7's constant-time live-element address calculation.
The scale primitive is shared with resident Nat/BigNumeric rather than proved
again instruction by instruction. -/
def elementAddressProgram (arrayIndex indexIndex cursorIndex : Nat) :
    Wasm.Program :=
  [.localGet indexIndex, .localSet cursorIndex] ++
    ResidentPrimitives.scale8Program cursorIndex cursorIndex ++ [
    .localGet arrayIndex,
    .const (UInt32.ofNat headerBytes),
    .add,
    .localGet cursorIndex,
    .add,
    .localSet cursorIndex]

/-- Exact modular address produced by `elementAddressProgram`. -/
def elementAddressWord (array index : UInt32) : UInt32 :=
  array + UInt32.ofNat headerBytes + ResidentPrimitives.scale8Word index

/-- On W6 mathematical addresses, the modular result is the exact resident
Array low-word slot address. -/
theorem elementAddressWord_ofNat (address index : Nat) :
    elementAddressWord (UInt32.ofNat address) (UInt32.ofNat index) =
      UInt32.ofNat
        (address + headerBytes + target.semanticSlotBytes * index) := by
  unfold elementAddressWord
  rw [ResidentPrimitives.scale8Word_eq_mul8]
  simp [target]

/-- Execute the complete resident Array element-address calculation.  Local
updates are explicit because the rule is independent of any installed helper
frame; installed aliases discharge them from their concrete local vectors. -/
theorem wp_elementAddressProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterIndex afterFirst afterSecond afterThird afterFinal :
      Wasm.Locals}
    {arrayIndex indexIndex cursorIndex : Nat} {array index : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (indexFound : initial.get indexIndex = some (.i32 index))
    (indexSet :
      ({ initial with values := .i32 index :: tail }).set?
          cursorIndex (.i32 index) = some afterIndex)
    (firstSet :
      ({ afterIndex with values := .i32 (index + index) :: tail }).set?
          cursorIndex (.i32 (index + index)) = some afterFirst)
    (secondSet :
      ({ afterFirst with values :=
          (.i32 (index + index + (index + index))) :: tail }).set?
          cursorIndex (.i32 (index + index + (index + index))) =
        some afterSecond)
    (thirdSet :
      ({ afterSecond with values :=
          (.i32 (ResidentPrimitives.scale8Word index)) :: tail }).set?
          cursorIndex (.i32 (ResidentPrimitives.scale8Word index)) =
        some afterThird)
    (arrayAfter : afterThird.get arrayIndex = some (.i32 array))
    (finalSet :
      ({ afterThird with values := .i32 (elementAddressWord array index) :: tail }).set?
          cursorIndex (.i32 (elementAddressWord array index)) = some afterFinal)
    (continued :
      Wasm.wp module rest Q store { afterFinal with values := tail } env) :
    Wasm.wp module
      (elementAddressProgram arrayIndex indexIndex cursorIndex ++ rest)
      Q store { initial with values := tail } env := by
  have indexAt (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get indexIndex =
        some (.i32 index) := by
    simpa using indexFound
  have indexUpdate := FirTalos.Correctness.localUpdate_of_set? indexSet
  have cursorAfterIndex : afterIndex.get cursorIndex = some (.i32 index) :=
    indexUpdate.1
  have thirdUpdate := FirTalos.Correctness.localUpdate_of_set? thirdSet
  have cursorAfterThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get cursorIndex =
        some (.i32 (ResidentPrimitives.scale8Word index)) := by
    simpa using thirdUpdate.1
  have arrayAt (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get arrayIndex =
        some (.i32 array) := by
    simpa using arrayAfter
  unfold elementAddressProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    indexAt, Wasm.wp_localSet_cons, indexSet]
  apply ResidentPrimitives.wp_scale8Program cursorAfterIndex firstSet secondSet
    thirdSet
  simp only [Wasm.wp_localGet_cons, arrayAt]
  change Wasm.wp module
    (.const (UInt32.ofNat headerBytes) :: .add :: .localGet cursorIndex ::
      .add :: .localSet cursorIndex :: rest) Q store
    { afterThird with values := .i32 array :: tail } env
  simp only [Wasm.wp_const_cons, Wasm.wp_add_cons]
  simp only [Wasm.wp_localGet_cons, cursorAfterThird, Wasm.wp_add_cons]
  have addressEq :
      ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + array) =
        elementAddressWord array index := by
    unfold elementAddressWord
    bv_decide
  rw [addressEq]
  simp only [Wasm.wp_localSet_cons, finalSet]
  exact continued

/-- A related live Array slot is accepted by Talos's checked `i32.store`
boundary at the exact resident low-word address. -/
theorem liveElementWasmInBounds
    {host : Type} {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header} {store : Wasm.Store host}
    (objectRelated :
      ResidentArrayObjectRel state witness address elements capacity header)
    (frontier : state.FrontierInvariant)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (index : Nat) (indexValid : index < elements.size) :
    (UInt32.ofNat
        (address.value + headerBytes + target.semanticSlotBytes * index)).toNat +
        4 ≤ store.mem.pages * wasmPageBytes := by
  have inBounds :=
    objectRelated.liveElementWordInBounds frontier index indexValid
  rw [memoryRelated.address_roundtrip inBounds]
  rw [← memoryRelated.size_eq]
  omega

/-- One successful concrete raw Array replacement and the matching Talos
`i32.store` preserve the byte-for-byte resident-memory relation. -/
theorem writeElementRaw_preservesMemory
    {host : Type} {state result : MemoryState}
    {witness : RefinementWitness} {address word : Word32}
    {elements : Array Value} {capacity : Nat} {header : Header}
    {store : Wasm.Store host}
    (objectRelated :
      ResidentArrayObjectRel state witness address elements capacity header)
    (frontier : state.FrontierInvariant)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (index : Nat) (indexValid : index < elements.size)
    (operation :
      writeResidentArrayElementRaw state address index word = .ok result) :
    ResidentMemoryRel result
      (store.mem.write32
        (UInt32.ofNat
          (address.value + headerBytes + target.semanticSlotBytes * index))
        (UInt32.ofNat word.value)) := by
  obtain ⟨memory, written, resultEq⟩ :=
    objectRelated.writeElementRaw_decompose index word indexValid operation
  subst result
  have inBounds :=
    objectRelated.liveElementWordInBounds frontier index indexValid
  unfold LinearMemory.writeWord32 at written
  exact memoryRelated.writeUInt32 inBounds written

/-- A related semantic live element exposes one exact borrowed physical word
to resident Wasm.  Borrowing does not retain it; the replacement branch must
later pass this same word to the checked decrement gate. -/
theorem liveElementResidentRead
    {host : Type} {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {elements : Array Value} {capacity : Nat}
    {header : Header} {store : Wasm.Store host}
    (objectRelated :
      ResidentArrayObjectRel state witness address elements capacity header)
    (frontier : state.FrontierInvariant)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (index : Nat) (value : Value)
    (valueAt : elements[index]? = some value) :
    ∃ word,
      state.memory.readWord32
          (address.value + headerBytes + target.semanticSlotBytes * index) =
        .ok word ∧
      ValueRel witness .tobject (.word32 word) value ∧
      store.mem.read32
          (UInt32.ofNat
            (address.value + headerBytes + target.semanticSlotBytes * index)) =
        UInt32.ofNat word.value := by
  have indexValid : index < elements.size :=
    Array.getElem?_eq_some_iff.mp valueAt |>.1
  obtain ⟨word, read, valueRelated⟩ :=
    objectRelated.liveElements index value valueAt
  have inBounds :=
    objectRelated.liveElementWordInBounds frontier index indexValid
  exact ⟨word, read, valueRelated,
    memoryRelated.readWord32_eq_read32 inBounds read⟩

/-- Borrow the displaced resident Array word before any ownership effect. -/
def borrowElementProgram (cursorIndex elementIndex : Nat) : Wasm.Program := [
  .localGet cursorIndex,
  .load32 0,
  .localSet elementIndex]

/-- Execute the borrowed old-word load.  The store is unchanged and the old
word is retained in `elementIndex`, exactly as required by the checked
decrement gate that must run next. -/
theorem wp_borrowElementProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterOld : Wasm.Locals}
    {cursorIndex elementIndex : Nat}
    {cursor oldWord : UInt32} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (cursorFound : initial.get cursorIndex = some (.i32 cursor))
    (oldRead : store.mem.read32 cursor = oldWord)
    (inBounds : cursor.toNat + 4 ≤ store.mem.pages * wasmPageBytes)
    (oldSet :
      ({ initial with values := .i32 oldWord :: tail }).set?
          elementIndex (.i32 oldWord) = some afterOld)
    (continued : Wasm.wp module rest Q store
      { afterOld with values := tail } env) :
    Wasm.wp module
      (borrowElementProgram cursorIndex elementIndex ++ rest)
      Q store { initial with values := tail } env := by
  have cursorAt (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get cursorIndex =
        some (.i32 cursor) := by
    simpa using cursorFound
  have loadInBounds :
      ¬(cursor.toNat + (0 : UInt32).toNat + 4 >
        store.mem.pages * wasmPageBytes) := by
    simpa using Nat.not_lt.mpr inBounds
  unfold borrowElementProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    cursorAt, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using loadInBounds),
    UInt32.add_zero, oldRead]
  simp only [Wasm.wp_localSet_cons, oldSet]
  exact continued

/-- Install the consumed replacement word after the displaced word's checked
decrement has completed. -/
def writeReplacementProgram (cursorIndex valueIndex : Nat) : Wasm.Program := [
  .localGet cursorIndex,
  .localGet valueIndex,
  .store32 0]

/-- Execute the final replacement store and expose its exact updated Talos
memory to the continuation. -/
theorem wp_writeReplacementProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {cursorIndex valueIndex : Nat}
    {cursor newWord : UInt32} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (cursorFound : locals.get cursorIndex = some (.i32 cursor))
    (valueFound : locals.get valueIndex = some (.i32 newWord))
    (inBounds : cursor.toNat + 4 ≤ store.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (ResidentMemoryRel.write32Store store cursor newWord)
      { locals with values := tail } env) :
    Wasm.wp module
      (writeReplacementProgram cursorIndex valueIndex ++ rest)
      Q store { locals with values := tail } env := by
  have continued' : Wasm.wp module rest Q
      (ResidentMemoryRel.write32Store store (cursor + 0) newWord)
      { locals with values := tail } env := by
    simpa only [UInt32.add_zero] using continued
  unfold writeReplacementProgram
  exact ResidentMemoryRel.wp_store32_localGet_of_inBounds cursorFound valueFound
    inBounds continued'

/-- Native-order ownership core of trusted Array replacement: borrow the old
word, run the shared checked decrement, and only then overwrite the slot. -/
def replaceElementOwnershipProgram
    (cursorIndex valueIndex elementIndex decrementIndex : Nat) : Wasm.Program :=
  borrowElementProgram cursorIndex elementIndex ++
    ResidentRelease.checkedDecrementLocalProgram elementIndex decrementIndex ++
    writeReplacementProgram cursorIndex valueIndex

/-- Compose the heap-valued arm of native-order Array replacement from the
shared checked-decrement theorem.  Read and write bounds are separated because
the recursive ownership call may change the store while preserving the parent
allocation through the caller's refinement invariant. -/
theorem wp_replaceElementOwnershipProgram_heap
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store middleStore : Wasm.Store host}
    {initial afterOld : Wasm.Locals}
    {cursorIndex valueIndex elementIndex decrementIndex : Nat}
    {cursor newWord : UInt32} {oldWord : Word32} {rest : Wasm.Program}
    (cursorFound : initial.get cursorIndex = some (.i32 cursor))
    (oldRead : store.mem.read32 cursor = UInt32.ofNat oldWord.value)
    (readInBounds : cursor.toNat + 4 ≤ store.mem.pages * wasmPageBytes)
    (oldSet :
      ({ initial with values := [.i32 (UInt32.ofNat oldWord.value)] }).set?
          elementIndex (.i32 (UInt32.ofNat oldWord.value)) = some afterOld)
    (cursorAfter : afterOld.get cursorIndex = some (.i32 cursor))
    (valueAfter : afterOld.get valueIndex = some (.i32 newWord))
    (oldHeap : oldWord.classify = .heap)
    (decrementRun : Wasm.TerminatesWith env module decrementIndex store
      [.i32 1, .i32 (UInt32.ofNat oldWord.value)]
      (fun next values => next = middleStore ∧ values = []))
    (writeInBounds :
      cursor.toNat + 4 ≤ middleStore.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (ResidentMemoryRel.write32Store middleStore cursor newWord)
      { afterOld with values := [] } env) :
    Wasm.wp module
      (replaceElementOwnershipProgram cursorIndex valueIndex elementIndex
          decrementIndex ++ rest)
      Q store { initial with values := [] } env := by
  have oldUpdate := FirTalos.Correctness.localUpdate_of_set? oldSet
  have decrementRun' :
      Wasm.TerminatesWith env module decrementIndex store
        ([.i32 1, .i32 (UInt32.ofNat oldWord.value)] ++
          ({ afterOld with values := [] } : Wasm.Locals).values)
        (fun next values =>
          next = middleStore ∧
            values = ({ afterOld with values := [] } : Wasm.Locals).values) := by
    simpa using decrementRun
  have writeWP := wp_writeReplacementProgram cursorAfter valueAfter
    writeInBounds continued
  have decrementWP :=
    ResidentRelease.wp_checkedDecrementLocalProgram_classifiedHeap_then
      (locals := { afterOld with values := [] }) oldUpdate.1 oldHeap
      decrementRun' writeWP
  have borrowWP := wp_borrowElementProgram cursorFound oldRead readInBounds
    oldSet decrementWP
  simpa [replaceElementOwnershipProgram, List.append_assoc] using borrowWP

/-- Representation-complete native-order replacement.  Tagged `.tobject`
elements take the local no-op gate and write in the original store; heap
elements resume from the exact store produced by the shared decrement helper. -/
theorem wp_replaceElementOwnershipProgram_tobject
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterOld : Wasm.Locals}
    {cursorIndex valueIndex elementIndex decrementIndex : Nat}
    {cursor newWord : UInt32} {oldWord : Word32}
    {witness : RefinementWitness} {oldValue : Value}
    {rest : Wasm.Program}
    (oldRelated : ValueRel witness .tobject (.word32 oldWord) oldValue)
    (valid : witness.WellFormed)
    (cursorFound : initial.get cursorIndex = some (.i32 cursor))
    (oldRead : store.mem.read32 cursor = UInt32.ofNat oldWord.value)
    (readInBounds : cursor.toNat + 4 ≤ store.mem.pages * wasmPageBytes)
    (oldSet :
      ({ initial with values := [.i32 (UInt32.ofNat oldWord.value)] }).set?
          elementIndex (.i32 (UInt32.ofNat oldWord.value)) = some afterOld)
    (cursorAfter : afterOld.get cursorIndex = some (.i32 cursor))
    (valueAfter : afterOld.get valueIndex = some (.i32 newWord))
    (noopWriteInBounds :
      cursor.toNat + 4 ≤ store.mem.pages * wasmPageBytes)
    (noopContinued : Wasm.wp module rest Q
      (ResidentMemoryRel.write32Store store cursor newWord)
      { afterOld with values := [] } env)
    (heapEffect : oldWord.classify = .heap →
      ∃ middleStore,
        Wasm.TerminatesWith env module decrementIndex store
          [.i32 1, .i32 (UInt32.ofNat oldWord.value)]
          (fun next values => next = middleStore ∧ values = []) ∧
        cursor.toNat + 4 ≤ middleStore.mem.pages * wasmPageBytes ∧
        Wasm.wp module rest Q
          (ResidentMemoryRel.write32Store middleStore cursor newWord)
          { afterOld with values := [] } env) :
    Wasm.wp module
      (replaceElementOwnershipProgram cursorIndex valueIndex elementIndex
          decrementIndex ++ rest)
      Q store { initial with values := [] } env := by
  have oldUpdate := FirTalos.Correctness.localUpdate_of_set? oldSet
  have oldFound :
      ({ afterOld with values := [] } : Wasm.Locals).get elementIndex =
        some (.i32 (UInt32.ofNat oldWord.value)) := by
    simpa using oldUpdate.1
  have noopWP := wp_writeReplacementProgram (tail := []) cursorAfter
    valueAfter noopWriteInBounds noopContinued
  have checkedWP :=
    ResidentRelease.ValueRel.wp_checkedDecrementLocalProgram_tobject_then
      (locals := { afterOld with values := [] }) oldRelated valid oldFound
      noopWP (fun oldHeap => by
      obtain ⟨middleStore, decrementRun, writeInBounds, continued⟩ :=
        heapEffect oldHeap
      have decrementRun' :
          Wasm.TerminatesWith env module decrementIndex store
            ([.i32 1, .i32 (UInt32.ofNat oldWord.value)] ++
              ({ afterOld with values := [] } : Wasm.Locals).values)
            (fun next values =>
              next = middleStore ∧
                values = ({ afterOld with values := [] } : Wasm.Locals).values) := by
        simpa using decrementRun
      exact ⟨middleStore, decrementRun',
        wp_writeReplacementProgram (tail := []) cursorAfter valueAfter
          writeInBounds continued⟩)
  have borrowWP := wp_borrowElementProgram cursorFound oldRead readInBounds
    oldSet checkedWP
  simpa [replaceElementOwnershipProgram, List.append_assoc] using borrowWP

/-- Exact Talos spelling of the production trusted exclusivity probe.  The
exclusive branch is kept abstract so the same control theorem can be reused by
all three installed helpers and by the typed `Array.set` caller rewrite. -/
def trustedExclusivePrefixProgram (arrayIndex : Nat)
    (exclusive : Wasm.Program) : Wasm.Program := [
  .localGet arrayIndex,
  .load32 (UInt32.ofNat headerRefCountOffset),
  .const 1,
  .eq,
  .iff 0 0 exclusive []]

/-- Function-local exclusive branches end by returning the Array address.
Keeping that fact in the postcondition rules out structured fallthrough and
branch completions before the deferred suffix is appended. -/
def ReturnOnly (Q : Wasm.Assertion host) : Wasm.Assertion host
  | continuation@(.Return _ _) => Q continuation
  | _ => False

/-- Semantic and concrete admission for the trusted in-place Array arm.  It
contains no compiler certificate: every field is runtime state already needed
by the whole-heap refinement and ownership proofs. -/
structure TrustedExclusiveAdmission
    (state : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (location : Location) (address : Word32)
    (cell : HeapCell) (elements : Array Value) (capacity : Nat) : Prop where
  heapRelated : LiveHeapRel state witness runtime
  canonicalHeaders :
    ResidentRelease.CanonicalMappedHeadersRel state witness
  mapped : witness.locations.lookup? location = some address
  found : findCell? runtime.heap location = some cell
  live : cell.live = true
  ordinary : cell.persistent = false
  exclusive : cell.rc = 1
  objectEq : cell.object = .array elements capacity
  descriptor : witness.descriptors.lookup? address = some (.array capacity)

/-- The semantic exclusivity premise determines the complete related Array
header, including its exact raw word representation. -/
theorem TrustedExclusiveAdmission.objectAdmission
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {elements : Array Value} {capacity : Nat}
    (admission : TrustedExclusiveAdmission state witness runtime location
      address cell elements capacity) :
    ∃ header,
      ResidentArrayObjectRel state witness address elements capacity header ∧
      header.refCount = 1 ∧
      header.persistent = false ∧
      Header.ExactWords state.memory address header := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    admission.heapRelated.concreteToSemantic location address admission.mapped
  rw [admission.found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true admission.live
  cases targetRelated with
  | constructor descriptor storedObjectEq objectRelated headerRead headerKind
      refCount persistent cellLive =>
      rw [admission.objectEq] at storedObjectEq
      contradiction
  | boxed descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [admission.objectEq] at storedObjectEq
      contradiction
  | natural descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [admission.objectEq] at storedObjectEq
      contradiction
  | integer descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [admission.objectEq] at storedObjectEq
      contradiction
  | string descriptor storedObjectEq objectRelated refCount persistent cellLive =>
      rw [admission.objectEq] at storedObjectEq
      contradiction
  | @array storedElements storedCapacity header _ descriptor storedObjectEq
      objectRelated refCount persistent cellLive =>
      have expectedDescriptor := admission.descriptor
      rw [descriptor] at expectedDescriptor
      have descriptorEq := Option.some.inj expectedDescriptor
      cases descriptorEq
      rw [admission.objectEq] at storedObjectEq
      have objectParts := HeapObject.array.inj storedObjectEq
      cases objectParts.1
      cases objectParts.2
      have refCountOne : header.refCount = 1 := by
        apply UInt32.toNat_inj.mp
        simpa [admission.exclusive] using refCount
      have persistentFalse : header.persistent = false :=
        persistent.trans admission.ordinary
      exact ⟨header, objectRelated, refCountOne,
        persistentFalse,
        admission.canonicalHeaders admission.mapped header
          objectRelated.headerRead⟩
  | closure closureRelated =>
      obtain ⟨function, arity, captures, storedObjectEq⟩ :=
        closureRelated.objectEq
      rw [admission.objectEq] at storedObjectEq
      contradiction

/-- Transport the exclusive Array's exact reference-count lane to Talos
memory.  This is the precise condition tested by the production trusted
helper; neither decoded flags nor a source-shape assumption enters the fact. -/
theorem TrustedExclusiveAdmission.residentRefCountRead
    {host : Type} {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {elements : Array Value} {capacity : Nat}
    {store : Wasm.Store host}
    (admission : TrustedExclusiveAdmission state witness runtime location
      address cell elements capacity)
    (memoryRelated : ResidentMemoryRel state store.mem) :
    ¬((UInt32.ofNat address.value).toNat +
        (UInt32.ofNat headerRefCountOffset).toNat + 4 >
      store.mem.pages * wasmPageBytes) ∧
    store.mem.read32
      (UInt32.ofNat address.value + UInt32.ofNat headerRefCountOffset) = 1 := by
  obtain ⟨header, objectRelated, refCountOne, _persistent, exactWords⟩ :=
    admission.objectAdmission
  have headerInBounds :
      address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans objectRelated.headerOwned
      admission.heapRelated.frontier.cursorInBounds
  have concreteRead :
      state.memory.readUInt32 (address.value + headerRefCountOffset) =
        .ok (1 : UInt32) := by
    rw [← refCountOne]
    exact exactWords.readRefCount
  exact ResidentBigNumeric.residentHeaderUInt32 memoryRelated headerInBounds
    (by simp [headerRefCountOffset, headerBytes]) concreteRead

/-- An admitted exclusive Array takes the trusted early branch.  In
particular, if that branch returns then instructions appended after the probe
(including the newly deferred capacity load and shared-copy tail) are not
executed. -/
theorem wp_trustedExclusivePrefixProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {arrayIndex : Nat} {address : Word32}
    {tail : List Wasm.Value} {exclusive rest : Wasm.Program}
    (arrayFound : locals.get arrayIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (refCountInBounds :
      ¬((UInt32.ofNat address.value).toNat +
          (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (UInt32.ofNat address.value + UInt32.ofNat headerRefCountOffset) = 1)
    (noFallthrough : ∀ nextStore nextLocals,
      ¬Q (.Fallthrough nextStore nextLocals))
    (exclusiveWP : Wasm.wp module exclusive (ReturnOnly Q) store
      { locals with values := tail } env) :
    Wasm.wp module
      (trustedExclusivePrefixProgram arrayIndex exclusive ++ rest)
      Q store { locals with values := tail } env := by
  apply FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
    noFallthrough
  have arrayFound' (values : List Wasm.Value) :
      ({ locals with values } : Wasm.Locals).get arrayIndex =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa using arrayFound
  unfold trustedExclusivePrefixProgram
  simp only [Wasm.wp_localGet_cons, arrayFound', Wasm.wp_load32_cons]
  have refCountInBounds' :
      ¬((UInt32.ofNat address.value).toNat +
          (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using refCountInBounds
  rw [if_neg refCountInBounds', refCountRead]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  apply Wasm.wp.conseq _ exclusiveWP
  intro continuation completed
  cases continuation <;> simp_all [ReturnOnly]

/-- Whole-relation specialization of the trusted early-branch theorem. -/
theorem TrustedExclusiveAdmission.wp_prefix
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {elements : Array Value} {capacity : Nat}
    {locals : Wasm.Locals} {arrayIndex : Nat} {tail : List Wasm.Value}
    {exclusive rest : Wasm.Program}
    (admission : TrustedExclusiveAdmission state witness runtime location
      address cell elements capacity)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (arrayFound : locals.get arrayIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (noFallthrough : ∀ nextStore nextLocals,
      ¬Q (.Fallthrough nextStore nextLocals))
    (exclusiveWP : Wasm.wp module exclusive (ReturnOnly Q) store
      { locals with values := tail } env) :
    Wasm.wp module
      (trustedExclusivePrefixProgram arrayIndex exclusive ++ rest)
      Q store { locals with values := tail } env := by
  obtain ⟨inBounds, read⟩ := admission.residentRefCountRead memoryRelated
  exact wp_trustedExclusivePrefixProgram arrayFound inBounds read
    noFallthrough exclusiveWP

end ResidentArray

end FirTalos.Concrete
