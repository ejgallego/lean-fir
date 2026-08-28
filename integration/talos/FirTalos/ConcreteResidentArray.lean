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

/-- Proof-side spelling of W7's constant-time live-element address
calculation.  The symbolic identifiers are supplied by the closed production
function so this definition is shared by all three trusted aliases. -/
def elementAddressSourceProgram (array index cursor : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  [.localGet index, .localSet cursor] ++
    ResidentPrimitives.scale8Source cursor cursor ++ [
    .localGet array,
    .i32Const .uint32 (UInt32.ofNat headerBytes),
    .i32Add,
    .localGet cursor,
    .i32Add,
    .localSet cursor]

/-- Exact source instruction order of the repaired production exclusive arm:
borrow the displaced value, release it, install the consumed replacement, and
return the original Array. -/
def exclusiveReplacementSourceProgram
    (array index cursor value element : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  elementAddressSourceProgram array index cursor ++ [
    .localGet cursor,
    .i32Load .tobject 0,
    .localSet element] ++
    Fir.Wasm.Emit.ResidentRelease.checkedDecrementLocal element ++ [
    .localGet cursor,
    .localGet value,
    .i32Store .tobject 0,
    .localGet array,
    .ret]

/-- Source spelling of the common trusted reference-count probe. -/
def trustedExclusivePrefixSourceProgram (array : Lean.FVarId)
    (exclusive : List Fir.Wasm.Instruction) : List Fir.Wasm.Instruction := [
  .localGet array,
  .i32Load .uint32 (UInt32.ofNat headerRefCountOffset),
  .i32Const .uint32 1,
  .i32Eq,
  .ifElse exclusive []]

/-- The actual production trusted `Array.uset` body contains the common
exclusive replacement fragment at its exact post-decoding position. -/
theorem trustedUsetFunction_exclusiveSourceShape :
    Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.body =
      Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.body.take 10 ++
        trustedExclusivePrefixSourceProgram
          Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.params[1]!.1
          (exclusiveReplacementSourceProgram
            Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.locals[6]!.1
            Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.locals[8]!.1
            Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.params[3]!.1
            Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.locals[13]!.1) ++
        Fir.Wasm.Emit.ResidentArray.trustedUsetFunction.body.drop 15 := by
  rfl

/-- The actual production trusted `Array.set` body contains the same common
exclusive replacement fragment, after its natural-index decoder. -/
theorem trustedSetFunction_exclusiveSourceShape :
    Fir.Wasm.Emit.ResidentArray.trustedSetFunction.body =
      Fir.Wasm.Emit.ResidentArray.trustedSetFunction.body.take 11 ++
        trustedExclusivePrefixSourceProgram
          Fir.Wasm.Emit.ResidentArray.trustedSetFunction.params[1]!.1
          (exclusiveReplacementSourceProgram
            Fir.Wasm.Emit.ResidentArray.trustedSetFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentArray.trustedSetFunction.locals[6]!.1
            Fir.Wasm.Emit.ResidentArray.trustedSetFunction.locals[8]!.1
            Fir.Wasm.Emit.ResidentArray.trustedSetFunction.params[3]!.1
            Fir.Wasm.Emit.ResidentArray.trustedSetFunction.locals[13]!.1) ++
        Fir.Wasm.Emit.ResidentArray.trustedSetFunction.body.drop 16 := by
  rfl

/-- The actual production trusted `Array.set!` body contains the same common
exclusive replacement fragment, after its checked bounds prefix. -/
theorem trustedSetBangFunction_exclusiveSourceShape :
    Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.body =
      Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.body.take 11 ++
        trustedExclusivePrefixSourceProgram
          Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.params[1]!.1
          (exclusiveReplacementSourceProgram
            Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.params[1]!.1
            Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.locals[6]!.1
            Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.locals[8]!.1
            Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.params[3]!.1
            Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.locals[13]!.1) ++
        Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction.body.drop 16 := by
  rfl

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

/-- A resident Array payload replacement preserves canonical raw headers for
every mapped allocation.  The target uses the exact-word payload-write lemma;
all other allocations are framed by descriptor disjointness. -/
theorem ResidentRelease.CanonicalMappedHeadersRel.writeResidentArrayElementRaw
    {state result : MemoryState} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address word : Word32}
    {elements : Array Value} {capacity : Nat} {header : Header}
    (canonical : ResidentRelease.CanonicalMappedHeadersRel state witness)
    (heapRelated : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.array capacity))
    (objectRelated :
      ResidentArrayObjectRel state witness address elements capacity header)
    (index : Nat) (indexValid : index < elements.size)
    (value : Value)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (operation :
      writeResidentArrayElementRaw state address index word = .ok result) :
    ResidentRelease.CanonicalMappedHeadersRel result witness := by
  obtain ⟨generated, generatedOperation, frame, _finalValid,
      _finalObject⟩ :=
    objectRelated.writeElementRaw_targetFrame heapRelated.frontier index value
      word indexValid valueRelated
  have generatedEq : generated = result := by
    exact Except.ok.inj (generatedOperation.symm.trans operation)
  subst generated
  have exactBefore : Header.ExactWords state.memory address header :=
    canonical mapped header objectRelated.headerRead
  have exactAfter : Header.ExactWords result.memory address header :=
    objectRelated.writeElementRaw_exactWords heapRelated.frontier exactBefore
      index word indexValid operation
  have rawRead : Header.read state.memory address = .ok header :=
    (MemoryState.PrefixExtension.readLiveHeader_facts state address header
      objectRelated.headerRead).2.1
  intro nextLocation nextAddress nextMapped
  exact (ResidentRelease.CanonicalMappedHeadersRel.ofTargetMutation
    (before := state) (after := result) (witness := witness)
    (targetAddress := address) (targetDescriptor := .array capacity)
    (targetHeader := header) (canonical := canonical)
    (related := heapRelated) (targetFound := descriptorFound)
    (targetRead := rawRead) (targetLive := objectRelated.headerRead)
    (frame := frame) (targetExactAfter := exactAfter)) nextMapped

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

/-- Relational outcome of one native-order resident Array replacement.  The
ownership decrement and payload write remain separately visible, while the
caller receives the rebuilt semantic heap, byte-exact resident memory,
canonical mapped headers, retained capacities, and unchanged frontier. -/
def ReplacementSuccess
    {host : Type} (fuel : Nat) (before : MemoryState)
    (witness : RefinementWitness) (nextRuntime : RuntimeState)
    (address : Word32) (index : Nat) (oldWord newWord : Word32)
    (result : MemoryState) (finalStore : Wasm.Store host) : Prop :=
  ∃ released,
    decrementReferenceOnceFuel fuel before oldWord true
        witness.closureDescriptors = .ok released ∧
    writeResidentArrayElementRaw released address index newWord = .ok result ∧
    LiveHeapRel result witness nextRuntime ∧
    ResidentMemoryRel result finalStore.mem ∧
    ResidentRelease.CanonicalMappedHeadersRel result witness ∧
    MappedHeaderCapacityTransport before result witness ∧
    result.heapCursor = before.heapCursor

/-- Semantic/concrete/resident refinement of the heap-valued replacement arm.
The recursive decrement is consumed only through `ResidentOwnershipStep`; the
explicit `parentPreserved` premise is the compiler ownership obligation that
rules out releasing the uniquely mutated Array through its displaced value. -/
theorem wp_replaceElementOwnershipProgram_heap_refines
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {state : MemoryState} {witness : RefinementWitness}
    {runtime releasedRuntime nextRuntime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {elements : Array Value} {capacity fuel index : Nat}
    {oldValue newValue : Value} {oldWord newWord : Word32}
    {initial afterOld : Wasm.Locals}
    {cursorIndex valueIndex elementIndex decrementIndex : Nat}
    {rest : Wasm.Program}
    (admission : TrustedExclusiveAdmission state witness runtime location
      address cell elements capacity)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (oldAt : elements[index]? = some oldValue)
    (oldRead : state.memory.readWord32
      (address.value + headerBytes + target.semanticSlotBytes * index) =
        .ok oldWord)
    (oldRelated : ValueRel witness .tobject (.word32 oldWord) oldValue)
    (newRelated : ValueRel witness .tobject (.word32 newWord) newValue)
    (oldHeap : oldWord.classify = .heap)
    (semanticRelease :
      (match oldValue with
      | .object (.heap child) =>
          Fir.LeanIR.Impure.decLocationFuel fuel runtime child
      | _ => .ok runtime) = .ok releasedRuntime)
    (parentPreserved :
      findCell? releasedRuntime.heap location = some cell)
    (semanticSet :
      setCell releasedRuntime location
          { cell with
            object := .array (elements.set index newValue
              (Array.getElem?_eq_some_iff.mp oldAt).1) capacity } =
        .ok nextRuntime)
    (step : ResidentRelease.ResidentOwnershipStep env module decrementIndex
      fuel witness)
    (cursorFound : initial.get cursorIndex =
      some (.i32 (UInt32.ofNat
        (address.value + headerBytes + target.semanticSlotBytes * index))))
    (oldSet :
      ({ initial with values := [.i32 (UInt32.ofNat oldWord.value)] }).set?
          elementIndex (.i32 (UInt32.ofNat oldWord.value)) = some afterOld)
    (cursorAfter : afterOld.get cursorIndex =
      some (.i32 (UInt32.ofNat
        (address.value + headerBytes + target.semanticSlotBytes * index))))
    (valueAfter : afterOld.get valueIndex =
      some (.i32 (UInt32.ofNat newWord.value)))
    (continued : ∀ result finalStore,
      ReplacementSuccess fuel state witness nextRuntime address index oldWord
          newWord result finalStore →
      Wasm.wp module rest Q finalStore { afterOld with values := [] } env) :
    Wasm.wp module
      (replaceElementOwnershipProgram cursorIndex valueIndex elementIndex
          decrementIndex ++ rest)
      Q store { initial with values := [] } env := by
  have indexValid : index < elements.size :=
    (Array.getElem?_eq_some_iff.mp oldAt).1
  obtain ⟨header, objectRelated, _refCount, _ordinary, _exact⟩ :=
    admission.objectAdmission
  have initialInBounds := liveElementWasmInBounds objectRelated
    admission.heapRelated.frontier memoryRelated index indexValid
  have concreteInBounds :=
    objectRelated.liveElementWordInBounds admission.heapRelated.frontier index
      indexValid
  have oldReadWasm : store.mem.read32
      (UInt32.ofNat
        (address.value + headerBytes + target.semanticSlotBytes * index)) =
      UInt32.ofNat oldWord.value :=
    memoryRelated.readWord32_eq_read32 concreteInBounds oldRead
  have oldUpdate := FirTalos.Correctness.localUpdate_of_set? oldSet
  have oldFound :
      ({ afterOld with values := [] } : Wasm.Locals).get elementIndex =
        some (.i32 (UInt32.ofNat oldWord.value)) := by
    simpa using oldUpdate.1
  have ownership : OwnershipValueRel witness oldWord oldValue :=
    .intro .tobject (by rfl) oldRelated
  have checkedWP :=
    ResidentRelease.ResidentOwnershipStep.wp_checkedDecrementLocalProgram_heap_then
      (locals := { afterOld with values := [] })
      (rest := writeReplacementProgram cursorIndex valueIndex ++ rest)
      step ownership admission.heapRelated memoryRelated
      admission.canonicalHeaders semanticRelease oldFound rfl oldHeap
      (fun released middleStore concreteRelease releasedRelated
          releasedMemory canonicalAfter payloadFrame => by
        obtain ⟨releasedHeader, releasedObject⟩ :=
          releasedRelated.residentArrayObjectRel_of_mapped admission.mapped
            parentPreserved admission.live admission.objectEq
            admission.descriptor
        obtain ⟨result, actualRuntime, concreteWrite, semanticWrite,
            finalRelated, writeCapacity, writeCursor⟩ :=
          releasedRelated.writeResidentArrayElementRaw_refines
            admission.mapped parentPreserved admission.live
            admission.objectEq admission.descriptor index newValue newWord
            indexValid newRelated
        have runtimeEq : actualRuntime = nextRuntime := by
          rw [semanticSet] at semanticWrite
          exact (Except.ok.inj semanticWrite).symm
        subst actualRuntime
        have writeInBounds := liveElementWasmInBounds releasedObject
          releasedRelated.frontier releasedMemory index indexValid
        have finalMemory : ResidentMemoryRel result
            (ResidentMemoryRel.write32Store middleStore
              (UInt32.ofNat
                (address.value + headerBytes +
                  target.semanticSlotBytes * index))
              (UInt32.ofNat newWord.value)).mem :=
          writeElementRaw_preservesMemory releasedObject releasedRelated.frontier
            releasedMemory index indexValid concreteWrite
        have finalCanonical :
            ResidentRelease.CanonicalMappedHeadersRel result witness := by
          intro nextLocation nextAddress nextMapped
          exact
            (ResidentRelease.CanonicalMappedHeadersRel.writeResidentArrayElementRaw
              canonicalAfter releasedRelated admission.mapped
              admission.descriptor releasedObject index indexValid newValue
              newRelated concreteWrite) nextMapped
        have finalCapacity :
            MappedHeaderCapacityTransport state result witness :=
          payloadFrame.capacity.trans writeCapacity
        have finalCursor : result.heapCursor = state.heapCursor :=
          writeCursor.trans payloadFrame.cursor
        let finalStore := ResidentMemoryRel.write32Store middleStore
          (UInt32.ofNat
            (address.value + headerBytes + target.semanticSlotBytes * index))
          (UInt32.ofNat newWord.value)
        have success : ReplacementSuccess fuel state witness nextRuntime
            address index oldWord newWord result finalStore :=
          ⟨released, concreteRelease, concreteWrite, finalRelated,
            finalMemory, finalCanonical, finalCapacity, finalCursor⟩
        exact wp_writeReplacementProgram (tail := []) cursorAfter valueAfter
          writeInBounds (continued result finalStore success))
  have borrowWP := wp_borrowElementProgram cursorFound oldReadWasm
    initialInBounds oldSet checkedWP
  simpa [replaceElementOwnershipProgram, List.append_assoc] using borrowWP

/-- Complete native-order exclusive replacement after trusted index decoding:
calculate the live slot address, borrow and release its displaced owner, write
the consumed replacement, and return the original Array address. -/
def exclusiveReplacementProgram
    (arrayIndex indexIndex cursorIndex valueIndex elementIndex decrementIndex :
      Nat) : Wasm.Program :=
  elementAddressProgram arrayIndex indexIndex cursorIndex ++
    replaceElementOwnershipProgram cursorIndex valueIndex elementIndex
      decrementIndex ++
    [.localGet arrayIndex, .ret]

/-- The repaired symbolic exclusive arm adapts to exactly the Talos program
used by the semantic refinement below.  This bridge is independent of the
three production frame sizes and resolves their locals positionally. -/
theorem instructions_exclusiveReplacementSourceProgram
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {array index cursor value element : Lean.FVarId}
    {arrayIndex indexIndex cursorIndex valueIndex elementIndex decrementIndex :
      Nat}
    (arrayFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) array =
        some arrayIndex)
    (indexFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) index =
        some indexIndex)
    (cursorFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) cursor =
        some cursorIndex)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some valueIndex)
    (elementFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) element =
        some elementIndex)
    (decrementFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentRelease.decrementOnceName) =
        some decrementIndex) :
    FirTalos.instructions sourceModule sourceFunction labels
      (exclusiveReplacementSourceProgram array index cursor value element) =
        .ok (exclusiveReplacementProgram arrayIndex indexIndex cursorIndex
          valueIndex elementIndex decrementIndex) := by
  have addressAdapted :
      FirTalos.instructions sourceModule sourceFunction labels
        (elementAddressSourceProgram array index cursor) =
          .ok (elementAddressProgram arrayIndex indexIndex cursorIndex) := by
    simp [elementAddressSourceProgram, elementAddressProgram,
      ResidentPrimitives.scale8Source, ResidentPrimitives.scale8Program,
      FirTalos.instructions, FirTalos.instruction, arrayFound, indexFound,
      cursorFound, Bind.bind, Except.bind, pure, Except.pure]
  have borrowAdapted :
      FirTalos.instructions sourceModule sourceFunction labels [
        .localGet cursor, .i32Load .tobject 0, .localSet element] =
          .ok (borrowElementProgram cursorIndex elementIndex) := by
    simp [borrowElementProgram, FirTalos.instructions, FirTalos.instruction,
      cursorFound, elementFound, Bind.bind, Except.bind, pure, Except.pure]
  have decrementAdapted :=
    ResidentRelease.instructions_checkedDecrementLocal
      (labels := labels) elementFound decrementFound
  have tailAdapted :
      FirTalos.instructions sourceModule sourceFunction labels [
        .localGet cursor, .localGet value, .i32Store .tobject 0,
        .localGet array, .ret] =
          .ok (writeReplacementProgram cursorIndex valueIndex ++ [
            .localGet arrayIndex, .ret]) := by
    simp [writeReplacementProgram, FirTalos.instructions,
      FirTalos.instruction, cursorFound, valueFound, arrayFound, Bind.bind,
      Except.bind, pure, Except.pure]
  rw [exclusiveReplacementSourceProgram]
  simp only [List.append_assoc]
  rw [FirTalos.Correctness.instructions_append, addressAdapted,
    FirTalos.Correctness.instructions_append, borrowAdapted,
    FirTalos.Correctness.instructions_append, decrementAdapted, tailAdapted]
  rfl

/-- The complete exclusive arm refines one semantic Array replacement and
returns the same resident Array address.  The explicit local-update premises
are discharged once for each installed helper layout; the semantic ownership
argument and all post-state invariants are shared by every alias. -/
theorem wp_exclusiveReplacementProgram_heap_refines
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {state : MemoryState} {witness : RefinementWitness}
    {runtime releasedRuntime nextRuntime : RuntimeState}
    {location : Location} {address : Word32} {cell : HeapCell}
    {elements : Array Value} {capacity fuel index : Nat}
    {oldValue newValue : Value} {oldWord newWord : Word32}
    {initial afterIndex afterFirst afterSecond afterThird afterCursor afterOld :
      Wasm.Locals}
    {arrayIndex indexIndex cursorIndex valueIndex elementIndex decrementIndex :
      Nat}
    (admission : TrustedExclusiveAdmission state witness runtime location
      address cell elements capacity)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (oldAt : elements[index]? = some oldValue)
    (oldRead : state.memory.readWord32
      (address.value + headerBytes + target.semanticSlotBytes * index) =
        .ok oldWord)
    (oldRelated : ValueRel witness .tobject (.word32 oldWord) oldValue)
    (newRelated : ValueRel witness .tobject (.word32 newWord) newValue)
    (oldHeap : oldWord.classify = .heap)
    (semanticRelease :
      (match oldValue with
      | .object (.heap child) =>
          Fir.LeanIR.Impure.decLocationFuel fuel runtime child
      | _ => .ok runtime) = .ok releasedRuntime)
    (parentPreserved :
      findCell? releasedRuntime.heap location = some cell)
    (semanticSet :
      setCell releasedRuntime location
          { cell with
            object := .array (elements.set index newValue
              (Array.getElem?_eq_some_iff.mp oldAt).1) capacity } =
        .ok nextRuntime)
    (step : ResidentRelease.ResidentOwnershipStep env module decrementIndex
      fuel witness)
    (indexFound : initial.get indexIndex =
      some (.i32 (UInt32.ofNat index)))
    (indexSet :
      ({ initial with values := [.i32 (UInt32.ofNat index)] }).set?
          cursorIndex (.i32 (UInt32.ofNat index)) = some afterIndex)
    (firstSet :
      ({ afterIndex with values :=
          [.i32 (UInt32.ofNat index + UInt32.ofNat index)] }).set?
          cursorIndex (.i32 (UInt32.ofNat index + UInt32.ofNat index)) =
        some afterFirst)
    (secondSet :
      ({ afterFirst with values :=
          [.i32 (UInt32.ofNat index + UInt32.ofNat index +
            (UInt32.ofNat index + UInt32.ofNat index))] }).set?
          cursorIndex
            (.i32 (UInt32.ofNat index + UInt32.ofNat index +
              (UInt32.ofNat index + UInt32.ofNat index))) =
        some afterSecond)
    (thirdSet :
      ({ afterSecond with values :=
          [.i32 (ResidentPrimitives.scale8Word (UInt32.ofNat index))] }).set?
          cursorIndex
            (.i32 (ResidentPrimitives.scale8Word (UInt32.ofNat index))) =
        some afterThird)
    (arrayAfterThird : afterThird.get arrayIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (cursorSet :
      ({ afterThird with values :=
          [.i32 (elementAddressWord (UInt32.ofNat address.value)
            (UInt32.ofNat index))] }).set? cursorIndex
          (.i32 (elementAddressWord (UInt32.ofNat address.value)
            (UInt32.ofNat index))) = some afterCursor)
    (oldSet :
      ({ afterCursor with values :=
          [.i32 (UInt32.ofNat oldWord.value)] }).set? elementIndex
          (.i32 (UInt32.ofNat oldWord.value)) = some afterOld)
    (cursorAfter : afterOld.get cursorIndex =
      some (.i32 (UInt32.ofNat
        (address.value + headerBytes + target.semanticSlotBytes * index))))
    (valueAfter : afterOld.get valueIndex =
      some (.i32 (UInt32.ofNat newWord.value)))
    (arrayAfter : afterOld.get arrayIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (returned : ∀ result finalStore,
      ReplacementSuccess fuel state witness nextRuntime address index oldWord
          newWord result finalStore →
      Q (.Return finalStore [.i32 (UInt32.ofNat address.value)])) :
    Wasm.wp module
      (exclusiveReplacementProgram arrayIndex indexIndex cursorIndex valueIndex
        elementIndex decrementIndex)
      Q store { initial with values := [] } env := by
  have cursorUpdate := FirTalos.Correctness.localUpdate_of_set? cursorSet
  have cursorFound : afterCursor.get cursorIndex =
      some (.i32 (UInt32.ofNat
        (address.value + headerBytes + target.semanticSlotBytes * index))) := by
    rw [← elementAddressWord_ofNat]
    exact cursorUpdate.1
  have arrayFound (values : List Wasm.Value) :
      ({ afterOld with values } : Wasm.Locals).get arrayIndex =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa using arrayAfter
  have replacementWP :=
    wp_replaceElementOwnershipProgram_heap_refines
      (rest := [.localGet arrayIndex, .ret]) admission memoryRelated oldAt
      oldRead oldRelated newRelated oldHeap semanticRelease parentPreserved
      semanticSet step cursorFound oldSet cursorAfter valueAfter
      (fun result finalStore success => by
        simp only [Wasm.wp_localGet_cons, arrayFound, Wasm.wp_ret_cons]
        exact returned result finalStore success)
  have addressWP := wp_elementAddressProgram indexFound indexSet firstSet
    secondSet thirdSet arrayAfterThird cursorSet replacementWP
  simpa [exclusiveReplacementProgram, List.append_assoc] using addressWP

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

/-- Talos adaptation preserves the common trusted probe and embeds the exact
adapted exclusive branch beneath its anonymous `if`. -/
theorem instructions_trustedExclusivePrefixSourceProgram
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {array : Lean.FVarId} {arrayIndex : Nat}
    {exclusiveSource : List Fir.Wasm.Instruction}
    {exclusiveTarget : Wasm.Program}
    (arrayFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) array =
        some arrayIndex)
    (exclusiveAdapted : FirTalos.instructions sourceModule sourceFunction
      (none :: labels) exclusiveSource = .ok exclusiveTarget) :
    FirTalos.instructions sourceModule sourceFunction labels
      (trustedExclusivePrefixSourceProgram array exclusiveSource) =
        .ok (trustedExclusivePrefixProgram arrayIndex exclusiveTarget) := by
  simp [trustedExclusivePrefixSourceProgram, trustedExclusivePrefixProgram,
    FirTalos.instructions, FirTalos.instruction, arrayFound, exclusiveAdapted,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Successful adaptation of a production-shaped trusted helper preserves the
exact common probe and repaired exclusive arm inside the installed target
body.  The decoder prefix, shared-copy suffix, and physical terminal remain
opaque: only their successful compiler adaptation is used. -/
theorem adapted_body_contains_trustedExclusive
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetFunction : Wasm.Function}
    {sourcePrefix sourceSuffix : List Fir.Wasm.Instruction}
    {array index cursor value element : Lean.FVarId}
    {arrayIndex indexIndex cursorIndex valueIndex elementIndex decrementIndex :
      Nat}
    (adapted : FirTalos.function sourceModule sourceFunction =
      .ok targetFunction)
    (shape : sourceFunction.body = sourcePrefix ++
      trustedExclusivePrefixSourceProgram array
        (exclusiveReplacementSourceProgram array index cursor value element) ++
      sourceSuffix)
    (arrayFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) array =
        some arrayIndex)
    (indexFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) index =
        some indexIndex)
    (cursorFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) cursor =
        some cursorIndex)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some valueIndex)
    (elementFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) element =
        some elementIndex)
    (decrementFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentRelease.decrementOnceName) =
        some decrementIndex) :
    ∃ targetPrefix targetSuffix,
      targetFunction.body = targetPrefix ++
        trustedExclusivePrefixProgram arrayIndex
          (exclusiveReplacementProgram arrayIndex indexIndex cursorIndex
            valueIndex elementIndex decrementIndex) ++
        targetSuffix := by
  have exclusiveAdapted :=
    instructions_exclusiveReplacementSourceProgram
      (labels := [none]) arrayFound indexFound cursorFound valueFound
      elementFound decrementFound
  have commonAdapted := instructions_trustedExclusivePrefixSourceProgram
    (labels := []) arrayFound exclusiveAdapted
  obtain ⟨targetBody, bodyAdapted, installedBody⟩ :=
    FirTalos.Correctness.function_preserves_body adapted
  rw [shape] at bodyAdapted
  simp only [List.append_assoc] at bodyAdapted
  cases prefixAdapted :
      FirTalos.instructions sourceModule sourceFunction [] sourcePrefix with
  | error error =>
      rw [FirTalos.Correctness.instructions_append, prefixAdapted] at bodyAdapted
      contradiction
  | ok targetPrefix =>
      rw [FirTalos.Correctness.instructions_append, prefixAdapted,
        FirTalos.Correctness.instructions_append, commonAdapted] at bodyAdapted
      cases suffixAdapted :
          FirTalos.instructions sourceModule sourceFunction [] sourceSuffix with
      | error error =>
          rw [suffixAdapted] at bodyAdapted
          contradiction
      | ok targetSuffix =>
          rw [suffixAdapted] at bodyAdapted
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at bodyAdapted
          subst targetBody
          refine ⟨targetPrefix,
            targetSuffix ++ FirTalos.functionTerminal sourceModule sourceFunction,
            ?_⟩
          simpa [List.append_assoc] using installedBody

/-- The adapted production trusted `Array.uset` helper contains the one common
exclusive proof program at the exact numeric frame indices selected by Talos. -/
theorem adapted_trustedUset_body_containsExclusive
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {decrementIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentArray.trustedUsetFunction = .ok targetFunction)
    (decrementFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentRelease.decrementOnceName) =
        some decrementIndex) :
    ∃ targetPrefix targetSuffix,
      targetFunction.body = targetPrefix ++
        trustedExclusivePrefixProgram 1
          (exclusiveReplacementProgram 1 11 13 3 18 decrementIndex) ++
        targetSuffix := by
  apply adapted_body_contains_trustedExclusive adapted
    trustedUsetFunction_exclusiveSourceShape
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · exact decrementFound

/-- The adapted production trusted `Array.set` helper reuses exactly the same
installed exclusive proof program as `Array.uset`. -/
theorem adapted_trustedSet_body_containsExclusive
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {decrementIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentArray.trustedSetFunction = .ok targetFunction)
    (decrementFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentRelease.decrementOnceName) =
        some decrementIndex) :
    ∃ targetPrefix targetSuffix,
      targetFunction.body = targetPrefix ++
        trustedExclusivePrefixProgram 1
          (exclusiveReplacementProgram 1 11 13 3 18 decrementIndex) ++
        targetSuffix := by
  apply adapted_body_contains_trustedExclusive adapted
    trustedSetFunction_exclusiveSourceShape
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · exact decrementFound

/-- The adapted production trusted `Array.set!` helper has one fewer erased
parameter, so only its decoded-index, cursor, and old-element numeric slots
shift; the semantic exclusive theorem remains unchanged. -/
theorem adapted_trustedSetBang_body_containsExclusive
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {decrementIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentArray.trustedSetBangFunction = .ok targetFunction)
    (decrementFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentRelease.decrementOnceName) =
        some decrementIndex) :
    ∃ targetPrefix targetSuffix,
      targetFunction.body = targetPrefix ++
        trustedExclusivePrefixProgram 1
          (exclusiveReplacementProgram 1 10 12 3 17 decrementIndex) ++
        targetSuffix := by
  apply adapted_body_contains_trustedExclusive adapted
    trustedSetBangFunction_exclusiveSourceShape
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · exact decrementFound

/-- Function-local exclusive branches end by returning the Array address.
Keeping that fact in the postcondition rules out structured fallthrough and
branch completions before the deferred suffix is appended. -/
def ReturnOnly (Q : Wasm.Assertion host) : Wasm.Assertion host
  | continuation@(.Return _ _) => Q continuation
  | _ => False

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
