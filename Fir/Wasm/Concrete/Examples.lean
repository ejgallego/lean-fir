import Fir.Wasm.Concrete.HeapRefinement

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

#guard target.name == "wasm32-lean64"
#guard target.pointerLane == .i32
#guard target.usizeLane == .i64
#guard target.semanticSlotBytes == 8

#guard (Word32.encodeImmediate? 0).map (·.value) == some 1
#guard (Word32.encodeImmediate? maxImmediatePayload).map (·.value) ==
  some 4294967295
#guard (Word32.encodeImmediate? (maxImmediatePayload + 1)).isNone

def mixedConstructorInfo : LCNF.CtorInfo := {
  name := `Concrete.mixed
  cidx := 3
  size := 1
  usize := 1
  ssize := 8 }

def mixedConstructorLayout : ConstructorLayout :=
  ConstructorLayout.ofInfo mixedConstructorInfo

#guard mixedConstructorLayout.objectFieldsOffset == 32
#guard mixedConstructorLayout.usizeFieldsOffset == 40
#guard mixedConstructorLayout.scalarFieldsOffset == 48
#guard mixedConstructorLayout.allocationBytes == 56
#guard mixedConstructorLayout.objectFieldOffset? 0 == some 32
#guard mixedConstructorLayout.objectFieldOffset? 1 == none
#guard mixedConstructorLayout.usizeFieldOffset? 0 == some 40
#guard mixedConstructorLayout.scalarFieldOffset? 2 0 .uint64 == some 48
#guard mixedConstructorLayout.scalarFieldOffset? 2 1 .uint64 == none
#guard mixedConstructorLayout.scalarFieldOffset? 1 0 .uint64 == none

def mixedClosureLayout : ClosureLayout :=
  ClosureLayout.ofCaptures #[.object, .uint64, .uint8]

#guard mixedClosureLayout.captureOffset? 0 == some 32
#guard mixedClosureLayout.captureOffset? 1 == some 40
#guard mixedClosureLayout.captureOffset? 2 == some 48
#guard mixedClosureLayout.captureOffset? 3 == none
#guard mixedClosureLayout.allocationBytes == 56

example : ValueRel (witness := {}) .tobject
    (.word32 (Word32.encodeImmediate 42 (by decide)))
    (.object (.tagged 42)) :=
  .tobject (.tagged (.immediate 42 (by decide)))

example : ValueRel (witness := {}) .usize
    (.word64 (18446744073709551615 : UInt64))
    (.usize (18446744073709551615 : UInt64)) := .usize

def uint32RoundTrip : Except MemoryError UInt32 := do
  let memory ← (LinearMemory.withPages 1).writeUInt32 17 4294967295
  memory.readUInt32 17

#guard match uint32RoundTrip with
  | .ok value => value == 4294967295
  | .error _ => false

def uint64RoundTrip : Except MemoryError UInt64 := do
  let memory ← (LinearMemory.withPages 1).writeUInt64 23 18446744073709551615
  memory.readUInt64 23

#guard match uint64RoundTrip with
  | .ok value => value == 18446744073709551615
  | .error _ => false

#guard match (LinearMemory.withPages 1).readUInt32 wasmPageBytes with
  | .error (.outOfBounds address bytes memoryBytes) =>
      address == wasmPageBytes && bytes == 1 && memoryBytes == wasmPageBytes
  | _ => false

def allocatedConstructor : Except MemoryError (MemoryState × Word32) :=
  MemoryState.initial.allocateObject .constructor 24
    (aux0 := 3) (aux1 := 1) (aux2 := 1) (aux3 := 8)

#guard match allocatedConstructor with
  | .error _ => false
  | .ok (state, address) =>
      address.value == heapBase && state.heapCursor == heapBase + 56 &&
        match state.readLiveHeader address with
        | .error _ => false
        | .ok header =>
            header.kind == .constructor && header.live && !header.persistent &&
              header.refCount == 1 && header.allocationBytes == 56 &&
              header.aux0 == 3 && header.aux1 == 1 && header.aux2 == 1 &&
              header.aux3 == 8

#guard match MemoryState.initial.allocateObject .natural wasmPageBytes with
  | .error _ => false
  | .ok (state, _) => state.memory.size == 2 * wasmPageBytes

def smallTagged : Except ConcreteError (MemoryState × Word32) :=
  encodeTagged MemoryState.initial 42

#guard match smallTagged with
  | .error _ => false
  | .ok (state, word) =>
      state.heapCursor == heapBase && word.value == 85 &&
        match readTag state word with
        | .ok value => value == 42
        | .error _ => false

def promotedTagged : Except ConcreteError (MemoryState × Word32) :=
  encodeTagged MemoryState.initial (UInt64.ofNat (maxImmediatePayload + 1))

#guard match promotedTagged with
  | .error _ => false
  | .ok (state, word) =>
      word.value == heapBase && state.heapCursor == heapBase + 40 &&
        match state.readLiveHeader word, readTag state word with
        | .ok header, .ok value =>
            header.kind == .natural && header.persistent && header.live &&
              header.refCount == 0 && header.aux0 == promotedTagMarker &&
              value.toNat == maxImmediatePayload + 1
        | _, _ => false

def emptyConcreteInfo : LCNF.CtorInfo := {
  name := `Concrete.empty
  cidx := 3
  size := 0
  usize := 0
  ssize := 0 }

#guard match allocateConstructor MemoryState.initial emptyConcreteInfo #[] with
  | .ok (state, word) => state.heapCursor == heapBase && word.value == 7
  | .error _ => false

def concreteMixedConstructor : Except ConcreteError (MemoryState × Word32) :=
  allocateConstructor MemoryState.initial mixedConstructorInfo
    #[Word32.encodeImmediate 11 (by decide)]

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match readTag state object, readObjectField state object 0,
          readUSizeField state object 0 with
      | .ok tag, .ok field, .ok usize =>
          tag == 3 && field.value == 23 && usize == 0
      | _, _, _ => false

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match readObjectField state object 1 with
      | .error (.source (.objectFieldOutOfBounds 1 1)) => true
      | _ => false

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match writeTag state object 9 with
      | .error _ => false
      | .ok result =>
          match readTag result object, readObjectField result object 0,
              readUSizeField result object 0 with
          | .ok tag, .ok field, .ok usize =>
              tag == 9 && field.value == 23 && usize == 0
          | _, _, _ => false

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match writeUSizeField state object 0 77 with
      | .error _ => false
      | .ok result =>
          match readTag result object, readObjectField result object 0,
              readUSizeField result object 0 with
          | .ok tag, .ok field, .ok usize =>
              tag == 3 && field.value == 23 && usize == 77
          | _, _, _ => false

#guard match allocateNatural MemoryState.initial
    (Fir.LeanIR.Impure.maxTaggedPayload + 1) with
  | .error _ => false
  | .ok (state, object) =>
      match state.readLiveHeader object, readNatural state object with
      | .error _, _ | _, .error _ => false
      | .ok header, .ok value =>
          header.kind == .natural && !header.persistent &&
            header.refCount == 1 && header.aux0 == bigNaturalMarker &&
            header.aux1 == 1 &&
            value == Fir.LeanIR.Impure.maxTaggedPayload + 1

#guard naturalLimbs (UInt64.size + 5) == [5, 1]

def semanticMixedConstructor :=
  Fir.LeanIR.Impure.allocCtor (runtime := {}) mixedConstructorInfo
    #[.object (.tagged 11)]

#guard match semanticMixedConstructor, concreteMixedConstructor with
  | .ok (semanticState, semanticObject), .ok (concreteState, concreteObject) =>
      match Fir.LeanIR.Impure.getTag semanticState semanticObject,
          Fir.LeanIR.Impure.getObjectField semanticState semanticObject 0,
          readTag concreteState concreteObject,
          readObjectField concreteState concreteObject 0 with
      | .ok semanticTag, .ok (.object (.tagged semanticPayload)),
          .ok concreteTag, .ok concreteField =>
          semanticTag == concreteTag.toNat &&
            concreteField.decodeImmediate? == some semanticPayload.toNat &&
            semanticState.nextLocation == 1
      | _, _, _, _ => false
  | _, _ => false

def firstHeapAddress : Word32 := ⟨heapBase, by decide⟩

example : ValueRel (({} : RefinementWitness).bindLocation 0 firstHeapAddress)
    .object (.word32 firstHeapAddress) (.object (.heap 0)) :=
  ValueRel.new_heap_location {} 0 firstHeapAddress

example : ValueRel (({} : RefinementWitness).promoteTag
    (UInt64.ofNat (maxImmediatePayload + 1)) firstHeapAddress)
    .tagged (.word32 firstHeapAddress)
    (.object (.tagged (UInt64.ofNat (maxImmediatePayload + 1)))) :=
  ValueRel.new_promoted_tag {} _ firstHeapAddress

end Fir.Wasm.Concrete
