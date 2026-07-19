import Fir.Wasm.Concrete.ExternalCorrectness
import Fir.Wasm.Concrete.ClosureRuntime

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

#guard target.name == "wasm32-lean64"
#guard target.pointerLane == .i32
#guard target.usizeLane == .i64
#guard target.semanticSlotBytes == 8

def exampleGlobals : ConcreteGlobals :=
  ConcreteGlobals.declare [(`cachedValue, .uint32)]

example : ConcreteRuntimeRel {
    heap := MemoryState.initial
    globals := ConcreteGlobals.declare [(`cachedValue, .uint32)] }
    (initialWitness #[] #[]) ({} : RuntimeState) :=
  ConcreteRuntimeRel.moduleInitial #[] #[] [(`cachedValue, .uint32)]

#guard match exampleGlobals.read `cachedValue .uint32 with
  | .error (.targetGlobal (.uninitializedGlobal `cachedValue)) => true
  | _ => false

#guard match exampleGlobals.write `cachedValue .uint32
    (.word32 (Word32.ofUInt32 17)) with
  | .error _ => false
  | .ok globals =>
      match globals.read `cachedValue .uint32 with
      | .ok (.word32 value) => value.value == 17
      | _ => false

#guard match exampleGlobals.read `cachedValue .uint64 with
  | .error (.targetGlobal (.kindMismatch `cachedValue .uint32 .uint64)) => true
  | _ => false

def exampleExternalRequest : ConcreteExternalRequest := {
  name := `record
  paramTypes := #[Lean.mkConst ``UInt32]
  resultType := Lean.mkConst ``UInt32
  paramKinds := #[.uint32]
  resultKind := .uint32
  args := #[.word32 (Word32.ofUInt32 17)] }

def incrementWorldExternal : ConcreteExternalImpl where
  call request before :=
    match request.args[0]? with
    | some value => .ok { value, heap := before.heap, world := before.world + 1 }
    | none => .error (.source (.externalFailure request.name "missing argument"))

#guard match incrementWorldExternal.invoke exampleExternalRequest { world := 4 } with
  | .error _ => false
  | .ok (after, .word32 result) =>
      result.value == 17 && after.world == 5 && after.trace.size == 1 &&
        match after.trace[0]? with
        | some event => event.name == `record && event.args.size == 1
        | none => false
  | .ok _ => false

def rejectConcreteExternal : ConcreteExternalImpl where
  call request _ :=
    .error (.source (.externalFailure request.name "rejected"))

#guard match rejectConcreteExternal.invoke exampleExternalRequest { world := 4 } with
  | .error failure =>
      failure.toTrap ==
        .source (.runtime (.externalFailure `record "rejected"))
  | .ok _ => false

#guard (ConcreteError.targetGlobal (.unknownGlobal `missing)).toTrap ==
  .target (.global (.unknownGlobal `missing))

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

def concreteClosureDispatch : ClosureDispatchTable :=
  #[`Concrete.closureTarget, `Concrete.otherTarget]

def concreteClosureDescriptors : ClosureDescriptorTable :=
  #[#[.object, .uint64, .uint8], #[.object, .uint64]]

def concreteMixedClosure : Except ConcreteError (MemoryState × Word32) :=
  allocateClosure MemoryState.initial concreteClosureDispatch concreteClosureDescriptors
    `Concrete.closureTarget 4 #[.object, .uint64, .uint8]
      #[.word32 (Word32.encodeImmediate 5 (by decide)),
        .word64 42, .word32 (Word32.ofUInt8 7)]

#guard match concreteMixedClosure with
  | .error _ => false
  | .ok (state, closure) =>
      match readClosureMetadata state concreteClosureDispatch
          concreteClosureDescriptors closure with
      | .error _ => false
      | .ok metadata =>
          match (closureMatches state concreteClosureDispatch
              concreteClosureDescriptors closure
              `Concrete.closureTarget 4 3) with
          | .error _ => false
          | .ok matched =>
              match (projectClosureCapture state concreteClosureDispatch
                  concreteClosureDescriptors closure `Concrete.closureTarget 4 3 1
                    .uint64) with
              | .error _ => false
              | .ok (.word64 captured) =>
                  state.heapCursor == heapBase + 56 &&
                    metadata.targetId == 0 &&
                    metadata.descriptorId == 0 &&
                    metadata.function == `Concrete.closureTarget &&
                    metadata.arity == 4 && metadata.fixed == 3 &&
                    metadata.captureKinds == #[.object, .uint64, .uint8] &&
                    matched == 1 && captured == 42
              | .ok _ => false

#guard match concreteMixedClosure with
  | .error _ => false
  | .ok (state, closure) =>
      match (closureMatches state concreteClosureDispatch
          concreteClosureDescriptors closure
          `Concrete.otherTarget 4 3) with
      | .ok matched => matched == 0
      | .error _ => false

#guard match allocateClosure MemoryState.initial concreteClosureDispatch #[]
    `Concrete.closureTarget 4 #[.object] #[.word32
      (Word32.encodeImmediate 5 (by decide))] with
  | .error (.target (.unknownClosureDescriptor kinds)) => kinds == #[.object]
  | _ => false

#guard match concreteMixedClosure with
  | .error _ => false
  | .ok (state, closure) =>
      match projectClosureCapture state concreteClosureDispatch
          concreteClosureDescriptors closure `Concrete.closureTarget 4 3 1 .object with
      | .error (.target .closureMetadataMismatch) => true
      | _ => false

/-- Closure ownership consults `aux3`, skips scalar captures, and recursively
releases the object captures in source order. -/
def releasedOwnedClosure : Except ConcreteError (MemoryState × Word32 × Word32) := do
  let tagged := Word32.encodeImmediate 1 (by decide)
  let (state, child) ← allocateConstructor MemoryState.initial mixedConstructorInfo
    #[tagged]
  let (state, closure) ← allocateClosure state concreteClosureDispatch
    concreteClosureDescriptors `Concrete.closureTarget 3 #[.object, .uint64]
      #[.word32 child, .word64 42]
  let header ← liftMemory <| state.readLiveHeader closure
  let owned ← readOwnedReferences state closure header concreteClosureDescriptors
  unless owned == [child] do
    throw (.target .closureMetadataMismatch)
  let state ← decrementReferenceOnce state closure true concreteClosureDescriptors
  return (state, child, closure)

#guard match releasedOwnedClosure with
  | .error _ => false
  | .ok (state, child, closure) =>
      match state.readLiveHeader child, state.readLiveHeader closure with
      | .error (.deadObject childAddress), .error (.deadObject closureAddress) =>
          childAddress == child && closureAddress == closure
      | _, _ => false

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

def uint16RoundTrip : Except MemoryError UInt16 := do
  let memory ← (LinearMemory.withPages 1).writeUInt16 19 65535
  memory.readUInt16 19

#guard match uint16RoundTrip with
  | .ok value => value == 65535
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

/-- Equal tagged payloads are not interned: both immutable representations
remain valid concrete values at distinct fresh addresses. -/
def repeatedPromotedTagged :
    Except ConcreteError (MemoryState × Word32 × Word32) := do
  let payload := UInt64.ofNat (maxImmediatePayload + 1)
  let (state, first) ← encodeTagged MemoryState.initial payload
  let (state, second) ← encodeTagged state payload
  return (state, first, second)

#guard match repeatedPromotedTagged with
  | .error _ => false
  | .ok (state, first, second) =>
      first.value == heapBase && second.value == heapBase + 40 &&
        state.heapCursor == heapBase + 80 &&
        match readTag state first, readTag state second with
        | .ok firstPayload, .ok secondPayload =>
            firstPayload.toNat == maxImmediatePayload + 1 &&
              secondPayload.toNat == maxImmediatePayload + 1
        | _, _ => false

def boxedUInt8Max : Except ConcreteError (MemoryState × Word32) :=
  boxScalar MemoryState.initial (.uint8 255)

#guard match boxedUInt8Max with
  | .error _ => false
  | .ok (state, word) =>
      state.heapCursor == heapBase && word.value == 511 &&
        match readBoxedScalar state .uint8 word with
        | .ok scalar => scalar == .uint8 255
        | .error _ => false

/-- `UInt32.max` is semantically tagged but cannot fit in a wasm32 immediate,
so boxing reuses the persistent promoted-tag representation. -/
def boxedUInt32Max : Except ConcreteError (MemoryState × Word32) :=
  boxScalar MemoryState.initial (.uint32 4294967295)

#guard match boxedUInt32Max with
  | .error _ => false
  | .ok (state, word) =>
      state.heapCursor == heapBase + 40 &&
        match state.readLiveHeader word, readBoxedScalar state .uint32 word with
        | .ok header, .ok scalar =>
            header.kind == .natural && header.persistent &&
              scalar == .uint32 4294967295
        | _, _ => false

/-- Only payloads above FIR's 63-bit semantic tagged range allocate a real
`boxed` object. -/
def boxedUInt64Max : Except ConcreteError (MemoryState × Word32) :=
  boxScalar MemoryState.initial (.uint64 18446744073709551615)

#guard match boxedUInt64Max with
  | .error _ => false
  | .ok (state, word) =>
      state.heapCursor == heapBase + 40 &&
        match state.readLiveHeader word, readBoxedScalar state .uint64 word with
        | .ok header, .ok scalar =>
            header.kind == .boxed && !header.persistent && header.refCount == 1 &&
              header.allocationBytes == 40 &&
              header.aux0 == BoxedScalarKind.uint64.code && header.aux1 == 8 &&
              header.aux2 == 0 && header.aux3 == 0 &&
              scalar == .uint64 18446744073709551615
        | _, _ => false

def semanticBoxedUInt64Max :=
  Fir.LeanIR.Impure.box (runtime := {}) LCNF.ImpureType.uint64
    (.scalar (.uint64 18446744073709551615))

#guard match semanticBoxedUInt64Max, boxedUInt64Max with
  | .ok (semanticState, .object (.heap semanticLocation)),
      .ok (concreteState, concreteObject) =>
      semanticLocation == 0 && semanticState.nextLocation == 1 &&
        match Fir.LeanIR.Impure.unbox semanticState LCNF.ImpureType.uint64
            (.object (.heap semanticLocation)),
          readBoxedScalar concreteState .uint64 concreteObject with
        | .ok (.scalar (.uint64 semantic)), .ok (.uint64 concrete) =>
            semantic == concrete && concrete == 18446744073709551615
        | _, _ => false
  | _, _ => false

/- Sharing follows the semantic representation split: direct and promoted
tags are shared, while a fresh ordinary heap box is unique. -/
#guard match smallTagged, promotedTagged, boxedUInt64Max with
  | .ok (immediateState, immediate), .ok (promotedState, promoted),
      .ok (boxedState, boxed) =>
      match readIsShared immediateState immediate,
          readIsShared promotedState promoted, readIsShared boxedState boxed with
      | .ok immediateShared, .ok promotedShared, .ok boxedShared =>
          immediateShared == 1 && promotedShared == 1 && boxedShared == 0
      | _, _, _ => false
  | _, _, _ => false

/-- The first concrete ownership transition changes only the common header:
the boxed payload remains decodable and becomes observably shared. -/
def incrementedBoxedUInt64Max : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← boxedUInt64Max
  let state ← incrementReference state object 2 true
  return (state, object)

#guard match incrementedBoxedUInt64Max with
  | .error _ => false
  | .ok (state, object) =>
      match state.readLiveHeader object, readBoxedScalar state .uint64 object,
          readIsShared state object with
      | .ok header, .ok scalar, .ok shared =>
          header.refCount == 3 && scalar == .uint64 18446744073709551615 &&
            shared == 1
      | _, _, _ => false

def decrementedSharedBoxedUInt64Max :
    Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← incrementedBoxedUInt64Max
  let state ← decrementReferenceOnce state object true
  return (state, object)

#guard match decrementedSharedBoxedUInt64Max with
  | .error _ => false
  | .ok (state, object) =>
      match state.readLiveHeader object, readBoxedScalar state .uint64 object,
          readIsShared state object with
      | .ok header, .ok scalar, .ok shared =>
          header.refCount == 2 && scalar == .uint64 18446744073709551615 &&
            shared == 1
      | _, _, _ => false

/-- Count one transitions to the canonical freed header rather than retaining
stale boxed payload metadata. -/
def releasedBoxedUInt64Max : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← boxedUInt64Max
  let state ← decrementReferenceOnce state object true
  return (state, object)

#guard match releasedBoxedUInt64Max with
  | .error _ => false
  | .ok (state, object) =>
      match Header.read state.memory object, state.readLiveHeader object with
      | .ok header, .error (.deadObject deadAddress) =>
          deadAddress == object && header.kind == .freed && !header.persistent &&
            !header.live && header.refCount == 0 &&
            header.aux0 == 0 && header.aux1 == 0 &&
            header.aux2 == 0 && header.aux3 == 0
      | _, _ => false

/-- Explicit deletion uses the same canonical freed header but does not run
the recursive ownership fold. -/
def deletedBoxedUInt64Max : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← boxedUInt64Max
  let state ← deleteObject state object
  return (state, object)

#guard match deletedBoxedUInt64Max with
  | .error _ => false
  | .ok (state, object) =>
      match Header.read state.memory object, state.readLiveHeader object with
      | .ok header, .error (.deadObject deadAddress) =>
          deadAddress == object && header.kind == .freed && !header.live &&
            header.refCount == 0
      | _, _ => false

/- The erased failed-reset sentinel is the sole non-heap delete no-op and
preserves the complete concrete state. -/
#guard match deleteObject MemoryState.initial Word32.zero with
  | .error _ => false
  | .ok result =>
      result.heapCursor == MemoryState.initial.heapCursor &&
        result.memory == MemoryState.initial.memory

#guard match smallTagged, promotedTagged with
  | .ok (immediateState, immediate), .ok (promotedState, promoted) =>
      match deleteObject immediateState immediate,
          deleteObject promotedState promoted with
      | .error (.source .expectedHeapReference),
          .error (.source .expectedHeapReference) => true
      | _, _ => false
  | _, _ => false

/- Tagged references retain their no-ownership representation contract:
checked increments are no-ops and unchecked increments reject them. -/
#guard match smallTagged, promotedTagged with
  | .ok (immediateState, immediate), .ok (promotedState, promoted) =>
      match incrementReference immediateState immediate 1 true,
          incrementReference promotedState promoted 1 true,
          incrementReference immediateState immediate 1 false,
          incrementReference promotedState promoted 1 false with
      | .ok immediateResult, .ok promotedResult,
          .error (.source .expectedHeapReference),
          .error (.source .expectedHeapReference) =>
          match readTag immediateResult immediate, readTag promotedResult promoted with
          | .ok immediatePayload, .ok promotedPayload =>
              immediatePayload == 42 &&
                promotedPayload.toNat == maxImmediatePayload + 1
          | _, _ => false
      | _, _, _, _ => false
  | _, _ => false

/- Reset distinguishes its empty token from semantic tagged zero: immediate,
promoted, and shared objects return word zero, while cleared constructor slots
contain the encoded tagged-zero word one. -/
#guard match smallTagged, promotedTagged, incrementedBoxedUInt64Max with
  | .ok (immediateState, immediate), .ok (promotedState, promoted),
      .ok (sharedState, shared) =>
      match resetObject immediateState 0 immediate,
          resetObject promotedState 0 promoted,
          resetObject sharedState 0 shared with
      | .ok (immediateResult, immediateToken),
          .ok (promotedResult, promotedToken),
          .ok (sharedResult, sharedToken) =>
          immediateToken == Word32.zero && promotedToken == Word32.zero &&
            sharedToken == Word32.zero &&
            immediateResult.heapCursor == immediateState.heapCursor &&
            promotedResult.heapCursor == promotedState.heapCursor &&
            match sharedResult.readLiveHeader shared with
            | .ok header => header.refCount == 2
            | .error _ => false
      | _, _, _ => false
  | _, _, _ => false

#guard match smallTagged, promotedTagged with
  | .ok (immediateState, immediate), .ok (promotedState, promoted) =>
      match decrementReferenceOnce immediateState immediate true,
          decrementReferenceOnce promotedState promoted true,
          decrementReferenceOnce immediateState immediate false,
          decrementReferenceOnce promotedState promoted false with
      | .ok immediateResult, .ok promotedResult,
          .error (.source .expectedHeapReference),
          .error (.source .expectedHeapReference) =>
          match readTag immediateResult immediate, readTag promotedResult promoted with
          | .ok immediatePayload, .ok promotedPayload =>
              immediatePayload == 42 &&
                promotedPayload.toNat == maxImmediatePayload + 1
          | _, _ => false
      | _, _, _, _ => false
  | _, _ => false

/- Regression for
`FIR-BUG-wasm-none-release-fuel-preempts-nonheap-noop`: checked non-owning
words do not consult heap-recursion fuel. -/
#guard match decrementReferenceOnceFuel 0 MemoryState.initial Word32.zero true with
  | .ok state =>
      state.heapCursor == heapBase && state.memory.size == wasmPageBytes
  | .error _ => false

#guard match decrementReferenceOnceFuel 0 MemoryState.initial
    (Word32.encodeImmediate 7 (by decide)) true with
  | .ok state =>
      state.heapCursor == heapBase && state.memory.size == wasmPageBytes
  | .error _ => false

#guard match promotedTagged with
  | .ok (state, object) =>
      match decrementReferenceOnceFuel 0 state object true with
      | .ok result =>
          match readTag result object with
          | .ok payload => payload.toNat == maxImmediatePayload + 1
          | .error _ => false
      | .error _ => false
  | .error _ => false

/-- Install the largest representable common-header count so the next
increment exercises the checked target-overflow boundary. -/
def boxedUInt64MaxAtRefCountMax : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← boxedUInt64Max
  let header ← liftMemory <| state.readLiveHeader object
  let memory ← liftMemory <| { header with refCount := (4294967295 : UInt32) }.write
    state.memory object
  return ({ state with memory }, object)

#guard match boxedUInt64MaxAtRefCountMax with
  | .error _ => false
  | .ok (state, object) =>
      match incrementReference state object 1 true with
      | .error (.target (.headerValueOverflow field value)) =>
          field == "reference count" && value == UInt32.size
      | _ => false

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

def resetMixedConstructor : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← concreteMixedConstructor
  let (state, token) ← resetObject state 1 object
  return (state, token)

#guard match resetMixedConstructor with
  | .error _ => false
  | .ok (state, token) =>
      token.value == heapBase &&
        match state.readLiveHeader token, readObjectField state token 0 with
        | .ok header, .ok field =>
            header.kind == .constructor && header.refCount == 1 &&
              field == taggedZero && taggedZero.value == 1
        | _, _ => false

def reusedMixedConstructor : Except ConcreteError (MemoryState × Word32) := do
  let (state, token) ← resetMixedConstructor
  reuseObject state token { mixedConstructorInfo with cidx := 9 } true
    #[Word32.encodeImmediate 13 (by decide)]

#guard match reusedMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match state.readLiveHeader object, readTag state object,
          readObjectField state object 0, readUSizeField state object 0,
          readScalarUInt64Field state object 2 0 with
      | .ok header, .ok tag, .ok field, .ok usize, .ok scalar =>
          header.allocationBytes == 56 && header.refCount == 1 && tag == 9 &&
            field.value == 27 && usize == 0 && scalar == 0
      | _, _, _, _, _ => false

def smallerReuseInfo : LCNF.CtorInfo := {
  name := `Concrete.smallerReuse
  cidx := 12
  size := 1
  usize := 0
  ssize := 0 }

/- Shrinking reuse changes the active constructor layout while retaining the
complete old physical allocation capacity for spatial decoding. -/
#guard match resetMixedConstructor with
  | .error _ => false
  | .ok (state, token) =>
      match reuseObject state token smallerReuseInfo true
          #[Word32.encodeImmediate 15 (by decide)] with
      | .error _ => false
      | .ok (result, object) =>
          object == token &&
            match result.readLiveHeader object,
                readObjectField result object 0 with
            | .ok header, .ok field =>
                header.allocationBytes == 56 && header.aux0 == 12 &&
                  header.aux1 == 1 && header.aux2 == 0 && header.aux3 == 0 &&
                  field.value == 31
            | _, _ => false

#guard match reuseObject MemoryState.initial Word32.zero mixedConstructorInfo false
    #[Word32.encodeImmediate 17 (by decide)] with
  | .ok (state, object) =>
      object.value == heapBase &&
        match readObjectField state object 0 with
        | .ok field => field.value == 35
        | .error _ => false
  | .error _ => false

#guard match reuseObject MemoryState.initial Word32.zero emptyConcreteInfo false #[] with
  | .ok (state, word) => state.heapCursor == heapBase && word.value == 7
  | .error _ => false

def oversizedReuseInfo : LCNF.CtorInfo := {
  name := `Concrete.oversizedReuse
  cidx := 10
  size := 4
  usize := 0
  ssize := 0 }

#guard match resetMixedConstructor with
  | .error _ => false
  | .ok (state, token) =>
      match reuseObject state token oversizedReuseInfo true
          (Array.replicate 4 taggedZero) with
      | .error (.target (.reuseAllocationTooSmall available required)) =>
          available == 56 && required == 64
      | _ => false

/- Actual heap recursion still consumes fuel and faults at depth zero. -/
#guard match concreteMixedConstructor with
  | .ok (state, object) =>
      match decrementReferenceOnceFuel 0 state object true with
      | .error (.target .releaseFuelExhausted) => true
      | _ => false
  | .error _ => false

def incrementedMixedConstructor : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← concreteMixedConstructor
  let state ← incrementReference state object 2 true
  return (state, object)

#guard match incrementedMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match state.readLiveHeader object, readTag state object,
          readObjectField state object 0, readUSizeField state object 0,
          readScalarUInt64Field state object 2 0 with
      | .ok header, .ok tag, .ok field, .ok usize, .ok scalar =>
          header.refCount == 3 && tag == 3 && field.value == 23 &&
            usize == 0 && scalar == 0
      | _, _, _, _, _ => false

/-- Constructor decrement above one retains every mixed payload region. -/
def decrementedMixedConstructor : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← incrementedMixedConstructor
  let state ← decrementReferenceOnce state object true
  return (state, object)

#guard match decrementedMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match state.readLiveHeader object, readTag state object,
          readObjectField state object 0, readUSizeField state object 0,
          readScalarUInt64Field state object 2 0 with
      | .ok header, .ok tag, .ok field, .ok usize, .ok scalar =>
          header.refCount == 2 && tag == 3 && field.value == 23 &&
            usize == 0 && scalar == 0
      | _, _, _, _, _ => false

/-- Regression for
`FIR-BUG-wasm-none-recursive-release-erased-sentinel`: the zero word is the
canonical representation of an erased object field and is skipped by checked
recursive release. -/
def releasedErasedFieldConstructor : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← allocateConstructor MemoryState.initial mixedConstructorInfo
    #[Word32.zero]
  let state ← decrementReferenceOnce state object true
  return (state, object)

#guard match releasedErasedFieldConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match Header.read state.memory object with
      | .ok header => header.kind == .freed && !header.live && header.refCount == 0
      | .error _ => false

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

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      -- Lean 4.32 emits the total fixed-slot count as the scalar operand.
      match writeScalarUInt64Field state object 2 0 66 with
      | .error _ => false
      | .ok result =>
          match readScalarUInt64Field result object 2 0,
              readTag result object, readObjectField result object 0,
              readUSizeField result object 0 with
          | .ok scalar, .ok tag, .ok field, .ok usize =>
              scalar == 66 && tag == 3 && field.value == 23 && usize == 0
          | _, _, _, _ => false

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match writeScalarUInt32Field state object 2 4 4294967295 with
      | .error _ => false
      | .ok result =>
          match readScalarUInt32Field result object 2 4,
              readTag result object, readObjectField result object 0,
              readUSizeField result object 0 with
          | .ok scalar, .ok tag, .ok field, .ok usize =>
              scalar == 4294967295 && tag == 3 && field.value == 23 && usize == 0
          | _, _, _, _ => false

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match readScalarUInt8Field state object 2 0 with
      | .ok scalar => scalar == 0
      | .error _ => false

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match writeScalarUInt8Field state object 2 3 255 with
      | .error _ => false
      | .ok result =>
          match readScalarUInt8Field result object 2 3,
              readTag result object, readObjectField result object 0,
              readUSizeField result object 0 with
          | .ok scalar, .ok tag, .ok field, .ok usize =>
              scalar == 255 && tag == 3 && field.value == 23 && usize == 0
          | _, _, _, _ => false

#guard match concreteMixedConstructor with
  | .error _ => false
  | .ok (state, object) =>
      match writeScalarUInt16Field state object 2 1 65535 with
      | .error _ => false
      | .ok result =>
          match readScalarUInt16Field result object 2 1,
              readTag result object, readObjectField result object 0,
              readUSizeField result object 0 with
          | .ok scalar, .ok tag, .ok field, .ok usize =>
              scalar == 65535 && tag == 3 && field.value == 23 && usize == 0
          | _, _, _, _ => false

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

def incrementedLargeNatural : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← allocateNatural MemoryState.initial
    (Fir.LeanIR.Impure.maxTaggedPayload + 1)
  let state ← incrementReference state object 4 true
  return (state, object)

#guard match incrementedLargeNatural with
  | .error _ => false
  | .ok (state, object) =>
      match state.readLiveHeader object, readNatural state object,
          readIsShared state object with
      | .ok header, .ok value, .ok shared =>
          header.kind == .natural && header.refCount == 5 &&
            value == Fir.LeanIR.Impure.maxTaggedPayload + 1 && shared == 1
      | _, _, _ => false

/-- Natural decrement above one frames every stored limb. -/
def decrementedLargeNatural : Except ConcreteError (MemoryState × Word32) := do
  let (state, object) ← incrementedLargeNatural
  let state ← decrementReferenceOnce state object true
  return (state, object)

#guard match decrementedLargeNatural with
  | .error _ => false
  | .ok (state, object) =>
      match state.readLiveHeader object, readNatural state object,
          readIsShared state object with
      | .ok header, .ok value, .ok shared =>
          header.kind == .natural && header.refCount == 4 &&
            value == Fir.LeanIR.Impure.maxTaggedPayload + 1 && shared == 1
      | _, _, _ => false

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

def secondHeapAddress : Word32 := ⟨heapBase + 40, by decide⟩

/-- Regression for `FIR-BUG-wasm-none-promoted-tag-aliasing`: recording a
second representation of an equal payload retains membership of the first. -/
example :
    let payload := UInt64.ofNat (maxImmediatePayload + 1)
    let first := ({} : RefinementWitness).promoteTag payload firstHeapAddress
    let second := first.promoteTag payload secondHeapAddress
    second.promotedTags.Contains payload firstHeapAddress ∧
      second.promotedTags.Contains payload secondHeapAddress := by
  simp [RefinementWitness.promoteTag, PromotedTags.Contains]

end Fir.Wasm.Concrete
