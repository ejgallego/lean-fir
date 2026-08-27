import Fir.Wasm.Emit.ResidentScalarBox
import Fir.Wasm.Concrete.BoxingCorrectness
import FirTalos.ConcreteResidentAllocator
import FirTalos.ConcreteResidentNat

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident `UInt64` scalar-box refinement

This module connects W7's production `fir_box_uint64` and
`fir_unbox_uint64` bodies to W6's heap-only `UInt64` contract.  The proof is
deliberately factored through the common resident allocator and the generic
32/64-bit memory bridges: it does not duplicate either the allocator proof or
the concrete boxed-scalar refinement.
-/

namespace ResidentScalarBox

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

/-- W6 spelling of W7's checked equality guard. -/
def equalsConstSource (kind : Fir.Wasm.AbiKind) (value : UInt32) :
    List Fir.Wasm.Instruction :=
  [.i32Const kind value, .i32Eq]

/-- W6 spelling of W7's checked `trap unless` combinator. -/
def trapUnlessSource (condition : List Fir.Wasm.Instruction) :
    List Fir.Wasm.Instruction :=
  condition ++ [.ifElse [] [.unreachable]]

/-- Public proof-side spelling of the heap-address admission checks. -/
def requireHeapAddressSource (object : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  trapUnlessSource ([.localGet object,
    .i32Const .uint32 (u32 heapBase), .i32LtU] ++
    equalsConstSource .uint32 0) ++
  trapUnlessSource ([.localGet object,
    .i32Const .uint32 (u32 (target.heapAlignment - 1)), .i32And] ++
    equalsConstSource .uint32 0)

/-- Public proof-side spelling of one exact header-word guard. -/
def requireHeaderWordSource (object : Lean.FVarId) (offset : Nat)
    (value : UInt32) : List Fir.Wasm.Instruction :=
  trapUnlessSource ([.localGet object, .i32Load .uint32 (u32 offset)] ++
    equalsConstSource .uint32 value)

def storeAddress32Source (address : Lean.FVarId)
    (value : List Fir.Wasm.Instruction) (offset : Nat) :
    List Fir.Wasm.Instruction :=
  [.localGet address] ++ value ++ [.i32Store .uint32 (u32 offset)]

def storeAddress64Source (address : Lean.FVarId)
    (value : List Fir.Wasm.Instruction) (offset : Nat) :
    List Fir.Wasm.Instruction :=
  [.localGet address] ++ value ++ [.i64Store .uint64 (u32 offset)]

/-- Proof-side spelling of W7's raw-i32 retyping sequence.  The result kind is
symbolic metadata: every admitted object-family kind has the same physical i32
load, local, and result representation after adaptation. -/
def retypeRawResultSource (resultKind : Fir.Wasm.AbiKind)
    (raw saved result : Lean.FVarId) : List Fir.Wasm.Instruction := [
  .localSet raw,
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet saved,
  .i32Const .uint32 0,
  .localGet raw,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load resultKind 0,
  .localSet result,
  .i32Const .uint32 0,
  .localGet saved,
  .i32Store .uint32 0,
  .localGet result,
  .ret]

/-- Common source shape of the generic and exact-result `UInt16` aliases. -/
def boxUInt16SourceProgram (resultKind : Fir.Wasm.AbiKind)
    (value raw saved result : Lean.FVarId) : List Fir.Wasm.Instruction :=
  [.localGet value,
    .localGet value,
    .i32Add,
    .i32Const .uint32 1,
    .i32Add] ++
  retypeRawResultSource resultKind raw saved result

/-- Every `UInt16` payload fits the concrete wasm32 immediate-object range. -/
def uint16FitsImmediate (value : UInt16) :
    value.toNat ≤ maxImmediatePayload := by
  have bound := value.toNat_lt
  simp [maxImmediatePayload] at bound ⊢
  omega

/-- Canonical concrete object word returned by `fir_box_uint16`. -/
def uint16ImmediateWord (value : UInt16) : Word32 :=
  Word32.encodeImmediate value.toNat (uint16FitsImmediate value)

/-- The production arithmetic prefix computes the canonical tagged-object
bits exactly: two copies of the physical payload plus the low tag bit. -/
theorem uint16ImmediateWord_physical (value : UInt16) :
    UInt32.ofNat (uint16ImmediateWord value).value =
      UInt32.ofNat value.toNat + UInt32.ofNat value.toNat + 1 := by
  simp [uint16ImmediateWord, Word32.encodeImmediate]
  exact UInt32.mul_two

/-- W7's generic `UInt16` helper has the common proof-side source shape. -/
theorem boxUInt16Function_shape :
    Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.body =
      boxUInt16SourceProgram .tobject
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.params[0]!.1
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.locals[0]!.1
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.locals[1]!.1
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.locals[2]!.1 := by
  rfl

/-- Re-annotating the production `UInt16` alias as `.tagged` preserves its
complete physical signature: payload, scratch locals, result local, and result
all remain wasm i32 values. -/
theorem boxUInt16Tagged_physicalSignature :
    (Fir.Wasm.Emit.ResidentScalarBox.boxUInt16TaggedFunction.params.toList.map
        (FirTalos.abiKind ∘ Prod.snd) =
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.params.toList.map
        (FirTalos.abiKind ∘ Prod.snd)) ∧
    (Fir.Wasm.Emit.ResidentScalarBox.boxUInt16TaggedFunction.locals.toList.map
        (FirTalos.abiKind ∘ Prod.snd) =
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.locals.toList.map
        (FirTalos.abiKind ∘ Prod.snd)) ∧
    (Fir.Wasm.Emit.ResidentScalarBox.boxUInt16TaggedFunction.results.toList.map
        FirTalos.abiKind =
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.results.toList.map
        FirTalos.abiKind) := by
  native_decide

/-- Exact source body of production `fir_box_uint64`, with private emitter
locals supplied positionally by the public function. -/
def boxUInt64SourceProgram (value raw address saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  [.i32Const .uint32 40,
    .call (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName),
    .localSet address] ++
  storeAddress32Source address
    [.i32Const .uint32 ObjectKind.boxed.code] headerKindOffset ++
  storeAddress32Source address [.i32Const .uint32 liveFlag]
    headerFlagsOffset ++
  storeAddress32Source address [.i32Const .uint32 1]
    headerRefCountOffset ++
  storeAddress32Source address [.i32Const .uint32 40]
    headerAllocationBytesOffset ++
  storeAddress32Source address
    [.i32Const .uint32 BoxedScalarKind.uint64.code] headerAux0Offset ++
  storeAddress32Source address [.i32Const .uint32 8] headerAux1Offset ++
  storeAddress32Source address [.i32Const .uint32 0] headerAux2Offset ++
  storeAddress32Source address [.i32Const .uint32 0] headerAux3Offset ++
  storeAddress64Source address [.localGet value] headerBytes ++
  [.localGet address] ++
    ResidentNat.retypeRawObjectResultSource raw saved result

/-- Exact-result source shape of production `fir_box_uint64_object`.  It is
the generic heap-allocation body with only the final object-family result load
re-annotated as `.object`. -/
def boxUInt64ObjectSourceProgram
    (value raw address saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  [.i32Const .uint32 40,
    .call (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName),
    .localSet address] ++
  storeAddress32Source address
    [.i32Const .uint32 ObjectKind.boxed.code] headerKindOffset ++
  storeAddress32Source address [.i32Const .uint32 liveFlag]
    headerFlagsOffset ++
  storeAddress32Source address [.i32Const .uint32 1]
    headerRefCountOffset ++
  storeAddress32Source address [.i32Const .uint32 40]
    headerAllocationBytesOffset ++
  storeAddress32Source address
    [.i32Const .uint32 BoxedScalarKind.uint64.code] headerAux0Offset ++
  storeAddress32Source address [.i32Const .uint32 8] headerAux1Offset ++
  storeAddress32Source address [.i32Const .uint32 0] headerAux2Offset ++
  storeAddress32Source address [.i32Const .uint32 0] headerAux3Offset ++
  storeAddress64Source address [.localGet value] headerBytes ++
  [.localGet address] ++
    retypeRawResultSource .object raw saved result

/-- Re-annotating the production heap-only `UInt64` alias as `.object`
preserves its complete physical signature; in particular the returned
concrete heap address is the same wasm i32 value as the generic `.tobject`
result. -/
theorem boxUInt64Object_physicalSignature :
    (Fir.Wasm.Emit.ResidentScalarBox.boxUInt64ObjectFunction.params.toList.map
        (FirTalos.abiKind ∘ Prod.snd) =
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.params.toList.map
        (FirTalos.abiKind ∘ Prod.snd)) ∧
    (Fir.Wasm.Emit.ResidentScalarBox.boxUInt64ObjectFunction.locals.toList.map
        (FirTalos.abiKind ∘ Prod.snd) =
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals.toList.map
        (FirTalos.abiKind ∘ Prod.snd)) ∧
    (Fir.Wasm.Emit.ResidentScalarBox.boxUInt64ObjectFunction.results.toList.map
        FirTalos.abiKind =
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.results.toList.map
        FirTalos.abiKind) := by
  native_decide

/-- Exact source body of production `fir_unbox_uint64`. -/
def unboxUInt64SourceProgram (object : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  requireHeapAddressSource object ++
  requireHeaderWordSource object headerKindOffset ObjectKind.boxed.code ++
  trapUnlessSource ([.localGet object,
    .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 liveFlag, .i32And] ++
    equalsConstSource .uint32 liveFlag) ++
  requireHeaderWordSource object headerAllocationBytesOffset 40 ++
  requireHeaderWordSource object headerAux0Offset
    BoxedScalarKind.uint64.code ++
  requireHeaderWordSource object headerAux1Offset 8 ++
  requireHeaderWordSource object headerAux2Offset 0 ++
  requireHeaderWordSource object headerAux3Offset 0 ++
  [.localGet object, .i64Load .uint64 (u32 headerBytes), .ret]

/-- W7's public box helper has exactly the proof-side source shape. -/
theorem boxUInt64Function_shape :
    Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.body =
      boxUInt64SourceProgram
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.params[0]!.1
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals[0]!.1
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals[1]!.1
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals[2]!.1
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals[3]!.1 := by
  rfl

/-- W7's public unbox helper has exactly the proof-side source shape. -/
theorem unboxUInt64Function_shape :
    Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function.body =
      unboxUInt64SourceProgram
        Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function.params[0]!.1 := by
  rfl

/-- Talos spelling of `trapUnlessSource`. -/
def trapUnlessProgram (condition : Wasm.Program) : Wasm.Program :=
  condition ++ [.iff 0 0 [] [.unreachable]]

def requireHeapAddressProgram (object : Nat) : Wasm.Program :=
  trapUnlessProgram [.localGet object, .const (u32 heapBase), .ltU,
    .const 0, .eq] ++
  trapUnlessProgram [.localGet object,
    .const (u32 (target.heapAlignment - 1)), .and, .const 0, .eq]

def requireHeaderWordProgram (object : Nat) (offset : Nat)
    (value : UInt32) : Wasm.Program :=
  trapUnlessProgram [.localGet object, .load32 (u32 offset), .const value, .eq]

/-- Physical common-header words installed by `fir_box_uint64`. -/
def uint64HeaderWords : List UInt32 := [
  ObjectKind.boxed.code, liveFlag, 1, 40,
  BoxedScalarKind.uint64.code, 8, 0, 0]

def writeHeaderStore (store : Wasm.Store host) (address : UInt32) :
    Wasm.Store host :=
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerKindOffset) ObjectKind.boxed.code
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerFlagsOffset) liveFlag
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerRefCountOffset) 1
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerAllocationBytesOffset) 40
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerAux0Offset) BoxedScalarKind.uint64.code
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerAux1Offset) 8
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerAux2Offset) 0
  ResidentMemoryRel.write32Store store
    (address + u32 headerAux3Offset) 0

def writePayloadStore (store : Wasm.Store host) (address : UInt32)
    (payload : UInt64) : Wasm.Store host :=
  let headerStore := writeHeaderStore store address
  { headerStore with mem :=
      headerStore.mem.write64 (address + u32 headerBytes) payload }

/-- The canonical W6 header for an ordinary heap-only `UInt64` box. -/
def uint64Header : Header :=
  Header.forAllocation .boxed 40 false BoxedScalarKind.uint64.code 8

/-- The eight explicit production stores are one adjacent common-header
write.  This lets scalar boxing reuse the generic allocator refinement. -/
theorem writeHeaderStore_eq_words (store : Wasm.Store host) (address : UInt32) :
    writeHeaderStore store address =
      ResidentMemoryRel.writeUInt32sStore store address uint64HeaderWords := by
  simp [writeHeaderStore, ResidentMemoryRel.writeUInt32sStore,
    uint64HeaderWords, headerKindOffset, headerFlagsOffset,
    headerRefCountOffset, headerAllocationBytesOffset, headerAux0Offset,
    headerAux1Offset, headerAux2Offset, headerAux3Offset]
  ac_rfl

/-- The proof-side canonical header has exactly the raw words written by the
production helper. -/
theorem uint64Header_words : uint64Header.words = uint64HeaderWords := by
  simp [uint64Header, uint64HeaderWords, Header.words, Header.forAllocation,
    Header.flags, liveFlag]

/-- One canonical W6 header write is represented by the production helper's
eight physical stores. -/
theorem writeHeaderStore_refines
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    {address : Word32} {result : LinearMemory}
    (inBounds : address.value + headerBytes ≤ heap.memory.size)
    (written : uint64Header.write heap.memory address = .ok result) :
    ResidentAllocatorRel { heap with memory := result }
      (writeHeaderStore store (UInt32.ofNat address.value)) frontierIndex := by
  have refined := related.writeHeader inBounds written
  rw [writeHeaderStore_eq_words, ResidentMemoryRel.writeUInt32sStore_eq,
    ← uint64Header_words]
  exact refined

/-- Canonical W6 admission boundary for the resident `UInt64` unbox helper.
It deliberately retains both the semantic decoder fact and the exact raw
header/payload reads consumed by the Wasm validator. -/
structure UInt64BoxAdmission (state : MemoryState) (address : Word32)
    (payload : UInt64) : Prop where
  valid : state.FrontierInvariant
  object : BoxedObjectRel state address .uint64 (.uint64 payload) uint64Header
  rawHeader : Header.ExactWords state.memory address uint64Header
  addressBase : heapBase ≤ address.value
  addressAligned : address.value % target.heapAlignment = 0
  payloadRead : state.memory.readUInt64 (address.value + headerBytes) =
    .ok payload

/-- Every successful heap-only W6 `UInt64` allocation establishes the exact
admission relation consumed by production unboxing. -/
theorem allocateBoxedScalar_uint64_admission
    (before after : MemoryState) (payload : UInt64) (address : Word32)
    (valid : before.FrontierInvariant)
    (frontierBase : heapBase ≤ before.heapCursor)
    (allocated : allocateBoxedScalar before (.uint64 payload) =
      .ok (after, address)) :
    UInt64BoxAdmission after address payload := by
  obtain ⟨middle, objectAllocation, payloadWrite, cursorEq⟩ :=
    allocateBoxedScalar_decompose before after (.uint64 payload) address
      allocated
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadInBounds :
      address.value + headerBytes + 7 < middle.memory.size := by
    have cursorInBounds := middleValid.cursorInBounds
    rw [middleExtent] at cursorInBounds
    simp [target, headerBytes, align8] at cursorInBounds ⊢
    omega
  have payloadRead := LinearMemory.readUInt64_of_writeUInt64_eq_ok middle.memory
    after.memory (address.value + headerBytes) payload payloadInBounds
      payloadWrite
  have stateEq : ({ middle with memory := after.memory } : MemoryState) =
      after := by
    cases middle
    cases after
    simp_all
  have finalValid :=
    (allocateBoxedScalar_objectRel before after (.uint64 payload) address valid
      allocated).1
  have headerBefore : middle.readLiveHeader address = .ok uint64Header := by
    simpa [uint64Header, target, headerBytes] using
      MemoryState.readLiveHeader_of_allocateObject_eq_ok before middle .boxed
        target.semanticSlotBytes false BoxedScalarKind.uint64.code 8 0 0
          address objectAllocation
  have headerFrame := middle.readLiveHeader_of_writeBoxedPayload after.memory
    address payload payloadInBounds payloadWrite
  have headerRead : after.readLiveHeader address = .ok uint64Header := by
    rw [← stateEq, headerFrame]
    exact headerBefore
  have initialExact : Header.ExactWords middle.memory address uint64Header := by
    simpa [uint64Header, target, headerBytes, BoxedScalar.kind,
      BoxedScalarKind.payloadBytes, BoxedScalarKind.abiKind, concreteBytes] using
      (Header.ExactWords.ofAllocateObject objectAllocation)
  have finalExact : Header.ExactWords after.memory address uint64Header := by
    refine ⟨?_⟩
    intro index word wordAt
    have indexLt := (List.getElem?_eq_some_iff.mp wordAt).1
    have withinHeader : 4 * index + 4 ≤ headerBytes := by
      simp [Header.words] at indexLt
      simp [headerBytes]
      omega
    calc
      after.memory.readUInt32 (address.value + 4 * index) =
          middle.memory.readUInt32 (address.value + 4 * index) :=
        LinearMemory.readUInt32_of_writeUInt64_eq_ok_other middle.memory
          after.memory (address.value + headerBytes)
          (address.value + 4 * index) payload payloadInBounds payloadWrite
          (by right; omega)
      _ = .ok word := initialExact.wordAt index word wordAt
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header before middle .boxed
      target.semanticSlotBytes false BoxedScalarKind.uint64.code 8 0 0 address
        objectAllocation
  have allocationPost := MemoryState.allocate_spec before rawState 40 address
    (by simpa [target, headerBytes, align8] using rawAllocation)
  have addressHeap : address.classify = .heap := allocationPost.addressClass
  have decoded : readBoxedScalar after .uint64 address =
      .ok (.uint64 payload) := by
    unfold readBoxedScalar
    rw [addressHeap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    have boxedBeq : (uint64Header.kind == ObjectKind.boxed) = true := by
      decide
    rw [boxedBeq]
    simp only [if_true]
    simpa [uint64Header, target, headerBytes, BoxedScalar.kind,
      BoxedScalarKind.payloadBytes, BoxedScalarKind.abiKind, concreteBytes] using
      readHeapBoxedScalar_forAllocation after address (.uint64 payload)
        payloadRead
  have resultExtent : address.value + 40 ≤ after.heapCursor := by
    rw [cursorEq, middleExtent]
    simp [target, headerBytes, align8]
  refine {
    valid := finalValid
    object := {
      scalarKind := rfl
      headerRead
      headerKind := rfl
      allocationBytes := by simp [uint64Header, Header.forAllocation, target,
        headerBytes, align8]
      kindCode := rfl
      payloadBytes := rfl
      reserved2 := rfl
      reserved3 := rfl
      headerOwned := by
        have minimum : address.value + headerBytes ≤ address.value + 40 := by
          simp [headerBytes]
        exact Nat.le_trans minimum resultExtent
      extent := by simpa [uint64Header, Header.forAllocation] using resultExtent
      decoded }
    rawHeader := finalExact
    addressBase := by
      rw [allocationPost.addressValue]
      exact Nat.le_trans frontierBase (align8_ge before.heapCursor)
    addressAligned := by
      rw [allocationPost.addressValue]
      change align8 before.heapCursor % 8 = 0
      exact align8_mod before.heapCursor
    payloadRead }

/-- Physical Talos body shared by generic `fir_box_uint16` and exact-result
`fir_box_uint16_tagged`.  Local zero is the `i32` payload; locals one through
three are raw bits, saved scratch word, and the object-family result. -/
def boxUInt16Program : Wasm.Program :=
  [.localGet 0, .localGet 0, .add, .const 1, .add] ++
  ResidentNat.retypeRawObjectResultProgram 1 2 3

/-- Exact Talos body of production `fir_box_uint64`.  Local zero is the
`i64` parameter; locals one through four are raw object, allocation address,
saved scratch word, and typed object result. -/
def boxUInt64Program (allocatorIndex : Nat) : Wasm.Program :=
  [.const 40, .call allocatorIndex, .localSet 2,
    .localGet 2, .const ObjectKind.boxed.code,
      .store32 (u32 headerKindOffset),
    .localGet 2, .const liveFlag, .store32 (u32 headerFlagsOffset),
    .localGet 2, .const 1, .store32 (u32 headerRefCountOffset),
    .localGet 2, .const 40, .store32 (u32 headerAllocationBytesOffset),
    .localGet 2, .const BoxedScalarKind.uint64.code,
      .store32 (u32 headerAux0Offset),
    .localGet 2, .const 8, .store32 (u32 headerAux1Offset),
    .localGet 2, .const 0, .store32 (u32 headerAux2Offset),
    .localGet 2, .const 0, .store32 (u32 headerAux3Offset),
    .localGet 2, .localGet 0, .store64 (u32 headerBytes),
    .localGet 2] ++
  ResidentNat.retypeRawObjectResultProgram 1 3 4

/-- Exact Talos body of production `fir_unbox_uint64`. -/
def unboxUInt64Program : Wasm.Program :=
  requireHeapAddressProgram 0 ++
  requireHeaderWordProgram 0 headerKindOffset ObjectKind.boxed.code ++
  trapUnlessProgram [.localGet 0, .load32 (u32 headerFlagsOffset),
    .const liveFlag, .and, .const liveFlag, .eq] ++
  requireHeaderWordProgram 0 headerAllocationBytesOffset 40 ++
  requireHeaderWordProgram 0 headerAux0Offset BoxedScalarKind.uint64.code ++
  requireHeaderWordProgram 0 headerAux1Offset 8 ++
  requireHeaderWordProgram 0 headerAux2Offset 0 ++
  requireHeaderWordProgram 0 headerAux3Offset 0 ++
  [.localGet 0, .load64 (u32 headerBytes), .ret]

def boxUInt64TargetFunction (allocatorIndex : Nat)
    (suffix : Wasm.Program := []) : Wasm.Function := {
  params := [.i64]
  locals := [.i32, .i32, .i32, .i32]
  results := [.i32]
  body := boxUInt64Program allocatorIndex ++ suffix }

def unboxUInt64TargetFunction (suffix : Wasm.Program := []) : Wasm.Function := {
  params := [.i32]
  locals := []
  results := [.i64]
  body := unboxUInt64Program ++ suffix }

/-- Concrete call frame of the one-parameter unbox helper. -/
def unboxUInt64Entry (object : UInt32) : Wasm.Locals := {
  params := [.i32 object]
  locals := []
  values := [] }

/-- Exact instruction-level success boundary of production `fir_unbox_uint64`.
The premises expose only the raw loads and admission checks performed by the
helper; the canonical W6 relation discharges them below. -/
theorem wp_unboxUInt64Program_of_reads
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object : UInt32} {payload : UInt64}
    (notBelowHeap : ¬object < u32 heapBase)
    (aligned : u32 (target.heapAlignment - 1) &&& object = 0)
    (wordInBounds : ∀ offset,
      offset ∈ [headerKindOffset, headerFlagsOffset,
        headerAllocationBytesOffset, headerAux0Offset, headerAux1Offset,
        headerAux2Offset, headerAux3Offset] →
      ¬(object.toNat + (u32 offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32 (object + u32 headerKindOffset) =
      ObjectKind.boxed.code)
    (flagsRead : store.mem.read32 (object + u32 headerFlagsOffset) = liveFlag)
    (allocationRead : store.mem.read32
      (object + u32 headerAllocationBytesOffset) = 40)
    (aux0Read : store.mem.read32 (object + u32 headerAux0Offset) =
      BoxedScalarKind.uint64.code)
    (aux1Read : store.mem.read32 (object + u32 headerAux1Offset) = 8)
    (aux2Read : store.mem.read32 (object + u32 headerAux2Offset) = 0)
    (aux3Read : store.mem.read32 (object + u32 headerAux3Offset) = 0)
    (payloadInBounds :
      ¬(object.toNat + (u32 headerBytes).toNat + 8 >
        store.mem.pages * wasmPageBytes))
    (payloadRead : store.mem.read64 (object + u32 headerBytes) = payload)
    (returned : Q (.Return store [.i64 payload])) :
    Wasm.wp module unboxUInt64Program Q store
      (unboxUInt64Entry object) env := by
  have objectFound (values : List Wasm.Value) :
      ({ unboxUInt64Entry object with values } : Wasm.Locals).get 0 =
        some (.i32 object) := by rfl
  have kindBound := wordInBounds headerKindOffset (by simp)
  have flagsBound := wordInBounds headerFlagsOffset (by simp)
  have allocationBound := wordInBounds headerAllocationBytesOffset (by simp)
  have aux0Bound := wordInBounds headerAux0Offset (by simp)
  have aux1Bound := wordInBounds headerAux1Offset (by simp)
  have aux2Bound := wordInBounds headerAux2Offset (by simp)
  have aux3Bound := wordInBounds headerAux3Offset (by simp)
  unfold unboxUInt64Program requireHeapAddressProgram
    requireHeaderWordProgram trapUnlessProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectFound, Wasm.wp_const_cons, Wasm.wp_ltU_cons, if_neg notBelowHeap,
    Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_const_cons, Wasm.wp_and_cons,
    aligned, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using kindBound), kindRead]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using flagsBound), flagsRead]
  simp only [Wasm.wp_const_cons, Wasm.wp_and_cons]
  rw [show liveFlag &&& liveFlag = liveFlag by decide]
  simp only [Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using allocationBound), allocationRead]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using aux0Bound), aux0Read]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using aux1Bound), aux1Read]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using aux2Bound), aux2Read]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using aux3Bound), aux3Read]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load64_cons]
  rw [if_neg (by simpa [wasmPageBytes] using payloadInBounds), payloadRead]
  simpa only [Wasm.wp_ret_cons, unboxUInt64Entry] using returned

/-- Any word below the resident heap base traps before the first memory
access. -/
theorem wp_unboxUInt64Program_belowHeap
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host} {object : UInt32}
    (below : object < u32 heapBase)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module unboxUInt64Program Q store
      (unboxUInt64Entry object) env := by
  have objectFound (values : List Wasm.Value) :
      ({ unboxUInt64Entry object with values } : Wasm.Locals).get 0 =
        some (.i32 object) := by rfl
  unfold unboxUInt64Program requireHeapAddressProgram
    requireHeaderWordProgram trapUnlessProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectFound, Wasm.wp_const_cons, Wasm.wp_ltU_cons, if_pos below,
    Wasm.wp_eq_cons]
  rw [if_neg (by decide : ¬(1 : UInt32) = 0)]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simpa only [Wasm.wp_unreachable_cons] using trapped

/-- A heap-range word that violates the eight-byte object alignment traps at
the second admission guard, still before any memory access. -/
theorem wp_unboxUInt64Program_misaligned
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host} {object : UInt32}
    (notBelow : ¬object < u32 heapBase)
    (misaligned : u32 (target.heapAlignment - 1) &&& object ≠ 0)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module unboxUInt64Program Q store
      (unboxUInt64Entry object) env := by
  have objectFound (values : List Wasm.Value) :
      ({ unboxUInt64Entry object with values } : Wasm.Locals).get 0 =
        some (.i32 object) := by rfl
  unfold unboxUInt64Program requireHeapAddressProgram
    requireHeaderWordProgram trapUnlessProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectFound, Wasm.wp_const_cons, Wasm.wp_ltU_cons, if_neg notBelow,
    Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_const_cons, Wasm.wp_and_cons,
    Wasm.wp_eq_cons, if_neg misaligned]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simpa only [Wasm.wp_unreachable_cons] using trapped

/-- A well-addressed heap word with a non-boxed raw kind traps at the first
header-word guard. -/
theorem wp_unboxUInt64Program_wrongKind
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object kind : UInt32}
    (notBelow : ¬object < u32 heapBase)
    (aligned : u32 (target.heapAlignment - 1) &&& object = 0)
    (kindInBounds :
      ¬(object.toNat + (u32 headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32 (object + u32 headerKindOffset) = kind)
    (wrongKind : kind ≠ ObjectKind.boxed.code)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module unboxUInt64Program Q store
      (unboxUInt64Entry object) env := by
  have objectFound (values : List Wasm.Value) :
      ({ unboxUInt64Entry object with values } : Wasm.Locals).get 0 =
        some (.i32 object) := by rfl
  unfold unboxUInt64Program requireHeapAddressProgram
    requireHeaderWordProgram trapUnlessProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectFound, Wasm.wp_const_cons, Wasm.wp_ltU_cons, if_neg notBelow,
    Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_const_cons, Wasm.wp_and_cons,
    aligned, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using kindInBounds), kindRead]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_neg wrongKind]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simpa only [Wasm.wp_unreachable_cons] using trapped

/-- Every low-bit tagged immediate is rejected.  Small tagged words fail the
heap-base check; larger ones fail the alignment check.  Neither path reads
linear memory. -/
theorem wp_unboxUInt64Program_tagged
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host} {object : UInt32}
    (tagged : (1 : UInt32) &&& object ≠ 0)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module unboxUInt64Program Q store
      (unboxUInt64Entry object) env := by
  by_cases below : object < u32 heapBase
  · exact wp_unboxUInt64Program_belowHeap below trapped
  · apply wp_unboxUInt64Program_misaligned below
    · intro aligned
      apply tagged
      have lowMask : (1 : UInt32) &&& 7 = 1 := by decide
      calc
        (1 : UInt32) &&& object = ((1 : UInt32) &&& 7) &&& object := by
          rw [lowMask]
        _ = (1 : UInt32) &&& (7 &&& object) := UInt32.and_assoc _ _ _
        _ = 0 := by
          have aligned' : (7 : UInt32) &&& object = 0 := by
            simpa [u32, target] using aligned
          rw [aligned']
          simp
    · exact trapped

/-- A canonical promoted tag is rejected as a non-boxed heap object.  The
proof starts from the actual W6 promoted allocation, so the result covers the
representation used when a tagged payload does not fit the immediate word. -/
theorem wp_unboxUInt64Program_of_allocatePromotedTag
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {before after : MemoryState}
    {store : Wasm.Store host} {payload : UInt64} {address : Word32}
    (valid : before.FrontierInvariant)
    (frontierBase : heapBase ≤ before.heapCursor)
    (allocated : allocatePromotedTag before payload = .ok (after, address))
    (related : ResidentMemoryRel after store.mem)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module unboxUInt64Program Q store
      (unboxUInt64Entry (UInt32.ofNat address.value)) env := by
  obtain ⟨middle, objectAllocation, payloadWrite, cursorEq⟩ :=
    allocatePromotedTag_decompose before after payload address allocated
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadInBounds :
      address.value + headerBytes + 7 < middle.memory.size := by
    have cursorInBounds := middleValid.cursorInBounds
    rw [middleExtent] at cursorInBounds
    simp [headerBytes, align8] at cursorInBounds ⊢
    omega
  have finalSize := LinearMemory.size_of_writeUInt64_eq_ok middle.memory
    after.memory (address.value + headerBytes) payload payloadInBounds
      payloadWrite
  let header := Header.forAllocation .natural 40 true promotedTagMarker 1
  have initialExact : Header.ExactWords middle.memory address header := by
    simpa [header, headerBytes, align8] using
      (Header.ExactWords.ofAllocateObject objectAllocation)
  have finalExact : Header.ExactWords after.memory address header := by
    refine ⟨?_⟩
    intro index word wordAt
    have indexLt := (List.getElem?_eq_some_iff.mp wordAt).1
    have withinHeader : 4 * index + 4 ≤ headerBytes := by
      simp [Header.words] at indexLt
      simp [headerBytes]
      omega
    calc
      after.memory.readUInt32 (address.value + 4 * index) =
          middle.memory.readUInt32 (address.value + 4 * index) :=
        LinearMemory.readUInt32_of_writeUInt64_eq_ok_other middle.memory
          after.memory (address.value + headerBytes)
          (address.value + 4 * index) payload payloadInBounds payloadWrite
          (by right; omega)
      _ = .ok word := initialExact.wordAt index word wordAt
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header before middle .natural 8 true
      promotedTagMarker 1 0 0 address objectAllocation
  have rawPost := MemoryState.allocate_spec before rawState 40 address
    (by simpa [headerBytes, align8] using rawAllocation)
  let object := UInt32.ofNat address.value
  have addressFits : address.value < UInt32.size := by
    simpa [wordModulus, UInt32.size] using address.isLt
  have objectToNat : object.toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' addressFits
  have addressBase : heapBase ≤ address.value := by
    rw [rawPost.addressValue]
    exact Nat.le_trans frontierBase (align8_ge before.heapCursor)
  have notBelow : ¬object < u32 heapBase := by
    intro below
    have belowNat := UInt32.lt_iff_toNat_lt.mp below
    have baseFits : heapBase < UInt32.size := by decide
    have baseToNat : (u32 heapBase).toNat = heapBase := by
      exact UInt32.toNat_ofNat_of_lt' baseFits
    rw [objectToNat, baseToNat] at belowNat
    exact (Nat.not_lt_of_ge addressBase) belowNat
  have addressAligned : address.value % 8 = 0 := by
    rw [rawPost.addressValue]
    exact align8_mod before.heapCursor
  have aligned : u32 (target.heapAlignment - 1) &&& object = 0 := by
    have alignedWord := ResidentAllocator.alignedWord_of_mod8 addressFits
      addressAligned
    simpa [object, u32, target, UInt32.and_comm] using alignedWord
  have kindLaneInBounds :
      address.value + headerKindOffset + 3 < after.memory.size := by
    rw [finalSize]
    have cursorInBounds := middleValid.cursorInBounds
    rw [middleExtent] at cursorInBounds
    simp [headerKindOffset, headerBytes, align8] at cursorInBounds ⊢
    omega
  have kindInBounds :
      ¬(object.toNat + (u32 headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes) := by
    rw [objectToNat, show (u32 headerKindOffset).toNat = headerKindOffset by
      decide, ← related.size_eq]
    omega
  have concreteKind : after.memory.readUInt32
      (address.value + headerKindOffset) = .ok ObjectKind.natural.code := by
    simpa [header, Header.forAllocation] using finalExact.readKind
  have kindRead : store.mem.read32 (object + u32 headerKindOffset) =
      ObjectKind.natural.code := by
    have bridge := related.readUInt32_eq_read32 kindLaneInBounds
    rw [concreteKind] at bridge
    have exactRead := Except.ok.inj bridge
    have physicalAddressEq : object + u32 headerKindOffset =
        UInt32.ofNat (address.value + headerKindOffset) := by
      simp [object, u32, UInt32.ofNat_add]
    rw [physicalAddressEq]
    exact exactRead.symm
  apply wp_unboxUInt64Program_wrongKind notBelow aligned kindInBounds kindRead
  · decide
  · exact trapped

/-- Canonical W6 admission and the common byte relation discharge every raw
production validator load.  Thus unboxing returns the payload bit-for-bit and
leaves the entire resident store unchanged. -/
theorem wp_unboxUInt64Program
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {state : MemoryState} {store : Wasm.Store host}
    {address : Word32} {payload : UInt64}
    (admitted : UInt64BoxAdmission state address payload)
    (related : ResidentMemoryRel state store.mem)
    (returned : Q (.Return store [.i64 payload])) :
    Wasm.wp module unboxUInt64Program Q store
      (unboxUInt64Entry (UInt32.ofNat address.value)) env := by
  let object := UInt32.ofNat address.value
  have addressFits : address.value < UInt32.size := by
    simpa [wordModulus, UInt32.size] using address.isLt
  have objectToNat : object.toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' addressFits
  have offsetToNat (offset : Nat) (small : offset < UInt32.size) :
      (u32 offset).toNat = offset := by
    exact UInt32.toNat_ofNat_of_lt' small
  have extentInBounds : address.value + 40 ≤ state.memory.size :=
    Nat.le_trans (by
      simpa [uint64Header, Header.forAllocation] using admitted.object.extent)
      admitted.valid.cursorInBounds
  have laneInBounds (offset : Nat) (within : offset + 4 ≤ 40) :
      address.value + offset + 3 < state.memory.size := by omega
  have physicalBound (offset : Nat) (within : offset + 4 ≤ 40) :
      ¬(object.toNat + (u32 offset).toNat + 4 >
        store.mem.pages * wasmPageBytes) := by
    have offsetSmall : offset < UInt32.size := by
      unfold UInt32.size
      omega
    rw [objectToNat, offsetToNat offset offsetSmall,
      ← related.size_eq]
    omega
  have physicalRead (offset : Nat) (value : UInt32)
      (within : offset + 4 ≤ 40)
      (read : state.memory.readUInt32 (address.value + offset) = .ok value) :
      store.mem.read32 (object + u32 offset) = value := by
    have bridge := related.readUInt32_eq_read32
      (laneInBounds offset within)
    rw [read] at bridge
    have exactRead := Except.ok.inj bridge
    have physicalAddressEq : object + u32 offset =
        UInt32.ofNat (address.value + offset) := by
      simp [object, u32, UInt32.ofNat_add]
    rw [physicalAddressEq]
    exact exactRead.symm
  have notBelowHeap : ¬object < u32 heapBase := by
    intro below
    have belowNat := UInt32.lt_iff_toNat_lt.mp below
    have baseFits : heapBase < UInt32.size := by decide
    rw [objectToNat, offsetToNat heapBase baseFits] at belowNat
    exact (Nat.not_lt_of_ge admitted.addressBase) belowNat
  have aligned : u32 (target.heapAlignment - 1) &&& object = 0 := by
    have objectAligned := ResidentAllocator.alignedWord_of_mod8 addressFits (by
      simpa [target] using admitted.addressAligned)
    simpa [object, u32, target, UInt32.and_comm] using objectAligned
  have wordBounds : ∀ offset,
      offset ∈ [headerKindOffset, headerFlagsOffset,
        headerAllocationBytesOffset, headerAux0Offset, headerAux1Offset,
        headerAux2Offset, headerAux3Offset] →
      ¬(object.toNat + (u32 offset).toNat + 4 >
        store.mem.pages * wasmPageBytes) := by
    intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (apply physicalBound; decide)
  have kindRead : store.mem.read32 (object + u32 headerKindOffset) =
      ObjectKind.boxed.code := by
    apply physicalRead headerKindOffset ObjectKind.boxed.code (by decide)
    simpa [uint64Header, Header.forAllocation] using admitted.rawHeader.readKind
  have flagsRead : store.mem.read32 (object + u32 headerFlagsOffset) =
      liveFlag := by
    apply physicalRead headerFlagsOffset liveFlag (by decide)
    change state.memory.readUInt32 (address.value + headerFlagsOffset) = .ok 2
    simpa [uint64Header, Header.forAllocation, Header.flags] using
      admitted.rawHeader.readFlags
  have allocationRead : store.mem.read32
      (object + u32 headerAllocationBytesOffset) = 40 := by
    apply physicalRead headerAllocationBytesOffset 40 (by decide)
    simpa [uint64Header, Header.forAllocation] using
      admitted.rawHeader.readAllocationBytes
  have aux0Read : store.mem.read32 (object + u32 headerAux0Offset) =
      BoxedScalarKind.uint64.code := by
    apply physicalRead headerAux0Offset BoxedScalarKind.uint64.code (by decide)
    simpa [uint64Header, Header.forAllocation] using admitted.rawHeader.readAux0
  have aux1Read : store.mem.read32 (object + u32 headerAux1Offset) = 8 := by
    apply physicalRead headerAux1Offset 8 (by decide)
    simpa [uint64Header, Header.forAllocation] using admitted.rawHeader.readAux1
  have aux2Read : store.mem.read32 (object + u32 headerAux2Offset) = 0 := by
    apply physicalRead headerAux2Offset 0 (by decide)
    simpa [uint64Header, Header.forAllocation] using admitted.rawHeader.readAux2
  have aux3Read : store.mem.read32 (object + u32 headerAux3Offset) = 0 := by
    apply physicalRead headerAux3Offset 0 (by decide)
    simpa [uint64Header, Header.forAllocation] using admitted.rawHeader.readAux3
  have payloadLaneInBounds :
      address.value + headerBytes + 7 < state.memory.size := by
    simp [headerBytes] at extentInBounds ⊢
    omega
  have physicalPayloadBound :
      ¬(object.toNat + (u32 headerBytes).toNat + 8 >
        store.mem.pages * wasmPageBytes) := by
    rw [objectToNat, offsetToNat headerBytes (by decide),
      ← related.size_eq]
    omega
  have payloadRead : store.mem.read64 (object + u32 headerBytes) = payload := by
    have bridge := related.readUInt64_eq_read64 payloadLaneInBounds
    rw [admitted.payloadRead] at bridge
    have exactRead := Except.ok.inj bridge
    have physicalAddressEq : object + u32 headerBytes =
        UInt32.ofNat (address.value + headerBytes) := by
      simp [object, u32, UInt32.ofNat_add]
    rw [physicalAddressEq]
    exact exactRead.symm
  simpa [object] using
    wp_unboxUInt64Program_of_reads notBelowHeap aligned wordBounds kindRead
      flagsRead allocationRead aux0Read aux1Read aux2Read aux3Read
      physicalPayloadBound payloadRead returned

/-- Any source helper with the common `UInt16` alias shape adapts to one
physical program, independently of whether its symbolic result load is
`.tobject` or `.tagged`.  `FirTalos.instruction` erases either annotation to
the same i32 load, while all three corresponding locals erase to i32. -/
theorem instructions_boxUInt16SourceProgram
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {resultKind : Fir.Wasm.AbiKind} {value raw saved result : Lean.FVarId}
    (shape : sourceFunction.body =
      boxUInt16SourceProgram resultKind value raw saved result)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some 0)
    (rawFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) raw =
        some 1)
    (savedFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) saved =
        some 2)
    (resultFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) result =
        some 3) :
    FirTalos.instructions sourceModule sourceFunction [] sourceFunction.body =
      .ok boxUInt16Program := by
  rw [shape]
  have valueGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) valueFound
  have rawSet := FirTalos.Correctness.instruction_localSet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) rawFound
  have rawGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) rawFound
  have savedSet := FirTalos.Correctness.instruction_localSet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) savedFound
  have savedGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) savedFound
  have resultSet := FirTalos.Correctness.instruction_localSet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) resultFound
  have resultGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) resultFound
  set_option maxRecDepth 100000 in
    simp [boxUInt16SourceProgram, boxUInt16Program, retypeRawResultSource,
      ResidentNat.retypeRawObjectResultProgram,
      FirTalos.instructions, FirTalos.instruction, valueGet, rawSet, rawGet,
      savedSet, savedGet, resultSet, resultGet,
      Bind.bind, Except.bind, pure, Except.pure]

/-- The generic production `UInt16` helper instantiates the annotation-erasing
adapter boundary. -/
theorem instructions_boxUInt16Function {sourceModule : Fir.Wasm.Module} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function []
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt16Function.body =
        .ok boxUInt16Program := by
  apply instructions_boxUInt16SourceProgram boxUInt16Function_shape
  · decide
  · decide
  · decide
  · decide

/-- Any source helper with the exact-object `UInt64` alias shape adapts to the
same heap-only physical program as the generic helper.  The `.object` result
load is erased to the same i32 load as `.tobject`; allocation and stores are
therefore untouched. -/
theorem instructions_boxUInt64ObjectSourceProgram
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {allocatorIndex : Nat} {value raw address saved result : Lean.FVarId}
    (shape : sourceFunction.body =
      boxUInt64ObjectSourceProgram value raw address saved result)
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some 0)
    (rawFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) raw =
        some 1)
    (addressFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) address =
        some 2)
    (savedFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) saved =
        some 3)
    (resultFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) result =
        some 4) :
    FirTalos.instructions sourceModule sourceFunction [] sourceFunction.body =
      .ok (boxUInt64Program allocatorIndex) := by
  rw [shape]
  have allocatorCall := FirTalos.Correctness.instruction_call
    (source := sourceFunction) (labels := []) allocatorFound
  have valueGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) valueFound
  have rawGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) rawFound
  have rawSet := FirTalos.Correctness.instruction_localSet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) rawFound
  have addressSet := FirTalos.Correctness.instruction_localSet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) addressFound
  have addressGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) addressFound
  have savedSet := FirTalos.Correctness.instruction_localSet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) savedFound
  have savedGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) savedFound
  have resultSet := FirTalos.Correctness.instruction_localSet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) resultFound
  have resultGet := FirTalos.Correctness.instruction_localGet
    (sourceModule := sourceModule) (source := sourceFunction)
    (labels := []) resultFound
  set_option maxRecDepth 100000 in
    simp [boxUInt64ObjectSourceProgram, boxUInt64Program,
      storeAddress32Source, storeAddress64Source, retypeRawResultSource,
      ResidentNat.retypeRawObjectResultProgram,
      FirTalos.instructions, FirTalos.instruction, allocatorCall,
      valueGet, rawGet, rawSet, addressSet, addressGet, savedSet, savedGet,
      resultSet, resultGet,
      Bind.bind, Except.bind, pure, Except.pure]

/-- The adapter preserves the complete production box body exactly. -/
theorem instructions_boxUInt64Function
    {sourceModule : Fir.Wasm.Module} {allocatorIndex : Nat}
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function []
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.body =
        .ok (boxUInt64Program allocatorIndex) := by
  have valueFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.params.toList ++
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals.toList)
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.params[0]!.1 =
        some 0 := by decide
  have rawFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.params.toList ++
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals.toList)
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals[0]!.1 =
        some 1 := by decide
  have addressFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.params.toList ++
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals.toList)
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals[1]!.1 =
        some 2 := by decide
  have savedFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.params.toList ++
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals.toList)
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals[2]!.1 =
        some 3 := by decide
  have resultFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.params.toList ++
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals.toList)
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function.locals[3]!.1 =
        some 4 := by decide
  rw [boxUInt64Function_shape]
  set_option maxRecDepth 100000 in
    simp [boxUInt64SourceProgram, boxUInt64Program, storeAddress32Source,
      storeAddress64Source, ResidentNat.retypeRawObjectResultSource,
      ResidentNat.retypeRawObjectResultProgram,
      FirTalos.instructions, FirTalos.instruction, allocatorFound,
      valueFound, rawFound, addressFound, savedFound, resultFound,
      Bind.bind, Except.bind, pure, Except.pure]

/-- The adapter preserves the complete production unbox body exactly. -/
theorem instructions_unboxUInt64Function
    {sourceModule : Fir.Wasm.Module} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function []
      Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function.body =
        .ok unboxUInt64Program := by
  have objectFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function.params.toList ++
        Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function.locals.toList)
      Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function.params[0]!.1 =
        some 0 := by decide
  rw [unboxUInt64Function_shape]
  set_option maxRecDepth 100000 in
    simp [unboxUInt64SourceProgram, unboxUInt64Program,
      requireHeapAddressSource, requireHeapAddressProgram,
      requireHeaderWordSource, requireHeaderWordProgram,
      trapUnlessSource, trapUnlessProgram, equalsConstSource,
      FirTalos.instructions, FirTalos.instruction, objectFound,
      Bind.bind, Except.bind, pure, Except.pure]

/-- Successful adaptation recovers the entire canonical box function. -/
theorem adaptedBoxUInt64Function_eq
    {sourceModule : Fir.Wasm.Module} {allocatorIndex : Nat}
    {targetFunction : Wasm.Function}
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex)
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function = .ok targetFunction) :
    targetFunction = boxUInt64TargetFunction allocatorIndex
      (FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function) := by
  unfold FirTalos.function at adapted
  rw [instructions_boxUInt64Function allocatorFound] at adapted
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at adapted
  simpa [boxUInt64TargetFunction,
    Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function,
    FirTalos.abiKind, Fir.Wasm.AbiKind.valueType, FirTalos.valueType]
    using adapted.symm

/-- Successful adaptation recovers the entire canonical unbox function. -/
theorem adaptedUnboxUInt64Function_eq
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function = .ok targetFunction) :
    targetFunction = unboxUInt64TargetFunction
      (FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function) := by
  unfold FirTalos.function at adapted
  rw [instructions_unboxUInt64Function] at adapted
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at adapted
  simpa [unboxUInt64TargetFunction,
    Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function,
    FirTalos.abiKind, Fir.Wasm.AbiKind.valueType, FirTalos.valueType]
    using adapted.symm

/-- Production installation evidence for one exact scalar-box alias.  The
source function itself is a parameter, so the same boundary covers tagged
immediates and heap objects without introducing a proof certificate into the
compiler. -/
structure ExactBoxAliasInstallation (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module) (sourceFunction : Fir.Wasm.Function) where
  target : Wasm.Function
  index : Nat
  adapted : FirTalos.function sourceModule sourceFunction = .ok target
  call : FirTalos.callIndex? sourceModule (.declaration sourceFunction.name) =
    some index
  notImport : module.imports[index]? = none
  installed : module.funcs[index - module.imports.length]? = some target

/-- Successful source adaptation turns a proved physical core into the exact
installed alias body, followed only by the adapter's validation terminal. -/
theorem ExactBoxAliasInstallation.body_of_instructions
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {core : Wasm.Program}
    (installation :
      ExactBoxAliasInstallation sourceModule module sourceFunction)
    (coreAdapted : FirTalos.instructions sourceModule sourceFunction []
      sourceFunction.body = .ok core) :
    installation.target.body =
      core ++ FirTalos.functionTerminal sourceModule sourceFunction := by
  obtain ⟨targetBody, bodyAdapted, targetBodyEq⟩ :=
    FirTalos.Correctness.function_preserves_body installation.adapted
  rw [coreAdapted] at bodyAdapted
  injection bodyAdapted with targetBodyEqCore
  simpa [targetBodyEqCore] using targetBodyEq

/-- Production exact-result installation for the tagged `UInt16` alias. -/
abbrev UInt16TaggedInstallation (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module) :=
  ExactBoxAliasInstallation sourceModule module
    Fir.Wasm.Emit.ResidentScalarBox.boxUInt16TaggedFunction

/-- Production exact-result installation for the heap-only `UInt64` alias. -/
abbrev UInt64ObjectInstallation (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module) :=
  ExactBoxAliasInstallation sourceModule module
    Fir.Wasm.Emit.ResidentScalarBox.boxUInt64ObjectFunction

/-- The installed tagged `UInt16` alias retains the generic helper's complete
physical `i32 -> i32` signature. -/
theorem UInt16TaggedInstallation.signature
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt16TaggedInstallation sourceModule module) :
    installation.target.params = [.i32] ∧
      installation.target.locals = [.i32, .i32, .i32] ∧
      installation.target.results = [.i32] := by
  obtain ⟨params, locals, results⟩ :=
    FirTalos.Correctness.function_preserves_signature installation.adapted
  obtain ⟨paramsPhysical, localsPhysical, resultsPhysical⟩ :=
    boxUInt16Tagged_physicalSignature
  refine ⟨?_, ?_, ?_⟩
  · rw [params, paramsPhysical]
    native_decide
  · rw [locals, localsPhysical]
    native_decide
  · rw [results, resultsPhysical]
    native_decide

/-- The installed exact-object `UInt64` alias retains the generic heap-only
helper's complete `i64 -> i32` physical signature. -/
theorem UInt64ObjectInstallation.signature
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt64ObjectInstallation sourceModule module) :
    installation.target.params = [.i64] ∧
      installation.target.locals = [.i32, .i32, .i32, .i32] ∧
      installation.target.results = [.i32] := by
  obtain ⟨params, locals, results⟩ :=
    FirTalos.Correctness.function_preserves_signature installation.adapted
  obtain ⟨paramsPhysical, localsPhysical, resultsPhysical⟩ :=
    boxUInt64Object_physicalSignature
  refine ⟨?_, ?_, ?_⟩
  · rw [params, paramsPhysical]
    native_decide
  · rw [locals, localsPhysical]
    native_decide
  · rw [results, resultsPhysical]
    native_decide

/-- Static adapter, resolver, and target-module evidence for the exact three
installed functions used by heap-only `UInt64` boxing.  The three indices are
recorded separately, so the source module's resolved installation order is
preserved rather than reconstructed by the proof. -/
structure UInt64Installation (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module) where
  allocatorTarget : Wasm.Function
  boxTarget : Wasm.Function
  unboxTarget : Wasm.Function
  allocatorIndex : Nat
  boxIndex : Nat
  unboxIndex : Nat
  frontierIndex : Nat
  allocatorAdapted : FirTalos.function sourceModule
    (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
      .ok allocatorTarget
  allocatorCall : FirTalos.callIndex? sourceModule
    (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
      some allocatorIndex
  allocatorNotImport : module.imports[allocatorIndex]? = none
  allocatorInstalled :
    module.funcs[allocatorIndex - module.imports.length]? = some allocatorTarget
  boxAdapted : FirTalos.function sourceModule
    Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function = .ok boxTarget
  boxCall : FirTalos.callIndex? sourceModule
    (.declaration Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Name) = some boxIndex
  boxNotImport : module.imports[boxIndex]? = none
  boxInstalled : module.funcs[boxIndex - module.imports.length]? = some boxTarget
  unboxAdapted : FirTalos.function sourceModule
    Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function = .ok unboxTarget
  unboxCall : FirTalos.callIndex? sourceModule
    (.declaration Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Name) =
      some unboxIndex
  unboxNotImport : module.imports[unboxIndex]? = none
  unboxInstalled :
    module.funcs[unboxIndex - module.imports.length]? = some unboxTarget

/-- The installed box helper retains W7's stable `i64 -> i32` physical
signature and its four private locals. -/
theorem UInt64Installation.box_signature
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt64Installation sourceModule module) :
    installation.boxTarget.params = [.i64] ∧
      installation.boxTarget.locals = [.i32, .i32, .i32, .i32] ∧
      installation.boxTarget.results = [.i32] := by
  obtain ⟨params, locals, results⟩ :=
    FirTalos.Correctness.function_preserves_signature installation.boxAdapted
  exact ⟨by simpa [Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using params,
    by simpa [Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using locals,
    by simpa [Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType]
      using results⟩

/-- The installed unbox helper retains W7's stable `i32 -> i64` physical
signature and has no private locals. -/
theorem UInt64Installation.unbox_signature
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt64Installation sourceModule module) :
    installation.unboxTarget.params = [.i32] ∧
      installation.unboxTarget.locals = [] ∧
      installation.unboxTarget.results = [.i64] := by
  obtain ⟨params, locals, results⟩ :=
    FirTalos.Correctness.function_preserves_signature installation.unboxAdapted
  exact ⟨by simpa [Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using params,
    by simpa [Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using locals,
    by simpa [Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType]
      using results⟩

/-- Exact installed box body: the verified core followed only by the standard
adapter terminal marker. -/
theorem UInt64Installation.box_body
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt64Installation sourceModule module) :
    installation.boxTarget.body =
      boxUInt64Program installation.allocatorIndex ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentScalarBox.boxUInt64Function := by
  rw [adaptedBoxUInt64Function_eq installation.allocatorCall
    installation.boxAdapted]
  rfl

/-- Exact installed unbox body, with the same terminal-marker convention. -/
theorem UInt64Installation.unbox_body
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt64Installation sourceModule module) :
    installation.unboxTarget.body = unboxUInt64Program ++
      FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentScalarBox.unboxUInt64Function := by
  rw [adaptedUnboxUInt64Function_eq installation.unboxAdapted]
  rfl

/-- Concrete call frame of the one-parameter/four-local box helper. -/
def boxUInt64Entry (payload : UInt64) : Wasm.Locals := {
  params := [.i64 payload]
  locals := [.i32 0, .i32 0, .i32 0, .i32 0]
  values := [] }

/-- The exact-object alias has the same concrete entry frame as the generic
heap-only helper, independently of caller operand slack. -/
theorem UInt64ObjectInstallation.box_entry
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt64ObjectInstallation sourceModule module)
    (payload : UInt64) (tail : List Wasm.Value) :
    installation.target.toLocals
        (([Wasm.Value.i64 payload] ++ tail).take
          installation.target.numParams).reverse =
      boxUInt64Entry payload := by
  obtain ⟨params, locals, _⟩ := installation.signature
  simp [Wasm.Function.toLocals, Wasm.Function.numParams, params, locals,
    boxUInt64Entry, Wasm.ValueType.zero]

/-- The installed box calling convention builds exactly the verified entry
frame, independently of caller operand slack. -/
theorem UInt64Installation.box_entry
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt64Installation sourceModule module)
    (payload : UInt64) (tail : List Wasm.Value) :
    installation.boxTarget.toLocals
        (([Wasm.Value.i64 payload] ++ tail).take
          installation.boxTarget.numParams).reverse =
      boxUInt64Entry payload := by
  obtain ⟨params, locals, _⟩ := installation.box_signature
  simp [Wasm.Function.toLocals, Wasm.Function.numParams, params, locals,
    boxUInt64Entry, Wasm.ValueType.zero]

/-- The installed unbox calling convention builds exactly the verified entry
frame. -/
theorem UInt64Installation.unbox_entry
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : UInt64Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value) :
    installation.unboxTarget.toLocals
        (([Wasm.Value.i32 object] ++ tail).take
          installation.unboxTarget.numParams).reverse =
      unboxUInt64Entry object := by
  obtain ⟨params, locals, _⟩ := installation.unbox_signature
  simp [Wasm.Function.toLocals, Wasm.Function.numParams, params, locals,
    unboxUInt64Entry]

def boxUInt64AllocatedLocals (payload : UInt64) (address : UInt32) :
    Wasm.Locals := {
  params := [.i64 payload]
  locals := [.i32 0, .i32 address, .i32 0, .i32 0]
  values := [] }

def boxUInt64RawLocals (payload : UInt64) (address : UInt32) :
    Wasm.Locals := {
  params := [.i64 payload]
  locals := [.i32 address, .i32 address, .i32 0, .i32 0]
  values := [.i32 address] }

def boxUInt64SavedLocals (payload : UInt64) (address saved : UInt32) :
    Wasm.Locals := {
  params := [.i64 payload]
  locals := [.i32 address, .i32 address, .i32 saved, .i32 0]
  values := [.i32 saved] }

def boxUInt64ResultLocals (payload : UInt64) (address saved : UInt32) :
    Wasm.Locals := {
  params := [.i64 payload]
  locals := [.i32 address, .i32 address, .i32 saved, .i32 address]
  values := [.i32 address] }

/-- Exact instruction-level execution of the production box body after the
shared raw allocator call.  Every header/payload write is checked against the
single 40-byte allocation extent, and the scratch cast restores the complete
store before returning the object word. -/
theorem wp_boxUInt64Program
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store allocatedStore : Wasm.Store host}
    {allocatorIndex : Nat} {payload : UInt64} {address : UInt32}
    (allocateRun : Wasm.TerminatesWith env module allocatorIndex store
      [.i32 40]
      (fun final values =>
        final = allocatedStore ∧ values = [.i32 address]))
    (allocationInBounds : address.toNat + 40 ≤
      allocatedStore.mem.pages * wasmPageBytes)
    (returned : Q (.Return
      (writePayloadStore allocatedStore address payload) [.i32 address])) :
    Wasm.wp module (boxUInt64Program allocatorIndex) Q store
      (boxUInt64Entry payload) env := by
  have bound (offset : Nat) (within : offset + 4 ≤ 40) :
      address.toNat + (u32 offset).toNat + 4 ≤
        allocatedStore.mem.pages * wasmPageBytes := by
    have offsetFits : offset < UInt32.size := by
      unfold UInt32.size
      omega
    have offsetRoundtrip : (u32 offset).toNat = offset := by
      unfold u32
      exact UInt32.toNat_ofNat_of_lt' offsetFits
    rw [offsetRoundtrip]
    omega
  have payloadBound : address.toNat + (u32 headerBytes).toNat + 8 ≤
      allocatedStore.mem.pages * wasmPageBytes := by
    have offsetRoundtrip : (u32 headerBytes).toNat = headerBytes := by
      decide
    rw [offsetRoundtrip]
    simpa [headerBytes] using allocationInBounds
  have pagesPositive : 0 <
      (writePayloadStore allocatedStore address payload).mem.pages := by
    have basePositive : 0 < allocatedStore.mem.pages := by
      unfold wasmPageBytes at allocationInBounds
      omega
    simpa [writePayloadStore, writeHeaderStore,
      ResidentMemoryRel.write32Store, Wasm.Mem.write64] using basePositive
  have allocatedAddress :
      (boxUInt64AllocatedLocals payload address).get 2 =
        some (.i32 address) := by
    rfl
  have allocatedPayload :
      (boxUInt64AllocatedLocals payload address).get 0 =
        some (.i64 payload) := by
    rfl
  unfold boxUInt64Program
  simp only [List.cons_append, List.nil_append, Wasm.wp_const_cons]
  apply Wasm.wp_call_tw allocateRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  apply FirTalos.Correctness.wp_localSet_of_set
    (locals := boxUInt64Entry payload)
    (updated := boxUInt64AllocatedLocals payload address)
    (tail := [])
  · rfl
  · apply ResidentMemoryRel.wp_store32_const_of_inBounds
      (address := address) (value := ObjectKind.boxed.code)
      (offset := u32 headerKindOffset) (addressIndex := 2)
    · exact allocatedAddress
    · exact bound headerKindOffset (by decide)
    · apply ResidentMemoryRel.wp_store32_const_of_inBounds
        (address := address) (value := liveFlag)
        (offset := u32 headerFlagsOffset) (addressIndex := 2)
      · exact allocatedAddress
      · simpa using bound headerFlagsOffset (by decide)
      · apply ResidentMemoryRel.wp_store32_const_of_inBounds
          (address := address) (value := 1)
          (offset := u32 headerRefCountOffset) (addressIndex := 2)
        · exact allocatedAddress
        · simpa using bound headerRefCountOffset (by decide)
        · apply ResidentMemoryRel.wp_store32_const_of_inBounds
            (address := address) (value := 40)
            (offset := u32 headerAllocationBytesOffset) (addressIndex := 2)
          · exact allocatedAddress
          · simpa using bound headerAllocationBytesOffset (by decide)
          · apply ResidentMemoryRel.wp_store32_const_of_inBounds
              (address := address) (value := BoxedScalarKind.uint64.code)
              (offset := u32 headerAux0Offset) (addressIndex := 2)
            · exact allocatedAddress
            · simpa using bound headerAux0Offset (by decide)
            · apply ResidentMemoryRel.wp_store32_const_of_inBounds
                (address := address) (value := 8)
                (offset := u32 headerAux1Offset) (addressIndex := 2)
              · exact allocatedAddress
              · simpa using bound headerAux1Offset (by decide)
              · apply ResidentMemoryRel.wp_store32_const_of_inBounds
                  (address := address) (value := 0)
                  (offset := u32 headerAux2Offset) (addressIndex := 2)
                · exact allocatedAddress
                · simpa using bound headerAux2Offset (by decide)
                · apply ResidentMemoryRel.wp_store32_const_of_inBounds
                    (address := address) (value := 0)
                    (offset := u32 headerAux3Offset) (addressIndex := 2)
                  · exact allocatedAddress
                  · simpa using bound headerAux3Offset (by decide)
                  · apply ResidentMemoryRel.wp_store64_localGet_of_inBounds
                      (address := address) (value := payload)
                      (offset := u32 headerBytes)
                      (addressIndex := 2) (valueIndex := 0)
                    · exact allocatedAddress
                    · exact allocatedPayload
                    · simpa [writeHeaderStore,
                        ResidentMemoryRel.write32Store] using payloadBound
                    · simp only [Wasm.wp_localGet_cons]
                      change Wasm.wp module
                        (ResidentNat.retypeRawObjectResultProgram 1 3 4) Q
                        (writePayloadStore final address payload)
                        { boxUInt64AllocatedLocals payload address with
                          values := [.i32 address] } env
                      have rawSet :
                          ({ boxUInt64AllocatedLocals payload address with
                            values := [.i32 address] }).set? 1 (.i32 address) =
                            some (boxUInt64RawLocals payload address) := by
                        simp [boxUInt64AllocatedLocals, boxUInt64RawLocals,
                          Wasm.Locals.set?]
                      have savedSet :
                          ({ boxUInt64RawLocals payload address with values :=
                            [.i32 ((writePayloadStore final address payload).mem.read32 0)]
                          }).set? 3
                            (.i32 ((writePayloadStore final address payload).mem.read32 0)) =
                            some (boxUInt64SavedLocals payload address
                              ((writePayloadStore final address payload).mem.read32 0)) := by
                        simp [boxUInt64RawLocals, boxUInt64SavedLocals,
                          Wasm.Locals.set?]
                      have resultSet :
                          ({ boxUInt64SavedLocals payload address
                              ((writePayloadStore final address payload).mem.read32 0)
                            with values := [.i32 address] }).set? 4 (.i32 address) =
                            some (boxUInt64ResultLocals payload address
                              ((writePayloadStore final address payload).mem.read32 0)) := by
                        simp [boxUInt64SavedLocals, boxUInt64ResultLocals,
                          Wasm.Locals.set?]
                      exact ResidentNat.wp_retypeRawObjectResultProgram
                        (initial := boxUInt64AllocatedLocals payload address)
                        (afterRaw := boxUInt64RawLocals payload address)
                        (afterSaved := boxUInt64SavedLocals payload address
                          ((writePayloadStore final address payload).mem.read32 0))
                        (afterResult := boxUInt64ResultLocals payload address
                          ((writePayloadStore final address payload).mem.read32 0))
                        pagesPositive (by decide) (by decide) rawSet savedSet
                          resultSet returned

/-- The production box body implements W6's heap-only `UInt64` allocator for
every 64-bit payload.  The result simultaneously preserves the allocating
runtime relation, establishes the canonical unbox admission boundary, and
returns the exact fresh object word. -/
theorem wp_boxUInt64Program_of_allocateBoxedScalar
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {allocatorFunction : Wasm.Function}
    {allocatorIndex frontierIndex : Nat}
    {before after : MemoryState} {store : Wasm.Store host}
    {payload : UInt64} {address : Word32}
    (allocatorAdapted : FirTalos.function sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
        .ok allocatorFunction)
    (allocatorNotImport : module.imports[allocatorIndex]? = none)
    (allocatorFound :
      module.funcs[allocatorIndex - module.imports.length]? =
        some allocatorFunction)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store frontierIndex)
    (allocated : allocateBoxedScalar before (.uint64 payload) =
      .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore frontierIndex ∧
      UInt64BoxAdmission after address payload ∧
      Wasm.wp module (boxUInt64Program allocatorIndex)
        (fun completion => completion = .Return finalStore
          [.i32 (UInt32.ofNat address.value)]) store
        (boxUInt64Entry payload) env := by
  obtain ⟨objectState, objectAllocation, payloadWrite, afterCursor⟩ :=
    allocateBoxedScalar_decompose before after (.uint64 payload) address
      allocated
  obtain ⟨rawState, rawAllocation, headerWrite, objectCursor, _⟩ :=
    MemoryState.allocateObject_header before objectState .boxed
      target.semanticSlotBytes false BoxedScalarKind.uint64.code 8 0 0 address
        objectAllocation
  have rawStrict : rawState.heapCursor < wordModulus := by
    rw [← objectCursor, ← afterCursor]
    exact strictEnd
  have rawWithinCap :
      (rawState.heapCursor - 1) / wasmPageBytes + 1 ≤
        store.memoryCap module 0 := by
    rw [← objectCursor, ← afterCursor]
    exact withinCap
  obtain ⟨allocatedStore, rawRelated, allocatorRun⟩ :=
    ResidentAllocator.terminatesWith_allocateFunction_of_allocate
      (env := env) allocatorAdapted allocatorNotImport allocatorFound memory32
      valid related
      (requestedAligned := (by decide : 40 % target.heapAlignment = 0))
      (by simpa [target, headerBytes, align8] using rawAllocation)
      rawStrict rawWithinCap
  have rawPost := MemoryState.allocate_spec before rawState 40 address
    (by simpa [target, headerBytes, align8] using rawAllocation)
  have headerInBounds : address.value + headerBytes ≤ rawState.memory.size := by
    have endInBounds := rawPost.endInBounds
    simp [headerBytes] at endInBounds ⊢
    omega
  let physicalAddress := UInt32.ofNat address.value
  let headerStore := writeHeaderStore allocatedStore physicalAddress
  have headerStateEq :
      ({ rawState with memory := objectState.memory } : MemoryState) =
        objectState := by
    cases rawState
    cases objectState
    simp_all only
  have headerRelated :
      ResidentAllocatorRel objectState headerStore frontierIndex := by
    have headerWrite' : uint64Header.write rawState.memory address =
        .ok objectState.memory := by
      simpa [uint64Header, target, headerBytes, align8] using headerWrite
    have refined := writeHeaderStore_refines rawRelated headerInBounds
      headerWrite'
    rw [headerStateEq] at refined
    simpa only [headerStore, physicalAddress] using refined
  have payloadInBounds :
      address.value + headerBytes + 7 < objectState.memory.size := by
    have objectValid := valid.allocateObject objectAllocation
    have objectExtent := MemoryState.allocateObject_extent objectAllocation
    have cursorInBounds := objectValid.cursorInBounds
    rw [objectExtent] at cursorInBounds
    simp [target, headerBytes, align8] at cursorInBounds ⊢
    omega
  let finalStore := writePayloadStore allocatedStore physicalAddress payload
  have payloadRelatedRaw :=
    headerRelated.writeUInt64 payloadInBounds payloadWrite
  have finalStateEq :
      ({ objectState with memory := after.memory } : MemoryState) = after := by
    cases objectState
    cases after
    simp_all only
  have finalRelated :
      ResidentAllocatorRel after finalStore frontierIndex := by
    rw [← finalStateEq]
    simpa [finalStore, writePayloadStore, headerStore, physicalAddress, u32,
      UInt32.ofNat_add, BoxedScalar.payload] using payloadRelatedRaw
  have physicalInBounds : physicalAddress.toNat + 40 ≤
      allocatedStore.mem.pages * wasmPageBytes := by
    have addressFits : address.value < UInt32.size := by
      simpa [wordModulus, UInt32.size] using address.isLt
    rw [show physicalAddress.toNat = address.value by
      exact UInt32.toNat_ofNat_of_lt' addressFits]
    rw [← rawRelated.toResidentMemoryRel.size_eq]
    exact rawPost.endInBounds
  have coreWP : Wasm.wp module (boxUInt64Program allocatorIndex)
      (fun completion => completion = .Return finalStore
        [.i32 physicalAddress]) store (boxUInt64Entry payload) env := by
    apply wp_boxUInt64Program allocatorRun physicalInBounds
    rfl
  refine ⟨finalStore, finalRelated, ?_, ?_⟩
  · exact allocateBoxedScalar_uint64_admission before after payload address valid
      related.frontierBase allocated
  · simpa [physicalAddress] using coreWP

/-- Lift the exact box core through the adapter's terminal suffix. -/
theorem UInt64Installation.wp_box_body
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {Q : Wasm.Assertion host}
    (installation : UInt64Installation sourceModule module)
    (noFallthrough : ∀ final finalLocals,
      ¬Q (.Fallthrough final finalLocals))
    (coreWP : Wasm.wp module
      (boxUInt64Program installation.allocatorIndex) Q store locals env) :
    Wasm.wp module installation.boxTarget.body Q store locals env := by
  rw [installation.box_body]
  exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
    noFallthrough coreWP

/-- Lift the exact unbox core through the adapter's terminal suffix. -/
theorem UInt64Installation.wp_unbox_body
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {Q : Wasm.Assertion host}
    (installation : UInt64Installation sourceModule module)
    (noFallthrough : ∀ final finalLocals,
      ¬Q (.Fallthrough final finalLocals))
    (coreWP : Wasm.wp module unboxUInt64Program Q store locals env) :
    Wasm.wp module installation.unboxTarget.body Q store locals env := by
  rw [installation.unbox_body]
  exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
    noFallthrough coreWP

/-- The installed production box call implements the complete heap-only W6
allocation contract, preserving arbitrary caller operand slack. -/
theorem UInt64Installation.terminatesWith_box_of_allocateBoxedScalar
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {before after : MemoryState}
    {store : Wasm.Store host} {payload : UInt64} {address : Word32}
    (installation : UInt64Installation sourceModule module)
    (tail : List Wasm.Value)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store installation.frontierIndex)
    (allocated : allocateBoxedScalar before (.uint64 payload) =
      .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore installation.frontierIndex ∧
      UInt64BoxAdmission after address payload ∧
      Wasm.TerminatesWith env module installation.boxIndex store
        ([.i64 payload] ++ tail)
        (fun final values => final = finalStore ∧
          values = .i32 (UInt32.ofNat address.value) :: tail) := by
  obtain ⟨finalStore, finalRelated, admitted, coreWP⟩ :=
    wp_boxUInt64Program_of_allocateBoxedScalar
      installation.allocatorAdapted installation.allocatorNotImport
      installation.allocatorInstalled memory32 valid related allocated
      strictEnd withinCap
  have bodyWP : Wasm.wp module installation.boxTarget.body
      (fun completion => completion = .Return finalStore
        [.i32 (UInt32.ofNat address.value)]) store
      (boxUInt64Entry payload) env := by
    apply installation.wp_box_body (by intros; simp)
    exact coreWP
  refine ⟨finalStore, finalRelated, admitted, ?_⟩
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at
    installation.boxNotImport installation.boxInstalled
  rw [installation.box_entry payload tail]
  apply Wasm.wp.conseq _ bodyWP
  intro completion completed
  subst completion
  obtain ⟨params, _locals, results⟩ := installation.box_signature
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
    params, results]

/-- Any installed exact-object alias whose source body adapts to the generic
heap-only core inherits the complete `UInt64` allocation refinement.  This is
the reusable semantic transport boundary: no allocator, heap, or scratch-slot
runtime argument is repeated here. -/
theorem UInt64ObjectInstallation.terminatesWith_box_of_allocateBoxedScalar_of_coreAdapted
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {before after : MemoryState}
    {store : Wasm.Store host} {payload : UInt64} {address : Word32}
    (generic : UInt64Installation sourceModule module)
    (installation : UInt64ObjectInstallation sourceModule module)
    (coreAdapted : FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64ObjectFunction []
      Fir.Wasm.Emit.ResidentScalarBox.boxUInt64ObjectFunction.body =
        .ok (boxUInt64Program generic.allocatorIndex))
    (tail : List Wasm.Value)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store generic.frontierIndex)
    (allocated : allocateBoxedScalar before (.uint64 payload) =
      .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore generic.frontierIndex ∧
      UInt64BoxAdmission after address payload ∧
      Wasm.TerminatesWith env module installation.index store
        ([.i64 payload] ++ tail)
        (fun final values => final = finalStore ∧
          values = .i32 (UInt32.ofNat address.value) :: tail) := by
  obtain ⟨finalStore, finalRelated, admitted, coreWP⟩ :=
    wp_boxUInt64Program_of_allocateBoxedScalar
      generic.allocatorAdapted generic.allocatorNotImport
      generic.allocatorInstalled memory32 valid related allocated
      strictEnd withinCap
  have bodyWP : Wasm.wp module installation.target.body
      (fun completion => completion = .Return finalStore
        [.i32 (UInt32.ofNat address.value)]) store
      (boxUInt64Entry payload) env := by
    rw [installation.body_of_instructions coreAdapted]
    exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
      (by intros; simp) coreWP
  refine ⟨finalStore, finalRelated, admitted, ?_⟩
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at
    installation.notImport installation.installed
  rw [installation.box_entry payload tail]
  apply Wasm.wp.conseq _ bodyWP
  intro completion completed
  subst completion
  obtain ⟨params, _locals, results⟩ := installation.signature
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
    params, results]

/-- The installed production unbox call round-trips one canonical W6 box
bit-for-bit and preserves the complete store and caller operand slack. -/
theorem UInt64Installation.terminatesWith_unbox
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {state : MemoryState}
    {store : Wasm.Store host} {address : Word32} {payload : UInt64}
    (installation : UInt64Installation sourceModule module)
    (tail : List Wasm.Value)
    (admitted : UInt64BoxAdmission state address payload)
    (related : ResidentMemoryRel state store.mem) :
    Wasm.TerminatesWith env module installation.unboxIndex store
      ([.i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values => final = store ∧ values = .i64 payload :: tail) := by
  have coreWP : Wasm.wp module unboxUInt64Program
      (fun completion => completion = .Return store [.i64 payload]) store
      (unboxUInt64Entry (UInt32.ofNat address.value)) env := by
    apply wp_unboxUInt64Program admitted related
    rfl
  have bodyWP : Wasm.wp module installation.unboxTarget.body
      (fun completion => completion = .Return store [.i64 payload]) store
      (unboxUInt64Entry (UInt32.ofNat address.value)) env := by
    apply installation.wp_unbox_body (by intros; simp)
    exact coreWP
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at
    installation.unboxNotImport installation.unboxInstalled
  rw [installation.unbox_entry (UInt32.ofNat address.value) tail]
  apply Wasm.wp.conseq _ bodyWP
  intro completion completed
  subst completion
  obtain ⟨params, _locals, results⟩ := installation.unbox_signature
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
    params, results]

/-- A body-level trap proof for the installed unbox helper is an exact
fuel-eventual statement about its public call. -/
theorem UInt64Installation.run_unbox_eq_trap_of_body_wp
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store final : Wasm.Store host}
    {message : String}
    (installation : UInt64Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value)
    (bodyWP : Wasm.wp module installation.unboxTarget.body
      (fun completion => completion = .Trap final message) store
      (unboxUInt64Entry object) env) :
    ∃ bound, ∀ fuel ≥ bound,
      Wasm.run fuel module installation.unboxIndex store
        ([.i32 object] ++ tail) env = .Trap final message := by
  unfold Wasm.wp at bodyWP
  obtain ⟨bound, bodyWP⟩ := bodyWP
  refine ⟨bound, ?_⟩
  intro fuel enoughFuel
  have trapped := bodyWP fuel enoughFuel
  rw [Wasm.run_eq installation.unboxNotImport]
  simp only [installation.unboxInstalled]
  rw [installation.unbox_entry object tail]
  cases execution : Wasm.exec fuel module store (unboxUInt64Entry object)
      installation.unboxTarget.body env <;> simp_all

/-- The installed unbox helper rejects every immediate/tagged physical word
without modifying the store. -/
theorem UInt64Installation.run_unbox_tagged_eq_trap
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    (installation : UInt64Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value)
    (tagged : (1 : UInt32) &&& object ≠ 0) :
    ∃ bound, ∀ fuel ≥ bound,
      Wasm.run fuel module installation.unboxIndex store
        ([.i32 object] ++ tail) env = .Trap store "unreachable" := by
  apply installation.run_unbox_eq_trap_of_body_wp object tail
  apply installation.wp_unbox_body (by intros; simp)
  exact wp_unboxUInt64Program_tagged tagged rfl

/-- The installed unbox helper likewise rejects the canonical promoted-tag
allocation instead of accepting it as a `UInt64` box. -/
theorem UInt64Installation.run_unbox_promoted_eq_trap
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {before after : MemoryState}
    {store : Wasm.Store host} {payload : UInt64} {address : Word32}
    (installation : UInt64Installation sourceModule module)
    (tail : List Wasm.Value)
    (valid : before.FrontierInvariant)
    (frontierBase : heapBase ≤ before.heapCursor)
    (allocated : allocatePromotedTag before payload = .ok (after, address))
    (related : ResidentMemoryRel after store.mem) :
    ∃ bound, ∀ fuel ≥ bound,
      Wasm.run fuel module installation.unboxIndex store
        ([.i32 (UInt32.ofNat address.value)] ++ tail) env =
          .Trap store "unreachable" := by
  apply installation.run_unbox_eq_trap_of_body_wp
    (UInt32.ofNat address.value) tail
  apply installation.wp_unbox_body (by intros; simp)
  exact wp_unboxUInt64Program_of_allocatePromotedTag valid frontierBase
    allocated related rfl

end ResidentScalarBox

end FirTalos.Concrete
