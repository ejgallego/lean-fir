import Fir.Wasm.Concrete.Refinement

namespace Fir.Wasm.Concrete

/-- Failures produced by checked concrete-memory operations. These remain
separate from source `RuntimeFault`s and will be embedded in the structured
target-failure boundary when concrete imports replace semantic hosts. -/
inductive MemoryError where
  | outOfBounds (address bytes memoryBytes : Nat)
  | addressSpaceExhausted (requestedEnd : Nat)
  | invalidObjectAddress (word : Word32)
  | unknownObjectKind (code : UInt32)
  | invalidAllocationSize (bytes : Nat)
  | malformedHeader (address allocationBytes : Nat)
  | deadObject (address : Word32)
  deriving BEq, Repr

abbrev LinearMemory := Array UInt8

def wasmPageBytes : Nat := 65536

def heapBase : Nat := 1024

namespace LinearMemory

def withPages (pages : Nat) : LinearMemory :=
  Array.replicate (pages * wasmPageBytes) 0

def readByte (memory : LinearMemory) (address : Nat) : Except MemoryError UInt8 :=
  match memory[address]? with
  | some byte => .ok byte
  | none => .error (.outOfBounds address 1 memory.size)

def writeByte (memory : LinearMemory) (address : Nat) (value : UInt8) :
    Except MemoryError LinearMemory :=
  if h : address < memory.size then
    .ok (memory.set address value h)
  else
    .error (.outOfBounds address 1 memory.size)

private def byte32 (value : UInt32) (shift : Nat) : UInt8 :=
  UInt8.ofNat ((value.toNat / (2 ^ shift)) % 256)

private def byte64 (value : UInt64) (shift : Nat) : UInt8 :=
  UInt8.ofNat ((value.toNat / (2 ^ shift)) % 256)

def readUInt32 (memory : LinearMemory) (address : Nat) : Except MemoryError UInt32 := do
  let b0 ← memory.readByte address
  let b1 ← memory.readByte (address + 1)
  let b2 ← memory.readByte (address + 2)
  let b3 ← memory.readByte (address + 3)
  return UInt32.ofNat <|
    b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216

def writeUInt32 (memory : LinearMemory) (address : Nat) (value : UInt32) :
    Except MemoryError LinearMemory := do
  let memory ← memory.writeByte address (byte32 value 0)
  let memory ← memory.writeByte (address + 1) (byte32 value 8)
  let memory ← memory.writeByte (address + 2) (byte32 value 16)
  memory.writeByte (address + 3) (byte32 value 24)

def readUInt64 (memory : LinearMemory) (address : Nat) : Except MemoryError UInt64 := do
  let b0 ← memory.readByte address
  let b1 ← memory.readByte (address + 1)
  let b2 ← memory.readByte (address + 2)
  let b3 ← memory.readByte (address + 3)
  let b4 ← memory.readByte (address + 4)
  let b5 ← memory.readByte (address + 5)
  let b6 ← memory.readByte (address + 6)
  let b7 ← memory.readByte (address + 7)
  return UInt64.ofNat <|
    b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
    b4.toNat * 4294967296 + b5.toNat * 1099511627776 +
    b6.toNat * 281474976710656 + b7.toNat * 72057594037927936

def writeUInt64 (memory : LinearMemory) (address : Nat) (value : UInt64) :
    Except MemoryError LinearMemory := do
  let memory ← memory.writeByte address (byte64 value 0)
  let memory ← memory.writeByte (address + 1) (byte64 value 8)
  let memory ← memory.writeByte (address + 2) (byte64 value 16)
  let memory ← memory.writeByte (address + 3) (byte64 value 24)
  let memory ← memory.writeByte (address + 4) (byte64 value 32)
  let memory ← memory.writeByte (address + 5) (byte64 value 40)
  let memory ← memory.writeByte (address + 6) (byte64 value 48)
  memory.writeByte (address + 7) (byte64 value 56)

def writeWord32 (memory : LinearMemory) (address : Nat) (value : Word32) :
    Except MemoryError LinearMemory :=
  memory.writeUInt32 address (UInt32.ofNat value.value)

def readWord32 (memory : LinearMemory) (address : Nat) : Except MemoryError Word32 := do
  let value ← memory.readUInt32 address
  let some word := Word32.ofNat? value.toNat |
    throw (.addressSpaceExhausted value.toNat)
  return word

def growToFit (memory : LinearMemory) (requiredBytes : Nat) : LinearMemory :=
  if requiredBytes ≤ memory.size then
    memory
  else
    let missing := requiredBytes - memory.size
    let pages := (missing + wasmPageBytes - 1) / wasmPageBytes
    memory ++ Array.replicate (pages * wasmPageBytes) 0

end LinearMemory

def ObjectKind.ofCode? (code : UInt32) : Option ObjectKind :=
  if code == ObjectKind.constructor.code then some .constructor
  else if code == ObjectKind.closure.code then some .closure
  else if code == ObjectKind.boxed.code then some .boxed
  else if code == ObjectKind.string.code then some .string
  else if code == ObjectKind.natural.code then some .natural
  else if code == ObjectKind.integer.code then some .integer
  else if code == ObjectKind.byteArray.code then some .byteArray
  else if code == ObjectKind.opaque.code then some .opaque
  else if code == ObjectKind.freed.code then some .freed
  else none

def Header.flags (header : Header) : UInt32 :=
  UInt32.ofNat ((if header.persistent then 1 else 0) + (if header.live then 2 else 0))

def Header.write (memory : LinearMemory) (address : Word32) (header : Header) :
    Except MemoryError LinearMemory := do
  let base := address.value
  let memory ← memory.writeUInt32 (base + headerKindOffset) header.kind.code
  let memory ← memory.writeUInt32 (base + headerFlagsOffset) header.flags
  let memory ← memory.writeUInt32 (base + headerRefCountOffset) header.refCount
  let memory ← memory.writeUInt32 (base + headerAllocationBytesOffset) header.allocationBytes
  let memory ← memory.writeUInt32 (base + headerAux0Offset) header.aux0
  let memory ← memory.writeUInt32 (base + headerAux1Offset) header.aux1
  let memory ← memory.writeUInt32 (base + headerAux2Offset) header.aux2
  memory.writeUInt32 (base + headerAux3Offset) header.aux3

def Header.read (memory : LinearMemory) (address : Word32) : Except MemoryError Header := do
  let base := address.value
  let kindCode ← memory.readUInt32 (base + headerKindOffset)
  let some kind := ObjectKind.ofCode? kindCode | throw (.unknownObjectKind kindCode)
  let flags ← memory.readUInt32 (base + headerFlagsOffset)
  let refCount ← memory.readUInt32 (base + headerRefCountOffset)
  let allocationBytes ← memory.readUInt32 (base + headerAllocationBytesOffset)
  let aux0 ← memory.readUInt32 (base + headerAux0Offset)
  let aux1 ← memory.readUInt32 (base + headerAux1Offset)
  let aux2 ← memory.readUInt32 (base + headerAux2Offset)
  let aux3 ← memory.readUInt32 (base + headerAux3Offset)
  return {
    kind
    persistent := flags.toNat % 2 = 1
    live := (flags.toNat / 2) % 2 = 1
    refCount
    allocationBytes
    aux0
    aux1
    aux2
    aux3 }

/-- Concrete state owned by the linear-memory runtime. World, trace, globals,
and structured faults are added in their W6 slices; allocation itself depends
only on bytes and the monotone heap cursor. -/
structure MemoryState where
  memory : LinearMemory := LinearMemory.withPages 1
  heapCursor : Nat := heapBase
  deriving Inhabited

def MemoryState.initial : MemoryState := {}

def MemoryState.allocate (state : MemoryState) (requestedBytes : Nat) :
    Except MemoryError (MemoryState × Word32) := do
  if requestedBytes < headerBytes then
    throw (.invalidAllocationSize requestedBytes)
  let bytes := align8 requestedBytes
  let addressValue := align8 state.heapCursor
  let requestedEnd := addressValue + bytes
  if wordModulus < requestedEnd then
    throw (.addressSpaceExhausted requestedEnd)
  let some address := Word32.ofNat? addressValue |
    throw (.addressSpaceExhausted addressValue)
  unless address.classify = .heap do
    throw (.invalidObjectAddress address)
  let memory := state.memory.growToFit requestedEnd
  return ({ memory, heapCursor := requestedEnd }, address)

def MemoryState.allocateObject (state : MemoryState) (kind : ObjectKind)
    (payloadBytes : Nat) (persistent := false) (aux0 : UInt32 := 0)
    (aux1 : UInt32 := 0) (aux2 : UInt32 := 0) (aux3 : UInt32 := 0) :
    Except MemoryError (MemoryState × Word32) := do
  let allocationBytes := align8 (headerBytes + payloadBytes)
  let (state, address) ← state.allocate allocationBytes
  let header : Header := {
    kind
    persistent
    live := true
    refCount := if persistent then 0 else 1
    allocationBytes := UInt32.ofNat allocationBytes
    aux0
    aux1
    aux2
    aux3 }
  let memory ← header.write state.memory address
  return ({ state with memory }, address)

def MemoryState.readLiveHeader (state : MemoryState) (address : Word32) :
    Except MemoryError Header := do
  unless address.classify = .heap do
    throw (.invalidObjectAddress address)
  let header ← Header.read state.memory address
  unless header.live do
    throw (.deadObject address)
  let bytes := header.allocationBytes.toNat
  unless headerBytes ≤ bytes && bytes % target.heapAlignment = 0 &&
      address.value + bytes ≤ state.memory.size do
    throw (.malformedHeader address.value bytes)
  return header

end Fir.Wasm.Concrete
