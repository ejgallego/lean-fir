import Fir.Wasm.ABI
import Fir.LeanIR.Runtime

namespace Fir.Wasm.Concrete

open Lean.Compiler

/-!
# W6 concrete wasm32/Lean64 data model

The concrete target uses standard wasm32 linear-memory addresses while
preserving the final-impure LCNF produced by this repository's 64-bit Lean
4.32 toolchain. Consequently object-like lanes and addresses are `i32`, but
`USize` remains `i64` and every pre-scalar constructor slot occupies eight
bytes. This makes an LCNF scalar address

`headerBytes + semanticSlotBytes * slotIndex + byteOffset`

agree with Lean 4.32's `sizeof(void*) * slotIndex + byteOffset` convention for
the captured 64-bit program, without pretending that source `USize` is a
wasm32 pointer.

The low bit of an object word distinguishes immediate tagged payloads from
heap addresses. A wasm32 word holds only a 31-bit immediate payload. Larger
semantic tagged naturals are represented by persistent heap naturals; the W6
refinement relation, rather than the source semantics, owns that
representation change.
-/

/-- Frozen concrete target configuration for W6. -/
structure TargetConfig where
  name : String
  pointerLane : ValueType
  pointerBits : Nat
  usizeLane : ValueType
  usizeBits : Nat
  semanticSlotBytes : Nat
  heapAlignment : Nat
  deriving Inhabited, BEq, Repr

def target : TargetConfig := {
  name := "wasm32-lean64"
  pointerLane := .i32
  pointerBits := 32
  usizeLane := .i64
  usizeBits := 64
  semanticSlotBytes := 8
  heapAlignment := 8 }

@[simp] theorem target_pointer_lane : target.pointerLane = .i32 := rfl

@[simp] theorem target_usize_lane : target.usizeLane = .i64 := rfl

@[simp] theorem target_usize_agrees_with_semantic_abi :
    target.usizeLane = AbiKind.usize.valueType := rfl

@[simp] theorem target_slot_covers_pointer :
    target.pointerBits / 8 ≤ target.semanticSlotBytes := by decide

@[simp] theorem target_slot_covers_usize :
    target.usizeBits / 8 = target.semanticSlotBytes := rfl

def wordModulus : Nat := 4294967296

def maxImmediatePayload : Nat := 2147483647

/-- Mathematical model of one concrete wasm32 word. The proof prevents silent
host-Nat wraparound in layout and refinement statements. -/
structure Word32 where
  value : Nat
  isLt : value < wordModulus
  deriving Repr

instance : BEq Word32 where
  beq left right := left.value == right.value

def Word32.zero : Word32 := ⟨0, by decide⟩

def Word32.ofNat? (value : Nat) : Option Word32 :=
  if h : value < wordModulus then some ⟨value, h⟩ else none

/-- Canonical wasm32 lane for one source `UInt8`. -/
def Word32.ofUInt8 (value : UInt8) : Word32 :=
  ⟨value.toNat, by
    have bound := value.toNat_lt
    simp [wordModulus] at bound ⊢
    omega⟩

/-- Canonical wasm32 lane for one source `UInt16`. -/
def Word32.ofUInt16 (value : UInt16) : Word32 :=
  ⟨value.toNat, by
    have bound := value.toNat_lt
    simp [wordModulus] at bound ⊢
    omega⟩

/-- Canonical wasm32 lane for one source `UInt32`. -/
def Word32.ofUInt32 (value : UInt32) : Word32 :=
  ⟨value.toNat, by simpa [wordModulus] using value.toNat_lt⟩

@[simp] theorem Word32.ofUInt8_value (value : UInt8) :
    (Word32.ofUInt8 value).value = value.toNat := rfl

@[simp] theorem Word32.ofUInt16_value (value : UInt16) :
    (Word32.ofUInt16 value).value = value.toNat := rfl

@[simp] theorem Word32.ofUInt32_value (value : UInt32) :
    (Word32.ofUInt32 value).value = value.toNat := rfl

inductive ObjectWordClass where
  | sentinel
  | immediate
  | heap
  | invalid
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Zero is reserved for erased values and empty reuse tokens. Valid heap
addresses are nonzero and eight-byte aligned; all odd words are immediates. -/
def Word32.classify (word : Word32) : ObjectWordClass :=
  if word.value = 0 then
    .sentinel
  else if word.value % 2 = 1 then
    .immediate
  else if word.value % target.heapAlignment = 0 then
    .heap
  else
    .invalid

def Word32.encodeImmediate (payload : Nat) (fits : payload ≤ maxImmediatePayload) : Word32 :=
  ⟨payload * 2 + 1, by
    unfold maxImmediatePayload at fits
    unfold wordModulus
    omega⟩

def Word32.encodeImmediate? (payload : Nat) : Option Word32 :=
  if fits : payload ≤ maxImmediatePayload then
    some (encodeImmediate payload fits)
  else
    none

def Word32.decodeImmediate? (word : Word32) : Option Nat :=
  if word.classify = .immediate then some (word.value / 2) else none

@[simp] theorem Word32.classify_encodeImmediate (payload : Nat)
    (fits : payload ≤ maxImmediatePayload) :
    (Word32.encodeImmediate payload fits).classify = .immediate := by
  simp [Word32.classify, Word32.encodeImmediate]

@[simp] theorem Word32.decode_encodeImmediate (payload : Nat)
    (fits : payload ≤ maxImmediatePayload) :
    (Word32.encodeImmediate payload fits).decodeImmediate? = some payload := by
  simp only [Word32.decodeImmediate?, Word32.classify_encodeImmediate, if_true]
  congr 1
  simp only [Word32.encodeImmediate]
  omega

theorem Word32.immediate_ne_zero (payload : Nat)
    (fits : payload ≤ maxImmediatePayload) :
    Word32.encodeImmediate payload fits ≠ Word32.zero := by
  intro equal
  have values := congrArg Word32.value equal
  simp [Word32.encodeImmediate, Word32.zero] at values

theorem Word32.immediate_not_heap (payload : Nat)
    (fits : payload ≤ maxImmediatePayload) :
    (Word32.encodeImmediate payload fits).classify ≠ .heap := by
  simp

/-- Stable tags stored in the first header word. These are deliberately not
Lean's native C runtime tags: W6 has a checked, self-describing memory format
that can report structured target faults. -/
inductive ObjectKind where
  | constructor
  | closure
  | boxed
  | string
  | natural
  | integer
  | byteArray
  | opaque
  | freed
  deriving Inhabited, BEq, Repr

def ObjectKind.code : ObjectKind → UInt32
  | .constructor => 1
  | .closure => 2
  | .boxed => 3
  | .string => 4
  | .natural => 5
  | .integer => 6
  | .byteArray => 7
  | .opaque => 8
  | .freed => 255

/-- Integer scalar kinds accepted by FIR's semantic boxing operation. The
codes are stored in `boxed` header `aux0`; floats stay outside this enum until
the shared FIR runtime has matching semantic scalar constructors. -/
inductive BoxedScalarKind where
  | uint8
  | uint16
  | uint32
  | uint64
  | usize
  deriving Inhabited, BEq, DecidableEq, Repr

def BoxedScalarKind.code : BoxedScalarKind → UInt32
  | .uint8 => 1
  | .uint16 => 2
  | .uint32 => 3
  | .uint64 => 4
  | .usize => 5

def BoxedScalarKind.ofCode? (code : UInt32) : Option BoxedScalarKind :=
  if code == BoxedScalarKind.uint8.code then some .uint8
  else if code == BoxedScalarKind.uint16.code then some .uint16
  else if code == BoxedScalarKind.uint32.code then some .uint32
  else if code == BoxedScalarKind.uint64.code then some .uint64
  else if code == BoxedScalarKind.usize.code then some .usize
  else none

def BoxedScalarKind.abiKind : BoxedScalarKind → AbiKind
  | .uint8 => .uint8
  | .uint16 => .uint16
  | .uint32 => .uint32
  | .uint64 => .uint64
  | .usize => .usize

/-- Number of meaningful low payload bytes in a canonical boxed slot. The
slot itself remains eight bytes so every semantic value slot has one target
extent under `wasm32-lean64`. -/
def BoxedScalarKind.payloadBytes : BoxedScalarKind → Nat
  | .uint8 | .uint16 | .uint32 => 4
  | .uint64 | .usize => 8

@[simp] theorem BoxedScalarKind.ofCode_code (kind : BoxedScalarKind) :
    BoxedScalarKind.ofCode? kind.code = some kind := by
  cases kind <;> decide

def headerBytes : Nat := 32

def headerKindOffset : Nat := 0
def headerFlagsOffset : Nat := 4
def headerRefCountOffset : Nat := 8
def headerAllocationBytesOffset : Nat := 12
def headerAux0Offset : Nat := 16
def headerAux1Offset : Nat := 20
def headerAux2Offset : Nat := 24
def headerAux3Offset : Nat := 28

def persistentFlag : UInt32 := 1
def liveFlag : UInt32 := 2

/-- Decoded common header. The four auxiliary words are interpreted by the
object kind; `allocationBytes` includes the header and final alignment. -/
structure Header where
  kind : ObjectKind
  persistent : Bool
  live : Bool
  refCount : UInt32
  allocationBytes : UInt32
  aux0 : UInt32 := 0
  aux1 : UInt32 := 0
  aux2 : UInt32 := 0
  aux3 : UInt32 := 0
  deriving Inhabited, BEq, Repr

/-- Canonical released-allocation header. The extent remains self-describing,
while all live payload metadata is erased behind the dedicated kind. -/
def Header.forRelease (header : Header) : Header := {
  header with
  kind := .freed
  persistent := false
  live := false
  refCount := 0
  aux0 := 0
  aux1 := 0
  aux2 := 0
  aux3 := 0 }

def align8 (bytes : Nat) : Nat := ((bytes + 7) / 8) * 8

@[simp] theorem align8_mod (bytes : Nat) : align8 bytes % 8 = 0 := by
  simp [align8]

theorem align8_ge (bytes : Nat) : bytes ≤ align8 bytes := by
  unfold align8
  omega

/-- Physical byte width of one value when stored in a closure capture slot or
boxed payload. Constructor scalar fields instead use their declared packed
width. -/
def concreteBytes : AbiKind → Nat
  | .object | .tagged | .tobject | .erased | .reuseToken
  | .uint8 | .uint16 | .uint32 | .float32 => 4
  | .uint64 | .usize | .float => 8

@[simp] theorem BoxedScalarKind.payloadBytes_eq_concreteBytes
    (kind : BoxedScalarKind) :
    kind.payloadBytes = concreteBytes kind.abiKind := by
  cases kind <;> rfl

theorem concreteBytes_le_slot (kind : AbiKind) :
    concreteBytes kind ≤ target.semanticSlotBytes := by
  cases kind <;> decide

/-- Packed scalar width used by LCNF `sproj`/`sset`. -/
def scalarBytes? : AbiKind → Option Nat
  | .uint8 => some 1
  | .uint16 => some 2
  | .uint32 | .float32 => some 4
  | .uint64 | .usize | .float => some 8
  | _ => none

/-- Concrete layout of a constructor object. Object and `USize` fields each
consume one eight-byte semantic slot. Object words occupy the low four bytes
of their slot; the high four bytes must be zero. Scalar bytes follow the slots
at the exact LCNF byte offsets. -/
structure ConstructorLayout where
  objectFields : Nat
  usizeFields : Nat
  scalarBytes : Nat
  objectFieldsOffset : Nat
  usizeFieldsOffset : Nat
  scalarFieldsOffset : Nat
  allocationBytes : Nat
  deriving Inhabited, BEq, Repr

def ConstructorLayout.ofInfo (info : LCNF.CtorInfo) : ConstructorLayout :=
  let objectFieldsOffset := headerBytes
  let usizeFieldsOffset :=
    headerBytes + target.semanticSlotBytes * info.size
  let scalarFieldsOffset :=
    headerBytes + target.semanticSlotBytes * (info.size + info.usize)
  { objectFields := info.size
    usizeFields := info.usize
    scalarBytes := info.ssize
    objectFieldsOffset
    usizeFieldsOffset
    scalarFieldsOffset
    allocationBytes := align8 (scalarFieldsOffset + info.ssize) }

def ConstructorLayout.objectFieldOffset? (layout : ConstructorLayout)
    (index : Nat) : Option Nat :=
  if index < layout.objectFields then
    some (layout.objectFieldsOffset + target.semanticSlotBytes * index)
  else
    none

def ConstructorLayout.usizeFieldOffset? (layout : ConstructorLayout)
    (index : Nat) : Option Nat :=
  if index < layout.usizeFields then
    some (layout.usizeFieldsOffset + target.semanticSlotBytes * index)
  else
    none

/-- Translate the two numeric operands carried by LCNF scalar operations.
`slotIndex` is normally `CtorInfo.size + CtorInfo.usize`; `byteOffset` is
relative to the packed scalar region. -/
def ConstructorLayout.scalarFieldOffset? (layout : ConstructorLayout)
    (slotIndex byteOffset : Nat) (kind : AbiKind) : Option Nat := do
  guard (slotIndex = layout.objectFields + layout.usizeFields)
  let width ← scalarBytes? kind
  guard (byteOffset + width ≤ layout.scalarBytes)
  return headerBytes + target.semanticSlotBytes * slotIndex + byteOffset

@[simp] theorem ConstructorLayout.ofInfo_object_offset (info : LCNF.CtorInfo) :
    (ConstructorLayout.ofInfo info).objectFieldsOffset = headerBytes := rfl

@[simp] theorem ConstructorLayout.ofInfo_usize_offset (info : LCNF.CtorInfo) :
    (ConstructorLayout.ofInfo info).usizeFieldsOffset =
      headerBytes + target.semanticSlotBytes * info.size := rfl

@[simp] theorem ConstructorLayout.ofInfo_scalar_offset (info : LCNF.CtorInfo) :
    (ConstructorLayout.ofInfo info).scalarFieldsOffset =
      headerBytes + target.semanticSlotBytes * (info.size + info.usize) := rfl

@[simp] theorem ConstructorLayout.ofInfo_allocation_aligned
    (info : LCNF.CtorInfo) :
    (ConstructorLayout.ofInfo info).allocationBytes % target.heapAlignment = 0 := by
  simp [ConstructorLayout.ofInfo, target]

/-- Captures use fixed eight-byte slots so the statically typed W5 trampoline
can project heterogeneous values without a second dynamic descriptor format. -/
structure ClosureLayout where
  captures : Array AbiKind
  capturesOffset : Nat
  allocationBytes : Nat
  deriving Inhabited, BEq

def ClosureLayout.ofCaptures (captures : Array AbiKind) : ClosureLayout := {
  captures
  capturesOffset := headerBytes
  allocationBytes := align8 (headerBytes + target.semanticSlotBytes * captures.size) }

def ClosureLayout.captureOffset? (layout : ClosureLayout) (index : Nat) : Option Nat :=
  if index < layout.captures.size then
    some (layout.capturesOffset + target.semanticSlotBytes * index)
  else
    none

@[simp] theorem ClosureLayout.ofCaptures_aligned (captures : Array AbiKind) :
    (ClosureLayout.ofCaptures captures).allocationBytes % target.heapAlignment = 0 := by
  simp [ClosureLayout.ofCaptures, target]

end Fir.Wasm.Concrete
