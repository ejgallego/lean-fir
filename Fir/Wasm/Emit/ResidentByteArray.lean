import Fir.Wasm.Emit.ResidentArray
import Fir.Wasm.Emit.ResidentScalarBox

namespace Fir.Wasm.Emit.ResidentByteArray

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean
open Lean.Compiler

/-!
# Wasm-resident packed ByteArrays

The representation is a module-private packed scalar array, not a boxed
`Array UInt8`: a checked FIR header is followed immediately by `capacity` raw
bytes.  The first generation slice implements the exact generic operations
needed by stored DEFLATE.  Every operation runs in Wasm and allocates from the
instance-lifetime arena; no host callback sees a Lean object address.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | missingNumericHelper (name : Name)
  | missingScalarHelper (name : Name)
  | missingOwnershipHelper (name : Name)
  | scalarHelperLink (error : ResidentScalarBox.LinkError)
  | reservedDeclaration (name : Name)
  | missingExternal (name : Name)
  | incompatibleExternal (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

/-- ASCII `BYTE`, stored in `byteArray.aux0`. -/
def byteArrayMarker : UInt32 := ResidentContainerLayout.byteArrayMarker

def validateName : Name := `fir_byte_array_validate
def expectedAllocationName : Name := `fir_byte_array_expected_allocation
def allocateName : Name := `fir_byte_array_allocate
def retypeObjectName : Name := `fir_byte_array_retype_object
def decodeNatural32Name : Name := `fir_byte_array_decode_natural32
def copyBytesName : Name := `fir_byte_array_copy_bytes
def releaseConsumedName : Name := `fir_byte_array_release_consumed

def internalHelperNames : Array Name := #[
  validateName,
  expectedAllocationName,
  allocateName,
  retypeObjectName,
  decodeNatural32Name,
  copyBytesName,
  releaseConsumedName]

def externalDeclarations : Array Name := #[
  `ByteArray.copySlice,
  `ByteArray.size,
  `ByteArray.mk,
  `ByteArray.emptyWithCapacity]

def externalName (declaration : Name) : Name :=
  Name.mkSimple s!"fir_ext_{declaration.toString.replace "." "_"}"

def externalHelperNames : Array Name := externalDeclarations.map externalName
def helperNames : Array Name := internalHelperNames ++ externalHelperNames

private def selectedInternalHelperNames (declarations : Array Name) : Array Name :=
  let needsValidation :=
    declarations.contains `ByteArray.size ||
      declarations.contains `ByteArray.copySlice
  let needsAllocation :=
    declarations.contains `ByteArray.mk ||
      declarations.contains `ByteArray.emptyWithCapacity ||
      declarations.contains `ByteArray.copySlice
  let names := if needsValidation then #[validateName] else #[]
  let names := if needsValidation || needsAllocation then
    names.push expectedAllocationName else names
  let names := if needsAllocation then names.push allocateName else names
  let names := if needsAllocation then names.push retypeObjectName else names
  let names := if declarations.contains `ByteArray.emptyWithCapacity ||
      declarations.contains `ByteArray.copySlice then
    names.push decodeNatural32Name else names
  if declarations.contains `ByteArray.copySlice then
    (names.push copyBytesName).push releaseConsumedName else names

private def sourceParam : FVarId := ⟨`source⟩
private def sourceOffsetParam : FVarId := ⟨`sourceOffset⟩
private def destinationParam : FVarId := ⟨`destination⟩
private def destinationOffsetParam : FVarId := ⟨`destinationOffset⟩
private def lengthParam : FVarId := ⟨`length⟩
private def exactParam : FVarId := ⟨`exact⟩
private def capacityParam : FVarId := ⟨`capacity⟩
private def sizeParam : FVarId := ⟨`size⟩
private def arrayParam : FVarId := ⟨`array⟩
private def rawParam : FVarId := ⟨`raw⟩
private def countParam : FVarId := ⟨`count⟩

private def addressLocal : FVarId := ⟨`address⟩
private def rawLocal : FVarId := ⟨`rawValue⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def arrayTobjectLocal : FVarId := ⟨`arrayTobject⟩
private def taggedResultLocal : FVarId := ⟨`taggedResult⟩
private def allocationLocal : FVarId := ⟨`allocationBytes⟩
private def unitsLocal : FVarId := ⟨`allocationUnits⟩
private def sizeLocal : FVarId := ⟨`sizeValue⟩
private def capacityLocal : FVarId := ⟨`capacityValue⟩
private def sourceSizeLocal : FVarId := ⟨`sourceSize⟩
private def destinationSizeLocal : FVarId := ⟨`destinationSize⟩
private def sourceOffsetLocal : FVarId := ⟨`sourceOffsetValue⟩
private def destinationOffsetLocal : FVarId := ⟨`destinationOffsetValue⟩
private def requestedLengthLocal : FVarId := ⟨`requestedLength⟩
private def copyLengthLocal : FVarId := ⟨`copyLength⟩
private def availableLocal : FVarId := ⟨`available⟩
private def endLocal : FVarId := ⟨`endOffset⟩
private def newSizeLocal : FVarId := ⟨`newSize⟩
private def newCapacityLocal : FVarId := ⟨`newCapacity⟩
private def sourceCursorLocal : FVarId := ⟨`sourceCursor⟩
private def destinationCursorLocal : FVarId := ⟨`destinationCursor⟩
private def elementLocal : FVarId := ⟨`element⟩
private def flagsLocal : FVarId := ⟨`flags⟩
private def refCountLocal : FVarId := ⟨`refCount⟩
private def reuseLocal : FVarId := ⟨`reuseDestination⟩

private def copyLoopLabel : FVarId := ⟨`copyLoop⟩
private def packLoopLabel : FVarId := ⟨`packLoop⟩

private def scalarPrerequisiteName : Name := `fir_byte_array_scalar_prerequisite

private def equalsConst (kind : AbiKind) (value : UInt32) :
    List Instruction :=
  [.i32Const kind value, .i32Eq]

private def trapWhenTrue (condition : List Instruction) : List Instruction :=
  condition ++ [.ifElse [.unreachable] []]

private def trapUnlessTrue (condition : List Instruction) : List Instruction :=
  trapWhenTrue (condition ++ equalsConst .uint32 0)

private def load32 (object : FVarId) (offset : Nat) : List Instruction :=
  [.localGet object, .i32Load .uint32 (u32 offset)]

private def requireHeapAddress (object : FVarId) : List Instruction :=
  trapWhenTrue [
    .localGet object,
    .i32Const .uint32 (u32 heapBase),
    .i32LtU] ++
  trapWhenTrue [
    .localGet object,
    .i32Const .uint32 (u32 (target.heapAlignment - 1)),
    .i32And]

private def retypeRaw (result : AbiKind) (resultLocal : FVarId) :
    List Instruction := [
  .localSet rawLocal,
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet rawLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load result 0,
  .localSet resultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet resultLocal,
  .ret]

def expectedAllocationFunction : Function := {
  name := expectedAllocationName
  params := #[(capacityParam, .uint32)]
  results := #[.uint32]
  locals := #[(allocationLocal, .uint32), (unitsLocal, .uint32)]
  body := [
    .localGet capacityParam,
    .i32Const .uint32 (u32 (headerBytes + target.heapAlignment - 1)),
    .i32Add,
    .localSet allocationLocal] ++
    trapWhenTrue [
      .localGet allocationLocal,
      .localGet capacityParam,
      .i32LtU] ++ [
    .localGet allocationLocal,
    .i32Const .uint32 3,
    .i32ShrU,
    .localSet unitsLocal,
    .localGet unitsLocal,
    .localGet unitsLocal,
    .i32Add,
    .localSet allocationLocal,
    .localGet allocationLocal,
    .localGet allocationLocal,
    .i32Add,
    .localSet allocationLocal,
    .localGet allocationLocal,
    .localGet allocationLocal,
    .i32Add,
    .ret] }

def validateFunction : Function := {
  name := validateName
  params := #[(sourceParam, .object)]
  results := #[]
  locals := #[(sizeLocal, .uint32), (capacityLocal, .uint32),
    (flagsLocal, .uint32), (refCountLocal, .uint32)]
  body := requireHeapAddress sourceParam ++
    trapUnlessTrue (load32 sourceParam headerKindOffset ++
      equalsConst .uint32 ObjectKind.byteArray.code) ++
    load32 sourceParam headerFlagsOffset ++ [.localSet flagsLocal] ++
    ([.localGet flagsLocal] ++ equalsConst .uint32 liveFlag ++
      [.ifElse []
        (trapUnlessTrue ([.localGet flagsLocal] ++
          equalsConst .uint32 (persistentFlag + liveFlag)))]) ++
    load32 sourceParam headerRefCountOffset ++ [.localSet refCountLocal] ++
    ([.localGet flagsLocal] ++ equalsConst .uint32 liveFlag ++
      [.ifElse
        (trapWhenTrue ([.localGet refCountLocal] ++
          equalsConst .uint32 0))
        (trapWhenTrue [.localGet refCountLocal])]) ++
    trapUnlessTrue (load32 sourceParam headerAux0Offset ++
      equalsConst .uint32 byteArrayMarker) ++
    trapWhenTrue (load32 sourceParam headerAux3Offset) ++ [
      .localGet sourceParam,
      .i32Load .uint32 (u32 headerAux1Offset),
      .localSet sizeLocal,
      .localGet sourceParam,
      .i32Load .uint32 (u32 headerAux2Offset),
      .localSet capacityLocal] ++
    trapWhenTrue [
      .localGet capacityLocal,
      .localGet sizeLocal,
      .i32LtU] ++
    trapUnlessTrue (
      load32 sourceParam headerAllocationBytesOffset ++ [
        .localGet capacityLocal,
        .call (.declaration expectedAllocationName),
        .i32Eq]) ++ [.ret] }

def allocateFunction : Function := {
  name := allocateName
  params := #[(sizeParam, .uint32), (capacityParam, .uint32)]
  results := #[.uint32]
  locals := #[(addressLocal, .uint32), (allocationLocal, .uint32)]
  body := trapWhenTrue [
    .localGet capacityParam,
    .localGet sizeParam,
    .i32LtU] ++ [
    .localGet capacityParam,
    .call (.declaration expectedAllocationName),
    .localSet allocationLocal,
    .localGet allocationLocal,
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal,
    .localGet addressLocal,
    .i32Const .uint32 ObjectKind.byteArray.code,
    .i32Store .uint32 (u32 headerKindOffset),
    .localGet addressLocal,
    .i32Const .uint32 liveFlag,
    .i32Store .uint32 (u32 headerFlagsOffset),
    .localGet addressLocal,
    .i32Const .uint32 1,
    .i32Store .uint32 (u32 headerRefCountOffset),
    .localGet addressLocal,
    .localGet allocationLocal,
    .i32Store .uint32 (u32 headerAllocationBytesOffset),
    .localGet addressLocal,
    .i32Const .uint32 byteArrayMarker,
    .i32Store .uint32 (u32 headerAux0Offset),
    .localGet addressLocal,
    .localGet sizeParam,
    .i32Store .uint32 (u32 headerAux1Offset),
    .localGet addressLocal,
    .localGet capacityParam,
    .i32Store .uint32 (u32 headerAux2Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux3Offset),
    .localGet addressLocal,
    .ret] }

def retypeObjectFunction : Function := {
  name := retypeObjectName
  params := #[(rawParam, .uint32)]
  results := #[.object]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (objectResultLocal, .object)]
  body := [.localGet rawParam] ++ retypeRaw .object objectResultLocal }

def decodeNatural32Function : Function := {
  name := decodeNatural32Name
  params := #[(rawParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet rawParam,
    .call (.declaration ResidentNumeric.validateNaturalName),
    .localGet rawParam,
    .call (.declaration ResidentNumeric.naturalHighName),
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse [] [.unreachable],
    .localGet rawParam,
    .call (.declaration ResidentNumeric.naturalLowName),
    .ret] }

def copyBytesFunction : Function := {
  name := copyBytesName
  params := #[(destinationParam, .uint32), (sourceParam, .uint32),
    (countParam, .uint32)]
  results := #[]
  locals := #[]
  body := [
    .loop copyLoopLabel [
      .localGet countParam,
      .i32Const .uint32 0,
      .i32Eq,
      .ifElse [.ret] [],
      .localGet destinationParam,
      .localGet sourceParam,
      .i32Load8U .uint32 0,
      .i32Store8 .uint32 0,
      .localGet destinationParam,
      .i32Const .uint32 1,
      .i32Add,
      .localSet destinationParam,
      .localGet sourceParam,
      .i32Const .uint32 1,
      .i32Add,
      .localSet sourceParam,
      .localGet countParam,
      .i32Const .uint32 1,
      .i32Sub,
      .localSet countParam,
      .br copyLoopLabel]] }

/-- Consume one ByteArray reference after copying it to a fresh destination. -/
def releaseConsumedFunction : Function := {
  name := releaseConsumedName
  params := #[(destinationParam, .object)]
  results := #[]
  locals := #[(addressLocal, .uint32), (flagsLocal, .uint32),
    (refCountLocal, .uint32)]
  body := [
    .localGet destinationParam,
    .call (.declaration validateName),
    .localGet destinationParam,
    .i32Const .uint32 0,
    .i32Add,
    .localSet addressLocal,
    .localGet addressLocal,
    .i32Load .uint32 (u32 headerFlagsOffset),
    .localSet flagsLocal,
    .localGet flagsLocal,
    .i32Const .uint32 persistentFlag,
    .i32And] ++ equalsConst .uint32 persistentFlag ++ [
    .ifElse [.ret] [],
    .localGet addressLocal,
    .i32Load .uint32 (u32 headerRefCountOffset),
    .localSet refCountLocal] ++
    trapWhenTrue ([.localGet refCountLocal] ++ equalsConst .uint32 0) ++ [
    .i32Const .uint32 1,
    .localGet refCountLocal,
    .i32LtU,
    .ifElse [
      .localGet addressLocal,
      .localGet refCountLocal,
      .i32Const .uint32 1,
      .i32Sub,
      .i32Store .uint32 (u32 headerRefCountOffset),
      .ret] [],
    .localGet addressLocal,
    .i32Const .uint32 ObjectKind.freed.code,
    .i32Store .uint32 (u32 headerKindOffset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerFlagsOffset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerRefCountOffset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux0Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux1Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux2Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux3Offset),
    .ret] }

def sizeFunction : Function := {
  name := externalName `ByteArray.size
  params := #[(sourceParam, .object)]
  results := #[.tagged]
  locals := #[(sizeLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (taggedResultLocal, .tagged)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName),
    .localGet sourceParam,
    .i32Load .uint32 (u32 headerAux1Offset),
    .localSet sizeLocal] ++
    trapUnlessTrue [
      .localGet sizeLocal,
      .i32Const .uint32 0x80000000,
      .i32LtU] ++ [
    .localGet sizeLocal,
    .localGet sizeLocal,
    .i32Add,
    .i32Const .uint32 1,
    .i32Add] ++ retypeRaw .tagged taggedResultLocal }

def emptyWithCapacityFunction : Function := {
  name := externalName `ByteArray.emptyWithCapacity
  params := #[(capacityParam, .tobject)]
  results := #[.object]
  locals := #[(capacityLocal, .uint32), (addressLocal, .uint32),
    (rawLocal, .uint32), (savedScratchLocal, .uint32),
    (objectResultLocal, .object)]
  body := [
    .localGet capacityParam,
    .call (.declaration decodeNatural32Name),
    .localSet capacityLocal,
    .i32Const .uint32 0,
    .localGet capacityLocal,
    .call (.declaration allocateName),
    .call (.declaration retypeObjectName),
    .ret] }

private def requireArray : List Instruction :=
  requireHeapAddress arrayParam ++
  trapUnlessTrue (load32 arrayParam headerKindOffset ++
    equalsConst .uint32 ObjectKind.opaque.code) ++
  (load32 arrayParam headerFlagsOffset ++ equalsConst .uint32 liveFlag ++
    [.ifElse
      (trapWhenTrue (load32 arrayParam headerRefCountOffset ++
        equalsConst .uint32 0))
      (trapUnlessTrue (load32 arrayParam headerFlagsOffset ++
          equalsConst .uint32 (persistentFlag + liveFlag)) ++
        trapWhenTrue (load32 arrayParam headerRefCountOffset))]) ++
  trapUnlessTrue (load32 arrayParam headerAux0Offset ++
    equalsConst .uint32 ResidentArray.arrayMarker) ++
  trapWhenTrue (load32 arrayParam headerAux3Offset) ++
  trapWhenTrue (load32 arrayParam headerAux2Offset ++
    load32 arrayParam headerAux1Offset ++ [.i32LtU])

private def captureArrayTobject : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet arrayParam,
  .i32Store .object 0,
  .i32Const .uint32 0,
  .i32Load .tobject 0,
  .localSet arrayTobjectLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0]

def mkFunction : Function := {
  name := externalName `ByteArray.mk
  params := #[(arrayParam, .object)]
  results := #[.object]
  locals := #[(addressLocal, .uint32), (sizeLocal, .uint32),
    (sourceCursorLocal, .uint32), (destinationCursorLocal, .uint32),
    (countParam, .uint32), (elementLocal, .tobject),
    (rawLocal, .uint32), (savedScratchLocal, .uint32),
    (objectResultLocal, .object), (arrayTobjectLocal, .tobject)]
  body := requireArray ++ captureArrayTobject ++ [
    .localGet arrayParam,
    .i32Load .uint32 (u32 headerAux1Offset),
    .localSet sizeLocal,
    .localGet sizeLocal,
    .localGet sizeLocal,
    .call (.declaration allocateName),
    .localSet addressLocal,
    .localGet arrayParam,
    .i32Const .uint32 (u32 headerBytes),
    .i32Add,
    .localSet sourceCursorLocal,
    .localGet addressLocal,
    .i32Const .uint32 (u32 headerBytes),
    .i32Add,
    .localSet destinationCursorLocal,
    .i32Const .uint32 0,
    .localSet countParam,
    .loop packLoopLabel [
      .localGet countParam,
      .localGet sizeLocal,
      .i32LtU,
      .ifElse [
        .localGet sourceCursorLocal,
        .i32Load .tobject 0,
        .localSet elementLocal,
        .localGet destinationCursorLocal,
        .localGet elementLocal,
        .call (.declaration ResidentScalarBox.unboxUInt8Name),
        .i32Store8 .uint8 0,
        .localGet sourceCursorLocal,
        .i32Const .uint32 (u32 target.semanticSlotBytes),
        .i32Add,
        .localSet sourceCursorLocal,
        .localGet destinationCursorLocal,
        .i32Const .uint32 1,
        .i32Add,
        .localSet destinationCursorLocal,
        .localGet countParam,
        .i32Const .uint32 1,
        .i32Add,
        .localSet countParam,
        .br packLoopLabel] []],
    .localGet arrayTobjectLocal,
    .i32Const .uint32 1,
    .call (.declaration ResidentRelease.decrementOnceName),
    .localGet addressLocal,
    .call (.declaration retypeObjectName),
    .ret] }

private def selectReusableDestination : List Instruction := [
  .localGet capacityLocal,
  .localGet newSizeLocal,
  .i32LtU,
  .ifElse [] (
    [.localGet destinationParam,
      .i32Load .uint32 (u32 headerFlagsOffset)] ++
    equalsConst .uint32 liveFlag ++ [
      .ifElse (
        [.localGet destinationParam,
          .i32Load .uint32 (u32 headerRefCountOffset)] ++
        equalsConst .uint32 1 ++ [
          .ifElse [
            .i32Const .uint32 1,
            .localSet reuseLocal] []]) []])]

def copySliceFunction : Function := {
  name := externalName `ByteArray.copySlice
  params := #[(sourceParam, .object), (sourceOffsetParam, .tobject),
    (destinationParam, .object), (destinationOffsetParam, .tobject),
    (lengthParam, .tobject), (exactParam, .uint8)]
  results := #[.object]
  locals := #[(addressLocal, .uint32), (sourceSizeLocal, .uint32),
    (destinationSizeLocal, .uint32), (capacityLocal, .uint32),
    (sourceOffsetLocal, .uint32), (destinationOffsetLocal, .uint32),
    (requestedLengthLocal, .uint32), (copyLengthLocal, .uint32),
    (availableLocal, .uint32), (endLocal, .uint32),
    (newSizeLocal, .uint32), (newCapacityLocal, .uint32),
    (reuseLocal, .uint32),
    (rawLocal, .uint32), (savedScratchLocal, .uint32),
    (objectResultLocal, .object)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName),
    .localGet destinationParam,
    .call (.declaration validateName),
    .localGet sourceParam,
    .i32Load .uint32 (u32 headerAux1Offset),
    .localSet sourceSizeLocal,
    .localGet destinationParam,
    .i32Load .uint32 (u32 headerAux1Offset),
    .localSet destinationSizeLocal,
    .localGet destinationParam,
    .i32Load .uint32 (u32 headerAux2Offset),
    .localSet capacityLocal,
    .localGet sourceOffsetParam,
    .call (.declaration decodeNatural32Name),
    .localSet sourceOffsetLocal,
    .localGet sourceSizeLocal,
    .localGet sourceOffsetLocal,
    .i32LtU,
    .ifElse [.localGet destinationParam, .ret] [],
    .localGet lengthParam,
    .call (.declaration decodeNatural32Name),
    .localSet requestedLengthLocal,
    .localGet destinationOffsetParam,
    .call (.declaration decodeNatural32Name),
    .localSet destinationOffsetLocal,
    .localGet sourceSizeLocal,
    .localGet sourceOffsetLocal,
    .i32Sub,
    .localSet availableLocal,
    .localGet availableLocal,
    .localGet requestedLengthLocal,
    .i32LtU,
    .ifElse
      [.localGet availableLocal, .localSet copyLengthLocal]
      [.localGet requestedLengthLocal, .localSet copyLengthLocal],
    .localGet destinationSizeLocal,
    .localGet destinationOffsetLocal,
    .i32LtU,
    .ifElse [.localGet destinationSizeLocal, .localSet destinationOffsetLocal] [],
    .localGet destinationOffsetLocal,
    .localGet copyLengthLocal,
    .i32Add,
    .localSet endLocal] ++
    trapWhenTrue [
      .localGet endLocal,
      .localGet destinationOffsetLocal,
      .i32LtU] ++ [
    .localGet destinationSizeLocal,
    .localSet newSizeLocal,
    .localGet destinationSizeLocal,
    .localGet endLocal,
    .i32LtU,
    .ifElse [.localGet endLocal, .localSet newSizeLocal] [],
    .localGet capacityLocal,
    .localSet newCapacityLocal,
    .localGet capacityLocal,
    .localGet newSizeLocal,
    .i32LtU,
    .ifElse [
      .localGet exactParam,
      .i32Const .uint8 0,
      .i32Eq,
      .ifElse [
        .localGet newSizeLocal,
        .localGet newSizeLocal,
        .i32Add,
        .localSet newCapacityLocal] [
        .localGet newSizeLocal,
        .localSet newCapacityLocal]] []] ++
    trapWhenTrue [
      .localGet newCapacityLocal,
      .localGet newSizeLocal,
      .i32LtU] ++ [
    .i32Const .uint32 0,
    .localSet reuseLocal] ++
    selectReusableDestination ++ [
    .localGet reuseLocal,
    .ifElse [
      .localGet destinationParam,
      .i32Const .uint32 0,
      .i32Add,
      .localGet newSizeLocal,
      .i32Store .uint32 (u32 headerAux1Offset),
      .localGet destinationParam,
      .i32Const .uint32 (u32 headerBytes),
      .i32Add,
      .localGet destinationOffsetLocal,
      .i32Add,
      .localGet sourceParam,
      .i32Const .uint32 (u32 headerBytes),
      .i32Add,
      .localGet sourceOffsetLocal,
      .i32Add,
      .localGet copyLengthLocal,
      .call (.declaration copyBytesName),
      .localGet destinationParam,
      .ret] [
      .localGet newSizeLocal,
      .localGet newCapacityLocal,
      .call (.declaration allocateName),
      .localSet addressLocal,
      .localGet addressLocal,
      .i32Const .uint32 (u32 headerBytes),
      .i32Add,
      .localGet destinationParam,
      .i32Const .uint32 (u32 headerBytes),
      .i32Add,
      .localGet destinationSizeLocal,
      .call (.declaration copyBytesName),
      .localGet addressLocal,
      .i32Const .uint32 (u32 headerBytes),
      .i32Add,
      .localGet destinationOffsetLocal,
      .i32Add,
      .localGet sourceParam,
      .i32Const .uint32 (u32 headerBytes),
      .i32Add,
      .localGet sourceOffsetLocal,
      .i32Add,
      .localGet copyLengthLocal,
      .call (.declaration copyBytesName),
      .localGet destinationParam,
      .call (.declaration releaseConsumedName),
      .localGet addressLocal,
      .call (.declaration retypeObjectName),
      .ret]] }

def functions : Array Function := #[
  validateFunction,
  expectedAllocationFunction,
  allocateFunction,
  retypeObjectFunction,
  decodeNatural32Function,
  copyBytesFunction,
  releaseConsumedFunction,
  copySliceFunction,
  sizeFunction,
  mkFunction,
  emptyWithCapacityFunction]

private def expectedSignature? (declaration : Name) : Option Signature :=
  if declaration == `ByteArray.copySlice then
    some {
      params := #[.object, .tobject, .object, .tobject, .tobject, .uint8]
      results := #[.object] }
  else if declaration == `ByteArray.size then
    some { params := #[.object], results := #[.tagged] }
  else if declaration == `ByteArray.mk then
    some { params := #[.object], results := #[.object] }
  else if declaration == `ByteArray.emptyWithCapacity then
    some { params := #[.tobject], results := #[.object] }
  else none

private partial def rewriteInstruction (declarations : Array Name) :
    Instruction → Instruction
  | .call (.declaration declaration) =>
      if declarations.contains declaration then
        .call (.declaration (externalName declaration))
      else .call (.declaration declaration)
  | .block label body => .block label (body.map (rewriteInstruction declarations))
  | .loop label body => .loop label (body.map (rewriteInstruction declarations))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteInstruction declarations))
        (elseBody.map (rewriteInstruction declarations))
  | instruction => instruction

private def internalizeSelected (module : Module) (declarations : Array Name) :
    Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  if declarations.contains `ByteArray.emptyWithCapacity ||
      declarations.contains `ByteArray.copySlice then
    for name in #[ResidentNumeric.validateNaturalName,
        ResidentNumeric.naturalLowName, ResidentNumeric.naturalHighName] do
      unless module.functions.any (·.name == name) do
        throw (.missingNumericHelper name)
  if declarations.contains `ByteArray.mk then
    unless module.functions.any (·.name == ResidentScalarBox.unboxUInt8Name) do
      throw (.missingScalarHelper ResidentScalarBox.unboxUInt8Name)
    unless module.functions.any (·.name == ResidentRelease.decrementOnceName) do
      throw (.missingOwnershipHelper ResidentRelease.decrementOnceName)
  let selectedExternalHelperNames := declarations.map externalName
  let selectedHelperNames :=
    selectedInternalHelperNames declarations ++ selectedExternalHelperNames
  for name in selectedHelperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) || module.exports.contains name then
      throw (.reservedDeclaration name)
  for declaration in declarations do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.missingExternal declaration)
    let some signature := expectedSignature? declaration |
      throw (.incompatibleExternal declaration)
    unless imports[0]!.signature == signature do
      throw (.incompatibleExternal declaration)
  let linkedFunctions := module.functions.map fun function =>
    { function with body := function.body.map (rewriteInstruction declarations) }
  let linkedFunctions := linkedFunctions ++ functions.filter fun function =>
    selectedHelperNames.contains function.name
  let imports := module.imports.filter fun import_ =>
    match import_.declaration? with
    | some declaration => !declarations.contains declaration
    | none => true
  let result : Module := {
    module with
    functions := linkedFunctions
    imports
    exports := selectedHelperNames.foldl Fir.Wasm.addUnique module.exports
    runtimeOperations := Fir.Wasm.collectRuntimeOps linkedFunctions }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

/-- Internalize exactly the supported ByteArray operations present. -/
def internalizeAvailable (module : Module) : Except LinkError Module :=
  let declarations := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
  if declarations.isEmpty then pure module else do
    let module ← if !declarations.contains `ByteArray.mk ||
        module.functions.any (·.name == ResidentScalarBox.unboxUInt8Name) then
      pure module
    else
      ResidentScalarBox.internalizeOperations module #[.unbox .uint8]
        |>.mapError .scalarHelperLink
    internalizeSelected module declarations

private def externalTypes (declaration : Name) : ExternalTypes :=
  if declaration == `ByteArray.copySlice then
    { params := #[LCNF.ImpureType.object, LCNF.ImpureType.tobject,
        LCNF.ImpureType.object, LCNF.ImpureType.tobject,
        LCNF.ImpureType.tobject, LCNF.ImpureType.uint8],
      result := LCNF.ImpureType.object }
  else if declaration == `ByteArray.size then
    { params := #[LCNF.ImpureType.object], result := LCNF.ImpureType.tagged }
  else if declaration == `ByteArray.mk then
    { params := #[LCNF.ImpureType.object], result := LCNF.ImpureType.object }
  else
    { params := #[LCNF.ImpureType.tobject], result := LCNF.ImpureType.object }

private def externalImport (declaration : Name) : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := (expectedSignature? declaration).get!
  externalTypes? := some (externalTypes declaration) }

private def scalarPrerequisiteFunction : Function := {
  name := scalarPrerequisiteName
  params := #[(rawParam, .tobject)]
  results := #[.uint8]
  locals := #[]
  body := [
    .localGet rawParam,
    .call (.runtime (.unbox .uint8)),
    .ret] }

def residentExampleModule : Except String Module := do
  let numeric ← ResidentNumeric.residentExampleModule
  let unboxOperation : RuntimeOp := .unbox .uint8
  let scalarInput : Module := {
    numeric with
    imports := numeric.imports.push (Fir.Wasm.runtimeImport numeric.imports.size
      unboxOperation)
    functions := numeric.functions.push scalarPrerequisiteFunction
    runtimeOperations := numeric.runtimeOperations.push unboxOperation }
  let scalar ← ResidentScalarBox.internalizeAvailable scalarInput
    |>.mapError fun error => s!"byte-array scalar prerequisite: {repr error}"
  let scalar ← ResidentRelease.internalizeReleases scalar
    |>.mapError fun error => s!"byte-array releases: {repr error}"
  let module : Module := {
    scalar with
    imports := scalar.imports ++ externalDeclarations.map externalImport }
  internalizeSelected module externalDeclarations
    |>.mapError fun error => s!"byte-array: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <| externalDeclarations.map fun declaration =>
      Json.mkObj [
        ("sourceEntry", declaration.toString),
        ("entry", externalName declaration |>.toString)]),
    ("layout", "fir.wasm.byte-array/v2"),
    ("ownership", "module-owned Lean reference counts; copied host output"),
    ("imports", Json.arr #[]),
    ("status", "generation-ready; W6 ByteArray contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      (externalDeclarations.all fun declaration =>
        module.exports.contains (externalName declaration)) &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentByteArray
