import Fir.Wasm.Emit.ResidentLiteral
import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentString

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean
open Lean.Compiler

/-!
# Wasm-resident `prettyM` UTF-8 frontier

This generation slice internalizes the eight String declarations reachable
from `Std.Format.prettyM`. It consumes and produces the W6 concrete UTF-8
String layout directly and reuses the resident one-limb Natural helpers for
String positions and results.

The byte walkers use structured Wasm loops. Their stack usage is therefore
independent of String size while preserving the same concrete W6 layout and
helper signatures.

The helper is intentionally independent from its W6 refinement theorem.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | missingNumericHelper (name : Name)
  | reservedDeclaration (name : Name)
  | missingExternal (name : Name)
  | incompatibleExternal (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def sourceParam : FVarId := ⟨`source⟩
private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def codePointParam : FVarId := ⟨`codePoint⟩
private def countParam : FVarId := ⟨`count⟩
private def positionParam : FVarId := ⟨`position⟩
private def beginParam : FVarId := ⟨`begin⟩
private def endParam : FVarId := ⟨`end⟩
private def rawParam : FVarId := ⟨`raw⟩
private def byteCountParam : FVarId := ⟨`byteCount⟩
private def destinationParam : FVarId := ⟨`destination⟩
private def indexParam : FVarId := ⟨`index⟩
private def widthParam : FVarId := ⟨`width⟩
private def byte0Param : FVarId := ⟨`byte0⟩
private def byte1Param : FVarId := ⟨`byte1⟩
private def byte2Param : FVarId := ⟨`byte2⟩
private def byte3Param : FVarId := ⟨`byte3⟩

private def copyBytesLoop : FVarId := ⟨`copyBytesLoop⟩
private def countLeadingLoop : FVarId := ⟨`countLeadingLoop⟩
private def fillCodePointLoop : FVarId := ⟨`fillCodePointLoop⟩
private def findCodePointLoop : FVarId := ⟨`findCodePointLoop⟩

private def addressLocal : FVarId := ⟨`address⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def tobjectResultLocal : FVarId := ⟨`tobjectResult⟩
private def taggedResultLocal : FVarId := ⟨`taggedResult⟩
private def rawLocal : FVarId := ⟨`rawValue⟩
private def allocationLocal : FVarId := ⟨`allocationBytes⟩
private def unitsLocal : FVarId := ⟨`allocationUnits⟩
private def byteLocal : FVarId := ⟨`byte⟩
private def incrementLocal : FVarId := ⟨`increment⟩
private def widthLocal : FVarId := ⟨`widthValue⟩
private def byte0Local : FVarId := ⟨`byte0Value⟩
private def byte1Local : FVarId := ⟨`byte1Value⟩
private def byte2Local : FVarId := ⟨`byte2Value⟩
private def byte3Local : FVarId := ⟨`byte3Value⟩
private def leftLengthLocal : FVarId := ⟨`leftLength⟩
private def rightLengthLocal : FVarId := ⟨`rightLength⟩
private def sourceLengthLocal : FVarId := ⟨`sourceLength⟩
private def totalLengthLocal : FVarId := ⟨`totalLength⟩
private def extraLengthLocal : FVarId := ⟨`extraLength⟩
private def lowLocal : FVarId := ⟨`lowValue⟩
private def highLocal : FVarId := ⟨`highValue⟩
private def limitLocal : FVarId := ⟨`limit⟩
private def remainingLocal : FVarId := ⟨`remaining⟩
private def matchLocal : FVarId := ⟨`matches⟩
private def leadingCountLocal : FVarId := ⟨`leadingCount⟩
private def effectiveEndLocal : FVarId := ⟨`effectiveEnd⟩
private def copyLengthLocal : FVarId := ⟨`copyLength⟩

def validateName : Name := `fir_string_validate
def byteLengthName : Name := `fir_string_byte_length
def expectedAllocationName : Name := `fir_string_expected_allocation
def allocateName : Name := `fir_string_allocate
def retypeObjectName : Name := `fir_string_retype_object
def makeNatural32Name : Name := `fir_string_make_natural32
def copyBytesName : Name := `fir_string_copy_bytes
def countLeadingName : Name := `fir_string_count_leading_bytes
def utf8WidthName : Name := `fir_string_utf8_width
def isBoundaryName : Name := `fir_string_is_boundary
def encodeCodePointName : Name := `fir_string_encode_code_point
def scaledCountName : Name := `fir_string_scaled_count
def fillCodePointName : Name := `fir_string_fill_code_point
def findCodePointName : Name := `fir_string_find_code_point

def internalHelperNames : Array Name := #[
  validateName,
  byteLengthName,
  expectedAllocationName,
  allocateName,
  retypeObjectName,
  makeNatural32Name,
  copyBytesName,
  countLeadingName,
  utf8WidthName,
  isBoundaryName,
  encodeCodePointName,
  scaledCountName,
  fillCodePointName,
  findCodePointName]

def externalDeclarations : Array Name := #[
  `String.Internal.pushn,
  `String.Internal.append,
  `String.Internal.length,
  `String.Internal.posOf,
  `String.Internal.offsetOfPos,
  `String.utf8ByteSize,
  `String.Internal.extract,
  `String.Internal.next]

def externalName (declaration : Name) : Name :=
  ResidentNumeric.externalName declaration

def externalHelperNames : Array Name := externalDeclarations.map externalName

def helperNames : Array Name := internalHelperNames ++ externalHelperNames

private def equalsConst (kind : AbiKind) (value : UInt32) :
    List Instruction :=
  [.i32Const kind value, .i32Eq]

private def trapWhenTrue (condition : List Instruction) : List Instruction :=
  condition ++ [.ifElse [.unreachable] []]

private def trapUnlessTrue (condition : List Instruction) : List Instruction :=
  trapWhenTrue (condition ++ equalsConst .uint32 0)

private def load32 (object : FVarId) (offset : Nat) :
    List Instruction :=
  [.localGet object, .i32Load .uint32 (u32 offset)]

private def dynamicByteLoad (object index : FVarId) : List Instruction := [
  .localGet object,
  .localGet index,
  .i32Add,
  .i32Load8U .uint32 (u32 headerBytes)]

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
  params := #[(byteCountParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (allocationLocal, .uint32),
    (unitsLocal, .uint32)]
  body := [
    .localGet byteCountParam,
    .i32Const .uint32 (u32 (headerBytes + target.heapAlignment - 1)),
    .i32Add,
    .localSet allocationLocal] ++
    trapWhenTrue [
      .localGet allocationLocal,
      .localGet byteCountParam,
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
  locals := #[(sourceLengthLocal, .uint32)]
  body :=
    requireHeapAddress sourceParam ++
    trapUnlessTrue (
      load32 sourceParam headerKindOffset ++
      equalsConst .uint32 ObjectKind.string.code) ++
    trapUnlessTrue (
      load32 sourceParam headerAux0Offset ++
      equalsConst .uint32 stringUtf8Marker) ++
    trapWhenTrue (load32 sourceParam headerAux2Offset) ++
    trapWhenTrue (load32 sourceParam headerAux3Offset) ++ [
      .localGet sourceParam,
      .i32Load .uint32 (u32 headerAux1Offset),
      .localSet sourceLengthLocal,
      .localGet sourceParam,
      .i32Load .uint32 (u32 headerAllocationBytesOffset),
      .localGet sourceLengthLocal,
      .call (.declaration expectedAllocationName),
      .i32Eq] ++
    trapUnlessTrue [] ++
    load32 sourceParam headerFlagsOffset ++
    equalsConst .uint32 liveFlag ++ [
      .ifElse
        (trapUnlessTrue (
          load32 sourceParam headerRefCountOffset ++
          equalsConst .uint32 0 ++
          equalsConst .uint32 0) ++ [.ret])
        (trapUnlessTrue (
          load32 sourceParam headerFlagsOffset ++
          equalsConst .uint32 (liveFlag + persistentFlag)) ++
          trapWhenTrue (load32 sourceParam headerRefCountOffset) ++
          [.ret])] }

def byteLengthFunction : Function := {
  name := byteLengthName
  params := #[(sourceParam, .object)]
  results := #[.uint32]
  locals := #[]
  body := load32 sourceParam headerAux1Offset ++ [.ret] }

def allocateFunction : Function := {
  name := allocateName
  params := #[(byteCountParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (addressLocal, .uint32),
    (allocationLocal, .uint32)]
  body := [
    .localGet byteCountParam,
    .call (.declaration expectedAllocationName),
    .localSet allocationLocal,
    .localGet allocationLocal,
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal,
    .localGet addressLocal,
    .i32Const .uint32 ObjectKind.string.code,
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
    .i32Const .uint32 stringUtf8Marker,
    .i32Store .uint32 (u32 headerAux0Offset),
    .localGet addressLocal,
    .localGet byteCountParam,
    .i32Store .uint32 (u32 headerAux1Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
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
  locals := #[
    (rawLocal, .uint32),
    (savedScratchLocal, .uint32),
    (objectResultLocal, .object)]
  body := [.localGet rawParam] ++ retypeRaw .object objectResultLocal }

def makeNatural32Function : Function := {
  name := makeNatural32Name
  params := #[(rawParam, .uint32)]
  results := #[.tobject]
  locals := #[
    (rawLocal, .uint32),
    (savedScratchLocal, .uint32),
    (tobjectResultLocal, .tobject)]
  body := [
    .localGet rawParam,
    .i32Const .uint32 0,
    .call (.declaration ResidentNumeric.makeNaturalName)] ++
    retypeRaw .tobject tobjectResultLocal }

def copyBytesFunction : Function := {
  name := copyBytesName
  params := #[
    (destinationParam, .uint32),
    (sourceParam, .uint32),
    (countParam, .uint32)]
  results := #[]
  locals := #[]
  body := [
    .loop copyBytesLoop [
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
      .br copyBytesLoop]] }

def countLeadingFunction : Function := {
  name := countLeadingName
  params := #[
    (sourceParam, .uint32),
    (countParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (byteLocal, .uint32),
    (incrementLocal, .uint32),
    (leadingCountLocal, .uint32)]
  body := [
    .i32Const .uint32 0,
    .localSet leadingCountLocal,
    .loop countLeadingLoop [
      .localGet countParam,
      .i32Const .uint32 0,
      .i32Eq,
      .ifElse [.localGet leadingCountLocal, .ret] [],
      .localGet sourceParam,
      .i32Load8U .uint32 0,
      .localSet byteLocal,
      .localGet byteLocal,
      .i32Const .uint32 192,
      .i32And,
      .i32Const .uint32 128,
      .i32Eq,
      .ifElse
        [.i32Const .uint32 0, .localSet incrementLocal]
        [.i32Const .uint32 1, .localSet incrementLocal],
      .localGet leadingCountLocal,
      .localGet incrementLocal,
      .i32Add,
      .localSet leadingCountLocal,
      .localGet sourceParam,
      .i32Const .uint32 1,
      .i32Add,
      .localSet sourceParam,
      .localGet countParam,
      .i32Const .uint32 1,
      .i32Sub,
      .localSet countParam,
      .br countLeadingLoop]] }

private def widthBranch (threshold width : UInt32)
    (fallback : List Instruction) : List Instruction := [
  .localGet byte0Param,
  .i32Const .uint32 threshold,
  .i32LtU,
  .ifElse [.i32Const .uint32 width, .ret] fallback]

def utf8WidthFunction : Function := {
  name := utf8WidthName
  params := #[(byte0Param, .uint32)]
  results := #[.uint32]
  locals := #[]
  body :=
    widthBranch 128 1 <|
    widthBranch 192 1 <|
    widthBranch 224 2 <|
    widthBranch 240 3 <|
    widthBranch 248 4 [.i32Const .uint32 1, .ret] }

def isBoundaryFunction : Function := {
  name := isBoundaryName
  params := #[
    (sourceParam, .object),
    (byteCountParam, .uint32),
    (positionParam, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet positionParam,
    .localGet byteCountParam,
    .i32Eq,
    .ifElse
      [.i32Const .uint32 1, .ret]
      [.localGet positionParam,
        .localGet byteCountParam,
        .i32LtU,
        .ifElse
          (dynamicByteLoad sourceParam positionParam ++ [
            .i32Const .uint32 192,
            .i32And,
            .i32Const .uint32 128,
            .i32Eq,
            .i32Const .uint32 0,
            .i32Eq,
            .ret])
          [.i32Const .uint32 0, .ret]]] }

private def setEncodedByte (target : FVarId)
    (prefixValue shift mask : UInt32) :
    List Instruction := [
  .i32Const .uint32 prefixValue,
  .localGet codePointParam,
  .i32Const .uint32 shift,
  .i32ShrU,
  .i32Const .uint32 mask,
  .i32And,
  .i32Add,
  .localSet target]

private def setFinalEncodedByte : List Instruction := [
  .i32Const .uint32 128,
  .localGet codePointParam,
  .i32Const .uint32 63,
  .i32And,
  .i32Add,
  .localSet byte3Local]

private def encodeOneByte : List Instruction := [
  .i32Const .uint32 1,
  .localSet widthLocal,
  .localGet codePointParam,
  .localSet byte0Local]

private def encodeTwoBytes : List Instruction :=
  [.i32Const .uint32 2, .localSet widthLocal] ++
    setEncodedByte byte0Local 192 6 31 ++ [
    .i32Const .uint32 128,
    .localGet codePointParam,
    .i32Const .uint32 63,
    .i32And,
    .i32Add,
    .localSet byte1Local]

private def encodeThreeBytes : List Instruction :=
  [.i32Const .uint32 3, .localSet widthLocal] ++
    setEncodedByte byte0Local 224 12 15 ++
    setEncodedByte byte1Local 128 6 63 ++ [
    .i32Const .uint32 128,
    .localGet codePointParam,
    .i32Const .uint32 63,
    .i32And,
    .i32Add,
    .localSet byte2Local]

private def encodeFourBytes : List Instruction :=
  [.i32Const .uint32 4, .localSet widthLocal] ++
    setEncodedByte byte0Local 240 18 7 ++
    setEncodedByte byte1Local 128 12 63 ++
    setEncodedByte byte2Local 128 6 63 ++
    setFinalEncodedByte

private def selectEncodedCodePoint : List Instruction := [
  .localGet codePointParam,
  .i32Const .uint32 128,
  .i32LtU,
  .ifElse encodeOneByte [
    .localGet codePointParam,
    .i32Const .uint32 2048,
    .i32LtU,
    .ifElse encodeTwoBytes [
      .localGet codePointParam,
      .i32Const .uint32 65536,
      .i32LtU,
      .ifElse encodeThreeBytes encodeFourBytes]]]

def encodeCodePointFunction : Function := {
  name := encodeCodePointName
  params := #[(codePointParam, .uint32)]
  results := #[
    .uint32, .uint32, .uint32, .uint32, .uint32]
  locals := #[
    (widthLocal, .uint32),
    (byte0Local, .uint32),
    (byte1Local, .uint32),
    (byte2Local, .uint32),
    (byte3Local, .uint32)]
  body :=
    trapUnlessTrue [
      .localGet codePointParam,
      .i32Const .uint32 1114112,
      .i32LtU] ++
    trapWhenTrue [
      .localGet codePointParam,
      .i32Const .uint32 55296,
      .i32LtU,
      .i32Const .uint32 0,
      .i32Eq,
      .localGet codePointParam,
      .i32Const .uint32 57344,
      .i32LtU,
      .i32And] ++ [
      .i32Const .uint32 0,
      .localSet byte0Local,
      .i32Const .uint32 0,
      .localSet byte1Local,
      .i32Const .uint32 0,
      .localSet byte2Local,
      .i32Const .uint32 0,
      .localSet byte3Local] ++
      selectEncodedCodePoint ++ [
      .localGet widthLocal,
      .localGet byte0Local,
      .localGet byte1Local,
      .localGet byte2Local,
      .localGet byte3Local,
      .ret] }

private def checkedAdd (left right result : FVarId) : List Instruction := [
  .localGet left,
  .localGet right,
  .i32Add,
  .localSet result] ++
  trapWhenTrue [
    .localGet result,
    .localGet left,
    .i32LtU]

private def scaledTwo : List Instruction :=
  checkedAdd countParam countParam extraLengthLocal ++
    [.localGet extraLengthLocal, .ret]

private def scaledThree : List Instruction :=
  checkedAdd countParam countParam extraLengthLocal ++
    checkedAdd extraLengthLocal countParam totalLengthLocal ++
    [.localGet totalLengthLocal, .ret]

private def scaledFour : List Instruction :=
  checkedAdd countParam countParam extraLengthLocal ++
    checkedAdd extraLengthLocal extraLengthLocal totalLengthLocal ++
    [.localGet totalLengthLocal, .ret]

private def scaleBranch (width : UInt32) (value fallback : List Instruction) :
    List Instruction := [
  .localGet widthParam,
  .i32Const .uint32 width,
  .i32Eq,
  .ifElse value fallback]

def scaledCountFunction : Function := {
  name := scaledCountName
  params := #[
    (countParam, .uint32),
    (widthParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (extraLengthLocal, .uint32),
    (totalLengthLocal, .uint32)]
  body :=
    scaleBranch 1 [.localGet countParam, .ret] <|
    scaleBranch 2 scaledTwo <|
    scaleBranch 3 scaledThree <|
    scaleBranch 4 scaledFour [.unreachable] }

private def storeEncodedByte (byte : FVarId) (offset : Nat) :
    List Instruction := [
  .localGet destinationParam,
  .localGet byte,
  .i32Store8 .uint32 (u32 offset)]

def fillCodePointFunction : Function := {
  name := fillCodePointName
  params := #[
    (destinationParam, .uint32),
    (widthParam, .uint32),
    (byte0Param, .uint32),
    (byte1Param, .uint32),
    (byte2Param, .uint32),
    (byte3Param, .uint32),
    (countParam, .uint32)]
  results := #[]
  locals := #[]
  body := [
    .loop fillCodePointLoop <|
      [
        .localGet countParam,
        .i32Const .uint32 0,
        .i32Eq,
        .ifElse [.ret] []] ++
      storeEncodedByte byte0Param 0 ++ [
        .i32Const .uint32 1,
        .localGet widthParam,
        .i32LtU,
        .ifElse (storeEncodedByte byte1Param 1) [],
        .i32Const .uint32 2,
        .localGet widthParam,
        .i32LtU,
        .ifElse (storeEncodedByte byte2Param 2) [],
        .i32Const .uint32 3,
        .localGet widthParam,
        .i32LtU,
        .ifElse (storeEncodedByte byte3Param 3) [],
        .localGet destinationParam,
        .localGet widthParam,
        .i32Add,
        .localSet destinationParam,
        .localGet countParam,
        .i32Const .uint32 1,
        .i32Sub,
        .localSet countParam,
        .br fillCodePointLoop]] }

private def compareDynamicByte (offset : Nat) (expected : FVarId) :
    List Instruction := [
  .localGet sourceParam,
  .localGet indexParam,
  .i32Add,
  .i32Load8U .uint32 (u32 (headerBytes + offset)),
  .localGet expected,
  .i32Eq,
  .localGet matchLocal,
  .i32And,
  .localSet matchLocal]

def findCodePointFunction : Function := {
  name := findCodePointName
  params := #[
    (sourceParam, .object),
    (byteCountParam, .uint32),
    (indexParam, .uint32),
    (widthParam, .uint32),
    (byte0Param, .uint32),
    (byte1Param, .uint32),
    (byte2Param, .uint32),
    (byte3Param, .uint32)]
  results := #[.uint32]
  locals := #[
    (remainingLocal, .uint32),
    (matchLocal, .uint32)]
  body := [
    .loop findCodePointLoop <|
      [
        .localGet byteCountParam,
        .localGet indexParam,
        .i32Sub,
        .localSet remainingLocal,
        .localGet remainingLocal,
        .localGet widthParam,
        .i32LtU,
        .ifElse [.localGet byteCountParam, .ret] [],
        .i32Const .uint32 1,
        .localSet matchLocal] ++
      compareDynamicByte 0 byte0Param ++ [
        .i32Const .uint32 1,
        .localGet widthParam,
        .i32LtU,
        .ifElse (compareDynamicByte 1 byte1Param) [],
        .i32Const .uint32 2,
        .localGet widthParam,
        .i32LtU,
        .ifElse (compareDynamicByte 2 byte2Param) [],
        .i32Const .uint32 3,
        .localGet widthParam,
        .i32LtU,
        .ifElse (compareDynamicByte 3 byte3Param) [],
        .localGet matchLocal,
        .ifElse
          [.localGet indexParam, .ret]
          [.localGet indexParam,
            .i32Const .uint32 1,
            .i32Add,
            .localSet indexParam,
            .br findCodePointLoop]]] }

private def encodedLocals : Array (FVarId × AbiKind) := #[
  (widthLocal, .uint32),
  (byte0Local, .uint32),
  (byte1Local, .uint32),
  (byte2Local, .uint32),
  (byte3Local, .uint32)]

private def receiveEncodedCodePoint : List Instruction := [
  .localGet codePointParam,
  .call (.declaration encodeCodePointName),
  .localSet byte3Local,
  .localSet byte2Local,
  .localSet byte1Local,
  .localSet byte0Local,
  .localSet widthLocal]

private def objectResultLocals : Array (FVarId × AbiKind) := #[
  (rawLocal, .uint32),
  (savedScratchLocal, .uint32),
  (objectResultLocal, .object)]

private def naturalResultLocals : Array (FVarId × AbiKind) := #[
  (rawLocal, .uint32),
  (savedScratchLocal, .uint32),
  (tobjectResultLocal, .tobject)]

private def validateNatural (value : FVarId) : List Instruction := [
  .localGet value,
  .call (.declaration ResidentNumeric.validateNaturalName)]

private def loadNaturalParts (value : FVarId) : List Instruction := [
  .localGet value,
  .call (.declaration ResidentNumeric.naturalLowName),
  .localSet lowLocal,
  .localGet value,
  .call (.declaration ResidentNumeric.naturalHighName),
  .localSet highLocal]

private def callCopyPayload
    (destinationObject sourceObject : FVarId)
    (destinationOffset : List Instruction)
    (sourceOffset : List Instruction)
    (count : FVarId) : List Instruction :=
  [.localGet destinationObject] ++ destinationOffset ++
    [.i32Add, .localGet sourceObject] ++ sourceOffset ++
    [.i32Add, .localGet count, .call (.declaration copyBytesName)]

def appendFunction : Function := {
  name := externalName `String.Internal.append
  params := #[
    (leftParam, .object),
    (rightParam, .object)]
  results := #[.object]
  locals := objectResultLocals ++ #[
    (leftLengthLocal, .uint32),
    (rightLengthLocal, .uint32),
    (totalLengthLocal, .uint32),
    (addressLocal, .uint32)]
  body := [
    .localGet leftParam,
    .call (.declaration validateName),
    .localGet rightParam,
    .call (.declaration validateName),
    .localGet leftParam,
    .call (.declaration byteLengthName),
    .localSet leftLengthLocal,
    .localGet rightParam,
    .call (.declaration byteLengthName),
    .localSet rightLengthLocal] ++
    checkedAdd leftLengthLocal rightLengthLocal totalLengthLocal ++ [
    .localGet totalLengthLocal,
    .call (.declaration allocateName),
    .localSet addressLocal] ++
    callCopyPayload addressLocal leftParam
      [.i32Const .uint32 (u32 headerBytes)]
      [.i32Const .uint32 (u32 headerBytes)]
      leftLengthLocal ++
    callCopyPayload addressLocal rightParam
      [.i32Const .uint32 (u32 headerBytes), .localGet leftLengthLocal, .i32Add]
      [.i32Const .uint32 (u32 headerBytes)]
      rightLengthLocal ++
    [.localGet addressLocal] ++ retypeRaw .object objectResultLocal }

def pushnFunction : Function := {
  name := externalName `String.Internal.pushn
  params := #[
    (sourceParam, .object),
    (codePointParam, .uint32),
    (countParam, .tobject)]
  results := #[.object]
  locals := objectResultLocals ++ encodedLocals ++ #[
    (sourceLengthLocal, .uint32),
    (extraLengthLocal, .uint32),
    (totalLengthLocal, .uint32),
    (addressLocal, .uint32),
    (lowLocal, .uint32),
    (highLocal, .uint32)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName)] ++
    validateNatural countParam ++
    loadNaturalParts countParam ++
    trapWhenTrue [.localGet highLocal] ++
    receiveEncodedCodePoint ++ [
    .localGet sourceParam,
    .call (.declaration byteLengthName),
    .localSet sourceLengthLocal,
    .localGet lowLocal,
    .localGet widthLocal,
    .call (.declaration scaledCountName),
    .localSet extraLengthLocal] ++
    checkedAdd sourceLengthLocal extraLengthLocal totalLengthLocal ++ [
    .localGet totalLengthLocal,
    .call (.declaration allocateName),
    .localSet addressLocal] ++
    callCopyPayload addressLocal sourceParam
      [.i32Const .uint32 (u32 headerBytes)]
      [.i32Const .uint32 (u32 headerBytes)]
      sourceLengthLocal ++ [
    .localGet addressLocal,
    .i32Const .uint32 (u32 headerBytes),
    .i32Add,
    .localGet sourceLengthLocal,
    .i32Add,
    .localGet widthLocal,
    .localGet byte0Local,
    .localGet byte1Local,
    .localGet byte2Local,
    .localGet byte3Local,
    .localGet lowLocal,
    .call (.declaration fillCodePointName),
    .localGet addressLocal] ++
    retypeRaw .object objectResultLocal }

def lengthFunction : Function := {
  name := externalName `String.Internal.length
  params := #[(sourceParam, .object)]
  results := #[.tobject]
  locals := naturalResultLocals ++ #[(sourceLengthLocal, .uint32)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName),
    .localGet sourceParam,
    .call (.declaration byteLengthName),
    .localSet sourceLengthLocal,
    .localGet sourceParam,
    .i32Const .uint32 (u32 headerBytes),
    .i32Add,
    .localGet sourceLengthLocal,
    .call (.declaration countLeadingName),
    .call (.declaration makeNatural32Name),
    .ret] }

def posOfFunction : Function := {
  name := externalName `String.Internal.posOf
  params := #[
    (sourceParam, .object),
    (codePointParam, .uint32)]
  results := #[.tobject]
  locals := naturalResultLocals ++ encodedLocals ++ #[
    (sourceLengthLocal, .uint32)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName)] ++
    receiveEncodedCodePoint ++ [
    .localGet sourceParam,
    .call (.declaration byteLengthName),
    .localSet sourceLengthLocal,
    .localGet sourceParam,
    .localGet sourceLengthLocal,
    .i32Const .uint32 0,
    .localGet widthLocal,
    .localGet byte0Local,
    .localGet byte1Local,
    .localGet byte2Local,
    .localGet byte3Local,
    .call (.declaration findCodePointName),
    .call (.declaration makeNatural32Name),
    .ret] }

def offsetOfPosFunction : Function := {
  name := externalName `String.Internal.offsetOfPos
  params := #[
    (sourceParam, .object),
    (positionParam, .tobject)]
  results := #[.tobject]
  locals := naturalResultLocals ++ #[
    (sourceLengthLocal, .uint32),
    (lowLocal, .uint32),
    (highLocal, .uint32),
    (limitLocal, .uint32)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName)] ++
    validateNatural positionParam ++
    loadNaturalParts positionParam ++ [
    .localGet sourceParam,
    .call (.declaration byteLengthName),
    .localSet sourceLengthLocal,
    .localGet highLocal,
    .ifElse
      [.localGet sourceLengthLocal, .localSet limitLocal]
      [.localGet sourceLengthLocal,
        .localGet lowLocal,
        .i32LtU,
        .ifElse
          [.localGet sourceLengthLocal, .localSet limitLocal]
          [.localGet lowLocal, .localSet limitLocal]],
    .localGet sourceParam,
    .i32Const .uint32 (u32 headerBytes),
    .i32Add,
    .localGet limitLocal,
    .call (.declaration countLeadingName),
    .call (.declaration makeNatural32Name),
    .ret] }

def utf8ByteSizeFunction : Function := {
  name := externalName `String.utf8ByteSize
  params := #[(sourceParam, .object)]
  results := #[.tagged]
  locals := #[
    (sourceLengthLocal, .uint32),
    (rawLocal, .uint32),
    (savedScratchLocal, .uint32),
    (taggedResultLocal, .tagged)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName),
    .localGet sourceParam,
    .call (.declaration byteLengthName),
    .localSet sourceLengthLocal,
    .localGet sourceLengthLocal,
    .i32Const .uint32 0,
    .call (.declaration ResidentNumeric.makeNaturalName)] ++
    retypeRaw .tagged taggedResultLocal }

private def allocateEmptyResult : List Instruction := [
  .i32Const .uint32 0,
  .call (.declaration allocateName)] ++
  retypeRaw .object objectResultLocal

def extractFunction : Function := {
  name := externalName `String.Internal.extract
  params := #[
    (sourceParam, .object),
    (beginParam, .tobject),
    (endParam, .tobject)]
  results := #[.object]
  locals := objectResultLocals ++ #[
    (sourceLengthLocal, .uint32),
    (lowLocal, .uint32),
    (highLocal, .uint32),
    (effectiveEndLocal, .uint32),
    (copyLengthLocal, .uint32),
    (addressLocal, .uint32),
    (leftLengthLocal, .uint32),
    (rightLengthLocal, .uint32)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName)] ++
    validateNatural beginParam ++
    validateNatural endParam ++ [
    .localGet sourceParam,
    .call (.declaration byteLengthName),
    .localSet sourceLengthLocal,
    .localGet beginParam,
    .call (.declaration ResidentNumeric.naturalLowName),
    .localSet leftLengthLocal,
    .localGet beginParam,
    .call (.declaration ResidentNumeric.naturalHighName),
    .localSet highLocal,
    .localGet highLocal,
    .ifElse allocateEmptyResult [],
    .localGet endParam,
    .call (.declaration ResidentNumeric.naturalLowName),
    .localSet rightLengthLocal,
    .localGet endParam,
    .call (.declaration ResidentNumeric.naturalHighName),
    .localSet highLocal,
    .localGet highLocal,
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse
      [.localGet leftLengthLocal,
        .localGet rightLengthLocal,
        .i32LtU,
        .i32Const .uint32 0,
        .i32Eq,
        .ifElse allocateEmptyResult []]
      [],
    .localGet leftLengthLocal,
    .localGet sourceLengthLocal,
    .i32LtU,
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse allocateEmptyResult [],
    .localGet sourceParam,
    .localGet sourceLengthLocal,
    .localGet leftLengthLocal,
    .call (.declaration isBoundaryName),
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse allocateEmptyResult [],
    .localGet highLocal,
    .ifElse
      [.localGet sourceLengthLocal, .localSet effectiveEndLocal]
      [.localGet sourceLengthLocal,
        .localGet rightLengthLocal,
        .i32LtU,
        .ifElse
          [.localGet sourceLengthLocal, .localSet effectiveEndLocal]
          [.localGet sourceParam,
            .localGet sourceLengthLocal,
            .localGet rightLengthLocal,
            .call (.declaration isBoundaryName),
            .ifElse
              [.localGet rightLengthLocal, .localSet effectiveEndLocal]
              [.localGet sourceLengthLocal, .localSet effectiveEndLocal]]],
    .localGet effectiveEndLocal,
    .localGet leftLengthLocal,
    .i32Sub,
    .localSet copyLengthLocal,
    .localGet copyLengthLocal,
    .call (.declaration allocateName),
    .localSet addressLocal] ++
    callCopyPayload addressLocal sourceParam
      [.i32Const .uint32 (u32 headerBytes)]
      [.i32Const .uint32 (u32 headerBytes), .localGet leftLengthLocal, .i32Add]
      copyLengthLocal ++
    [.localGet addressLocal] ++ retypeRaw .object objectResultLocal }

def nextFunction : Function := {
  name := externalName `String.Internal.next
  params := #[
    (sourceParam, .object),
    (positionParam, .tobject)]
  results := #[.tobject]
  locals := naturalResultLocals ++ #[
    (sourceLengthLocal, .uint32),
    (lowLocal, .uint32),
    (highLocal, .uint32),
    (widthLocal, .uint32)]
  body := [
    .localGet sourceParam,
    .call (.declaration validateName)] ++
    validateNatural positionParam ++
    loadNaturalParts positionParam ++ [
    .localGet sourceParam,
    .call (.declaration byteLengthName),
    .localSet sourceLengthLocal,
    .localGet highLocal,
    .ifElse
      [.localGet positionParam,
        .i32Const .tobject 3,
        .call (.declaration (externalName `Nat.add)),
        .ret]
      [.localGet lowLocal,
        .localGet sourceLengthLocal,
        .i32LtU,
        .ifElse
          (dynamicByteLoad sourceParam lowLocal ++ [
            .call (.declaration utf8WidthName),
            .localSet widthLocal,
            .localGet lowLocal,
            .localGet widthLocal,
            .i32Add,
            .call (.declaration makeNatural32Name),
            .ret])
          [.localGet positionParam,
            .i32Const .tobject 3,
            .call (.declaration (externalName `Nat.add)),
            .ret]]] }

def externalFunctions : Array Function := #[
  pushnFunction,
  appendFunction,
  lengthFunction,
  posOfFunction,
  offsetOfPosFunction,
  utf8ByteSizeFunction,
  extractFunction,
  nextFunction]

def internalFunctions : Array Function := #[
  expectedAllocationFunction,
  validateFunction,
  byteLengthFunction,
  allocateFunction,
  retypeObjectFunction,
  makeNatural32Function,
  copyBytesFunction,
  countLeadingFunction,
  utf8WidthFunction,
  isBoundaryFunction,
  encodeCodePointFunction,
  scaledCountFunction,
  fillCodePointFunction,
  findCodePointFunction]

private partial def rewriteInstruction : Instruction → Instruction
  | .call (.declaration declaration) =>
      if externalDeclarations.contains declaration then
        .call (.declaration (externalName declaration))
      else
        .call (.declaration declaration)
  | .block label body =>
      .block label (body.map rewriteInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse
        (thenBody.map rewriteInstruction)
        (elseBody.map rewriteInstruction)
  | instruction => instruction

private def rewriteFunction (function : Function) : Function :=
  { function with body := function.body.map rewriteInstruction }

private def expectedSignature? (declaration : Name) : Option Signature :=
  if declaration == `String.Internal.pushn then
    some {
      params := #[.object, .uint32, .tobject]
      results := #[.object] }
  else if declaration == `String.Internal.append then
    some { params := #[.object, .object], results := #[.object] }
  else if declaration == `String.Internal.length then
    some { params := #[.object], results := #[.tobject] }
  else if declaration == `String.Internal.posOf then
    some { params := #[.object, .uint32], results := #[.tobject] }
  else if declaration == `String.Internal.offsetOfPos ||
      declaration == `String.Internal.next then
    some { params := #[.object, .tobject], results := #[.tobject] }
  else if declaration == `String.utf8ByteSize then
    some { params := #[.object], results := #[.tagged] }
  else if declaration == `String.Internal.extract then
    some {
      params := #[.object, .tobject, .tobject]
      results := #[.object] }
  else
    none

def internalize (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  for name in ResidentNumeric.helperNames do
    unless module.functions.any (·.name == name) do
      throw (.missingNumericHelper name)
  for name in helperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) ||
        module.exports.contains name then
      throw (.reservedDeclaration name)
  for declaration in externalDeclarations do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.missingExternal declaration)
    let some signature := expectedSignature? declaration |
      throw (.incompatibleExternal declaration)
    unless imports[0]!.signature == signature do
      throw (.incompatibleExternal declaration)
  let functions :=
    module.functions.map rewriteFunction ++ internalFunctions ++ externalFunctions
  let imports := module.imports.filter fun import_ =>
    match import_.declaration? with
    | some declaration => !externalDeclarations.contains declaration
    | none => true
  let result : Module := {
    module with
    imports
    functions
    exports := helperNames.foldl Fir.Wasm.addUnique module.exports }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

private def externalTypes? (declaration : Name) : Option ExternalTypes :=
  let object := LCNF.ImpureType.object
  let tobject := LCNF.ImpureType.tobject
  let uint32 := LCNF.ImpureType.uint32
  let tagged := LCNF.ImpureType.tagged
  if declaration == `String.Internal.pushn then
    some {
      params := #[object, uint32, tobject]
      result := object }
  else if declaration == `String.Internal.append then
    some { params := #[object, object], result := object }
  else if declaration == `String.Internal.length then
    some { params := #[object], result := tobject }
  else if declaration == `String.Internal.posOf then
    some { params := #[object, uint32], result := tobject }
  else if declaration == `String.Internal.offsetOfPos ||
      declaration == `String.Internal.next then
    some { params := #[object, tobject], result := tobject }
  else if declaration == `String.utf8ByteSize then
    some { params := #[object], result := tagged }
  else if declaration == `String.Internal.extract then
    some {
      params := #[object, tobject, tobject]
      result := object }
  else
    none

private def exampleExternalImport (declaration : Name) : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := (expectedSignature? declaration).get!
  externalTypes? := externalTypes? declaration }

def exampleStringOperations : Array RuntimeOp := #[
  .literal (.str "") .object,
  .literal (.str "λ\n") .object]

private def exampleStringCaller (index : Nat) (name : Name) : Function := {
  name
  params := #[]
  results := #[.object]
  locals := #[]
  body := [
    .call (.runtime exampleStringOperations[index]!),
    .ret] }

def exampleStringFunctions : Array Function := #[
  exampleStringCaller 0 `resident_string_empty_literal,
  exampleStringCaller 1 `resident_string_unicode_literal]

def exampleModule : Module := {
  imports :=
    exampleStringOperations.mapIdx Fir.Wasm.runtimeImport ++
    ResidentNumeric.externalDeclarations.map
      (fun declaration =>
        let signature := (ResidentNumeric.exampleModule.imports.find?
          (·.declaration? == some declaration)).get!.signature
        let types := (ResidentNumeric.exampleModule.imports.find?
          (·.declaration? == some declaration)).get!.externalTypes?
        {
          key := .external declaration
          moduleName := "lean.extern"
          itemName := declaration.toString
          signature
          externalTypes? := types }) ++
    externalDeclarations.map exampleExternalImport
  functions := exampleStringFunctions
  exports := exampleStringFunctions.map (·.name)
  initializers := #[]
  runtimeOperations := exampleStringOperations }

def residentExampleModule : Except String Module := do
  let module ← ResidentAllocator.install exampleModule
    |>.mapError fun error => s!"allocator: {repr error}"
  let module ← ResidentNumeric.internalize module
    |>.mapError fun error => s!"numeric: {repr error}"
  let module ← internalize module
    |>.mapError fun error => s!"string: {repr error}"
  ResidentLiteral.internalizeStrings module
    |>.mapError fun error => s!"literal: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("sourceEntry", externalName `String.Internal.append |>.toString),
    ("entry", externalName `String.Internal.append |>.toString),
    ("params", Json.arr #["object", "object"]),
    ("result", "object"),
    ("closureDispatch", Json.arr #[]),
    ("closureDescriptors", Json.arr #[]),
    ("imports", Json.arr #[]),
    ("stringEncoding", "UTF-8"),
    ("walkerImplementation", "structured-loop"),
    ("status", "generation-only; W6 String contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      externalHelperNames.all module.exports.contains &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentString
