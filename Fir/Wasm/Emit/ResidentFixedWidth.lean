import Fir.Wasm.Emit.ResidentBigNumeric
import Fir.Wasm.Emit.ResidentUSize

namespace Fir.Wasm.Emit.ResidentFixedWidth

open Fir.Wasm
open Lean
open Lean.Compiler

/-!
# Wasm-resident fixed-width integer operations

Lean's raw fixed-width externs are ordinary machine operations. This module
internalizes the subset currently exercised by the generic ByteArray/DEFLATE
frontier using the corresponding core Wasm scalar instructions. The
declarations and signatures are source-level Lean APIs; no lean-zip declaration
is named here.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingNumericHelper (name : Name)
  | reservedDeclaration (name : Name)
  | missingExternal (name : Name)
  | incompatibleExternal (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def valueParam : FVarId := ⟨`value⟩
private def proofParam : FVarId := ⟨`proof⟩
private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def raw64Local : FVarId := ⟨`raw64⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def uint8ResultLocal : FVarId := ⟨`uint8Result⟩
private def uint16ResultLocal : FVarId := ⟨`uint16Result⟩
private def uint32ResultLocal : FVarId := ⟨`uint32Result⟩
private def uint64ResultLocal : FVarId := ⟨`uint64Result⟩
private def usizeResultLocal : FVarId := ⟨`usizeResult⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def taggedResultLocal : FVarId := ⟨`taggedResult⟩
private def countLocal : FVarId := ⟨`count⟩

def externalDeclarations : Array Name := #[
  `UInt8.ofBitVec,
  `UInt8.toBitVec,
  `UInt8.ofNat,
  `UInt8.ofNatLT,
  `UInt8.toNat,
  `UInt8.toUInt32,
  `UInt8.toUInt64,
  `UInt8.toUSize,
  `UInt8.decEq,
  `UInt8.decLt,
  `UInt8.decLe,
  `UInt8.shiftRight,
  `UInt8.land,
  `UInt8.lor,
  `UInt16.shiftRight,
  `UInt16.ofNat,
  `UInt16.toUInt8,
  `UInt16.toNat,
  `UInt16.toUInt32,
  `UInt16.toUInt64,
  `UInt16.land,
  `UInt16.xor,
  `UInt16.shiftLeft,
  `UInt16.lor,
  `UInt32.ofBitVec,
  `UInt32.ofNat,
  `UInt32.ofNatLT,
  `UInt32.log2Clz,
  `UInt32.toNat,
  `UInt32.toUInt8,
  `UInt32.toUInt16,
  `UInt32.toUInt64,
  `UInt32.toUSize,
  `UInt32.add,
  `UInt32.sub,
  `UInt32.land,
  `UInt32.xor,
  `UInt32.shiftRight,
  `UInt32.decLt,
  `UInt32.decLe,
  `UInt32.shiftLeft,
  `UInt32.lor,
  `UInt32.mul,
  `UInt64.ofBitVec,
  `UInt64.ofNat,
  `UInt64.toUInt8,
  `UInt64.toUInt16,
  `UInt64.toUSize,
  `UInt64.shiftLeft,
  `UInt64.shiftRight,
  `UInt64.decEq,
  `UInt64.add,
  `UInt64.sub,
  `UInt64.land,
  `UInt64.lor,
  `UInt64.xor,
  `UInt64.complement,
  `UInt64.decLt,
  `UInt64.mul,
  `UInt64.ctzFast,
  `UInt64.mod]

def externalName (declaration : Name) : Name :=
  Name.mkSimple s!"fir_ext_{declaration.toString.replace "." "_"}"

def helperNames : Array Name := externalDeclarations.map externalName

private def retypeRaw (result : AbiKind) (resultLocal : FVarId) :
    List Instruction := [
  .localSet rawLocal,
  .i32Const .uint32 0,
  .i64Load .uint64 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet rawLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load result 0,
  .localSet resultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i64Store .uint64 0,
  .localGet resultLocal,
  .ret]

private def retypeRaw64 (result : AbiKind) (resultLocal : FVarId) :
    List Instruction := [
  .localSet raw64Local,
  .i32Const .uint32 0,
  .i64Load .uint64 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet raw64Local,
  .i64Store .uint64 0,
  .i32Const .uint32 0,
  .i64Load result 0,
  .localSet resultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i64Store .uint64 0,
  .localGet resultLocal,
  .ret]

private def i32ResultLocal (kind : AbiKind) : FVarId :=
  if kind == .uint8 then uint8ResultLocal
  else if kind == .uint16 then uint16ResultLocal
  else if kind == .tagged then taggedResultLocal
  else if kind == .tobject then objectResultLocal
  else uint32ResultLocal

private def i64ResultLocal (kind : AbiKind) : FVarId :=
  if kind == .usize then usizeResultLocal else uint64ResultLocal

private def retypedI32Function (declaration : Name) (params : Array (FVarId × AbiKind))
    (result : AbiKind) (body : List Instruction) : Function :=
  let resultLocal := i32ResultLocal result
  {
    name := externalName declaration
    params
    results := #[result]
    locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint64),
      (resultLocal, result)]
    body := body ++ retypeRaw result resultLocal }

private def retypedI64Function (declaration : Name) (params : Array (FVarId × AbiKind))
    (result : AbiKind) (body : List Instruction) : Function :=
  let resultLocal := i64ResultLocal result
  {
    name := externalName declaration
    params
    results := #[result]
    locals := #[(raw64Local, .uint64), (savedScratchLocal, .uint64),
      (resultLocal, result)]
    body := body ++ retypeRaw64 result resultLocal }

private def ofNat32Function (declaration : Name) (result : AbiKind)
    (mask : UInt32) : Function :=
  retypedI32Function declaration #[(valueParam, .tobject)] result [
    .localGet valueParam,
    .call (.declaration ResidentBigNumeric.validateNaturalName),
    .localGet valueParam,
    .i32Const .uint32 0,
    .call (.declaration ResidentBigNumeric.naturalLowName),
    .i32Const .uint32 mask,
    .i32And]

/-- The bound proof is erased but remains a physical zero-valued parameter in
final LCNF. The conversion body is otherwise identical to `ofNat32Function`. -/
private def ofNatLT32Function (declaration : Name) (result : AbiKind)
    (mask : UInt32) : Function :=
  retypedI32Function declaration
    #[(valueParam, .tobject), (proofParam, .erased)] result [
      .localGet valueParam,
      .call (.declaration ResidentBigNumeric.validateNaturalName),
      .localGet valueParam,
      .i32Const .uint32 0,
      .call (.declaration ResidentBigNumeric.naturalLowName),
      .i32Const .uint32 mask,
      .i32And]

private def toNat32Function (declaration : Name) (param result : AbiKind) : Function :=
  retypedI32Function declaration #[(valueParam, param)] result [
    .localGet valueParam,
    .i32Const .uint32 0xffffffff,
    .i32And,
    .i32Const .uint32 0,
    .call (.declaration ResidentNumeric.makeNaturalName)]

private def widenI32Function (declaration : Name) (param result : AbiKind) : Function :=
  retypedI32Function declaration #[(valueParam, param)] result [
    .localGet valueParam,
    .i32Const .uint32 0xffffffff,
    .i32And]

private def extendI32Function (declaration : Name) (param result : AbiKind) : Function := {
  name := externalName declaration
  params := #[(valueParam, param)]
  results := #[result]
  locals := #[]
  body := [.localGet valueParam, .i64ExtendI32U result, .ret] }

private def decisionI32Function (declaration : Name) (param : AbiKind)
    (comparison : Instruction) : Function :=
  retypedI32Function declaration #[(leftParam, param), (rightParam, param)] .uint8 [
    .localGet leftParam,
    .localGet rightParam,
    comparison]

private def binaryI32Function (declaration : Name) (param : AbiKind)
    (operation : Instruction) : Function :=
  retypedI32Function declaration #[(leftParam, param), (rightParam, param)] param [
    .localGet leftParam,
    .localGet rightParam,
    operation]

private def binaryI64Function (declaration : Name) (param : AbiKind)
    (operation : Instruction) : Function :=
  retypedI64Function declaration #[(leftParam, param), (rightParam, param)] param [
    .localGet leftParam,
    .localGet rightParam,
    operation]

def shiftRightFunction : Function :=
  retypedI32Function `UInt16.shiftRight
    #[(leftParam, .uint16), (rightParam, .uint16)] .uint16 [
    .localGet leftParam,
    .localGet rightParam,
    .i32Const .uint32 16,
    .i32RemU,
    .i32ShrU]

def ofNatFunction : Function :=
  ofNat32Function `UInt16.ofNat .uint16 0xffff

def toUInt8Function : Function :=
  retypedI32Function `UInt16.toUInt8 #[(valueParam, .uint16)] .uint8 [
    .localGet valueParam,
    .i32Const .uint32 0xff,
    .i32And]

def landFunction : Function :=
  binaryI32Function `UInt16.land .uint16 .i32And

def xorFunction : Function :=
  binaryI32Function `UInt16.xor .uint16 .i32Xor

def shiftLeftFunction : Function :=
  retypedI32Function `UInt16.shiftLeft
    #[(leftParam, .uint16), (rightParam, .uint16)] .uint16 [
    .localGet leftParam,
    .localGet rightParam,
    .i32Const .uint32 16,
    .i32RemU,
    .i32Shl,
    .i32Const .uint32 0xffff,
    .i32And]

def lorFunction : Function :=
  binaryI32Function `UInt16.lor .uint16 .i32Or

def uint8OfNatFunction : Function :=
  ofNat32Function `UInt8.ofNat .uint8 0xff

/-- Proof arguments are erased by final LCNF, so the physical provider is the
same checked natural-to-byte conversion as `UInt8.ofNat`. -/
def uint8OfNatLTFunction : Function :=
  ofNatLT32Function `UInt8.ofNatLT .uint8 0xff

def uint8OfBitVecFunction : Function :=
  ofNat32Function `UInt8.ofBitVec .uint8 0xff

def uint8ToNatFunction : Function :=
  toNat32Function `UInt8.toNat .uint8 .tagged

def uint8ToBitVecFunction : Function :=
  toNat32Function `UInt8.toBitVec .uint8 .tobject

def uint8ToUInt32Function : Function :=
  widenI32Function `UInt8.toUInt32 .uint8 .uint32

def uint8ToUInt64Function : Function :=
  extendI32Function `UInt8.toUInt64 .uint8 .uint64

def uint8ToUSizeFunction : Function :=
  extendI32Function `UInt8.toUSize .uint8 .usize

def uint8DecEqFunction : Function :=
  decisionI32Function `UInt8.decEq .uint8 .i32Eq

def uint8DecLtFunction : Function :=
  decisionI32Function `UInt8.decLt .uint8 .i32LtU

def uint8DecLeFunction : Function :=
  retypedI32Function `UInt8.decLe
    #[(leftParam, .uint8), (rightParam, .uint8)] .uint8 [
      .localGet leftParam,
      .localGet rightParam,
      .i32LeU]

def uint8ShiftRightFunction : Function :=
  retypedI32Function `UInt8.shiftRight
    #[(leftParam, .uint8), (rightParam, .uint8)] .uint8 [
      .localGet leftParam,
      .localGet rightParam,
      .i32Const .uint32 8,
      .i32RemU,
      .i32ShrU]

def uint8LandFunction : Function :=
  binaryI32Function `UInt8.land .uint8 .i32And

def uint8LorFunction : Function :=
  binaryI32Function `UInt8.lor .uint8 .i32Or

def uint16ToNatFunction : Function :=
  toNat32Function `UInt16.toNat .uint16 .tagged

def uint16ToUInt32Function : Function :=
  widenI32Function `UInt16.toUInt32 .uint16 .uint32

def uint16ToUInt64Function : Function :=
  extendI32Function `UInt16.toUInt64 .uint16 .uint64

def uint32OfNatFunction : Function :=
  ofNat32Function `UInt32.ofNat .uint32 0xffffffff

/-- The erased proof leaves the same physical conversion as `UInt32.ofNat`. -/
def uint32OfNatLTFunction : Function :=
  ofNatLT32Function `UInt32.ofNatLT .uint32 0xffffffff

def uint32OfBitVecFunction : Function :=
  ofNat32Function `UInt32.ofBitVec .uint32 0xffffffff

/-- Floor log2 with Lean's `0 ↦ 0` convention. -/
def uint32Log2ClzFunction : Function := {
  (retypedI32Function `UInt32.log2Clz #[(valueParam, .uint32)] .uint32 [
    .i32Const .uint32 0,
    .localSet countLocal,
    .localGet valueParam,
    .i32Eqz,
    .ifElse
      []
      [.i32Const .uint32 31,
        .localGet valueParam,
        .i32Clz,
        .i32Sub,
        .localSet countLocal],
    .localGet countLocal]) with
    locals := #[(rawLocal, .uint32), (countLocal, .uint32),
      (savedScratchLocal, .uint64), (uint32ResultLocal, .uint32)] }

def uint32ToNatFunction : Function :=
  toNat32Function `UInt32.toNat .uint32 .tobject

private def narrowUInt32Function (declaration : Name) (result : AbiKind)
    (mask : UInt32) : Function :=
  retypedI32Function declaration #[(valueParam, .uint32)] result [
    .localGet valueParam,
    .i32Const .uint32 mask,
    .i32And]

def uint32ToUInt8Function : Function :=
  narrowUInt32Function `UInt32.toUInt8 .uint8 0xff

def uint32ToUInt16Function : Function :=
  narrowUInt32Function `UInt32.toUInt16 .uint16 0xffff

def uint32ToUInt64Function : Function :=
  extendI32Function `UInt32.toUInt64 .uint32 .uint64

def uint32ToUSizeFunction : Function :=
  extendI32Function `UInt32.toUSize .uint32 .usize

def uint32AddFunction : Function :=
  binaryI32Function `UInt32.add .uint32 .i32Add

def uint32SubFunction : Function :=
  binaryI32Function `UInt32.sub .uint32 .i32Sub

def uint32LandFunction : Function :=
  binaryI32Function `UInt32.land .uint32 .i32And

def uint32XorFunction : Function :=
  binaryI32Function `UInt32.xor .uint32 .i32Xor

def uint32ShiftRightFunction : Function :=
  binaryI32Function `UInt32.shiftRight .uint32 .i32ShrU

def uint32DecLtFunction : Function :=
  decisionI32Function `UInt32.decLt .uint32 .i32LtU

def uint32DecLeFunction : Function :=
  retypedI32Function `UInt32.decLe
    #[(leftParam, .uint32), (rightParam, .uint32)] .uint8 [
      .localGet leftParam,
      .localGet rightParam,
      .i32LeU]

def uint32ShiftLeftFunction : Function :=
  binaryI32Function `UInt32.shiftLeft .uint32 .i32Shl

def uint32LorFunction : Function :=
  binaryI32Function `UInt32.lor .uint32 .i32Or

def uint32MulFunction : Function :=
  binaryI32Function `UInt32.mul .uint32 .i32Mul

private def uint64OfNaturalFunction (declaration : Name) : Function := {
  name := externalName declaration
  params := #[(valueParam, .tobject)]
  results := #[.uint64]
  locals := #[]
  body := [
    .localGet valueParam,
    .call (.declaration ResidentBigNumeric.validateNaturalName),
    .localGet valueParam,
    .i32Const .uint32 0,
    .call (.declaration ResidentBigNumeric.naturalHighName),
    .i64ExtendI32U .uint64,
    .i64Const .uint64 32,
    .i64Shl,
    .localGet valueParam,
    .i32Const .uint32 0,
    .call (.declaration ResidentBigNumeric.naturalLowName),
    .i64ExtendI32U .uint64,
    .i64Or,
    .ret] }

def uint64OfBitVecFunction : Function :=
  uint64OfNaturalFunction `UInt64.ofBitVec

def uint64OfNatFunction : Function :=
  uint64OfNaturalFunction `UInt64.ofNat

private def narrowUInt64Function (declaration : Name) (result : AbiKind)
    (mask : UInt32) : Function :=
  retypedI32Function declaration #[(valueParam, .uint64)] result [
    .localGet valueParam,
    .i32WrapI64 .uint32,
    .i32Const .uint32 mask,
    .i32And]

def uint64ToUInt8Function : Function :=
  narrowUInt64Function `UInt64.toUInt8 .uint8 0xff

def uint64ToUInt16Function : Function :=
  narrowUInt64Function `UInt64.toUInt16 .uint16 0xffff

def uint64ToUSizeFunction : Function :=
  retypedI64Function `UInt64.toUSize #[(valueParam, .uint64)] .usize [
    .localGet valueParam]

def uint64ShiftLeftFunction : Function :=
  retypedI64Function `UInt64.shiftLeft
    #[(leftParam, .uint64), (rightParam, .uint64)] .uint64 [
      .localGet leftParam,
      .localGet rightParam,
      .i64Shl]

def uint64ShiftRightFunction : Function :=
  retypedI64Function `UInt64.shiftRight
    #[(leftParam, .uint64), (rightParam, .uint64)] .uint64 [
      .localGet leftParam,
      .localGet rightParam,
      .i64ShrU]

def uint64DecEqFunction : Function :=
  retypedI32Function `UInt64.decEq
    #[(leftParam, .uint64), (rightParam, .uint64)] .uint8 [
      .localGet leftParam,
      .localGet rightParam,
      .i64Eq]

def uint64AddFunction : Function :=
  binaryI64Function `UInt64.add .uint64 .i64Add

def uint64SubFunction : Function :=
  binaryI64Function `UInt64.sub .uint64 .i64Sub

def uint64LandFunction : Function :=
  binaryI64Function `UInt64.land .uint64 .i64And

def uint64LorFunction : Function :=
  retypedI64Function `UInt64.lor
    #[(leftParam, .uint64), (rightParam, .uint64)] .uint64 [
    .localGet leftParam,
    .localGet rightParam,
    .i64Or]

def uint64XorFunction : Function :=
  binaryI64Function `UInt64.xor .uint64 .i64Xor

def uint64ComplementFunction : Function :=
  retypedI64Function `UInt64.complement #[(valueParam, .uint64)] .uint64 [
    .localGet valueParam,
    .i64Const .uint64 0xffffffffffffffff,
    .i64Xor]

def uint64DecLtFunction : Function :=
  retypedI32Function `UInt64.decLt
    #[(leftParam, .uint64), (rightParam, .uint64)] .uint8 [
      .localGet leftParam,
      .localGet rightParam,
      .i64LtU]

def uint64MulFunction : Function :=
  binaryI64Function `UInt64.mul .uint64 .i64Mul

def uint64CtzFastFunction : Function :=
  retypedI64Function `UInt64.ctzFast #[(valueParam, .uint64)] .uint64 [
    .localGet valueParam,
    .i64Ctz]

/-- Lean specifies `a % 0 = a`, while core Wasm remainder traps at zero. -/
def uint64ModFunction : Function :=
  retypedI64Function `UInt64.mod
    #[(leftParam, .uint64), (rightParam, .uint64)] .uint64 [
    .localGet rightParam,
    .i64Eqz,
    .ifElse
      [.localGet leftParam,
        .localSet raw64Local]
      [.localGet leftParam,
        .localGet rightParam,
        .i64RemU,
        .localSet raw64Local],
    .localGet raw64Local]

def functions : Array Function := #[
  uint8OfBitVecFunction,
  uint8ToBitVecFunction,
  uint8OfNatFunction,
  uint8OfNatLTFunction,
  uint8ToNatFunction,
  uint8ToUInt32Function,
  uint8ToUInt64Function,
  uint8ToUSizeFunction,
  uint8DecEqFunction,
  uint8DecLtFunction,
  uint8DecLeFunction,
  uint8ShiftRightFunction,
  uint8LandFunction,
  uint8LorFunction,
  shiftRightFunction,
  ofNatFunction,
  toUInt8Function,
  uint16ToNatFunction,
  uint16ToUInt32Function,
  uint16ToUInt64Function,
  landFunction,
  xorFunction,
  shiftLeftFunction,
  lorFunction,
  uint32OfBitVecFunction,
  uint32OfNatFunction,
  uint32OfNatLTFunction,
  uint32Log2ClzFunction,
  uint32ToNatFunction,
  uint32ToUInt8Function,
  uint32ToUInt16Function,
  uint32ToUInt64Function,
  uint32ToUSizeFunction,
  uint32AddFunction,
  uint32SubFunction,
  uint32LandFunction,
  uint32XorFunction,
  uint32ShiftRightFunction,
  uint32DecLtFunction,
  uint32DecLeFunction,
  uint32ShiftLeftFunction,
  uint32LorFunction,
  uint32MulFunction,
  uint64OfBitVecFunction,
  uint64OfNatFunction,
  uint64ToUInt8Function,
  uint64ToUInt16Function,
  uint64ToUSizeFunction,
  uint64ShiftLeftFunction,
  uint64ShiftRightFunction,
  uint64DecEqFunction,
  uint64AddFunction,
  uint64SubFunction,
  uint64LandFunction,
  uint64LorFunction,
  uint64XorFunction,
  uint64ComplementFunction,
  uint64DecLtFunction,
  uint64MulFunction,
  uint64CtzFastFunction,
  uint64ModFunction]

private def expectedSignature? (declaration : Name) : Option Signature :=
  if #[`UInt8.decEq, `UInt8.decLt, `UInt8.decLe].contains declaration then
    some { params := #[.uint8, .uint8], results := #[.uint8] }
  else if #[`UInt8.ofBitVec, `UInt8.ofNat].contains declaration then
    some { params := #[.tobject], results := #[.uint8] }
  else if declaration == `UInt8.ofNatLT then
    some { params := #[.tobject, .erased], results := #[.uint8] }
  else if #[`UInt8.shiftRight, `UInt8.land, `UInt8.lor].contains declaration then
    some { params := #[.uint8, .uint8], results := #[.uint8] }
  else if declaration == `UInt8.toBitVec then
    some { params := #[.uint8], results := #[.tobject] }
  else if declaration == `UInt8.toNat then
    some { params := #[.uint8], results := #[.tobject] }
  else if declaration == `UInt8.toUInt32 then
    some { params := #[.uint8], results := #[.uint32] }
  else if declaration == `UInt8.toUInt64 then
    some { params := #[.uint8], results := #[.uint64] }
  else if declaration == `UInt8.toUSize then
    some { params := #[.uint8], results := #[.usize] }
  else if #[`UInt16.shiftRight, `UInt16.land, `UInt16.xor,
      `UInt16.shiftLeft, `UInt16.lor].contains declaration then
    some { params := #[.uint16, .uint16], results := #[.uint16] }
  else if declaration == `UInt16.ofNat then
    some { params := #[.tobject], results := #[.uint16] }
  else if declaration == `UInt16.toUInt8 then
    some { params := #[.uint16], results := #[.uint8] }
  else if declaration == `UInt16.toNat then
    some { params := #[.uint16], results := #[.tagged] }
  else if declaration == `UInt16.toUInt32 then
    some { params := #[.uint16], results := #[.uint32] }
  else if declaration == `UInt16.toUInt64 then
    some { params := #[.uint16], results := #[.uint64] }
  else if #[`UInt32.add, `UInt32.sub, `UInt32.land, `UInt32.xor,
      `UInt32.shiftRight, `UInt32.shiftLeft, `UInt32.lor,
      `UInt32.mul].contains declaration then
    some { params := #[.uint32, .uint32], results := #[.uint32] }
  else if #[`UInt32.decLt, `UInt32.decLe].contains declaration then
    some { params := #[.uint32, .uint32], results := #[.uint8] }
  else if #[`UInt32.ofBitVec, `UInt32.ofNat].contains declaration then
    some { params := #[.tobject], results := #[.uint32] }
  else if declaration == `UInt32.ofNatLT then
    some { params := #[.tobject, .erased], results := #[.uint32] }
  else if declaration == `UInt32.log2Clz then
    some { params := #[.uint32], results := #[.uint32] }
  else if declaration == `UInt32.toNat then
    some { params := #[.uint32], results := #[.tobject] }
  else if declaration == `UInt32.toUInt8 then
    some { params := #[.uint32], results := #[.uint8] }
  else if declaration == `UInt32.toUInt16 then
    some { params := #[.uint32], results := #[.uint16] }
  else if declaration == `UInt32.toUInt64 then
    some { params := #[.uint32], results := #[.uint64] }
  else if declaration == `UInt32.toUSize then
    some { params := #[.uint32], results := #[.usize] }
  else if #[`UInt64.shiftLeft, `UInt64.shiftRight, `UInt64.add, `UInt64.sub,
      `UInt64.land, `UInt64.lor, `UInt64.xor, `UInt64.mul,
      `UInt64.mod].contains declaration then
    some { params := #[.uint64, .uint64], results := #[.uint64] }
  else if declaration == `UInt64.complement then
    some { params := #[.uint64], results := #[.uint64] }
  else if declaration == `UInt64.ctzFast then
    some { params := #[.uint64], results := #[.uint64] }
  else if declaration == `UInt64.decEq || declaration == `UInt64.decLt then
    some { params := #[.uint64, .uint64], results := #[.uint8] }
  else if declaration == `UInt64.ofBitVec || declaration == `UInt64.ofNat then
    some { params := #[.tobject], results := #[.uint64] }
  else if declaration == `UInt64.toUInt8 then
    some { params := #[.uint64], results := #[.uint8] }
  else if declaration == `UInt64.toUInt16 then
    some { params := #[.uint64], results := #[.uint16] }
  else if declaration == `UInt64.toUSize then
    some { params := #[.uint64], results := #[.usize] }
  else none

private def functionSignature (function : Function) : Signature := {
  params := function.params.map (·.2)
  results := function.results }

private def sourceProviderCompatible (helper provider : Signature) : Bool :=
  helper.params == provider.params &&
    Fir.Wasm.kindsRefine helper.results provider.results

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

private def internalizeSelected (module : Module) (declarations : Array Name)
    (validate : Bool) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let needsFromNat := declarations.any fun declaration =>
    #[`UInt8.ofBitVec, `UInt8.ofNat, `UInt8.ofNatLT, `UInt16.ofNat,
      `UInt32.ofBitVec, `UInt32.ofNat, `UInt32.ofNatLT,
      `UInt64.ofBitVec, `UInt64.ofNat].contains declaration
  let needsToNat := declarations.any fun declaration =>
    #[`UInt8.toBitVec, `UInt8.toNat, `UInt16.toNat, `UInt32.toNat].contains declaration
  let needsHigh := declarations.contains `UInt64.ofBitVec ||
    declarations.contains `UInt64.ofNat
  let numericHelpers :=
    (if needsFromNat then
      #[ResidentBigNumeric.validateNaturalName, ResidentBigNumeric.naturalLowName]
    else #[]) ++
    (if needsHigh then #[ResidentBigNumeric.naturalHighName] else #[]) ++
    (if needsToNat then #[ResidentNumeric.makeNaturalName] else #[])
  if !numericHelpers.isEmpty then
    for name in numericHelpers do
      unless module.functions.any (·.name == name) do
        throw (.missingNumericHelper name)
  let selectedHelperNames := declarations.map externalName
  for name in selectedHelperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) || module.exports.contains name then
      throw (.reservedDeclaration name)
  for declaration in declarations do
    let imports := module.imports.filter (·.declaration? == some declaration)
    let definitions := module.functions.filter (·.name == declaration)
    unless imports.size + definitions.size == 1 do
      throw (.missingExternal declaration)
    let some expected := expectedSignature? declaration |
      throw (.incompatibleExternal declaration)
    let some helper := functions.find? (·.name == externalName declaration) |
      throw (.incompatibleExternal declaration)
    let helperSignature := functionSignature helper
    unless sourceProviderCompatible helperSignature expected do
      throw (.incompatibleExternal declaration)
    match imports[0]?, definitions[0]? with
    | some import_, none =>
        unless sourceProviderCompatible helperSignature import_.signature do
          throw (.incompatibleExternal declaration)
    | none, some function =>
        unless sourceProviderCompatible helperSignature (functionSignature function) do
          throw (.incompatibleExternal declaration)
    | _, _ => throw (.missingExternal declaration)
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
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

/-- Internalize exactly the supported fixed-width operations present. -/
def internalizeAvailable (module : Module) (validate : Bool := true) : Except LinkError Module :=
  let declarations := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration) ||
      module.functions.any (·.name == declaration)
  if declarations.isEmpty then pure module else internalizeSelected module declarations validate

private def impureType (kind : AbiKind) : Expr :=
  match kind with
  | .uint8 => LCNF.ImpureType.uint8
  | .uint16 => LCNF.ImpureType.uint16
  | .uint32 => LCNF.ImpureType.uint32
  | .uint64 => LCNF.ImpureType.uint64
  | .usize => LCNF.ImpureType.usize
  | .tagged => LCNF.ImpureType.tagged
  | .tobject => LCNF.ImpureType.tobject
  | .erased => LCNF.ImpureType.erased
  | _ => LCNF.ImpureType.tobject

private def externalTypesForSignature (signature : Signature) : ExternalTypes :=
  {
    params := signature.params.map impureType
    result := impureType signature.results[0]! }

private def externalTypes (declaration : Name) : ExternalTypes :=
  externalTypesForSignature (expectedSignature? declaration).get!

private def externalImport (declaration : Name) : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := (expectedSignature? declaration).get!
  externalTypes? := some (externalTypes declaration) }

private def usizeExternalImport (declaration : Name) : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := (ResidentUSize.expectedSignature? declaration).get!
  externalTypes? := some <| externalTypesForSignature
    (ResidentUSize.expectedSignature? declaration).get! }

def residentExampleModule : Except String Module := do
  let numeric ← ResidentBigNumeric.residentExampleModule
  let module : Module := {
    numeric with
    imports := numeric.imports ++ externalDeclarations.map externalImport ++
      ResidentUSize.externalDeclarations.map usizeExternalImport }
  let module ← internalizeSelected module externalDeclarations true
    |>.mapError fun error => s!"fixed-width: {repr error}"
  ResidentUSize.internalizeAvailable module
    |>.mapError fun error => s!"usize: {repr error}"

private def sourceUInt32OfNatFunction : Function := {
  name := `UInt32.ofNat
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [.i32Const .uint32 0, .ret] }

private def sourceUInt32OfNatCaller : Function := {
  name := `resident_fixed_width_source_definition
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[(uint32ResultLocal, .uint32)]
  body := [
    .localGet valueParam,
    .call (.declaration `UInt32.ofNat),
    .localSet uint32ResultLocal,
    .localGet uint32ResultLocal,
    .ret] }

/-- The same checked fixed-width implementation replaces a captured source
definition as well as an external import. -/
def sourceDefinitionExampleModule : Except String Module := do
  let numeric ← ResidentBigNumeric.residentExampleModule
  let module : Module := {
    numeric with
    functions := numeric.functions ++ #[
      sourceUInt32OfNatFunction, sourceUInt32OfNatCaller]
    exports := #[sourceUInt32OfNatCaller.name] }
  internalizeAvailable module
    |>.mapError fun error => s!"fixed-width source definition: {repr error}"

private def taggedUInt8ToNatSignature : Signature :=
  functionSignature uint8ToNatFunction

private def taggedUInt8ToNatExternalImport : Import := {
  key := .external `UInt8.toNat
  moduleName := "lean.extern"
  itemName := "UInt8.toNat"
  signature := taggedUInt8ToNatSignature
  externalTypes? := some <| externalTypesForSignature taggedUInt8ToNatSignature }

/-- Lean may capture `UInt8.toNat` with either its precise tagged result or
the ordinary object-family `tobject` boundary. The same stricter resident
helper is a valid implementation of both providers. -/
def taggedUInt8ToNatExampleModule : Except String Module := do
  let numeric ← ResidentBigNumeric.residentExampleModule
  let module : Module := {
    numeric with imports := numeric.imports.push taggedUInt8ToNatExternalImport }
  internalizeAvailable module
    |>.mapError fun error => s!"tagged UInt8.toNat: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <| (externalDeclarations ++
        ResidentUSize.externalDeclarations).map fun declaration =>
      Json.mkObj [
        ("sourceEntry", declaration.toString),
        ("entry", externalName declaration |>.toString)]),
    ("imports", Json.arr #[]),
    ("providers", Json.arr #["external", "source-definition"]),
    ("scalarStrategy", "direct-core-wasm"),
    ("structuredScalarLoops", 0),
    ("status", "generation-ready; W6 fixed-width contract proofs pending")]

private partial def instructionContains (target : Instruction) : Instruction → Bool
  | instruction@(.block _ body) | instruction@(.loop _ body) =>
      instruction == target || body.any (instructionContains target)
  | instruction@(.ifElse thenBody elseBody) =>
      instruction == target || thenBody.any (instructionContains target) ||
        elseBody.any (instructionContains target)
  | instruction => instruction == target

private partial def instructionContainsLoop : Instruction → Bool
  | .loop _ _ => true
  | .block _ body => body.any instructionContainsLoop
  | .ifElse thenBody elseBody =>
      thenBody.any instructionContainsLoop || elseBody.any instructionContainsLoop
  | _ => false

private def functionContainsLoop (function : Function) : Bool :=
  function.body.any instructionContainsLoop

#guard !functions.any functionContainsLoop
#guard !ResidentUSize.functions.any functionContainsLoop
#guard uint32Log2ClzFunction.body.any (instructionContains .i32Clz)
#guard uint32MulFunction.body.any (instructionContains .i32Mul)
#guard uint64MulFunction.body.any (instructionContains .i64Mul)
#guard uint64CtzFastFunction.body.any (instructionContains .i64Ctz)
#guard uint64ModFunction.body.any (instructionContains .i64RemU)
#guard ResidentUSize.modFunction.body.any (instructionContains .i64RemU)

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      externalDeclarations.all fun declaration =>
        module.exports.contains (externalName declaration) &&
      ResidentUSize.externalDeclarations.all fun declaration =>
        module.exports.contains (ResidentUSize.externalName declaration) &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

#guard match sourceDefinitionExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      module.functions.any (·.name == externalName `UInt32.ofNat) &&
      (module.functions.find? (·.name == sourceUInt32OfNatCaller.name)).any
        fun function => function.body.contains
          (.call (.declaration (externalName `UInt32.ofNat)) ) &&
      (Fir.Wasm.validateModule module).isOk &&
      (Fir.Wasm.Emit.encode module).isOk
  | .error _ => false

#guard match taggedUInt8ToNatExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      (module.functions.find? (·.name == externalName `UInt8.toNat)).any
        fun function => functionSignature function == taggedUInt8ToNatSignature &&
      (Fir.Wasm.validateModule module).isOk &&
      (Fir.Wasm.Emit.encode module).isOk
  | .error _ => false

end Fir.Wasm.Emit.ResidentFixedWidth
