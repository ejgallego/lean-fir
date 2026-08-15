import Fir.Wasm.Emit.ResidentAllocator

namespace Fir.Wasm.Emit.ResidentNumeric

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean
open Lean.Compiler

/-!
# Wasm-resident `prettyM` Nat/Int frontier

This generation slice internalizes the ten Nat/Int externals reachable from
`Std.Format.prettyM`.  It accepts every canonical wasm32 immediate and every
canonical one-limb W6 Natural/Integer representation.  A multi-limb numeric
object traps explicitly; extending the same helper surface to recursive limb
arithmetic is a later generation slice.

The helper is intentionally independent from its W6 refinement theorem.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | reservedDeclaration (name : Name)
  | missingExternal (name : Name)
  | incompatibleExternal (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def valueParam : FVarId := ⟨`value⟩
private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def invertParam : FVarId := ⟨`invertRight⟩
private def signParam : FVarId := ⟨`sign⟩
private def lowParam : FVarId := ⟨`low⟩
private def highParam : FVarId := ⟨`high⟩
private def leftLowParam : FVarId := ⟨`leftLow⟩
private def leftHighParam : FVarId := ⟨`leftHigh⟩
private def rightLowParam : FVarId := ⟨`rightLow⟩
private def rightHighParam : FVarId := ⟨`rightHigh⟩
private def kindParam : FVarId := ⟨`kind⟩
private def flagsParam : FVarId := ⟨`flags⟩
private def refCountParam : FVarId := ⟨`refCount⟩
private def markerParam : FVarId := ⟨`marker⟩
private def aux2Param : FVarId := ⟨`aux2⟩

private def addressLocal : FVarId := ⟨`address⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def resultLocal : FVarId := ⟨`result⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def leftLowLocal : FVarId := ⟨`leftLowValue⟩
private def leftHighLocal : FVarId := ⟨`leftHighValue⟩
private def rightLowLocal : FVarId := ⟨`rightLowValue⟩
private def rightHighLocal : FVarId := ⟨`rightHighValue⟩
private def leftSignLocal : FVarId := ⟨`leftSignValue⟩
private def rightSignLocal : FVarId := ⟨`rightSignValue⟩
private def lowLocal : FVarId := ⟨`lowValue⟩
private def highLocal : FVarId := ⟨`highValue⟩
private def naturalLocal : FVarId := ⟨`naturalValue⟩
private def integerLocal : FVarId := ⟨`integerValue⟩
private def carryLocal : FVarId := ⟨`carry⟩
private def borrowLocal : FVarId := ⟨`borrow⟩
private def compareLocal : FVarId := ⟨`compare⟩

def allocateOneLimbName : Name := `fir_numeric_allocate_one_limb
def validateNaturalName : Name := `fir_numeric_validate_natural
def naturalLowName : Name := `fir_numeric_natural_low
def naturalHighName : Name := `fir_numeric_natural_high
def validateIntegerName : Name := `fir_numeric_validate_integer
def integerSignName : Name := `fir_numeric_integer_sign
def integerLowName : Name := `fir_numeric_integer_low
def integerHighName : Name := `fir_numeric_integer_high
def compareMagnitudeName : Name := `fir_numeric_compare_magnitude
def makeNaturalName : Name := `fir_numeric_make_natural
def makeIntegerName : Name := `fir_numeric_make_integer
def naturalSumName : Name := `fir_numeric_natural_sum
def naturalDifferenceName : Name := `fir_numeric_natural_difference
def integerSumName : Name := `fir_numeric_integer_sum
def integerDifferenceName : Name := `fir_numeric_integer_difference
def integerCombineName : Name := `fir_numeric_integer_combine

def internalHelperNames : Array Name := #[
  allocateOneLimbName,
  validateNaturalName,
  naturalLowName,
  naturalHighName,
  validateIntegerName,
  integerSignName,
  integerLowName,
  integerHighName,
  compareMagnitudeName,
  makeNaturalName,
  makeIntegerName,
  naturalSumName,
  naturalDifferenceName,
  integerSumName,
  integerDifferenceName,
  integerCombineName]

/- The prettyM checkpoint historically requires this exact core inventory.
Keep that ratchet stable while allowing larger source closures to select the
additional generic operations below through `internalizeAvailable`. -/
def requiredExternalDeclarations : Array Name := #[
  `Int.ofNat,
  `Int.decLt,
  `Int.natAbs,
  `Int.sub,
  `Nat.add,
  `Nat.decEq,
  `Nat.sub,
  `Int.add,
  `Nat.decLt,
  `Nat.decLe]

def additionalExternalDeclarations : Array Name := #[
  `Int.negSucc,
  `Int.neg,
  `Int.decLe]

def externalDeclarations : Array Name :=
  requiredExternalDeclarations ++ additionalExternalDeclarations

def externalName (declaration : Name) : Name :=
  Name.mkSimple s!"fir_ext_{declaration.toString.replace "." "_"}"

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

private def requireHeapAddress (object : FVarId) : List Instruction :=
  trapWhenTrue [
    .localGet object,
    .i32Const .uint32 (u32 heapBase),
    .i32LtU] ++
  trapWhenTrue [
    .localGet object,
    .i32Const .uint32 (u32 (target.heapAlignment - 1)),
    .i32And]

private def requireCommonOneLimb (object : FVarId) : List Instruction :=
  requireHeapAddress object ++
  trapUnlessTrue (
    load32 object headerFlagsOffset ++
    [.i32Const .uint32 liveFlag, .i32And]) ++
  trapUnlessTrue (
    load32 object headerAllocationBytesOffset ++
    equalsConst .uint32 (u32 (headerBytes + target.semanticSlotBytes))) ++
  trapUnlessTrue (
    load32 object headerAux1Offset ++
    equalsConst .uint32 1) ++
  trapWhenTrue (load32 object headerAux3Offset)

private def requirePersistent (object : FVarId) : List Instruction :=
  trapUnlessTrue (
    load32 object headerFlagsOffset ++
    [.i32Const .uint32 persistentFlag, .i32And]) ++
  trapWhenTrue (load32 object headerRefCountOffset)

private def requireOrdinary (object : FVarId) : List Instruction :=
  trapWhenTrue (
    load32 object headerFlagsOffset ++
    [.i32Const .uint32 persistentFlag, .i32And]) ++
  trapUnlessTrue (
    load32 object headerRefCountOffset ++
    equalsConst .uint32 1)

private def oneLimbPayloadLow (object : FVarId) : List Instruction :=
  load32 object headerBytes

private def oneLimbPayloadHigh (object : FVarId) : List Instruction :=
  load32 object (headerBytes + 4)

private def naturalPromotedValidation : List Instruction :=
  requirePersistent valueParam ++
  trapUnlessTrue (
    oneLimbPayloadHigh valueParam ++
    [.i32Const .uint32 2147483648, .i32LtU]) ++
  oneLimbPayloadHigh valueParam ++
  equalsConst .uint32 0 ++
  [.ifElse
    (trapUnlessTrue (
      [.i32Const .uint32 (u32 maxImmediatePayload)] ++
      oneLimbPayloadLow valueParam ++
      [.i32LtU]))
    []]

private def naturalBigValidation : List Instruction :=
  requireOrdinary valueParam ++
  trapUnlessTrue (
    oneLimbPayloadHigh valueParam ++
    [.i32Const .uint32 2147483648, .i32LtU] ++
    equalsConst .uint32 0)

def validateNaturalFunction : Function := {
  name := validateNaturalName
  params := #[(valueParam, .tobject)]
  results := #[]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.ret]
      (requireCommonOneLimb valueParam ++
        trapUnlessTrue (
          load32 valueParam headerKindOffset ++
          equalsConst .uint32 ObjectKind.natural.code) ++
        load32 valueParam headerAux0Offset ++
        equalsConst .uint32 promotedTagMarker ++
        [Instruction.ifElse
          (naturalPromotedValidation ++ [.ret])
          (trapUnlessTrue (
              load32 valueParam headerAux0Offset ++
              equalsConst .uint32 bigNaturalMarker) ++
            naturalBigValidation ++
            [.ret])])] }

def naturalLowFunction : Function := {
  name := naturalLowName
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.localGet valueParam,
        .i32Const .uint32 1,
        .i32ShrU,
        .ret]
      (oneLimbPayloadLow valueParam ++ [.ret])] }

def naturalHighFunction : Function := {
  name := naturalHighName
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.i32Const .uint32 0, .ret]
      (oneLimbPayloadHigh valueParam ++ [.ret])] }

private def integerPromotedValidation : List Instruction :=
  requirePersistent valueParam ++
  trapWhenTrue (oneLimbPayloadHigh valueParam) ++
  trapUnlessTrue (
    oneLimbPayloadLow valueParam ++
    [.i32Const .uint32 2147483648, .i32LtU] ++
    equalsConst .uint32 0)

private def integerHeapValidation : List Instruction :=
  requireOrdinary valueParam ++
  trapUnlessTrue (
    load32 valueParam headerAux0Offset ++
    equalsConst .uint32 integerSignMagnitudeMarker) ++
  trapUnlessTrue (
    load32 valueParam headerAux2Offset ++
    [.i32Const .uint32 2, .i32LtU]) ++
  trapUnlessTrue (
    (oneLimbPayloadLow valueParam ++ equalsConst .uint32 0) ++
    (oneLimbPayloadHigh valueParam ++ equalsConst .uint32 0) ++
    [.i32And] ++
    equalsConst .uint32 0)

def validateIntegerFunction : Function := {
  name := validateIntegerName
  params := #[(valueParam, .tobject)]
  results := #[]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.ret]
      (requireCommonOneLimb valueParam ++
        load32 valueParam headerKindOffset ++
        equalsConst .uint32 ObjectKind.natural.code ++
        [Instruction.ifElse
          (trapUnlessTrue (
              load32 valueParam headerAux0Offset ++
              equalsConst .uint32 promotedTagMarker) ++
            integerPromotedValidation ++
            [.ret])
          (trapUnlessTrue (
              load32 valueParam headerKindOffset ++
              equalsConst .uint32 ObjectKind.integer.code) ++
            integerHeapValidation ++
            [.ret])])] }

def integerSignFunction : Function := {
  name := integerSignName
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.i32Const .uint32 0, .ret]
      (load32 valueParam headerKindOffset ++
        equalsConst .uint32 ObjectKind.natural.code ++
        [Instruction.ifElse
          [.i32Const .uint32 1, .ret]
          (load32 valueParam headerAux2Offset ++ [.ret])])] }

def integerLowFunction : Function := {
  name := integerLowName
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.localGet valueParam,
        .i32Const .uint32 1,
        .i32ShrU,
        .ret]
      (load32 valueParam headerKindOffset ++
        equalsConst .uint32 ObjectKind.natural.code ++
        [Instruction.ifElse
          ([.i32Const .uint32 0] ++
            oneLimbPayloadLow valueParam ++
            [.i32Sub, .ret])
          (oneLimbPayloadLow valueParam ++ [.ret])])] }

def integerHighFunction : Function := {
  name := integerHighName
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.i32Const .uint32 0, .ret]
      (load32 valueParam headerKindOffset ++
        equalsConst .uint32 ObjectKind.natural.code ++
        [Instruction.ifElse
          [.i32Const .uint32 0, .ret]
          (oneLimbPayloadHigh valueParam ++ [.ret])])] }

def allocateOneLimbFunction : Function := {
  name := allocateOneLimbName
  params := #[
    (kindParam, .uint32),
    (flagsParam, .uint32),
    (refCountParam, .uint32),
    (markerParam, .uint32),
    (aux2Param, .uint32),
    (lowParam, .uint32),
    (highParam, .uint32)]
  results := #[.uint32]
  locals := #[(addressLocal, .uint32)]
  body := [
    .i32Const .uint32 (u32 (headerBytes + target.semanticSlotBytes)),
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal,
    .localGet addressLocal,
    .localGet kindParam,
    .i32Store .uint32 (u32 headerKindOffset),
    .localGet addressLocal,
    .localGet flagsParam,
    .i32Store .uint32 (u32 headerFlagsOffset),
    .localGet addressLocal,
    .localGet refCountParam,
    .i32Store .uint32 (u32 headerRefCountOffset),
    .localGet addressLocal,
    .i32Const .uint32 (u32 (headerBytes + target.semanticSlotBytes)),
    .i32Store .uint32 (u32 headerAllocationBytesOffset),
    .localGet addressLocal,
    .localGet markerParam,
    .i32Store .uint32 (u32 headerAux0Offset),
    .localGet addressLocal,
    .i32Const .uint32 1,
    .i32Store .uint32 (u32 headerAux1Offset),
    .localGet addressLocal,
    .localGet aux2Param,
    .i32Store .uint32 (u32 headerAux2Offset),
    .localGet addressLocal,
    .i32Const .uint32 0,
    .i32Store .uint32 (u32 headerAux3Offset),
    .localGet addressLocal,
    .localGet lowParam,
    .i32Store .uint32 (u32 headerBytes),
    .localGet addressLocal,
    .localGet highParam,
    .i32Store .uint32 (u32 (headerBytes + 4)),
    .localGet addressLocal,
    .ret] }

private def callAllocateOneLimb (kind flags refCount marker aux2 : UInt32)
    (low high : FVarId) : List Instruction := [
  .i32Const .uint32 kind,
  .i32Const .uint32 flags,
  .i32Const .uint32 refCount,
  .i32Const .uint32 marker,
  .i32Const .uint32 aux2,
  .localGet low,
  .localGet high,
  .call (.declaration allocateOneLimbName)]

def makeNaturalFunction : Function := {
  name := makeNaturalName
  params := #[(lowParam, .uint32), (highParam, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet highParam,
    .i32Const .uint32 2147483648,
    .i32LtU,
    .ifElse
      ([.localGet highParam] ++
        equalsConst .uint32 0 ++
        [.ifElse
          ([.localGet lowParam,
            .i32Const .uint32 2147483648,
            .i32LtU,
            .ifElse
              [.localGet lowParam,
                .localGet lowParam,
                .i32Add,
                .i32Const .uint32 1,
                .i32Add,
                .ret]
              (callAllocateOneLimb ObjectKind.natural.code
                (persistentFlag + liveFlag) 0 promotedTagMarker 0
                lowParam highParam ++ [.ret])])
          (callAllocateOneLimb ObjectKind.natural.code
            (persistentFlag + liveFlag) 0 promotedTagMarker 0
            lowParam highParam ++ [.ret])])
      (callAllocateOneLimb ObjectKind.natural.code
        liveFlag 1 bigNaturalMarker 0 lowParam highParam ++ [.ret])] }

def makeIntegerFunction : Function := {
  name := makeIntegerName
  params := #[(signParam, .uint32), (lowParam, .uint32), (highParam, .uint32)]
  results := #[.uint32]
  locals := #[(rawLocal, .uint32)]
  body := [
    .localGet lowParam,
    .i32Const .uint32 0,
    .i32Eq,
    .localGet highParam,
    .i32Const .uint32 0,
    .i32Eq,
    .i32And,
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse
      ([.localGet signParam,
        .ifElse
          ([.localGet highParam] ++
            equalsConst .uint32 0 ++
            [.ifElse
              [.localGet lowParam,
                .i32Const .uint32 2147483649,
                .i32LtU,
                .ifElse
                  ([.i32Const .uint32 0,
                    .localGet lowParam,
                    .i32Sub,
                    .localSet rawLocal] ++
                    callAllocateOneLimb ObjectKind.natural.code
                      (persistentFlag + liveFlag) 0 promotedTagMarker 0
                      rawLocal highParam ++ [.ret])
                  (callAllocateOneLimb ObjectKind.integer.code
                    liveFlag 1 integerSignMagnitudeMarker 1
                    lowParam highParam ++ [.ret])]
              (callAllocateOneLimb ObjectKind.integer.code
                liveFlag 1 integerSignMagnitudeMarker 1
                lowParam highParam ++ [.ret])])
          ([.localGet highParam] ++
            equalsConst .uint32 0 ++
            [.ifElse
              [.localGet lowParam,
                .i32Const .uint32 2147483648,
                .i32LtU,
                .ifElse
                  [.localGet lowParam,
                    .localGet lowParam,
                    .i32Add,
                    .i32Const .uint32 1,
                    .i32Add,
                    .ret]
                  (callAllocateOneLimb ObjectKind.integer.code
                    liveFlag 1 integerSignMagnitudeMarker 0
                    lowParam highParam ++ [.ret])]
              (callAllocateOneLimb ObjectKind.integer.code
                liveFlag 1 integerSignMagnitudeMarker 0
                lowParam highParam ++ [.ret])])])
      [.i32Const .uint32 1, .ret]] }

def compareMagnitudeFunction : Function := {
  name := compareMagnitudeName
  params := #[
    (leftLowParam, .uint32),
    (leftHighParam, .uint32),
    (rightLowParam, .uint32),
    (rightHighParam, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet leftHighParam,
    .localGet rightHighParam,
    .i32Eq,
    .ifElse
      [.localGet leftLowParam,
        .localGet rightLowParam,
        .i32Eq,
        .ifElse
          [.i32Const .uint32 0, .ret]
          [.localGet leftLowParam,
            .localGet rightLowParam,
            .i32LtU,
            .ifElse
              [.i32Const .uint32 1, .ret]
              [.i32Const .uint32 2, .ret]]]
      [.localGet leftHighParam,
        .localGet rightHighParam,
        .i32LtU,
        .ifElse
          [.i32Const .uint32 1, .ret]
          [.i32Const .uint32 2, .ret]]] }

private def sumLocals : Array (FVarId × AbiKind) := #[
  (lowLocal, .uint32),
  (highLocal, .uint32),
  (carryLocal, .uint32)]

private def unsignedSumBody (make : Name) : List Instruction := [
  .localGet leftLowParam,
  .localGet rightLowParam,
  .i32Add,
  .localSet lowLocal,
  .localGet lowLocal,
  .localGet leftLowParam,
  .i32LtU,
  .localSet carryLocal,
  .localGet leftHighParam,
  .localGet rightHighParam,
  .i32Add,
  .localSet highLocal] ++
  trapWhenTrue [
    .localGet highLocal,
    .localGet leftHighParam,
    .i32LtU] ++ [
  .localGet highLocal,
  .localGet carryLocal,
  .i32Add,
  .localSet highLocal] ++
  trapWhenTrue [
    .localGet highLocal,
    .localGet carryLocal,
    .i32LtU] ++ [
  .localGet lowLocal,
  .localGet highLocal,
  .call (.declaration make),
  .ret]

def naturalSumFunction : Function := {
  name := naturalSumName
  params := #[
    (leftLowParam, .uint32),
    (leftHighParam, .uint32),
    (rightLowParam, .uint32),
    (rightHighParam, .uint32)]
  results := #[.uint32]
  locals := sumLocals
  body := unsignedSumBody makeNaturalName }

def integerSumFunction : Function := {
  name := integerSumName
  params := #[
    (signParam, .uint32),
    (leftLowParam, .uint32),
    (leftHighParam, .uint32),
    (rightLowParam, .uint32),
    (rightHighParam, .uint32)]
  results := #[.uint32]
  locals := sumLocals
  body := [
    .localGet leftLowParam,
    .localGet rightLowParam,
    .i32Add,
    .localSet lowLocal,
    .localGet lowLocal,
    .localGet leftLowParam,
    .i32LtU,
    .localSet carryLocal,
    .localGet leftHighParam,
    .localGet rightHighParam,
    .i32Add,
    .localSet highLocal] ++
    trapWhenTrue [
      .localGet highLocal,
      .localGet leftHighParam,
      .i32LtU] ++ [
    .localGet highLocal,
    .localGet carryLocal,
    .i32Add,
    .localSet highLocal] ++
    trapWhenTrue [
      .localGet highLocal,
      .localGet carryLocal,
      .i32LtU] ++ [
    .localGet signParam,
    .localGet lowLocal,
    .localGet highLocal,
    .call (.declaration makeIntegerName),
    .ret] }

private def unsignedDifferenceBody (make : Name)
    (prelude : List Instruction := []) : List Instruction :=
  prelude ++ [
    .localGet leftLowParam,
    .localGet rightLowParam,
    .i32LtU,
    .localSet borrowLocal,
    .localGet leftLowParam,
    .localGet rightLowParam,
    .i32Sub,
    .localSet lowLocal,
    .localGet leftHighParam,
    .localGet rightHighParam,
    .i32Sub,
    .localGet borrowLocal,
    .i32Sub,
    .localSet highLocal,
    .localGet lowLocal,
    .localGet highLocal,
    .call (.declaration make),
    .ret]

private def differenceLocals : Array (FVarId × AbiKind) := #[
  (lowLocal, .uint32),
  (highLocal, .uint32),
  (borrowLocal, .uint32)]

def naturalDifferenceFunction : Function := {
  name := naturalDifferenceName
  params := #[
    (leftLowParam, .uint32),
    (leftHighParam, .uint32),
    (rightLowParam, .uint32),
    (rightHighParam, .uint32)]
  results := #[.uint32]
  locals := differenceLocals
  body := unsignedDifferenceBody makeNaturalName }

def integerDifferenceFunction : Function := {
  name := integerDifferenceName
  params := #[
    (signParam, .uint32),
    (leftLowParam, .uint32),
    (leftHighParam, .uint32),
    (rightLowParam, .uint32),
    (rightHighParam, .uint32)]
  results := #[.uint32]
  locals := differenceLocals
  body := [
    .localGet leftLowParam,
    .localGet rightLowParam,
    .i32LtU,
    .localSet borrowLocal,
    .localGet leftLowParam,
    .localGet rightLowParam,
    .i32Sub,
    .localSet lowLocal,
    .localGet leftHighParam,
    .localGet rightHighParam,
    .i32Sub,
    .localGet borrowLocal,
    .i32Sub,
    .localSet highLocal,
    .localGet signParam,
    .localGet lowLocal,
    .localGet highLocal,
    .call (.declaration makeIntegerName),
    .ret] }

private def loadIntegerOperands : List Instruction := [
  .localGet leftParam,
  .call (.declaration validateIntegerName),
  .localGet rightParam,
  .call (.declaration validateIntegerName),
  .localGet leftParam,
  .call (.declaration integerLowName),
  .localSet leftLowLocal,
  .localGet leftParam,
  .call (.declaration integerHighName),
  .localSet leftHighLocal,
  .localGet rightParam,
  .call (.declaration integerLowName),
  .localSet rightLowLocal,
  .localGet rightParam,
  .call (.declaration integerHighName),
  .localSet rightHighLocal,
  .localGet leftParam,
  .call (.declaration integerSignName),
  .localSet leftSignLocal,
  .localGet rightParam,
  .call (.declaration integerSignName),
  .localSet rightSignLocal]

private def integerOperandLocals : Array (FVarId × AbiKind) := #[
  (leftLowLocal, .uint32),
  (leftHighLocal, .uint32),
  (rightLowLocal, .uint32),
  (rightHighLocal, .uint32),
  (leftSignLocal, .uint32),
  (rightSignLocal, .uint32),
  (compareLocal, .uint32)]

private def callIntegerDifference (sign leftLow leftHigh rightLow rightHigh :
    FVarId) : List Instruction := [
  .localGet sign,
  .localGet leftLow,
  .localGet leftHigh,
  .localGet rightLow,
  .localGet rightHigh,
  .call (.declaration integerDifferenceName),
  .ret]

def integerCombineFunction : Function := {
  name := integerCombineName
  params := #[
    (leftParam, .tobject),
    (rightParam, .tobject),
    (invertParam, .uint32)]
  results := #[.uint32]
  locals := integerOperandLocals
  body := loadIntegerOperands ++ [
    .localGet invertParam,
    .ifElse
      [.i32Const .uint32 1,
        .localGet rightSignLocal,
        .i32Sub,
        .localSet rightSignLocal]
      [],
    .localGet leftSignLocal,
    .localGet rightSignLocal,
    .i32Eq,
    .ifElse
      [.localGet leftSignLocal,
        .localGet leftLowLocal,
        .localGet leftHighLocal,
        .localGet rightLowLocal,
        .localGet rightHighLocal,
        .call (.declaration integerSumName),
        .ret]
      [.localGet leftLowLocal,
        .localGet leftHighLocal,
        .localGet rightLowLocal,
        .localGet rightHighLocal,
        .call (.declaration compareMagnitudeName),
        .localSet compareLocal,
        .localGet compareLocal,
        .ifElse
          [.localGet compareLocal,
            .i32Const .uint32 1,
            .i32Eq,
            .ifElse
              (callIntegerDifference rightSignLocal rightLowLocal
                rightHighLocal leftLowLocal leftHighLocal)
              (callIntegerDifference leftSignLocal leftLowLocal
                leftHighLocal rightLowLocal rightHighLocal)]
          [.i32Const .uint32 0,
            .i32Const .uint32 0,
            .i32Const .uint32 0,
            .call (.declaration makeIntegerName),
            .ret]]] }

private def retypeRawResult (result : AbiKind) : List Instruction := [
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

private def objectResultLocals : Array (FVarId × AbiKind) := #[
  (rawLocal, .uint32),
  (savedScratchLocal, .uint32),
  (resultLocal, .tobject)]

private def decisionResultLocals : Array (FVarId × AbiKind) := #[
  (rawLocal, .uint32),
  (savedScratchLocal, .uint32),
  (resultLocal, .uint8)]

def intOfNatFunction : Function := {
  name := externalName `Int.ofNat
  params := #[(valueParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals ++ #[
    (lowLocal, .uint32),
    (highLocal, .uint32)]
  body := [
    .localGet valueParam,
    .call (.declaration validateNaturalName),
    .localGet valueParam,
    .call (.declaration naturalLowName),
    .localSet lowLocal,
    .localGet valueParam,
    .call (.declaration naturalHighName),
    .localSet highLocal,
    .i32Const .uint32 0,
    .localGet lowLocal,
    .localGet highLocal,
    .call (.declaration makeIntegerName)] ++
    retypeRawResult .tobject }

def intNatAbsFunction : Function := {
  name := externalName `Int.natAbs
  params := #[(valueParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals ++ #[
    (lowLocal, .uint32),
    (highLocal, .uint32)]
  body := [
    .localGet valueParam,
    .call (.declaration validateIntegerName),
    .localGet valueParam,
    .call (.declaration integerLowName),
    .localSet lowLocal,
    .localGet valueParam,
    .call (.declaration integerHighName),
    .localSet highLocal,
    .localGet lowLocal,
    .localGet highLocal,
    .call (.declaration makeNaturalName)] ++
    retypeRawResult .tobject }

private def naturalOperandLocals : Array (FVarId × AbiKind) := #[
  (leftLowLocal, .uint32),
  (leftHighLocal, .uint32),
  (rightLowLocal, .uint32),
  (rightHighLocal, .uint32),
  (compareLocal, .uint32)]

private def loadNaturalOperands : List Instruction := [
  .localGet leftParam,
  .call (.declaration validateNaturalName),
  .localGet rightParam,
  .call (.declaration validateNaturalName),
  .localGet leftParam,
  .call (.declaration naturalLowName),
  .localSet leftLowLocal,
  .localGet leftParam,
  .call (.declaration naturalHighName),
  .localSet leftHighLocal,
  .localGet rightParam,
  .call (.declaration naturalLowName),
  .localSet rightLowLocal,
  .localGet rightParam,
  .call (.declaration naturalHighName),
  .localSet rightHighLocal]

def natAddFunction : Function := {
  name := externalName `Nat.add
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals ++ naturalOperandLocals
  body := loadNaturalOperands ++ [
    .localGet leftLowLocal,
    .localGet leftHighLocal,
    .localGet rightLowLocal,
    .localGet rightHighLocal,
    .call (.declaration naturalSumName)] ++
    retypeRawResult .tobject }

def natSubFunction : Function := {
  name := externalName `Nat.sub
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals ++ naturalOperandLocals
  body := loadNaturalOperands ++ [
    .localGet leftLowLocal,
    .localGet leftHighLocal,
    .localGet rightLowLocal,
    .localGet rightHighLocal,
    .call (.declaration compareMagnitudeName),
    .localSet compareLocal,
    .localGet compareLocal,
    .i32Const .uint32 2,
    .i32Eq,
    .ifElse
      [.localGet leftLowLocal,
        .localGet leftHighLocal,
        .localGet rightLowLocal,
        .localGet rightHighLocal,
        .call (.declaration naturalDifferenceName),
        .localSet rawLocal]
      [.i32Const .uint32 0,
        .i32Const .uint32 0,
        .call (.declaration makeNaturalName),
        .localSet rawLocal],
    .localGet rawLocal] ++
    retypeRawResult .tobject }

def intAddFunction : Function := {
  name := externalName `Int.add
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i32Const .uint32 0,
    .call (.declaration integerCombineName)] ++
    retypeRawResult .tobject }

def intSubFunction : Function := {
  name := externalName `Int.sub
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .i32Const .uint32 1,
    .call (.declaration integerCombineName)] ++
    retypeRawResult .tobject }

def intNegFunction : Function := {
  name := externalName `Int.neg
  params := #[(valueParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals
  body := [
    .i32Const .tobject 1,
    .localGet valueParam,
    .i32Const .uint32 1,
    .call (.declaration integerCombineName)] ++
    retypeRawResult .tobject }

/-- `Int.negSucc n` is `-(n + 1)`. Keeping this expression in terms of the
resident Nat and Int helpers lets the arbitrary-precision layer replace the
same calls without introducing a second constructor algorithm. -/
def intNegSuccFunction : Function := {
  name := externalName `Int.negSucc
  params := #[(valueParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals ++ #[(naturalLocal, .tobject), (integerLocal, .tobject)]
  body := [
    .localGet valueParam,
    .i32Const .tobject 3,
    .call (.declaration (externalName `Nat.add)),
    .localSet naturalLocal,
    .localGet naturalLocal,
    .call (.declaration (externalName `Int.ofNat)),
    .localSet integerLocal,
    .i32Const .tobject 1,
    .localGet integerLocal,
    .i32Const .uint32 1,
    .call (.declaration integerCombineName)] ++
    retypeRawResult .tobject }

inductive DecisionKind where
  | eq
  | lt
  | le

private def naturalDecisionBody (kind : DecisionKind) : List Instruction :=
  loadNaturalOperands ++ [
    .localGet leftLowLocal,
    .localGet leftHighLocal,
    .localGet rightLowLocal,
    .localGet rightHighLocal,
    .call (.declaration compareMagnitudeName),
    .localSet compareLocal] ++
  (match kind with
  | .eq =>
      [.localGet compareLocal,
        .i32Const .uint32 0,
        .i32Eq]
  | .lt =>
      [.localGet compareLocal,
        .i32Const .uint32 1,
        .i32Eq]
  | .le =>
      [.localGet compareLocal,
        .i32Const .uint32 2,
        .i32LtU]) ++
  retypeRawResult .uint8

def natDecEqFunction : Function := {
  name := externalName `Nat.decEq
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := decisionResultLocals ++ naturalOperandLocals
  body := naturalDecisionBody .eq }

def natDecLtFunction : Function := {
  name := externalName `Nat.decLt
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := decisionResultLocals ++ naturalOperandLocals
  body := naturalDecisionBody .lt }

def natDecLeFunction : Function := {
  name := externalName `Nat.decLe
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := decisionResultLocals ++ naturalOperandLocals
  body := naturalDecisionBody .le }

def intDecLtFunction : Function := {
  name := externalName `Int.decLt
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := decisionResultLocals ++ integerOperandLocals
  body := loadIntegerOperands ++ [
    .localGet leftSignLocal,
    .localGet rightSignLocal,
    .i32Eq,
    .ifElse
      [.localGet leftLowLocal,
        .localGet leftHighLocal,
        .localGet rightLowLocal,
        .localGet rightHighLocal,
        .call (.declaration compareMagnitudeName),
        .localSet compareLocal,
        .localGet leftSignLocal,
        .ifElse
          [.localGet compareLocal,
            .i32Const .uint32 2,
            .i32Eq,
            .localSet rawLocal]
          [.localGet compareLocal,
            .i32Const .uint32 1,
            .i32Eq,
            .localSet rawLocal]]
      [.localGet leftSignLocal,
        .localSet rawLocal],
    .localGet rawLocal] ++
    retypeRawResult .uint8 }

def intDecLeFunction : Function := {
  name := externalName `Int.decLe
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := decisionResultLocals ++ integerOperandLocals
  body := loadIntegerOperands ++ [
    .localGet leftSignLocal,
    .localGet rightSignLocal,
    .i32Eq,
    .ifElse
      [.localGet leftLowLocal,
        .localGet leftHighLocal,
        .localGet rightLowLocal,
        .localGet rightHighLocal,
        .call (.declaration compareMagnitudeName),
        .localSet compareLocal,
        .localGet leftSignLocal,
        .ifElse
          [.localGet compareLocal,
            .i32Const .uint32 1,
            .i32Eq,
            .i32Eqz,
            .localSet rawLocal]
          [.localGet compareLocal,
            .i32Const .uint32 2,
            .i32LtU,
            .localSet rawLocal]]
      [.localGet leftSignLocal,
        .localSet rawLocal],
    .localGet rawLocal] ++
    retypeRawResult .uint8 }

def externalFunctions : Array Function := #[
  intOfNatFunction,
  intNegSuccFunction,
  intNegFunction,
  intDecLtFunction,
  intDecLeFunction,
  intNatAbsFunction,
  intSubFunction,
  natAddFunction,
  natDecEqFunction,
  natSubFunction,
  intAddFunction,
  natDecLtFunction,
  natDecLeFunction]

def internalFunctions : Array Function := #[
  allocateOneLimbFunction,
  validateNaturalFunction,
  naturalLowFunction,
  naturalHighFunction,
  validateIntegerFunction,
  integerSignFunction,
  integerLowFunction,
  integerHighFunction,
  compareMagnitudeFunction,
  makeNaturalFunction,
  makeIntegerFunction,
  naturalSumFunction,
  naturalDifferenceFunction,
  integerSumFunction,
  integerDifferenceFunction,
  integerCombineFunction]

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
  if declaration == `Int.ofNat || declaration == `Int.negSucc ||
      declaration == `Int.neg || declaration == `Int.natAbs then
    some { params := #[.tobject], results := #[.tobject] }
  else if declaration == `Int.decLt || declaration == `Int.decLe ||
      declaration == `Nat.decEq ||
      declaration == `Nat.decLt || declaration == `Nat.decLe then
    some { params := #[.tobject, .tobject], results := #[.uint8] }
  else if declaration == `Int.sub || declaration == `Int.add ||
      declaration == `Nat.add || declaration == `Nat.sub then
    some { params := #[.tobject, .tobject], results := #[.tobject] }
  else
    none

def internalize (module : Module) (validate : Bool := true) : Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  for name in helperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) ||
        module.exports.contains name then
      throw (.reservedDeclaration name)
  for declaration in requiredExternalDeclarations do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.missingExternal declaration)
  let present := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
  for declaration in present do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.incompatibleExternal declaration)
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
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

/--
Install the resident numeric helper family while replacing only recognized
Nat/Int imports that are present in the source module. This keeps the strict
`prettyM` inventory gate above unchanged and gives larger source closures a
fail-closed, signature-checked incremental linker.
-/
def internalizeAvailable (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  for name in helperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) ||
        module.exports.contains name then
      throw (.reservedDeclaration name)
  let present := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
  for declaration in present do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.incompatibleExternal declaration)
    let some signature := expectedSignature? declaration |
      throw (.incompatibleExternal declaration)
    unless imports[0]!.signature == signature do
      throw (.incompatibleExternal declaration)
  let functions :=
    module.functions.map rewriteFunction ++ internalFunctions ++ externalFunctions
  let imports := module.imports.filter fun import_ =>
    match import_.declaration? with
    | some declaration => !present.contains declaration
    | none => true
  let result : Module := {
    module with
    imports
    functions
    exports := helperNames.foldl Fir.Wasm.addUnique module.exports }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

private def externalTypes? (declaration : Name) : Option ExternalTypes :=
  let nat := LCNF.ImpureType.tobject
  let int := LCNF.ImpureType.tobject
  let bool := LCNF.ImpureType.uint8
  if declaration == `Int.ofNat || declaration == `Int.negSucc then
    some { params := #[nat], result := int }
  else if declaration == `Int.neg then
    some { params := #[int], result := int }
  else if declaration == `Int.natAbs then
    some { params := #[int], result := nat }
  else if declaration == `Int.decLt || declaration == `Int.decLe then
    some { params := #[int, int], result := bool }
  else if declaration == `Int.add || declaration == `Int.sub then
    some { params := #[int, int], result := int }
  else if declaration == `Nat.decEq || declaration == `Nat.decLt ||
      declaration == `Nat.decLe then
    some { params := #[nat, nat], result := bool }
  else if declaration == `Nat.add || declaration == `Nat.sub then
    some { params := #[nat, nat], result := nat }
  else
    none

private def exampleExternalImport (declaration : Name) : Import :=
  let signature := (expectedSignature? declaration).get!
  {
    key := .external declaration
    moduleName := "lean.extern"
    itemName := declaration.toString
    signature
    externalTypes? := externalTypes? declaration }

def exampleModule : Module := {
  imports := externalDeclarations.map exampleExternalImport
  functions := #[]
  exports := #[]
  initializers := #[]
  runtimeOperations := #[] }

def residentExampleModule : Except String Module := do
  let module ← ResidentAllocator.install exampleModule
    |>.mapError fun error => s!"allocator: {repr error}"
  internalize module
    |>.mapError fun error => s!"numeric: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("sourceEntry", externalName `Nat.add |>.toString),
    ("entry", externalName `Nat.add |>.toString),
    ("params", Json.arr #["tobject", "tobject"]),
    ("result", "tobject"),
    ("closureDispatch", Json.arr #[]),
    ("closureDescriptors", Json.arr #[]),
    ("imports", Json.arr #[]),
    ("supportedMagnitudeBits", 64),
    ("multiLimbPolicy", "trap"),
    ("status", "generation-only; W6 numeric contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      externalHelperNames.all module.exports.contains &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentNumeric
