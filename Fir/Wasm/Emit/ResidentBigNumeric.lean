import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentBigNumeric

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean
open Lean.Compiler

/-!
# Wasm-resident arbitrary-precision `prettyM` Nat/Int frontier

This layer leaves the generation-ready one-limb helpers in `ResidentNumeric`
unchanged and installs a versioned helper set over the same W6 layouts. Calls
from compiler-generated functions are redirected to this layer; the stable
one-limb exports remain available for W6's current proof work.

The implementation accepts canonical immediate, promoted-tag, and
arbitrary-limb Natural/Integer values. Limb walkers are recursive until the
shared symbolic loop contract lands; replacing their control shape does not
change the public helper signatures or the W6 numeric layout.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | missingNumericHelper (name : Name)
  | reservedDeclaration (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def valueParam : FVarId := ⟨`value⟩
private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def flavorParam : FVarId := ⟨`flavor⟩
private def leftFlavorParam : FVarId := ⟨`leftFlavor⟩
private def rightFlavorParam : FVarId := ⟨`rightFlavor⟩
private def indexParam : FVarId := ⟨`index⟩
private def countParam : FVarId := ⟨`count⟩
private def signParam : FVarId := ⟨`sign⟩
private def invertParam : FVarId := ⟨`invertRight⟩
private def carryParam : FVarId := ⟨`carryIn⟩
private def borrowParam : FVarId := ⟨`borrowIn⟩
private def lastParam : FVarId := ⟨`lastNonzero⟩
private def resultParam : FVarId := ⟨`resultAddress⟩
private def storeCountParam : FVarId := ⟨`storeCount⟩

private def countLocal : FVarId := ⟨`countValue⟩
private def leftCountLocal : FVarId := ⟨`leftCount⟩
private def rightCountLocal : FVarId := ⟨`rightCount⟩
private def resultCountLocal : FVarId := ⟨`resultCount⟩
private def scaledLocal : FVarId := ⟨`scaledValue⟩
private def addressLocal : FVarId := ⟨`address⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def decisionResultLocal : FVarId := ⟨`decisionResult⟩
private def leftLowLocal : FVarId := ⟨`leftLowValue⟩
private def leftHighLocal : FVarId := ⟨`leftHighValue⟩
private def rightLowLocal : FVarId := ⟨`rightLowValue⟩
private def rightHighLocal : FVarId := ⟨`rightHighValue⟩
private def lowLocal : FVarId := ⟨`lowValue⟩
private def highLocal : FVarId := ⟨`highValue⟩
private def carryLocal : FVarId := ⟨`carryValue⟩
private def borrowLocal : FVarId := ⟨`borrowValue⟩
private def carryExtraLocal : FVarId := ⟨`carryExtra⟩
private def borrowExtraLocal : FVarId := ⟨`borrowExtra⟩
private def compareLocal : FVarId := ⟨`compareValue⟩
private def nextIndexLocal : FVarId := ⟨`nextIndex⟩
private def nextLastLocal : FVarId := ⟨`nextLast⟩
private def leftSignLocal : FVarId := ⟨`leftSign⟩
private def rightSignLocal : FVarId := ⟨`rightSign⟩
private def resultSignLocal : FVarId := ⟨`resultSign⟩
private def minuendLocal : FVarId := ⟨`minuend⟩
private def subtrahendLocal : FVarId := ⟨`subtrahend⟩

def validateCommonName : Name := `fir_big_numeric_validate_common
def validateNaturalName : Name := `fir_big_numeric_validate_natural
def validateIntegerName : Name := `fir_big_numeric_validate_integer
def naturalCountName : Name := `fir_big_numeric_natural_count
def naturalLowName : Name := `fir_big_numeric_natural_low
def naturalHighName : Name := `fir_big_numeric_natural_high
def integerCountName : Name := `fir_big_numeric_integer_count
def integerSignName : Name := `fir_big_numeric_integer_sign
def integerLowName : Name := `fir_big_numeric_integer_low
def integerHighName : Name := `fir_big_numeric_integer_high
def magnitudeCountName : Name := `fir_big_numeric_magnitude_count
def magnitudeLowName : Name := `fir_big_numeric_magnitude_low
def magnitudeHighName : Name := `fir_big_numeric_magnitude_high
def allocateName : Name := `fir_big_numeric_allocate
def compareAtName : Name := `fir_big_numeric_compare_at
def compareName : Name := `fir_big_numeric_compare
def copyFromName : Name := `fir_big_numeric_copy_from
def sumCarryFromName : Name := `fir_big_numeric_sum_carry_from
def writeSumFromName : Name := `fir_big_numeric_write_sum_from
def differenceScanFromName : Name := `fir_big_numeric_difference_scan_from
def writeDifferenceFromName : Name := `fir_big_numeric_write_difference_from
def differenceLowName : Name := `fir_big_numeric_difference_low
def differenceHighName : Name := `fir_big_numeric_difference_high
def integerCombineName : Name := `fir_big_numeric_integer_combine

def externalName (declaration : Name) : Name :=
  Name.mkSimple s!"fir_big_ext_{declaration.toString.replace "." "_"}"

def externalHelperNames : Array Name :=
  ResidentNumeric.externalDeclarations.map externalName

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

private def scale8 (source destination : FVarId) : List Instruction := [
  .localGet source,
  .localGet source,
  .i32Add,
  .localSet destination,
  .localGet destination,
  .localGet destination,
  .i32Add,
  .localSet destination,
  .localGet destination,
  .localGet destination,
  .i32Add,
  .localSet destination]

private def limbAddress (object index scaled : FVarId) :
    List Instruction :=
  scale8 index scaled ++ [
    .localGet object,
    .i32Const .uint32 (u32 headerBytes),
    .i32Add,
    .localGet scaled,
    .i32Add]

private def dynamicLimbLoad (object index scaled : FVarId) (offset : Nat) :
    List Instruction :=
  limbAddress object index scaled ++ [.i32Load .uint32 (u32 offset)]

private def dynamicLimbStore (object index scaled value : FVarId)
    (offset : Nat) : List Instruction :=
  limbAddress object index scaled ++ [
    .localGet value,
    .i32Store .uint32 (u32 offset)]

private def countFitsExtent : List Instruction := [
  .localGet countLocal,
  .i32Const .uint32 536870908,
  .i32LtU]

private def expectedExtent : List Instruction :=
  scale8 countLocal scaledLocal ++ [
    .i32Const .uint32 (u32 headerBytes),
    .localGet scaledLocal,
    .i32Add]

def validateCommonFunction : Function := {
  name := validateCommonName
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[
    (countLocal, .uint32),
    (scaledLocal, .uint32)]
  body :=
    requireHeapAddress valueParam ++
    trapUnlessTrue (
      load32 valueParam headerFlagsOffset ++
      [.i32Const .uint32 liveFlag, .i32And]) ++
    [
      .localGet valueParam,
      .i32Load .uint32 (u32 headerAux1Offset),
      .localSet countLocal] ++
    trapUnlessTrue [
      .localGet countLocal] ++
    trapUnlessTrue countFitsExtent ++
    trapUnlessTrue (
      load32 valueParam headerAllocationBytesOffset ++
      expectedExtent ++ [.i32Eq]) ++
    [
      .localGet countLocal,
      .ret] }

private def requirePersistent : List Instruction :=
  trapUnlessTrue (
    load32 valueParam headerFlagsOffset ++
    [.i32Const .uint32 persistentFlag, .i32And]) ++
  trapWhenTrue (load32 valueParam headerRefCountOffset)

private def requireOrdinary : List Instruction :=
  trapWhenTrue (
    load32 valueParam headerFlagsOffset ++
    [.i32Const .uint32 persistentFlag, .i32And]) ++
  trapUnlessTrue (
    load32 valueParam headerRefCountOffset ++
    equalsConst .uint32 1)

private def requireReservedZero : List Instruction :=
  trapWhenTrue (load32 valueParam headerAux2Offset) ++
  trapWhenTrue (load32 valueParam headerAux3Offset)

private def requireOneCount : List Instruction :=
  trapUnlessTrue [
    .localGet countLocal,
    .i32Const .uint32 1,
    .i32Eq]

private def loadTopLow : List Instruction := [
  .localGet valueParam,
  .localGet countLocal,
  .i32Const .uint32 1,
  .i32Sub,
  .call (.declaration naturalLowName)]

private def loadTopHigh : List Instruction := [
  .localGet valueParam,
  .localGet countLocal,
  .i32Const .uint32 1,
  .i32Sub,
  .call (.declaration naturalHighName)]

private def requireTopNonzero : List Instruction :=
  trapUnlessTrue (
    (loadTopLow ++ equalsConst .uint32 0) ++
    (loadTopHigh ++ equalsConst .uint32 0) ++
    [.i32And] ++
    equalsConst .uint32 0)

private def naturalPromotedValidation : List Instruction :=
  requireOneCount ++ requirePersistent ++ requireReservedZero ++
  trapUnlessTrue (
    loadTopHigh ++
    [.i32Const .uint32 2147483648, .i32LtU]) ++
  loadTopHigh ++ equalsConst .uint32 0 ++
  [.ifElse
    (trapUnlessTrue (
      [.i32Const .uint32 (u32 maxImmediatePayload)] ++
      loadTopLow ++
      [.i32LtU]))
    []]

private def naturalBigValidation : List Instruction :=
  requireOrdinary ++ requireReservedZero ++ requireTopNonzero ++
  [.localGet countLocal,
    .i32Const .uint32 1,
    .i32Eq,
    .ifElse
      (trapWhenTrue (
        loadTopHigh ++
        [.i32Const .uint32 2147483648, .i32LtU]))
      []]

def validateNaturalFunction : Function := {
  name := validateNaturalName
  params := #[(valueParam, .tobject)]
  results := #[]
  locals := #[(countLocal, .uint32)]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.ret]
      ([
        .localGet valueParam,
        .call (.declaration validateCommonName),
        .localSet countLocal] ++
        trapUnlessTrue (
          load32 valueParam headerKindOffset ++
          equalsConst .uint32 ObjectKind.natural.code) ++
        load32 valueParam headerAux0Offset ++
        equalsConst .uint32 promotedTagMarker ++
        [.ifElse
          (naturalPromotedValidation ++ [.ret])
          (trapUnlessTrue (
              load32 valueParam headerAux0Offset ++
              equalsConst .uint32 bigNaturalMarker) ++
            naturalBigValidation ++
            [.ret])])] }

private def integerPromotedValidation : List Instruction :=
  requireOneCount ++ requirePersistent ++ requireReservedZero ++
  trapWhenTrue loadTopHigh ++
  trapWhenTrue (
    loadTopLow ++
    [.i32Const .uint32 2147483648, .i32LtU])

private def requireCanonicalIntegerOneLimb : List Instruction := [
  .localGet countLocal,
  .i32Const .uint32 1,
  .i32Eq,
  .ifElse
    (loadTopHigh ++ equalsConst .uint32 0 ++
      [.ifElse
        (load32 valueParam headerAux2Offset ++
          [.ifElse
            (trapUnlessTrue (
              [.i32Const .uint32 2147483648] ++
              loadTopLow ++
              [.i32LtU]))
            (trapWhenTrue (
              loadTopLow ++
              [.i32Const .uint32 2147483648, .i32LtU]))])
        []])
    []]

private def integerHeapValidation : List Instruction :=
  requireOrdinary ++
  trapUnlessTrue (
    load32 valueParam headerAux0Offset ++
    equalsConst .uint32 integerSignMagnitudeMarker) ++
  trapUnlessTrue (
    load32 valueParam headerAux2Offset ++
    [.i32Const .uint32 2, .i32LtU]) ++
  trapWhenTrue (load32 valueParam headerAux3Offset) ++
  requireTopNonzero ++
  requireCanonicalIntegerOneLimb

def validateIntegerFunction : Function := {
  name := validateIntegerName
  params := #[(valueParam, .tobject)]
  results := #[]
  locals := #[(countLocal, .uint32)]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.ret]
      ([
        .localGet valueParam,
        .call (.declaration validateCommonName),
        .localSet countLocal] ++
        load32 valueParam headerKindOffset ++
        equalsConst .uint32 ObjectKind.natural.code ++
        [.ifElse
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

def naturalCountFunction : Function := {
  name := naturalCountName
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.i32Const .uint32 1, .ret]
      (load32 valueParam headerAux1Offset ++ [.ret])] }

private def naturalLimbFunction (name : Name) (offset : Nat) : Function := {
  name
  params := #[(valueParam, .tobject), (indexParam, .uint32)]
  results := #[.uint32]
  locals := #[(scaledLocal, .uint32)]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      ([.localGet indexParam,
        .i32Const .uint32 0,
        .i32Eq,
        .ifElse
          (if offset == 0 then
            [.localGet valueParam,
              .i32Const .uint32 1,
              .i32ShrU,
              .ret]
           else
            [.i32Const .uint32 0, .ret])
          [.i32Const .uint32 0, .ret]])
      (dynamicLimbLoad valueParam indexParam scaledLocal offset ++ [.ret])] }

def naturalLowFunction : Function := naturalLimbFunction naturalLowName 0
def naturalHighFunction : Function := naturalLimbFunction naturalHighName 4

def integerCountFunction : Function := {
  name := integerCountName
  params := #[(valueParam, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      [.i32Const .uint32 1, .ret]
      (load32 valueParam headerKindOffset ++
        equalsConst .uint32 ObjectKind.natural.code ++
        [.ifElse
          [.i32Const .uint32 1, .ret]
          (load32 valueParam headerAux1Offset ++ [.ret])])] }

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
        [.ifElse
          [.i32Const .uint32 1, .ret]
          (load32 valueParam headerAux2Offset ++ [.ret])])] }

private def integerLimbFunction (name : Name) (offset : Nat) : Function := {
  name
  params := #[(valueParam, .tobject), (indexParam, .uint32)]
  results := #[.uint32]
  locals := #[(scaledLocal, .uint32)]
  body := [
    .localGet valueParam,
    .i32Const .uint32 1,
    .i32And,
    .ifElse
      ([.localGet indexParam,
        .i32Const .uint32 0,
        .i32Eq,
        .ifElse
          (if offset == 0 then
            [.localGet valueParam,
              .i32Const .uint32 1,
              .i32ShrU,
              .ret]
           else
            [.i32Const .uint32 0, .ret])
          [.i32Const .uint32 0, .ret]])
      (load32 valueParam headerKindOffset ++
        equalsConst .uint32 ObjectKind.natural.code ++
        [.ifElse
          ([.localGet indexParam,
            .i32Const .uint32 0,
            .i32Eq,
            .ifElse
              (if offset == 0 then
                [.i32Const .uint32 0] ++
                dynamicLimbLoad valueParam indexParam scaledLocal 0 ++
                [.i32Sub, .ret]
               else
                [.i32Const .uint32 0, .ret])
              [.i32Const .uint32 0, .ret]])
          (dynamicLimbLoad valueParam indexParam scaledLocal offset ++ [.ret])])] }

def integerLowFunction : Function := integerLimbFunction integerLowName 0
def integerHighFunction : Function := integerLimbFunction integerHighName 4

def magnitudeCountFunction : Function := {
  name := magnitudeCountName
  params := #[(valueParam, .tobject), (flavorParam, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet flavorParam,
    .ifElse
      [.localGet valueParam, .call (.declaration integerCountName), .ret]
      [.localGet valueParam, .call (.declaration naturalCountName), .ret]] }

private def magnitudeLimbFunction (name natural integer : Name) : Function := {
  name
  params := #[
    (valueParam, .tobject),
    (flavorParam, .uint32),
    (indexParam, .uint32)]
  results := #[.uint32]
  locals := #[(countLocal, .uint32)]
  body := [
    .localGet valueParam,
    .localGet flavorParam,
    .call (.declaration magnitudeCountName),
    .localSet countLocal,
    .localGet indexParam,
    .localGet countLocal,
    .i32LtU,
    .ifElse
      [.localGet flavorParam,
        .ifElse
          [.localGet valueParam,
            .localGet indexParam,
            .call (.declaration integer),
            .ret]
          [.localGet valueParam,
            .localGet indexParam,
            .call (.declaration natural),
            .ret]]
      [.i32Const .uint32 0, .ret]] }

def magnitudeLowFunction : Function :=
  magnitudeLimbFunction magnitudeLowName naturalLowName integerLowName

def magnitudeHighFunction : Function :=
  magnitudeLimbFunction magnitudeHighName naturalHighName integerHighName

def validationAndAccessFunctions : Array Function := #[
  validateCommonFunction,
  naturalCountFunction,
  naturalLowFunction,
  naturalHighFunction,
  validateNaturalFunction,
  integerCountFunction,
  integerSignFunction,
  integerLowFunction,
  integerHighFunction,
  validateIntegerFunction,
  magnitudeCountFunction,
  magnitudeLowFunction,
  magnitudeHighFunction]

private def kindParam : FVarId := ⟨`kind⟩
private def markerParam : FVarId := ⟨`marker⟩

def allocateFunction : Function := {
  name := allocateName
  params := #[
    (kindParam, .uint32),
    (markerParam, .uint32),
    (signParam, .uint32),
    (countParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (scaledLocal, .uint32),
    (addressLocal, .uint32)]
  body :=
    trapUnlessTrue [
      .localGet countParam,
      .i32Const .uint32 536870908,
      .i32LtU] ++
    scale8 countParam scaledLocal ++ [
      .i32Const .uint32 (u32 headerBytes),
      .localGet scaledLocal,
      .i32Add,
      .call (.declaration ResidentAllocator.allocateName),
      .localSet addressLocal,
      .localGet addressLocal,
      .localGet kindParam,
      .i32Store .uint32 (u32 headerKindOffset),
      .localGet addressLocal,
      .i32Const .uint32 liveFlag,
      .i32Store .uint32 (u32 headerFlagsOffset),
      .localGet addressLocal,
      .i32Const .uint32 1,
      .i32Store .uint32 (u32 headerRefCountOffset),
      .localGet addressLocal,
      .i32Const .uint32 (u32 headerBytes),
      .localGet scaledLocal,
      .i32Add,
      .i32Store .uint32 (u32 headerAllocationBytesOffset),
      .localGet addressLocal,
      .localGet markerParam,
      .i32Store .uint32 (u32 headerAux0Offset),
      .localGet addressLocal,
      .localGet countParam,
      .i32Store .uint32 (u32 headerAux1Offset),
      .localGet addressLocal,
      .localGet signParam,
      .i32Store .uint32 (u32 headerAux2Offset),
      .localGet addressLocal,
      .i32Const .uint32 0,
      .i32Store .uint32 (u32 headerAux3Offset),
      .localGet addressLocal,
      .ret] }

private def loadMagnitude (object flavor index low high : FVarId) :
    List Instruction := [
  .localGet object,
  .localGet flavor,
  .localGet index,
  .call (.declaration magnitudeLowName),
  .localSet low,
  .localGet object,
  .localGet flavor,
  .localGet index,
  .call (.declaration magnitudeHighName),
  .localSet high]

def compareAtFunction : Function := {
  name := compareAtName
  params := #[
    (leftParam, .tobject),
    (leftFlavorParam, .uint32),
    (rightParam, .tobject),
    (rightFlavorParam, .uint32),
    (indexParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (leftLowLocal, .uint32),
    (leftHighLocal, .uint32),
    (rightLowLocal, .uint32),
    (rightHighLocal, .uint32)]
  body :=
    loadMagnitude leftParam leftFlavorParam indexParam
      leftLowLocal leftHighLocal ++
    loadMagnitude rightParam rightFlavorParam indexParam
      rightLowLocal rightHighLocal ++ [
      .localGet leftHighLocal,
      .localGet rightHighLocal,
      .i32Eq,
      .ifElse
        [.localGet leftLowLocal,
          .localGet rightLowLocal,
          .i32Eq,
          .ifElse
            [.localGet indexParam,
              .i32Const .uint32 0,
              .i32Eq,
              .ifElse
                [.i32Const .uint32 0, .ret]
                [.localGet leftParam,
                  .localGet leftFlavorParam,
                  .localGet rightParam,
                  .localGet rightFlavorParam,
                  .localGet indexParam,
                  .i32Const .uint32 1,
                  .i32Sub,
                  .call (.declaration compareAtName),
                  .ret]]
            [.localGet leftLowLocal,
              .localGet rightLowLocal,
              .i32LtU,
              .ifElse
                [.i32Const .uint32 1, .ret]
                [.i32Const .uint32 2, .ret]]]
        [.localGet leftHighLocal,
          .localGet rightHighLocal,
          .i32LtU,
          .ifElse
            [.i32Const .uint32 1, .ret]
            [.i32Const .uint32 2, .ret]]] }

def compareFunction : Function := {
  name := compareName
  params := #[
    (leftParam, .tobject),
    (leftFlavorParam, .uint32),
    (rightParam, .tobject),
    (rightFlavorParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (leftCountLocal, .uint32),
    (rightCountLocal, .uint32)]
  body := [
    .localGet leftParam,
    .localGet leftFlavorParam,
    .call (.declaration magnitudeCountName),
    .localSet leftCountLocal,
    .localGet rightParam,
    .localGet rightFlavorParam,
    .call (.declaration magnitudeCountName),
    .localSet rightCountLocal,
    .localGet leftCountLocal,
    .localGet rightCountLocal,
    .i32Eq,
    .ifElse
      [.localGet leftParam,
        .localGet leftFlavorParam,
        .localGet rightParam,
        .localGet rightFlavorParam,
        .localGet leftCountLocal,
        .i32Const .uint32 1,
        .i32Sub,
        .call (.declaration compareAtName),
        .ret]
      [.localGet leftCountLocal,
        .localGet rightCountLocal,
        .i32LtU,
        .ifElse
          [.i32Const .uint32 1, .ret]
          [.i32Const .uint32 2, .ret]]] }

def copyFromFunction : Function := {
  name := copyFromName
  params := #[
    (valueParam, .tobject),
    (flavorParam, .uint32),
    (resultParam, .uint32),
    (indexParam, .uint32),
    (countParam, .uint32)]
  results := #[]
  locals := #[
    (lowLocal, .uint32),
    (highLocal, .uint32),
    (scaledLocal, .uint32)]
  body := [
    .localGet indexParam,
    .localGet countParam,
    .i32Eq,
    .ifElse [.ret] []] ++
    loadMagnitude valueParam flavorParam indexParam lowLocal highLocal ++
    dynamicLimbStore resultParam indexParam scaledLocal lowLocal 0 ++
    dynamicLimbStore resultParam indexParam scaledLocal highLocal 4 ++ [
      .localGet valueParam,
      .localGet flavorParam,
      .localGet resultParam,
      .localGet indexParam,
      .i32Const .uint32 1,
      .i32Add,
      .localGet countParam,
      .call (.declaration copyFromName),
      .ret] }

private def sumStep : List Instruction :=
  loadMagnitude leftParam leftFlavorParam indexParam
      leftLowLocal leftHighLocal ++
  loadMagnitude rightParam rightFlavorParam indexParam
      rightLowLocal rightHighLocal ++ [
    .localGet leftLowLocal,
    .localGet rightLowLocal,
    .i32Add,
    .localSet lowLocal,
    .localGet lowLocal,
    .localGet leftLowLocal,
    .i32LtU,
    .localSet carryLocal,
    .localGet lowLocal,
    .localGet carryParam,
    .i32Add,
    .localSet lowLocal,
    .localGet lowLocal,
    .localGet carryParam,
    .i32LtU,
    .localSet carryExtraLocal,
    .localGet carryLocal,
    .localGet carryExtraLocal,
    .i32Add,
    .localSet carryLocal,
    .localGet leftHighLocal,
    .localGet rightHighLocal,
    .i32Add,
    .localSet highLocal,
    .localGet highLocal,
    .localGet leftHighLocal,
    .i32LtU,
    .localSet carryExtraLocal,
    .localGet highLocal,
    .localGet carryLocal,
    .i32Add,
    .localSet highLocal,
    .localGet highLocal,
    .localGet carryLocal,
    .i32LtU,
    .localSet carryLocal,
    .localGet carryLocal,
    .localGet carryExtraLocal,
    .i32Add,
    .localSet carryLocal]

private def arithmeticLocals : Array (FVarId × AbiKind) := #[
  (leftLowLocal, .uint32),
  (leftHighLocal, .uint32),
  (rightLowLocal, .uint32),
  (rightHighLocal, .uint32),
  (lowLocal, .uint32),
  (highLocal, .uint32),
  (carryLocal, .uint32),
  (carryExtraLocal, .uint32),
  (scaledLocal, .uint32)]

def sumCarryFromFunction : Function := {
  name := sumCarryFromName
  params := #[
    (leftParam, .tobject),
    (leftFlavorParam, .uint32),
    (rightParam, .tobject),
    (rightFlavorParam, .uint32),
    (indexParam, .uint32),
    (countParam, .uint32),
    (carryParam, .uint32)]
  results := #[.uint32]
  locals := arithmeticLocals
  body := [
    .localGet indexParam,
    .localGet countParam,
    .i32Eq,
    .ifElse [.localGet carryParam, .ret] []] ++
    sumStep ++ [
      .localGet leftParam,
      .localGet leftFlavorParam,
      .localGet rightParam,
      .localGet rightFlavorParam,
      .localGet indexParam,
      .i32Const .uint32 1,
      .i32Add,
      .localGet countParam,
      .localGet carryLocal,
      .call (.declaration sumCarryFromName),
      .ret] }

def writeSumFromFunction : Function := {
  name := writeSumFromName
  params := #[
    (leftParam, .tobject),
    (leftFlavorParam, .uint32),
    (rightParam, .tobject),
    (rightFlavorParam, .uint32),
    (resultParam, .uint32),
    (indexParam, .uint32),
    (countParam, .uint32),
    (carryParam, .uint32)]
  results := #[.uint32]
  locals := arithmeticLocals
  body := [
    .localGet indexParam,
    .localGet countParam,
    .i32Eq,
    .ifElse [.localGet carryParam, .ret] []] ++
    sumStep ++
    dynamicLimbStore resultParam indexParam scaledLocal lowLocal 0 ++
    dynamicLimbStore resultParam indexParam scaledLocal highLocal 4 ++ [
      .localGet leftParam,
      .localGet leftFlavorParam,
      .localGet rightParam,
      .localGet rightFlavorParam,
      .localGet resultParam,
      .localGet indexParam,
      .i32Const .uint32 1,
      .i32Add,
      .localGet countParam,
      .localGet carryLocal,
      .call (.declaration writeSumFromName),
      .ret] }

private def differenceStep : List Instruction :=
  loadMagnitude leftParam leftFlavorParam indexParam
      leftLowLocal leftHighLocal ++
  loadMagnitude rightParam rightFlavorParam indexParam
      rightLowLocal rightHighLocal ++ [
    .localGet leftLowLocal,
    .localGet rightLowLocal,
    .i32Sub,
    .localSet lowLocal,
    .localGet leftLowLocal,
    .localGet rightLowLocal,
    .i32LtU,
    .localSet borrowLocal,
    .localGet lowLocal,
    .localGet borrowParam,
    .i32LtU,
    .localSet borrowExtraLocal,
    .localGet lowLocal,
    .localGet borrowParam,
    .i32Sub,
    .localSet lowLocal,
    .localGet borrowLocal,
    .localGet borrowExtraLocal,
    .i32Add,
    .localSet borrowLocal,
    .localGet leftHighLocal,
    .localGet rightHighLocal,
    .i32Sub,
    .localSet highLocal,
    .localGet leftHighLocal,
    .localGet rightHighLocal,
    .i32LtU,
    .localSet borrowExtraLocal,
    .localGet highLocal,
    .localGet borrowLocal,
    .i32LtU,
    .localSet carryExtraLocal,
    .localGet highLocal,
    .localGet borrowLocal,
    .i32Sub,
    .localSet highLocal,
    .localGet borrowExtraLocal,
    .localGet carryExtraLocal,
    .i32Add,
    .localSet borrowLocal]

private def differenceLocals : Array (FVarId × AbiKind) :=
  arithmeticLocals ++ #[
    (borrowLocal, .uint32),
    (borrowExtraLocal, .uint32),
    (nextLastLocal, .uint32)]

def differenceScanFromFunction : Function := {
  name := differenceScanFromName
  params := #[
    (leftParam, .tobject),
    (leftFlavorParam, .uint32),
    (rightParam, .tobject),
    (rightFlavorParam, .uint32),
    (indexParam, .uint32),
    (countParam, .uint32),
    (borrowParam, .uint32),
    (lastParam, .uint32)]
  results := #[.uint32]
  locals := differenceLocals
  body := [
    .localGet indexParam,
    .localGet countParam,
    .i32Eq,
    .ifElse
      (trapWhenTrue [.localGet borrowParam] ++
        [.localGet lastParam, .ret])
      []] ++
    differenceStep ++ [
      .localGet lowLocal,
      .i32Const .uint32 0,
      .i32Eq,
      .localGet highLocal,
      .i32Const .uint32 0,
      .i32Eq,
      .i32And,
      .ifElse
        [.localGet lastParam, .localSet nextLastLocal]
        [.localGet indexParam,
          .i32Const .uint32 1,
          .i32Add,
          .localSet nextLastLocal],
      .localGet leftParam,
      .localGet leftFlavorParam,
      .localGet rightParam,
      .localGet rightFlavorParam,
      .localGet indexParam,
      .i32Const .uint32 1,
      .i32Add,
      .localGet countParam,
      .localGet borrowLocal,
      .localGet nextLastLocal,
      .call (.declaration differenceScanFromName),
      .ret] }

def writeDifferenceFromFunction : Function := {
  name := writeDifferenceFromName
  params := #[
    (leftParam, .tobject),
    (leftFlavorParam, .uint32),
    (rightParam, .tobject),
    (rightFlavorParam, .uint32),
    (resultParam, .uint32),
    (indexParam, .uint32),
    (countParam, .uint32),
    (storeCountParam, .uint32),
    (borrowParam, .uint32)]
  results := #[]
  locals := differenceLocals
  body := [
    .localGet indexParam,
    .localGet countParam,
    .i32Eq,
    .ifElse (trapWhenTrue [.localGet borrowParam] ++ [.ret]) []] ++
    differenceStep ++ [
      .localGet indexParam,
      .localGet storeCountParam,
      .i32LtU,
      .ifElse
        (dynamicLimbStore resultParam indexParam scaledLocal lowLocal 0 ++
          dynamicLimbStore resultParam indexParam scaledLocal highLocal 4)
        [],
      .localGet leftParam,
      .localGet leftFlavorParam,
      .localGet rightParam,
      .localGet rightFlavorParam,
      .localGet resultParam,
      .localGet indexParam,
      .i32Const .uint32 1,
      .i32Add,
      .localGet countParam,
      .localGet storeCountParam,
      .localGet borrowLocal,
      .call (.declaration writeDifferenceFromName),
      .ret] }

def differenceLowFunction : Function := {
  name := differenceLowName
  params := #[
    (leftParam, .tobject),
    (leftFlavorParam, .uint32),
    (rightParam, .tobject),
    (rightFlavorParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (leftLowLocal, .uint32),
    (rightLowLocal, .uint32)]
  body := [
    .localGet leftParam,
    .localGet leftFlavorParam,
    .i32Const .uint32 0,
    .call (.declaration magnitudeLowName),
    .localSet leftLowLocal,
    .localGet rightParam,
    .localGet rightFlavorParam,
    .i32Const .uint32 0,
    .call (.declaration magnitudeLowName),
    .localSet rightLowLocal,
    .localGet leftLowLocal,
    .localGet rightLowLocal,
    .i32Sub,
    .ret] }

def differenceHighFunction : Function := {
  name := differenceHighName
  params := #[
    (leftParam, .tobject),
    (leftFlavorParam, .uint32),
    (rightParam, .tobject),
    (rightFlavorParam, .uint32)]
  results := #[.uint32]
  locals := #[
    (leftLowLocal, .uint32),
    (leftHighLocal, .uint32),
    (rightLowLocal, .uint32),
    (rightHighLocal, .uint32),
    (borrowLocal, .uint32)]
  body := [
      .localGet leftParam,
      .localGet leftFlavorParam,
      .i32Const .uint32 0,
      .call (.declaration magnitudeLowName),
      .localSet leftLowLocal,
      .localGet leftParam,
      .localGet leftFlavorParam,
      .i32Const .uint32 0,
      .call (.declaration magnitudeHighName),
      .localSet leftHighLocal,
      .localGet rightParam,
      .localGet rightFlavorParam,
      .i32Const .uint32 0,
      .call (.declaration magnitudeLowName),
      .localSet rightLowLocal,
      .localGet rightParam,
      .localGet rightFlavorParam,
      .i32Const .uint32 0,
      .call (.declaration magnitudeHighName),
      .localSet rightHighLocal,
      .localGet leftLowLocal,
      .localGet rightLowLocal,
      .i32LtU,
      .localSet borrowLocal,
      .localGet leftHighLocal,
      .localGet rightHighLocal,
      .i32Sub,
      .localGet borrowLocal,
      .i32Sub,
      .ret] }

def limbFunctions : Array Function := #[
  allocateFunction,
  compareAtFunction,
  compareFunction,
  copyFromFunction,
  sumCarryFromFunction,
  writeSumFromFunction,
  differenceScanFromFunction,
  writeDifferenceFromFunction,
  differenceLowFunction,
  differenceHighFunction]

private def retypeRawResult (result : AbiKind) (resultLocal : FVarId) :
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

private def objectResultLocals : Array (FVarId × AbiKind) := #[
  (rawLocal, .uint32),
  (savedScratchLocal, .uint32),
  (objectResultLocal, .tobject)]

private def decisionResultLocals : Array (FVarId × AbiKind) := #[
  (rawLocal, .uint32),
  (savedScratchLocal, .uint32),
  (decisionResultLocal, .uint8)]

private def loadCount (object flavor destination : FVarId) :
    List Instruction := [
  .localGet object,
  .localGet flavor,
  .call (.declaration magnitudeCountName),
  .localSet destination]

private def loadFirstMagnitude (object flavor low high : FVarId) :
    List Instruction := [
  .localGet object,
  .localGet flavor,
  .i32Const .uint32 0,
  .call (.declaration magnitudeLowName),
  .localSet low,
  .localGet object,
  .localGet flavor,
  .i32Const .uint32 0,
  .call (.declaration magnitudeHighName),
  .localSet high]

private def allocateNatural (count : FVarId) : List Instruction := [
  .i32Const .uint32 ObjectKind.natural.code,
  .i32Const .uint32 bigNaturalMarker,
  .i32Const .uint32 0,
  .localGet count,
  .call (.declaration allocateName)]

private def allocateInteger (sign count : FVarId) : List Instruction := [
  .i32Const .uint32 ObjectKind.integer.code,
  .i32Const .uint32 integerSignMagnitudeMarker,
  .localGet sign,
  .localGet count,
  .call (.declaration allocateName)]

private def allocateIntegerConst (sign : UInt32) (count : FVarId) :
    List Instruction := [
  .i32Const .uint32 ObjectKind.integer.code,
  .i32Const .uint32 integerSignMagnitudeMarker,
  .i32Const .uint32 sign,
  .localGet count,
  .call (.declaration allocateName)]

private def storeConstantLimbPart (object index scaled : FVarId)
    (value : UInt32) (offset : Nat) : List Instruction :=
  limbAddress object index scaled ++ [
    .i32Const .uint32 value,
    .i32Store .uint32 (u32 offset)]

private def copyInto (source flavor result count : FVarId) :
    List Instruction := [
  .localGet source,
  .localGet flavor,
  .localGet result,
  .i32Const .uint32 0,
  .localGet count,
  .call (.declaration copyFromName)]

private def maxCounts : List Instruction := [
  .localGet leftCountLocal,
  .localGet rightCountLocal,
  .i32LtU,
  .ifElse
    [.localGet rightCountLocal, .localSet countLocal]
    [.localGet leftCountLocal, .localSet countLocal]]

private def callSumCarry : List Instruction := [
  .localGet leftParam,
  .localGet leftFlavorParam,
  .localGet rightParam,
  .localGet rightFlavorParam,
  .i32Const .uint32 0,
  .localGet countLocal,
  .i32Const .uint32 0,
  .call (.declaration sumCarryFromName),
  .localSet carryLocal,
  .localGet countLocal,
  .localGet carryLocal,
  .i32Add,
  .localSet resultCountLocal]

private def writeSum (result : FVarId) : List Instruction := [
  .localGet leftParam,
  .localGet leftFlavorParam,
  .localGet rightParam,
  .localGet rightFlavorParam,
  .localGet result,
  .i32Const .uint32 0,
  .localGet countLocal,
  .i32Const .uint32 0,
  .call (.declaration writeSumFromName),
  .localSet carryExtraLocal] ++
  trapUnlessTrue [
    .localGet carryExtraLocal,
    .localGet carryLocal,
    .i32Eq] ++ [
  .localGet carryLocal,
  .ifElse
    (storeConstantLimbPart result countLocal scaledLocal 1 0 ++
      storeConstantLimbPart result countLocal scaledLocal 0 4)
    []]

private def callOneLimbNaturalSum : List Instruction :=
  loadFirstMagnitude leftParam leftFlavorParam leftLowLocal leftHighLocal ++
  loadFirstMagnitude rightParam rightFlavorParam rightLowLocal rightHighLocal ++ [
    .localGet leftLowLocal,
    .localGet leftHighLocal,
    .localGet rightLowLocal,
    .localGet rightHighLocal,
    .call (.declaration ResidentNumeric.naturalSumName)]

private def callOneLimbIntegerSum (sign : FVarId) : List Instruction :=
  loadFirstMagnitude leftParam leftFlavorParam leftLowLocal leftHighLocal ++
  loadFirstMagnitude rightParam rightFlavorParam rightLowLocal rightHighLocal ++ [
    .localGet sign,
    .localGet leftLowLocal,
    .localGet leftHighLocal,
    .localGet rightLowLocal,
    .localGet rightHighLocal,
    .call (.declaration ResidentNumeric.integerSumName)]

private def callDifferencePart (name : Name) (left leftFlavor right rightFlavor :
    FVarId) : List Instruction := [
  .localGet left,
  .localGet leftFlavor,
  .localGet right,
  .localGet rightFlavor,
  .call (.declaration name)]

def intOfNatFunction : Function := {
  name := externalName `Int.ofNat
  params := #[(valueParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals ++ #[
    (flavorParam, .uint32),
    (countLocal, .uint32),
    (lowLocal, .uint32),
    (highLocal, .uint32)]
  body := [
    .i32Const .uint32 0,
    .localSet flavorParam,
    .localGet valueParam,
    .call (.declaration validateNaturalName)] ++
    loadCount valueParam flavorParam countLocal ++ [
    .localGet countLocal,
    .i32Const .uint32 1,
    .i32Eq,
    .ifElse
      (loadFirstMagnitude valueParam flavorParam lowLocal highLocal ++ [
        .i32Const .uint32 0,
        .localGet lowLocal,
        .localGet highLocal,
        .call (.declaration ResidentNumeric.makeIntegerName)] ++
        retypeRawResult .tobject objectResultLocal)
      (allocateIntegerConst 0 countLocal ++ [
        .localSet rawLocal] ++
        copyInto valueParam flavorParam rawLocal countLocal ++ [
        .localGet rawLocal] ++
        retypeRawResult .tobject objectResultLocal)] }

def intNatAbsFunction : Function := {
  name := externalName `Int.natAbs
  params := #[(valueParam, .tobject)]
  results := #[.tobject]
  locals := objectResultLocals ++ #[
    (flavorParam, .uint32),
    (countLocal, .uint32),
    (lowLocal, .uint32),
    (highLocal, .uint32)]
  body := [
    .i32Const .uint32 1,
    .localSet flavorParam,
    .localGet valueParam,
    .call (.declaration validateIntegerName)] ++
    loadCount valueParam flavorParam countLocal ++ [
    .localGet countLocal,
    .i32Const .uint32 1,
    .i32Eq,
    .ifElse
      (loadFirstMagnitude valueParam flavorParam lowLocal highLocal ++ [
        .localGet lowLocal,
        .localGet highLocal,
        .call (.declaration ResidentNumeric.makeNaturalName)] ++
        retypeRawResult .tobject objectResultLocal)
      (allocateNatural countLocal ++ [
        .localSet rawLocal] ++
        copyInto valueParam flavorParam rawLocal countLocal ++ [
        .localGet rawLocal] ++
        retypeRawResult .tobject objectResultLocal)] }

private def naturalArithmeticLocals : Array (FVarId × AbiKind) :=
  objectResultLocals ++ #[
    (leftFlavorParam, .uint32),
    (rightFlavorParam, .uint32),
    (leftCountLocal, .uint32),
    (rightCountLocal, .uint32),
    (countLocal, .uint32),
    (resultCountLocal, .uint32),
    (leftLowLocal, .uint32),
    (leftHighLocal, .uint32),
    (rightLowLocal, .uint32),
    (rightHighLocal, .uint32),
    (carryLocal, .uint32),
    (carryExtraLocal, .uint32),
    (scaledLocal, .uint32),
    (compareLocal, .uint32)]

private def validateNaturalsAndCounts : List Instruction := [
  .localGet leftParam,
  .call (.declaration validateNaturalName),
  .localGet rightParam,
  .call (.declaration validateNaturalName)] ++
  loadCount leftParam leftFlavorParam leftCountLocal ++
  loadCount rightParam rightFlavorParam rightCountLocal

def natAddFunction : Function := {
  name := externalName `Nat.add
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.tobject]
  locals := naturalArithmeticLocals
  body := [
    .i32Const .uint32 0,
    .localSet leftFlavorParam,
    .i32Const .uint32 0,
    .localSet rightFlavorParam] ++
    validateNaturalsAndCounts ++ maxCounts ++ callSumCarry ++ [
    .localGet resultCountLocal,
    .i32Const .uint32 1,
    .i32Eq,
    .ifElse
      (callOneLimbNaturalSum ++
        retypeRawResult .tobject objectResultLocal)
      (allocateNatural resultCountLocal ++ [
        .localSet rawLocal] ++
        writeSum rawLocal ++ [
        .localGet rawLocal] ++
        retypeRawResult .tobject objectResultLocal)] }

private def scanDifference (left leftFlavor right rightFlavor total : FVarId) :
    List Instruction := [
  .localGet left,
  .localGet leftFlavor,
  .localGet right,
  .localGet rightFlavor,
  .i32Const .uint32 0,
  .localGet total,
  .i32Const .uint32 0,
  .i32Const .uint32 0,
  .call (.declaration differenceScanFromName),
  .localSet resultCountLocal]

private def writeDifference (left leftFlavor right rightFlavor result total store :
    FVarId) : List Instruction := [
  .localGet left,
  .localGet leftFlavor,
  .localGet right,
  .localGet rightFlavor,
  .localGet result,
  .i32Const .uint32 0,
  .localGet total,
  .localGet store,
  .i32Const .uint32 0,
  .call (.declaration writeDifferenceFromName)]

private def finishNaturalDifference : List Instruction :=
  scanDifference leftParam leftFlavorParam rightParam rightFlavorParam leftCountLocal ++ [
    .localGet resultCountLocal,
    .i32Const .uint32 1,
    .i32Eq,
    .ifElse
      (callDifferencePart differenceLowName leftParam leftFlavorParam
          rightParam rightFlavorParam ++
        callDifferencePart differenceHighName leftParam leftFlavorParam
          rightParam rightFlavorParam ++
        [.call (.declaration ResidentNumeric.makeNaturalName)] ++
        retypeRawResult .tobject objectResultLocal)
      (allocateNatural resultCountLocal ++ [
        .localSet rawLocal] ++
        writeDifference leftParam leftFlavorParam rightParam rightFlavorParam
          rawLocal leftCountLocal resultCountLocal ++ [
        .localGet rawLocal] ++
        retypeRawResult .tobject objectResultLocal)]

def natSubFunction : Function := {
  name := externalName `Nat.sub
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.tobject]
  locals := naturalArithmeticLocals
  body := [
    .i32Const .uint32 0,
    .localSet leftFlavorParam,
    .i32Const .uint32 0,
    .localSet rightFlavorParam] ++
    validateNaturalsAndCounts ++ [
    .localGet leftParam,
    .i32Const .uint32 0,
    .localGet rightParam,
    .i32Const .uint32 0,
    .call (.declaration compareName),
    .localSet compareLocal,
    .localGet compareLocal,
    .i32Const .uint32 2,
    .i32Eq,
    .ifElse
      finishNaturalDifference
      ([.i32Const .uint32 0,
        .i32Const .uint32 0,
        .call (.declaration ResidentNumeric.makeNaturalName)] ++
        retypeRawResult .tobject objectResultLocal)] }

private def integerCombineLocals : Array (FVarId × AbiKind) := #[
  (leftFlavorParam, .uint32),
  (rightFlavorParam, .uint32),
  (leftCountLocal, .uint32),
  (rightCountLocal, .uint32),
  (countLocal, .uint32),
  (resultCountLocal, .uint32),
  (leftLowLocal, .uint32),
  (leftHighLocal, .uint32),
  (rightLowLocal, .uint32),
  (rightHighLocal, .uint32),
  (leftSignLocal, .uint32),
  (rightSignLocal, .uint32),
  (resultSignLocal, .uint32),
  (carryLocal, .uint32),
  (carryExtraLocal, .uint32),
  (scaledLocal, .uint32),
  (compareLocal, .uint32),
  (rawLocal, .uint32),
  (minuendLocal, .tobject),
  (subtrahendLocal, .tobject)]

private def finishIntegerSum : List Instruction :=
  maxCounts ++ callSumCarry ++ [
    .localGet resultCountLocal,
    .i32Const .uint32 1,
    .i32Eq,
    .ifElse
      (callOneLimbIntegerSum resultSignLocal ++ [.ret])
      (allocateInteger resultSignLocal resultCountLocal ++ [
        .localSet rawLocal] ++
        writeSum rawLocal ++ [
        .localGet rawLocal,
        .ret])]

private def finishIntegerDifference : List Instruction :=
  scanDifference minuendLocal leftFlavorParam subtrahendLocal
      rightFlavorParam countLocal ++ [
    .localGet resultCountLocal,
    .i32Const .uint32 1,
    .i32Eq,
    .ifElse
      ([.localGet resultSignLocal] ++
        callDifferencePart differenceLowName minuendLocal leftFlavorParam
          subtrahendLocal rightFlavorParam ++
        callDifferencePart differenceHighName minuendLocal leftFlavorParam
          subtrahendLocal rightFlavorParam ++
        [.call (.declaration ResidentNumeric.makeIntegerName),
          .ret])
      (allocateInteger resultSignLocal resultCountLocal ++ [
        .localSet rawLocal] ++
        writeDifference minuendLocal leftFlavorParam subtrahendLocal
          rightFlavorParam rawLocal countLocal resultCountLocal ++ [
        .localGet rawLocal,
        .ret])]

private def finishIntegerOppositeSigns : List Instruction := [
  .localGet leftParam,
  .i32Const .uint32 1,
  .localGet rightParam,
  .i32Const .uint32 1,
  .call (.declaration compareName),
  .localSet compareLocal,
  .localGet compareLocal,
  .i32Const .uint32 0,
  .i32Eq,
  .ifElse
    [.i32Const .uint32 0,
      .i32Const .uint32 0,
      .i32Const .uint32 0,
      .call (.declaration ResidentNumeric.makeIntegerName),
      .ret]
    ([.localGet compareLocal,
      .i32Const .uint32 1,
      .i32Eq,
      .ifElse
        [.localGet rightParam,
          .localSet minuendLocal,
          .localGet leftParam,
          .localSet subtrahendLocal,
          .localGet rightSignLocal,
          .localSet resultSignLocal,
          .localGet rightCountLocal,
          .localSet countLocal]
        [.localGet leftParam,
          .localSet minuendLocal,
          .localGet rightParam,
          .localSet subtrahendLocal,
          .localGet leftSignLocal,
          .localSet resultSignLocal,
          .localGet leftCountLocal,
          .localSet countLocal]] ++
      finishIntegerDifference)]

def integerCombineFunction : Function := {
  name := integerCombineName
  params := #[
    (leftParam, .tobject),
    (rightParam, .tobject),
    (invertParam, .uint32)]
  results := #[.uint32]
  locals := integerCombineLocals
  body := [
    .i32Const .uint32 1,
    .localSet leftFlavorParam,
    .i32Const .uint32 1,
    .localSet rightFlavorParam,
    .localGet leftParam,
    .call (.declaration validateIntegerName),
    .localGet rightParam,
    .call (.declaration validateIntegerName),
    .localGet leftParam,
    .call (.declaration integerCountName),
    .localSet leftCountLocal,
    .localGet rightParam,
    .call (.declaration integerCountName),
    .localSet rightCountLocal,
    .localGet leftParam,
    .call (.declaration integerSignName),
    .localSet leftSignLocal,
    .localGet rightParam,
    .call (.declaration integerSignName),
    .localSet rightSignLocal,
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
      ([.localGet leftSignLocal,
        .localSet resultSignLocal] ++
        finishIntegerSum)
      finishIntegerOppositeSigns] }

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
    retypeRawResult .tobject objectResultLocal }

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
    retypeRawResult .tobject objectResultLocal }

inductive DecisionKind where
  | eq
  | lt
  | le

private def naturalDecisionBody (kind : DecisionKind) : List Instruction := [
  .localGet leftParam,
  .call (.declaration validateNaturalName),
  .localGet rightParam,
  .call (.declaration validateNaturalName),
  .localGet leftParam,
  .i32Const .uint32 0,
  .localGet rightParam,
  .i32Const .uint32 0,
  .call (.declaration compareName),
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
  retypeRawResult .uint8 decisionResultLocal

private def naturalDecisionLocals : Array (FVarId × AbiKind) :=
  decisionResultLocals ++ #[(compareLocal, .uint32)]

def natDecEqFunction : Function := {
  name := externalName `Nat.decEq
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := naturalDecisionLocals
  body := naturalDecisionBody .eq }

def natDecLtFunction : Function := {
  name := externalName `Nat.decLt
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := naturalDecisionLocals
  body := naturalDecisionBody .lt }

def natDecLeFunction : Function := {
  name := externalName `Nat.decLe
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := naturalDecisionLocals
  body := naturalDecisionBody .le }

def intDecLtFunction : Function := {
  name := externalName `Int.decLt
  params := #[(leftParam, .tobject), (rightParam, .tobject)]
  results := #[.uint8]
  locals := decisionResultLocals ++ #[
    (leftSignLocal, .uint32),
    (rightSignLocal, .uint32),
    (compareLocal, .uint32)]
  body := [
    .localGet leftParam,
    .call (.declaration validateIntegerName),
    .localGet rightParam,
    .call (.declaration validateIntegerName),
    .localGet leftParam,
    .call (.declaration integerSignName),
    .localSet leftSignLocal,
    .localGet rightParam,
    .call (.declaration integerSignName),
    .localSet rightSignLocal,
    .localGet leftSignLocal,
    .localGet rightSignLocal,
    .i32Eq,
    .ifElse
      [.localGet leftParam,
        .i32Const .uint32 1,
        .localGet rightParam,
        .i32Const .uint32 1,
        .call (.declaration compareName),
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
    retypeRawResult .uint8 decisionResultLocal }

def externalFunctions : Array Function := #[
  intOfNatFunction,
  intDecLtFunction,
  intNatAbsFunction,
  intSubFunction,
  natAddFunction,
  natDecEqFunction,
  natSubFunction,
  intAddFunction,
  natDecLtFunction,
  natDecLeFunction]

def internalFunctions : Array Function :=
  validationAndAccessFunctions ++ limbFunctions ++ #[integerCombineFunction]

def internalHelperNames : Array Name := #[
  validateCommonName,
  validateNaturalName,
  validateIntegerName,
  naturalCountName,
  naturalLowName,
  naturalHighName,
  integerCountName,
  integerSignName,
  integerLowName,
  integerHighName,
  magnitudeCountName,
  magnitudeLowName,
  magnitudeHighName,
  allocateName,
  compareAtName,
  compareName,
  copyFromName,
  sumCarryFromName,
  writeSumFromName,
  differenceScanFromName,
  writeDifferenceFromName,
  differenceLowName,
  differenceHighName,
  integerCombineName]

def helperNames : Array Name := internalHelperNames ++ externalHelperNames

private def replacement? (name : Name) : Option Name := do
  let declaration ← ResidentNumeric.externalDeclarations.find? fun declaration =>
    ResidentNumeric.externalName declaration == name
  return externalName declaration

private partial def rewriteInstruction : Instruction → Instruction
  | .call (.declaration name) =>
      match replacement? name with
      | some replacement => .call (.declaration replacement)
      | none => .call (.declaration name)
  | .block label body =>
      .block label (body.map rewriteInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse
        (thenBody.map rewriteInstruction)
        (elseBody.map rewriteInstruction)
  | instruction => instruction

private def rewriteFunction (function : Function) : Function :=
  { function with body := function.body.map rewriteInstruction }

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
  let result : Module := {
    module with
    functions :=
      module.functions.map rewriteFunction ++ internalFunctions ++ externalFunctions
    exports := helperNames.foldl Fir.Wasm.addUnique module.exports }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

def residentExampleModule : Except String Module := do
  let module ← ResidentNumeric.residentExampleModule
  internalize module
    |>.mapError fun error => s!"big numeric: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("sourceEntry", externalName `Nat.add |>.toString),
    ("entry", externalName `Nat.add |>.toString),
    ("params", Json.arr #["tobject", "tobject"]),
    ("result", "tobject"),
    ("closureDispatch", Json.arr #[]),
    ("closureDescriptors", Json.arr #[]),
    ("imports", Json.arr #[]),
    ("numericLimbBits", 64),
    ("multiLimbPolicy", "canonical-arbitrary-precision"),
    ("walkerControl", "recursive-pending-symbolic-loop-release"),
    ("status", "generation-only; W6 arbitrary-precision contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      externalHelperNames.all module.exports.contains &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentBigNumeric
