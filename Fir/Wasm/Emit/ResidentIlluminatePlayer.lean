import Fir.Wasm.Emit.ResidentArray
import Fir.Wasm.Emit.ResidentLiteral

namespace Fir.Wasm.Emit.ResidentIlluminatePlayer

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

/-!
# Illuminate compiler-specialization closure

Lean 4.32 emits private, application-specific specializations for the
animation player without serializing their bodies for downstream final-LCNF
capture. This module implements those exact specializations inside Wasm. They
are not host callbacks: they execute against the resident Natural, Array,
String, and constructor layouts in module-owned memory.

The linker checks every imported signature and fails closed if Lean changes
the specialization frontier. The helpers cover validation and trace traversal
for the real SVG-free `PlayerAnimation` entry; they do not define an alternate
entry or duplicate the player transition function.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | incompatibleMemory
  | missingDependency (name : Name)
  | reservedDeclaration (name : Name)
  | unexpectedExternalInventory (names : Array String)
  | missingSpecialization (label : String)
  | duplicateSpecialization (label : String)
  | incompatibleSpecialization (label : String)
  | invalidValidationLiteral (error : ResidentLiteral.LinkError)
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

def naturalFromU32Name : Name := `fir_illuminate_natural_from_u32
def oneFieldConstructorName : Name := `fir_illuminate_ctor_tag1_1
def errorConstructorName : Name := `fir_illuminate_except_error
def okTobjectConstructorName : Name := `fir_illuminate_except_ok_tobject
def okObjectConstructorName : Name := `fir_illuminate_except_ok_object
def attributeUpdateConstructorName : Name := `fir_illuminate_attribute_update
def productConstructorName : Name := `fir_illuminate_product
def optionNatEqName : Name := `fir_illuminate_option_nat_eq
def findSegmentLoopName : Name := `fir_illuminate_find_segment_loop
def findCurrentStepLoopName : Name := `fir_illuminate_find_current_step_loop
def findCurrentStepFromBackwardLoopName : Name :=
  `fir_illuminate_find_current_step_from_backward_loop
def findCurrentStepFromForwardLoopName : Name :=
  `fir_illuminate_find_current_step_from_forward_loop
def parameterUpdatesLoopName : Name := `fir_illuminate_parameter_updates_loop
def findCrossedPauseLoopName : Name := `fir_illuminate_find_crossed_pause_loop
def validateSegmentsLoopName : Name := `fir_illuminate_validate_segments_loop
def validateStepsLoopName : Name := `fir_illuminate_validate_steps_loop
def replayTraceLoopName : Name := `fir_illuminate_replay_trace_loop

private def validationMessages : Array String := #[
  "animation segments must be contiguous from frame zero",
  "animation segments must contain at least one frame",
  "animation segment parameter-frame count is inconsistent",
  "animation segment parameter values are inconsistent",
  "animation steps must start within the animation",
  "animation steps must be ordered"]

private def validationStringName (index : Nat) : Name :=
  ResidentLiteral.stringName (1000 + index)

private def validationStringNames : Array Name :=
  validationMessages.mapIdx fun index _ => validationStringName index

def helperNames : Array Name := #[
  naturalFromU32Name,
  oneFieldConstructorName,
  errorConstructorName,
  okTobjectConstructorName,
  okObjectConstructorName,
  attributeUpdateConstructorName,
  productConstructorName,
  optionNatEqName,
  findSegmentLoopName,
  findCurrentStepLoopName,
  findCurrentStepFromBackwardLoopName,
  findCurrentStepFromForwardLoopName,
  parameterUpdatesLoopName,
  findCrossedPauseLoopName,
  validateSegmentsLoopName,
  validateStepsLoopName,
  replayTraceLoopName] ++ validationStringNames

private def p0 : FVarId := ⟨`p0⟩
private def p1 : FVarId := ⟨`p1⟩
private def p2 : FVarId := ⟨`p2⟩
private def p3 : FVarId := ⟨`p3⟩
private def p4 : FVarId := ⟨`p4⟩

private def addressLocal : FVarId := ⟨`address⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def tobjectResultLocal : FVarId := ⟨`tobjectResult⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def uint8ResultLocal : FVarId := ⟨`uint8Result⟩
private def indexLocal : FVarId := ⟨`index⟩
private def indexHighLocal : FVarId := ⟨`indexHigh⟩
private def indexNatLocal : FVarId := ⟨`indexNat⟩
private def sizeLocal : FVarId := ⟨`size⟩
private def outerSizeLocal : FVarId := ⟨`outerSize⟩
private def sizeNatLocal : FVarId := ⟨`sizeNat⟩
private def secondSizeLocal : FVarId := ⟨`secondSize⟩
private def secondSizeNatLocal : FVarId := ⟨`secondSizeNat⟩
private def frameLocal : FVarId := ⟨`frame⟩
private def frameHighLocal : FVarId := ⟨`frameHigh⟩
private def segmentLocal : FVarId := ⟨`segment⟩
private def startNatLocal : FVarId := ⟨`startNat⟩
private def countNatLocal : FVarId := ⟨`countNat⟩
private def startLocal : FVarId := ⟨`start⟩
private def countLocal : FVarId := ⟨`count⟩
private def highLocal : FVarId := ⟨`high⟩
private def endLocal : FVarId := ⟨`end⟩
private def bindingLocal : FVarId := ⟨`binding⟩
private def valueLocal : FVarId := ⟨`value⟩
private def elementLocal : FVarId := ⟨`element⟩
private def attributeLocal : FVarId := ⟨`attribute⟩
private def targetLocal : FVarId := ⟨`target⟩
private def updateLocal : FVarId := ⟨`update⟩
private def updatesLocal : FVarId := ⟨`updates⟩
private def matchesLocal : FVarId := ⟨`matches⟩
private def leftValueLocal : FVarId := ⟨`leftValue⟩
private def rightValueLocal : FVarId := ⟨`rightValue⟩
private def stopNatLocal : FVarId := ⟨`stopNat⟩
private def stopLocal : FVarId := ⟨`stop⟩
private def stepLocal : FVarId := ⟨`step⟩
private def optionLocal : FVarId := ⟨`option⟩
private def rowLocal : FVarId := ⟨`row⟩
private def rowIndexLocal : FVarId := ⟨`rowIndex⟩
private def rowIndexNatLocal : FVarId := ⟨`rowIndexNat⟩
private def rowSizeNatLocal : FVarId := ⟨`rowSizeNat⟩
private def rowSizeLocal : FVarId := ⟨`rowSize⟩
private def paramsLocal : FVarId := ⟨`params⟩
private def paramMapLocal : FVarId := ⟨`paramMap⟩
private def expectedLocal : FVarId := ⟨`expected⟩
private def previousLocal : FVarId := ⟨`previous⟩
private def stepIndexLocal : FVarId := ⟨`stepIndex⟩
private def lowLocal : FVarId := ⟨`low⟩
private def midLocal : FVarId := ⟨`mid⟩
private def midNatLocal : FVarId := ⟨`midNat⟩
private def pairLocal : FVarId := ⟨`pair⟩
private def eventsLocal : FVarId := ⟨`events⟩
private def eventLocal : FVarId := ⟨`event⟩
private def tailLocal : FVarId := ⟨`tail⟩
private def stateLocal : FVarId := ⟨`state⟩
private def actionLocal : FVarId := ⟨`action⟩
private def transitionLocal : FVarId := ⟨`transition⟩

private def loopLabel : FVarId := ⟨`loop⟩
private def rowLoopLabel : FVarId := ⟨`rowLoop⟩

private def storeAddress (kind : AbiKind) (offset : Nat)
    (value : List Instruction) : List Instruction :=
  [.localGet addressLocal] ++ value ++ [.i32Store kind (u32 offset)]

private def constructorHeader (tag fields allocationBytes : Nat) : List Instruction :=
  storeAddress .uint32 headerKindOffset
      [.i32Const .uint32 ObjectKind.constructor.code] ++
    storeAddress .uint32 headerFlagsOffset
      [.i32Const .uint32 liveFlag] ++
    storeAddress .uint32 headerRefCountOffset
      [.i32Const .uint32 1] ++
    storeAddress .uint32 headerAllocationBytesOffset
      [.i32Const .uint32 (u32 allocationBytes)] ++
    storeAddress .uint32 headerAux0Offset
      [.i32Const .uint32 (u32 tag)] ++
    storeAddress .uint32 headerAux1Offset
      [.i32Const .uint32 (u32 fields)] ++
    storeAddress .uint32 headerAux2Offset
      [.i32Const .uint32 0] ++
    storeAddress .uint32 headerAux3Offset
      [.i32Const .uint32 0]

private def retypeRaw (result : AbiKind) (resultLocal : FVarId) :
    List Instruction := [
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

private def trapUnlessZero (localId : FVarId) : List Instruction := [
  .localGet localId,
  .i32Const .uint32 0,
  .i32Eq,
  .ifElse [] [.unreachable]]

/--
Wasm represents all of these booleans as `i32`, but FIR keeps the source ABI
refinement (`uint8`) distinct from an instruction condition (`uint32`).  The
two comparisons preserve the Boolean value while widening its symbolic kind.
-/
private def normalizeBoolean : List Instruction := [
  .i32Const .uint8 0,
  .i32Eq,
  .i32Const .uint32 0,
  .i32Eq]

private def decodeNatural32 (source low high : FVarId) : List Instruction := [
  .localGet source,
  .call (.declaration ResidentNumeric.validateNaturalName),
  .localGet source,
  .call (.declaration ResidentNumeric.naturalLowName),
  .localSet low,
  .localGet source,
  .call (.declaration ResidentNumeric.naturalHighName),
  .localSet high] ++ trapUnlessZero high

private def callArraySize (array : FVarId) (sizeNat size : FVarId) :
    List Instruction := [
  .i32Const .erased 0,
  .localGet array,
  .call (.declaration (ResidentArray.externalName `Array.size)),
  .localSet sizeNat,
  .localGet sizeNat,
  .call (.declaration ResidentNumeric.naturalLowName),
  .localSet size]

private def callArrayGet (array index result : FVarId) : List Instruction := [
  .i32Const .erased 0,
  .localGet array,
  .localGet index,
  .i32Const .erased 0,
  .call (.declaration (ResidentArray.externalName `Array.getInternalBorrowed)),
  .localSet result]

def naturalFromU32Function : Function := {
  name := naturalFromU32Name
  params := #[(p0, .uint32)]
  results := #[.tobject]
  locals := #[(rawLocal, .uint32), (savedScratchLocal, .uint32),
    (tobjectResultLocal, .tobject)]
  body := [
    .localGet p0,
    .i32Const .uint32 0,
    .call (.declaration ResidentNumeric.makeNaturalName),
    .localSet rawLocal] ++ retypeRaw .tobject tobjectResultLocal }

/-- Layout shared by `Option.some` and `PatchTarget.attribute`. -/
def oneFieldConstructorFunction : Function := {
  name := oneFieldConstructorName
  params := #[(p0, .tobject)]
  results := #[.tobject]
  locals := #[(addressLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (tobjectResultLocal, .tobject)]
  body := [
    .i32Const .uint32 (u32 (headerBytes + target.semanticSlotBytes)),
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++
    constructorHeader 1 1 (headerBytes + target.semanticSlotBytes) ++
    storeAddress .tobject headerBytes [.localGet p0] ++ [
    .localGet addressLocal,
    .localSet rawLocal] ++ retypeRaw .tobject tobjectResultLocal }

private def heapOneFieldConstructorFunction (name : Name) (tag : Nat)
    (parameter result : AbiKind) : Function := {
  name
  params := #[(p0, parameter)]
  results := #[result]
  locals := #[(addressLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (objectResultLocal, result)]
  body := [
    .i32Const .uint32 (u32 (headerBytes + target.semanticSlotBytes)),
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++
    constructorHeader tag 1 (headerBytes + target.semanticSlotBytes) ++
    storeAddress parameter headerBytes [.localGet p0] ++ [
    .localGet addressLocal,
    .localSet rawLocal] ++ retypeRaw result objectResultLocal }

def errorConstructorFunction : Function :=
  heapOneFieldConstructorFunction errorConstructorName 0 .object .object

def okTobjectConstructorFunction : Function :=
  heapOneFieldConstructorFunction okTobjectConstructorName 1 .tobject .object

def okObjectConstructorFunction : Function :=
  heapOneFieldConstructorFunction okObjectConstructorName 1 .object .object

def attributeUpdateConstructorFunction : Function := {
  name := attributeUpdateConstructorName
  params := #[(p0, .tobject), (p1, .tobject), (p2, .tobject)]
  results := #[.tobject]
  locals := #[(addressLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (tobjectResultLocal, .tobject)]
  body := [
    .i32Const .uint32 (u32 (headerBytes + 3 * target.semanticSlotBytes)),
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++
    constructorHeader 0 3 (headerBytes + 3 * target.semanticSlotBytes) ++
    storeAddress .tobject headerBytes [.localGet p0] ++
    storeAddress .tobject (headerBytes + target.semanticSlotBytes) [.localGet p1] ++
    storeAddress .tobject (headerBytes + 2 * target.semanticSlotBytes) [.localGet p2] ++ [
    .localGet addressLocal,
    .localSet rawLocal] ++ retypeRaw .tobject tobjectResultLocal }

def productConstructorFunction : Function := {
  name := productConstructorName
  params := #[(p0, .tobject), (p1, .tobject)]
  results := #[.object]
  locals := #[(addressLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (objectResultLocal, .object)]
  body := [
    .i32Const .uint32 (u32 (headerBytes + 2 * target.semanticSlotBytes)),
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++
    constructorHeader 0 2 (headerBytes + 2 * target.semanticSlotBytes) ++
    storeAddress .tobject headerBytes [.localGet p0] ++
    storeAddress .tobject (headerBytes + target.semanticSlotBytes) [.localGet p1] ++ [
    .localGet addressLocal,
    .localSet rawLocal] ++ retypeRaw .object objectResultLocal }

private def returnValidationError (index : Nat) : List Instruction := [
  .call (.declaration (validationStringName index)),
  .call (.declaration errorConstructorName),
  .ret]

def optionNatEqFunction : Function := {
  name := optionNatEqName
  params := #[(p0, .tobject), (p1, .tobject)]
  results := #[.uint8]
  locals := #[(leftValueLocal, .tobject), (rightValueLocal, .tobject),
    (rawLocal, .uint32), (savedScratchLocal, .uint32),
    (uint8ResultLocal, .uint8)]
  body := [
    .localGet p0,
    .i32Const .tobject 1,
    .i32Eq,
    .ifElse
      [.localGet p1,
        .i32Const .tobject 1,
        .i32Eq,
        .localSet rawLocal]
      [.localGet p1,
        .i32Const .tobject 1,
        .i32Eq,
        .ifElse
          [.i32Const .uint32 0, .localSet rawLocal]
          [.localGet p0,
            .i32Load .tobject (u32 headerBytes),
            .localSet leftValueLocal,
            .localGet p1,
            .i32Load .tobject (u32 headerBytes),
            .localSet rightValueLocal,
            .localGet leftValueLocal,
            .localGet rightValueLocal,
            .call (.declaration (ResidentNumeric.externalName `Nat.decEq)),
            .ret]]] ++
    retypeRaw .uint8 uint8ResultLocal }

private def advanceIndex : List Instruction := [
  .localGet indexLocal,
  .i32Const .uint32 1,
  .i32Add,
  .localSet indexLocal,
  .br loopLabel]

def findSegmentLoopFunction : Function := {
  name := findSegmentLoopName
  params := #[(p0, .tobject), (p1, .object), (p2, .tobject)]
  results := #[.tobject]
  locals := #[(frameLocal, .uint32), (frameHighLocal, .uint32),
    (indexLocal, .uint32), (indexHighLocal, .uint32),
    (indexNatLocal, .tobject), (sizeNatLocal, .tagged),
    (sizeLocal, .uint32), (segmentLocal, .object),
    (startNatLocal, .tobject), (countNatLocal, .tobject),
    (startLocal, .uint32), (countLocal, .uint32),
    (highLocal, .uint32), (endLocal, .uint32),
    (optionLocal, .tobject)]
  body := decodeNatural32 p0 frameLocal frameHighLocal ++
    decodeNatural32 p2 indexLocal indexHighLocal ++
    callArraySize p1 sizeNatLocal sizeLocal ++ [
    .loop loopLabel [
      .localGet indexLocal,
      .localGet sizeLocal,
      .i32LtU,
      .ifElse
        ([.localGet indexLocal,
          .call (.declaration naturalFromU32Name),
          .localSet indexNatLocal] ++
          callArrayGet p1 indexNatLocal segmentLocal ++ [
          .localGet segmentLocal,
          .i32Load .tobject (u32 headerBytes),
          .localSet startNatLocal,
          .localGet segmentLocal,
          .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
          .localSet countNatLocal] ++
          decodeNatural32 startNatLocal startLocal highLocal ++
          decodeNatural32 countNatLocal countLocal highLocal ++ [
          .localGet frameLocal,
          .localGet startLocal,
          .i32LtU,
          .ifElse advanceIndex [
            .localGet startLocal,
            .localGet countLocal,
            .i32Add,
            .localSet endLocal,
            .localGet endLocal,
            .localGet startLocal,
            .i32LtU,
            .ifElse [.unreachable] [],
            .localGet frameLocal,
            .localGet endLocal,
            .i32LtU,
            .ifElse
              [.localGet indexNatLocal,
                .call (.declaration oneFieldConstructorName),
                .localSet optionLocal,
                .localGet optionLocal,
                .ret]
              advanceIndex]])
        []],
    .i32Const .tobject 1,
    .ret] }

def findCurrentStepLoopFunction : Function := {
  name := findCurrentStepLoopName
  params := #[(p0, .object), (p1, .tobject), (p2, .object)]
  results := #[.object]
  locals := #[(frameLocal, .uint32), (frameHighLocal, .uint32),
    (lowLocal, .uint32), (highLocal, .uint32), (midLocal, .uint32),
    (midNatLocal, .tobject), (indexNatLocal, .tobject),
    (countNatLocal, .tobject), (stepLocal, .object),
    (startNatLocal, .tobject), (startLocal, .uint32),
    (indexHighLocal, .uint32)]
  body := decodeNatural32 p1 frameLocal frameHighLocal ++ [
    .localGet p2,
    .i32Load .tobject (u32 headerBytes),
    .localSet indexNatLocal,
    .localGet p2,
    .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
    .localSet countNatLocal] ++
    decodeNatural32 indexNatLocal lowLocal indexHighLocal ++
    decodeNatural32 countNatLocal highLocal indexHighLocal ++ [
    .loop loopLabel [
      .localGet lowLocal,
      .localGet highLocal,
      .i32LtU,
      .ifElse
        ([.localGet highLocal,
          .localGet lowLocal,
          .i32Sub,
          .i32Const .uint32 1,
          .i32ShrU,
          .localGet lowLocal,
          .i32Add,
          .localSet midLocal,
          .localGet midLocal,
          .call (.declaration naturalFromU32Name),
          .localSet midNatLocal] ++
          callArrayGet p0 midNatLocal stepLocal ++ [
          .localGet stepLocal,
          .i32Load .tobject (u32 headerBytes),
          .localSet startNatLocal] ++
          decodeNatural32 startNatLocal startLocal indexHighLocal ++ [
          .localGet frameLocal,
          .localGet startLocal,
          .i32LtU,
          .ifElse
            [.localGet midLocal,
              .localSet highLocal]
            [.localGet midLocal,
              .i32Const .uint32 1,
              .i32Add,
              .localSet lowLocal],
          .br loopLabel])
        []],
    .localGet lowLocal,
    .call (.declaration naturalFromU32Name),
    .localGet highLocal,
    .call (.declaration naturalFromU32Name),
    .call (.declaration productConstructorName),
    .ret] }

def findCurrentStepFromBackwardLoopFunction : Function := {
  name := findCurrentStepFromBackwardLoopName
  params := #[(p0, .object), (p1, .tobject), (p2, .tobject)]
  results := #[.tobject]
  locals := #[(frameLocal, .uint32), (frameHighLocal, .uint32),
    (indexLocal, .uint32), (indexHighLocal, .uint32),
    (indexNatLocal, .tobject), (stepLocal, .object),
    (startNatLocal, .tobject), (startLocal, .uint32),
    (highLocal, .uint32)]
  body := decodeNatural32 p1 frameLocal frameHighLocal ++
    decodeNatural32 p2 indexLocal indexHighLocal ++ [
    .loop loopLabel [
      .i32Const .uint32 0,
      .localGet indexLocal,
      .i32LtU,
      .ifElse
        ([.localGet indexLocal,
          .call (.declaration naturalFromU32Name),
          .localSet indexNatLocal] ++
          callArrayGet p0 indexNatLocal stepLocal ++ [
          .localGet stepLocal,
          .i32Load .tobject (u32 headerBytes),
          .localSet startNatLocal] ++
          decodeNatural32 startNatLocal startLocal highLocal ++ [
          .localGet frameLocal,
          .localGet startLocal,
          .i32LtU,
          .ifElse
            [.localGet indexLocal,
              .i32Const .uint32 1,
              .i32Sub,
              .localSet indexLocal,
              .br loopLabel]
            []])
        []],
    .localGet indexLocal,
    .call (.declaration naturalFromU32Name),
    .ret] }

def findCurrentStepFromForwardLoopFunction : Function := {
  name := findCurrentStepFromForwardLoopName
  params := #[(p0, .tobject), (p1, .object), (p2, .tobject),
    (p3, .tobject)]
  results := #[.tobject]
  locals := #[(sizeLocal, .uint32), (sizeNatLocal, .uint32),
    (frameLocal, .uint32), (frameHighLocal, .uint32),
    (indexLocal, .uint32), (indexHighLocal, .uint32),
    (indexNatLocal, .tobject), (stepLocal, .object),
    (startNatLocal, .tobject), (startLocal, .uint32),
    (highLocal, .uint32)]
  body := decodeNatural32 p0 sizeLocal sizeNatLocal ++
    decodeNatural32 p2 frameLocal frameHighLocal ++
    decodeNatural32 p3 indexLocal indexHighLocal ++ [
    .loop loopLabel [
      .localGet indexLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet indexHighLocal,
      .localGet indexHighLocal,
      .localGet sizeLocal,
      .i32LtU,
      .ifElse
        ([.localGet indexHighLocal,
          .call (.declaration naturalFromU32Name),
          .localSet indexNatLocal] ++
          callArrayGet p1 indexNatLocal stepLocal ++ [
          .localGet stepLocal,
          .i32Load .tobject (u32 headerBytes),
          .localSet startNatLocal] ++
          decodeNatural32 startNatLocal startLocal highLocal ++ [
          .localGet frameLocal,
          .localGet startLocal,
          .i32LtU,
          .ifElse [] [
            .localGet indexHighLocal,
            .localSet indexLocal,
            .br loopLabel]])
        []],
    .localGet indexLocal,
    .call (.declaration naturalFromU32Name),
    .ret] }

def parameterUpdatesLoopFunction : Function := {
  name := parameterUpdatesLoopName
  params := #[(p0, .object), (p1, .object), (p2, .object),
    (p3, .object), (p4, .tobject)]
  results := #[.object]
  locals := #[(indexLocal, .uint32), (indexHighLocal, .uint32),
    (indexNatLocal, .tobject), (sizeNatLocal, .tagged),
    (sizeLocal, .uint32), (secondSizeNatLocal, .tagged),
    (secondSizeLocal, .uint32), (bindingLocal, .object),
    (valueLocal, .object), (elementLocal, .tobject),
    (targetLocal, .tobject),
    (updateLocal, .tobject), (updatesLocal, .object)]
  body := decodeNatural32 p4 indexLocal indexHighLocal ++
    callArraySize p0 sizeNatLocal sizeLocal ++
    callArraySize p1 secondSizeNatLocal secondSizeLocal ++ [
    .localGet p3,
    .localSet updatesLocal,
    .loop loopLabel [
      .localGet indexLocal,
      .localGet sizeLocal,
      .i32LtU,
      .ifElse
        ([.localGet indexLocal,
          .localGet secondSizeLocal,
          .i32LtU,
          .ifElse
            ([.localGet indexLocal,
              .call (.declaration naturalFromU32Name),
              .localSet indexNatLocal] ++
              callArrayGet p0 indexNatLocal bindingLocal ++
              callArrayGet p1 indexNatLocal valueLocal ++ [
              .localGet bindingLocal,
              .i32Load .tobject (u32 headerBytes),
              .localSet elementLocal,
              .localGet bindingLocal,
              .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
              .localSet targetLocal,
              .localGet elementLocal,
              .localGet targetLocal,
              .localGet valueLocal,
              .call (.declaration attributeUpdateConstructorName),
              .localSet updateLocal,
              .i32Const .erased 0,
              .localGet updatesLocal,
              .localGet updateLocal,
              .call (.declaration (ResidentArray.externalName `Array.push)),
              .localSet updatesLocal])
            []] ++ advanceIndex)
        []],
    .localGet updatesLocal,
    .ret] }

def findCrossedPauseLoopFunction : Function := {
  name := findCrossedPauseLoopName
  params := #[(p0, .object), (p1, .object), (p2, .object), (p3, .tobject)]
  results := #[.object]
  locals := #[(indexLocal, .uint32), (indexHighLocal, .uint32),
    (indexNatLocal, .tobject), (stopNatLocal, .tobject),
    (stopLocal, .uint32), (highLocal, .uint32),
    (sizeNatLocal, .tagged), (sizeLocal, .uint32),
    (stepLocal, .object), (optionLocal, .tobject)]
  body := decodeNatural32 p3 indexLocal indexHighLocal ++ [
    .localGet p1,
    .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
    .localSet stopNatLocal] ++
    decodeNatural32 stopNatLocal stopLocal highLocal ++
    callArraySize p0 sizeNatLocal sizeLocal ++ [
    .loop loopLabel [
      .localGet indexLocal,
      .localGet stopLocal,
      .i32LtU,
      .ifElse
        ([.localGet indexLocal,
          .localGet sizeLocal,
          .i32LtU,
          .ifElse
            ([.localGet indexLocal,
              .call (.declaration naturalFromU32Name),
              .localSet indexNatLocal] ++
              callArrayGet p0 indexNatLocal stepLocal ++ [
              .localGet stepLocal,
              .i32Load8U .uint32
                (u32 (headerBytes + target.semanticSlotBytes)),
              .ifElse
                [.localGet indexNatLocal,
                  .call (.declaration oneFieldConstructorName),
                  .call (.declaration oneFieldConstructorName),
                  .localSet optionLocal,
                  .localGet optionLocal,
                  .i32Const .tobject 1,
                  .call (.declaration productConstructorName),
                  .ret]
                []])
            []] ++ advanceIndex)
        []],
    .localGet p2,
    .ret] }

def validateSegmentsLoopFunction : Function := {
  name := validateSegmentsLoopName
  params := #[(p0, .tobject), (p1, .object), (p2, .usize),
    (p3, .usize), (p4, .tobject)]
  results := #[.object]
  locals := #[(indexLocal, .uint32), (outerSizeLocal, .uint32),
    (sizeLocal, .uint32),
    (indexNatLocal, .tobject), (segmentLocal, .object),
    (startNatLocal, .tobject), (countNatLocal, .tobject),
    (countLocal, .uint32), (highLocal, .uint32),
    (expectedLocal, .tobject), (paramsLocal, .object),
    (paramMapLocal, .object), (sizeNatLocal, .tagged),
    (secondSizeNatLocal, .tagged), (secondSizeLocal, .uint32),
    (rowIndexLocal, .uint32), (rowIndexNatLocal, .tobject),
    (rowLocal, .object), (rowSizeNatLocal, .tagged),
    (rowSizeLocal, .uint32)]
  body := [
    .localGet p2,
    .i32WrapI64 .uint32,
    .localSet outerSizeLocal,
    .localGet p3,
    .i32WrapI64 .uint32,
    .localSet indexLocal,
    .localGet p4,
    .localSet expectedLocal,
    .loop loopLabel [
      .localGet indexLocal,
      .localGet outerSizeLocal,
      .i32LtU,
      .ifElse
        ([.localGet indexLocal,
          .call (.declaration naturalFromU32Name),
          .localSet indexNatLocal] ++
          callArrayGet p1 indexNatLocal segmentLocal ++ [
          .localGet segmentLocal,
          .i32Load .tobject (u32 headerBytes),
          .localSet startNatLocal,
          .localGet segmentLocal,
          .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
          .localSet countNatLocal,
          .localGet segmentLocal,
          .i32Load .object (u32 (headerBytes + 2 * target.semanticSlotBytes)),
          .localSet paramMapLocal,
          .localGet segmentLocal,
          .i32Load .object (u32 (headerBytes + 3 * target.semanticSlotBytes)),
          .localSet paramsLocal,
          .localGet startNatLocal,
          .localGet expectedLocal,
          .call (.declaration (ResidentNumeric.externalName `Nat.decEq))] ++
          normalizeBoolean ++ [
          .ifElse [] (returnValidationError 0)] ++
          decodeNatural32 countNatLocal countLocal highLocal ++ [
          .localGet countLocal,
          .i32Const .uint32 0,
          .i32Eq,
          .ifElse (returnValidationError 1) []] ++
          callArraySize paramsLocal sizeNatLocal sizeLocal ++ [
          .localGet sizeLocal,
          .localGet countLocal,
          .i32Eq,
          .ifElse [] (returnValidationError 2)] ++
          callArraySize paramMapLocal secondSizeNatLocal secondSizeLocal ++ [
          .i32Const .uint32 0,
          .localSet rowIndexLocal,
          .loop rowLoopLabel [
            .localGet rowIndexLocal,
            .localGet sizeLocal,
            .i32LtU,
            .ifElse
              ([.localGet rowIndexLocal,
                .call (.declaration naturalFromU32Name),
                .localSet rowIndexNatLocal] ++
                callArrayGet paramsLocal rowIndexNatLocal rowLocal ++
                callArraySize rowLocal rowSizeNatLocal rowSizeLocal ++ [
                .localGet rowSizeLocal,
                .localGet secondSizeLocal,
                .i32Eq,
                .ifElse [] (returnValidationError 3),
                .localGet rowIndexLocal,
                .i32Const .uint32 1,
                .i32Add,
                .localSet rowIndexLocal,
                .br rowLoopLabel])
              []],
          .localGet expectedLocal,
          .localGet countNatLocal,
          .call (.declaration (ResidentNumeric.externalName `Nat.add)),
          .localSet expectedLocal,
          .localGet indexLocal,
          .i32Const .uint32 1,
          .i32Add,
          .localSet indexLocal,
          .br loopLabel])
        []],
    .localGet expectedLocal,
    .call (.declaration okTobjectConstructorName),
    .ret] }

def validateStepsLoopFunction : Function := {
  name := validateStepsLoopName
  params := #[(p0, .object), (p1, .object), (p2, .usize),
    (p3, .usize), (p4, .object)]
  results := #[.object]
  locals := #[(indexLocal, .uint32), (sizeLocal, .uint32),
    (indexNatLocal, .tobject), (stepLocal, .object),
    (frameLocal, .tobject), (stopNatLocal, .tobject),
    (previousLocal, .tobject), (stepIndexLocal, .tobject),
    (pairLocal, .object), (updateLocal, .tobject)]
  body := [
    .localGet p2,
    .i32WrapI64 .uint32,
    .localSet sizeLocal,
    .localGet p3,
    .i32WrapI64 .uint32,
    .localSet indexLocal,
    .localGet p0,
    .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
    .localSet stopNatLocal,
    .localGet p4,
    .localSet pairLocal,
    .loop loopLabel [
      .localGet indexLocal,
      .localGet sizeLocal,
      .i32LtU,
      .ifElse
        ([.localGet indexLocal,
          .call (.declaration naturalFromU32Name),
          .localSet indexNatLocal] ++
          callArrayGet p1 indexNatLocal stepLocal ++ [
          .localGet stepLocal,
          .i32Load .tobject (u32 headerBytes),
          .localSet frameLocal,
          .localGet stopNatLocal,
          .localGet frameLocal,
          .call (.declaration (ResidentNumeric.externalName `Nat.decLe))] ++
          normalizeBoolean ++ [
          .ifElse (returnValidationError 4) [],
          .localGet pairLocal,
          .i32Load .tobject (u32 headerBytes),
          .localSet previousLocal,
          .localGet pairLocal,
          .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
          .localSet stepIndexLocal,
          .localGet stepIndexLocal,
          .i32Const .tobject 1,
          .call (.declaration (ResidentNumeric.externalName `Nat.decEq))] ++
          normalizeBoolean ++ [
          .ifElse [] (
            [.localGet frameLocal,
              .localGet previousLocal,
              .call (.declaration (ResidentNumeric.externalName `Nat.decLt))] ++
              normalizeBoolean ++ [
              .ifElse (returnValidationError 5) []]),
          .localGet stepIndexLocal,
          .i32Const .tobject 3,
          .call (.declaration (ResidentNumeric.externalName `Nat.add)),
          .localSet updateLocal,
          .localGet frameLocal,
          .localGet updateLocal,
          .call (.declaration productConstructorName),
          .localSet pairLocal,
          .localGet indexLocal,
          .i32Const .uint32 1,
          .i32Add,
          .localSet indexLocal,
          .br loopLabel])
        []],
    .localGet pairLocal,
    .call (.declaration okObjectConstructorName),
    .ret] }

def replayTraceLoopFunction : Function := {
  name := replayTraceLoopName
  params := #[(p0, .object), (p1, .tobject), (p2, .object)]
  results := #[.object]
  locals := #[(eventsLocal, .tobject), (pairLocal, .object),
    (eventLocal, .tobject), (tailLocal, .tobject),
    (stateLocal, .object), (updatesLocal, .object),
    (transitionLocal, .object), (actionLocal, .object)]
  body := [
    .localGet p1,
    .localSet eventsLocal,
    .localGet p2,
    .localSet pairLocal,
    .loop loopLabel [
      .localGet eventsLocal,
      .i32Const .tobject 1,
      .i32Eq,
      .ifElse
        [.localGet pairLocal,
          .call (.declaration okObjectConstructorName),
          .ret]
        [.localGet eventsLocal,
          .i32Load .tobject (u32 headerBytes),
          .localSet eventLocal,
          .localGet eventsLocal,
          .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes)),
          .localSet tailLocal,
          .localGet pairLocal,
          .i32Load .object (u32 headerBytes),
          .localSet stateLocal,
          .localGet pairLocal,
          .i32Load .object (u32 (headerBytes + target.semanticSlotBytes)),
          .localSet updatesLocal,
          .localGet p0,
          .localGet stateLocal,
          .localGet eventLocal,
          .call (.declaration `Illuminate.AnimationPlayer.transitionPrepared),
          .localSet transitionLocal,
          .localGet transitionLocal,
          .i32Load .object (u32 headerBytes),
          .localSet stateLocal,
          .localGet transitionLocal,
          .i32Load .object (u32 (headerBytes + target.semanticSlotBytes)),
          .localSet actionLocal,
          .i32Const .erased 0,
          .localGet updatesLocal,
          .localGet actionLocal,
          .call (.declaration (ResidentArray.externalName `Array.push)),
          .localSet updatesLocal,
          .localGet stateLocal,
          .localGet updatesLocal,
          .call (.declaration productConstructorName),
          .localSet pairLocal,
          .localGet tailLocal,
          .localSet eventsLocal,
          .br loopLabel]],
    .unreachable] }

def functions : Array Function := #[
  naturalFromU32Function,
  oneFieldConstructorFunction,
  errorConstructorFunction,
  okTobjectConstructorFunction,
  okObjectConstructorFunction,
  attributeUpdateConstructorFunction,
  productConstructorFunction,
  optionNatEqFunction,
  findSegmentLoopFunction,
  findCurrentStepLoopFunction,
  findCurrentStepFromBackwardLoopFunction,
  findCurrentStepFromForwardLoopFunction,
  parameterUpdatesLoopFunction,
  findCrossedPauseLoopFunction,
  validateSegmentsLoopFunction,
  validateStepsLoopFunction,
  replayTraceLoopFunction]

/--
Compiler ancestors pulled in while reconstructing `Float.ofScientific` leave
these unreachable declarations in the pre-pruned source module.  The final
dead-code pass removes them; pinning the list here still rejects a genuinely
new resident-runtime dependency.
-/
private def dormantExternalNames : Array String := #[
  "Nat.pow",
  "Nat.mul",
  "Nat.log2",
  "Nat.shiftRight",
  "UInt64.ofNat",
  "UInt64.toFloat",
  "Float.scaleB",
  "Nat.shiftLeft",
  "Nat.div",
  "Int.neg",
  "Int.mul"]

private structure Specialization where
  label : String
  declaration : Name
  replacement : Name
  signature : Signature

private def findSpecialization (module : Module) (label : String)
    (predicate : String → Bool) (replacement : Name)
    (signature : Signature) : Except LinkError Specialization := do
  let names := module.imports.filterMap (fun import_ => import_.declaration?) |>.filter
    (fun name => predicate name.toString)
  if names.isEmpty then throw (.missingSpecialization label)
  unless names.size == 1 do throw (.duplicateSpecialization label)
  let declaration := names[0]!
  let imports := module.imports.filter (fun import_ =>
    import_.declaration? == some declaration)
  unless imports.size == 1 && imports[0]!.signature == signature do
    throw (.incompatibleSpecialization label)
  return { label, declaration, replacement, signature }

private def validationStringFunctions : Except LinkError (Array Function) :=
  validationMessages.mapIdxM fun index message =>
    ResidentLiteral.literalFunction (1000 + index)
      (.literal (.str message) .object)
      |>.mapError .invalidValidationLiteral

private partial def rewriteInstruction
    (specializations : Array Specialization) : Instruction → Instruction
  | .call (.declaration declaration) =>
      match specializations.find? (fun specialization =>
          specialization.declaration == declaration) with
      | some specialization => .call (.declaration specialization.replacement)
      | none => .call (.declaration declaration)
  | .block label body =>
      .block label (body.map (rewriteInstruction specializations))
  | .loop label body =>
      .loop label (body.map (rewriteInstruction specializations))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteInstruction specializations))
        (elseBody.map (rewriteInstruction specializations))
  | instruction => instruction

def internalize (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  for dependency in #[
      ResidentAllocator.allocateName,
      ResidentNumeric.validateNaturalName,
      ResidentNumeric.naturalLowName,
      ResidentNumeric.naturalHighName,
      ResidentNumeric.makeNaturalName,
      ResidentNumeric.externalName `Nat.decEq,
      ResidentNumeric.externalName `Nat.decLe,
      ResidentNumeric.externalName `Nat.decLt,
      ResidentNumeric.externalName `Nat.add,
      ResidentArray.externalName `Array.size,
      ResidentArray.externalName `Array.getInternalBorrowed,
      ResidentArray.externalName `Array.push,
      `Illuminate.AnimationPlayer.transitionPrepared] do
    unless module.functions.any (fun function => function.name == dependency) do
      throw (.missingDependency dependency)
  for name in helperNames do
    if module.imports.any (fun import_ => import_.declaration? == some name) ||
        module.functions.any (fun function => function.name == name) ||
        module.exports.contains name then
      throw (.reservedDeclaration name)
  let validateSegments ← findSpecialization module "validatePrepared segments"
    (fun name => name.contains "Array.forIn'Unsafe.loop" &&
      name.contains "Illuminate.AnimationPlayer.validatePrepared.spec_1")
    validateSegmentsLoopName {
      params := #[.tobject, .object, .usize, .usize, .tobject],
      results := #[.object] }
  let validateSteps ← findSpecialization module "validatePrepared steps"
    (fun name => name.contains "Array.forIn'Unsafe.loop" &&
      name.contains "Illuminate.AnimationPlayer.validatePrepared.spec_2")
    validateStepsLoopName {
      params := #[.object, .object, .usize, .usize, .object],
      results := #[.object] }
  let findCurrentStep ← findSpecialization module "findCurrentStep"
    (fun name => name.contains "whileM.erased" &&
      name.contains "Illuminate.AnimationPlayer.findCurrentStep.spec_0" &&
      !name.contains "findCurrentStepFrom")
    findCurrentStepLoopName {
      params := #[.object, .tobject, .object], results := #[.object] }
  let findSegment ← findSpecialization module "findPlayerSegment"
    (fun name => name.contains "Array.findIdx?.loop" &&
      name.contains "Illuminate.AnimationPlayer.findPlayerSegment.spec_")
    findSegmentLoopName {
      params := #[.tobject, .object, .tobject], results := #[.tobject] }
  let parameterUpdates ← findSpecialization module "parameterUpdates"
    (fun name => name.contains "Range.forIn'.loop" &&
      name.contains "Illuminate.AnimationPlayer.parameterUpdates.spec_")
    parameterUpdatesLoopName {
      params := #[.object, .object, .object, .object, .tobject],
      results := #[.object] }
  let optionEq ← findSpecialization module "Option BEq"
    (fun name => name.startsWith "Option.instBEq.beq._at_.")
    optionNatEqName {
      params := #[.tobject, .tobject], results := #[.uint8] }
  let replayTrace ← findSpecialization module "replayTrace"
    (fun name => name.contains "List.forIn'.loop" &&
      name.contains "Illuminate.AnimationPlayer.replayTrace.spec_0")
    replayTraceLoopName {
      params := #[.object, .tobject, .object], results := #[.object] }
  let findCurrentStepFromBackward ← findSpecialization module
    "findCurrentStepFrom backward"
    (fun name => name.contains "whileM.erased" &&
      name.contains "Illuminate.AnimationPlayer.findCurrentStepFrom.spec_0")
    findCurrentStepFromBackwardLoopName {
      params := #[.object, .tobject, .tobject], results := #[.tobject] }
  let findCurrentStepFromForward ← findSpecialization module
    "findCurrentStepFrom forward"
    (fun name => name.contains "whileM.erased" &&
      name.contains "Illuminate.AnimationPlayer.findCurrentStepFrom.spec_1")
    findCurrentStepFromForwardLoopName {
      params := #[.tobject, .object, .tobject, .tobject],
      results := #[.tobject] }
  let crossedPause ← findSpecialization module "findCrossedPauseTo"
    (fun name => name.contains "Range.forIn'.loop" &&
      name.contains "Illuminate.AnimationPlayer.findCrossedPauseTo.spec_")
    findCrossedPauseLoopName {
      params := #[.object, .object, .object, .tobject], results := #[.object] }
  let specializations := #[validateSegments, validateSteps, findCurrentStep,
    findSegment, parameterUpdates, optionEq, replayTrace,
    findCurrentStepFromBackward, findCurrentStepFromForward, crossedPause]
  let externalNames := module.imports.filterMap (fun import_ => import_.declaration?)
  let dormantNames := externalNames.filter (fun name =>
    !specializations.any (fun specialization =>
      specialization.declaration == name))
  unless externalNames.size == specializations.size + dormantExternalNames.size &&
      specializations.all (fun specialization =>
        externalNames.contains specialization.declaration) &&
      dormantNames.size == dormantExternalNames.size &&
      dormantNames.all (fun name => dormantExternalNames.contains name.toString) do
    throw (.unexpectedExternalInventory (externalNames.map Name.toString))
  let linkedFunctions := module.functions.map (fun candidate =>
    let body := candidate.body.map (rewriteInstruction specializations)
    { candidate with body })
  let validationFunctions ← validationStringFunctions
  let linkedFunctions := linkedFunctions ++ functions ++ validationFunctions
  let declarations := specializations.map (fun specialization =>
    specialization.declaration)
  let result : Module := {
    module with
    functions := linkedFunctions
    imports := module.imports.filter (fun import_ =>
      !(import_.declaration?).any declarations.contains)
    exports := helperNames.foldl Fir.Wasm.addUnique module.exports
    runtimeOperations := Fir.Wasm.collectRuntimeOps linkedFunctions }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

end Fir.Wasm.Emit.ResidentIlluminatePlayer
