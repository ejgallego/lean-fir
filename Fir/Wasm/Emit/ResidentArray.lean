import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentArray

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean
open Lean.Compiler

/-!
# Persistent arena arrays for whole-trace execution

The Illuminate package transfers one complete input graph and decodes one
complete output graph. Arrays therefore use a module-private persistent arena
layout: every push allocates a fresh array, and reclamation happens when the
Wasm instance is discarded. JavaScript only writes this documented layout;
all Array semantics below execute in Wasm.
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

/-- ASCII `ARRY`, stored in `opaque.aux0`. -/
def arrayMarker : UInt32 := 0x41525259

def allocateEmptyName : Name := `fir_array_allocate_empty

def externalDeclarations : Array Name := #[
  `Array.size,
  `Array.get!InternalBorrowed,
  `Array.emptyWithCapacity,
  `Array.mkEmpty,
  `Array.getInternalBorrowed,
  `Array.push,
  `Array.get!Internal]

/--
Additional array operations linked only when the captured source closure needs
them.  They are deliberately not part of `externalDeclarations`, so the
historical strict `internalize` frontier remains source-compatible.
-/
def availableExternalDeclarations : Array Name :=
  externalDeclarations ++ #[`Array.usize, `Array.ugetBorrowed, `Array.uget,
    `Array.uset, `Array.replicate]

def externalName (declaration : Name) : Name :=
  Name.mkSimple s!"fir_ext_{declaration.toString.replace "." "_"}"

def externalHelperNames : Array Name :=
  availableExternalDeclarations.map externalName
def helperNames : Array Name := #[allocateEmptyName] ++ externalHelperNames

private def erasedParam : FVarId := ⟨`erased⟩
private def defaultParam : FVarId := ⟨`default⟩
private def arrayParam : FVarId := ⟨`array⟩
private def indexParam : FVarId := ⟨`index⟩
private def proofParam : FVarId := ⟨`proof⟩
private def capacityParam : FVarId := ⟨`capacity⟩
private def valueParam : FVarId := ⟨`value⟩

private def addressLocal : FVarId := ⟨`address⟩
private def sizeLocal : FVarId := ⟨`size⟩
private def indexLocal : FVarId := ⟨`indexValue⟩
private def countLocal : FVarId := ⟨`count⟩
private def sourceCursorLocal : FVarId := ⟨`sourceCursor⟩
private def targetCursorLocal : FVarId := ⟨`targetCursor⟩
private def allocationBytesLocal : FVarId := ⟨`allocationBytes⟩
private def elementLocal : FVarId := ⟨`element⟩
private def rawLocal : FVarId := ⟨`raw⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def taggedResultLocal : FVarId := ⟨`taggedResult⟩

private def elementLoopLabel : FVarId := ⟨`elementLoop⟩
private def byteLoopLabel : FVarId := ⟨`byteLoop⟩
private def copyLoopLabel : FVarId := ⟨`copyLoop⟩

private def equalsConst (kind : AbiKind) (value : UInt32) : List Instruction :=
  [.i32Const kind value, .i32Eq]

private def trapUnless (condition : List Instruction) : List Instruction :=
  condition ++ [.ifElse [] [.unreachable]]

private def requireArray (array : FVarId) : List Instruction :=
  trapUnless ([
    .localGet array,
    .i32Const .uint32 (u32 heapBase),
    .i32LtU] ++ equalsConst .uint32 0) ++
  trapUnless (
    [.localGet array,
      .i32Const .uint32 (u32 (target.heapAlignment - 1)),
      .i32And] ++ equalsConst .uint32 0) ++
  trapUnless (
    [.localGet array,
      .i32Load .uint32 (u32 headerFlagsOffset),
      .i32Const .uint32 (persistentFlag + liveFlag),
      .i32And] ++ equalsConst .uint32 (persistentFlag + liveFlag)) ++
  trapUnless (
    [.localGet array,
      .i32Load .uint32 (u32 headerKindOffset)] ++
      equalsConst .uint32 ObjectKind.opaque.code) ++
  trapUnless (
    [.localGet array,
      .i32Load .uint32 (u32 headerAux0Offset)] ++
      equalsConst .uint32 arrayMarker)

private def loadSize (array : FVarId) : List Instruction := [
  .localGet array,
  .i32Load .uint32 (u32 headerAux1Offset),
  .localSet sizeLocal]

private def decodeIndex : List Instruction := [
  .localGet indexParam,
  .call (.declaration ResidentNumeric.validateNaturalName),
  .localGet indexParam,
  .call (.declaration ResidentNumeric.naturalHighName),
  .i32Const .uint32 0,
  .i32Eq,
  .ifElse [] [.unreachable],
  .localGet indexParam,
  .call (.declaration ResidentNumeric.naturalLowName),
  .localSet indexLocal]

private def storeHeaderWord (offset : Nat) (value : List Instruction) :
    List Instruction :=
  [.localGet addressLocal] ++ value ++ [.i32Store .uint32 (u32 offset)]

private def initializeHeader (newSize : List Instruction) : List Instruction :=
  storeHeaderWord headerKindOffset
      [.i32Const .uint32 ObjectKind.opaque.code] ++
  storeHeaderWord headerFlagsOffset
      [.i32Const .uint32 (persistentFlag + liveFlag)] ++
  storeHeaderWord headerRefCountOffset [.i32Const .uint32 0] ++
  storeHeaderWord headerAllocationBytesOffset
      [.localGet allocationBytesLocal] ++
  storeHeaderWord headerAux0Offset [.i32Const .uint32 arrayMarker] ++
  storeHeaderWord headerAux1Offset newSize ++
  storeHeaderWord headerAux2Offset newSize ++
  storeHeaderWord headerAux3Offset [.i32Const .uint32 0]

private def retypeAddress : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet addressLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .object 0,
  .localSet objectResultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet objectResultLocal,
  .ret]

private def retypeTagged : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet rawLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .tagged 0,
  .localSet taggedResultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet taggedResultLocal,
  .ret]

def allocateEmptyFunction : Function := {
  name := allocateEmptyName
  params := #[]
  results := #[.object]
  locals := #[(addressLocal, .uint32), (allocationBytesLocal, .uint32),
    (savedScratchLocal, .uint32), (objectResultLocal, .object)]
  body := [
    .i32Const .uint32 (u32 headerBytes),
    .localSet allocationBytesLocal,
    .localGet allocationBytesLocal,
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++
    initializeHeader [.i32Const .uint32 0] ++
    retypeAddress }

def sizeFunction : Function := {
  name := externalName `Array.size
  params := #[(erasedParam, .erased), (arrayParam, .object)]
  results := #[.tagged]
  locals := #[(sizeLocal, .uint32), (rawLocal, .uint32),
    (savedScratchLocal, .uint32), (taggedResultLocal, .tagged)]
  body := requireArray arrayParam ++ loadSize arrayParam ++ [
    .localGet sizeLocal,
    .localGet sizeLocal,
    .i32Add,
    .i32Const .uint32 1,
    .i32Add,
    .localSet rawLocal] ++ retypeTagged }

def usizeFunction : Function := {
  name := externalName `Array.usize
  params := #[(erasedParam, .erased), (arrayParam, .object)]
  results := #[.usize]
  locals := #[(sizeLocal, .uint32)]
  body := requireArray arrayParam ++ loadSize arrayParam ++ [
    .localGet sizeLocal,
    .i64ExtendI32U .usize,
    .ret] }

private def elementAddress : List Instruction := [
  .localGet arrayParam,
  .i32Const .uint32 (u32 headerBytes),
  .i32Add,
  .localSet sourceCursorLocal,
  .i32Const .uint32 0,
  .localSet countLocal,
  .loop elementLoopLabel [
    .localGet countLocal,
    .localGet indexLocal,
    .i32LtU,
    .ifElse [
      .localGet sourceCursorLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet sourceCursorLocal,
      .localGet countLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet countLocal,
      .br elementLoopLabel] []]]

private def getBody (useDefault : Bool) : List Instruction :=
  requireArray arrayParam ++ loadSize arrayParam ++ decodeIndex ++ [
    .localGet indexLocal,
    .localGet sizeLocal,
    .i32LtU,
    .ifElse
      (elementAddress ++ [
        .localGet sourceCursorLocal,
        .i32Load .object 0,
        .ret])
      (if useDefault then [.localGetObject defaultParam, .ret]
       else [.unreachable])]

private def getBangFunction (declaration : Name) : Function := {
  name := externalName declaration
  params := #[(erasedParam, .erased), (defaultParam, .tobject),
    (arrayParam, .object), (indexParam, .tobject)]
  results := #[.object]
  locals := #[(sizeLocal, .uint32), (indexLocal, .uint32),
    (countLocal, .uint32), (sourceCursorLocal, .uint32)]
  body := getBody true }

def getBangBorrowedFunction : Function :=
  getBangFunction `Array.get!InternalBorrowed

def getBangOwnedFunction : Function :=
  getBangFunction `Array.get!Internal

def getBorrowedFunction : Function := {
  name := externalName `Array.getInternalBorrowed
  params := #[(erasedParam, .erased), (arrayParam, .object),
    (indexParam, .tobject), (proofParam, .erased)]
  results := #[.object]
  locals := #[(sizeLocal, .uint32), (indexLocal, .uint32),
    (countLocal, .uint32), (sourceCursorLocal, .uint32)]
  body := getBody false }

def ugetBorrowedFunction : Function := {
  name := externalName `Array.ugetBorrowed
  params := #[(erasedParam, .erased), (arrayParam, .object),
    (indexParam, .usize), (proofParam, .erased)]
  results := #[.object]
  locals := #[(sizeLocal, .uint32), (indexLocal, .uint32),
    (countLocal, .uint32), (sourceCursorLocal, .uint32)]
  body := requireArray arrayParam ++ loadSize arrayParam ++ [
    .localGet indexParam,
    .localGet sizeLocal,
    .i64ExtendI32U .usize,
    .i64LtU,
    .ifElse [] [.unreachable],
    .localGet indexParam,
    .i32WrapI64 .uint32,
    .localSet indexLocal] ++ elementAddress ++ [
    .localGet sourceCursorLocal,
    .i32Load .object 0,
    .ret] }

def ugetFunction : Function := {
  name := externalName `Array.uget
  params := #[(erasedParam, .erased), (arrayParam, .object),
    (indexParam, .usize), (proofParam, .erased)]
  results := #[.tobject]
  locals := #[(sizeLocal, .uint32), (indexLocal, .uint32),
    (countLocal, .uint32), (sourceCursorLocal, .uint32)]
  body := requireArray arrayParam ++ loadSize arrayParam ++ [
    .localGet indexParam,
    .localGet sizeLocal,
    .i64ExtendI32U .usize,
    .i64LtU,
    .ifElse [] [.unreachable],
    .localGet indexParam,
    .i32WrapI64 .uint32,
    .localSet indexLocal] ++ elementAddress ++ [
    .localGet sourceCursorLocal,
    .i32Load .tobject 0,
    .ret] }

private def emptyWrapper (declaration : Name) : Function := {
  name := externalName declaration
  params := #[(erasedParam, .erased), (capacityParam, .tobject)]
  results := #[.object]
  locals := #[]
  body := [.call (.declaration allocateEmptyName), .ret] }

def emptyWithCapacityFunction : Function :=
  emptyWrapper `Array.emptyWithCapacity

def mkEmptyFunction : Function := emptyWrapper `Array.mkEmpty

private def allocationBytesBody : List Instruction := [
  .i32Const .uint32 (u32 (headerBytes + target.semanticSlotBytes)),
  .localSet allocationBytesLocal,
  .i32Const .uint32 0,
  .localSet countLocal,
  .loop byteLoopLabel [
    .localGet countLocal,
    .localGet sizeLocal,
    .i32LtU,
    .ifElse [
      .localGet allocationBytesLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet allocationBytesLocal,
      .localGet countLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet countLocal,
      .br byteLoopLabel] []]]

private def exactAllocationBytesBody : List Instruction := [
  .i32Const .uint32 (u32 headerBytes),
  .localSet allocationBytesLocal,
  .i32Const .uint32 0,
  .localSet countLocal,
  .loop byteLoopLabel [
    .localGet countLocal,
    .localGet sizeLocal,
    .i32LtU,
    .ifElse [
      .localGet allocationBytesLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet allocationBytesLocal,
      .localGet countLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet countLocal,
      .br byteLoopLabel] []]]

private def copyElementsBody : List Instruction := [
  .localGet arrayParam,
  .i32Const .uint32 (u32 headerBytes),
  .i32Add,
  .localSet sourceCursorLocal,
  .localGet addressLocal,
  .i32Const .uint32 (u32 headerBytes),
  .i32Add,
  .localSet targetCursorLocal,
  .i32Const .uint32 0,
  .localSet countLocal,
  .loop copyLoopLabel [
    .localGet countLocal,
    .localGet sizeLocal,
    .i32LtU,
    .ifElse [
      .localGet targetCursorLocal,
      .localGet sourceCursorLocal,
      .i32Load .object 0,
      .i32Store .object 0,
      .localGet sourceCursorLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet sourceCursorLocal,
      .localGet targetCursorLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet targetCursorLocal,
      .localGet countLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet countLocal,
      .br copyLoopLabel] []]]

def pushFunction : Function := {
  name := externalName `Array.push
  params := #[(erasedParam, .erased), (arrayParam, .object),
    (valueParam, .tobject)]
  results := #[.object]
  locals := #[(addressLocal, .uint32), (sizeLocal, .uint32),
    (countLocal, .uint32), (sourceCursorLocal, .uint32),
    (targetCursorLocal, .uint32), (allocationBytesLocal, .uint32),
    (savedScratchLocal, .uint32), (objectResultLocal, .object),
    (elementLocal, .object)]
  body := requireArray arrayParam ++ loadSize arrayParam ++
    allocationBytesBody ++ [
      .localGet allocationBytesLocal,
      .call (.declaration ResidentAllocator.allocateName),
      .localSet addressLocal] ++
    initializeHeader [
      .localGet sizeLocal,
      .i32Const .uint32 1,
      .i32Add] ++
    copyElementsBody ++ [
      .localGet targetCursorLocal,
      .localGet valueParam,
      .i32Store .tobject 0] ++
    retypeAddress }

private def copyUpdatedElementsBody : List Instruction := [
  .localGet arrayParam,
  .i32Const .uint32 (u32 headerBytes),
  .i32Add,
  .localSet sourceCursorLocal,
  .localGet addressLocal,
  .i32Const .uint32 (u32 headerBytes),
  .i32Add,
  .localSet targetCursorLocal,
  .i32Const .uint32 0,
  .localSet countLocal,
  .loop copyLoopLabel [
    .localGet countLocal,
    .localGet sizeLocal,
    .i32LtU,
    .ifElse [
      .localGet countLocal,
      .localGet indexLocal,
      .i32Eq,
      .ifElse [
        .localGet targetCursorLocal,
        .localGet valueParam,
        .i32Store .tobject 0] [
        .localGet targetCursorLocal,
        .localGet sourceCursorLocal,
        .i32Load .tobject 0,
        .i32Store .tobject 0],
      .localGet sourceCursorLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet sourceCursorLocal,
      .localGet targetCursorLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet targetCursorLocal,
      .localGet countLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet countLocal,
      .br copyLoopLabel] []]]

def usetFunction : Function := {
  name := externalName `Array.uset
  params := #[(erasedParam, .erased), (arrayParam, .object),
    (indexParam, .usize), (valueParam, .tobject), (proofParam, .erased)]
  results := #[.object]
  locals := #[(addressLocal, .uint32), (sizeLocal, .uint32),
    (indexLocal, .uint32), (countLocal, .uint32),
    (sourceCursorLocal, .uint32), (targetCursorLocal, .uint32),
    (allocationBytesLocal, .uint32), (savedScratchLocal, .uint32),
    (objectResultLocal, .object)]
  body := requireArray arrayParam ++ loadSize arrayParam ++ [
    .localGet indexParam,
    .localGet sizeLocal,
    .i64ExtendI32U .usize,
    .i64LtU,
    .ifElse [] [.unreachable],
    .localGet indexParam,
    .i32WrapI64 .uint32,
    .localSet indexLocal] ++ exactAllocationBytesBody ++ [
    .localGet allocationBytesLocal,
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++ initializeHeader [.localGet sizeLocal] ++
    copyUpdatedElementsBody ++ retypeAddress }

private def fillElementsBody : List Instruction := [
  .localGet addressLocal,
  .i32Const .uint32 (u32 headerBytes),
  .i32Add,
  .localSet targetCursorLocal,
  .i32Const .uint32 0,
  .localSet countLocal,
  .loop copyLoopLabel [
    .localGet countLocal,
    .localGet sizeLocal,
    .i32LtU,
    .ifElse [
      .localGet targetCursorLocal,
      .localGet valueParam,
      .i32Store .tobject 0,
      .localGet targetCursorLocal,
      .i32Const .uint32 (u32 target.semanticSlotBytes),
      .i32Add,
      .localSet targetCursorLocal,
      .localGet countLocal,
      .i32Const .uint32 1,
      .i32Add,
      .localSet countLocal,
      .br copyLoopLabel] []]]

def replicateFunction : Function := {
  name := externalName `Array.replicate
  params := #[(erasedParam, .erased), (indexParam, .tobject),
    (valueParam, .tobject)]
  results := #[.object]
  locals := #[(addressLocal, .uint32), (sizeLocal, .uint32),
    (indexLocal, .uint32), (countLocal, .uint32),
    (targetCursorLocal, .uint32), (allocationBytesLocal, .uint32),
    (savedScratchLocal, .uint32), (objectResultLocal, .object)]
  body := decodeIndex ++ [
    .localGet indexLocal,
    .localSet sizeLocal] ++ exactAllocationBytesBody ++ [
    .localGet allocationBytesLocal,
    .call (.declaration ResidentAllocator.allocateName),
    .localSet addressLocal] ++ initializeHeader [.localGet sizeLocal] ++
    fillElementsBody ++ retypeAddress }

def functions : Array Function := #[
  allocateEmptyFunction,
  sizeFunction,
  usizeFunction,
  getBangBorrowedFunction,
  emptyWithCapacityFunction,
  mkEmptyFunction,
  getBorrowedFunction,
  ugetBorrowedFunction,
  ugetFunction,
  pushFunction,
  getBangOwnedFunction,
  usetFunction,
  replicateFunction]

private partial def rewriteInstruction (declarations : Array Name) : Instruction → Instruction
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

private def expectedSignature? (declaration : Name) : Option Signature :=
  if declaration == `Array.size then
    some { params := #[.erased, .object], results := #[.tagged] }
  else if declaration == `Array.usize then
    some { params := #[.erased, .object], results := #[.usize] }
  else if declaration == `Array.get!InternalBorrowed ||
      declaration == `Array.get!Internal then
    some {
      params := #[.erased, .tobject, .object, .tobject]
      results := #[.object] }
  else if declaration == `Array.emptyWithCapacity ||
      declaration == `Array.mkEmpty then
    some { params := #[.erased, .tobject], results := #[.object] }
  else if declaration == `Array.getInternalBorrowed then
    some {
      params := #[.erased, .object, .tobject, .erased]
      results := #[.object] }
  else if declaration == `Array.ugetBorrowed then
    some {
      params := #[.erased, .object, .usize, .erased]
      results := #[.object] }
  else if declaration == `Array.uget then
    some {
      params := #[.erased, .object, .usize, .erased]
      results := #[.tobject] }
  else if declaration == `Array.uset then
    some {
      params := #[.erased, .object, .usize, .tobject, .erased]
      results := #[.object] }
  else if declaration == `Array.replicate then
    some {
      params := #[.erased, .tobject, .tobject]
      results := #[.object] }
  else if declaration == `Array.push then
    some { params := #[.erased, .object, .tobject], results := #[.object] }
  else none

private def internalizeSelected (module : Module) (declarations : Array Name) :
    Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  for name in #[ResidentNumeric.validateNaturalName,
      ResidentNumeric.naturalLowName, ResidentNumeric.naturalHighName] do
    unless module.functions.any (·.name == name) do
      throw (.missingNumericHelper name)
  let needsEmptyAllocator := declarations.contains `Array.emptyWithCapacity ||
    declarations.contains `Array.mkEmpty
  let selectedHelperNames := declarations.map externalName
  let selectedHelperNames := if needsEmptyAllocator then
    #[allocateEmptyName] ++ selectedHelperNames
  else selectedHelperNames
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
  let selectedFunctions := functions.filter fun function =>
    selectedHelperNames.contains function.name
  let linkedFunctions := linkedFunctions ++ selectedFunctions
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

/-- Internalize the complete historical array frontier, rejecting omissions. -/
def internalize (module : Module) : Except LinkError Module :=
  internalizeSelected module externalDeclarations

/--
Internalize exactly the array operations imported by a source closure.  This
keeps narrowly linked resident packages independent of unrelated array APIs
while preserving the same fail-closed signature checks as `internalize`.
-/
def internalizeAvailable (module : Module) : Except LinkError Module :=
  let declarations := availableExternalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
  internalizeSelected module declarations

private def exampleDeclarations : Array Name :=
  #[`Array.uget, `Array.uset, `Array.replicate]

private def exampleExternalTypes (declaration : Name) : ExternalTypes :=
  let erased := LCNF.ImpureType.erased
  let object := LCNF.ImpureType.object
  let tobject := LCNF.ImpureType.tobject
  let usize := LCNF.ImpureType.usize
  if declaration == `Array.uget then
    { params := #[erased, object, usize, erased], result := tobject }
  else if declaration == `Array.uset then
    { params := #[erased, object, usize, tobject, erased], result := object }
  else
    { params := #[erased, tobject, tobject], result := object }

private def exampleExternalImport (declaration : Name) : Import := {
  key := .external declaration
  moduleName := "lean.extern"
  itemName := declaration.toString
  signature := (expectedSignature? declaration).get!
  externalTypes? := some (exampleExternalTypes declaration) }

/-- Closed generation-only probe for the array helpers added by the compact
Illuminate validation closure. -/
def residentExampleModule : Except String Module := do
  let numeric ← ResidentNumeric.residentExampleModule
  let module : Module := {
    numeric with
    imports := numeric.imports ++ exampleDeclarations.map exampleExternalImport }
  internalizeSelected module exampleDeclarations
    |>.mapError fun error => s!"array: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <| exampleDeclarations.map fun declaration =>
      Json.mkObj [
        ("sourceEntry", declaration.toString),
        ("entry", externalName declaration |>.toString)]),
    ("imports", Json.arr #[]),
    ("status", "generation-ready; W6 array contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      exampleDeclarations.all fun declaration =>
        module.exports.contains (externalName declaration) &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentArray
