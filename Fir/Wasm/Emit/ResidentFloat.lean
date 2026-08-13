import Fir.Wasm.Emit.ResidentNumeric

namespace Fir.Wasm.Emit.ResidentFloat

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

/-!
# Wasm-resident Float frontier

This generation helper internalizes the exact Lean 4.33 floating operations
supported by the resident runtime. It deliberately assigns Lean extern
semantics here, after the shared symbolic Wasm instruction layer has landed
independently. Other standard Float declarations remain at the checked
external-runtime frontier.
-/

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | missingNumericHelper (name : Name)
  | missingOperation (name : Name)
  | reservedDeclaration (name : Name)
  | missingExternal (name : Name)
  | incompatibleExternal (name : Name)
  | incompatibleMemory
  | projectionOffsetOverflow (value : Nat)
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def objectParam : FVarId := ⟨`object⟩
private def valueParam : FVarId := ⟨`value⟩
private def leftParam : FVarId := ⟨`left⟩
private def rightParam : FVarId := ⟨`right⟩
private def addressLocal : FVarId := ⟨`address⟩
private def raw32Local : FVarId := ⟨`raw32⟩
private def raw64Local : FVarId := ⟨`raw64⟩
private def lowLocal : FVarId := ⟨`low⟩
private def highLocal : FVarId := ⟨`high⟩
private def floatLocal : FVarId := ⟨`floatValue⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def objectResultLocal : FVarId := ⟨`objectResult⟩
private def uint8ResultLocal : FVarId := ⟨`uint8Result⟩

/-- Private `boxed.aux0` marker for an eight-byte Float payload. W6 may later
promote this marker into its proved scalar-box descriptor table. -/
def floatBoxMarker : UInt32 := 6

def boxName : Name := `fir_float_box
def unboxName : Name := `fir_float_unbox

def scalarProjectionName (width byteOffset : Nat) : Name :=
  Name.mkSimple s!"fir_sproj_f64_{width}_{byteOffset}"

def externalDeclarations : Array Name := #[
  `Float.sub,
  `Float.div,
  `Float.mul,
  `Float.decLt,
  `Float.decLe,
  `Float.round,
  `Float.toUInt64,
  `UInt64.toNat]

def externalName (declaration : Name) : Name :=
  Name.mkSimple s!"fir_ext_{declaration.toString.replace "." "_"}"

def externalHelperNames : Array Name := externalDeclarations.map externalName

private def equalsConst (kind : AbiKind) (value : UInt32) : List Instruction :=
  [.i32Const kind value, .i32Eq]

private def requireHeapAddress (object : FVarId) : List Instruction :=
  [.localGet object,
    .i32Const .uint32 (u32 heapBase),
    .i32LtU,
    .ifElse [.unreachable] [],
    .localGet object,
    .i32Const .uint32 (u32 (target.heapAlignment - 1)),
    .i32And] ++
  equalsConst .uint32 0 ++
  [.ifElse [] [.unreachable]]

private def requireHeader (object : FVarId) (kind marker : UInt32) : List Instruction :=
  requireHeapAddress object ++
  [.localGet object,
    .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 liveFlag,
    .i32And] ++
  equalsConst .uint32 liveFlag ++
  [.ifElse [] [.unreachable],
    .localGet object,
    .i32Load .uint32 (u32 headerKindOffset)] ++
  equalsConst .uint32 kind ++
  [.ifElse [] [.unreachable]] ++
  (if marker == 0 then [] else
    [.localGet object,
      .i32Load .uint32 (u32 headerAux0Offset)] ++
    equalsConst .uint32 marker ++
    [.ifElse [] [.unreachable]])

private def store32 (kind : AbiKind) (value : List Instruction)
    (offset : Nat) : List Instruction :=
  [.localGet addressLocal] ++ value ++ [.i32Store kind (u32 offset)]

private def zeroAllocation (allocationBytes : Nat) : List Instruction :=
  (List.range (allocationBytes / 4)).flatMap fun index =>
    store32 .uint32 [.i32Const .uint32 0] (4 * index)

private def retypeAddress (result : AbiKind) : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet addressLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load result 0,
  .localSet objectResultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet objectResultLocal,
  .ret]

private def retypeUInt8 : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet raw32Local,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load8U .uint8 0,
  .localSet uint8ResultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet uint8ResultLocal,
  .ret]

private def retypeNatural : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet raw32Local,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .tobject 0,
  .localSet objectResultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet objectResultLocal,
  .ret]

def boxFunction : Function :=
  let allocationBytes := align8 (headerBytes + target.semanticSlotBytes)
  {
    name := boxName
    params := #[(valueParam, .float)]
    results := #[.object]
    locals := #[(addressLocal, .uint32), (savedScratchLocal, .uint32),
      (objectResultLocal, .object)]
    body :=
      [.i32Const .uint32 (u32 allocationBytes),
        .call (.declaration ResidentAllocator.allocateName),
        .localSet addressLocal] ++
      zeroAllocation allocationBytes ++
      store32 .uint32 [.i32Const .uint32 ObjectKind.boxed.code]
        headerKindOffset ++
      store32 .uint32 [.i32Const .uint32 liveFlag]
        headerFlagsOffset ++
      store32 .uint32 [.i32Const .uint32 1]
        headerRefCountOffset ++
      store32 .uint32 [.i32Const .uint32 (u32 allocationBytes)]
        headerAllocationBytesOffset ++
      store32 .uint32 [.i32Const .uint32 floatBoxMarker]
        headerAux0Offset ++
      store32 .uint32 [.i32Const .uint32 8]
        headerAux1Offset ++
      [.localGet addressLocal,
        .localGet valueParam,
        .i64ReinterpretF64 .uint64,
        .i64Store .uint64 (u32 headerBytes)] ++
      retypeAddress .object }

def unboxFunction : Function := {
  name := unboxName
  params := #[(objectParam, .tobject)]
  results := #[.float]
  locals := #[]
  body := requireHeader objectParam ObjectKind.boxed.code floatBoxMarker ++ [
    .localGet objectParam,
    .i64Load .uint64 (u32 headerBytes),
    .f64ReinterpretI64 .float,
    .ret] }

def scalarProjectionFunction (width byteOffset : Nat) : Except LinkError Function := do
  let offset := headerBytes + target.semanticSlotBytes * width + byteOffset
  unless offset < UInt32.size do
    throw (.projectionOffsetOverflow offset)
  return {
    name := scalarProjectionName width byteOffset
    params := #[(objectParam, .tobject)]
    results := #[.float]
    locals := #[]
    body := requireHeader objectParam ObjectKind.constructor.code 0 ++ [
      .localGet objectParam,
      .i64Load .uint64 (u32 offset),
      .f64ReinterpretI64 .float,
      .ret] }

private def runtimeName? : RuntimeOp → Option Name
  | .box .float .object => some boxName
  | .unbox .float => some unboxName
  | .scalarProj width byteOffset .float =>
      some (scalarProjectionName width byteOffset)
  | _ => none

private def runtimeFunction (operation : RuntimeOp) : Except LinkError Function :=
  match operation with
  | .box .float .object => pure boxFunction
  | .unbox .float => pure unboxFunction
  | .scalarProj width byteOffset .float => scalarProjectionFunction width byteOffset
  | _ => throw (.missingOperation `unsupportedFloatRuntimeOperation)

private partial def rewriteRuntimeInstruction (operation : RuntimeOp)
    (name : Name) : Instruction → Instruction
  | .call (.runtime candidate) =>
      if candidate == operation then .call (.declaration name)
      else .call (.runtime candidate)
  | .block label body =>
      .block label (body.map (rewriteRuntimeInstruction operation name))
  | .loop label body =>
      .loop label (body.map (rewriteRuntimeInstruction operation name))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteRuntimeInstruction operation name))
        (elseBody.map (rewriteRuntimeInstruction operation name))
  | instruction => instruction

private def rewriteRuntimeFunction (operation : RuntimeOp) (name : Name)
    (function : Function) : Function :=
  { function with body := function.body.map (rewriteRuntimeInstruction operation name) }

private def internalizeRuntimeOne (module : Module) (operation : RuntimeOp) :
    Except LinkError Module := do
  let some name := runtimeName? operation |
    throw (.missingOperation `unsupportedFloatRuntimeOperation)
  if module.imports.any (·.declaration? == some name) ||
      module.functions.any (·.name == name) || module.exports.contains name then
    throw (.reservedDeclaration name)
  let helper ← runtimeFunction operation
  let functions := (module.functions.map
    (rewriteRuntimeFunction operation name)).push helper
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  return {
    module with
    functions
    runtimeOperations
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    exports := Fir.Wasm.addUnique module.exports name }

private def internalizeRuntime (module : Module) : Except LinkError Module := do
  let operations := module.runtimeOperations.filter (runtimeName? · |>.isSome)
  operations.foldlM (init := module) internalizeRuntimeOne

private def binaryFloatFunction (declaration : Name) (instruction : Instruction) : Function := {
  name := externalName declaration
  params := #[(leftParam, .float), (rightParam, .float)]
  results := #[.float]
  locals := #[]
  body := [.localGet leftParam, .localGet rightParam, instruction, .ret] }

def subFunction : Function := binaryFloatFunction `Float.sub .f64Sub
def divFunction : Function := binaryFloatFunction `Float.div .f64Div
def mulFunction : Function := binaryFloatFunction `Float.mul .f64Mul

def decLtFunction : Function := {
  name := externalName `Float.decLt
  params := #[(leftParam, .float), (rightParam, .float)]
  results := #[.uint8]
  locals := #[(raw32Local, .uint32), (savedScratchLocal, .uint32),
    (uint8ResultLocal, .uint8)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .f64Lt,
    .localSet raw32Local] ++ retypeUInt8 }

def decLeFunction : Function := {
  name := externalName `Float.decLe
  params := #[(leftParam, .float), (rightParam, .float)]
  results := #[.uint8]
  locals := #[(raw32Local, .uint32), (savedScratchLocal, .uint32),
    (uint8ResultLocal, .uint8)]
  body := [
    .localGet leftParam,
    .localGet rightParam,
    .f64Le,
    .localSet raw32Local] ++ retypeUInt8 }

def roundFunction : Function := {
  name := externalName `Float.round
  params := #[(valueParam, .float)]
  results := #[.float]
  locals := #[(floatLocal, .float)]
  body := [
    .localGet valueParam,
    .f64Const 0,
    .f64Eq,
    .ifElse
      [.localGet valueParam, .localSet floatLocal]
      [.localGet valueParam,
        .f64Const 0,
        .f64Lt,
        .ifElse
          [.localGet valueParam,
            .f64Const 0x3fe0000000000000,
            .f64Sub,
            .f64Ceil,
            .localSet floatLocal]
          [.localGet valueParam,
            .f64Const 0x3fe0000000000000,
            .f64Add,
            .f64Floor,
            .localSet floatLocal]],
    .localGet floatLocal,
    .ret] }

def toUInt64Function : Function := {
  name := externalName `Float.toUInt64
  params := #[(valueParam, .float)]
  results := #[.uint64]
  locals := #[]
  body := [.localGet valueParam, .i64TruncSatF64U .uint64, .ret] }

def uint64ToNatFunction : Function := {
  name := externalName `UInt64.toNat
  params := #[(valueParam, .uint64)]
  results := #[.tobject]
  locals := #[(lowLocal, .uint32), (highLocal, .uint32),
    (raw32Local, .uint32), (savedScratchLocal, .uint32),
    (objectResultLocal, .tobject)]
  body := [
    .localGet valueParam,
    .i32WrapI64 .uint32,
    .localSet lowLocal,
    .localGet valueParam,
    .i64Const .uint64 32,
    .i64ShrU,
    .i32WrapI64 .uint32,
    .localSet highLocal,
    .localGet lowLocal,
    .localGet highLocal,
    .call (.declaration ResidentNumeric.makeNaturalName),
    .localSet raw32Local] ++ retypeNatural }

def externalFunctions : Array Function := #[
  subFunction,
  divFunction,
  mulFunction,
  decLtFunction,
  decLeFunction,
  roundFunction,
  toUInt64Function,
  uint64ToNatFunction]

private partial def rewriteExternalInstruction : Instruction → Instruction
  | .call (.declaration declaration) =>
      if externalDeclarations.contains declaration then
        .call (.declaration (externalName declaration))
      else
        .call (.declaration declaration)
  | .block label body => .block label (body.map rewriteExternalInstruction)
  | .loop label body => .loop label (body.map rewriteExternalInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map rewriteExternalInstruction)
        (elseBody.map rewriteExternalInstruction)
  | instruction => instruction

private def expectedExternalSignature? (declaration : Name) : Option Signature :=
  if declaration == `Float.sub || declaration == `Float.div ||
      declaration == `Float.mul then
    some { params := #[.float, .float], results := #[.float] }
  else if declaration == `Float.decLt || declaration == `Float.decLe then
    some { params := #[.float, .float], results := #[.uint8] }
  else if declaration == `Float.round then
    some { params := #[.float], results := #[.float] }
  else if declaration == `Float.toUInt64 then
    some { params := #[.float], results := #[.uint64] }
  else if declaration == `UInt64.toNat then
    some { params := #[.uint64], results := #[.tobject] }
  else none

/-- Internalize the exact declaration-and-signature-checked Float frontier. -/
def internalize (module : Module) (validate : Bool := true) : Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  for name in #[ResidentNumeric.makeNaturalName, ResidentNumeric.naturalLowName,
      ResidentNumeric.naturalHighName] do
    unless module.functions.any (·.name == name) do
      throw (.missingNumericHelper name)
  for declaration in externalDeclarations do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.missingExternal declaration)
    let some signature := expectedExternalSignature? declaration |
      throw (.incompatibleExternal declaration)
    unless imports[0]!.signature == signature do
      throw (.incompatibleExternal declaration)
  let module ← internalizeRuntime module
  for name in externalHelperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) || module.exports.contains name then
      throw (.reservedDeclaration name)
  let functions := module.functions.map fun function =>
    { function with body := function.body.map rewriteExternalInstruction }
  let functions := functions ++ externalFunctions
  let imports := module.imports.filter fun import_ =>
    match import_.declaration? with
    | some declaration => !externalDeclarations.contains declaration
    | none => true
  let result : Module := {
    module with
    functions
    imports
    exports := externalHelperNames.foldl Fir.Wasm.addUnique module.exports
    runtimeOperations := Fir.Wasm.collectRuntimeOps functions }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

/-- Internalize the supported Float/runtime operations present in a source
closure while retaining the strict historical `internalize` inventory above. -/
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
  for name in #[ResidentNumeric.makeNaturalName, ResidentNumeric.naturalLowName,
      ResidentNumeric.naturalHighName] do
    unless module.functions.any (·.name == name) do
      throw (.missingNumericHelper name)
  let present := externalDeclarations.filter fun declaration =>
    module.imports.any (·.declaration? == some declaration)
  for declaration in present do
    let imports := module.imports.filter (·.declaration? == some declaration)
    unless imports.size == 1 do
      throw (.incompatibleExternal declaration)
    let some signature := expectedExternalSignature? declaration |
      throw (.incompatibleExternal declaration)
    unless imports[0]!.signature == signature do
      throw (.incompatibleExternal declaration)
  let module ← internalizeRuntime module
  for name in externalHelperNames do
    if module.imports.any (·.declaration? == some name) ||
        module.functions.any (·.name == name) || module.exports.contains name then
      throw (.reservedDeclaration name)
  let functions := module.functions.map fun function =>
    { function with body := function.body.map rewriteExternalInstruction }
  let functions := functions ++ externalFunctions
  let imports := module.imports.filter fun import_ =>
    match import_.declaration? with
    | some declaration => !present.contains declaration
    | none => true
  let result : Module := {
    module with
    functions
    imports
    exports := externalHelperNames.foldl Fir.Wasm.addUnique module.exports
    runtimeOperations := Fir.Wasm.collectRuntimeOps functions }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

end Fir.Wasm.Emit.ResidentFloat
