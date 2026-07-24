import Fir.Wasm.Concrete.Runtime
import Fir.Wasm.Emit.Binary

namespace Fir.Wasm.Emit.ResidentRuntime

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

/--
Reserved declaration/export name for the first Wasm-resident runtime helper.
Later import-internalization rewrites `.runtime .getTag` calls to this exact
declaration instead of retaining the semantic-host import.
-/
def getTagName : Name := `fir_getTag

def isSharedName : Name := `fir_isShared

def objectParam : FVarId := ⟨`object⟩

def resultLocal : FVarId := ⟨`result⟩

def sharedLocal : FVarId := ⟨`shared⟩

private def offset (value : Nat) : UInt32 := UInt32.ofNat value

private def equalsConst (kind : AbiKind) (value : UInt32) : List Instruction :=
  [.i32Const kind value, .i32Eq]

private def loadFlags : List Instruction :=
  [.localGet objectParam, .i32Load .uint32 (offset headerFlagsOffset)]

private def requireFlag (flag : UInt32) (success : List Instruction) : List Instruction :=
  loadFlags ++
    [.i32Const .uint32 flag, .i32And] ++
    equalsConst .uint32 flag ++
    [.ifElse success [.unreachable]]

private def promotedTagBody : List Instruction :=
  requireFlag persistentFlag <|
    [.localGet objectParam, .i32Load .uint32 (offset headerAux0Offset)] ++
    equalsConst .uint32 promotedTagMarker ++
    [.ifElse
      [.localGet objectParam,
        .i64Load .uint64 (offset headerBytes),
        .i32WrapI64 .uint32,
        .localSet resultLocal]
      [.unreachable]]

private def heapKindBody : List Instruction :=
  [.localGet objectParam,
    .i32Load .uint32 (offset headerKindOffset)] ++
  equalsConst .uint32 ObjectKind.constructor.code ++
  [.ifElse
    [.localGet objectParam,
      .i32Load .uint32 (offset headerAux0Offset),
      .localSet resultLocal]
    ([.localGet objectParam,
      .i32Load .uint32 (offset headerKindOffset)] ++
      equalsConst .uint32 ObjectKind.natural.code ++
      [.ifElse promotedTagBody [.unreachable]])]

private def alignedHeapBody : List Instruction :=
  requireFlag liveFlag heapKindBody

private def heapBody : List Instruction :=
  [.localGet objectParam] ++
    equalsConst .tobject 0 ++
    [.ifElse
      [.unreachable]
      ([.localGet objectParam,
        .i32Const .uint32 (UInt32.ofNat (target.heapAlignment - 1)),
        .i32And] ++
        equalsConst .uint32 0 ++
        [.ifElse alignedHeapBody [.unreachable]])]

private def immediateBody : List Instruction :=
  [.localGet objectParam,
    .i32Const .uint32 1,
    .i32ShrU,
    .localSet resultLocal]

/--
Executable valid-input portion of W6 `readTag`:

* odd words decode as immediate tags;
* live constructor headers return `aux0`;
* live persistent natural headers carrying the promoted-tag marker return the
  low wasm32 lane of their 64-bit payload.

The full theorem relating this helper to the W6 `getTag` contract is
intentionally owned by the proof lane. This generation definition traps on
the checked invalid cases it recognizes and relies on the W6 refinement
precondition for the remaining header-allocation invariants.
-/
def getTagFunction : Function := {
  name := getTagName
  params := #[(objectParam, .tobject)]
  results := #[.uint32]
  locals := #[(resultLocal, .uint32)]
  body :=
    [.localGet objectParam,
      .i32Const .uint32 1,
      .i32And,
      .ifElse immediateBody heapBody,
      .localGet resultLocal,
      .ret] }

def residentMemory : MemoryDecl := {
  pagesMin := 1
  exportName := some "memory" }

private def setShared (value : UInt32) : List Instruction :=
  [.i32Const .uint8 value, .localSet sharedLocal]

private def refCountSharingBody : List Instruction :=
  [.localGet objectParam,
    .i32Load .uint32 (offset headerRefCountOffset)] ++
  equalsConst .uint32 1 ++
  [.ifElse (setShared 0) (setShared 1)]

private def sharingHeaderBody : List Instruction :=
  loadFlags ++
    [.i32Const .uint32 persistentFlag, .i32And] ++
    equalsConst .uint32 persistentFlag ++
    [.ifElse (setShared 1) refCountSharingBody]

private def isSharedAlignedHeapBody : List Instruction :=
  requireFlag liveFlag sharingHeaderBody

private def isSharedHeapBody : List Instruction :=
  [.localGet objectParam] ++
    equalsConst .tobject 0 ++
    [.ifElse
      [.unreachable]
      ([.localGet objectParam,
        .i32Const .uint32 (UInt32.ofNat (target.heapAlignment - 1)),
        .i32And] ++
        equalsConst .uint32 0 ++
        [.ifElse isSharedAlignedHeapBody [.unreachable]])]

/--
Executable valid-input portion of W6 `readIsShared`. Tagged immediates and
persistent objects return one; a live ordinary heap object returns zero
exactly when its reference count is one.

As with `getTagFunction`, the proof that this helper implements the W6
contract on related states remains a separate proof-lane theorem.
-/
def isSharedFunction : Function := {
  name := isSharedName
  params := #[(objectParam, .tobject)]
  results := #[.uint8]
  locals := #[(sharedLocal, .uint8)]
  body :=
    [.localGet objectParam,
      .i32Const .uint32 1,
      .i32And,
      .ifElse (setShared 1) isSharedHeapBody,
      .localGet sharedLocal,
      .ret] }

def getTagModule : Module := {
  imports := #[]
  functions := #[getTagFunction]
  exports := #[getTagName]
  initializers := #[]
  runtimeOperations := #[]
  memory := some residentMemory }

def isSharedModule : Module := {
  imports := #[]
  functions := #[isSharedFunction]
  exports := #[isSharedName]
  initializers := #[]
  runtimeOperations := #[]
  memory := some residentMemory }

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingOperation (name : Name)
  | reservedDeclaration (name : Name)
  | unsupportedProjection (width offset : Nat) (result : AbiKind)
  | unsupportedClosureProjection (index : Nat) (result : AbiKind)
  | unsupportedClosureMatch
  | missingClosureTarget (function : Name)
  | closureMetadataOverflow (value : Nat)
  | projectionOffsetOverflow (value : Nat)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def objectProjectionSuffix? : AbiKind → Option String
  | .object => some "object"
  | .tagged => some "tagged"
  | .tobject => some "tobject"
  | .erased => some "erased"
  | _ => none

/--
Reserved declaration/export name for one supported resident projection.
The full semantic descriptor is encoded in the name so two distinct runtime
imports can never alias one helper.
-/
def readProjectionName? : RuntimeOp → Option Name
  | .objectProj index result =>
      (objectProjectionSuffix? result).map fun suffix =>
        Name.mkSimple s!"fir_oproj_{index}_{suffix}"
  | .scalarProj width byteOffset .uint8 =>
      some <| Name.mkSimple s!"fir_sproj_u8_{width}_{byteOffset}"
  | _ => none

def supportsReadProjection (operation : RuntimeOp) : Bool :=
  (readProjectionName? operation).isSome

private def checkedProjectionOffset (value : Nat) : Except LinkError UInt32 :=
  if value < UInt32.size then
    pure (UInt32.ofNat value)
  else
    throw (.projectionOffsetOverflow value)

private def liveConstructorProjectionBody
    (load : List Instruction) : List Instruction :=
  requireFlag liveFlag <|
    [.localGet objectParam,
      .i32Load .uint32 (offset headerKindOffset)] ++
    equalsConst .uint32 ObjectKind.constructor.code ++
    [.ifElse load [.unreachable]]

private def projectionHeapBody (load : List Instruction) : List Instruction :=
  [.localGet objectParam] ++
    equalsConst .tobject 0 ++
    [.ifElse
      [.unreachable]
      ([.localGet objectParam,
        .i32Const .uint32 (UInt32.ofNat (target.heapAlignment - 1)),
        .i32And] ++
        equalsConst .uint32 0 ++
        [.ifElse (liveConstructorProjectionBody load) [.unreachable]])]

private def objectProjectionFunction (index : Nat) (result : AbiKind) :
    Except LinkError Function := do
  let some name := readProjectionName? (.objectProj index result) |
    throw (.unsupportedProjection index 0 result)
  let fieldOffset ← checkedProjectionOffset <|
    headerBytes + target.semanticSlotBytes * index
  return {
    name
    params := #[(objectParam, .tobject)]
    results := #[result]
    locals := #[(resultLocal, result)]
    body := projectionHeapBody
      [.localGet objectParam,
        .i32Load result fieldOffset,
        .localSet resultLocal] ++
      [.localGet resultLocal, .ret] }

private def scalarUInt8ProjectionFunction (width byteOffset : Nat) :
    Except LinkError Function := do
  let some name := readProjectionName? (.scalarProj width byteOffset .uint8) |
    throw (.unsupportedProjection width byteOffset .uint8)
  let fieldOffset ← checkedProjectionOffset <|
    headerBytes + target.semanticSlotBytes * width + byteOffset
  return {
    name
    params := #[(objectParam, .tobject)]
    results := #[.uint8]
    locals := #[(resultLocal, .uint8)]
    body := projectionHeapBody
      [.localGet objectParam,
        .i32Load8U .uint8 fieldOffset,
        .localSet resultLocal] ++
      [.localGet resultLocal, .ret] }

private def readProjectionFunction (operation : RuntimeOp) :
    Except LinkError Function :=
  match operation with
  | .objectProj index result => objectProjectionFunction index result
  | .scalarProj width byteOffset .uint8 =>
      scalarUInt8ProjectionFunction width byteOffset
  | .scalarProj width byteOffset result =>
      throw (.unsupportedProjection width byteOffset result)
  | _ => throw (.unsupportedProjection 0 0 .erased)

private partial def rewriteRuntimeInstruction (operation : RuntimeOp)
    (name : Name) : Instruction → Instruction
  | .call (.runtime candidate) =>
      if candidate == operation then
        .call (.declaration name)
      else
        .call (.runtime candidate)
  | .block label body =>
      .block label (body.map (rewriteRuntimeInstruction operation name))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteRuntimeInstruction operation name))
        (elseBody.map (rewriteRuntimeInstruction operation name))
  | instruction => instruction

private def rewriteRuntimeFunction (operation : RuntimeOp) (name : Name)
    (function : Function) : Function :=
  { function with
    body := function.body.map (rewriteRuntimeInstruction operation name) }

/--
Internalize one semantic runtime import in an already validated symbolic
module. Runtime imports are rebuilt from the rewritten function bodies
because their presentation names contain ordinals; external declaration
imports retain their original stable names and order.
-/
private def internalizeOperation (operation : RuntimeOp) (name : Name)
    (function : Function) (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.runtimeOperations.contains operation do
    throw (.missingOperation name)
  if module.imports.any (·.declaration? == some name) then
    throw (.reservedDeclaration name)
  let memory ←
    match module.memory with
    | none => pure residentMemory
    | some memory =>
        unless memory == residentMemory do
          throw .incompatibleMemory
        pure memory
  let functions := module.functions.map (rewriteRuntimeFunction operation name)
  let functions ←
    match functions.find? (·.name == name) with
    | none => pure (functions.push function)
    | some existing =>
        unless existing == function do
          throw (.reservedDeclaration name)
        pure functions
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
  let result : Module := {
    module with
    imports
    functions
    exports := Fir.Wasm.addUnique module.exports name
    runtimeOperations
    memory := some memory }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

def internalizeGetTag (module : Module) : Except LinkError Module :=
  internalizeOperation .getTag getTagName getTagFunction module

def internalizeIsShared (module : Module) : Except LinkError Module :=
  internalizeOperation .isShared isSharedName isSharedFunction module

/--
Internalize every object projection and packed `UInt8` projection supported by
the current resident load surface. Other scalar widths stay explicit semantic
imports until their typed load instructions land.

The helpers trap on recognized non-heap, misaligned, dead, and non-constructor
inputs. Their generation relies on the W6 related-state precondition for
descriptor bounds and packed-coordinate validity; proving that implication is
separate proof-lane work.
-/
def internalizeReadProjections (module : Module) : Except LinkError Module := do
  let operations := module.runtimeOperations.filter supportsReadProjection
  operations.foldlM (init := module) fun result operation => do
    let some name := readProjectionName? operation |
      throw (.unsupportedProjection 0 0 .erased)
    let function ← readProjectionFunction operation
    internalizeOperation operation name function result

/-- The exact projection family exercised by compiler-produced Lean 4.32 `prettyM`. -/
def prettyFormatReadProjections : Array RuntimeOp := #[
  .objectProj 0 .object,
  .objectProj 0 .tobject,
  .objectProj 1 .tobject,
  .objectProj 2 .tobject,
  .scalarProj 0 0 .uint8,
  .scalarProj 1 0 .uint8,
  .scalarProj 1 1 .uint8,
  .scalarProj 2 0 .uint8]

/--
Import-free module exposing the complete read-projection family needed by
`prettyM`, independently of compiler linking.
-/
def prettyFormatReadProjectionModule : Except LinkError Module := do
  let functions ← prettyFormatReadProjections.mapM readProjectionFunction
  return {
    imports := #[]
    functions
    exports := functions.map (·.name)
    initializers := #[]
    runtimeOperations := #[]
    memory := some residentMemory }

private def closureProjectionSuffix? : AbiKind → Option String
  | .object => some "object"
  | .tobject => some "tobject"
  | .uint8 => some "uint8"
  | .uint32 => some "uint32"
  | _ => none

def closureProjectionCoordinate? : RuntimeOp → Option (Nat × AbiKind)
  | .closureProj _ _ _ index result =>
      if (closureProjectionSuffix? result).isSome then
        some (index, result)
      else
        none
  | _ => none

/--
Resident closure-capture helpers are shared by descriptors with the same
physical slot and result kind. Function/arity/fixed metadata is guaranteed by
the compiler call site and the W6 related-state precondition; the later
correctness theorem recovers those semantic checks.
-/
def closureProjectionName? (operation : RuntimeOp) : Option Name := do
  let (index, result) ← closureProjectionCoordinate? operation
  let suffix ← closureProjectionSuffix? result
  return Name.mkSimple s!"fir_cproj_{index}_{suffix}"

def supportsClosureProjection (operation : RuntimeOp) : Bool :=
  (closureProjectionName? operation).isSome

private def liveClosureBody
    (load : List Instruction) : List Instruction :=
  requireFlag liveFlag <|
    [.localGet objectParam,
      .i32Load .uint32 (offset headerKindOffset)] ++
    equalsConst .uint32 ObjectKind.closure.code ++
    [.ifElse load [.unreachable]]

private def closureHeapBody
    (load : List Instruction) : List Instruction :=
  [.localGet objectParam] ++
    equalsConst .tobject 0 ++
    [.ifElse
      [.unreachable]
      ([.localGet objectParam,
        .i32Const .uint32 (UInt32.ofNat (target.heapAlignment - 1)),
        .i32And] ++
        equalsConst .uint32 0 ++
        [.ifElse (liveClosureBody load) [.unreachable]])]

private def closureProjectionFunction (index : Nat) (result : AbiKind) :
    Except LinkError Function := do
  let probe : RuntimeOp :=
    .closureProj `resident (index + 2) (index + 1) index result
  let some name := closureProjectionName? probe |
    throw (.unsupportedClosureProjection index result)
  let fieldOffset ← checkedProjectionOffset <|
    headerBytes + target.semanticSlotBytes * index
  return {
    name
    params := #[(objectParam, .tobject)]
    results := #[result]
    locals := #[(resultLocal, result)]
    body := closureHeapBody
      [.localGet objectParam,
        .i32Load result fieldOffset,
        .localSet resultLocal] ++
      [.localGet resultLocal, .ret] }

def internalizeClosureProjections (module : Module) : Except LinkError Module := do
  let operations := module.runtimeOperations.filter supportsClosureProjection
  operations.foldlM (init := module) fun result operation => do
    let some name := closureProjectionName? operation |
      throw (.unsupportedClosureProjection 0 .erased)
    let some (index, kind) := closureProjectionCoordinate? operation |
      throw (.unsupportedClosureProjection 0 .erased)
    let function ← closureProjectionFunction index kind
    internalizeOperation operation name function result

/-- The twelve distinct physical closure-capture reads reachable from `prettyM`. -/
def prettyFormatClosureProjectionCoordinates : Array (Nat × AbiKind) := #[
  (0, .object),
  (0, .tobject),
  (0, .uint8),
  (1, .object),
  (1, .tobject),
  (1, .uint8),
  (1, .uint32),
  (2, .object),
  (2, .tobject),
  (3, .object),
  (3, .tobject),
  (4, .object)]

def prettyFormatClosureProjectionModule : Except LinkError Module := do
  let functions ← prettyFormatClosureProjectionCoordinates.mapM fun coordinate =>
    closureProjectionFunction coordinate.1 coordinate.2
  return {
    imports := #[]
    functions
    exports := functions.map (·.name)
    initializers := #[]
    runtimeOperations := #[]
    memory := some residentMemory }

def closureMatchCoordinate? (dispatch : Array Name) : RuntimeOp →
    Option (Nat × Nat × Nat)
  | .closureMatches function arity fixed =>
      (dispatch.findIdx? (· == function)).map fun targetId =>
        (targetId, arity, fixed)
  | _ => none

def closureMatchName? (dispatch : Array Name) (operation : RuntimeOp) : Option Name :=
  (closureMatchCoordinate? dispatch operation).map fun coordinate =>
    Name.mkSimple s!"fir_cmatch_{coordinate.1}_{coordinate.2.1}_{coordinate.2.2}"

def isClosureMatch : RuntimeOp → Bool
  | .closureMatches .. => true
  | _ => false

private def checkedClosureWord (value : Nat) : Except LinkError UInt32 :=
  if value < UInt32.size then
    pure (UInt32.ofNat value)
  else
    throw (.closureMetadataOverflow value)

private def closureMatchFunction (dispatch : Array Name) (operation : RuntimeOp) :
    Except LinkError Function := do
  let some (targetId, arity, fixed) := closureMatchCoordinate? dispatch operation |
    match operation.closureTarget? with
    | some function => throw (.missingClosureTarget function)
    | none => throw .unsupportedClosureMatch
  let some name := closureMatchName? dispatch operation |
    throw .unsupportedClosureMatch
  let targetId ← checkedClosureWord targetId
  let arity ← checkedClosureWord arity
  let fixed ← checkedClosureWord fixed
  let compareMetadata :=
    [.localGet objectParam,
      .i32Load .uint32 (offset headerAux0Offset)] ++
    equalsConst .uint32 targetId ++
    [.localGet objectParam,
      .i32Load .uint32 (offset headerAux1Offset)] ++
    equalsConst .uint32 arity ++
    [.i32And,
      .localGet objectParam,
      .i32Load .uint32 (offset headerAux2Offset)] ++
    equalsConst .uint32 fixed ++
    [.i32And,
      .localSet resultLocal]
  return {
    name
    params := #[(objectParam, .tobject)]
    results := #[.uint32]
    locals := #[(resultLocal, .uint32)]
    body := closureHeapBody compareMetadata ++
      [.localGet resultLocal, .ret] }

/--
Internalize exact closure identity tests against the stable module dispatch
table. Each helper checks target ID, total arity, and fixed-capture count in
linear memory; recognized non-closure inputs trap.

The W6 related-state precondition remains responsible for target-table and
capture-descriptor validity. The separate proof theorem must establish that
these physical header comparisons implement semantic `closureMatches`.
-/
def internalizeClosureMatches (module : Module) : Except LinkError Module := do
  let operations := module.runtimeOperations.filter isClosureMatch
  operations.foldlM (init := module) fun result operation => do
    let some name := closureMatchName? result.closureDispatch operation |
      match operation.closureTarget? with
      | some function => throw (.missingClosureTarget function)
      | none => throw .unsupportedClosureMatch
    let function ← closureMatchFunction result.closureDispatch operation
    internalizeOperation operation name function result

def closureMatchExampleDispatch : Array Name := #[`callee, `other]

def closureMatchExampleOperations : Array RuntimeOp := #[
  .closureMatches `callee 2 1,
  .closureMatches `other 2 1,
  .closureMatches `callee 3 1,
  .closureMatches `callee 2 0]

def closureMatchExampleModule : Except LinkError Module := do
  let functions ← closureMatchExampleOperations.mapM
    (closureMatchFunction closureMatchExampleDispatch)
  return {
    imports := #[]
    functions
    exports := functions.map (·.name)
    initializers := #[]
    runtimeOperations := #[]
    closureDispatch := closureMatchExampleDispatch
    memory := some residentMemory }

def getTagManifest : Json :=
  Json.mkObj [
    ("entry", getTagName.toString),
    ("params", Json.arr #["tobject"]),
    ("result", "uint32"),
    ("memory", "memory"),
    ("imports", Json.arr #[]),
    ("status", "generation-only; W6 contract proof pending")]

def isSharedManifest : Json :=
  Json.mkObj [
    ("entry", isSharedName.toString),
    ("params", Json.arr #["tobject"]),
    ("result", "uint8"),
    ("memory", "memory"),
    ("imports", Json.arr #[]),
    ("status", "generation-only; W6 contract proof pending")]

private def readProjectionEntryJson (operation : RuntimeOp) : Json :=
  match operation with
  | .objectProj index result =>
      Json.mkObj [
        ("entry", (readProjectionName? operation).getD .anonymous |>.toString),
        ("kind", "objectProj"),
        ("index", index),
        ("result", (objectProjectionSuffix? result).getD "unsupported")]
  | .scalarProj width byteOffset .uint8 =>
      Json.mkObj [
        ("entry", (readProjectionName? operation).getD .anonymous |>.toString),
        ("kind", "scalarProj"),
        ("width", width),
        ("offset", byteOffset),
        ("result", "uint8")]
  | _ => Json.mkObj [("kind", "unsupported")]

def prettyFormatReadProjectionManifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <| prettyFormatReadProjections.map readProjectionEntryJson),
    ("memory", "memory"),
    ("imports", Json.arr #[]),
    ("status", "generation-only; W6 contract proofs pending")]

private def closureProjectionEntryJson (coordinate : Nat × AbiKind) : Json :=
  let operation : RuntimeOp :=
    .closureProj `resident (coordinate.1 + 2) (coordinate.1 + 1)
      coordinate.1 coordinate.2
  Json.mkObj [
    ("entry", (closureProjectionName? operation).getD .anonymous |>.toString),
    ("index", coordinate.1),
    ("result", (closureProjectionSuffix? coordinate.2).getD "unsupported")]

def prettyFormatClosureProjectionManifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <|
      prettyFormatClosureProjectionCoordinates.map closureProjectionEntryJson),
    ("memory", "memory"),
    ("imports", Json.arr #[]),
    ("status", "generation-only; W6 contract proofs pending")]

private def closureMatchEntryJson (dispatch : Array Name)
    (operation : RuntimeOp) : Json :=
  match operation with
  | .closureMatches function arity fixed =>
      Json.mkObj [
        ("entry", (closureMatchName? dispatch operation).getD .anonymous |>.toString),
        ("function", function.toString),
        ("targetId", (dispatch.findIdx? (· == function)).getD 0),
        ("arity", arity),
        ("fixed", fixed)]
  | _ => Json.mkObj [("kind", "unsupported")]

def closureMatchExampleManifest : Json :=
  Json.mkObj [
    ("entries", Json.arr <| closureMatchExampleOperations.map
      (closureMatchEntryJson closureMatchExampleDispatch)),
    ("closureDispatch", Json.arr <| closureMatchExampleDispatch.map fun name =>
      (name.toString : Json)),
    ("memory", "memory"),
    ("imports", Json.arr #[]),
    ("status", "generation-only; W6 contract proofs pending")]

#guard getTagModule.imports.isEmpty
#guard getTagModule.memory.any fun memory =>
  memory.pagesMin == 1 && memory.exportName == some "memory"
#guard Fir.Wasm.validateModule getTagModule |>.isOk
#guard Fir.Wasm.Emit.encode getTagModule |>.isOk
#guard isSharedModule.imports.isEmpty
#guard isSharedModule.memory.any fun memory =>
  memory.pagesMin == 1 && memory.exportName == some "memory"
#guard Fir.Wasm.validateModule isSharedModule |>.isOk
#guard Fir.Wasm.Emit.encode isSharedModule |>.isOk
#guard match prettyFormatReadProjectionModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.functions.size == prettyFormatReadProjections.size &&
      module.exports.size == prettyFormatReadProjections.size &&
      (module.memory.any fun memory =>
        memory.pagesMin == 1 && memory.exportName == some "memory") &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false
#guard match prettyFormatClosureProjectionModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.functions.size == prettyFormatClosureProjectionCoordinates.size &&
      module.exports.size == prettyFormatClosureProjectionCoordinates.size &&
      (module.memory.any fun memory =>
        memory.pagesMin == 1 && memory.exportName == some "memory") &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false
#guard match closureMatchExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.functions.size == closureMatchExampleOperations.size &&
      module.exports.size == closureMatchExampleOperations.size &&
      module.closureDispatch == closureMatchExampleDispatch &&
      (module.memory.any fun memory =>
        memory.pagesMin == 1 && memory.exportName == some "memory") &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentRuntime
