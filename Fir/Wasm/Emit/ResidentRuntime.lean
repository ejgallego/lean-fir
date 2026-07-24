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

def objectParam : FVarId := ⟨`object⟩

def resultLocal : FVarId := ⟨`result⟩

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

def getTagModule : Module := {
  imports := #[]
  functions := #[getTagFunction]
  exports := #[getTagName]
  initializers := #[]
  runtimeOperations := #[]
  memory := some { pagesMin := 1, exportName := some "memory" } }

def residentMemory : MemoryDecl := {
  pagesMin := 1
  exportName := some "memory" }

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingGetTag
  | reservedDeclaration (name : Name)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private partial def rewriteGetTagInstruction : Instruction → Instruction
  | .call (.runtime .getTag) => .call (.declaration getTagName)
  | .block label body => .block label (body.map rewriteGetTagInstruction)
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map rewriteGetTagInstruction)
        (elseBody.map rewriteGetTagInstruction)
  | instruction => instruction

private def rewriteGetTagFunction (function : Function) : Function :=
  { function with body := function.body.map rewriteGetTagInstruction }

/--
Internalize the semantic `getTag` import in an already validated symbolic
module. Runtime imports are rebuilt from the rewritten function bodies because
their presentation names contain ordinals; external declaration imports retain
their original stable names and order.
-/
def internalizeGetTag (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.runtimeOperations.contains .getTag do
    throw .missingGetTag
  if module.imports.any (·.declaration? == some getTagName) then
    throw (.reservedDeclaration getTagName)
  let memory ←
    match module.memory with
    | none => pure residentMemory
    | some memory =>
        unless memory == residentMemory do
          throw .incompatibleMemory
        pure memory
  let functions := module.functions.map rewriteGetTagFunction
  let functions ←
    match functions.find? (·.name == getTagName) with
    | none => pure (functions.push getTagFunction)
    | some function =>
        unless function == getTagFunction do
          throw (.reservedDeclaration getTagName)
        pure functions
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
  let result : Module := {
    module with
    imports
    functions
    exports := Fir.Wasm.addUnique module.exports getTagName
    runtimeOperations
    memory := some memory }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

def getTagManifest : Json :=
  Json.mkObj [
    ("entry", getTagName.toString),
    ("params", Json.arr #["tobject"]),
    ("result", "uint32"),
    ("memory", "memory"),
    ("imports", Json.arr #[]),
    ("status", "generation-only; W6 contract proof pending")]

#guard getTagModule.imports.isEmpty
#guard getTagModule.memory.any fun memory =>
  memory.pagesMin == 1 && memory.exportName == some "memory"
#guard Fir.Wasm.validateModule getTagModule |>.isOk
#guard Fir.Wasm.Emit.encode getTagModule |>.isOk

end Fir.Wasm.Emit.ResidentRuntime
