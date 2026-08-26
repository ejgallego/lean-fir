import Fir.Wasm.Emit.ResidentLinker
import Fir.Wasm.Emit.Source
import Lean.Elab.Command

namespace Fir.Wasm.Emit.ScalarBoxingExamples

open Lean Elab Command
open Lean.Compiler
open Fir.Wasm
open Fir.Wasm.Emit.Source

/-!
This source-generated fixture covers every scalar family recognized by final
LCNF `box` and `unbox`. It exercises both generic polymorphic boxing and the
exact `_boxed` wrapper synthesized by Lean's own ExplicitBoxing pass.

`generationReady := false` is not an admission fence: the fixture still
compiles the real Lean source and requires the resident linker to leave
exactly its box/unbox pair. Flipping the flag to `true` tightens that family to
zero imports and zero residual runtime operations.
-/

@[noinline]
def polyId (α : Type) (value : α) : α := value

def uint8Entry (value : UInt8) : UInt8 := polyId UInt8 value
def uint16Entry (value : UInt16) : UInt16 := polyId UInt16 value
def uint32Entry (value : UInt32) : UInt32 := polyId UInt32 value
def uint64Entry (value : UInt64) : UInt64 := polyId UInt64 value
def usizeEntry (value : USize) : USize := polyId USize value
def float32Entry (value : Float32) : Float32 := polyId Float32 value
def floatEntry (value : Float) : Float := polyId Float value

@[noinline] def rawUInt8 (value : UInt8) : UInt8 := value
@[noinline] def rawUInt16 (value : UInt16) : UInt16 := value
@[noinline] def rawUInt32 (value : UInt32) : UInt32 := value
@[noinline] def rawUInt64 (value : UInt64) : UInt64 := value
@[noinline] def rawUSize (value : USize) : USize := value
@[noinline] def rawFloat32 (value : Float32) : Float32 := value
@[noinline] def rawFloat (value : Float) : Float := value

@[noinline]
def applyFn (f : α → α) (value : α) : α := f value

def uint8ClosureEntry (value : UInt8) : UInt8 := applyFn rawUInt8 value
def uint16ClosureEntry (value : UInt16) : UInt16 := applyFn rawUInt16 value
def uint32ClosureEntry (value : UInt32) : UInt32 := applyFn rawUInt32 value
def uint64ClosureEntry (value : UInt64) : UInt64 := applyFn rawUInt64 value
def usizeClosureEntry (value : USize) : USize := applyFn rawUSize value
def float32ClosureEntry (value : Float32) : Float32 := applyFn rawFloat32 value
def floatClosureEntry (value : Float) : Float := applyFn rawFloat value

structure ScalarFamily where
  label : String
  type : Lean.Expr
  scalar : AbiKind
  genericEntry : Name
  rawEntry : Name
  closureEntry : Name
  generationReady : Bool

def families : Array ScalarFamily := #[
  { label := "UInt8", type := LCNF.ImpureType.uint8, scalar := .uint8
    genericEntry := ``uint8Entry, rawEntry := ``rawUInt8
    closureEntry := ``uint8ClosureEntry, generationReady := true },
  { label := "UInt16", type := LCNF.ImpureType.uint16, scalar := .uint16
    genericEntry := ``uint16Entry, rawEntry := ``rawUInt16
    closureEntry := ``uint16ClosureEntry, generationReady := true },
  { label := "UInt32", type := LCNF.ImpureType.uint32, scalar := .uint32
    genericEntry := ``uint32Entry, rawEntry := ``rawUInt32
    closureEntry := ``uint32ClosureEntry, generationReady := true },
  { label := "UInt64", type := LCNF.ImpureType.uint64, scalar := .uint64
    genericEntry := ``uint64Entry, rawEntry := ``rawUInt64
    closureEntry := ``uint64ClosureEntry, generationReady := true },
  { label := "USize", type := LCNF.ImpureType.usize, scalar := .usize
    genericEntry := ``usizeEntry, rawEntry := ``rawUSize
    closureEntry := ``usizeClosureEntry, generationReady := false },
  { label := "Float32", type := LCNF.ImpureType.float32, scalar := .float32
    genericEntry := ``float32Entry, rawEntry := ``rawFloat32
    closureEntry := ``float32ClosureEntry, generationReady := false },
  { label := "Float", type := LCNF.ImpureType.float, scalar := .float
    genericEntry := ``floatEntry, rawEntry := ``rawFloat
    closureEntry := ``floatClosureEntry, generationReady := true }]

#guard families.size == 7
#guard (families.filter (!·.generationReady)).map (·.label) ==
  #["USize", "Float32"]

private def operationText (operations : Array RuntimeOp) : String :=
  (Json.arr <| operations.map fun operation =>
    match Manifest.operationJson operation with
    | .ok json => json
    | .error error => Json.mkObj [("error", error)]).compress

private def scalarOperations (scalar : AbiKind)
    (operations : Array RuntimeOp) : Array RuntimeOp :=
  operations.filter fun
    | .box source _ => source == scalar
    | .unbox source => source == scalar
    | _ => false

private def checkLinkedFrontier (family : ScalarFamily) (entry : Name)
    (boxResult : AbiKind) (artifact : ModuleArtifact) : CommandElabM Unit := do
  let policy := {
    ResidentLinker.closedApplicationAvailablePolicy artifact.module #[entry] with
    requireZeroImports := false
    requireNoRuntimeOperations := false }
  let linked ← match ResidentLinker.linkArtifact policy artifact with
    | .ok linked => pure linked
    | .error error =>
        throwError "{family.label} resident link failed before its frontier could be checked: {repr error}"
  let residual := scalarOperations family.scalar linked.module.runtimeOperations
  if family.generationReady then
    unless linked.module.imports.isEmpty do
      throwError "{family.label} retained {linked.module.imports.size} import(s) after resident linking"
    unless linked.module.runtimeOperations.isEmpty do
      throwError "{family.label} retained runtime operations after resident linking: {operationText linked.module.runtimeOperations}"
  else
    unless residual.size == 2 &&
        residual.contains (.box family.scalar boxResult) &&
        residual.contains (.unbox family.scalar) &&
        residual.size == linked.module.runtimeOperations.size do
      throwError "{family.label} unresolved frontier changed: {operationText linked.module.runtimeOperations}"

run_cmd do
  for family in families do
    let some exactResult := upstreamBoxResultKind? family.type
      | throwError "upstream has no exact boxed result kind for {family.label}"
    let genericResult := boxResultKind family.type .tobject

    let genericArtifact ← match ← liftCoreM <|
        compileModule family.genericEntry #[``polyId] with
      | .ok artifact => pure artifact
      | .error error =>
          throwError "{family.label} generic source fixture did not compile: {repr error}"
    let genericOperations :=
      scalarOperations family.scalar genericArtifact.module.runtimeOperations
    unless genericOperations.contains (.box family.scalar genericResult) &&
        genericOperations.contains (.unbox family.scalar) do
      throwError "{family.label} generic box/unbox inventory changed: {operationText genericOperations}"
    checkLinkedFrontier family family.genericEntry genericResult genericArtifact

    let closureArtifact ← match ← liftCoreM <|
        compileModule family.closureEntry #[family.rawEntry, ``applyFn] with
      | .ok artifact => pure artifact
      | .error error =>
          throwError "{family.label} closure source fixture did not compile: {repr error}"
    let wrapperName := family.rawEntry.str "_boxed"
    let some wrapper := closureArtifact.module.functions.find? (·.name == wrapperName)
      | throwError "{family.label} lost compiler-generated wrapper {wrapperName}"
    let wrapperOperations := collectRuntimeOps #[wrapper]
    unless wrapper.results == #[exactResult] &&
        wrapperOperations.contains (.box family.scalar exactResult) &&
        wrapperOperations.contains (.unbox family.scalar) do
      throwError "{family.label} exact wrapper changed: operations={operationText wrapperOperations}"
    checkLinkedFrontier family family.closureEntry exactResult closureArtifact

end Fir.Wasm.Emit.ScalarBoxingExamples
