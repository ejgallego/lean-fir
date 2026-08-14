import LeanZipFir.CaptureCache
import Fir.Wasm.Emit.ResidentLinker

open Lean

private def entry : Name := `Zip.Wasm.compressLevel1

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

private def functionSignatureJson (function : Fir.Wasm.Function) : Json :=
  Json.mkObj [
    ("name", function.name.toString),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson (function.params.map (·.2))),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson function.results)]

private structure Compilation where
  base : Fir.Wasm.Emit.Source.ModuleArtifact
  linked : Fir.Wasm.Emit.Source.ModuleArtifact
  loadEndMs : Nat
  captureEndMs : Nat
  lowerEndMs : Nat
  linkEndMs : Nat

private unsafe def compileArtifact (started : Nat) : IO Compilation := do
  /-
  The package driver invokes this executable from `integration/lean-zip`.
  Supplying the two local build roots removes `lake env` startup from the hot
  path while retaining Lean's toolchain library as the final search entry.
  -/
  Lean.initSearchPath (← Lean.findSysroot) [
    ".lake/build/lib/lean",
    "../../.lake/build/lib/lean"]
  Lean.enableInitializersExecution
  let options := maxHeartbeats.set ({} : Options) 0
  let env ← Lean.importModules #[{ module := `LeanZipFir.CapturedLevel1 }] options
    (leakEnv := true) (loadExts := false)
  let loaded ← IO.monoMsNow
  let ((source, baseResult, linkedResult, capturedAt, loweredAt, linkedAt), _) ←
      Lean.Core.CoreM.toIO
      (ctx := { fileName := "Level1ArtifactMain.lean", fileMap := default, options })
      (s := { env }) do
    let some source ← LeanZipFir.CaptureCache.getModule?
        `LeanZipFir.CapturedLevel1 `leanZipLevel1
      | throwError "cached Level-1 capture is unavailable"
    let capturedAt ← IO.monoMsNow
    let baseResult ← Fir.Wasm.Emit.Source.compileModuleArtifact source
    let loweredAt ← IO.monoMsNow
    let linkedResult := baseResult.bind fun artifact =>
      Fir.Wasm.Emit.ResidentLinker.linkArtifact
        (Fir.Wasm.Emit.ResidentLinker.closedApplicationAvailablePolicy
          artifact.module #[entry])
        artifact
    let linkedAt ← IO.monoMsNow
    return (source, baseResult, linkedResult, capturedAt, loweredAt, linkedAt)
  let base ← IO.ofExcept <| baseResult.mapError fun error => s!"{repr error}"
  let linked ← IO.ofExcept <| linkedResult.mapError fun error => s!"{repr error}"
  unless source.program.decls.size == linked.source.program.decls.size do
    throw <| IO.userError "cached source changed while linking"
  return {
    base
    linked
    loadEndMs := loaded - started
    captureEndMs := capturedAt - started
    lowerEndMs := loweredAt - started
    linkEndMs := linkedAt - started }

private def writeCompilation (compilation : Compilation) : IO Unit := do
  IO.FS.createDirAll "_build"
  IO.ofExcept <| (← compilation.base.write
    "_build/lean-zip-level1-base.wasm").mapError fun error => s!"{repr error}"
  IO.ofExcept <| (← compilation.linked.write
    "_build/lean-zip-level1.wasm").mapError fun error => s!"{repr error}"
  let linked := compilation.linked
  unless linked.module.imports.isEmpty do
    throw <| IO.userError "Level-1 module retained function imports"
  unless linked.module.runtimeOperations.isEmpty do
    throw <| IO.userError "Level-1 module retained runtime operations"
  let functionNames := linked.module.functions.map (·.name)
  let sourceFunctionNames := linked.source.program.decls.filterMap fun decl =>
    match decl.value with
    | .code _ => some decl.name
    | .extern _ => none
  let retainedSourceFunctions := sourceFunctionNames.filter functionNames.contains
  let residentHelpers := functionNames.filter fun name =>
    !retainedSourceFunctions.contains name
  let inventory := Json.mkObj [
    ("entry", entry.toString),
    ("capturedDeclarations", linked.source.program.decls.size),
    ("reviewedExternalsBeforeLink", linked.source.externalNames.size),
    ("externals", nameArrayJson linked.source.externalNames),
    ("functions", nameArrayJson functionNames),
    ("publicFunctions", nameArrayJson linked.module.exports),
    ("publicSignatures", Json.arr <| linked.module.functions.filterMap fun function =>
      if linked.module.exports.contains function.name then
        some (functionSignatureJson function)
      else none),
    ("sourceFunctions", nameArrayJson retainedSourceFunctions),
    ("residentHelpers", nameArrayJson residentHelpers),
    ("residentGlobals", linked.module.globals.size),
    ("runtimeOperations", linked.module.runtimeOperations.size)]
  IO.FS.writeFile "_build/lean-zip-level1.inventory.json"
    (inventory.pretty ++ "\n")

unsafe def main (_ : List String) : IO UInt32 := do
  try
    let started ← IO.monoMsNow
    let compilation ← compileArtifact started
    writeCompilation compilation
    let finished ← IO.monoMsNow
    let total := finished - started
    IO.println s!"Level-1 compilation timeline (ms): [0,{compilation.loadEndMs}] frontend/load; [{compilation.loadEndMs},{compilation.captureEndMs}] cached capture; [{compilation.captureEndMs},{compilation.lowerEndMs}] lower/base encode; [{compilation.lowerEndMs},{compilation.linkEndMs}] resident link/final encode; [{compilation.linkEndMs},{total}] write; total={total}"
    IO.println s!"wrote {compilation.linked.bytes.size} Level-1 bytes"
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
