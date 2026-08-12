import LeanZipFir.Compile
import Lean.Elab.Command
import Lean.Compiler.LCNF.PrettyPrinter

open Lean Elab Command

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

private def runtimeOperationArrayJson (operations : Array Fir.Wasm.RuntimeOp) : Json :=
  Json.arr <| operations.map fun operation =>
    match Fir.Wasm.Emit.Manifest.operationJson operation with
    | .ok json => json
    | .error error => Json.mkObj [("manifestError", error)]

private def externalImportNames (imports : Array Fir.Wasm.Import) : Array Name :=
  imports.filterMap (fun import_ => import_.declaration?)

set_option maxHeartbeats 0 in
run_cmd do
  IO.FS.createDirAll "_build"
  let startedAt ← IO.monoMsNow
  let source ← liftCoreM LeanZipFir.Compile.captureLevel1
  let capturedAt ← IO.monoMsNow
  let unsupported := source.program.decls.filter fun declaration =>
    !Fir.Wasm.supportedDecl source.program declaration
  let unsupportedText ← unsupported.mapM fun declaration => do
    let formatted ← liftCoreM <|
      Lean.Compiler.LCNF.ppDecl' declaration .impure
    pure s!"{formatted.pretty}\n"
  let result ← liftCoreM <| Fir.Wasm.Emit.Source.compileModuleArtifact source
  let loweredAt ← IO.monoMsNow
  let (baseFunctions, runtimeOperations, loweringError) := match result with
    | .ok artifact =>
        (artifact.module.functions.size, artifact.module.runtimeOperations,
          Json.null)
    | .error error =>
        (0, #[], (toString (repr error) : Json))
  let linkedResult := result.bind <|
    Fir.Wasm.Emit.ResidentLinker.prepareArenaAndLinkArtifact fun module => {
        steps :=
          Fir.Wasm.Emit.ResidentLinker.availableCommonSteps module ++
          Fir.Wasm.Emit.ResidentLinker.closedApplicationFamilySteps
        requireZeroImports := false
        requireNoRuntimeOperations := false }
  let (linkedFunctions, remainingImports, remainingRuntimeOperations,
      linkingError) := match linkedResult with
    | .ok artifact =>
        ((artifact.module.functions.size : Json),
          externalImportNames artifact.module.imports,
          artifact.module.runtimeOperations, Json.null)
    | .error error =>
        (Json.null, #[], #[], (toString (repr error) : Json))
  let linkedAt ← IO.monoMsNow
  let inventory := Json.mkObj [
    ("entry", LeanZipFir.Compile.level1Entry.toString),
    ("capturedDeclarations", source.program.decls.size),
    ("declarations", nameArrayJson (source.program.decls.map (·.name))),
    ("reviewedExternalsBeforeLink", source.externalNames.size),
    ("externals", nameArrayJson source.externalNames),
    ("unsupportedDeclarations", nameArrayJson (unsupported.map (·.name))),
    ("baseFunctions", baseFunctions),
    ("runtimeOperations", runtimeOperations.size),
    ("runtimeOperationNames", runtimeOperationArrayJson runtimeOperations),
    ("loweringError", loweringError),
    ("linkedFunctions", linkedFunctions),
    ("remainingImports", nameArrayJson remainingImports),
    ("remainingRuntimeOperations", remainingRuntimeOperations.size),
    ("remainingRuntimeOperationNames",
      runtimeOperationArrayJson remainingRuntimeOperations),
    ("linkingError", linkingError),
    ("captureMs", capturedAt - startedAt),
    ("lowerMs", loweredAt - capturedAt),
    ("linkMs", linkedAt - loweredAt)]
  IO.FS.writeFile "_build/level1-probe.json" (inventory.pretty ++ "\n")
  IO.FS.writeFile "_build/level1-unsupported.lcnf"
    (String.intercalate "\n" unsupportedText.toList)
  match linkedResult with
  | .ok _ =>
      logInfo m!"captured {source.program.decls.size} Level-1 declarations with {source.externalNames.size} externals and {unsupported.size} unsupported declarations; linked to {remainingImports.size} imports and {remainingRuntimeOperations.size} runtime operations (capture {capturedAt - startedAt}ms, lower {loweredAt - capturedAt}ms, link {linkedAt - loweredAt}ms)"
  | .error error =>
      logInfo m!"captured {source.program.decls.size} Level-1 declarations with {source.externalNames.size} externals and {unsupported.size} unsupported declarations; resident linking stopped at {repr error} (capture {capturedAt - startedAt}ms, lower {loweredAt - capturedAt}ms, link {linkedAt - loweredAt}ms)"
