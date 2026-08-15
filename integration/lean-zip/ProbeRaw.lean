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
  let source ← liftCoreM LeanZipFir.Compile.captureRaw
  let capturedAt ← IO.monoMsNow
  let environment ← liftCoreM getEnv
  let localizedExterns := source.program.decls.filter fun declaration =>
    isExtern environment declaration.name &&
      !source.externalNames.contains declaration.name
  unless localizedExterns.isEmpty do
    throwError "raw capture localized native extern fallbacks: {localizedExterns.map (·.name)}"
  let externalSpecializations := source.externalNames.filter fun name =>
    !(Fir.Wasm.Emit.CompilerPrivate.specializationCallerCandidates name).isEmpty
  unless externalSpecializations.isEmpty do
    throwError "raw capture retained generated specializations: {externalSpecializations}"
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
  let linkedResult := result.bind fun artifact =>
    Fir.Wasm.Emit.ResidentLinker.linkArtifact
      { Fir.Wasm.Emit.ResidentLinker.closedApplicationAvailablePolicy
          artifact.module #[LeanZipFir.Compile.rawEntry] with
        allowedExternalImports :=
          some Fir.Wasm.Emit.ExternalRuntime.mathDeclarations
        requireZeroImports := false
        requireNoRuntimeOperations := true }
      artifact
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
    ("entry", LeanZipFir.Compile.rawEntry.toString),
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
  IO.FS.writeFile "_build/raw-probe.json" (inventory.pretty ++ "\n")
  IO.FS.writeFile "_build/raw-unsupported.lcnf"
    (String.intercalate "\n" unsupportedText.toList)
  match linkedResult with
  | .ok _ =>
      let expectedMathImports : Array Name :=
        #[`Float.log2]
      unless remainingImports == expectedMathImports do
        throwError "raw frontier imports changed: expected {expectedMathImports}, got {remainingImports}"
      unless remainingRuntimeOperations.isEmpty do
        throwError "raw frontier retained {remainingRuntimeOperations.size} runtime operations; see _build/raw-probe.json"
      logInfo m!"captured {source.program.decls.size} raw declarations with {source.externalNames.size} externals and {unsupported.size} unsupported declarations; linked to {remainingImports.size} imports and {remainingRuntimeOperations.size} runtime operations (capture {capturedAt - startedAt}ms, lower {loweredAt - capturedAt}ms, link {linkedAt - loweredAt}ms)"
  | .error error =>
      throwError "raw zero-frontier ratchet failed after capturing {source.program.decls.size} declarations with {source.externalNames.size} externals and {unsupported.size} unsupported declarations: {repr error} (capture {capturedAt - startedAt}ms, lower {loweredAt - capturedAt}ms, link {linkedAt - loweredAt}ms)"
