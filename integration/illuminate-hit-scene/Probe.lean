import IlluminateFirHitScene.Compile
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

private def partialApplicationDiagnosticNames : Array Name := #[
  `Illuminate.endpointToCenter._closed_1._boxed_const_1,
  `Illuminate.endpointToCenter._closed_1,
  `Illuminate.endpointToCenter._lam_0._boxed]

run_cmd do
  IO.FS.createDirAll "_build"
  let startedAt ← IO.monoMsNow
  let source ← liftCoreM IlluminateFirHitScene.Compile.captureSource
  let capturedAt ← IO.monoMsNow
  let unsupported := source.program.decls.filter fun declaration =>
    !Fir.Wasm.supportedDecl source.program declaration
  let unsupportedText ← unsupported.mapM fun declaration => do
    let formatted ← liftCoreM <|
      Lean.Compiler.LCNF.ppDecl' declaration .impure
    pure s!"{formatted.pretty}\n"
  let capturedText ← source.program.decls.mapM fun declaration => do
    let formatted ← liftCoreM <|
      Lean.Compiler.LCNF.ppDecl' declaration .impure
    pure s!"{formatted.pretty}\n"
  let partialApplicationDiagnostics ← source.program.decls.filterMapM fun declaration => do
    if partialApplicationDiagnosticNames.contains declaration.name then
      let formatted ← liftCoreM <|
        Lean.Compiler.LCNF.ppDecl' declaration .impure
      return some s!"{formatted.pretty}\n"
    return none
  let rawLoweringError := match Fir.Wasm.lower source.program with
    | .ok _ => Json.null
    | .error error => (toString (repr error) : Json)
  let result ← liftCoreM <|
    Fir.Wasm.Emit.Source.compileModuleArtifact source
  let loweredAt ← IO.monoMsNow
  let (baseFunctions, runtimeOperations, loweringError) := match result with
    | .ok artifact =>
        (artifact.module.functions.size, artifact.module.runtimeOperations, Json.null)
    | .error error =>
        (0, #[], (toString (repr error) : Json))
  let inventory := Json.mkObj [
    ("entry", IlluminateFirHitScene.Compile.entry.toString),
    ("capturedDeclarations", source.program.decls.size),
    ("declarations", nameArrayJson (source.program.decls.map (·.name))),
    ("reviewedExternalsBeforeLink", source.externalNames.size),
    ("externals", nameArrayJson source.externalNames),
    ("unsupportedDeclarations", nameArrayJson (unsupported.map (·.name))),
    ("baseFunctions", baseFunctions),
    ("runtimeOperations", runtimeOperations.size),
    ("runtimeOperationNames", runtimeOperationArrayJson runtimeOperations),
    ("rawLoweringError", rawLoweringError),
    ("loweringError", loweringError)]
  IO.FS.writeFile "_build/hit-scene-probe.json" (inventory.pretty ++ "\n")
  IO.FS.writeFile "_build/hit-scene-unsupported.lcnf"
    (String.intercalate "\n" unsupportedText.toList)
  IO.FS.writeFile "_build/hit-scene-captured.lcnf"
    (String.intercalate "\n" capturedText.toList)
  IO.FS.writeFile "_build/hit-scene-partial-application.lcnf"
    (String.intercalate "\n" partialApplicationDiagnostics.toList)
  logInfo m!"captured {source.program.decls.size} HitScene declarations with {source.externalNames.size} externals and {unsupported.size} unsupported declarations (capture {capturedAt - startedAt}ms, lower {loweredAt - capturedAt}ms)"
