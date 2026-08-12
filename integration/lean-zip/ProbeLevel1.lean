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
    ("captureMs", capturedAt - startedAt),
    ("lowerMs", loweredAt - capturedAt)]
  IO.FS.writeFile "_build/level1-probe.json" (inventory.pretty ++ "\n")
  IO.FS.writeFile "_build/level1-unsupported.lcnf"
    (String.intercalate "\n" unsupportedText.toList)
  logInfo m!"captured {source.program.decls.size} Level-1 declarations with {source.externalNames.size} externals and {unsupported.size} unsupported declarations (capture {capturedAt - startedAt}ms, lower {loweredAt - capturedAt}ms)"
