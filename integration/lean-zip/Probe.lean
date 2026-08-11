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

private def unsupportedDeclarationJson (program : Fir.LeanIR.ImpureProgram)
    (declaration : Lean.Compiler.LCNF.Decl .impure) : Json :=
  let parameterLocals := Fir.Wasm.addSupportedDeclarationParams? program declaration
  let codeSupported := match parameterLocals, declaration.value with
    | some locals, .code code =>
        Fir.Wasm.supportedCode program locals
          (Fir.Wasm.effectiveDeclarationResultKind? declaration) code
    | _, _ => false
  let reuseSafe := match declaration.value with
    | .code code => Fir.Wasm.reuseCapacitySafeCode [] code
    | .extern _ => true
  Json.mkObj [
    ("name", declaration.name.toString),
    ("parameterIdsUnique", Fir.Wasm.declarationParameterIdsUnique declaration),
    ("declarationAbiKnown", Fir.Wasm.abiTypeKnown declaration.type),
    ("parameterKindsKnown", parameterLocals.isSome),
    ("effectiveResultKind", reprStr (Fir.Wasm.effectiveDeclarationResultKind? declaration)),
    ("codeSupported", codeSupported),
    ("reuseCapacitySafe", reuseSafe)]

run_cmd do
  IO.FS.createDirAll "_build"
  let startedAt ← IO.monoMsNow
  let source ← liftCoreM LeanZipFir.Compile.captureStored
  let capturedAt ← IO.monoMsNow
  let unsupported := source.program.decls.filter fun declaration =>
    !Fir.Wasm.supportedDecl source.program declaration
  let unsupportedText ← unsupported.mapM fun declaration => do
    let formatted ← liftCoreM <|
      Lean.Compiler.LCNF.ppDecl' declaration .impure
    pure s!"{formatted.pretty}\n"
  let declarationText ← source.program.decls.mapM fun declaration => do
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
  let linked ← liftCoreM LeanZipFir.Compile.compileStored
  let linkedAt ← IO.monoMsNow
  let (linkedFunctions, linkedImports, linkedOperations, linkedBytes,
      linkingError) := match linked with
    | .ok artifact =>
        (artifact.module.functions.size, artifact.module.imports.size,
          artifact.module.runtimeOperations.size, artifact.bytes.size, Json.null)
    | .error error =>
        (0, 0, 0, 0, (toString (repr error) : Json))
  let inventory := Json.mkObj [
    ("entry", LeanZipFir.Compile.storedEntry.toString),
    ("capturedDeclarations", source.program.decls.size),
    ("declarations", nameArrayJson (source.program.decls.map (·.name))),
    ("reviewedExternalsBeforeLink", source.externalNames.size),
    ("externals", nameArrayJson source.externalNames),
    ("unsupportedDeclarations", nameArrayJson (unsupported.map (·.name))),
    ("unsupportedDiagnostics", Json.arr <| unsupported.map
      (unsupportedDeclarationJson source.program)),
    ("baseFunctions", baseFunctions),
    ("runtimeOperations", runtimeOperations.size),
    ("runtimeOperationNames", runtimeOperationArrayJson runtimeOperations),
    ("loweringError", loweringError),
    ("linkedFunctions", linkedFunctions),
    ("linkedImports", linkedImports),
    ("linkedRuntimeOperations", linkedOperations),
    ("linkedBytes", linkedBytes),
    ("linkingError", linkingError)]
  IO.FS.writeFile "_build/stored-probe.json" (inventory.pretty ++ "\n")
  IO.FS.writeFile "_build/stored-unsupported.lcnf"
    (String.intercalate "\n" unsupportedText.toList)
  IO.FS.writeFile "_build/stored.lcnf"
    (String.intercalate "\n" declarationText.toList)
  logInfo m!"captured {source.program.decls.size} stored-block declarations with {source.externalNames.size} externals and {unsupported.size} unsupported declarations (capture {capturedAt - startedAt}ms, lower {loweredAt - capturedAt}ms, link {linkedAt - loweredAt}ms)"
