import LeanZipFir.Compile
import Lean.Elab.Command
import Lean.Compiler.LCNF.PrettyPrinter

open Lean Elab Command

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

private def functionSignatureJson (function : Fir.Wasm.Function) : Json :=
  Json.mkObj [
    ("name", function.name.toString),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson (function.params.map (·.2))),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson function.results)]

private def importNameArrayJson (imports : Array Fir.Wasm.Import) : Json :=
  Json.arr <| imports.filterMap fun import_ =>
    import_.declaration?.map fun name => (name.toString : Json)

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
  IO.FS.writeFile "_build/raw-unsupported.lcnf"
    (String.intercalate "\n" unsupportedText.toList)
  unless unsupported.isEmpty do
    throwError "raw capture retained unsupported declarations: {unsupported.map (·.name)}; see _build/raw-unsupported.lcnf"
  let baseResult ← liftCoreM <| LeanZipFir.Compile.compileRawCaptured source
  let loweredAt ← IO.monoMsNow
  let base ← match baseResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile raw source: {repr error}"
  let linkedResult := LeanZipFir.Compile.linkRawArtifact base
  let linked ← match linkedResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link raw runtime: {repr error}"
  let linkedAt ← IO.monoMsNow
  match ← base.write "_build/lean-zip-raw-base.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write raw base module: {repr error}"
  match ← linked.write "_build/lean-zip-raw-frontier.wasm" with
  | .error error => throwError "failed to write resident raw frontier: {repr error}"
  | .ok () =>
      let expectedMathImports : Array Name :=
        #[`Float.log2]
      let frontierImports := linked.module.imports.filterMap (·.declaration?)
      unless frontierImports == expectedMathImports do
        throwError "raw frontier imports changed: expected {expectedMathImports}, got {frontierImports}"
      unless linked.module.runtimeOperations.isEmpty do
        throwError "raw frontier retained runtime operations"
      let functionNames := linked.module.functions.map (·.name)
      let sourceFunctionNames := linked.source.program.decls.filterMap fun decl =>
        match decl.value with
        | .code _ => some decl.name
        | .extern _ => none
      let retainedSourceFunctions := sourceFunctionNames.filter functionNames.contains
      let residentHelpers := functionNames.filter fun name =>
        !retainedSourceFunctions.contains name
      let sourceClosureTargets :=
        Fir.Wasm.Emit.ClosureDispatch.partialApplicationTargets
          linked.source.program
      let inventory := Json.mkObj [
        ("entry", LeanZipFir.Compile.rawEntry.toString),
        ("capturedDeclarations", source.program.decls.size),
        ("reviewedExternalsBeforeLink", source.externalNames.size),
        ("externals", nameArrayJson source.externalNames),
        ("unsupportedDeclarations", nameArrayJson (unsupported.map (·.name))),
        ("functions", nameArrayJson functionNames),
        ("publicFunctions", nameArrayJson linked.module.exports),
        ("publicSignatures", Json.arr <| linked.module.functions.filterMap fun function =>
          if linked.module.exports.contains function.name then
            some (functionSignatureJson function)
          else none),
        ("sourceFunctions", nameArrayJson retainedSourceFunctions),
        ("sourceClosureTargets", nameArrayJson sourceClosureTargets),
        ("residentHelpers", nameArrayJson residentHelpers),
        ("residentGlobals", linked.module.globals.size),
        ("frontierImports", importNameArrayJson linked.module.imports),
        ("runtimeOperations", linked.module.runtimeOperations.size),
        ("captureMs", capturedAt - startedAt),
        ("lowerMs", loweredAt - capturedAt),
        ("linkMs", linkedAt - loweredAt)]
      IO.FS.writeFile "_build/lean-zip-raw.inventory.json"
        (inventory.pretty ++ "\n")
      IO.FS.writeFile "_build/raw-probe.json" (inventory.pretty ++ "\n")
      logInfo m!"wrote {linked.bytes.size} raw frontier bytes with {frontierImports.size} math imports, {retainedSourceFunctions.size} source functions, and {residentHelpers.size} resident helpers from one capture/lower pass (capture {capturedAt - startedAt}ms, lower {loweredAt - capturedAt}ms, link {linkedAt - loweredAt}ms)"
