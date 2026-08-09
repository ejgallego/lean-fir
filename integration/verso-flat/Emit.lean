import VersoFirFlat.Compile
import Lean.Elab.Command

open Lean Elab Command

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

private def functionSignatureJson (function : Fir.Wasm.Function) : Json :=
  Json.mkObj [
    ("name", function.name.toString),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson (function.params.map (·.2))),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson function.results)]

run_cmd do
  IO.FS.createDirAll "_build"
  let baseResult ← liftCoreM VersoFirFlat.Compile.compileBaseModule
  let base ← match baseResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile Verso Flat source: {repr error}"
  match ← base.write "_build/prettyM-flat-base.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write base Flat module: {repr error}"
  let artifact ← match VersoFirFlat.Compile.linkResidentRuntime base with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link Flat resident runtime: {repr error}"
  match ← artifact.write "_build/prettyM-flat-resident.wasm" with
  | .error error => throwError "failed to write resident Flat module: {repr error}"
  | .ok () =>
      unless artifact.module.runtimeOperations.isEmpty do
        throwError "Flat module retained unresolved runtime operations"
      let functionNames := artifact.module.functions.map (·.name)
      let sourceFunctionNames := artifact.source.program.decls.filterMap fun decl =>
        match decl.value with
        | .code _ => some decl.name
        | .extern _ => none
      let retainedSourceFunctions := sourceFunctionNames.filter functionNames.contains
      let residentHelpers := functionNames.filter fun name =>
        !retainedSourceFunctions.contains name
      let inventory := Json.mkObj [
        ("capturedDeclarations", artifact.source.program.decls.size),
        ("reviewedExternalsBeforeLink", artifact.source.externalNames.size),
        ("functions", nameArrayJson functionNames),
        ("publicFunctions", nameArrayJson artifact.module.exports),
        ("publicSignatures", Json.arr <| artifact.module.functions.filterMap fun function =>
          if artifact.module.exports.contains function.name then
            some (functionSignatureJson function)
          else none),
        ("sourceFunctions", nameArrayJson retainedSourceFunctions),
        ("residentHelpers", nameArrayJson residentHelpers),
        ("lazyCacheInitializerNames", nameArrayJson artifact.module.initializers),
        ("lazyCacheInitializers", artifact.module.initializers.size),
        ("residentGlobals", artifact.module.globals.size),
        ("runtimeOperations", artifact.module.runtimeOperations.size)]
      IO.FS.writeFile "_build/prettyM-flat-resident.inventory.json"
        (inventory.pretty ++ "\n")
      logInfo m!"wrote {artifact.bytes.size} Flat bytes, {retainedSourceFunctions.size} source functions, and {residentHelpers.size} resident helpers"
