import Fir.Wasm.Emit.ResidentLinker
import FirVbpVersoViewer.Compile
import Lean.Elab.Command

open Lean Elab Command

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

private def functionSignatureJson (function : Fir.Wasm.Function) : Json :=
  Json.mkObj [
    ("name", function.name.toString),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson (function.params.map (·.2))),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson function.results)]

private def importJson (import_ : Fir.Wasm.Import) : Json :=
  Json.mkObj [
    ("module", import_.moduleName),
    ("name", import_.itemName),
    ("declaration", match import_.declaration? with
      | some name => name.toString
      | none => Json.null),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson import_.signature.params),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson import_.signature.results)]

set_option maxHeartbeats 0 in
run_cmd do
  IO.FS.createDirAll "_build"
  let base ← match ← liftCoreM FirVbpVersoViewer.Compile.compileBaseModule with
    | .ok artifact => pure artifact
    | .error error => throwError "viewer base compilation failed: {repr error}"
  match ← base.write "_build/vbp-verso-viewer-base.wasm" with
  | .ok () => pure ()
  | .error error => throwError "viewer base write failed: {repr error}"
  let artifact ←
    match FirVbpVersoViewer.Compile.linkResidentRuntime base with
    | .ok artifact => pure artifact
    | .error error => throwError "viewer resident link failed: {repr error}"
  match ← artifact.write "_build/vbp-verso-viewer.wasm" with
  | .error error => throwError "viewer resident write failed: {repr error}"
  | .ok () =>
      unless artifact.module.runtimeOperations.isEmpty do
        throwError "viewer retained unresolved runtime operations"
      let importedNames := artifact.module.imports.filterMap (·.declaration?)
      unless importedNames.size == FirVbpVersoViewer.Compile.hostNames.size &&
          importedNames.all FirVbpVersoViewer.Compile.hostNames.contains &&
          FirVbpVersoViewer.Compile.hostNames.all importedNames.contains do
        throwError "viewer host import frontier changed: {repr importedNames}"
      let declarationNames := artifact.source.program.decls.map (·.name)
      let sourceFunctionNames := artifact.source.program.decls.filterMap fun decl =>
        match decl.value with
        | .code _ => some decl.name
        | .extern _ => none
      let functionNames := artifact.module.functions.map (·.name)
      let retainedSourceFunctions :=
        sourceFunctionNames.filter functionNames.contains
      let residentHelpers := functionNames.filter fun name =>
        !retainedSourceFunctions.contains name
      let inventory := Json.mkObj [
        ("capturedDeclarations", declarationNames.size),
        ("capturedDeclarationNames", nameArrayJson declarationNames),
        ("reviewedExternalsBeforeLink", artifact.source.externalNames.size),
        ("reviewedExternalNamesBeforeLink",
          nameArrayJson artifact.source.externalNames),
        ("functions", nameArrayJson functionNames),
        ("publicFunctions", nameArrayJson artifact.module.exports),
        ("publicSignatures", Json.arr <| artifact.module.functions.filterMap fun function =>
          if artifact.module.exports.contains function.name then
            some (functionSignatureJson function)
          else none),
        ("imports", Json.arr <| artifact.module.imports.map importJson),
        ("sourceFunctions", nameArrayJson retainedSourceFunctions),
        ("residentHelpers", nameArrayJson residentHelpers),
        ("lazyCacheInitializerNames", nameArrayJson artifact.module.initializers),
        ("lazyCacheInitializers", artifact.module.initializers.size),
        ("residentGlobals", artifact.module.globals.size),
        ("runtimeOperations", artifact.module.runtimeOperations.size)]
      IO.FS.writeFile "_build/vbp-verso-viewer.inventory.json"
        (inventory.pretty ++ "\n")
      logInfo m!"wrote {artifact.bytes.size} viewer bytes, {retainedSourceFunctions.size} source functions, {residentHelpers.size} resident helpers, and {artifact.module.imports.size} host imports"
