import FirArrayProbe.Compile
import Lean.Elab.Command

open Lean Elab Command

private def namesJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

private def signatureJson (function : Fir.Wasm.Function) : Json :=
  Json.mkObj [
    ("name", function.name.toString),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson (function.params.map (·.2))),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson function.results)]

set_option maxHeartbeats 0 in
run_cmd do
  IO.FS.createDirAll "_build"
  let result ← liftCoreM FirArrayProbe.Compile.compileResident
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile Array probe: {repr error}"
  match ← artifact.write "_build/array-probe.raw.wasm" with
  | .error error => throwError "failed to write Array probe: {repr error}"
  | .ok () =>
      unless artifact.module.imports.isEmpty do
        throwError "Array probe retained {artifact.module.imports.size} imports"
      unless artifact.module.runtimeOperations.isEmpty do
        throwError "Array probe retained {artifact.module.runtimeOperations.size} runtime operations"
      let functionNames := artifact.module.functions.map (·.name)
      let sourceNames := artifact.source.program.decls.filterMap fun declaration =>
        match declaration.value with
        | .code _ => some declaration.name
        | .extern _ => none
      let retainedSource := sourceNames.filter functionNames.contains
      let residentHelpers := functionNames.filter fun name =>
        !retainedSource.contains name
      let inventory := Json.mkObj [
        ("functions", namesJson functionNames),
        ("sourceFunctions", namesJson retainedSource),
        ("residentHelpers", namesJson residentHelpers),
        ("publicFunctions", namesJson artifact.module.exports),
        ("publicSignatures", Json.arr <| artifact.module.functions.filterMap
          fun function => if artifact.module.exports.contains function.name then
            some (signatureJson function) else none),
        ("capturedDeclarations", artifact.source.program.decls.size),
        ("reviewedExternalsBeforeLink", artifact.source.externalNames.size),
        ("runtimeOperations", artifact.module.runtimeOperations.size)]
      IO.FS.writeFile "_build/array-probe.raw.wasm.inventory.json"
        (inventory.pretty ++ "\n")
      logInfo m!"wrote {artifact.bytes.size} Array-probe bytes with {retainedSource.size} source functions and {residentHelpers.size} resident helpers"
