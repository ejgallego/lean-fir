import IlluminateFirNative.Compile
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
  let baseResult ← liftCoreM IlluminateFirNative.Compile.compileBaseModule
  let base ← match baseResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile Illuminate player: {repr error}"
  match ← base.write "_build/illuminate-player-base.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write base Illuminate player: {repr error}"
  let artifact ← match IlluminateFirNative.Compile.internalizeExistingRuntime base with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link Illuminate runtime: {repr error}"
  match ← artifact.write "_build/illuminate-player-resident.wasm" with
  | .ok () =>
      unless artifact.module.initializers.isEmpty do
        throwError "live Illuminate module retained lazy-cache globals"
      unless artifact.module.globals.size == 1 do
        throwError "live Illuminate module must retain only the allocator frontier global"
      unless artifact.module.runtimeOperations.isEmpty do
        throwError "live Illuminate module retained unresolved runtime operations"
      let functionNames := artifact.module.functions.map (fun function => function.name)
      let sourceFunctionNames := artifact.source.program.decls.filterMap fun declaration =>
        match declaration.value with
        | .code _ => some declaration.name
        | .extern _ => none
      let retainedSourceFunctions := sourceFunctionNames.filter functionNames.contains
      let residentHelpers := functionNames.filter fun name =>
        !retainedSourceFunctions.contains name
      let internalFunctions := functionNames.filter fun name =>
        !artifact.module.exports.contains name
      let inventory := Json.mkObj [
        ("functions", nameArrayJson functionNames),
        ("publicFunctions", nameArrayJson artifact.module.exports),
        ("publicSignatures", Json.arr <| artifact.module.functions.filterMap fun function =>
          if artifact.module.exports.contains function.name then
            some (functionSignatureJson function)
          else none),
        ("internalFunctions", nameArrayJson internalFunctions),
        ("sourceFunctions", nameArrayJson retainedSourceFunctions),
        ("residentHelpers", nameArrayJson residentHelpers),
        ("lazyCacheInitializers", artifact.module.initializers.size),
        ("residentGlobals", artifact.module.globals.size),
        ("runtimeOperations", artifact.module.runtimeOperations.size)]
      IO.FS.writeFile "_build/illuminate-player-resident.wasm.inventory.json"
        (inventory.pretty ++ "\n")
      logInfo (s!"wrote {artifact.bytes.size} bytes and {functionNames.size} functions " ++
        s!"({artifact.module.exports.size} public) for {artifact.source.entry}")
  | .error error => throwError "failed to write Illuminate player: {repr error}"
