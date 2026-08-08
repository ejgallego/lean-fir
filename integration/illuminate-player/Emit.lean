import IlluminateFirNative.Compile
import Lean.Elab.Command

open Lean Elab Command

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

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
        ("internalFunctions", nameArrayJson internalFunctions),
        ("sourceFunctions", nameArrayJson retainedSourceFunctions),
        ("residentHelpers", nameArrayJson residentHelpers)]
      IO.FS.writeFile "_build/illuminate-player-resident.wasm.inventory.json"
        (inventory.pretty ++ "\n")
      logInfo (s!"wrote {artifact.bytes.size} bytes and {functionNames.size} functions " ++
        s!"({artifact.module.exports.size} public) for {artifact.source.entry}")
  | .error error => throwError "failed to write Illuminate player: {repr error}"
