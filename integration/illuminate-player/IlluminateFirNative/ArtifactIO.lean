import Fir.Wasm.Emit.ResidentLinker

namespace IlluminateFirNative.ArtifactIO

open Lean

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

private def functionSignatureJson (function : Fir.Wasm.Function) : Json :=
  Json.mkObj [
    ("name", function.name.toString),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson (function.params.map (·.2))),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson function.results)]

/-- Shared frontend/native output path and unchanged arena/inventory checks. -/
def write (stem : String) (base artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    IO (Except String Unit) := do
  match ← base.write (stem ++ "-base.wasm") with
  | .error error => return .error s!"failed to write base player: {repr error}"
  | .ok () => pure ()
  match ← artifact.write (stem ++ "-resident.wasm") with
  | .error error => return .error s!"failed to write resident player: {repr error}"
  | .ok () => pure ()
  unless artifact.module.initializers.isEmpty do
    return .error "live player module retained lazy-cache globals"
  unless artifact.module.globals.size == 1 do
    return .error "live player module must retain only the allocator frontier global"
  unless artifact.module.runtimeOperations.isEmpty do
    return .error "live player module retained unresolved runtime operations"
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
  IO.FS.writeFile (stem ++ "-resident.wasm.inventory.json") (inventory.pretty ++ "\n")
  IO.println s!"wrote {artifact.bytes.size} bytes and {functionNames.size} functions ({artifact.module.exports.size} public) for {artifact.source.entry}"
  return .ok ()

end IlluminateFirNative.ArtifactIO
