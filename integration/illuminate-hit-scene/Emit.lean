import IlluminateFirHitScene.Compile
import Lean.Elab.Command

open Lean Elab Command

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

run_cmd do
  IO.FS.createDirAll "_build"
  let baseResult ← liftCoreM IlluminateFirHitScene.Compile.compileBaseModule
  let base ← match baseResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile HitScene source: {repr error}"
  match ← base.write "_build/illuminate-hit-scene-base.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write base HitScene module: {repr error}"
  let frontier ← match IlluminateFirHitScene.Compile.linkResidentFrontier base with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link HitScene resident frontier: {repr error}"
  match ← frontier.write "_build/illuminate-hit-scene-frontier.wasm" with
  | .error error => throwError "failed to write HitScene resident frontier: {repr error}"
  | .ok () =>
      unless frontier.module.runtimeOperations.isEmpty do
        throwError "HitScene resident frontier retained runtime operations"
      let imports ← frontier.module.imports.mapM fun import_ =>
        match Fir.Wasm.Emit.Manifest.importJson import_ with
        | .ok json => pure json
        | .error error => throwError "failed to describe HitScene import: {error}"
      let functions := frontier.module.functions.map (·.name)
      let inventory := Json.mkObj [
        ("entry", (frontier.source.entry.toString : Json)),
        ("capturedDeclarations", frontier.source.program.decls.size),
        ("reviewedExternalsBeforeLink", frontier.source.externalNames.size),
        ("functions", nameArrayJson functions),
        ("publicFunctions", nameArrayJson frontier.module.exports),
        ("imports", Json.arr imports),
        ("runtimeOperations", frontier.module.runtimeOperations.size)]
      IO.FS.writeFile "_build/illuminate-hit-scene-frontier.inventory.json"
        (inventory.pretty ++ "\n")
      logInfo m!"wrote {frontier.bytes.size} HitScene frontier bytes with {functions.size} functions and {imports.size} unresolved external imports"
