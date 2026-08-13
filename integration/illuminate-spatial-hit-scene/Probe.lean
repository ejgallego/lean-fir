import IlluminateFirSpatialHitScene.Compile
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let source ← liftCoreM IlluminateFirSpatialHitScene.Compile.captureSource
  logInfo m!"spatial HitScene captured {source.program.decls.size} declarations and {source.externalNames.size} reviewed externals"
  let base ← match ← liftCoreM IlluminateFirSpatialHitScene.Compile.compileBaseModule with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile spatial HitScene source: {repr error}"
  logInfo m!"spatial HitScene base has {base.module.functions.size} functions, {base.module.imports.size} imports, and {base.module.runtimeOperations.size} runtime operations"
  let frontier ← match IlluminateFirSpatialHitScene.Compile.linkResidentFrontier base with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link spatial HitScene resident frontier: {repr error}"
  logInfo m!"spatial HitScene frontier has {frontier.module.functions.size} functions, {frontier.module.imports.size} imports, and {frontier.module.runtimeOperations.size} runtime operations"
  for import_ in frontier.module.imports do
    match Fir.Wasm.Emit.Manifest.importJson import_ with
    | .ok json => logInfo m!"spatial unresolved: {json.compress}"
    | .error error => throwError "failed to describe spatial import: {error}"
