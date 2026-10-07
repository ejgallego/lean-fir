import IlluminateFirNative.SelectionCompile
import IlluminateFirNative.ArtifactIO
import Lean.Elab.Command

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let baseResult ← liftCoreM IlluminateFirNative.SelectionCompile.compileBaseModule
  let base ← match baseResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile Illuminate selection player: {repr error}"
  let artifact ← match
      IlluminateFirNative.Compile.internalizeExistingRuntimeForExports base
        IlluminateFirNative.SelectionCompile.selectionPublicExports with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link selection runtime: {repr error}"
  match ← IlluminateFirNative.ArtifactIO.write "_build/illuminate-selection-player" base artifact with
  | .ok () => pure ()
  | .error error => throwError "{error}"
