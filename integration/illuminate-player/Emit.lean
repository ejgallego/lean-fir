import IlluminateFirNative.Compile
import IlluminateFirNative.ArtifactIO
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let baseResult ← liftCoreM IlluminateFirNative.Compile.compileBaseModule
  let base ← match baseResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile Illuminate player: {repr error}"
  let artifact ← match IlluminateFirNative.Compile.internalizeExistingRuntime base with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link Illuminate runtime: {repr error}"
  match ← IlluminateFirNative.ArtifactIO.write "_build/illuminate-player" base artifact with
  | .ok () => pure ()
  | .error error => throwError "{error}"
