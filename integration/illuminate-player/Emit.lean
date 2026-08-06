import IlluminateFirNative.Compile
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let result ← liftCoreM IlluminateFirNative.Compile.compileResidentModule
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile Illuminate player: {repr error}"
  match ← artifact.write "_build/illuminate-player-resident.wasm" with
  | .ok () =>
      logInfo s!"wrote {artifact.bytes.size} bytes for {artifact.source.entry}"
  | .error error => throwError "failed to write Illuminate player: {repr error}"
