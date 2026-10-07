import Fir.Compiler.LCNF.Checkpoint
import IlluminateFirNative.Compile
import Lean.Elab.Command

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let .ok source ← liftCoreM IlluminateFirNative.Compile.captureSource
    | throwError "full player capture failed"
  liftCoreM <| Fir.Compiler.Lcnf.Checkpoint.add `full source
  logInfo m!"captured full player: {source.program.decls.size} declarations"
