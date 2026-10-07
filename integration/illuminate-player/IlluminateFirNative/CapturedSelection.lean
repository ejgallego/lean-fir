import Fir.Compiler.LCNF.Checkpoint
import IlluminateFirNative.SelectionCompile
import Lean.Elab.Command

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let .ok source ← liftCoreM IlluminateFirNative.SelectionCompile.captureSource
    | throwError "selection player capture failed"
  liftCoreM <| Fir.Compiler.Lcnf.Checkpoint.add `selection source
  logInfo m!"captured selection player: {source.program.decls.size} declarations"
