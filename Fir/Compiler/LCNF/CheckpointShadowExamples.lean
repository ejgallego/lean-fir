import Fir.Compiler.LCNF.CheckpointExamples
import Lean.Elab.Command

open Lean Elab Command

/- The same key in a different owning module must not replace an explicit
lookup in the first module, even when merged extension state shadows it. -/
run_cmd do
  let some artifact ← liftCoreM <|
      Fir.Compiler.Lcnf.Checkpoint.getModule?
        `Fir.Compiler.LCNF.CheckpointExamples `zeta
    | throwError "checkpoint producer was not loaded"
  liftCoreM <| Fir.Compiler.Lcnf.Checkpoint.add `alpha artifact
