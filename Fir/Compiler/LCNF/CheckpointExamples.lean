import Fir.Compiler.LCNF.Checkpoint
import Fir.Compiler.LCNF.Reify
import Lean.Elab.Command

namespace Fir.Compiler.Lcnf.CheckpointExamples

open Lean Elab Command

def identityNat (value : Nat) : Nat := value
def addTwo (value : Nat) : Nat := value + 2

/- Capture real compiler output once, and independently retain its complete
constructor quotation as a kernel-checked reference for fresh-process readback.
The reverse insertion order also exercises the extension's sorted export. -/
set_option maxHeartbeats 0 in
run_cmd do
  for (key, entry, reference) in #[
      (`zeta, ``addTwo, `Fir.Compiler.Lcnf.CheckpointExamples.expectedAdd),
      (`alpha, ``identityNat, `Fir.Compiler.Lcnf.CheckpointExamples.expectedIdentity)] do
    let artifact ← liftCoreM <| withoutModifyingEnv <| compileEntry entry
    unless artifact.program.contains entry do
      throwError "checkpoint fixture omitted its real source entry"
    let _ ← liftCoreM <| Reify.defineProgram reference artifact.program
    liftCoreM <| Checkpoint.add key artifact

end Fir.Compiler.Lcnf.CheckpointExamples
