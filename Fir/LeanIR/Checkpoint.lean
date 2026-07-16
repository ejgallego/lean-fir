import Fir.LeanIR.Pipeline

namespace Fir.LeanIR

open Lean
open Lean.Compiler

/-- The actual declaration group observed immediately around one compiler pass. -/
structure ImpurePassCheckpoint where
  key : PassKey
  before : Array (LCNF.Decl .impure)
  after : Array (LCNF.Decl .impure)
  deriving Inhabited

initialize impurePassCheckpointExt : EnvExtension (Array ImpurePassCheckpoint) ←
  registerEnvExtension (pure #[]) (asyncMode := .sync)

def getImpurePassCheckpoints : CoreM (Array ImpurePassCheckpoint) := do
  return impurePassCheckpointExt.getState (← getEnv)

def ImpurePassCheckpoint.contains (checkpoint : ImpurePassCheckpoint) (name : Name) : Bool :=
  checkpoint.before.any (·.name == name) || checkpoint.after.any (·.name == name)

def findLatestImpurePassCheckpoint? (key : PassKey) (declName : Name) :
    CoreM (Option ImpurePassCheckpoint) := do
  return (← getImpurePassCheckpoints).toList.reverse.find? fun checkpoint =>
    checkpoint.key == key && checkpoint.contains declName

private def recordImpurePassCheckpoint (checkpoint : ImpurePassCheckpoint) :
    LCNF.CompilerM Unit := do
  modifyEnv fun environment =>
    impurePassCheckpointExt.modifyState environment (·.push checkpoint)

/--
Lean 4.32's real `simpCase` pass, wrapped only with before/after recording.
The pass body is not reimplemented here.
-/
def capturedSimpCasePass : LCNF.Pass where
  occurrence := LCNF.simpCase.occurrence
  phase := .impure
  phaseOut := .impure
  name := LCNF.simpCase.name
  shouldAlwaysRunCheck := LCNF.simpCase.shouldAlwaysRunCheck
  run before := do
    let after ← LCNF.simpCase.run before
    recordImpurePassCheckpoint {
      key := PassKey.ofPass LCNF.simpCase
      before
      after }
    return after

/-- A dynamic installer; it is intentionally not registered with `@[cpass]`. -/
def simpCaseCaptureInstaller : LCNF.PassInstaller :=
  LCNF.PassInstaller.replacePass .impure `simpCase (fun _ => capturedSimpCasePass)

/-- Install checkpoint capture in the current environment, for inspection commands only. -/
def installSimpCaseCapture : CoreM Unit :=
  LCNF.addPass ``simpCaseCaptureInstaller

end Fir.LeanIR
