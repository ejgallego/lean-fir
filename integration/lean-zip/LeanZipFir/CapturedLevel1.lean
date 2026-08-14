import LeanZipFir.CaptureCache
import LeanZipFir.Compile
import Lean.Elab.Command

open Lean Elab Command

/-
Build-time checkpoint for the expensive compiler capture. Lake builds this
olean as a dependency of the native generator without linking its lean-zip
source closure into that executable.
-/
set_option maxHeartbeats 0 in
run_cmd do
  let started ← IO.monoMsNow
  let artifact ← liftCoreM LeanZipFir.Compile.captureLevel1
  liftCoreM <| LeanZipFir.CaptureCache.add `leanZipLevel1 artifact
  let finished ← IO.monoMsNow
  logInfo m!"cached {artifact.program.decls.size} Level-1 declarations in {finished - started}ms"
