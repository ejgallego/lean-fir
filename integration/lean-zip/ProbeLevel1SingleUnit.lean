import LeanZipFir.Compile
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  discard <| ← liftCoreM LeanZipFir.Compile.captureLevel1SingleUnit
