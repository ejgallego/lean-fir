import Fir.Compiler.LCNF.Checkpoint
import IlluminateFirNative.Entries
import IlluminateFirNative.ArtifactIO

open Lean

private def usage :=
  "usage: illuminatePlayerArtifact (full|selection) CAPTURE_MODULE CAPTURE_KEY"

private unsafe def generate (mode moduleName key : String) : IO Unit := do
  let (entries, exports, stem) ← match mode with
    | "full" => pure (IlluminateFirNative.Entries.full,
        IlluminateFirNative.Entries.full, "_build/illuminate-player")
    | "selection" => pure (IlluminateFirNative.Entries.selection,
        IlluminateFirNative.Entries.selectionPublic, "_build/illuminate-selection-player")
    | _ => throw <| IO.userError usage
  initSearchPath (← findSysroot) [".lake/build/lib/lean", "../../.lake/build/lib/lean"]
  enableInitializersExecution
  let options := maxHeartbeats.set ({} : Options) 0
  let env ← importModules #[{ module := moduleName.toName }] options
    (leakEnv := true) (loadExts := false)
  let ((baseResult, linkedResult), _) ← Core.CoreM.toIO
      (ctx := { fileName := "NativeArtifactMain.lean", fileMap := default, options })
      (s := { env }) do
    let some source ← Fir.Compiler.Lcnf.Checkpoint.getModule? moduleName.toName key.toName
      | throwError "missing player checkpoint {moduleName}/{key}"
    unless source.entry == entries[0]! && entries.all source.program.contains do
      throwError "player checkpoint does not contain the selected source entries"
    let baseResult ← Fir.Wasm.Emit.Source.compileModuleArtifactWithExports source entries .ok
    let baseResult := baseResult.bind Fir.Wasm.Emit.ResidentLinker.prepareArenaArtifact
    let linkedResult := baseResult.bind fun artifact =>
      Fir.Wasm.Emit.ResidentLinker.linkArtifact
        (Fir.Wasm.Emit.ResidentLinker.closedApplicationFrontierPolicy exports) artifact
    return (baseResult, linkedResult)
  let base ← IO.ofExcept <| baseResult.mapError fun error => s!"{repr error}"
  let linked ← IO.ofExcept <| linkedResult.mapError fun error => s!"{repr error}"
  IO.ofExcept (← IlluminateFirNative.ArtifactIO.write stem base linked)

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, moduleName, key] =>
    if mode != "full" && mode != "selection" then
      IO.eprintln usage
      return 2
    try
      generate mode moduleName key
      return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
    IO.eprintln usage
    return 2
