import Fir.Wasm.Emit.ResidentNatArithmetic

/-! Diagnostic exports expose the unchanged production generic helper directly,
including cases normally handled by its immediate caller fast path. -/
open Fir.Wasm Fir.Wasm.Emit

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected output Wasm path")
  let module ← IO.ofExcept ResidentNatArithmetic.residentExampleModule
  let module := { module with exports := (#[
    ResidentNatArithmetic.mulGenericName, ResidentRelease.decrementOnceName,
    ResidentBigNumeric.validateNaturalName]).foldl Fir.Wasm.addUnique module.exports }
  let bytes ← IO.ofExcept <| (encode module).mapError (fun e => reprStr e)
  IO.FS.writeBinFile path bytes
  IO.FS.writeFile (path ++ ".json") ResidentNatArithmetic.manifest.compress
  IO.println s!"Nat multiplication diagnostic: {bytes.size} bytes, {module.imports.size} imports"
