import Fir.Validation.LCNF
import Fir.Wasm.Emit.Manifest
import Fir.Wasm.WellFormed

namespace Fir.Wasm.Emit.Source

open Lean

inductive CompileError where
  | lowering (error : Fir.Wasm.SupportedLoweringError)
  | encoding (error : Fir.Wasm.Emit.EncodeError)
  | manifest (message : String)
  deriving Inhabited, Repr

structure Artifact where
  source : Fir.Validation.Lcnf.Artifact
  module : Fir.Wasm.Module
  bytes : ByteArray
  manifest : Json
  formattedLcnf : String

/-- Compile one closed Lean declaration through final impure LCNF into a Wasm artifact. -/
def compileClosed (entry : Name) (dependencies : Array Name := #[]) :
    CoreM (Except CompileError Artifact) := do
  let source ← Fir.Validation.Lcnf.compileEntry entry dependencies
  let module ←
    match Fir.Wasm.lowerSupported source.program with
    | .ok module => pure module
    | .error error => return .error (.lowering error)
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => return .error (.encoding error)
  let manifest ←
    match Manifest.artifactJson entry.toString entry entry module #[] with
    | .ok manifest => pure manifest
    | .error message => return .error (.manifest message)
  let formattedLcnf ← source.format
  return .ok { source, module, bytes, manifest, formattedLcnf }

def Artifact.write (artifact : Artifact) (path : System.FilePath) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path artifact.bytes
  IO.FS.writeFile (path.toString ++ ".json") artifact.manifest.compress
  IO.FS.writeFile (path.toString ++ ".lcnf") (artifact.formattedLcnf ++ "\n")

end Fir.Wasm.Emit.Source
