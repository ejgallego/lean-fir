import Fir.Wasm.Emit.PrettyFormat
import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentPrettyFormat

open Lean
open Fir.Wasm.Emit.Source

/--
Compile the existing monomorphic `prettyM` facade, then internalize only its
`getTag` runtime operation. The captured final LCNF is unchanged; this is a
symbolic Wasm linking step after ordinary lowering.
-/
def compileModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← Fir.Wasm.Emit.PrettyFormat.compileModule entry
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => return .error error
  let module ← match Fir.Wasm.Emit.ResidentRuntime.internalizeGetTag artifact.module with
    | .ok module => pure module
    | .error error =>
        return .error (.manifest s!"failed to internalize resident getTag: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => return .error (.encoding error)
  return .ok { artifact with module, bytes }

end Fir.Wasm.Emit.ResidentPrettyFormat
