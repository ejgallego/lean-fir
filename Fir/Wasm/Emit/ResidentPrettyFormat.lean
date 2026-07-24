import Fir.Wasm.Emit.PrettyFormat
import Fir.Wasm.Emit.ResidentRuntime

namespace Fir.Wasm.Emit.ResidentPrettyFormat

open Lean
open Fir.Wasm.Emit.Source

private def linkRuntime (label : String)
    (link : Fir.Wasm.Module →
      Except Fir.Wasm.Emit.ResidentRuntime.LinkError Fir.Wasm.Module)
    (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ← match link artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to internalize resident {label}: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

/--
Compile the existing monomorphic `prettyM` facade, then internalize only its
`getTag` runtime operation. The captured final LCNF is unchanged; this is a
symbolic Wasm linking step after ordinary lowering.
-/
def compileGetTagModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← Fir.Wasm.Emit.PrettyFormat.compileModule entry
  return result.bind <| linkRuntime "getTag"
    Fir.Wasm.Emit.ResidentRuntime.internalizeGetTag

/--
Compile the monomorphic `prettyM` facade and internalize the currently landed
W7 runtime closure (`getTag` and `isShared`) in order.
-/
def compileModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileGetTagModule entry
  return result.bind <| linkRuntime "isShared"
    Fir.Wasm.Emit.ResidentRuntime.internalizeIsShared

end Fir.Wasm.Emit.ResidentPrettyFormat
