import Fir.Wasm.Emit.PrettyFormat
import Fir.Wasm.Emit.ResidentAllocator
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

private def linkAllocator (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentAllocator.install artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to install resident allocator: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
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
W7 scalar-header closure (`getTag` and `isShared`) in order.
-/
def compileRuntimeModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileGetTagModule entry
  return result.bind <| linkRuntime "isShared"
    Fir.Wasm.Emit.ResidentRuntime.internalizeIsShared

/--
Compile the monomorphic `prettyM` facade, retain the scalar-header checkpoint,
then internalize every object and packed-`UInt8` projection supported by the
resident load surface. The captured final LCNF remains unchanged.
-/
def compileReadProjectionModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileRuntimeModule entry
  return result.bind <| linkRuntime "read projections"
    Fir.Wasm.Emit.ResidentRuntime.internalizeReadProjections

/--
Continue from the read-projection checkpoint and internalize all supported
closure-capture projections. Helpers are shared by physical slot/result kind;
the compiler and W6 refinement own operation-specific closure metadata.
-/
def compileClosureProjectionModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileReadProjectionModule entry
  return result.bind <| linkRuntime "closure projections"
    Fir.Wasm.Emit.ResidentRuntime.internalizeClosureProjections

/--
Continue from the closure-projection checkpoint and internalize exact
closure-identity tests using the stable module-wide dispatch table.
-/
def compileClosureMatchModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileClosureProjectionModule entry
  return result.bind <| linkRuntime "closure matches"
    Fir.Wasm.Emit.ResidentRuntime.internalizeClosureMatches

/--
Continue from the closure-match checkpoint and install the first Wasm-resident
heap owner. This stage intentionally leaves semantic allocation imports
unchanged; it establishes the low-level frontier and raw-store boundary used
by subsequent allocation-family internalization.
-/
def compileModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileClosureMatchModule entry
  return result.bind linkAllocator

end Fir.Wasm.Emit.ResidentPrettyFormat
