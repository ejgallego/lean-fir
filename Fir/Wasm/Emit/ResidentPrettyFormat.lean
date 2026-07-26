import Fir.Wasm.Emit.PrettyFormat
import Fir.Wasm.Emit.ResidentAllocator
import Fir.Wasm.Emit.ResidentConstructor
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

def installAllocator (artifact : Source.ModuleArtifact) :
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

def internalizeConstructors (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentConstructor.internalizeConstructors artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident constructor allocation: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeGetTag (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact :=
  linkRuntime "getTag" Fir.Wasm.Emit.ResidentRuntime.internalizeGetTag artifact

def internalizeIsShared (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact :=
  linkRuntime "isShared" Fir.Wasm.Emit.ResidentRuntime.internalizeIsShared artifact

def internalizeReadProjections (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact :=
  linkRuntime "read projections"
    Fir.Wasm.Emit.ResidentRuntime.internalizeReadProjections artifact

def internalizeClosureProjections (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact :=
  linkRuntime "closure projections"
    Fir.Wasm.Emit.ResidentRuntime.internalizeClosureProjections artifact

def internalizeClosureMatches (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact :=
  linkRuntime "closure matches"
    Fir.Wasm.Emit.ResidentRuntime.internalizeClosureMatches artifact

/--
Compile the existing monomorphic `prettyM` facade, then internalize only its
`getTag` runtime operation. The captured final LCNF is unchanged; this is a
symbolic Wasm linking step after ordinary lowering.
-/
def compileGetTagModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← Fir.Wasm.Emit.PrettyFormat.compileModule entry
  return result.bind internalizeGetTag

/--
Compile the monomorphic `prettyM` facade and internalize the currently landed
W7 scalar-header closure (`getTag` and `isShared`) in order.
-/
def compileRuntimeModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileGetTagModule entry
  return result.bind internalizeIsShared

/--
Compile the monomorphic `prettyM` facade, retain the scalar-header checkpoint,
then internalize every object and packed-`UInt8` projection supported by the
resident load surface. The captured final LCNF remains unchanged.
-/
def compileReadProjectionModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileRuntimeModule entry
  return result.bind internalizeReadProjections

/--
Continue from the read-projection checkpoint and internalize all supported
closure-capture projections. Helpers are shared by physical slot/result kind;
the compiler and W6 refinement own operation-specific closure metadata.
-/
def compileClosureProjectionModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileReadProjectionModule entry
  return result.bind internalizeClosureProjections

/--
Continue from the closure-projection checkpoint and internalize exact
closure-identity tests using the stable module-wide dispatch table.
-/
def compileClosureMatchModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileClosureProjectionModule entry
  return result.bind internalizeClosureMatches

/--
Continue from the closure-match checkpoint and install the first Wasm-resident
heap owner. This stage intentionally leaves semantic allocation imports
unchanged; it establishes the low-level frontier and raw-store boundary used
by subsequent allocation-family internalization.
-/
def compileAllocatorModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileClosureMatchModule entry
  return result.bind installAllocator

/--
Continue from the resident allocator checkpoint and replace every supported
constructor-allocation runtime import with a direct Wasm helper. Empty
constructors return their immediate word; heap constructors allocate, zero,
and initialize the exact concrete header and object-field slots.
-/
def compileConstructorModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileAllocatorModule entry
  return result.bind internalizeConstructors

/-- Current furthest W7 resident-runtime checkpoint for compiler consumers. -/
def compileModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) :=
  compileConstructorModule entry

end Fir.Wasm.Emit.ResidentPrettyFormat
