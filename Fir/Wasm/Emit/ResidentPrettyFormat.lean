import Fir.Wasm.Emit.PrettyFormat
import Fir.Wasm.Emit.ResidentAllocator
import Fir.Wasm.Emit.ResidentCache
import Fir.Wasm.Emit.ResidentClosureAllocation
import Fir.Wasm.Emit.ResidentConstructor
import Fir.Wasm.Emit.ResidentFallback
import Fir.Wasm.Emit.ResidentLiteral
import Fir.Wasm.Emit.ResidentMutation
import Fir.Wasm.Emit.ResidentBigNumeric
import Fir.Wasm.Emit.ResidentNumeric
import Fir.Wasm.Emit.ResidentReferenceCount
import Fir.Wasm.Emit.ResidentRelease
import Fir.Wasm.Emit.ResidentRuntime
import Fir.Wasm.Emit.ResidentString
import Fir.Wasm.Emit.ResidentLinker
import Fir.Wasm.Emit.TailCall

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

def internalizeImmediateNaturals (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentLiteral.internalizeImmediateNaturals
        artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident immediate Naturals: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizePartialApplications (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match
        Fir.Wasm.Emit.ResidentClosureAllocation.internalizePartialApplications
          artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident partial applications: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeSetters (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentMutation.internalizeSetters artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident setters: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeTagSetters (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentMutation.internalizeTagSetters artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident tag setters: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeIncrements (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentReferenceCount.internalizeIncrements
        artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident increments: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeReleases (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentRelease.internalizeReleases artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident recursive releases: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeCacheSets (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentCache.internalizeCacheSets artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident lazy-cache publication: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeNumeric (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentNumeric.internalize artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident Nat/Int operations: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeBigNumeric (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentBigNumeric.internalize artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize arbitrary-precision Nat/Int operations: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeStringOperations (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentString.internalize artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident String operations: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeStringLiterals (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentLiteral.internalizeStrings artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident String literals: {repr error}")
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

def internalizeFallbacks (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ←
    match Fir.Wasm.Emit.ResidentFallback.internalize artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest
          s!"failed to internalize resident fallbacks: {repr error}")
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

/--
Continue from constructor allocation and internalize the immediate-Natural
literal family. String helpers are already available standalone, but remain
imports until their JavaScript-consuming external family is resident.
-/
def compileImmediateNaturalModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileConstructorModule entry
  return result.bind internalizeImmediateNaturals

/--
Continue from immediate Naturals and internalize closure allocation using the
retained dispatch and capture-descriptor tables.
-/
def compilePartialApplicationModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileImmediateNaturalModule entry
  return result.bind internalizePartialApplications

/--
Continue from closure allocation and internalize the object-slot and packed
scalar writes reachable from `prettyM`.
-/
def compileSetterModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compilePartialApplicationModule entry
  return result.bind internalizeSetters

/--
Continue from direct constructor writes and internalize nonrecursive
reference-count increments reachable from `prettyM`.
-/
def compileIncrementModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileSetterModule entry
  return result.bind internalizeIncrements

/--
Continue from nonrecursive increments and internalize recursive decrements and
nonrecursive delete using the retained closure-capture descriptor table.
-/
def compileReleaseModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileIncrementModule entry
  return result.bind internalizeReleases

/--
Continue from recursive release and internalize constructor-tag writes. The
plain-text `prettyM` facade currently has no such operation; the
styling-preserving facade has one fixed tag write.
-/
def compileTagSetterModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileReleaseModule entry
  return result.bind internalizeTagSetters

/--
Continue from constructor-tag writes and internalize lazy-cache publication.
The compiler-produced miss path retains the physical cached value and
initialized flag in module globals; this stage makes its reachable object
graph persistent in Wasm and returns the same physical lane.
-/
def compileCacheModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileTagSetterModule entry
  return result.bind internalizeCacheSets

/--
Continue from lazy-cache publication and internalize the ten Nat/Int
operations reachable from `prettyM`. The current generation helper covers
canonical immediates and canonical one-limb W6 numeric objects; multi-limb
numeric inputs trap explicitly pending the recursive-limb extension.
-/
def compileNumericModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) :=
  return (← compileCacheModule entry).bind internalizeNumeric

/--
Continue from the stable one-limb helper checkpoint and redirect
compiler-generated Nat/Int calls to the versioned arbitrary-precision helper
set. The one-limb exports remain present for parallel W6 proof work.
-/
def compileBigNumericModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) :=
  return (← compileNumericModule entry).bind internalizeBigNumeric

/--
Continue from arbitrary-precision Nat/Int operations, internalize the eight UTF-8 String
declarations reachable from `prettyM`, and then move its four String literals
into the same module-owned heap.
-/
def compileStringModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileBigNumericModule entry
  return result.bind internalizeStringOperations |>.bind internalizeStringLiterals

/--
Close the last two failure-only declarations with unconditional resident traps.
The resulting module owns its memory and has no function imports.
-/
def compileClosedModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileStringModule entry
  return result.bind internalizeFallbacks

/--
Eliminate direct self calls in tail position after closing the resident
runtime. Lean's `Std.Format.prettyM` work-list worker uses this shape for each
document step; retaining ordinary Wasm calls makes a cold engine's native
stack proportional to the document size.
-/
def eliminateDirectSelfCalls (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let result ← Fir.Wasm.Emit.TailCall.eliminateDirectSelfCalls artifact.module
    |>.mapError fun message => .manifest message
  unless result.rewrittenCalls > 0 do
    throw (.manifest "prettyM closure contains no direct self-tail calls")
  let bytes ← Fir.Wasm.Emit.encode result.module
    |>.mapError Source.CompileError.encoding
  return { artifact with module := result.module, bytes }

/-- Close the resident runtime and make compiler-generated self-tail calls stack-safe. -/
def compileStackSafeModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let result ← compileClosedModule entry
  return result.bind eliminateDirectSelfCalls

/--
Current furthest W7 resident-runtime artifact for compiler consumers. The
checkpoint API above remains available for acceptance generation; this path
encodes only the final closed module.
-/
def compileModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let source ← Fir.Wasm.Emit.PrettyFormat.compileSource entry
  match source with
  | .ok source =>
      Source.compileModuleArtifactWith source fun module =>
        Fir.Wasm.Emit.ResidentLinker.linkModule
          Fir.Wasm.Emit.ResidentLinker.prettyFormatPolicy module
  | .error error => return .error error

end Fir.Wasm.Emit.ResidentPrettyFormat
