import Fir.Wasm.Emit.ResidentLinker
import Illuminate.Animation.FirLive

namespace IlluminateFirNative.Compile

open Lean
open Lean.Compiler

private def liveEntries : Array Name := #[
  ``Illuminate.AnimationPlayer.initialLive,
  ``Illuminate.AnimationPlayer.transitionLive]

/--
Capture both persistent-player entries through Lean's ordinary final-LCNF
object-family calling convention. No application-specific ABI recovery is
needed: FIR admits the same `object`/`tagged`/`tobject` call compatibility
used by upstream Lean's final-LCNF emitter.
-/
def captureSource : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Validation.Lcnf.Artifact) := do
  return .ok (← Fir.Wasm.Emit.Source.compileEntriesFinalCapturedInternalized
    liveEntries)

private def configureLiveModule
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← Fir.Wasm.Emit.ResidentCache.eliminateLazyInitializers
      artifact.module |>.mapError fun error =>
        Fir.Wasm.Emit.Source.CompileError.manifest
          s!"failed to make the live module rewind-safe: {repr error}"
  unless module.globals.isEmpty do
    throw (.manifest "live source module unexpectedly retained resident globals")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

/-- Lower the unmodified Illuminate final-LCNF closure before resident linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  match source with
  | .error error => return .error error
  | .ok source => do
      let result ← Fir.Wasm.Emit.Source.compileModuleArtifactWithExports source
        liveEntries .ok
      return result.bind configureLiveModule

/-- Link every reusable resident helper family already accepted by W7, then
retain exactly the requested source and allocator exports. -/
def internalizeExistingRuntimeForExports
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact)
    (sourceExports : Array Name) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  Fir.Wasm.Emit.ResidentLinker.linkArtifact
    (Fir.Wasm.Emit.ResidentLinker.closedApplicationPolicy sourceExports) artifact

/-- Link the accepted resident runtime for the v3 live-player entries. -/
def internalizeExistingRuntime (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  internalizeExistingRuntimeForExports artifact liveEntries

/-- Compile and link the currently reusable Wasm-resident runtime frontier. -/
def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind internalizeExistingRuntime

end IlluminateFirNative.Compile
