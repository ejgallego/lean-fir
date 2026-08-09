import IlluminateFirNative.Compile
import Illuminate.Animation.FirSelection

namespace IlluminateFirNative

/--
Constructor-specific browser entry for the steady-state animation-frame path.
The state machine remains the real Illuminate implementation: this facade only
constructs the `tick` event on the Wasm side.
-/
def transitionSelectionTickLive
    (animation : Illuminate.AnimationPlayer.SelectionAnimation)
    (state : Illuminate.AnimationPlayer.PlayerState)
    (timestamp : Float) : Illuminate.AnimationPlayer.LiveSelectionTransition :=
  Illuminate.AnimationPlayer.transitionSelectionLive animation state (.tick timestamp)

end IlluminateFirNative

namespace IlluminateFirNative.SelectionCompile

open Lean
open Lean.Compiler

def selectionEntries : Array Name := #[
  ``Illuminate.AnimationPlayer.initialSelectionLive,
  ``Illuminate.AnimationPlayer.transitionSelectionLive,
  ``IlluminateFirNative.transitionSelectionTickLive]

/--
The raw `Float` entry stays internal. JavaScript calls its automatically
generated integer-lane facade so all binary64 payload bits cross the boundary
without a host floating-point coercion.
-/
def selectionPublicExports : Array Name := #[
  ``Illuminate.AnimationPlayer.initialSelectionLive,
  ``Illuminate.AnimationPlayer.transitionSelectionLive,
  Fir.Wasm.Emit.BitExactFloat.facadeName
    ``IlluminateFirNative.transitionSelectionTickLive]

/-- Capture the real selection-only entries without application-specific ABI repair. -/
def captureSource : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Validation.Lcnf.Artifact) := do
  return .ok (← Fir.Wasm.Emit.Source.compileEntriesFinalCapturedInternalized
    selectionEntries)

private def configureSelectionModule
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← Fir.Wasm.Emit.ResidentCache.eliminateLazyInitializers
      artifact.module |>.mapError fun error =>
        Fir.Wasm.Emit.Source.CompileError.manifest
          s!"failed to make the selection module rewind-safe: {repr error}"
  unless module.globals.isEmpty do
    throw (.manifest "selection source module unexpectedly retained resident globals")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

/-- Lower the checked selection-only final-LCNF closure before resident linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  match source with
  | .error error => return .error error
  | .ok source => do
      let result ← Fir.Wasm.Emit.Source.compileModuleArtifactWithExports source
        selectionEntries .ok
      return result.bind configureSelectionModule

/-- Compile and link the selection-only entries against the accepted resident
runtime while retaining the generic oracle and bit-exact tick facade. -/
def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind fun artifact =>
    IlluminateFirNative.Compile.internalizeExistingRuntimeForExports artifact
      selectionPublicExports

end IlluminateFirNative.SelectionCompile
