import Fir.Wasm.Emit.PrettyFormat
import Fir.Wasm.Emit.ResidentLinker
import VersoSlides.Pretty

namespace VersoFirFlat.Compile

open Lean

def entry : Name := ``VersoSlides.Pretty.formatRenderedForRuntime

/-- Capture the real Verso entry immediately before Lean's final LCNF-to-IR handoff. -/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntryFinalCapturedInternalized entry #[]
    #[Fir.Wasm.Emit.PrettyFormat.weakMonadInhabitedName]

/-- Lower the unmodified source closure before resident runtime linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  Fir.Wasm.Emit.Source.compileModuleArtifact source

/--
The explicit Flat closure policy. `commonSteps` carries the shared object,
closure, reference-count, mutation, and scalar-box surface. The remaining
steps are exactly the source closure observed for the Verso renderer.
-/
def residentPolicy : Fir.Wasm.Emit.ResidentLinker.Policy := {
  steps := Fir.Wasm.Emit.ResidentLinker.commonSteps ++ #[
    .numericAvailable,
    .bigNumeric,
    .floatAvailable,
    .arraysAvailable,
    .natModAvailable,
    .natShiftAvailable,
    .usizeAvailable,
    .stringOperations,
    .stringLiterals,
    .fallbacks,
    .directSelfTailCallsRequired]
  publicExports := some <|
    #[entry] ++ Fir.Wasm.Emit.ResidentLinker.allocatorExports
  requireZeroImports := true
  requireNoRuntimeOperations := true }

def linkResidentRuntime (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  Fir.Wasm.Emit.ResidentLinker.linkArtifact residentPolicy artifact

/-- Compile the real source entry and close its complete runtime in Wasm. -/
def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind linkResidentRuntime

end VersoFirFlat.Compile

