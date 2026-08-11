import Fir.Wasm.Emit.ResidentLinker
import VersoSlides.Pretty

namespace VersoFirHtml.Compile

open Lean

/-- The real complete-HTML entry published by Verso. -/
def entry : Name := ``VersoSlides.Pretty.formatHtmlForRuntime

/--
Capture the real entry immediately before Lean's final LCNF-to-IR handoff.

This is the same single-unit capture used by the accepted Flat package. It
lets Lean specialize the imported `Std.Format.prettyM` closure for the HTML
monad and leaves only genuine runtime primitives at the resident boundary.
-/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntryFinalCapturedInternalized entry #[]
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/-- Lower the unmodified source closure before resident-runtime linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  let result ← Fir.Wasm.Emit.Source.compileModuleArtifact source
  return result.bind Fir.Wasm.Emit.ResidentLinker.prepareArenaArtifact

def residentPolicy : Fir.Wasm.Emit.ResidentLinker.Policy :=
  Fir.Wasm.Emit.ResidentLinker.closedApplicationPolicy #[entry]

def linkResidentRuntime (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  Fir.Wasm.Emit.ResidentLinker.linkArtifact residentPolicy artifact

/-- Compile the source entry and close its complete runtime in Wasm. -/
def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind linkResidentRuntime

end VersoFirHtml.Compile
