import Fir.Wasm.Emit.ResidentLinker
import VersoSlides.Pretty

namespace VersoFirFlat.Compile

open Lean

def entry : Name := ``VersoSlides.Pretty.formatRenderedForRuntime

/-- Capture the real Verso entry immediately before Lean's final LCNF-to-IR handoff. -/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntryFinalCapturedInternalized entry #[]
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/-- Lower the unmodified source closure before resident runtime linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  let result ← Fir.Wasm.Emit.Source.compileModuleArtifact source
  return result.bind Fir.Wasm.Emit.ResidentLinker.prepareArenaArtifact

/--
Use the same declaration-driven closed-application policy as the Illuminate
packages. Flat supplies only its public entry; runtime-family selection and
postconditions are shared rather than repeated as a package-specific list.
-/
def residentPolicy : Fir.Wasm.Emit.ResidentLinker.Policy :=
  Fir.Wasm.Emit.ResidentLinker.closedApplicationPolicy #[entry]

def linkResidentRuntime (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  Fir.Wasm.Emit.ResidentLinker.linkArtifact residentPolicy artifact

/-- Compile the real source entry and close its complete runtime in Wasm. -/
def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind linkResidentRuntime

end VersoFirFlat.Compile
