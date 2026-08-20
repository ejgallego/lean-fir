import Fir.Wasm.Emit.ResidentLinker
import FirArrayProbe

namespace FirArrayProbe.Compile

open Lean

def entries : Array Name := #[
  ``FirArrayProbe.readRepeated,
  ``FirArrayProbe.buildOnly,
  ``FirArrayProbe.updateUnique,
  ``FirArrayProbe.updateShared]

/-- Capture the real probe declarations at Lean's final-LCNF boundary. -/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntriesFinalCapturedInternalized entries
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/-- Compile and close the ordinary Lean probe against the generic resident runtime. -/
def compileResident : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  let result ← Fir.Wasm.Emit.Source.compileModuleArtifactWithExports source
    entries .ok
  return result.bind <|
    Fir.Wasm.Emit.ResidentLinker.prepareArenaAndLinkArtifact fun module =>
      Fir.Wasm.Emit.ResidentLinker.closedApplicationAvailablePolicy module
        entries

end FirArrayProbe.Compile
