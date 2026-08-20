import Fir.Wasm.Emit.ResidentLinker
import Illuminate.Diagram.HitScene

namespace IlluminateFirHitScene.Compile

open Lean

/-- The real prepared hit-scene query requested by Illuminate. -/
def entry : Name := ``Illuminate.HitScene.query

/-- The upstream module whose exact final-LCNF groups own the public entry. -/
def sourceModule : Name := `Illuminate.Diagram.HitScene

/-- Capture the real entry and recursively discovered dependencies in their
ordinary separately compiled final-LCNF units. Only the entry module is
replayed from a postponed source view; ordinary imported modules are closed
through FIR's generic final-dependency path. -/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact := do
  let artifact ← Fir.Wasm.Emit.Source.compileEntryModuleWiseInternalizedFrom
    sourceModule entry entry
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames
  Fir.Wasm.Emit.Source.internalizeFinalDependencies artifact
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/--
Diagnostic single-unit capture. Large imported closures may generate different
closed-term sharing when all roots are recompiled as one synthetic unit.
-/
def captureSourceSingleUnit : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntryFinalCapturedInternalized entry #[]
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/-- Diagnostic reproducer for per-root generated-name ABI drift. Production
uses `captureSource`, which preserves the entry module's native boundary. -/
def captureSourceIndividual : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntryIndividuallyInternalized entry
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/-- Lower the unmodified source closure before resident runtime linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  let result ← Fir.Wasm.Emit.Source.compileModuleArtifact source
  return result.bind Fir.Wasm.Emit.ResidentLinker.prepareArenaArtifact

def publicExports : Array Name := #[
  entry,
  Fir.Wasm.Emit.BitExactFloat.facadeName entry] ++
  Fir.Wasm.Emit.ResidentLinker.allocatorExports

/--
Link every already-accepted resident helper while deliberately retaining the
unresolved external frontier. This is the publication diagnostic boundary:
runtime operations must be closed before the separately compiled upstream C
math helpers are merged into the final zero-import module.
-/
def residentFrontierPolicy : Fir.Wasm.Emit.ResidentLinker.Policy := {
  Fir.Wasm.Emit.ResidentLinker.closedApplicationFrontierPolicy
    #[entry, Fir.Wasm.Emit.BitExactFloat.facadeName entry] with
  publicExports := some publicExports }

def linkResidentFrontier
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  Fir.Wasm.Emit.ResidentLinker.linkArtifact residentFrontierPolicy artifact

end IlluminateFirHitScene.Compile
