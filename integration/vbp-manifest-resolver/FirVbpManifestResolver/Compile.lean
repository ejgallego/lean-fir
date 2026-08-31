import Fir.Wasm.Emit.ResidentLinker

namespace FirVbpManifestResolver.Compile

open Lean

def sourceModule : Name := `VersoBlueprintRuntime.ManifestResolver

def entry : Name :=
  `VersoBlueprint.Runtime.ManifestResolver.resolveBatchJson

/-- Capture the real isolated root from its exact final-LCNF source view. -/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact := do
  let artifact ← Fir.Wasm.Emit.Source.compileEntryIndividuallyInternalized
    entry Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames
  Fir.Wasm.Emit.Source.internalizeFinalDependencies artifact
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

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

def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind linkResidentRuntime

end FirVbpManifestResolver.Compile
