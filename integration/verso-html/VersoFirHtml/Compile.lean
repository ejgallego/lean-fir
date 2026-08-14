import Fir.Wasm.Emit.ResidentLinker

namespace VersoFirHtml.Compile

open Lean

/-- The real complete-HTML entry published by Verso. -/
def sourceModule : Name := `VersoSlides.Pretty

def entry : Name := `VersoSlides.Pretty.formatHtmlForRuntime

/--
Replay the real source module immediately before Lean's final LCNF-to-IR
handoff. This preserves the same specialization/SCC boundary as Lean's native
module build and leaves only genuine runtime primitives at the resident
boundary.
-/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact := do
  let artifact ← Fir.Wasm.Emit.Source.compileEntryModuleWiseInternalizedFrom
    sourceModule entry entry
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames
  Fir.Wasm.Emit.Source.internalizeFinalDependencies artifact
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
