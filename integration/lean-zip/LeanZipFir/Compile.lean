import Fir.Wasm.Emit.ResidentLinker
import Zip.Wasm.Stored

namespace LeanZipFir.Compile

open Lean

/-- Smallest backend-neutral lean-zip root. -/
def storedEntry : Name := ``Zip.Wasm.compressStored

/--
Capture the real stored-block entry through FIR's legacy-source final-LCNF
pipeline. This lean-zip revision predates Lean's `module` / `public section`
syntax, so its oleans do not contain the per-module deferred compiler groups
used by `compileEntryModuleWiseInternalized`. The generic single-unit capture
still compiles the declarations obtained from the real source environment; it
does not copy the compressor into FIR.
-/
def captureStored : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntriesFinalCapturedInternalized #[storedEntry]
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/-- Lower the unmodified source closure before adding resident ByteArray code. -/
def compileStoredBase : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureStored
  let result ← Fir.Wasm.Emit.Source.compileModuleArtifact source
  return result.bind Fir.Wasm.Emit.ResidentLinker.prepareArenaArtifact

/-- Complete zero-import resident package frontier for stored DEFLATE. -/
def compileStored : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let base ← compileStoredBase
  return base.bind fun artifact =>
    Fir.Wasm.Emit.ResidentLinker.linkArtifact
      (Fir.Wasm.Emit.ResidentLinker.closedApplicationAvailablePolicy
        artifact.module #[storedEntry]) artifact

end LeanZipFir.Compile
