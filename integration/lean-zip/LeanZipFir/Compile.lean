import Fir.Wasm.Emit.ResidentLinker
import Zip.Wasm.Stored
import Zip.Wasm.Level1

namespace LeanZipFir.Compile

open Lean

/-- Smallest backend-neutral lean-zip root. -/
def storedEntry : Name := ``Zip.Wasm.compressStored

/-- First production DEFLATE matcher/emitter root. -/
def level1Entry : Name := ``Zip.Wasm.compressLevel1

/-- Package-lifetime initializer retained by the Level-1 two-region arena. -/
def level1PersistentInitializer : Name :=
  Fir.Wasm.Emit.ResidentCache.persistentInitializerName

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

/--
Capture the real Level-1 source closure through the repaired generic
final-LCNF path. The capture owns the generated closed-term and specialization
names in its synthetic compiler unit while retaining the real source entry.
-/
def captureLevel1 : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntriesFinalCapturedInternalized #[level1Entry]
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

private def compileStoredUnprepared : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureStored
  Fir.Wasm.Emit.Source.compileModuleArtifact source

/-- Lower the unmodified source closure before adding resident ByteArray code. -/
def compileStoredBase : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileStoredUnprepared
  return result.bind Fir.Wasm.Emit.ResidentLinker.prepareArenaArtifact

/-- Complete zero-import resident package frontier for stored DEFLATE. -/
def compileStored : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileStoredUnprepared
  return result.bind <|
    Fir.Wasm.Emit.ResidentLinker.prepareArenaAndLinkArtifact fun module =>
      Fir.Wasm.Emit.ResidentLinker.closedApplicationAvailablePolicy
        module #[storedEntry]

private def compileLevel1Unprepared : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureLevel1
  Fir.Wasm.Emit.Source.compileModuleArtifact source

/-- Lower the unmodified Level-1 closure before resident linking. -/
def compileLevel1Base : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileLevel1Unprepared
  return result.bind
    Fir.Wasm.Emit.ResidentLinker.preparePersistentCacheArenaArtifact

/-- Complete zero-import resident package frontier for Level-1 DEFLATE. -/
def compileLevel1 : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileLevel1Unprepared
  return result.bind <|
    Fir.Wasm.Emit.ResidentLinker.preparePersistentCacheArenaAndLinkArtifact fun module =>
      Fir.Wasm.Emit.ResidentLinker.closedApplicationAvailablePolicy
        module #[level1Entry, level1PersistentInitializer]

end LeanZipFir.Compile
