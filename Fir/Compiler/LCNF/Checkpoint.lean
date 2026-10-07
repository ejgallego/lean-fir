import Fir.Compiler.LCNF

namespace Fir.Compiler.Lcnf.Checkpoint

open Lean

/-- One named final-LCNF source closure persisted in its owning olean. -/
structure Entry where
  key : Name
  artifact : Artifact

/--
Persist compiler capture independently of lowering and runtime linking. Lake
owns the olean's dependencies; consumers read an exact module/key rather than
replaying capture or relying on merged state from unrelated modules.
-/
initialize capturedArtifactExt :
    SimplePersistentEnvExtension Entry (NameMap Artifact) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.insert entry.key entry.artifact
    addImportedFn := fun modules => modules.foldl (init := {}) fun state entries =>
      entries.foldl (fun state entry => state.insert entry.key entry.artifact) state
    toArrayFn := fun entries => entries.toArray.qsort fun left right =>
      Name.quickLt left.key right.key
    asyncMode := .sync }

def add (key : Name) (artifact : Artifact) : CoreM Unit :=
  modifyEnv fun env => capturedArtifactExt.addEntry env { key, artifact }

/-- Read one owning module's entry, including with `importModules loadExts := false`. -/
def getModule? (moduleName key : Name) : CoreM (Option Artifact) := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName | return none
  return (capturedArtifactExt.getModuleEntries env moduleIndex).findSome? fun entry =>
    if entry.key == key then some entry.artifact else none

end Fir.Compiler.Lcnf.Checkpoint
