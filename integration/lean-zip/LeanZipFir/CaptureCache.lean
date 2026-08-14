import Fir.Wasm.Emit.Source

namespace LeanZipFir.CaptureCache

open Lean

/-- One named final-LCNF source closure persisted in the importing olean. -/
structure Entry where
  key : Name
  artifact : Fir.Validation.Lcnf.Artifact

/--
Persist source capture independently of native lowering and resident linking.
The native generator reads the owning module's entry directly, so importing
the cache does not replay the compiler or load unrelated extension state.
-/
initialize capturedArtifactExt :
    SimplePersistentEnvExtension Entry (NameMap Fir.Validation.Lcnf.Artifact) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.insert entry.key entry.artifact
    addImportedFn := fun modules => modules.foldl (init := {}) fun state entries =>
      entries.foldl (fun state entry => state.insert entry.key entry.artifact) state
    toArrayFn := fun entries => entries.toArray.qsort fun left right =>
      Name.quickLt left.key right.key
    asyncMode := .sync }

def add (key : Name) (artifact : Fir.Validation.Lcnf.Artifact) : CoreM Unit :=
  modifyEnv fun env => capturedArtifactExt.addEntry env { key, artifact }

/-- Read one entry from a specific imported module without loading all extensions. -/
def getModule? (moduleName key : Name) : CoreM (Option Fir.Validation.Lcnf.Artifact) := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName | return none
  return (capturedArtifactExt.getModuleEntries env moduleIndex).findSome? fun entry =>
    if entry.key == key then some entry.artifact else none

end LeanZipFir.CaptureCache
