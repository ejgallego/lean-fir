import Fir.Wasm.Emit.ResidentLinker

namespace Fir.Wasm.Emit.ResidentFloatSource

open Lean

/-!
# Source-compiled Float construction

Lean exposes `Float.ofNat` and `Float.ofScientific` as ordinary definitions.
FIR therefore captures their real final-LCNF bodies and closes the resulting
generic Nat/Int/Float frontier with the same resident families used by any
other closed application.  No declaration-named decimal conversion shim is
part of this path.
-/

def entries : Array Name := ExternalRuntime.sourceDeclarations

def facadeEntries : Array Name :=
  entries.map Fir.Wasm.Emit.BitExactFloat.facadeName

def publicExports : Array Name := entries ++ facadeEntries

def capture : CoreM Fir.Validation.Lcnf.Artifact :=
  Source.compileEntryIndividuallyInternalized entries[0]!
    ResidentLinker.closedApplicationRetainedExternalNames

/-- Compile the upstream definitions into a self-contained, module-memory
Wasm artifact. Both ordinary `f64` entries and their integer-lane bit-exact
facades are exported together with the resident arena surface. -/
def compile : CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let source ← capture
  Source.compileModuleArtifactWithExports source entries fun module =>
    ResidentLinker.linkModule
      (ResidentLinker.closedApplicationAvailablePolicy module publicExports)
      module

#guard entries == #[`Float.ofNat, `Float.ofScientific]

#guard publicExports == entries ++ entries.map
  Fir.Wasm.Emit.BitExactFloat.facadeName

end Fir.Wasm.Emit.ResidentFloatSource
