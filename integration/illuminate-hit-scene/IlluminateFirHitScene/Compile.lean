import Fir.Wasm.Emit.ResidentLinker
import Illuminate.Diagram.HitScene

namespace IlluminateFirHitScene.Compile

open Lean

/-- The real prepared hit-scene query requested by Illuminate. -/
def entry : Name := ``Illuminate.HitScene.query

private def residentExternalNames : Array String := #[
  "Float.add",
  "Float.mul",
  "Float.neg",
  "Float.div",
  "Float.decLt",
  "Float.abs",
  "Float.sub",
  "Float.decLe",
  "Float.sqrt",
  "Float.sin",
  "Float.cos",
  "Float.atan2",
  "Float.floor",
  "Float.scaleB",
  "Float.acos",
  "Float.beq",
  "Float.cbrt",
  "Array.usize",
  "Array.uget",
  "Array.size",
  "Array.get!Internal",
  "USize.decLt",
  "USize.add",
  "Nat.decEq",
  "Nat.mod",
  "Nat.add",
  "Nat.decLt",
  "Nat.mul",
  "Nat.sub",
  "Nat.log2",
  "Nat.shiftLeft",
  "Nat.pow",
  "Nat.div",
  "Nat.shiftRight",
  "Int.ofNat",
  "Int.neg",
  "Int.mul",
  "Int.sub",
  "Int.add",
  "UInt64.ofNat",
  "UInt64.toFloat"]

/--
Capture the real entry and recursively discovered dependencies in their
ordinary separately compiled final-LCNF units. This preserves the module-level
closed-term boundary used by Lean's own native emitter.
-/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntryModuleWiseInternalized entry residentExternalNames

/--
Diagnostic single-unit capture. Large imported closures may generate different
closed-term sharing when all roots are recompiled as one synthetic unit.
-/
def captureSourceSingleUnit : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntryFinalCapturedInternalized entry

/-- Lower the unmodified source closure before resident runtime linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  Fir.Wasm.Emit.Source.compileModuleArtifact source

end IlluminateFirHitScene.Compile
