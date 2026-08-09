import Fir.Wasm.Emit.Source
import Fir.Wasm.PrettyFormat

namespace Fir.Wasm.Emit.PrettyFormat

open Lean
open Fir.Wasm.Emit.Source

/-- The only compiler-generated helper deliberately retained during source internalization. -/
def weakMonadInhabitedName : String := "instInhabitedOfMonad._redArg"

/--
Capture and internalize a locally expanded Format facade.

The captured final LCNF remains untouched. Its generic `tobject` results cross
ordinary object-family call sites through the same representation-compatible
path used by upstream Lean's final-LCNF emitter.
-/
def compileSource (entry : Name) :
    CoreM (Except Source.CompileError Fir.Validation.Lcnf.Artifact) := do
  return .ok (← compileEntrySeparatelyInternalized entry
    #[weakMonadInhabitedName])

/-- Capture, internalize, lower, and encode a locally expanded Format facade. -/
def compileModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let source ← compileSource entry
  match source with
  | .ok source => compileModuleArtifact source
  | .error error => return .error error

end Fir.Wasm.Emit.PrettyFormat
