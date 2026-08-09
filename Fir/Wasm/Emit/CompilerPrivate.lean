module

public import Lean.Compiler.LCNF.Specialize
public import Lean.EnvExtension
import all Lean.Compiler.LCNF.Specialize
import all Lean.Environment

public section

namespace Fir.Wasm.Emit.CompilerPrivate

open Lean
open Lean.Compiler

/--
Forget imported specialization-name mappings inside an already isolated
compiler environment.  Lean can then rebuild those private helpers from the
source declarations visible to the ordinary LCNF pipeline.
-/
def clearSpecializationCache (env : Environment) : Environment :=
  SimplePersistentEnvExtension.setState LCNF.Specialize.specCacheExt env {}

/-- Match `leanir`'s target-module import phase without exposing Lean's private
`ImportState.moduleNameMap` field to the ordinary FIR source module. -/
def setTargetRuntimePhase (state : ImportState) (moduleName : Name) : ImportState :=
  { state with moduleNameMap := state.moduleNameMap.modify moduleName fun data =>
      if data.module == moduleName then { data with irPhases := .runtime } else data }

/-- Match `leanir`'s direct-import header after privately importing its target
module. Lean keeps the nested environment fields private, so this small bridge
is kept beside the specialization-cache bridge above. -/
def setTargetDirectImports (environment : Environment) (moduleIndex : ModuleIdx) :
    Option Environment := do
  let moduleData ← environment.header.moduleData[moduleIndex]?
  return { environment with base.private.header.imports := moduleData.imports }

end Fir.Wasm.Emit.CompilerPrivate
