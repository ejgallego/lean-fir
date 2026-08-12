module

public import Lean.Compiler.LCNF.Specialize
public import Lean.EnvExtension
import all Lean.Compiler.ClosedTermCache
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

/--
Forget imported mappings from erased closed terms to generated names. Reusing
these mappings while recompiling imported source can pair a new typed LCNF
binding with a closed declaration generated in the original module unit.
-/
def clearClosedTermCache (env : Environment) : Environment :=
  Lean.closedTermCacheExt.setState (asyncMode := .sync) env {}

/--
Treat imported generated closed terms and specializations as local names during
source recompilation. Their original module indices make LCNF phase lookup
prefer the imported signature over the freshly generated declaration with the
same name. Ordinary source declarations keep their module mapping. Use each
selected module's `extraConstNames`, the environment's reverse index for
compiler auxiliaries, instead of scanning every imported constant mapping.
-/
def forgetGeneratedCompilerModuleMappings (env : Environment)
    (moduleIndices : Array ModuleIdx) : Environment :=
  let closedNames := (Lean.closedTermCacheExt.getState env).constNames
  let specializationCache := LCNF.Specialize.specCacheExt.getState env
  let originalMappings := env.base.private.const2ModIdx
  let selectedModules := moduleIndices.foldl
    (init := Std.HashSet.emptyWithCapacity moduleIndices.size)
    fun modules moduleIndex => modules.insert moduleIndex
  let mappings := moduleIndices.foldl (init := env.base.private.const2ModIdx)
    fun mappings moduleIndex =>
      let moduleData := env.header.moduleData[moduleIndex]!
      moduleData.extraConstNames.foldl
        (fun mappings name =>
          if name.toString.contains "._closed_" then mappings.erase name else mappings)
        mappings
  let mappings := closedNames.foldl
    (fun mappings name =>
      match originalMappings[name]? with
      | some moduleIndex =>
          if selectedModules.contains moduleIndex then mappings.erase name else mappings
      | none => mappings) mappings
  let mappings := SMap.fold
    (fun mappings _ name =>
      match originalMappings[name]? with
      | some moduleIndex =>
          if selectedModules.contains moduleIndex then mappings.erase name else mappings
      | none => mappings) mappings specializationCache
  { env with base.private.const2ModIdx := mappings }

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
