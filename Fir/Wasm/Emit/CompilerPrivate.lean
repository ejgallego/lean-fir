module

public import Lean.Compiler.LCNF.Specialize
public import Lean.EnvExtension
import all Lean.Compiler.ClosedTermCache
import all Lean.Compiler.LCNF.Specialize
import all Lean.Compiler.NameDemangling
import all Lean.Environment

public section

namespace Fir.Wasm.Emit.CompilerPrivate

open Lean
open Lean.Compiler

/--
Recover the caller contexts embedded by Lean's generic LCNF specializer.

`LCNF.Specialize.mkSpecDecl` names a specialization by appending `._at_.`,
the declaration currently being compiled, and a `spec_N` component to the
specialized declaration's name. Reuse Lean's demangler primitives so FIR
follows that compiler convention instead of parsing a rendered name.

Candidates are returned from the innermost context out. Callers still require
source-environment validation.
-/
def specializationCallerCandidates (name : Name) : Array Name := Id.run do
  let parts := Lean.Name.Demangle.nameToNameParts name
  let mut candidates : Array Name := #[]
  for index in [:parts.size] do
    unless parts[index]! == .str "_at_" do continue
    let start := index + 1
    let mut stop := start
    while h : stop < parts.size do
      if Lean.Name.Demangle.isSpecIndex parts[stop] then break
      stop := stop + 1
    if stop == start || stop == parts.size then continue
    let candidate := Lean.Name.Demangle.namePartsToName
      (parts.extract start stop)
    unless candidate.isAnonymous || candidates.contains candidate do
      candidates := candidates.push candidate
  return candidates.reverse

/-- Recover the generic declaration before each `._at_.` caller marker. -/
def specializationCalleeCandidates (name : Name) : Array Name := Id.run do
  let parts := Lean.Name.Demangle.nameToNameParts name
  let mut candidates : Array Name := #[]
  for index in [:parts.size] do
    unless parts[index]! == .str "_at_" do continue
    if index == 0 then continue
    let candidate := Lean.Name.Demangle.namePartsToName (parts.extract 0 index)
    unless candidate.isAnonymous || candidates.contains candidate do
      candidates := candidates.push candidate
  return candidates.reverse

private partial def sourceDeclarationAncestor? (sourceNames : Array Name) (name : Name) :
    Option Name :=
  if sourceNames.contains name then
    some name
  else if name.isAnonymous then
    none
  else
    sourceDeclarationAncestor? sourceNames name.getPrefix

private def generatedNameOwnedBy (env : Environment) (sourceRoots : Array Name)
    (name : Name) : Bool := Id.run do
  let callers := specializationCallerCandidates name
  if !callers.isEmpty then
    return callers.any sourceRoots.contains
  let some moduleIndex := env.getModuleIdxFor? name | return false
  let sourceNames := env.header.moduleData[moduleIndex]!.constNames
  return (sourceDeclarationAncestor? sourceNames name).any sourceRoots.contains

/--
Forget precisely the compiler state generated on behalf of the source roots
being recompiled. Upstream never imports a module's own saved LCNF phases while
compiling it; FIR's source view does, so leaving these entries visible makes a
fresh root resolve stale `_redArg`, closed-term, or specialization declarations
from the imported module.

The roots themselves are hidden as well: otherwise recursive calls consult the
imported mono declaration and can be rewritten to a stale `_redArg` child. An
ordinary generated descendant belongs to its nearest real source declaration
in the owning module's `constNames` index. Do not search `env.constants`:
compiler-generated closed terms are themselves environment constants and
would stop that search too early. Do not use a plain name prefix either:
nested source declarations such as a `where` helper compile independently.
Specializations instead use the caller provenance encoded by Lean after
`._at_.`; their apparent module may be the private namespace of the generic
callee, so it is not an ownership constraint.
Unrelated helpers from the same module remain imported. They are ordinary
dependencies of this synthetic unit and can be discovered and compiled in a
later unit. This is intentionally rooted in Lean's generated-name conventions,
not in a textual suffix list.

Candidate mappings come from the selected modules' `extraConstNames` reverse
index and the two compiler caches. This preserves the indexed mainline path;
it does not scan every imported constant mapping.

The synthetic FIR unit cannot reuse an imported specialization or closed-term
cache entry: unlike Lean's native linker, it has no object code containing the
generated declaration named by that entry. A specialization key may also name
a helper owned by an unrelated imported caller. Preserve unrelated declaration
mappings for direct dependencies, but start both caches empty so Lean generates
helpers in the selected source unit and repopulates the caches normally during
that compilation.
-/
def forgetGeneratedCompilerModuleMappings (env : Environment)
    (moduleIndices : Array ModuleIdx) (sourceRoots : Array Name) : Environment :=
  let isOwned := generatedNameOwnedBy env sourceRoots
  let mappings := sourceRoots.foldl (init := env.base.private.const2ModIdx)
    fun mappings name => mappings.erase name
  let mappings := moduleIndices.foldl (init := mappings)
    fun mappings moduleIndex =>
      let moduleData := env.header.moduleData[moduleIndex]!
      moduleData.extraConstNames.foldl
        (fun mappings name =>
          if isOwned name then mappings.erase name else mappings)
        mappings
  let mappings := SMap.fold
    (fun mappings _ name =>
      if isOwned name then mappings.erase name else mappings)
    mappings (LCNF.Specialize.specCacheExt.getState env)
  let oldClosedCache := Lean.closedTermCacheExt.getState env
  let mappings := oldClosedCache.map.foldl (init := mappings)
    fun mappings _ name =>
      if isOwned name then mappings.erase name else mappings
  let env := { env with base.private.const2ModIdx := mappings }
  let env := SimplePersistentEnvExtension.setState
    LCNF.Specialize.specCacheExt env {}
  Lean.closedTermCacheExt.setState (asyncMode := .sync) env {}

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
