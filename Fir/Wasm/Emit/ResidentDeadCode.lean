import Fir.Wasm.Emit.Binary

namespace Fir.Wasm.Emit.ResidentDeadCode

open Fir.Wasm
open Lean

inductive PruneError where
  | invalidInput (error : SymbolicError)
  | unavailableExport (name : Name)
  | missingRoot (name : Name)
  | missingDeclaration (name : Name)
  | invalidCacheIndex (index : Nat)
  | removedCacheReference (name : Name)
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private partial def instructionCalls (pending : List Name) :
    Instruction → List Name
  | .call (.declaration name) => name :: pending
  | .block _ body | .loop _ body => body.foldl instructionCalls pending
  | .ifElse thenBody elseBody =>
      elseBody.foldl instructionCalls (thenBody.foldl instructionCalls pending)
  | _ => pending

private def functionCalls (function : Function) (pending : List Name) : List Name :=
  function.body.foldl instructionCalls pending

private partial def reachableNames (functions : Std.HashMap Name Function)
    (imports : Std.HashSet Name) (pending : List Name)
    (seen : Std.HashSet Name) : Except PruneError (Std.HashSet Name) := do
  match pending with
  | [] => return seen
  | name :: pending =>
      if seen.contains name then
        reachableNames functions imports pending seen
      else if let some function := functions.get? name then
        reachableNames functions imports (functionCalls function pending)
          (seen.insert name)
      else if imports.contains name then
        reachableNames functions imports pending (seen.insert name)
      else
        throw (.missingDeclaration name)

private def remapGlobalIndex (oldInitializers : Array Name)
    (newInitializerIndices : Std.HashMap Name Nat)
    (oldCacheSize newCacheSize index : Nat) : Except PruneError Nat := do
  if index < oldCacheSize then
    let ordinal := index / 2
    let lane := index % 2
    let some name := oldInitializers[ordinal]? |
      throw (.invalidCacheIndex index)
    let some newOrdinal := newInitializerIndices.get? name |
      throw (.removedCacheReference name)
    return 2 * newOrdinal + lane
  return newCacheSize + (index - oldCacheSize)

private partial def remapInstruction (oldInitializers : Array Name)
    (newInitializerIndices : Std.HashMap Name Nat)
    (oldCacheSize newCacheSize : Nat) : Instruction → Except PruneError Instruction
  | .globalGet index kind => do
      return .globalGet (← remapGlobalIndex oldInitializers newInitializerIndices
        oldCacheSize newCacheSize index) kind
  | .globalSet index kind => do
      return .globalSet (← remapGlobalIndex oldInitializers newInitializerIndices
        oldCacheSize newCacheSize index) kind
  | .block label body =>
      return .block label (← body.mapM <| remapInstruction oldInitializers
        newInitializerIndices oldCacheSize newCacheSize)
  | .loop label body =>
      return .loop label (← body.mapM <| remapInstruction oldInitializers
        newInitializerIndices oldCacheSize newCacheSize)
  | .ifElse thenBody elseBody =>
      return .ifElse
        (← thenBody.mapM <| remapInstruction oldInitializers newInitializerIndices
          oldCacheSize newCacheSize)
        (← elseBody.mapM <| remapInstruction oldInitializers newInitializerIndices
          oldCacheSize newCacheSize)
  | instruction => return instruction

private def remapFunction (oldInitializers : Array Name)
    (newInitializerIndices : Std.HashMap Name Nat)
    (oldCacheSize newCacheSize : Nat) (function : Function) :
    Except PruneError Function := do
  let body ← function.body.mapM <|
    remapInstruction oldInitializers newInitializerIndices oldCacheSize newCacheSize
  return { function with body }

/--
Remove declarations with no direct-call path from a public export. Lazy-cache
global indices are compacted and rewritten as one checked operation; resident
globals retain their declaration order after the shorter cache prefix.
-/
def prune (module : Module) (validate : Bool := true) : Except PruneError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  let functionsByName := module.functions.foldl
    (init := Std.HashMap.emptyWithCapacity module.functions.size)
    fun functions function => functions.insert function.name function
  let importedDeclarations := module.imports.foldl
    (init := Std.HashSet.emptyWithCapacity module.imports.size)
    fun declarations import_ =>
      match import_.declaration? with
      | some name => declarations.insert name
      | none => declarations
  for root in module.exports do
    unless functionsByName.contains root do
      throw (.missingRoot root)
  let reachable ← reachableNames functionsByName importedDeclarations
    module.exports.toList
    (Std.HashSet.emptyWithCapacity
      (module.functions.size + importedDeclarations.size))
  let functions := module.functions.filter fun function =>
    reachable.contains function.name
  let initializers := module.initializers.filter reachable.contains
  let newInitializerIndices := initializers.zipIdx.foldl
    (init := Std.HashMap.emptyWithCapacity initializers.size)
    fun indices (name, index) => indices.insert name index
  let oldCacheSize := module.cacheGlobalKinds.size
  let shape : Module := { module with functions, initializers }
  let newCacheSize := shape.cacheGlobalKinds.size
  let functions ← functions.mapM <|
    remapFunction module.initializers newInitializerIndices oldCacheSize newCacheSize
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter fun import_ =>
    match import_.declaration? with
    | some declaration => reachable.contains declaration
    | none => false
  let result : Module := {
    module with
    functions
    initializers
    runtimeOperations
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

/--
Restrict a linked module to an explicit public function surface and remove
everything unreachable from that surface. Requested names must already be
exports: this operation can hide linker exports, but cannot accidentally make
an internal helper public.
-/
def pruneToExports (module : Module) (exports : Array Name) (validate : Bool := true) :
    Except PruneError Module := do
  for name in exports do
    unless module.exports.contains name do
      throw (.unavailableExport name)
  prune { module with exports } validate

private def publicRootName : Name := `residentDeadCodePublicRoot
private def retainedHelperName : Name := `residentDeadCodeRetainedHelper
private def unusedHelperName : Name := `residentDeadCodeUnusedHelper

private def emptyFunction (name : Name) (body : List Instruction := [.ret]) :
    Function := {
  name
  params := #[]
  results := #[]
  locals := #[]
  body }

private def exportRestrictionExample : Module := {
  imports := #[]
  functions := #[
    emptyFunction publicRootName
      [.call (.declaration retainedHelperName), .ret],
    emptyFunction retainedHelperName,
    emptyFunction unusedHelperName]
  exports := #[publicRootName, retainedHelperName, unusedHelperName]
  initializers := #[]
  runtimeOperations := #[] }

#guard match pruneToExports exportRestrictionExample #[publicRootName] with
  | .ok module =>
      module.exports == #[publicRootName] &&
      module.functions.map (fun function => function.name) ==
        #[publicRootName, retainedHelperName]
  | .error _ => false

#guard match pruneToExports exportRestrictionExample #[`notPreviouslyExported] with
  | .error (.unavailableExport name) => name == `notPreviouslyExported
  | _ => false

end Fir.Wasm.Emit.ResidentDeadCode
