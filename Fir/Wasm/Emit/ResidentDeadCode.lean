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

private def addUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

private partial def instructionCalls (names : Array Name) :
    Instruction → Array Name
  | .call (.declaration name) => addUnique names name
  | .block _ body | .loop _ body => body.foldl instructionCalls names
  | .ifElse thenBody elseBody =>
      elseBody.foldl instructionCalls (thenBody.foldl instructionCalls names)
  | _ => names

private def functionCalls (function : Function) : Array Name :=
  function.body.foldl instructionCalls #[]

private partial def reachableNames (module : Module) (pending : List Name)
    (seen : Array Name := #[]) : Except PruneError (Array Name) := do
  match pending with
  | [] => return seen
  | name :: pending =>
      if seen.contains name then
        reachableNames module pending seen
      else if let some function := module.functions.find? (·.name == name) then
        reachableNames module ((functionCalls function).toList ++ pending)
          (seen.push name)
      else if module.imports.any (·.declaration? == some name) then
        reachableNames module pending (seen.push name)
      else
        throw (.missingDeclaration name)

private def remapGlobalIndex (oldInitializers newInitializers : Array Name)
    (oldCacheSize newCacheSize index : Nat) : Except PruneError Nat := do
  if index < oldCacheSize then
    let ordinal := index / 2
    let lane := index % 2
    let some name := oldInitializers[ordinal]? |
      throw (.invalidCacheIndex index)
    let some newOrdinal := newInitializers.findIdx? (· == name) |
      throw (.removedCacheReference name)
    return 2 * newOrdinal + lane
  return newCacheSize + (index - oldCacheSize)

private partial def remapInstruction (oldInitializers newInitializers : Array Name)
    (oldCacheSize newCacheSize : Nat) : Instruction → Except PruneError Instruction
  | .globalGet index kind => do
      return .globalGet (← remapGlobalIndex oldInitializers newInitializers
        oldCacheSize newCacheSize index) kind
  | .globalSet index kind => do
      return .globalSet (← remapGlobalIndex oldInitializers newInitializers
        oldCacheSize newCacheSize index) kind
  | .block label body =>
      return .block label (← body.mapM <| remapInstruction oldInitializers
        newInitializers oldCacheSize newCacheSize)
  | .loop label body =>
      return .loop label (← body.mapM <| remapInstruction oldInitializers
        newInitializers oldCacheSize newCacheSize)
  | .ifElse thenBody elseBody =>
      return .ifElse
        (← thenBody.mapM <| remapInstruction oldInitializers newInitializers
          oldCacheSize newCacheSize)
        (← elseBody.mapM <| remapInstruction oldInitializers newInitializers
          oldCacheSize newCacheSize)
  | instruction => return instruction

private def remapFunction (oldInitializers newInitializers : Array Name)
    (oldCacheSize newCacheSize : Nat) (function : Function) :
    Except PruneError Function := do
  let body ← function.body.mapM <|
    remapInstruction oldInitializers newInitializers oldCacheSize newCacheSize
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
  for root in module.exports do
    unless module.functions.any (·.name == root) do
      throw (.missingRoot root)
  let reachable ← reachableNames module module.exports.toList
  let functions := module.functions.filter (reachable.contains ·.name)
  let initializers := module.initializers.filter reachable.contains
  let oldCacheSize := module.cacheGlobalKinds.size
  let shape : Module := { module with functions, initializers }
  let newCacheSize := shape.cacheGlobalKinds.size
  let functions ← functions.mapM <|
    remapFunction module.initializers initializers oldCacheSize newCacheSize
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
