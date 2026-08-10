import Fir.Wasm.Emit.ResidentAllocator

namespace Fir.Wasm.Emit.ResidentCache

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

private def objectParam : FVarId := ⟨`object⟩
private def addressLocal : FVarId := ⟨`address⟩
private def flagsLocal : FVarId := ⟨`flags⟩
private def kindLocal : FVarId := ⟨`kind⟩
private def countLocal : FVarId := ⟨`count⟩
private def captureCountLocal : FVarId := ⟨`captureCount⟩
private def descriptorLocal : FVarId := ⟨`descriptor⟩
private def allocationBytesLocal : FVarId := ⟨`allocationBytes⟩
private def allocationEndLocal : FVarId := ⟨`allocationEnd⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | descriptorOverflow (count : Nat)
  | incompatibleMemory
  | malformedLazyCache (name : Name)
  | retainedCacheGlobal (index : Nat)
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

def isCacheSet : RuntimeOp → Bool
  | .cacheSet .. => true
  | _ => false

def cacheSetName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_cache_set_{ordinal}"

private def markPersistentName : Name := `fir_mark_persistent

/--
The compiler-produced `prettyM` cache graph has at most five constructor
object fields. As with resident release, keep a substantially wider explicit
frontier until the symbolic instruction layer grows loops.
-/
def constructorFieldLimit : Nat := 32

private def equalsConst (kind : AbiKind) (value : UInt32) :
    List Instruction :=
  [.i32Const kind value, .i32Eq]

private def trapWhenTrue (condition : List Instruction) : List Instruction :=
  condition ++ [.ifElse [.unreachable] []]

private def requireTrue (condition : List Instruction) : List Instruction :=
  condition ++ [.ifElse [] [.unreachable]]

private def markChild (index : Nat) : List Instruction := [
  .localGet addressLocal,
  .i32Load .tobject (u32 (headerBytes + target.semanticSlotBytes * index)),
  .call (.declaration markPersistentName)]

private def markConstructorFields : List Instruction :=
  (List.range constructorFieldLimit).flatMap fun index =>
    [.i32Const .uint32 (u32 index),
      .localGet countLocal,
      .i32LtU,
      .ifElse (markChild index) []]

private def constructorBody : List Instruction :=
  [.i32Const .uint32 (u32 constructorFieldLimit),
    .localGet countLocal,
    .i32LtU,
    .ifElse [.unreachable] (markConstructorFields ++ [.ret])]

private def descriptorOwnedFields (descriptor : Array AbiKind) :
    List Instruction :=
  descriptor.toList.zipIdx.flatMap fun (kind, index) =>
    if kind.isObjectField then markChild index else []

private partial def descriptorBody
    (descriptors : Array (Array AbiKind)) (index : Nat) :
    Except LinkError (List Instruction) := do
  if h : index < descriptors.size then
    let descriptor := descriptors[index]
    if UInt32.size ≤ index || UInt32.size ≤ descriptor.size then
      throw (.descriptorOverflow (max index descriptor.size))
    let rest ← descriptorBody descriptors (index + 1)
    return (
      [.localGet descriptorLocal] ++
      equalsConst .uint32 (u32 index) ++
      [.ifElse
        ([.localGet captureCountLocal] ++
          equalsConst .uint32 (u32 descriptor.size) ++
          [.ifElse
            (descriptorOwnedFields descriptor ++ [.ret])
            [.unreachable]])
        rest])
  else
    return [.unreachable]

private def ownedBody (descriptors : Array (Array AbiKind)) :
    Except LinkError (List Instruction) := do
  let closureBody ← descriptorBody descriptors 0
  return (
    [.localGet kindLocal] ++
    equalsConst .uint32 ObjectKind.constructor.code ++
    [.ifElse
      constructorBody
      ([.localGet kindLocal] ++
        equalsConst .uint32 ObjectKind.closure.code ++
        [.ifElse closureBody [.ret]])])

private def canonicalFreedBody : List Instruction :=
  requireTrue (
    [.localGet kindLocal] ++
      equalsConst .uint32 ObjectKind.freed.code) ++
    requireTrue (
      [.localGet flagsLocal] ++ equalsConst .uint32 0) ++
    requireTrue (
      [.localGet addressLocal,
        .i32Load .uint32 (u32 headerRefCountOffset)] ++
        equalsConst .uint32 0) ++
    (List.range 4).flatMap fun index =>
      requireTrue (
        [.localGet addressLocal,
          .i32Load .uint32 (u32 (headerAux0Offset + 4 * index))] ++
          equalsConst .uint32 0) ++
    [.localGet addressLocal,
      .i32Load .uint32 (u32 headerAllocationBytesOffset),
      .localSet allocationBytesLocal] ++
    trapWhenTrue [
      .localGet allocationBytesLocal,
      .i32Const .uint32 (u32 headerBytes),
      .i32LtU] ++
    trapWhenTrue [
      .localGet allocationBytesLocal,
      .i32Const .uint32 (u32 (target.heapAlignment - 1)),
      .i32And] ++
    [.localGet addressLocal,
      .localGet allocationBytesLocal,
      .i32Add,
      .localSet allocationEndLocal] ++
    trapWhenTrue [
      .localGet allocationEndLocal,
      .localGet addressLocal,
      .i32LtU] ++
    trapWhenTrue [
      .call (.declaration ResidentAllocator.frontierName),
      .localGet allocationEndLocal,
      .i32LtU] ++
    [.ret]

private def liveBody (descriptors : Array (Array AbiKind)) :
    Except LinkError (List Instruction) := do
  let owned ← ownedBody descriptors
  return (
    [.localGet flagsLocal,
      .i32Const .uint32 persistentFlag,
      .i32And] ++
    equalsConst .uint32 persistentFlag ++
    [.ifElse
      [.ret]
      (requireTrue (
          [.localGet flagsLocal] ++ equalsConst .uint32 liveFlag) ++
        [.localGet addressLocal,
          .i32Load .uint32 (u32 headerKindOffset),
          .localSet kindLocal,
          .localGet addressLocal,
          .i32Load .uint32 (u32 headerAux1Offset),
          .localSet countLocal,
          .localGet addressLocal,
          .i32Load .uint32 (u32 headerAux2Offset),
          .localSet captureCountLocal,
          .localGet addressLocal,
          .i32Load .uint32 (u32 headerAux3Offset),
          .localSet descriptorLocal,
          .localGet addressLocal,
          .i32Const .uint32 (liveFlag + persistentFlag),
          .i32Store .uint32 (u32 headerFlagsOffset),
          .localGet addressLocal,
          .i32Const .uint32 0,
          .i32Store .uint32 (u32 headerRefCountOffset)] ++ owned)])

private def alignedBody (descriptors : Array (Array AbiKind)) :
    Except LinkError (List Instruction) := do
  let live ← liveBody descriptors
  return (
    [.localGet objectParam,
      .i32Const .uint32 0,
      .i32Add,
      .localSet addressLocal,
      .localGet addressLocal,
      .i32Load .uint32 (u32 headerFlagsOffset),
      .localSet flagsLocal,
      .localGet flagsLocal,
      .i32Const .uint32 liveFlag,
      .i32And] ++
    equalsConst .uint32 liveFlag ++
    [.ifElse
      live
      ([.localGet addressLocal,
        .i32Load .uint32 (u32 headerKindOffset),
        .localSet kindLocal] ++ canonicalFreedBody)])

private def markPersistentFunction
    (descriptors : Array (Array AbiKind)) :
    Except LinkError Function := do
  if UInt32.size ≤ descriptors.size then
    throw (.descriptorOverflow descriptors.size)
  let aligned ← alignedBody descriptors
  return {
    name := markPersistentName
    params := #[(objectParam, .tobject)]
    results := #[]
    locals := #[
      (addressLocal, .uint32),
      (flagsLocal, .uint32),
      (kindLocal, .uint32),
      (countLocal, .uint32),
      (captureCountLocal, .uint32),
      (descriptorLocal, .uint32),
      (allocationBytesLocal, .uint32),
      (allocationEndLocal, .uint32)]
    body := [
      .localGet objectParam,
      .i32Const .uint32 1,
      .i32And,
      .ifElse
        [.ret]
        (trapWhenTrue [
            .localGet objectParam,
            .i32Const .uint32 (u32 heapBase),
            .i32LtU] ++
          trapWhenTrue [
            .localGet objectParam,
            .i32Const .uint32 (u32 (target.heapAlignment - 1)),
            .i32And] ++ aligned)] }

private def cacheSetFunction (ordinal : Nat) (operation : RuntimeOp) :
    Except LinkError Function := do
  unless operation.abiWellFormed do
    throw .unsupportedOperation
  let .cacheSet _ value := operation | throw .unsupportedOperation
  let persist :=
    if value.isObjectLike then
      [.localGet objectParam, .call (.declaration markPersistentName)]
    else
      []
  return {
    name := cacheSetName ordinal
    params := #[(objectParam, value)]
    results := #[value]
    locals := #[]
    body := persist ++ [.localGet objectParam, .ret] }

private partial def rewriteInstruction
    (rewrites : List (RuntimeOp × Name)) : Instruction → Instruction
  | .call (.runtime candidate) =>
      match rewrites.find? (·.1 == candidate) with
      | some (_, name) => .call (.declaration name)
      | none => .call (.runtime candidate)
  | .block label body =>
      .block label (body.map (rewriteInstruction rewrites))
  | .ifElse thenBody elseBody =>
      .ifElse
        (thenBody.map (rewriteInstruction rewrites))
        (elseBody.map (rewriteInstruction rewrites))
  | instruction => instruction

private def rewriteFunction (rewrites : List (RuntimeOp × Name))
    (function : Function) : Function :=
  { function with body := function.body.map (rewriteInstruction rewrites) }

private def reserved (module : Module) (name : Name) : Bool :=
  module.imports.any (·.declaration? == some name) ||
    module.functions.any (·.name == name) ||
    module.exports.contains name

/--
Internalize lazy-cache publication. The generated miss path already stores the
physical result and initialized flag in module globals; these helpers replace
the host call that marks the complete reachable object graph persistent and
returns the physical lane unchanged.
-/
def internalizeCacheSets (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let operations := module.runtimeOperations.filter isCacheSet
  if operations.isEmpty then
    return module
  let needsPersistence := operations.any fun operation =>
    match operation with
    | .cacheSet _ value => value.isObjectLike
    | _ => false
  if needsPersistence &&
      !module.functions.any (·.name == ResidentAllocator.frontierName) then
    throw .missingAllocator
  let rewrites := operations.toList.zipIdx.map fun (operation, ordinal) =>
    (operation, cacheSetName ordinal)
  let reservedNames :=
    (if needsPersistence then [markPersistentName] else []) ++ rewrites.map (·.2)
  if let some name := reservedNames.find? (reserved module) then
    throw (.reservedDeclaration name)
  let wrappers ← operations.toList.zipIdx.mapM fun (operation, ordinal) =>
    cacheSetFunction ordinal operation
  let persistence : Array Function ←
    if needsPersistence then
      pure #[← markPersistentFunction module.closureDescriptors]
    else
      pure #[]
  let functions :=
    (module.functions.map (rewriteFunction rewrites)) ++
      persistence ++ wrappers.toArray
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
  let exports := rewrites.foldl (init := module.exports)
    fun exports (_, name) => Fir.Wasm.addUnique exports name
  let result := {
    module with
    imports
    functions
    exports
    runtimeOperations }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

/-!
Rewindable consumers cannot retain a lazy singleton allocated above their
scratch checkpoint. Before resident linking, the compiler's exact cache
sequence can instead be reduced to a direct call: each use receives a fresh
closed value in the current arena, so no private global publishes a scratch
address across calls.

This transform is deliberately fail-closed. It recognizes only the sequence
fixed by `Fir.Wasm.compileLetValue_fap_cached`, rejects every residual cache
global or `cacheSet`, and shifts pre-existing resident globals down after the
cache prefix is removed.
-/

mutual

private partial def eliminateLazyCacheInstructions
    (initializers : Array Name) (cacheGlobalCount : Nat) :
    List Instruction → Except LinkError (List Instruction)
  | .globalGet flagIndex .uint32 :: .ifElse [] miss ::
      .globalGet valueIndex resultKind :: rest => do
      if flagIndex < cacheGlobalCount then
        match miss with
        | [.call (.declaration target),
            .call (.runtime (.cacheSet cacheTarget cacheKind)),
            .globalSet storedValueIndex storedKind,
            .i32Const .uint32 initialized,
            .globalSet storedFlagIndex .uint32] =>
            let some initializer := initializers[flagIndex / 2]? |
              throw (.malformedLazyCache target)
            unless flagIndex % 2 == 0 && valueIndex == flagIndex + 1 &&
                valueIndex < cacheGlobalCount && initializer == target &&
                target == cacheTarget && resultKind == cacheKind &&
                valueIndex == storedValueIndex && resultKind == storedKind &&
                flagIndex == storedFlagIndex && initialized == 1 do
              throw (.malformedLazyCache target)
            return .call (.declaration target) ::
              .call (.runtime (.cacheSet target resultKind)) ::
              (← eliminateLazyCacheInstructions initializers cacheGlobalCount rest)
        | _ => throw (.retainedCacheGlobal flagIndex)
      else
        return .globalGet (flagIndex - cacheGlobalCount) .uint32 ::
          (← eliminateLazyCacheInstructions initializers cacheGlobalCount
            (.ifElse [] miss :: .globalGet valueIndex resultKind :: rest))
  | instruction :: rest =>
      return (← eliminateLazyCacheInstruction initializers cacheGlobalCount instruction) ::
        (← eliminateLazyCacheInstructions initializers cacheGlobalCount rest)
  | [] => return []

private partial def eliminateLazyCacheInstruction
    (initializers : Array Name) (cacheGlobalCount : Nat) :
    Instruction → Except LinkError Instruction
  | .globalGet index kind =>
      if index < cacheGlobalCount then
        throw (.retainedCacheGlobal index)
      else
        return .globalGet (index - cacheGlobalCount) kind
  | .globalSet index kind =>
      if index < cacheGlobalCount then
        throw (.retainedCacheGlobal index)
      else
        return .globalSet (index - cacheGlobalCount) kind
  | .block label body =>
      return .block label
        (← eliminateLazyCacheInstructions initializers cacheGlobalCount body)
  | .loop label body =>
      return .loop label
        (← eliminateLazyCacheInstructions initializers cacheGlobalCount body)
  | .ifElse thenBody elseBody =>
      return .ifElse
        (← eliminateLazyCacheInstructions initializers cacheGlobalCount thenBody)
        (← eliminateLazyCacheInstructions initializers cacheGlobalCount elseBody)
  | instruction => return instruction

end

/--
Remove compiler-generated lazy singleton state so a consumer may rewind its
allocation arena after every public call. Each use constructs a fresh graph
and routes it through the existing recursive cache-publication helper, thereby
preserving the persistent ownership contract already assumed by final LCNF
without retaining a module-global root. Run this before cache-set
internalization; no initializer or cache global remains.
-/
def eliminateLazyInitializers (module : Module) : Except LinkError Module := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw (.invalidInput error)
  let cacheGlobalCount := module.cacheGlobalKinds.size
  let functions ← module.functions.mapM fun function => do
    let body ← eliminateLazyCacheInstructions module.initializers
      cacheGlobalCount function.body
    return { function with body }
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let result := {
    module with
    functions
    initializers := #[]
    runtimeOperations
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports }
  match Fir.Wasm.validateModule result with
  | .ok () => return result
  | .error error => throw (.invalidOutput error)

def exampleDescriptors : Array (Array AbiKind) :=
  #[#[.tobject, .uint8, .tobject]]

def exampleOperation : RuntimeOp :=
  .cacheSet `residentCacheExample .object

def exampleCaller : Function := {
  name := `resident_cache_set
  params := #[(objectParam, .object)]
  results := #[.object]
  locals := #[]
  body := [
    .localGet objectParam,
    .call (.runtime exampleOperation),
    .ret] }

def exampleModule : Module := {
  imports := #[Fir.Wasm.runtimeImport 0 exampleOperation]
  functions := #[exampleCaller]
  exports := #[exampleCaller.name]
  initializers := #[]
  runtimeOperations := #[exampleOperation]
  closureDescriptors := exampleDescriptors }

def residentExampleModule : Except String Module := do
  let allocated ← ResidentAllocator.install exampleModule
    |>.mapError fun error => s!"allocator: {repr error}"
  internalizeCacheSets allocated
    |>.mapError fun error => s!"cache: {repr error}"

private def lazyInitializerName : Name := `residentLazyInitializer
private def lazyCallerName : Name := `residentLazyCaller
private def lazyValueLocal : FVarId := ⟨`lazyValue⟩

private def lazyInitializer : Function := {
  name := lazyInitializerName
  params := #[]
  results := #[.uint32]
  locals := #[]
  body := [.i32Const .uint32 37, .ret] }

private def lazyCaller : Function := {
  name := lazyCallerName
  params := #[]
  results := #[.uint32]
  locals := #[(lazyValueLocal, .uint32)]
  body := [
    .globalGet 0 .uint32,
    .ifElse [] [
      .call (.declaration lazyInitializerName),
      .call (.runtime (.cacheSet lazyInitializerName .uint32)),
      .globalSet 1 .uint32,
      .i32Const .uint32 1,
      .globalSet 0 .uint32],
    .globalGet 1 .uint32,
    .localSet lazyValueLocal,
    .globalGet 2 .uint32,
    .ret] }

private def lazyModule : Module := {
  imports := #[Fir.Wasm.runtimeImport 0
    (.cacheSet lazyInitializerName .uint32)]
  functions := #[lazyInitializer, lazyCaller]
  exports := #[lazyCallerName]
  initializers := #[lazyInitializerName]
  runtimeOperations := #[.cacheSet lazyInitializerName .uint32]
  globals := #[{ kind := .uint32, init := .i32 91 }] }

private def eliminatedLazyCallerBody : List Instruction := [
  .call (.declaration lazyInitializerName),
  .call (.runtime (.cacheSet lazyInitializerName .uint32)),
  .localSet lazyValueLocal,
  .globalGet 0 .uint32,
  .ret]

#guard match eliminateLazyInitializers lazyModule with
  | .ok module =>
      module.initializers.isEmpty &&
      module.runtimeOperations == #[.cacheSet lazyInitializerName .uint32] &&
      module.imports.size == 1 && module.globals == lazyModule.globals &&
      (module.functions[1]?.map (·.body) == some eliminatedLazyCallerBody) &&
      (Fir.Wasm.validateModule module).isOk
  | .error _ => false

private def malformedLazyCaller : Function := {
  lazyCaller with
  body := [
    .globalGet 0 .uint32,
    .ifElse [] [
      .call (.declaration lazyInitializerName),
      .call (.runtime (.cacheSet lazyInitializerName .uint32)),
      .globalSet 1 .uint32,
      .i32Const .uint32 0,
      .globalSet 0 .uint32],
    .globalGet 1 .uint32,
    .localSet lazyValueLocal,
    .globalGet 2 .uint32,
    .ret] }

#guard match eliminateLazyInitializers {
    lazyModule with
    functions := lazyModule.functions.map fun function =>
      if function.name == lazyCallerName then
        malformedLazyCaller
      else function } with
  | .error (.malformedLazyCache name) => name == lazyInitializerName
  | _ => false

def manifest : Json :=
  Json.mkObj [
    ("entry", exampleCaller.name.toString),
    ("value", "object"),
    ("constructorFieldLimit", constructorFieldLimit),
    ("status", "generation-only; W6 cache-persistence contract proof pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      module.exports.contains exampleCaller.name &&
      module.exports.contains (cacheSetName 0) &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentCache
