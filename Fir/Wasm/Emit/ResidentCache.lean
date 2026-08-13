import Fir.Wasm.Emit.ResidentAllocator
import Fir.Wasm.Emit.ResidentConstructor

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
  | malformedAllocator
  | malformedLazyCache (name : Name)
  | invalidInitializerSignature (name : Name)
  | unsupportedStaticInitializer (name : Name)
  | staticImageOverflow (name : Name)
  | retainedCacheGlobal (index : Nat)
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

private def wordLE (value : UInt32) : Array UInt8 :=
  #[value.toUInt8,
    (value >>> (8 : UInt32)).toUInt8,
    (value >>> (16 : UInt32)).toUInt8,
    (value >>> (24 : UInt32)).toUInt8]

private def staticFieldAccepted : AbiKind × UInt32 → Bool
  | (.erased, value) => value == 0
  | (.tagged, value) | (.tobject, value) => value.toNat % 2 == 1
  | _ => false

private partial def staticConstructorBody?
    (instructions : List Instruction)
    (fields : Array (AbiKind × UInt32) := #[]) :
    Option (Lean.Compiler.LCNF.CtorInfo × Array (AbiKind × UInt32) × AbiKind) :=
  match instructions with
  | .i32Const kind value :: rest =>
      staticConstructorBody? rest (fields.push (kind, value))
  | .call (.runtime (.allocCtor info kinds result)) :: [.ret] =>
      if fields.map (·.1) == kinds then some (info, fields, result) else none
  | _ => none

private def staticConstructorBytes
    (info : Lean.Compiler.LCNF.CtorInfo)
    (fields : Array (AbiKind × UInt32)) : Array UInt8 :=
  let layout := ConstructorLayout.ofInfo info
  wordLE ObjectKind.constructor.code ++
    wordLE (liveFlag + persistentFlag) ++
    wordLE 0 ++
    wordLE (u32 layout.allocationBytes) ++
    wordLE (u32 info.cidx) ++
    wordLE (u32 info.size) ++
    wordLE (u32 info.usize) ++
    wordLE (u32 info.ssize) ++
    fields.foldl (init := #[]) fun bytes (_, value) =>
      bytes ++ wordLE value ++ #[0, 0, 0, 0]

private def nextStaticAddress (module : Module) : Nat :=
  let dataEnd := module.dataSegments.foldl (init := 0) fun end_ segment =>
    max end_ (segment.offset.toNat + segment.bytes.size)
  align8 (max heapBase dataEnd)

/--
Materialize one explicitly selected compiler lazy initializer when its entire
body is a single immutable constructor whose fields are immediate constants.
The transform is intentionally narrow and fail-closed: it does not execute
Lean code, chase calls, accept heap pointers, or infer purity.

The original lazy cache protocol remains in place. Its flag is still zero at
instantiation and first ordinary access publishes the preverified image
address. The initializer itself becomes a constant-address function, so that
first access performs no allocation.

This is an experimental proof of the Wasm image/allocator mechanism. Before
production use, replace its local syntactic classifier with Lean's upstream
`SimpleGroundExpr` result from final LCNF and retain only the W6-layout
serialization performed by the FIR backend.
-/
def materializeClosedConstructor (module : Module) (initializer : Name)
    (validate : Bool := true) : Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.initializers.contains initializer do
    throw (.unsupportedStaticInitializer initializer)
  let some function := module.functions.find? (·.name == initializer) |
    throw (.unsupportedStaticInitializer initializer)
  unless function.params.isEmpty && function.results.size == 1 &&
      function.locals.isEmpty do
    throw (.unsupportedStaticInitializer initializer)
  let some (info, fields, resultKind) := staticConstructorBody? function.body |
    throw (.unsupportedStaticInitializer initializer)
  unless info.usize == 0 && info.ssize == 0 && info.size == fields.size &&
      fields.all staticFieldAccepted && function.results == #[resultKind] &&
      resultKind.isObjectLike do
    throw (.unsupportedStaticInitializer initializer)
  let memory ← match module.memory with
    | none => pure ResidentRuntime.residentMemory
    | some memory =>
        unless memory == ResidentRuntime.residentMemory do
          throw .incompatibleMemory
        pure memory
  let address := nextStaticAddress module
  let bytes := staticConstructorBytes info fields
  unless address + bytes.size < UInt32.size &&
      address + bytes.size ≤ memory.pagesMin.toNat * 65536 do
    throw (.staticImageOverflow initializer)
  let addressWord := u32 address
  let functions := module.functions.map fun candidate =>
    if candidate.name == initializer then
      { candidate with body := [.i32Const resultKind addressWord, .ret] }
    else candidate
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let result : Module := {
    module with
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    functions
    runtimeOperations
    memory := some memory
    dataSegments := module.dataSegments.push { offset := addressWord, bytes } }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

def isCacheSet : RuntimeOp → Bool
  | .cacheSet .. => true
  | _ => false

def cacheSetName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_cache_set_{ordinal}"

private def markPersistentName : Name := `fir_mark_persistent

/-- Diagnostic-only entry that unsafely forces every compiler lazy cache. -/
def unsafeEagerPersistentInitializerName : Name :=
  `fir_initialize_persistent_caches

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

private def cacheSetFunction
    (ordinal : Nat) (operation : RuntimeOp)
    (persistentFloorIndex : Option Nat := none) :
    Except LinkError Function := do
  unless operation.abiWellFormed do
    throw .unsupportedOperation
  let .cacheSet _ value := operation | throw .unsupportedOperation
  let persist :=
    if value.isObjectLike then
      [.localGet objectParam, .call (.declaration markPersistentName)]
    else
      []
  let retainFloor := persistentFloorIndex.map (fun index => [
    .call (.declaration ResidentAllocator.frontierName),
    .globalSet index .uint32]) |>.getD []
  return {
    name := cacheSetName ordinal
    params := #[(objectParam, value)]
    results := #[value]
    locals := #[]
    body := persist ++ retainFloor ++ [.localGet objectParam, .ret] }

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

private def retainedObjectCache
    (module : Module) (operation : RuntimeOp) : Bool :=
  match operation with
  | .cacheSet initializer kind =>
      kind.isObjectLike && module.initializers.contains initializer
  | _ => false

private def allocatorFrontierIndex? (module : Module) : Option Nat := do
  let function ← module.functions.find? (·.name == ResidentAllocator.frontierName)
  match function.body with
  | [.globalGet index .uint32, .ret] => some index
  | _ => none

private def installCacheAwareRewind
    (module : Module) (persistentFloorIndex : Nat) : Except LinkError Module := do
  let some frontierIndex := allocatorFrontierIndex? module |
    throw .malformedAllocator
  unless module.functions.any (·.name == ResidentAllocator.rewindName) do
    throw .malformedAllocator
  return {
    module with
    functions := module.functions.map fun function =>
      if function.name == ResidentAllocator.rewindName then
        ResidentAllocator.cacheAwareRewindFunction
          frontierIndex persistentFloorIndex
      else
        function }

/--
Internalize lazy-cache publication. The generated miss path already stores the
physical result and initialized flag in module globals; these helpers replace
the host call that marks the complete reachable object graph persistent and
returns the physical lane unchanged.
-/
def internalizeCacheSets (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
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
  let needsPersistentFloor := operations.any (retainedObjectCache module)
  let persistentFloorIndex :=
    if needsPersistentFloor then
      some (module.cacheGlobalKinds.size + module.globals.size)
    else
      none
  let persistentFloorInitial ← match persistentFloorIndex with
    | none => pure none
    | some _ =>
        let some frontier := ResidentAllocator.initialFrontier? module |
          throw (.staticImageOverflow `persistentFloor)
        pure (some frontier)
  let rewrites := operations.toList.zipIdx.map fun (operation, ordinal) =>
    (operation, cacheSetName ordinal)
  let reservedNames :=
    (if needsPersistence then [markPersistentName] else []) ++ rewrites.map (·.2)
  if let some name := reservedNames.find? (reserved module) then
    throw (.reservedDeclaration name)
  let wrappers ← operations.toList.zipIdx.mapM fun (operation, ordinal) =>
    cacheSetFunction ordinal operation <|
      if retainedObjectCache module operation then persistentFloorIndex else none
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
    runtimeOperations
    globals := match persistentFloorInitial with
      | some frontier => module.globals.push {
          kind := .uint32
          init := .i32 frontier }
      | none => module.globals }
  let result ← match persistentFloorIndex with
    | some index => installCacheAwareRewind result index
    | none => pure result
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

private def persistentCacheMiss
    (ordinal : Nat) (initializer : Name) (kind : AbiKind) : List Instruction := [
  .call (.declaration initializer),
  .call (.runtime (.cacheSet initializer kind)),
  .globalSet (2 * ordinal + 1) kind,
  .i32Const .uint32 1,
  .globalSet (2 * ordinal) .uint32]

private def persistentCacheInitializerFunction (module : Module) :
    Except LinkError Function := do
  let mut body : List Instruction := []
  for ordinal in [:module.initializers.size] do
    let initializer := module.initializers[ordinal]!
    let some signature := module.callSignature? (.declaration initializer) |
      throw (.invalidInitializerSignature initializer)
    let some kind := signature.results[0]? |
      throw (.invalidInitializerSignature initializer)
    unless signature.params.isEmpty && signature.results.size == 1 do
      throw (.invalidInitializerSignature initializer)
    body := body ++ [
      .globalGet (2 * ordinal) .uint32,
      .ifElse [] (persistentCacheMiss ordinal initializer kind)]
  return {
    name := unsafeEagerPersistentInitializerName
    params := #[]
    results := #[]
    locals := #[]
    body := body ++ [.ret] }

/--
Diagnostic-only transform that preserves the compiler's exact lazy-cache
globals and adds one explicit, idempotent eager initializer. Each cache miss follows
the ordinary lowering protocol: call the original nullary declaration,
publish recursive persistence through `cacheSet`, store the typed value, then
set the initialized flag. Run this before allocator and cache-set
internalization; consumers call the exported entry before allocating scratch
inputs and retain its resulting frontier as their rewind checkpoint. This is
unsafe for arbitrary captured closures because it changes lazy evaluation and
may force unreachable panic or effect paths. Production consumers must retain
the original lazy miss sequence and use the cache-aware rewind floor instead.

The existing `eliminateLazyInitializers` path remains available for packages
that deliberately reconstruct closed values in each scratch call.
-/
def installUnsafeEagerPersistentInitializer
    (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  if reserved module unsafeEagerPersistentInitializerName then
    throw (.reservedDeclaration unsafeEagerPersistentInitializerName)
  let initializer ← persistentCacheInitializerFunction module
  let functions := module.functions.push initializer
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let result : Module := {
    module with
    functions
    exports := Fir.Wasm.addUnique module.exports
      unsafeEagerPersistentInitializerName
    runtimeOperations
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

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
def eliminateLazyInitializers (module : Module) (validate : Bool := true) :
    Except LinkError Module := do
  if validate then
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
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => pure ()
    | .error error => throw (.invalidOutput error)
  return result

def exampleDescriptors : Array (Array AbiKind) :=
  #[#[.tobject, .uint8, .tobject]]

def exampleOperation : RuntimeOp :=
  .cacheSet `residentCacheExample .object

def persistentExampleCallerName : Name := `resident_lazy_object

private def persistentObjectInitializerName : Name :=
  `residentLazyObjectInitializer

private def persistentObjectInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `ResidentCache.persistentObject
  cidx := 0
  size := 1
  «usize» := 0
  ssize := 0 }

private def persistentObjectAllocation : RuntimeOp :=
  .allocCtor persistentObjectInfo #[.tobject] .object

private def persistentObjectCacheSet : RuntimeOp :=
  .cacheSet persistentObjectInitializerName .object

private def persistentObjectInitializer : Function := {
  name := persistentObjectInitializerName
  params := #[]
  results := #[.object]
  locals := #[]
  body := [
    .i32Const .tobject 1,
    .call (.runtime persistentObjectAllocation),
    .ret] }

private def persistentObjectCaller : Function := {
  name := persistentExampleCallerName
  params := #[]
  results := #[.object]
  locals := #[]
  body := [
    .globalGet 0 .uint32,
    .ifElse [] [
      .call (.declaration persistentObjectInitializerName),
      .call (.runtime persistentObjectCacheSet),
      .globalSet 1 .object,
      .i32Const .uint32 1,
      .globalSet 0 .uint32],
    .globalGet 1 .object,
    .ret] }

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
  imports := #[exampleOperation, persistentObjectAllocation,
    persistentObjectCacheSet].mapIdx Fir.Wasm.runtimeImport
  functions := #[exampleCaller, persistentObjectInitializer,
    persistentObjectCaller]
  exports := #[exampleCaller.name, persistentObjectCaller.name]
  initializers := #[persistentObjectInitializerName]
  runtimeOperations := #[exampleOperation, persistentObjectAllocation,
    persistentObjectCacheSet]
  closureDescriptors := exampleDescriptors }

def residentExampleModule : Except String Module := do
  let prepared ← installUnsafeEagerPersistentInitializer exampleModule
    |>.mapError fun error => s!"initializer: {repr error}"
  let allocated ← ResidentAllocator.install prepared
    |>.mapError fun error => s!"allocator: {repr error}"
  let constructed ← ResidentConstructor.internalizeConstructors allocated
    |>.mapError fun error => s!"constructor: {repr error}"
  internalizeCacheSets constructed
    |>.mapError fun error => s!"cache: {repr error}"

def persistentCacheFlagName : Name := `resident_lazy_object_initialized

private def persistentCacheFlag : Function := {
  name := persistentCacheFlagName
  params := #[]
  results := #[.uint32]
  locals := #[]
  body := [.globalGet 0 .uint32, .ret] }

private def materializedInputModule : Module := {
  exampleModule with
  functions := exampleModule.functions.push persistentCacheFlag
  exports := exampleModule.exports.push persistentCacheFlagName }

/-- Focused zero-import proof-of-design for lazy publication of a static image. -/
def materializedExampleModule : Except String Module := do
  let imaged ← materializeClosedConstructor materializedInputModule
    persistentObjectInitializerName
    |>.mapError fun error => s!"static image: {repr error}"
  let allocated ← ResidentAllocator.install imaged
    |>.mapError fun error => s!"allocator: {repr error}"
  let constructed ← ResidentConstructor.internalizeConstructors allocated
    |>.mapError fun error => s!"constructors: {repr error}"
  internalizeCacheSets constructed
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

private def persistentInitializerBody : List Instruction := [
  .globalGet 0 .uint32,
  .ifElse [] [
    .call (.declaration lazyInitializerName),
    .call (.runtime (.cacheSet lazyInitializerName .uint32)),
    .globalSet 1 .uint32,
    .i32Const .uint32 1,
    .globalSet 0 .uint32],
  .ret]

#guard match installUnsafeEagerPersistentInitializer lazyModule with
  | .ok module =>
      module.initializers == lazyModule.initializers &&
      module.cacheGlobalKinds == lazyModule.cacheGlobalKinds &&
      module.globals == lazyModule.globals &&
      module.runtimeOperations == lazyModule.runtimeOperations &&
      module.exports.contains unsafeEagerPersistentInitializerName &&
      (module.functions.find?
          (·.name == unsafeEagerPersistentInitializerName) |>.map (·.body)) ==
        some persistentInitializerBody &&
      (Fir.Wasm.validateModule module).isOk
  | .error _ => false

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
    ("unsafeEagerPersistentInitializer",
      unsafeEagerPersistentInitializerName.toString),
    ("persistentEntry", persistentExampleCallerName.toString),
    ("value", "object"),
    ("constructorFieldLimit", constructorFieldLimit),
    ("cacheAwareRewind", true),
    ("status", "generation-ready; W6 recursive cache-persistence publication proved")]

def materializedManifest : Json :=
  Json.mkObj [
    ("entry", persistentExampleCallerName.toString),
    ("initializedEntry", persistentCacheFlagName.toString),
    ("initializer", persistentObjectInitializerName.toString),
    ("imageAddress", heapBase),
    ("imageBytes", 40),
    ("initialFrontier", (heapBase + 40 : Nat)),
    ("lazyPublication", true),
    ("status", "generation-ready focused static-image fixture")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      module.exports.contains exampleCaller.name &&
      module.exports.contains (cacheSetName 0) &&
      module.exports.contains (cacheSetName 1) &&
      module.exports.contains unsafeEagerPersistentInitializerName &&
      module.exports.contains persistentExampleCallerName &&
      module.globals.size == 2 &&
      (module.functions.find? (·.name == ResidentAllocator.rewindName)
        |>.map (·.body)) ==
        some (ResidentAllocator.cacheAwareRewindFunction 2 3).body &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

#guard match materializedExampleModule with
  | .ok module =>
      module.imports.isEmpty && module.runtimeOperations.isEmpty &&
      module.dataSegments.size == 1 &&
      module.dataSegments[0]?.map (·.offset) == some (u32 heapBase) &&
      module.dataSegments[0]?.map (·.bytes.size) == some 40 &&
      module.exports.contains persistentCacheFlagName &&
      (module.functions.find? (·.name == persistentObjectInitializerName)
        |>.map (·.body)) ==
        some [.i32Const .object (u32 heapBase), .ret] &&
      (Fir.Wasm.validateModule module).isOk &&
      (Fir.Wasm.Emit.encode module).isOk
  | .error _ => false

#guard match materializeClosedConstructor lazyModule lazyInitializerName with
  | .error (.unsupportedStaticInitializer name) => name == lazyInitializerName
  | _ => false

end Fir.Wasm.Emit.ResidentCache
