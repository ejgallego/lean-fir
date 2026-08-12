import Fir.Wasm.Emit.ResidentAllocator

namespace Fir.Wasm.Emit.ResidentLiteral

open Fir.Wasm
open Fir.Wasm.Concrete
open Lean

private def addressLocal : FVarId := ⟨`address⟩
private def savedScratchLocal : FVarId := ⟨`savedScratch⟩
private def resultLocal : FVarId := ⟨`result⟩

inductive LinkError where
  | invalidInput (error : SymbolicError)
  | missingAllocator
  | reservedDeclaration (name : Name)
  | unsupportedOperation
  | metadataOverflow (label : String) (value : Nat)
  | incompatibleMemory
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

/--
The resident literal slice deliberately supports the exact representation
families it can construct without a host: immediate and promoted tagged
naturals plus UTF-8 string objects. Naturals above Lean's semantic tagged limit
retain their semantic import until the big-natural allocator is internalized.
-/
def isImmediateNatural : RuntimeOp → Bool
  | .literal (.nat value) result =>
      decide (value ≤ maxImmediatePayload) &&
        (result == .tagged || result == .tobject)
  | _ => false

def isPromotedNatural : RuntimeOp → Bool
  | .literal (.nat value) result =>
      decide (maxImmediatePayload < value) &&
        decide (value ≤ Fir.LeanIR.Impure.maxTaggedPayload) &&
        (result == .tagged || result == .tobject)
  | _ => false

def isNaturalLiteral (operation : RuntimeOp) : Bool :=
  isImmediateNatural operation || isPromotedNatural operation

def isStringLiteral : RuntimeOp → Bool
  | .literal (.str _) result =>
      result == .object || result == .tobject
  | _ => false

def isSupportedLiteral (operation : RuntimeOp) : Bool :=
  isNaturalLiteral operation || isStringLiteral operation

def naturalName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_nat_literal_{ordinal}"

def stringName (ordinal : Nat) : Name :=
  Name.mkSimple s!"fir_string_literal_{ordinal}"

private def operationName (ordinal : Nat) : RuntimeOp → Name
  | .literal (.nat _) _ => naturalName ordinal
  | .literal (.str _) _ => stringName ordinal
  | _ => Name.mkSimple s!"fir_unsupported_literal_{ordinal}"

private def checkedWord (label : String) (value : Nat) :
    Except LinkError UInt32 :=
  if value < UInt32.size then
    pure (u32 value)
  else
    throw (.metadataOverflow label value)

private def store32 (value : List Instruction) (offset : UInt32) :
    List Instruction :=
  [.localGet addressLocal] ++ value ++ [.i32Store .uint32 offset]

private def zeroAllocation (allocationBytes : Nat) : List Instruction :=
  (List.range (allocationBytes / 4)).flatMap fun index =>
    store32 [.i32Const .uint32 0] (u32 (4 * index))

private def stringHeaderStores (allocationBytes byteCount : UInt32) :
    List Instruction :=
  store32 [.i32Const .uint32 ObjectKind.string.code]
      (u32 headerKindOffset) ++
    store32 [.i32Const .uint32 liveFlag]
      (u32 headerFlagsOffset) ++
    store32 [.i32Const .uint32 1]
      (u32 headerRefCountOffset) ++
    store32 [.i32Const .uint32 allocationBytes]
      (u32 headerAllocationBytesOffset) ++
    store32 [.i32Const .uint32 stringUtf8Marker]
      (u32 headerAux0Offset) ++
    store32 [.i32Const .uint32 byteCount]
      (u32 headerAux1Offset) ++
    store32 [.i32Const .uint32 0]
      (u32 headerAux2Offset) ++
    store32 [.i32Const .uint32 0]
      (u32 headerAux3Offset)

private def stringByteStores (bytes : List UInt8) : List Instruction :=
  bytes.zipIdx.flatMap fun (byte, index) => [
    .localGet addressLocal,
    .i32Const .uint8 (u32 byte.toNat),
    .i32Store8 .uint8 (u32 (headerBytes + index))]

/--
Retag one raw wasm32 address as the statically declared object-like result.
The scratch word is below `heapBase` and is restored exactly.
-/
private def retagAddress (result : AbiKind) : List Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet savedScratchLocal,
  .i32Const .uint32 0,
  .localGet addressLocal,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load result 0,
  .localSet resultLocal,
  .i32Const .uint32 0,
  .localGet savedScratchLocal,
  .i32Store .uint32 0,
  .localGet resultLocal,
  .ret]

private def naturalFunction (name : Name) (value : Nat)
    (result : AbiKind) : Except LinkError Function := do
  unless value ≤ Fir.LeanIR.Impure.maxTaggedPayload &&
      (result == .tagged || result == .tobject) do
    throw .unsupportedOperation
  if value ≤ maxImmediatePayload then
    let encoded ← checkedWord "immediate natural literal" (value * 2 + 1)
    return {
      name
      params := #[]
      results := #[result]
      locals := #[]
      body := [.i32Const result encoded, .ret] }
  else
    let payload := UInt64.ofNat value
    let allocationSize := align8 (headerBytes + target.semanticSlotBytes)
    let allocationBytes ← checkedWord "promoted natural allocation bytes"
      allocationSize
    return {
      name
      params := #[]
      results := #[result]
      locals := #[(addressLocal, .uint32), (savedScratchLocal, .uint32),
        (resultLocal, result)]
      body :=
        [.i32Const .uint32 allocationBytes,
          .call (.declaration ResidentAllocator.allocateName),
          .localSet addressLocal] ++
        zeroAllocation allocationSize ++
        store32 [.i32Const .uint32 ObjectKind.natural.code]
          (u32 headerKindOffset) ++
        store32 [.i32Const .uint32 (liveFlag + persistentFlag)]
          (u32 headerFlagsOffset) ++
        store32 [.i32Const .uint32 0] (u32 headerRefCountOffset) ++
        store32 [.i32Const .uint32 allocationBytes]
          (u32 headerAllocationBytesOffset) ++
        store32 [.i32Const .uint32 promotedTagMarker] (u32 headerAux0Offset) ++
        store32 [.i32Const .uint32 1] (u32 headerAux1Offset) ++
        store32 [.i32Const .uint32 0] (u32 headerAux2Offset) ++
        store32 [.i32Const .uint32 0] (u32 headerAux3Offset) ++ [
          .localGet addressLocal,
          .i64Const .uint64 payload,
          .i64Store .uint64 (u32 headerBytes)] ++
        retagAddress result }

private def stringFunction (name : Name) (value : String)
    (result : AbiKind) : Except LinkError Function := do
  unless result == .object || result == .tobject do
    throw .unsupportedOperation
  let bytes := value.toUTF8.data.toList
  let byteCount ← checkedWord "string UTF-8 byte count" bytes.length
  let allocationSize := align8 (headerBytes + bytes.length)
  let allocationBytes ← checkedWord "string allocation bytes" allocationSize
  return {
    name
    params := #[]
    results := #[result]
    locals := #[
      (addressLocal, .uint32),
      (savedScratchLocal, .uint32),
      (resultLocal, result)]
    body :=
      [.i32Const .uint32 allocationBytes,
        .call (.declaration ResidentAllocator.allocateName),
        .localSet addressLocal] ++
      zeroAllocation allocationSize ++
      stringHeaderStores allocationBytes byteCount ++
      stringByteStores bytes ++
      retagAddress result }

def literalFunction (ordinal : Nat) (operation : RuntimeOp) :
    Except LinkError Function := do
  unless operation.abiWellFormed do
    throw .unsupportedOperation
  let name := operationName ordinal operation
  match operation with
  | .literal (.nat value) result => naturalFunction name value result
  | .literal (.str value) result => stringFunction name value result
  | _ => throw .unsupportedOperation

private partial def rewriteInstruction (operation : RuntimeOp)
    (name : Name) : Instruction → Instruction
  | .call (.runtime candidate) =>
      if candidate == operation then
        .call (.declaration name)
      else
        .call (.runtime candidate)
  | .block label body =>
      .block label (body.map (rewriteInstruction operation name))
  | .loop label body =>
      .loop label (body.map (rewriteInstruction operation name))
  | .ifElse thenBody elseBody =>
      .ifElse
        (thenBody.map (rewriteInstruction operation name))
        (elseBody.map (rewriteInstruction operation name))
  | instruction => instruction

private def rewriteFunction (operation : RuntimeOp) (name : Name)
    (function : Function) : Function :=
  { function with body := function.body.map (rewriteInstruction operation name) }

private def internalizeOne (ordinal : Nat) (operation : RuntimeOp)
    (module : Module) : Except LinkError Module := do
  let name := operationName ordinal operation
  if module.imports.any (·.declaration? == some name) ||
      module.functions.any (·.name == name) ||
      module.exports.contains name then
    throw (.reservedDeclaration name)
  let function ← literalFunction ordinal operation
  let functions :=
    (module.functions.map (rewriteFunction operation name)).push function
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := module.imports.filter (·.operation?.isNone)
  let imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
  return {
    module with
    imports
    functions
    exports := Fir.Wasm.addUnique module.exports name
    runtimeOperations }

/--
Internalize every currently supported natural or string literal after the
resident allocator has been installed. Unsupported literal representations
remain imports rather than being silently reinterpreted.
-/
private def internalizeMatching (predicate : RuntimeOp → Bool)
    (module : Module) (validate : Bool) : Except LinkError Module := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  unless module.functions.any (·.name == ResidentAllocator.allocateName) do
    throw .missingAllocator
  unless module.memory == some ResidentRuntime.residentMemory do
    throw .incompatibleMemory
  let operations := module.runtimeOperations.filter predicate
  let result ← operations.toList.zipIdx.foldlM (init := module)
    fun result (operation, ordinal) =>
      internalizeOne ordinal operation result
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => return result
    | .error error => throw (.invalidOutput error)
  else return result

/--
Internalize natural literals through Lean's semantic tagged limit. The
historical name is retained for policy/API compatibility; generated helpers
select an immediate word or promoted natural from the literal value.
-/
def internalizeImmediateNaturals (module : Module) (validate : Bool := true) :
    Except LinkError Module :=
  internalizeMatching isNaturalLiteral module validate

def internalizeStrings (module : Module) (validate : Bool := true) : Except LinkError Module :=
  internalizeMatching isStringLiteral module validate

def internalizeLiterals (module : Module) (validate : Bool := true) : Except LinkError Module := do
  let module ← internalizeImmediateNaturals module validate
  internalizeStrings module validate

def exampleOperations : Array RuntimeOp := #[
  .literal (.nat 0) .tagged,
  .literal (.nat 1) .tobject,
  .literal (.nat 4294967296) .tagged,
  .literal (.str "") .object,
  .literal (.str "λ\n") .object]

private def exampleCaller (index : Nat) (name : Name)
    (result : AbiKind) : Function := {
  name
  params := #[]
  results := #[result]
  locals := #[]
  body := [.call (.runtime exampleOperations[index]!), .ret] }

def exampleFunctions : Array Function := #[
  exampleCaller 0 `resident_literal_nat_zero .tagged,
  exampleCaller 1 `resident_literal_nat_one .tobject,
  exampleCaller 2 `resident_literal_nat_promoted .tagged,
  exampleCaller 3 `resident_literal_empty_string .object,
  exampleCaller 4 `resident_literal_unicode_string .object]

def exampleModule : Module := {
  imports := exampleOperations.mapIdx Fir.Wasm.runtimeImport
  functions := exampleFunctions
  exports := exampleFunctions.map (·.name)
  initializers := #[]
  runtimeOperations := exampleOperations }

def residentExampleModule : Except String Module := do
  let allocated ← ResidentAllocator.install exampleModule
    |>.mapError fun error => s!"allocator: {repr error}"
  internalizeLiterals allocated
    |>.mapError fun error => s!"literals: {repr error}"

def manifest : Json :=
  Json.mkObj [
    ("entries", Json.arr #[
      Json.mkObj [("entry", "resident_literal_nat_zero"), ("kind", "nat"),
        ("value", 0)],
      Json.mkObj [("entry", "resident_literal_nat_one"), ("kind", "nat"),
        ("value", 1)],
      Json.mkObj [("entry", "resident_literal_nat_promoted"), ("kind", "nat"),
        ("value", "4294967296")],
      Json.mkObj [("entry", "resident_literal_empty_string"), ("kind", "string"),
        ("value", "")],
      Json.mkObj [("entry", "resident_literal_unicode_string"), ("kind", "string"),
        ("value", "λ\n")]]),
    ("stringEncoding", "UTF-8"),
    ("stringMarker", stringUtf8Marker.toNat),
    ("scratchAddress", 0),
    ("scratchPolicy", "saved-and-restored"),
    ("status", "generation-only; W6 literal contract proofs pending")]

#guard match residentExampleModule with
  | .ok module =>
      module.imports.isEmpty &&
      module.runtimeOperations.isEmpty &&
      module.functions.size ==
        exampleFunctions.size + ResidentAllocator.helperNames.size +
          exampleOperations.size &&
      exampleFunctions.all fun function => module.exports.contains function.name &&
      module.memory == some ResidentRuntime.residentMemory &&
      (Fir.Wasm.validateModule module |>.isOk) &&
      (Fir.Wasm.Emit.encode module |>.isOk)
  | .error _ => false

end Fir.Wasm.Emit.ResidentLiteral
