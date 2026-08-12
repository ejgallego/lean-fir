import Fir.Wasm.Validate

namespace Fir.Wasm.Emit

open Lean
open Fir.Wasm

abbrev Bytes := Array UInt8

inductive EncodeError where
  | invalidModule (error : SymbolicError)
  | unknownLocal (function : Name) (fvarId : FVarId)
  | unknownLabel (function : Name) (fvarId : FVarId)
  | unknownCallTarget (function : Name)
  | unknownExport (name : Name)
  deriving Inhabited, BEq, Repr

private partial def encodeU32 (value : Nat) : Bytes :=
  let low := value % 0x80
  if value < 0x80 then
    #[UInt8.ofNat low]
  else
    #[UInt8.ofNat (low + 0x80)] ++ encodeU32 (value / 0x80)

/--
Encode an i32 bit pattern as a valid five-byte signed LEB128 value. WebAssembly
permits signed encodings up to `ceil(32 / 7)` bytes; using the fixed width
avoids converting the unsigned FIR lane through a host-sized signed integer.
-/
private def encodeI32 (value : UInt32) : Bytes :=
  let chunk (shift : Nat) : UInt8 :=
    UInt8.ofNat (((value >>> UInt32.ofNat shift).toNat % 0x80) + 0x80)
  let top := (value >>> (28 : UInt32)).toNat % 0x10
  let signedTop := if (value >>> (31 : UInt32)) == 0 then top else top + 0x70
  #[chunk 0, chunk 7, chunk 14, chunk 21, UInt8.ofNat signedTop]

/-- Fixed-width signed LEB128 encoding of an i64 bit pattern. -/
private def encodeI64 (value : UInt64) : Bytes :=
  let chunk (shift : Nat) : UInt8 :=
    UInt8.ofNat (((value >>> UInt64.ofNat shift).toNat % 0x80) + 0x80)
  let signedTop := if (value >>> (63 : UInt64)) == 0 then 0 else 0x7f
  #[chunk 0, chunk 7, chunk 14, chunk 21, chunk 28, chunk 35, chunk 42,
    chunk 49, chunk 56, UInt8.ofNat signedTop]

private def encodeF32 (value : UInt32) : Bytes :=
  #[value.toUInt8,
    (value >>> (8 : UInt32)).toUInt8,
    (value >>> (16 : UInt32)).toUInt8,
    (value >>> (24 : UInt32)).toUInt8]

private def encodeF64 (value : UInt64) : Bytes :=
  #[value.toUInt8,
    (value >>> (8 : UInt64)).toUInt8,
    (value >>> (16 : UInt64)).toUInt8,
    (value >>> (24 : UInt64)).toUInt8,
    (value >>> (32 : UInt64)).toUInt8,
    (value >>> (40 : UInt64)).toUInt8,
    (value >>> (48 : UInt64)).toUInt8,
    (value >>> (56 : UInt64)).toUInt8]

private def concat (values : List Bytes) : Bytes :=
  values.foldl (· ++ ·) #[]

private def encodeVector (values : List Bytes) : Bytes :=
  encodeU32 values.length ++ concat values

private def encodeName (value : String) : Bytes :=
  let bytes := value.toUTF8
  encodeU32 bytes.size ++ bytes.data

private def encodeValueType : ValueType → UInt8
  | .i32 => 0x7f
  | .i64 => 0x7e
  | .f32 => 0x7d
  | .f64 => 0x7c

private def encodeSignature (signature : Signature) : Bytes :=
  #[0x60] ++
    encodeVector (signature.params.toList.map fun kind => #[encodeValueType kind.valueType]) ++
    encodeVector (signature.results.toList.map fun kind => #[encodeValueType kind.valueType])

private def findLabelIndex? : List (Option FVarId) → FVarId → Option Nat
  | [], _ => none
  | none :: rest, label => (findLabelIndex? rest label).map (· + 1)
  | some candidate :: rest, label =>
      if candidate.name == label.name then
        some 0
      else
        (findLabelIndex? rest label).map (· + 1)

private structure EncodeIndex where
  callTargets : Std.HashMap CallTarget Nat
  functionTargets : Std.HashMap Name Nat

private def importCallTarget (import_ : Import) : CallTarget :=
  match import_.key with
  | .runtime operation => .runtime operation
  | .external name => .declaration name

private def insertCallTarget
    (targets : Std.HashMap CallTarget Nat) (target : CallTarget) (index : Nat) :
    Std.HashMap CallTarget Nat :=
  if targets.contains target then targets else targets.insert target index

private def buildEncodeIndex (module : Module) : EncodeIndex :=
  let callTargets := module.imports.foldl (init := {}) fun targets import_ =>
    insertCallTarget targets (importCallTarget import_) targets.size
  let (callTargets, functionTargets) := module.functions.foldl
    (init := (callTargets, {})) fun (calls, functions) function =>
      let index := module.imports.size + functions.size
      (insertCallTarget calls (.declaration function.name) index,
        if functions.contains function.name then functions
        else functions.insert function.name index)
  { callTargets, functionTargets }

private structure Context where
  module : Module
  index : EncodeIndex
  function : Function
  localIndices : Std.HashMap Name Nat
  /-- Every Wasm control frame counts toward branch depth; only named FIR blocks match labels. -/
  labels : List (Option FVarId) := []

private def buildLocalIndex (function : Function) : Std.HashMap Name Nat :=
  let locals := function.params ++ function.locals
  (locals.foldl
    (init := (Std.HashMap.emptyWithCapacity locals.size, 0))
    fun (indices, next) (fvarId, _) =>
      let indices := if indices.contains fvarId.name then indices
        else indices.insert fvarId.name next
      (indices, next + 1)).1

mutual

private partial def encodeInstruction (context : Context) : Instruction → Except EncodeError Bytes
  | .i32Const _ value => return #[0x41] ++ encodeI32 value
  | .i64Const _ value => return #[0x42] ++ encodeI64 value
  | .f64Const bits => return #[0x44] ++ encodeF64 bits
  | .localGet fvarId => do
      let some index := context.localIndices.get? fvarId.name |
        throw (.unknownLocal context.function.name fvarId)
      return #[0x20] ++ encodeU32 index
  | .localGetObject fvarId => do
      let some index := context.localIndices.get? fvarId.name |
        throw (.unknownLocal context.function.name fvarId)
      return #[0x20] ++ encodeU32 index
  | .localSet fvarId => do
      let some index := context.localIndices.get? fvarId.name |
        throw (.unknownLocal context.function.name fvarId)
      return #[0x21] ++ encodeU32 index
  | .globalGet index _ => return #[0x23] ++ encodeU32 index
  | .globalSet index _ => return #[0x24] ++ encodeU32 index
  | .call target => do
      let some index := context.index.callTargets.get? target |
        throw (.unknownCallTarget context.function.name)
      return #[0x10] ++ encodeU32 index
  | .i32Eq => return #[0x46]
  | .i32And => return #[0x71]
  | .i32ShrU => return #[0x76]
  | .i32Add => return #[0x6a]
  | .i32Sub => return #[0x6b]
  | .i32RemU => return #[0x70]
  | .i32LtU => return #[0x49]
  | .i64Or => return #[0x84]
  | .i64Shl => return #[0x86]
  | .i64ShrU => return #[0x88]
  | .i64LtU => return #[0x54]
  | .f64Eq => return #[0x61]
  | .f64Lt => return #[0x63]
  | .f64Le => return #[0x65]
  | .f64Add => return #[0xa0]
  | .f64Sub => return #[0xa1]
  | .f64Mul => return #[0xa2]
  | .f64Div => return #[0xa3]
  | .f64Ceil => return #[0x9b]
  | .f64Floor => return #[0x9c]
  | .i32Load _ offset => return #[0x28, 0x02] ++ encodeU32 offset.toNat
  | .i32Load8U _ offset => return #[0x2d, 0x00] ++ encodeU32 offset.toNat
  | .i32Load16U _ offset => return #[0x2f, 0x01] ++ encodeU32 offset.toNat
  | .i64Load _ offset => return #[0x29, 0x03] ++ encodeU32 offset.toNat
  | .i32Store8 _ offset => return #[0x3a, 0x00] ++ encodeU32 offset.toNat
  | .i32Store16 _ offset => return #[0x3b, 0x01] ++ encodeU32 offset.toNat
  | .i32Store _ offset => return #[0x36, 0x02] ++ encodeU32 offset.toNat
  | .i64Store _ offset => return #[0x37, 0x03] ++ encodeU32 offset.toNat
  | .memorySize => return #[0x3f, 0x00]
  | .memoryGrow => return #[0x40, 0x00]
  | .i32WrapI64 _ => return #[0xa7]
  | .i64ExtendI32U _ => return #[0xad]
  | .f64ConvertI64U => return #[0xba]
  | .i64TruncSatF64U _ => return #[0xfc, 0x07]
  | .i32ReinterpretF32 _ => return #[0xbc]
  | .i64ReinterpretF64 _ => return #[0xbd]
  | .f32ReinterpretI32 _ => return #[0xbe]
  | .f64ReinterpretI64 _ => return #[0xbf]
  | .block label body => do
      let body ← encodeInstructions { context with labels := some label :: context.labels } body
      return #[0x02, 0x40] ++ body ++ #[0x0b]
  | .loop label body => do
      let body ← encodeInstructions { context with labels := some label :: context.labels } body
      return #[0x03, 0x40] ++ body ++ #[0x0b]
  | .ifElse thenBody elseBody => do
      let nested := { context with labels := none :: context.labels }
      let thenBody ← encodeInstructions nested thenBody
      let elseBody ← encodeInstructions nested elseBody
      return #[0x04, 0x40] ++ thenBody ++ #[0x05] ++ elseBody ++ #[0x0b]
  | .br label => do
      let some index := findLabelIndex? context.labels label |
        throw (.unknownLabel context.function.name label)
      return #[0x0c] ++ encodeU32 index
  | .ret => return #[0x0f]
  | .unreachable => return #[0x00]

private partial def encodeInstructions (context : Context) :
    List Instruction → Except EncodeError Bytes :=
  let rec encode (bytes : Bytes) : List Instruction → Except EncodeError Bytes
    | [] => return bytes
    | instruction :: rest => do
        let instructionBytes ← encodeInstruction context instruction
        encode (bytes ++ instructionBytes) rest
  encode #[]

end

private def encodeImport (index : Nat) (import_ : Import) : Bytes :=
  encodeName import_.moduleName ++ encodeName import_.itemName ++ #[0x00] ++ encodeU32 index

private def encodeFunctionBody (module : Module) (checkIndex : CheckIndex)
    (index : EncodeIndex) (function : Function) :
    Except EncodeError Bytes := do
  let localDeclarations := function.locals.toList.map fun (_, kind) =>
    encodeU32 1 ++ #[encodeValueType kind.valueType]
  let body ← encodeInstructions {
    module, index, function, localIndices := buildLocalIndex function } function.body
  let locals := function.params ++ function.locals
  let checkerContext : CheckContext := {
    module
    function
    locals := locals.toList
    localIndex? := some <| locals.foldl
      (init := Std.HashMap.emptyWithCapacity locals.size)
      fun localIndex (fvarId, kind) => localIndex.insert fvarId.name kind
    index? := some checkIndex }
  let flow ←
    match checkInstructions checkerContext (some []) function.body with
    | .ok flow => pure flow
    | .error error => throw (.invalidModule error)
  /-
  Standard Wasm does not propagate an unreachable branch state through the
  end of a zero-result `if`. When FIR's validated symbolic flow has no normal
  fallthrough, make that fact explicit before the function end. This is
  unreachable on every symbolic execution and supplies the polymorphic stack
  required by the standard validator.
  -/
  let terminal := if flow.fallthrough.isNone then #[0x00] else #[]
  let payload := encodeVector localDeclarations ++ body ++ terminal ++ #[0x0b]
  return encodeU32 payload.size ++ payload

private def encodeExport (index : EncodeIndex) (name : Name) : Except EncodeError Bytes := do
  let some target := index.functionTargets.get? name | throw (.unknownExport name)
  return encodeName name.toString ++ #[0x00] ++ encodeU32 target

private def encodeMemoryExport (name : String) : Bytes :=
  encodeName name ++ #[0x02] ++ encodeU32 0

private def encodeMemory (memory : MemoryDecl) : Bytes :=
  match memory.pagesMax with
  | none => #[0x00] ++ encodeU32 memory.pagesMin.toNat
  | some pagesMax =>
      #[0x01] ++ encodeU32 memory.pagesMin.toNat ++ encodeU32 pagesMax.toNat

private def zeroGlobal (kind : AbiKind) : GlobalDecl := {
  kind
  init :=
    match kind.valueType with
    | .i32 => .i32 0
    | .i64 => .i64 0
    | .f32 => .f32 0
    | .f64 => .f64 0 }

private def encodeGlobal (global : GlobalDecl) : Bytes :=
  let initializer :=
    match global.init with
    | .i32 value => #[0x41] ++ encodeI32 value ++ #[0x0b]
    | .i64 value => #[0x42] ++ encodeI64 value ++ #[0x0b]
    | .f32 bits => #[0x43] ++ encodeF32 bits ++ #[0x0b]
    | .f64 bits => #[0x44] ++ encodeF64 bits ++ #[0x0b]
  #[encodeValueType global.kind.valueType, 0x01] ++ initializer

private def encodeSection (id : UInt8) (payload : Bytes) : Bytes :=
  #[id] ++ encodeU32 payload.size ++ payload

def header : Bytes := #[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]

/--
Serialize a statically validated FIR symbolic module as a deterministic
WebAssembly 1.0 binary. Types are deliberately retained in declaration order
instead of deduplicated: this keeps indices simple, stable, and inspectable.
-/
private def encodeCore (module : Module) (validate : Bool) :
    Except EncodeError ByteArray := do
  if validate then
    match validateModule module with
    | .ok _ => pure ()
    | .error error => throw (.invalidModule error)

  let checkIndex := module.checkIndex
  let index := buildEncodeIndex module

  let signatures :=
    module.imports.toList.map (·.signature) ++
      module.functions.toList.map Function.signature
  let typePayload := encodeVector (signatures.map encodeSignature)
  let importPayload := encodeVector <|
    module.imports.toList.zipIdx.map fun (import_, index) => encodeImport index import_
  let functionPayload := encodeVector <|
    module.functions.toList.zipIdx.map fun (_, index) =>
      encodeU32 (module.imports.size + index)
  let globals :=
    module.cacheGlobalKinds.map zeroGlobal ++ module.globals
  let globalPayload := encodeVector <| globals.toList.map encodeGlobal
  let functionExports ← module.exports.toList.mapM (encodeExport index)
  let memoryExports :=
    match module.memory.bind (·.exportName) with
    | none => []
    | some name => [encodeMemoryExport name]
  let exportPayload := encodeVector (functionExports ++ memoryExports)
  let codePayload ← encodeVector <$> module.functions.toList.mapM
    (encodeFunctionBody module checkIndex index)

  let mut bytes := header
  unless signatures.isEmpty do
    bytes := bytes ++ encodeSection 0x01 typePayload
  unless module.imports.isEmpty do
    bytes := bytes ++ encodeSection 0x02 importPayload
  unless module.functions.isEmpty do
    bytes := bytes ++ encodeSection 0x03 functionPayload
  if let some memory := module.memory then
    bytes := bytes ++ encodeSection 0x05 (encodeVector [encodeMemory memory])
  unless globals.isEmpty do
    bytes := bytes ++ encodeSection 0x06 globalPayload
  unless functionExports.isEmpty && memoryExports.isEmpty do
    bytes := bytes ++ encodeSection 0x07 exportPayload
  unless module.functions.isEmpty do
    bytes := bytes ++ encodeSection 0x0a codePayload
  return ByteArray.mk bytes

/-- Validate and serialize one FIR symbolic module. -/
def encode (module : Module) : Except EncodeError ByteArray :=
  encodeCore module true

/--
Serialize a module already accepted by `validateModule`. This retains the
per-function flow check needed to emit explicit unreachable terminals, but
does not repeat the module's entry/exit validation. Keep this at a composition
boundary that has the validated module as its immediate input.
-/
def encodeValidated (module : Module) : Except EncodeError ByteArray :=
  encodeCore module false

end Fir.Wasm.Emit
