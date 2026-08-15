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
  | .f32Const bits => return #[0x43] ++ encodeF32 bits
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
  | .i32Eqz => return #[0x45]
  | .i32Eq => return #[0x46]
  | .i32Ne => return #[0x47]
  | .i32LtS => return #[0x48]
  | .i32LtU => return #[0x49]
  | .i32GtS => return #[0x4a]
  | .i32GtU => return #[0x4b]
  | .i32LeS => return #[0x4c]
  | .i32LeU => return #[0x4d]
  | .i32GeS => return #[0x4e]
  | .i32GeU => return #[0x4f]
  | .i64Eqz => return #[0x50]
  | .i64Eq => return #[0x51]
  | .i64Ne => return #[0x52]
  | .i64LtS => return #[0x53]
  | .i64LtU => return #[0x54]
  | .i64GtS => return #[0x55]
  | .i64GtU => return #[0x56]
  | .i64LeS => return #[0x57]
  | .i64LeU => return #[0x58]
  | .i64GeS => return #[0x59]
  | .i64GeU => return #[0x5a]
  | .f32Eq => return #[0x5b]
  | .f32Ne => return #[0x5c]
  | .f32Lt => return #[0x5d]
  | .f32Gt => return #[0x5e]
  | .f32Le => return #[0x5f]
  | .f32Ge => return #[0x60]
  | .f64Eq => return #[0x61]
  | .f64Ne => return #[0x62]
  | .f64Lt => return #[0x63]
  | .f64Gt => return #[0x64]
  | .f64Le => return #[0x65]
  | .f64Ge => return #[0x66]
  | .i32Clz => return #[0x67]
  | .i32Ctz => return #[0x68]
  | .i32Popcnt => return #[0x69]
  | .i32Add => return #[0x6a]
  | .i32Sub => return #[0x6b]
  | .i32Mul => return #[0x6c]
  | .i32DivS => return #[0x6d]
  | .i32DivU => return #[0x6e]
  | .i32RemS => return #[0x6f]
  | .i32RemU => return #[0x70]
  | .i32And => return #[0x71]
  | .i32Or => return #[0x72]
  | .i32Xor => return #[0x73]
  | .i32Shl => return #[0x74]
  | .i32ShrS => return #[0x75]
  | .i32ShrU => return #[0x76]
  | .i32Rotl => return #[0x77]
  | .i32Rotr => return #[0x78]
  | .i64Clz => return #[0x79]
  | .i64Ctz => return #[0x7a]
  | .i64Popcnt => return #[0x7b]
  | .i64Add => return #[0x7c]
  | .i64Sub => return #[0x7d]
  | .i64Mul => return #[0x7e]
  | .i64DivS => return #[0x7f]
  | .i64DivU => return #[0x80]
  | .i64RemS => return #[0x81]
  | .i64RemU => return #[0x82]
  | .i64And => return #[0x83]
  | .i64Or => return #[0x84]
  | .i64Xor => return #[0x85]
  | .i64Shl => return #[0x86]
  | .i64ShrS => return #[0x87]
  | .i64ShrU => return #[0x88]
  | .i64Rotl => return #[0x89]
  | .i64Rotr => return #[0x8a]
  | .f32Abs => return #[0x8b]
  | .f32Neg => return #[0x8c]
  | .f32Ceil => return #[0x8d]
  | .f32Floor => return #[0x8e]
  | .f32Trunc => return #[0x8f]
  | .f32Nearest => return #[0x90]
  | .f32Sqrt => return #[0x91]
  | .f32Add => return #[0x92]
  | .f32Sub => return #[0x93]
  | .f32Mul => return #[0x94]
  | .f32Div => return #[0x95]
  | .f32Min => return #[0x96]
  | .f32Max => return #[0x97]
  | .f32Copysign => return #[0x98]
  | .f64Abs => return #[0x99]
  | .f64Neg => return #[0x9a]
  | .f64Ceil => return #[0x9b]
  | .f64Floor => return #[0x9c]
  | .f64Trunc => return #[0x9d]
  | .f64Nearest => return #[0x9e]
  | .f64Sqrt => return #[0x9f]
  | .f64Add => return #[0xa0]
  | .f64Sub => return #[0xa1]
  | .f64Mul => return #[0xa2]
  | .f64Div => return #[0xa3]
  | .f64Min => return #[0xa4]
  | .f64Max => return #[0xa5]
  | .f64Copysign => return #[0xa6]
  | .i32Load _ offset => return #[0x28, 0x02] ++ encodeU32 offset.toNat
  | .i32Load8S _ offset => return #[0x2c, 0x00] ++ encodeU32 offset.toNat
  | .i32Load8U _ offset => return #[0x2d, 0x00] ++ encodeU32 offset.toNat
  | .i32Load16S _ offset => return #[0x2e, 0x01] ++ encodeU32 offset.toNat
  | .i32Load16U _ offset => return #[0x2f, 0x01] ++ encodeU32 offset.toNat
  | .i64Load _ offset => return #[0x29, 0x03] ++ encodeU32 offset.toNat
  | .i64Load8S _ offset => return #[0x30, 0x00] ++ encodeU32 offset.toNat
  | .i64Load8U _ offset => return #[0x31, 0x00] ++ encodeU32 offset.toNat
  | .i64Load16S _ offset => return #[0x32, 0x01] ++ encodeU32 offset.toNat
  | .i64Load16U _ offset => return #[0x33, 0x01] ++ encodeU32 offset.toNat
  | .i64Load32S _ offset => return #[0x34, 0x02] ++ encodeU32 offset.toNat
  | .i64Load32U _ offset => return #[0x35, 0x02] ++ encodeU32 offset.toNat
  | .f32Load offset => return #[0x2a, 0x02] ++ encodeU32 offset.toNat
  | .f64Load offset => return #[0x2b, 0x03] ++ encodeU32 offset.toNat
  | .i32Store8 _ offset => return #[0x3a, 0x00] ++ encodeU32 offset.toNat
  | .i32Store16 _ offset => return #[0x3b, 0x01] ++ encodeU32 offset.toNat
  | .i32Store _ offset => return #[0x36, 0x02] ++ encodeU32 offset.toNat
  | .i64Store _ offset => return #[0x37, 0x03] ++ encodeU32 offset.toNat
  | .i64Store8 _ offset => return #[0x3c, 0x00] ++ encodeU32 offset.toNat
  | .i64Store16 _ offset => return #[0x3d, 0x01] ++ encodeU32 offset.toNat
  | .i64Store32 _ offset => return #[0x3e, 0x02] ++ encodeU32 offset.toNat
  | .f32Store offset => return #[0x38, 0x02] ++ encodeU32 offset.toNat
  | .f64Store offset => return #[0x39, 0x03] ++ encodeU32 offset.toNat
  | .memorySize => return #[0x3f, 0x00]
  | .memoryGrow => return #[0x40, 0x00]
  | .i32WrapI64 _ => return #[0xa7]
  | .i64ExtendI32S _ => return #[0xac]
  | .i64ExtendI32U _ => return #[0xad]
  | .i32Extend8S _ => return #[0xc0]
  | .i32Extend16S _ => return #[0xc1]
  | .i64Extend8S _ => return #[0xc2]
  | .i64Extend16S _ => return #[0xc3]
  | .i64Extend32S _ => return #[0xc4]
  | .f32ConvertI32S => return #[0xb2]
  | .f32ConvertI32U => return #[0xb3]
  | .f32ConvertI64S => return #[0xb4]
  | .f32ConvertI64U => return #[0xb5]
  | .f64ConvertI32S => return #[0xb7]
  | .f64ConvertI32U => return #[0xb8]
  | .f64ConvertI64S => return #[0xb9]
  | .f64ConvertI64U => return #[0xba]
  | .i32TruncF32S _ => return #[0xa8]
  | .i32TruncF32U _ => return #[0xa9]
  | .i32TruncF64S _ => return #[0xaa]
  | .i32TruncF64U _ => return #[0xab]
  | .i64TruncF32S _ => return #[0xae]
  | .i64TruncF32U _ => return #[0xaf]
  | .i64TruncF64S _ => return #[0xb0]
  | .i64TruncF64U _ => return #[0xb1]
  | .i32TruncSatF32S _ => return #[0xfc, 0x00]
  | .i32TruncSatF32U _ => return #[0xfc, 0x01]
  | .i32TruncSatF64S _ => return #[0xfc, 0x02]
  | .i32TruncSatF64U _ => return #[0xfc, 0x03]
  | .i64TruncSatF32S _ => return #[0xfc, 0x04]
  | .i64TruncSatF32U _ => return #[0xfc, 0x05]
  | .i64TruncSatF64S _ => return #[0xfc, 0x06]
  | .i64TruncSatF64U _ => return #[0xfc, 0x07]
  | .f32DemoteF64 => return #[0xb6]
  | .f64PromoteF32 => return #[0xbb]
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

private def encodeDataSegment (segment : DataSegment) : Bytes :=
  /- Active segment for memory 0, followed by an i32.const offset expression. -/
  #[0x00, 0x41] ++ encodeI32 segment.offset ++ #[0x0b] ++
    encodeU32 segment.bytes.size ++ segment.bytes

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
  let dataPayload := encodeVector <|
    module.dataSegments.toList.map encodeDataSegment

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
  unless module.dataSegments.isEmpty do
    bytes := bytes ++ encodeSection 0x0b dataPayload
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
