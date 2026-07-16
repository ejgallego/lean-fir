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

private def findFVarIndex? : List (FVarId × α) → FVarId → Option Nat
  | [], _ => none
  | (candidate, _) :: rest, fvarId =>
      if candidate.name == fvarId.name then
        some 0
      else
        (findFVarIndex? rest fvarId).map (· + 1)

private def findLabelIndex? : List (Option FVarId) → FVarId → Option Nat
  | [], _ => none
  | none :: rest, label => (findLabelIndex? rest label).map (· + 1)
  | some candidate :: rest, label =>
      if candidate.name == label.name then
        some 0
      else
        (findLabelIndex? rest label).map (· + 1)

private def findImportTarget? (module : Module) : CallTarget → Option Nat
  | .runtime operation =>
      module.imports.findIdx? fun import_ => import_.operation? == some operation
  | .declaration name =>
      module.imports.findIdx? fun import_ => import_.declaration? == some name

private def findFunctionTarget? (module : Module) (name : Name) : Option Nat :=
  (module.functions.findIdx? (·.name == name)).map (module.imports.size + ·)

private def findCallTarget? (module : Module) : CallTarget → Option Nat
  | target@(.runtime _) => findImportTarget? module target
  | target@(.declaration name) =>
      findImportTarget? module target <|> findFunctionTarget? module name

private structure Context where
  module : Module
  function : Function
  /-- Every Wasm control frame counts toward branch depth; only named FIR blocks match labels. -/
  labels : List (Option FVarId) := []

mutual

private partial def encodeInstruction (context : Context) : Instruction → Except EncodeError Bytes
  | .i32Const _ value => return #[0x41] ++ encodeI32 value
  | .i64Const _ value => return #[0x42] ++ encodeI64 value
  | .localGet fvarId => do
      let locals := context.function.params.toList ++ context.function.locals.toList
      let some index := findFVarIndex? locals fvarId |
        throw (.unknownLocal context.function.name fvarId)
      return #[0x20] ++ encodeU32 index
  | .localSet fvarId => do
      let locals := context.function.params.toList ++ context.function.locals.toList
      let some index := findFVarIndex? locals fvarId |
        throw (.unknownLocal context.function.name fvarId)
      return #[0x21] ++ encodeU32 index
  | .call target => do
      let some index := findCallTarget? context.module target |
        throw (.unknownCallTarget context.function.name)
      return #[0x10] ++ encodeU32 index
  | .i32Eq => return #[0x46]
  | .block label body => do
      let body ← encodeInstructions { context with labels := some label :: context.labels } body
      return #[0x02, 0x40] ++ body ++ #[0x0b]
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
    List Instruction → Except EncodeError Bytes
  | [] => return #[]
  | instruction :: rest =>
      return (← encodeInstruction context instruction) ++
        (← encodeInstructions context rest)

end

private def encodeImport (index : Nat) (import_ : Import) : Bytes :=
  encodeName import_.moduleName ++ encodeName import_.itemName ++ #[0x00] ++ encodeU32 index

private def encodeFunctionBody (module : Module) (function : Function) :
    Except EncodeError Bytes := do
  let localDeclarations := function.locals.toList.map fun (_, kind) =>
    encodeU32 1 ++ #[encodeValueType kind.valueType]
  let body ← encodeInstructions { module, function } function.body
  let checkerContext : CheckContext := {
    module
    function
    locals := (function.params ++ function.locals).toList }
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

private def encodeExport (module : Module) (name : Name) : Except EncodeError Bytes := do
  let some index := findFunctionTarget? module name | throw (.unknownExport name)
  return encodeName name.toString ++ #[0x00] ++ encodeU32 index

private def encodeSection (id : UInt8) (payload : Bytes) : Bytes :=
  #[id] ++ encodeU32 payload.size ++ payload

def header : Bytes := #[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]

/--
Serialize a statically validated FIR symbolic module as a deterministic
WebAssembly 1.0 binary. Types are deliberately retained in declaration order
instead of deduplicated: this keeps indices simple, stable, and inspectable.
-/
def encode (module : Module) : Except EncodeError ByteArray := do
  match validateModule module with
  | .ok _ => pure ()
  | .error error => throw (.invalidModule error)

  let signatures :=
    module.imports.toList.map (·.signature) ++
      module.functions.toList.map Function.signature
  let typePayload := encodeVector (signatures.map encodeSignature)
  let importPayload := encodeVector <|
    module.imports.toList.zipIdx.map fun (import_, index) => encodeImport index import_
  let functionPayload := encodeVector <|
    module.functions.toList.zipIdx.map fun (_, index) =>
      encodeU32 (module.imports.size + index)
  let exportPayload ← encodeVector <$> module.exports.toList.mapM (encodeExport module)
  let codePayload ← encodeVector <$> module.functions.toList.mapM (encodeFunctionBody module)

  let mut bytes := header
  unless signatures.isEmpty do
    bytes := bytes ++ encodeSection 0x01 typePayload
  unless module.imports.isEmpty do
    bytes := bytes ++ encodeSection 0x02 importPayload
  unless module.functions.isEmpty do
    bytes := bytes ++ encodeSection 0x03 functionPayload
  unless module.exports.isEmpty do
    bytes := bytes ++ encodeSection 0x07 exportPayload
  unless module.functions.isEmpty do
    bytes := bytes ++ encodeSection 0x0a codePayload
  return ByteArray.mk bytes

end Fir.Wasm.Emit
