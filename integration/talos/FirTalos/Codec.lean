import Fir.Wasm.Handle
import Interpreter.Wasm.Syntax

namespace FirTalos

open Fir.Wasm
open Fir.LeanIR.Impure

/-- Decode one physical Talos value according to FIR's retained semantic ABI kind. -/
def decodeValue (table : HandleTable) (kind : AbiKind) (value : Wasm.Value) :
    Except TargetFailure Value :=
  match kind, value with
  | .object, .i32 handle
  | .tagged, .i32 handle
  | .tobject, .i32 handle
  | .erased, .i32 handle
  | .reuseToken, .i32 handle =>
      match table.decodeAs kind handle with
      | .ok value => .ok value
      | .error error => .error error.toTargetFailure
  | .uint8, .i32 value =>
      if value.toNat ≤ 255 then
        .ok (.scalar (.uint8 (UInt8.ofNat value.toNat)))
      else
        .error (.abiKindMismatch kind)
  | .uint16, .i32 value =>
      if value.toNat ≤ 65535 then
        .ok (.scalar (.uint16 (UInt16.ofNat value.toNat)))
      else
        .error (.abiKindMismatch kind)
  | .uint32, .i32 value => .ok (.scalar (.uint32 value))
  | .uint64, .i64 value => .ok (.scalar (.uint64 value))
  | .usize, .i64 value => .ok (.usize value)
  | _, _ => .error (.abiKindMismatch kind)

/-- Encode one FIR value, threading the alias-preserving handle table when needed. -/
def encodeValue (table : HandleTable) (kind : AbiKind) (value : Value) :
    Except TargetFailure (HandleTable × Wasm.Value) :=
  match kind, value with
  | .object, value
  | .tagged, value
  | .tobject, value
  | .erased, value
  | .reuseToken, value =>
      match table.encode kind value with
      | .ok (table, handle) => .ok (table, .i32 handle)
      | .error error => .error error.toTargetFailure
  | .uint8, .scalar (.uint8 value) =>
      .ok (table, .i32 (UInt32.ofNat value.toNat))
  | .uint16, .scalar (.uint16 value) =>
      .ok (table, .i32 (UInt32.ofNat value.toNat))
  | .uint32, .scalar (.uint32 value) => .ok (table, .i32 value)
  | .uint64, .scalar (.uint64 value) => .ok (table, .i64 value)
  | .usize, .usize value => .ok (table, .i64 value)
  | _, _ => .error (.abiKindMismatch kind)

private def decodeValueList (table : HandleTable) :
    List AbiKind → List Wasm.Value → Except TargetFailure (List Value)
  | [], [] => .ok []
  | kind :: kinds, value :: values => do
      let value ← decodeValue table kind value
      return value :: (← decodeValueList table kinds values)
  | kinds, values => .error (.arityMismatch kinds.length values.length)

/-- Decode a complete host argument vector, rejecting both wrong arity and wrong lanes. -/
def decodeArgs (table : HandleTable) (kinds : Array AbiKind) (values : List Wasm.Value) :
    Except TargetFailure (Array Value) := do
  if kinds.size != values.length then
    throw (.arityMismatch kinds.size values.length)
  return (← decodeValueList table kinds.toList values).toArray

private def encodeValueList (table : HandleTable) :
    List AbiKind → List Value → Except TargetFailure (HandleTable × List Wasm.Value)
  | [], [] => .ok (table, [])
  | kind :: kinds, value :: values => do
      let (table, value) ← encodeValue table kind value
      let (table, values) ← encodeValueList table kinds values
      return (table, value :: values)
  | kinds, values => .error (.arityMismatch kinds.length values.length)

/-- Encode a complete host result vector and retain all newly allocated handles. -/
def encodeResults (table : HandleTable) (kinds : Array AbiKind) (values : Array Value) :
    Except TargetFailure (HandleTable × List Wasm.Value) := do
  if kinds.size != values.size then
    throw (.arityMismatch kinds.size values.size)
  encodeValueList table kinds.toList values.toList

@[simp] theorem decodeArgs_empty (table : HandleTable) :
    decodeArgs table #[] [] = .ok #[] := by
  rfl

@[simp] theorem encodeResults_empty (table : HandleTable) :
    encodeResults table #[] #[] = .ok (table, []) := by
  rfl

theorem encodeResults_handle_singleton_of_encode
    {before after : HandleTable} {kind : AbiKind} {value : Value} {handle : Handle}
    (usesHandle : kind.usesHandle = true)
    (encoded : before.encode kind value = .ok (after, handle)) :
    encodeResults before #[kind] #[value] = .ok (after, [.i32 handle]) := by
  cases kind <;> simp_all [AbiKind.usesHandle, encodeResults, encodeValueList, encodeValue]
  all_goals rfl

theorem encodeResults_tobject_singleton_of_encode
    {before after : HandleTable} {value : Value} {handle : Handle}
    (encoded : before.encode .tobject value = .ok (after, handle)) :
    encodeResults before #[.tobject] #[value] = .ok (after, [.i32 handle]) := by
  simp [encodeResults, encodeValueList, encodeValue, encoded]
  rfl

theorem encodeResults_object_singleton_of_encode
    {before after : HandleTable} {value : Value} {handle : Handle}
    (encoded : before.encode .object value = .ok (after, handle)) :
    encodeResults before #[.object] #[value] = .ok (after, [.i32 handle]) := by
  simp [encodeResults, encodeValueList, encodeValue, encoded]
  rfl

/-- A successful direct-value encoding lifts to the singleton result vector
without making any assumptions about whether the ABI lane uses a handle. -/
theorem encodeResults_singleton_of_encodeValue
    {before after : HandleTable} {kind : AbiKind} {value : Value}
    {physical : Wasm.Value}
    (encoded : encodeValue before kind value = .ok (after, physical)) :
    encodeResults before #[kind] #[value] = .ok (after, [physical]) := by
  simp [encodeResults, encodeValueList, encoded]
  rfl

@[simp] theorem encodeResults_uint32_singleton (table : HandleTable) (value : UInt32) :
    encodeResults table #[.uint32] #[.scalar (.uint32 value)] =
      .ok (table, [.i32 value]) := by
  simp [encodeResults, encodeValueList, encodeValue]
  rfl

/-- Proof-side relation for a successful single-value decode. -/
def DecodesValue (table : HandleTable) (kind : AbiKind) (physical : Wasm.Value)
    (semantic : Value) : Prop :=
  decodeValue table kind physical = .ok semantic

/-- A related physical value is exactly a successful singleton ABI decode. -/
theorem decodeArgs_singleton_of_decodesValue
    {table : HandleTable} {kind : AbiKind} {physical : Wasm.Value}
    {semantic : Value}
    (decoded : DecodesValue table kind physical semantic) :
    decodeArgs table #[kind] [physical] = .ok #[semantic] := by
  change decodeValue table kind physical = .ok semantic at decoded
  simp [decodeArgs, decodeValueList, decoded]
  rfl

/-- Proof-side relation for a successful single-value encode. -/
def EncodesValue (before after : HandleTable) (kind : AbiKind) (semantic : Value)
    (physical : Wasm.Value) : Prop :=
  encodeValue before kind semantic = .ok (after, physical)

end FirTalos
