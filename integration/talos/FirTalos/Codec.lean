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

/-- Proof-side relation for a successful single-value decode. -/
def DecodesValue (table : HandleTable) (kind : AbiKind) (physical : Wasm.Value)
    (semantic : Value) : Prop :=
  decodeValue table kind physical = .ok semantic

/-- Proof-side relation for a successful single-value encode. -/
def EncodesValue (before after : HandleTable) (kind : AbiKind) (semantic : Value)
    (physical : Wasm.Value) : Prop :=
  encodeValue before kind semantic = .ok (after, physical)

end FirTalos
