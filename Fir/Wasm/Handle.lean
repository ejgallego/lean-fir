import Fir.Wasm.ABI
import Fir.LeanIR.Runtime

namespace Fir.Wasm

open Fir.LeanIR.Impure

/-- Handle zero is reserved for erased/null-like ABI sentinels. -/
abbrev Handle := UInt32

def reservedHandle : Handle := 0

def firstHandle : Nat := 1

def maxHandle : Nat := 4294967295

inductive HandleError where
  | kindDoesNotUseHandles (kind : AbiKind)
  | valueKindMismatch (kind : AbiKind) (value : Value)
  | invalidSentinel (kind : AbiKind) (handle : Handle)
  | invalidNextHandle (next : Nat)
  | handleSpaceExhausted
  | unknownHandle (handle : Handle)
  deriving Inhabited, BEq, Repr

/-- Failures introduced by the semantic target boundary rather than by FIR evaluation. -/
inductive TargetFailure where
  | invalidHandle (handle : Handle)
  | handleSpaceExhausted
  | invalidHandleTable (next : Nat)
  | abiKindMismatch (kind : AbiKind)
  deriving Inhabited, BEq, Repr

/-- A trap retains whether the fault came from source semantics or target machinery. -/
inductive StructuredTrap where
  | source (fault : RuntimeFault)
  | target (failure : TargetFailure)
  deriving Inhabited, BEq, Repr

def HandleError.toTargetFailure : HandleError → TargetFailure
  | .unknownHandle handle => .invalidHandle handle
  | .handleSpaceExhausted => .handleSpaceExhausted
  | .invalidNextHandle next => .invalidHandleTable next
  | .kindDoesNotUseHandles kind | .valueKindMismatch kind _
  | .invalidSentinel kind _ => .abiKindMismatch kind

def AbiKind.usesHandle : AbiKind → Bool
  | .object | .tagged | .tobject | .reuseToken => true
  | .erased | .uint8 | .uint16 | .uint32 | .uint64 | .usize | .float32 | .float => false

def AbiKind.acceptsValue : AbiKind → Value → Bool
  | .object, .object (.heap _) => true
  | .tagged, .object (.tagged _) => true
  | .tobject, .object _ => true
  | .erased, .erased => true
  | .reuseToken, .reuseToken _ => true
  | .uint8, .scalar (.uint8 _) => true
  | .uint16, .scalar (.uint16 _) => true
  | .uint32, .scalar (.uint32 _) => true
  | .uint64, .scalar (.uint64 _) => true
  | .usize, .usize _ => true
  | _, _ => false

/--
An alias-preserving table for values represented as opaque `i32` handles.
`next` is a natural number so exhaustion is detected before conversion to
`UInt32`, rather than being hidden by wraparound.
-/
structure HandleTable where
  entries : List (Handle × Value) := []
  next : Nat := firstHandle
  deriving Inhabited, BEq, Repr

/-- State threaded by the future Talos semantic hosts. -/
structure RuntimeHost where
  runtime : RuntimeState := {}
  handles : HandleTable := {}
  fault? : Option RuntimeFault := none
  deriving Inhabited, BEq

def HandleTable.lookup? : List (Handle × Value) → Handle → Option Value
  | [], _ => none
  | (candidate, value) :: rest, handle =>
      if candidate == handle then some value else lookup? rest handle

def HandleTable.findHandle? : List (Handle × Value) → Value → Option Handle
  | [], _ => none
  | (handle, candidate) :: rest, value =>
      if candidate == value then some handle else findHandle? rest value

def HandleTable.decode (table : HandleTable) (handle : Handle) : Except HandleError Value :=
  if handle == reservedHandle then
    .error (.unknownHandle handle)
  else
    match lookup? table.entries handle with
    | some value => .ok value
    | none => .error (.unknownHandle handle)

def HandleTable.decodeAs (table : HandleTable) (kind : AbiKind) (handle : Handle) :
    Except HandleError Value := do
  if kind == .erased then
    if handle == reservedHandle then
      return .erased
    else
      throw (.invalidSentinel kind handle)
  unless kind.usesHandle do
    throw (.kindDoesNotUseHandles kind)
  let value ← table.decode handle
  unless kind.acceptsValue value do
    throw (.valueKindMismatch kind value)
  return value

def HandleTable.encode (table : HandleTable) (kind : AbiKind) (value : Value) :
    Except HandleError (HandleTable × Handle) := do
  if kind == .erased then
    if value == .erased then
      return (table, reservedHandle)
    else
      throw (.valueKindMismatch kind value)
  unless kind.usesHandle do
    throw (.kindDoesNotUseHandles kind)
  unless kind.acceptsValue value do
    throw (.valueKindMismatch kind value)
  match findHandle? table.entries value with
  | some handle => return (table, handle)
  | none =>
      if table.next < firstHandle then
        throw (.invalidNextHandle table.next)
      else if table.next > maxHandle then
        throw .handleSpaceExhausted
      else
        let handle := UInt32.ofNat table.next
        return ({ entries := (handle, value) :: table.entries, next := table.next + 1 }, handle)

/-- The relational form used by host-runtime refinement statements. -/
def HandleTable.Encodes (table : HandleTable) (kind : AbiKind) (handle : Handle)
    (value : Value) : Prop :=
  table.decodeAs kind handle = .ok value

theorem HandleTable.decode_of_encodes {table : HandleTable} {kind : AbiKind}
    {handle : Handle} {value : Value} (encoding : table.Encodes kind handle value) :
    table.decodeAs kind handle = .ok value :=
  encoding

@[simp] theorem HandleTable.decode_reserved (table : HandleTable) :
    table.decode reservedHandle = .error (.unknownHandle reservedHandle) := by
  simp [HandleTable.decode, reservedHandle]

end Fir.Wasm
