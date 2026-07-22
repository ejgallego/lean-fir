import FirTalos.Adapter
import FirTalos.Codec
import Fir.LeanIR.Interpreter
import Interpreter.Wasm.Host

namespace FirTalos

open Fir.Wasm
open Fir.LeanIR.Impure

/-- Source-level identity and ABI metadata for one imported Lean declaration. -/
structure ExternalOperation where
  name : Lean.Name
  paramTypes : Array Lean.Expr
  resultType : Lean.Expr
  signature : Signature
  deriving Inhabited, BEq

/-- The deliberately small semantic-runtime fragment enabled by W2. -/
inductive HostOperation where
  | naturalLiteral (value : Nat) (result : AbiKind)
  | stringLiteral (value : String) (result : AbiKind)
  | allocCtor (info : Lean.Compiler.LCNF.CtorInfo) (fields : Array AbiKind)
      (result : AbiKind)
  | objectProj (index : Nat) (result : AbiKind)
  | usizeProj (index : Nat)
  | scalarProj (width offset : Nat) (result : AbiKind)
  | cacheSet (declaration : Lean.Name) (value : AbiKind)
  | partialApply (function : Lean.Name) (arity fixed : Nat)
      (fields : Array AbiKind) (result : AbiKind)
  | closureMatches (function : Lean.Name) (arity fixed : Nat)
  | closureProj (function : Lean.Name) (arity fixed index : Nat)
      (result : AbiKind)
  | box (scalar result : AbiKind)
  | unbox (scalar : AbiKind)
  | isShared
  | reset (objectFields : Nat)
  | reuse (info : Lean.Compiler.LCNF.CtorInfo) (updateHeader : Bool)
      (fields : Array AbiKind) (result : AbiKind)
  | objectSet (index : Nat) (field : AbiKind)
  | usizeSet (index : Nat)
  | scalarSet (width offset : Nat) (field : AbiKind)
  | setTag (tag : Nat)
  | inc (amount : Nat) (check : Bool)
  | dec (amount : Nat) (check : Bool) (objectFields? : Option Nat)
  | delete
  | getTag
  | external (operation : ExternalOperation)
  deriving Inhabited, BEq

def HostOperation.runtimeOp : HostOperation → Option RuntimeOp
  | .naturalLiteral value result => some (.literal (.nat value) result)
  | .stringLiteral value result => some (.literal (.str value) result)
  | .allocCtor info fields result => some (.allocCtor info fields result)
  | .objectProj index result => some (.objectProj index result)
  | .usizeProj index => some (.usizeProj index)
  | .scalarProj width offset result => some (.scalarProj width offset result)
  | .cacheSet declaration value => some (.cacheSet declaration value)
  | .partialApply function arity fixed fields result =>
      some (.partialApply function arity fixed fields result)
  | .closureMatches function arity fixed =>
      some (.closureMatches function arity fixed)
  | .closureProj function arity fixed index result =>
      some (.closureProj function arity fixed index result)
  | .box scalar result => some (.box scalar result)
  | .unbox scalar => some (.unbox scalar)
  | .isShared => some .isShared
  | .reset objectFields => some (.reset objectFields)
  | .reuse info updateHeader fields result =>
      some (.reuse info updateHeader fields result)
  | .objectSet index field => some (.objectSet index field)
  | .usizeSet index => some (.usizeSet index)
  | .scalarSet width offset field => some (.scalarSet width offset field)
  | .setTag tag => some (.setTag tag)
  | .inc amount check => some (.inc amount check)
  | .dec amount check objectFields? => some (.dec amount check objectFields?)
  | .delete => some .delete
  | .getTag => some .getTag
  | .external _ => none

def HostOperation.signature : HostOperation → Signature
  | .external operation => operation.signature
  | operation => operation.runtimeOp.getD .getTag |>.signature

def HostOperation.ofRuntime? : RuntimeOp → Option HostOperation
  | .literal (.nat value) result => some (.naturalLiteral value result)
  | .literal (.str value) result => some (.stringLiteral value result)
  | .allocCtor info fields result => some (.allocCtor info fields result)
  | .objectProj index result => some (.objectProj index result)
  | .usizeProj index => some (.usizeProj index)
  | .scalarProj width offset result => some (.scalarProj width offset result)
  | .cacheSet declaration value => some (.cacheSet declaration value)
  | .partialApply function arity fixed fields result =>
      some (.partialApply function arity fixed fields result)
  | .closureMatches function arity fixed =>
      some (.closureMatches function arity fixed)
  | .closureProj function arity fixed index result =>
      some (.closureProj function arity fixed index result)
  | .box scalar result => some (.box scalar result)
  | .unbox scalar => some (.unbox scalar)
  | .isShared => some .isShared
  | .reset objectFields => some (.reset objectFields)
  | .reuse info updateHeader fields result =>
      some (.reuse info updateHeader fields result)
  | .objectSet index field => some (.objectSet index field)
  | .usizeSet index => some (.usizeSet index)
  | .scalarSet width offset field => some (.scalarSet width offset field)
  | .setTag tag => some (.setTag tag)
  | .inc amount check => some (.inc amount check)
  | .dec amount check objectFields? => some (.dec amount check objectFields?)
  | .delete => some .delete
  | .getTag => some .getTag
  | _ => none

/-- Recover the exact canonical impure type retained by integer boxing.
Floating-point kinds stay unavailable until the shared runtime grows matching
`ScalarValue` constructors. -/
def runtimeScalarType? : AbiKind → Option Lean.Expr
  | .uint8 => some Lean.Compiler.LCNF.ImpureType.uint8
  | .uint16 => some Lean.Compiler.LCNF.ImpureType.uint16
  | .uint32 => some Lean.Compiler.LCNF.ImpureType.uint32
  | .uint64 => some Lean.Compiler.LCNF.ImpureType.uint64
  | .usize => some Lean.Compiler.LCNF.ImpureType.usize
  | _ => none

def structuredTrapMessage : StructuredTrap → String
  | .source fault => s!"FIR source fault: {repr fault}"
  | .target failure => s!"FIR target failure: {repr failure}"

def ExternalOperation.request (operation : ExternalOperation)
    (args : Array Value) : ExternalRequest := {
  name := operation.name
  paramTypes := operation.paramTypes
  resultType := operation.resultType
  args }

/-- Apply a successful foreign response exactly as `resumeExternal` does on
the source interpreter side. -/
def applyExternalResponse (request : ExternalRequest) (runtime : RuntimeState)
    (response : ExternalResponse) : RuntimeState :=
  let waiting : MachineState := {
    program := { decls := #[] }
    control := .yielded .erased
    runtime }
  (resumeExternal request waiting response).runtime

private def clearTrapState (store : Wasm.Store RuntimeHost) : Wasm.Store RuntimeHost :=
  { store with host := { store.host with fault? := none, targetFailure? := none } }

private def sourceTrap (store : Wasm.Store RuntimeHost) (fault : RuntimeFault) :
    Wasm.HostResult RuntimeHost :=
  let store := { store with host := { store.host with fault? := some fault } }
  .Trap store (structuredTrapMessage (.source fault))

private def targetTrap (store : Wasm.Store RuntimeHost) (failure : TargetFailure) :
    Wasm.HostResult RuntimeHost :=
  let store := { store with host := { store.host with targetFailure? := some failure } }
  .Trap store (structuredTrapMessage (.target failure))

def closureData (runtime : RuntimeState) (value : Value) :
    Except RuntimeFault (Lean.Name × Nat × Array Value) := do
  let .object (.heap location) := value | throw .expectedClosure
  let cell ← getLiveCell runtime location
  let .closure function arity fixed := cell.object | throw .expectedClosure
  return (function, arity, fixed)

private def evaluate (operation : HostOperation) (runtime : RuntimeState)
    (externals : ExternalImpl) (args : Array Value) :
    Except StructuredTrap (RuntimeState × Array Value) :=
  match operation with
  | .naturalLiteral value _ =>
      let (runtime, value) := literal runtime (.nat value)
      .ok (runtime, #[value])
  | .stringLiteral value _ =>
      let (runtime, value) := literal runtime (.str value)
      .ok (runtime, #[value])
  | .allocCtor info _ _ =>
      match allocCtor runtime info args with
      | .ok (runtime, value) => .ok (runtime, #[value])
      | .error fault => .error (.source fault)
  | .objectProj index _ =>
      match args[0]? with
      | some object =>
          match getObjectField runtime object index with
          | .ok value => .ok (runtime, #[value])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .usizeProj index =>
      match args[0]? with
      | some object =>
          match getUSizeSlot runtime object index with
          | .ok value => .ok (runtime, #[value])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .scalarProj width offset _ =>
      match args[0]? with
      | some object =>
          match getScalarField runtime object width offset with
          | .ok value => .ok (runtime, #[value])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .cacheSet declaration _ =>
      match args[0]? with
      | some value => .ok (runtime.setGlobal declaration value, #[value])
      | none => .error (.target (.arityMismatch 1 args.size))
  | .partialApply function arity _ _ _ =>
      let (runtime, reference) := alloc runtime (.closure function arity args)
      .ok (runtime, #[.object reference])
  | .closureMatches function arity fixed =>
      match args[0]? with
      | some closure =>
          match closureData runtime closure with
          | .ok (actualFunction, actualArity, actualFixed) =>
              let isMatch := actualFunction == function && actualArity == arity &&
                actualFixed.size == fixed
              .ok (runtime, #[.scalar (.uint32 (if isMatch then 1 else 0))])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .closureProj function arity fixed index _ =>
      match args[0]? with
      | some closure =>
          match closureData runtime closure with
          | .ok (actualFunction, actualArity, actualFixed) =>
              if actualFunction != function || actualArity != arity ||
                  actualFixed.size != fixed then
                .error (.target .closureMetadataMismatch)
              else
                match actualFixed[index]? with
                | some value => .ok (runtime, #[value])
                | none => .error (.target (.arityMismatch (index + 1) actualFixed.size))
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .box scalar _ =>
      match runtimeScalarType? scalar, args[0]? with
      | some type, some value =>
          match Fir.LeanIR.Impure.box runtime type value with
          | .ok result => .ok (result.1, #[result.2])
          | .error fault => .error (.source fault)
      | none, _ => .error (.target (.abiKindMismatch scalar))
      | _, none => .error (.target (.arityMismatch 1 args.size))
  | .unbox scalar =>
      match runtimeScalarType? scalar, args[0]? with
      | some type, some value =>
          match Fir.LeanIR.Impure.unbox runtime type value with
          | .ok value => .ok (runtime, #[value])
          | .error fault => .error (.source fault)
      | none, _ => .error (.target (.abiKindMismatch scalar))
      | _, none => .error (.target (.arityMismatch 1 args.size))
  | .isShared =>
      match args[0]? with
      | some object =>
          match Fir.LeanIR.Impure.isShared runtime object with
          | .ok value => .ok (runtime, #[value])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .reset objectFields =>
      match args[0]? with
      | some object =>
          match Fir.LeanIR.Impure.reset runtime objectFields object with
          | .ok result => .ok (result.1, #[result.2])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .reuse info updateHeader _ _ =>
      match args[0]? with
      | some token =>
          match Fir.LeanIR.Impure.reuse runtime token info updateHeader
              (args.extract 1 args.size) with
          | .ok result => .ok (result.1, #[result.2])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .objectSet index _ =>
      match args[0]?, args[1]? with
      | some object, some field =>
          match setObjectField runtime object index field with
          | .ok runtime => .ok (runtime, #[])
          | .error fault => .error (.source fault)
      | _, _ => .error (.target (.arityMismatch 2 args.size))
  | .usizeSet index =>
      match args[0]?, args[1]? with
      | some object, some field =>
          match setUSizeSlot runtime object index field with
          | .ok runtime => .ok (runtime, #[])
          | .error fault => .error (.source fault)
      | _, _ => .error (.target (.arityMismatch 2 args.size))
  | .scalarSet width offset _ =>
      match args[0]?, args[1]? with
      | some object, some field =>
          match setScalarField runtime object width offset field with
          | .ok runtime => .ok (runtime, #[])
          | .error fault => .error (.source fault)
      | _, _ => .error (.target (.arityMismatch 2 args.size))
  | .setTag tag =>
      match args[0]? with
      | some object =>
          match Fir.LeanIR.Impure.setTag runtime object tag with
          | .ok runtime => .ok (runtime, #[])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .inc amount check =>
      match args[0]? with
      | some object =>
          match incValue runtime object amount check with
          | .ok runtime => .ok (runtime, #[])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .dec amount check _ =>
      match args[0]? with
      | some object =>
          match decValue runtime object amount check with
          | .ok runtime => .ok (runtime, #[])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .delete =>
      match args[0]? with
      | some object =>
          match deleteValue runtime object with
          | .ok runtime => .ok (runtime, #[])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .getTag =>
      match args[0]? with
      | some object =>
          match getTag runtime object with
          | .ok tag => .ok (runtime, #[.scalar (.uint32 (UInt32.ofNat tag))])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))
  | .external operation =>
      let request := operation.request args
      match externals.call request runtime with
      | .error fault => .error (.source fault)
      | .ok response =>
          let runtime := applyExternalResponse request runtime response
          match operation.signature.results.size with
          | 0 => .ok (runtime, #[])
          | 1 => .ok (runtime, #[response.value])
          | count => .error (.target (.arityMismatch 1 count))

/--
Decode one host call, retaining the operation-specific erased sentinel accepted
by `delete`. Ordinary `.object` decoding remains heap-only; physical zero is
recognized here only because `ExpandResetReuse` can retain `del` on its
failed-reset path.
 -/
@[simp] def decodeHostArgs (operation : HostOperation) (table : HandleTable)
    (physicalArgs : List Wasm.Value) : Except TargetFailure (Array Value) :=
  match operation, physicalArgs with
  | .delete, [.i32 handle] =>
      if handle == reservedHandle then .ok #[.erased]
      else decodeArgs table #[.object] physicalArgs
  | _, _ => decodeArgs table operation.signature.params physicalArgs

/-- The semantic host step, factored independently from Talos's `HostFn` record. -/
def hostStep (operation : HostOperation) (initial : Wasm.Store RuntimeHost)
    (physicalArgs : List Wasm.Value) : Wasm.HostResult RuntimeHost :=
  let initial := clearTrapState initial
  match decodeHostArgs operation initial.host.handles physicalArgs with
  | .error failure => targetTrap initial failure
  | .ok args =>
      match evaluate operation initial.host.runtime initial.host.externals args with
      | .error (.source fault) => sourceTrap initial fault
      | .error (.target failure) => targetTrap initial failure
      | .ok (runtime, results) =>
          let evaluated := { initial with host := { initial.host with runtime } }
          match encodeResults evaluated.host.handles operation.signature.results results with
          | .error failure => targetTrap evaluated failure
          | .ok (handles, results) =>
              .Return results { evaluated with host := { evaluated.host with handles } }

theorem hostStep_external_singleton_of_decode_call_encode
    (operation : ExternalOperation) (resultKind : AbiKind)
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (semanticArgs : Array Value) (response : ExternalResponse)
    {after : HandleTable} {physicalResult : Wasm.Value}
    (resultSignature : operation.signature.results = #[resultKind])
    (decoded :
      decodeArgs initial.host.handles operation.signature.params physicalArgs =
        .ok semanticArgs)
    (called : initial.host.externals.call (operation.request semanticArgs)
      initial.host.runtime = .ok response)
    (encoded : encodeValue initial.host.handles resultKind response.value =
      .ok (after, physicalResult)) :
    hostStep (.external operation) initial physicalArgs =
      .Return [physicalResult] {
        initial with host := {
          initial.host with
          runtime := applyExternalResponse (operation.request semanticArgs)
            initial.host.runtime response
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    resultSignature, decoded, called,
    encodeResults_singleton_of_encodeValue encoded]

theorem hostStep_cacheSet_of_decode_encode
    (declaration : Lean.Name) (kind : AbiKind)
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (sourceValue : Value) {after : HandleTable} {physicalResult : Wasm.Value}
    (decoded : decodeArgs initial.host.handles #[kind] physicalArgs =
      .ok #[sourceValue])
    (encoded : encodeValue initial.host.handles kind sourceValue =
      .ok (after, physicalResult)) :
    hostStep (.cacheSet declaration kind) initial physicalArgs =
      .Return [physicalResult] {
        initial with host := {
          initial.host with
          runtime := initial.host.runtime.setGlobal declaration sourceValue
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded,
    encodeResults_singleton_of_encodeValue encoded]

theorem hostStep_partialApply_of_decode_encode
    (function : Lean.Name) (arity fixed : Nat) (fieldKinds : Array AbiKind)
    (resultKind : AbiKind) (initial : Wasm.Store RuntimeHost)
    (physicalArgs : List Wasm.Value) (semanticArgs : Array Value)
    (sourceRuntime : RuntimeState) (reference : ObjectRef)
    {after : HandleTable} {handle : Handle}
    (decoded : decodeArgs initial.host.handles fieldKinds physicalArgs =
      .ok semanticArgs)
    (allocated : alloc initial.host.runtime (.closure function arity semanticArgs) =
      (sourceRuntime, reference))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind (.object reference) =
      .ok (after, handle)) :
    hostStep (.partialApply function arity fixed fieldKinds resultKind)
        initial physicalArgs =
      .Return [.i32 handle] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, allocated,
    encodeResults_handle_singleton_of_encode usesHandle encoded]

theorem hostStep_closureMatches_of_decode_read
    (function : Lean.Name) (arity fixed : Nat)
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (closure : Value) (captured : Array Value)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[closure])
    (read : closureData initial.host.runtime closure =
      .ok (function, arity, captured))
    (fixedSize : captured.size = fixed) :
    hostStep (.closureMatches function arity fixed) initial physicalArgs =
      .Return [.i32 1] {
        initial with host := {
          initial.host with
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, read, fixedSize,
    encodeResults_singleton_of_encodeValue (by rfl :
      encodeValue initial.host.handles .uint32 (.scalar (.uint32 1)) =
        .ok (initial.host.handles, .i32 1))]

theorem hostStep_closureProj_of_decode_read_encode
    (function : Lean.Name) (arity fixed index : Nat) (resultKind : AbiKind)
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (closure sourceValue : Value) (captured : Array Value)
    {after : HandleTable} {physicalResult : Wasm.Value}
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[closure])
    (read : closureData initial.host.runtime closure =
      .ok (function, arity, captured))
    (fixedSize : captured.size = fixed)
    (projected : captured[index]? = some sourceValue)
    (encoded : encodeValue initial.host.handles resultKind sourceValue =
      .ok (after, physicalResult)) :
    hostStep (.closureProj function arity fixed index resultKind)
        initial physicalArgs =
      .Return [physicalResult] {
        initial with host := {
          initial.host with
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, read, fixedSize,
    projected, encodeResults_singleton_of_encodeValue encoded]

theorem hostStep_naturalLiteral_of_encode
    (initial : Wasm.Store RuntimeHost) (value : Nat) {after : HandleTable}
    {handle : Handle}
    (encoded :
      initial.host.handles.encode .tobject (literal initial.host.runtime (.nat value)).2 =
        .ok (after, handle)) :
    hostStep (.naturalLiteral value .tobject) initial [] =
      .Return [.i32 handle] {
        initial with host := {
          initial.host with
          runtime := (literal initial.host.runtime (.nat value)).1
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature,
    encodeResults_tobject_singleton_of_encode encoded]

theorem hostStep_stringLiteral_of_encode
    (initial : Wasm.Store RuntimeHost) (value : String) {after : HandleTable}
    {handle : Handle}
    (encoded :
      initial.host.handles.encode .object (literal initial.host.runtime (.str value)).2 =
        .ok (after, handle)) :
    hostStep (.stringLiteral value .object) initial [] =
      .Return [.i32 handle] {
        initial with host := {
          initial.host with
          runtime := (literal initial.host.runtime (.str value)).1
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature,
    encodeResults_object_singleton_of_encode encoded]

theorem hostStep_allocCtor_of_decode_encode
    (initial : Wasm.Store RuntimeHost) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (semanticArgs : Array Value)
    (sourceRuntime : RuntimeState) (sourceValue : Value) {after : HandleTable}
    {handle : Handle}
    (decoded : decodeArgs initial.host.handles fieldKinds physicalArgs = .ok semanticArgs)
    (allocated : allocCtor initial.host.runtime info semanticArgs =
      .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, handle)) :
    hostStep (.allocCtor info fieldKinds resultKind) initial physicalArgs =
      .Return [.i32 handle] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, allocated,
    encodeResults_handle_singleton_of_encode usesHandle encoded]

theorem hostStep_objectProj_of_decode_encode
    (initial : Wasm.Store RuntimeHost) (index : Nat) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (sourceObject sourceValue : Value)
    {after : HandleTable} {handle : Handle}
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (projected : getObjectField initial.host.runtime sourceObject index = .ok sourceValue)
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, handle)) :
    hostStep (.objectProj index resultKind) initial physicalArgs =
      .Return [.i32 handle] {
        initial with host := {
          initial.host with
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, projected,
    encodeResults_handle_singleton_of_encode usesHandle encoded]

theorem hostStep_usizeProj_of_decode
    (initial : Wasm.Store RuntimeHost) (index : Nat)
    (physicalArgs : List Wasm.Value) (sourceObject : Value) (value : UInt64)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (projected : getUSizeSlot initial.host.runtime sourceObject index =
      .ok (.usize value)) :
    hostStep (.usizeProj index) initial physicalArgs =
      .Return [.i64 value] {
        initial with host := {
          initial.host with
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, projected,
    encodeResults_singleton_of_encodeValue (by rfl :
      encodeValue initial.host.handles .usize (.usize value) =
        .ok (initial.host.handles, .i64 value))]

theorem hostStep_scalarProj_of_decode_encode
    (initial : Wasm.Store RuntimeHost) (width offset : Nat)
    (resultKind : AbiKind) (physicalArgs : List Wasm.Value)
    (sourceObject sourceValue : Value) (physical : Wasm.Value)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (projected : getScalarField initial.host.runtime sourceObject width offset =
      .ok sourceValue)
    (encoded : encodeValue initial.host.handles resultKind sourceValue =
      .ok (initial.host.handles, physical)) :
    hostStep (.scalarProj width offset resultKind) initial physicalArgs =
      .Return [physical] {
        initial with host := {
          initial.host with
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, projected,
    encodeResults_singleton_of_encodeValue encoded]

theorem hostStep_box_of_decode_encode
    (initial : Wasm.Store RuntimeHost) (scalarKind resultKind : AbiKind)
    (type : Lean.Expr) (physicalArgs : List Wasm.Value) (sourceScalar : Value)
    (sourceRuntime : RuntimeState) (sourceValue : Value)
    {after : HandleTable} {handle : Handle}
    (typeEq : runtimeScalarType? scalarKind = some type)
    (decoded : decodeArgs initial.host.handles #[scalarKind] physicalArgs =
      .ok #[sourceScalar])
    (boxed : Fir.LeanIR.Impure.box initial.host.runtime type sourceScalar =
      .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, handle)) :
    hostStep (.box scalarKind resultKind) initial physicalArgs =
      .Return [.i32 handle] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, typeEq, decoded, boxed,
    encodeResults_handle_singleton_of_encode usesHandle encoded]

theorem hostStep_unbox_of_decode_encode
    (initial : Wasm.Store RuntimeHost) (scalarKind : AbiKind) (type : Lean.Expr)
    (physicalArgs : List Wasm.Value) (sourceObject sourceValue : Value)
    (physical : Wasm.Value)
    (typeEq : runtimeScalarType? scalarKind = some type)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (unboxed : Fir.LeanIR.Impure.unbox initial.host.runtime type sourceObject =
      .ok sourceValue)
    (encoded : encodeValue initial.host.handles scalarKind sourceValue =
      .ok (initial.host.handles, physical)) :
    hostStep (.unbox scalarKind) initial physicalArgs =
      .Return [physical] {
        initial with host := {
          initial.host with
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, typeEq, decoded, unboxed,
    encodeResults_singleton_of_encodeValue encoded]

theorem hostStep_isShared_of_decode
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (sourceObject : Value) (shared : UInt8)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (evaluated : Fir.LeanIR.Impure.isShared initial.host.runtime sourceObject =
      .ok (.scalar (.uint8 shared))) :
    hostStep .isShared initial physicalArgs =
      .Return [.i32 (UInt32.ofNat shared.toNat)] {
        initial with host := {
          initial.host with
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, evaluated,
    encodeResults_singleton_of_encodeValue (by rfl :
      encodeValue initial.host.handles .uint8 (.scalar (.uint8 shared)) =
        .ok (initial.host.handles, .i32 (UInt32.ofNat shared.toNat)))]

theorem hostStep_reset_of_decode_encode
    (initial : Wasm.Store RuntimeHost) (objectFields : Nat)
    (physicalArgs : List Wasm.Value) (sourceObject : Value)
    (sourceRuntime : RuntimeState) (sourceToken : Value)
    {after : HandleTable} {handle : Handle}
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (resetResult : Fir.LeanIR.Impure.reset initial.host.runtime objectFields
      sourceObject = .ok (sourceRuntime, sourceToken))
    (encoded : initial.host.handles.encode .reuseToken sourceToken =
      .ok (after, handle)) :
    hostStep (.reset objectFields) initial physicalArgs =
      .Return [.i32 handle] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, resetResult,
    encodeResults_handle_singleton_of_encode (by rfl) encoded]

theorem hostStep_reuse_of_decode_encode
    (initial : Wasm.Store RuntimeHost) (info : Lean.Compiler.LCNF.CtorInfo)
    (updateHeader : Bool) (fieldKinds : Array AbiKind) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (semanticArgs : Array Value)
    (sourceToken : Value) (sourceRuntime : RuntimeState) (sourceValue : Value)
    {after : HandleTable} {handle : Handle}
    (decoded : decodeArgs initial.host.handles (#[.reuseToken] ++ fieldKinds)
      physicalArgs = .ok semanticArgs)
    (tokenHead : semanticArgs[0]? = some sourceToken)
    (reused : Fir.LeanIR.Impure.reuse initial.host.runtime sourceToken info
      updateHeader (semanticArgs.extract 1 semanticArgs.size) =
        .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, handle)) :
    hostStep (.reuse info updateHeader fieldKinds resultKind) initial physicalArgs =
      .Return [.i32 handle] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          handles := after
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, tokenHead, reused,
    encodeResults_handle_singleton_of_encode usesHandle encoded]

theorem hostStep_objectSet_of_decode
    (initial : Wasm.Store RuntimeHost) (index : Nat) (fieldKind : AbiKind)
    (physicalArgs : List Wasm.Value) (sourceObject sourceField : Value)
    (sourceRuntime : RuntimeState)
    (decoded : decodeArgs initial.host.handles #[.object, fieldKind] physicalArgs =
      .ok #[sourceObject, sourceField])
    (mutated : setObjectField initial.host.runtime sourceObject index sourceField =
      .ok sourceRuntime) :
    hostStep (.objectSet index fieldKind) initial physicalArgs =
      .Return [] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, mutated]

theorem hostStep_usizeSet_of_decode
    (initial : Wasm.Store RuntimeHost) (index : Nat)
    (physicalArgs : List Wasm.Value) (sourceObject sourceField : Value)
    (sourceRuntime : RuntimeState)
    (decoded : decodeArgs initial.host.handles #[.object, .usize] physicalArgs =
      .ok #[sourceObject, sourceField])
    (mutated : setUSizeSlot initial.host.runtime sourceObject index sourceField =
      .ok sourceRuntime) :
    hostStep (.usizeSet index) initial physicalArgs =
      .Return [] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, mutated]

theorem hostStep_scalarSet_of_decode
    (initial : Wasm.Store RuntimeHost) (width offset : Nat)
    (fieldKind : AbiKind) (physicalArgs : List Wasm.Value)
    (sourceObject sourceField : Value) (sourceRuntime : RuntimeState)
    (decoded : decodeArgs initial.host.handles #[.object, fieldKind] physicalArgs =
      .ok #[sourceObject, sourceField])
    (mutated : setScalarField initial.host.runtime sourceObject width offset sourceField =
      .ok sourceRuntime) :
    hostStep (.scalarSet width offset fieldKind) initial physicalArgs =
      .Return [] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, mutated]

theorem hostStep_setTag_of_decode
    (initial : Wasm.Store RuntimeHost) (tag : Nat)
    (physicalArgs : List Wasm.Value) (sourceObject : Value)
    (sourceRuntime : RuntimeState)
    (decoded : decodeArgs initial.host.handles #[.object] physicalArgs =
      .ok #[sourceObject])
    (mutated : Fir.LeanIR.Impure.setTag initial.host.runtime sourceObject tag =
      .ok sourceRuntime) :
    hostStep (.setTag tag) initial physicalArgs =
      .Return [] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, mutated]

theorem hostStep_inc_of_decode
    (initial : Wasm.Store RuntimeHost) (amount : Nat) (check : Bool)
    (physicalArgs : List Wasm.Value) (sourceObject : Value)
    (sourceRuntime : RuntimeState)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (updated : incValue initial.host.runtime sourceObject amount check =
      .ok sourceRuntime) :
    hostStep (.inc amount check) initial physicalArgs =
      .Return [] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, updated]

theorem hostStep_dec_of_decode
    (initial : Wasm.Store RuntimeHost) (amount : Nat) (check : Bool)
    (objectFields? : Option Nat) (physicalArgs : List Wasm.Value)
    (sourceObject : Value) (sourceRuntime : RuntimeState)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (updated : decValue initial.host.runtime sourceObject amount check =
      .ok sourceRuntime) :
    hostStep (.dec amount check objectFields?) initial physicalArgs =
      .Return [] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, updated]

theorem hostStep_delete_of_decode
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (sourceObject : Value) (sourceRuntime : RuntimeState)
    (decoded : decodeArgs initial.host.handles #[.object] physicalArgs =
      .ok #[sourceObject])
    (updated : deleteValue initial.host.runtime sourceObject = .ok sourceRuntime) :
    hostStep .delete initial physicalArgs =
      .Return [] {
        initial with host := {
          initial.host with
          runtime := sourceRuntime
          fault? := none
          targetFailure? := none } } := by
  have decodedHost :
      decodeHostArgs .delete initial.host.handles physicalArgs = .ok #[sourceObject] := by
    simp only [decodeHostArgs]
    split
    · next handle =>
      have notReserved := decodeArgs_object_handle_ne_reserved decoded
      simp [notReserved, decoded]
    · simpa [HostOperation.signature, HostOperation.runtimeOp, RuntimeOp.signature]
        using decoded
  unfold hostStep
  simp only [clearTrapState]
  rw [decodedHost]
  simp [evaluate, HostOperation.signature, HostOperation.runtimeOp,
    RuntimeOp.signature, updated]

/-- Physical zero is the erased failed-reset token for `delete` only. -/
theorem hostStep_delete_erased (initial : Wasm.Store RuntimeHost) :
    hostStep .delete initial [.i32 reservedHandle] =
      .Return [] {
        initial with host := {
          initial.host with
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decodeHostArgs]

theorem hostStep_getTag_of_decode
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (sourceObject : Value) (tag : Nat)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (tagged : getTag initial.host.runtime sourceObject = .ok tag) :
    hostStep .getTag initial physicalArgs =
      .Return [.i32 (UInt32.ofNat tag)] {
        initial with host := {
          initial.host with
          fault? := none
          targetFailure? := none } } := by
  simp [hostStep, clearTrapState, evaluate, HostOperation.signature,
    HostOperation.runtimeOp, RuntimeOp.signature, decoded, tagged,
    encodeResults_uint32_singleton]

/-- Concrete Talos resolver for one supported semantic FIR runtime operation. -/
def hostFn (operation : HostOperation) : Wasm.HostFn RuntimeHost :=
  { params := operation.signature.params.toList.map abiKind
    results := operation.signature.results.toList.map abiKind
    invoke := hostStep operation }

/-- Abstract, proof-facing contract for one semantic runtime operation. -/
def hostContract (operation : HostOperation) : Wasm.HostContract RuntimeHost :=
  fun initial args result => result = hostStep operation initial args

theorem hostFn_satisfies_contract (operation : HostOperation) (initial args) :
    hostContract operation initial args ((hostFn operation).invoke initial args) := by
  rfl

inductive ResolverError where
  | invalidModule (error : SymbolicError)
  | malformedRuntimeImport (index : Nat)
  | unsupportedRuntimeImport (index : Nat) (operation : RuntimeOp)
  | malformedExternalImport (index : Nat) (declaration : Lean.Name)
  deriving Inhabited, BEq

structure ResolvedHosts where
  operations : List HostOperation

def ResolvedHosts.env (resolved : ResolvedHosts) : Wasm.HostEnv RuntimeHost :=
  { funcs := resolved.operations.map hostFn }

def ResolvedHosts.spec (resolved : ResolvedHosts) : Wasm.HostSpec RuntimeHost :=
  { contracts := resolved.operations.map hostContract }

private def resolveImports (index : Nat) :
    List Import → Except ResolverError (List HostOperation)
  | [] => .ok []
  | sourceImport :: imports => do
      let operation ←
        match sourceImport.key with
        | .runtime operation =>
            if sourceImport.signature != operation.signature || !operation.abiWellFormed then
              throw (.malformedRuntimeImport index)
            let some operation := HostOperation.ofRuntime? operation |
              throw (.unsupportedRuntimeImport index operation)
            pure operation
        | .external declaration =>
            let some types := sourceImport.externalTypes? |
              throw (.malformedExternalImport index declaration)
            pure (.external {
              name := declaration
              paramTypes := types.params
              resultType := types.result
              signature := sourceImport.signature })
      return operation :: (← resolveImports (index + 1) imports)

/-- Resolve every FIR import exactly once, preserving declaration order. -/
def resolveHosts (source : Fir.Wasm.Module) : Except ResolverError ResolvedHosts := do
  match validateModule source with
  | .ok _ => pure ()
  | .error error => throw (.invalidModule error)
  return { operations := ← resolveImports 0 source.imports.toList }

/-- Positional Talos satisfaction follows from the operation list and equal import counts. -/
theorem ResolvedHosts.satisfies (resolved : ResolvedHosts) (module : Wasm.Module)
    (aligned : module.imports.length = resolved.operations.length) :
    resolved.env.Satisfies module resolved.spec := by
  intro i hi
  have hop : i < resolved.operations.length := by omega
  let operation := resolved.operations[i]
  refine ⟨hostFn operation, hostContract operation, ?_, ?_, ?_⟩
  · simp [ResolvedHosts.env, operation, hop]
  · simp [ResolvedHosts.spec, operation, hop]
  · exact hostFn_satisfies_contract operation

end FirTalos
