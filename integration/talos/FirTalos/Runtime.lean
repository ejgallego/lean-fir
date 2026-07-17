import FirTalos.Adapter
import FirTalos.Codec
import Interpreter.Wasm.Host

namespace FirTalos

open Fir.Wasm
open Fir.LeanIR.Impure

/-- The deliberately small semantic-runtime fragment enabled by W2. -/
inductive HostOperation where
  | naturalLiteral (value : Nat) (result : AbiKind)
  | stringLiteral (value : String) (result : AbiKind)
  | allocCtor (info : Lean.Compiler.LCNF.CtorInfo) (fields : Array AbiKind)
      (result : AbiKind)
  | objectProj (index : Nat) (result : AbiKind)
  | usizeProj (index : Nat)
  | scalarProj (width offset : Nat) (result : AbiKind)
  | box (scalar result : AbiKind)
  | unbox (scalar : AbiKind)
  | isShared
  | objectSet (index : Nat) (field : AbiKind)
  | usizeSet (index : Nat)
  | scalarSet (width offset : Nat) (field : AbiKind)
  | setTag (tag : Nat)
  | getTag
  deriving Inhabited, BEq

def HostOperation.runtimeOp : HostOperation → RuntimeOp
  | .naturalLiteral value result => .literal (.nat value) result
  | .stringLiteral value result => .literal (.str value) result
  | .allocCtor info fields result => .allocCtor info fields result
  | .objectProj index result => .objectProj index result
  | .usizeProj index => .usizeProj index
  | .scalarProj width offset result => .scalarProj width offset result
  | .box scalar result => .box scalar result
  | .unbox scalar => .unbox scalar
  | .isShared => .isShared
  | .objectSet index field => .objectSet index field
  | .usizeSet index => .usizeSet index
  | .scalarSet width offset field => .scalarSet width offset field
  | .setTag tag => .setTag tag
  | .getTag => .getTag

def HostOperation.signature (operation : HostOperation) : Signature :=
  operation.runtimeOp.signature

def HostOperation.ofRuntime? : RuntimeOp → Option HostOperation
  | .literal (.nat value) result => some (.naturalLiteral value result)
  | .literal (.str value) result => some (.stringLiteral value result)
  | .allocCtor info fields result => some (.allocCtor info fields result)
  | .objectProj index result => some (.objectProj index result)
  | .usizeProj index => some (.usizeProj index)
  | .scalarProj width offset result => some (.scalarProj width offset result)
  | .box scalar result => some (.box scalar result)
  | .unbox scalar => some (.unbox scalar)
  | .isShared => some .isShared
  | .objectSet index field => some (.objectSet index field)
  | .usizeSet index => some (.usizeSet index)
  | .scalarSet width offset field => some (.scalarSet width offset field)
  | .setTag tag => some (.setTag tag)
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

private def evaluate (operation : HostOperation) (runtime : RuntimeState)
    (args : Array Value) : Except StructuredTrap (RuntimeState × Array Value) :=
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
          match getUSizeField runtime object index with
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
          match setUSizeField runtime object index field with
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
  | .getTag =>
      match args[0]? with
      | some object =>
          match getTag runtime object with
          | .ok tag => .ok (runtime, #[.scalar (.uint32 (UInt32.ofNat tag))])
          | .error fault => .error (.source fault)
      | none => .error (.target (.arityMismatch 1 args.size))

/-- The semantic host step, factored independently from Talos's `HostFn` record. -/
def hostStep (operation : HostOperation) (initial : Wasm.Store RuntimeHost)
    (physicalArgs : List Wasm.Value) : Wasm.HostResult RuntimeHost :=
  let initial := clearTrapState initial
  match decodeArgs initial.host.handles operation.signature.params physicalArgs with
  | .error failure => targetTrap initial failure
  | .ok args =>
      match evaluate operation initial.host.runtime args with
      | .error (.source fault) => sourceTrap initial fault
      | .error (.target failure) => targetTrap initial failure
      | .ok (runtime, results) =>
          let evaluated := { initial with host := { initial.host with runtime } }
          match encodeResults evaluated.host.handles operation.signature.results results with
          | .error failure => targetTrap evaluated failure
          | .ok (handles, results) =>
              .Return results { evaluated with host := { evaluated.host with handles } }

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
    (projected : getUSizeField initial.host.runtime sourceObject index =
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
    (mutated : setUSizeField initial.host.runtime sourceObject index sourceField =
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
  | externalImport (index : Nat) (declaration : Lean.Name)
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
        | .external declaration => throw (.externalImport index declaration)
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
