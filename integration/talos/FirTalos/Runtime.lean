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
  | getTag
  deriving Inhabited, BEq

def HostOperation.runtimeOp : HostOperation → RuntimeOp
  | .naturalLiteral value result => .literal (.nat value) result
  | .stringLiteral value result => .literal (.str value) result
  | .allocCtor info fields result => .allocCtor info fields result
  | .objectProj index result => .objectProj index result
  | .getTag => .getTag

def HostOperation.signature (operation : HostOperation) : Signature :=
  operation.runtimeOp.signature

def HostOperation.ofRuntime? : RuntimeOp → Option HostOperation
  | .literal (.nat value) result => some (.naturalLiteral value result)
  | .literal (.str value) result => some (.stringLiteral value result)
  | .allocCtor info fields result => some (.allocCtor info fields result)
  | .objectProj index result => some (.objectProj index result)
  | .getTag => some .getTag
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
