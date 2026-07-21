import FirTalos.ConcreteRuntime

namespace FirTalos.Concrete

open Fir.Wasm

/-- Operations omitted from the concrete resolver are honest fragment gates:
string allocation, floating-point scalar storage, legacy closure callbacks,
and external implementations still need concrete executable counterparts. -/
private def boxedScalarKind? :
    AbiKind → Option Fir.Wasm.Concrete.BoxedScalarKind
  | .uint8 => some Fir.Wasm.Concrete.BoxedScalarKind.uint8
  | .uint16 => some Fir.Wasm.Concrete.BoxedScalarKind.uint16
  | .uint32 => some Fir.Wasm.Concrete.BoxedScalarKind.uint32
  | .uint64 => some Fir.Wasm.Concrete.BoxedScalarKind.uint64
  | .usize => some Fir.Wasm.Concrete.BoxedScalarKind.usize
  | _ => none

private def integerScalarKind : AbiKind → Bool
  | .uint8 | .uint16 | .uint32 | .uint64 => true
  | _ => false

private def representedKind : AbiKind → Bool
  | .float32 | .float => false
  | _ => true

/-- Resolve one supported semantic runtime identity to the executable W6 host
that owns concrete linear memory. No semantic runtime or handle table is
available to any returned function. -/
def hostFn? : RuntimeOp → Option (Wasm.HostFn Host)
  | .literal value _ =>
      match value with
      | .nat value => some (naturalLiteralFn value)
      | _ => none
  | .allocCtor info fields result => some (allocCtorFn info fields result)
  | .objectProj index _ => some (objectProjFn index)
  | .usizeProj index => some (usizeProjFn index)
  | .scalarProj width offset kind =>
      if integerScalarKind kind then some (scalarProjFn width offset kind) else none
  | .cacheSet declaration kind =>
      if representedKind kind then some (cacheSetFn declaration kind) else none
  | .partialApply function arity fixed fields result =>
      if fields.all representedKind && representedKind result then
        some (partialApplyFn function arity fixed fields result)
      else none
  | .closureApply _ _ => none
  | .closureMatches function arity fixed =>
      some (closureMatchesFn function arity fixed)
  | .closureProj function arity fixed index result =>
      if representedKind result then
        some (closureProjFn function arity fixed index result)
      else none
  | .reset objectFields => some (resetFn objectFields)
  | .reuse info updateHeader fields result =>
      some (reuseFn info updateHeader fields result)
  | .box scalar result =>
      (boxedScalarKind? scalar).map fun kind => boxFn kind result
  | .unbox scalar => (boxedScalarKind? scalar).map unboxFn
  | .isShared => some isSharedFn
  | .objectSet index field => some (objectSetFn index field)
  | .usizeSet index => some (usizeSetFn index)
  | .scalarSet width offset kind =>
      if integerScalarKind kind then some (scalarSetFn width offset kind) else none
  | .setTag tag => some (setTagFn tag)
  | .inc amount check => some (incrementFn amount check)
  | .dec amount check objectFields? =>
      some (decrementFn amount check objectFields?)
  | .delete => some deleteFn
  | .getTag => some getTagFn

inductive ResolverError where
  | invalidModule (error : SymbolicError)
  | malformedRuntimeImport (index : Nat)
  | unsupportedRuntimeImport (index : Nat) (operation : RuntimeOp)
  | unsupportedExternalImport (index : Nat) (declaration : Lean.Name)
  deriving Inhabited, BEq

/-- One positional import paired with the exact concrete executable selected
from its stable runtime identity. -/
structure ResolvedHost where
  operation : RuntimeOp
  function : Wasm.HostFn Host

def ResolvedHost.contract (resolved : ResolvedHost) : Wasm.HostContract Host :=
  fun initial args result => result = resolved.function.invoke initial args

structure ResolvedHosts where
  hosts : List ResolvedHost

def ResolvedHosts.env (resolved : ResolvedHosts) : Wasm.HostEnv Host :=
  { funcs := resolved.hosts.map (·.function) }

def ResolvedHosts.spec (resolved : ResolvedHosts) : Wasm.HostSpec Host :=
  { contracts := resolved.hosts.map (·.contract) }

private def resolveImports (index : Nat) :
    List Import → Except ResolverError (List ResolvedHost)
  | [] => .ok []
  | sourceImport :: imports => do
      let resolved ←
        match sourceImport.key with
        | .runtime operation =>
            if sourceImport.signature != operation.signature || !operation.abiWellFormed then
              throw (.malformedRuntimeImport index)
            let some function := hostFn? operation |
              throw (.unsupportedRuntimeImport index operation)
            if function.params != operation.signature.params.toList.map FirTalos.abiKind ||
                function.results !=
                  operation.signature.results.toList.map FirTalos.abiKind then
              throw (.malformedRuntimeImport index)
            pure { operation, function }
        | .external declaration =>
            throw (.unsupportedExternalImport index declaration)
      return resolved :: (← resolveImports (index + 1) imports)

/-- Validate and resolve every source import in declaration order. A successful
result is sufficient to instantiate the adapted Talos module with the W6
linear-memory host; unsupported fragment cases fail before execution. -/
def resolveHosts (source : Fir.Wasm.Module) : Except ResolverError ResolvedHosts := do
  match validateModule source with
  | .ok _ => pure ()
  | .error error => throw (.invalidModule error)
  return { hosts := ← resolveImports 0 source.imports.toList }

theorem ResolvedHosts.satisfies (resolved : ResolvedHosts) (module : Wasm.Module)
    (aligned : module.imports.length = resolved.hosts.length) :
    resolved.env.Satisfies module resolved.spec := by
  intro i hi
  have hresolved : i < resolved.hosts.length := by omega
  let host := resolved.hosts[i]
  refine ⟨host.function, host.contract, ?_, ?_, ?_⟩
  · simp [ResolvedHosts.env, host, hresolved]
  · simp [ResolvedHosts.spec, host, hresolved]
  · intro store args
    rfl

end FirTalos.Concrete
