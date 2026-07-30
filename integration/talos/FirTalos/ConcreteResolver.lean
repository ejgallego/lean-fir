import FirTalos.ConcreteRuntime

namespace FirTalos.Concrete

open Fir.Wasm

/-- Operations omitted from the concrete resolver are honest fragment gates:
floating-point scalar storage and legacy closure callbacks still need
concrete executable counterparts. -/
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
      | .str value => some (stringLiteralFn value)
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

/-- Every generated reset identity resolves to the count-indexed concrete
reset host. -/
@[simp] theorem hostFn?_reset (count : Nat) :
    hostFn? (.reset count) = some (resetFn count) := rfl

/-- Every concrete boxed-scalar kind resolves to its matching typed-unbox
host. This is the public proof boundary for the resolver's private scalar
classification table. -/
@[simp] theorem hostFn?_unbox_abiKind (kind : Fir.Wasm.Concrete.BoxedScalarKind) :
    hostFn? (.unbox kind.abiKind) = some (unboxFn kind) := by
  cases kind <;> rfl

/-- Every concrete boxed-scalar kind resolves to its matching boxing host.
The result kind remains an explicit part of the generated runtime identity. -/
@[simp] theorem hostFn?_box_abiKind
    (kind : Fir.Wasm.Concrete.BoxedScalarKind) (resultKind : AbiKind) :
    hostFn? (.box kind.abiKind resultKind) =
      some (boxFn kind resultKind) := by
  cases kind <;> rfl

/-- The concrete resolver implements exactly the four packed-integer scalar
setter kinds used by the W6 scalar-mutation refinement theorem. This public
boundary keeps the resolver's classification function private. -/
theorem hostFn?_scalarSet_of_packedInteger
    {slotIndex byteOffset : Nat} {kind : AbiKind}
    (supported :
      kind = .uint8 ∨ kind = .uint16 ∨ kind = .uint32 ∨ kind = .uint64) :
    hostFn? (.scalarSet slotIndex byteOffset kind) =
      some (scalarSetFn slotIndex byteOffset kind) := by
  rcases supported with rfl | rfl | rfl | rfl <;> rfl

inductive ResolverError where
  | invalidModule (error : SymbolicError)
  | malformedRuntimeImport (index : Nat)
  | unsupportedRuntimeImport (index : Nat) (operation : RuntimeOp)
  | malformedExternalImport (index : Nat) (declaration : Lean.Name)
  deriving Inhabited, BEq

/-- One positional import paired with the exact concrete executable selected
from its stable runtime identity. -/
structure ResolvedHost where
  key : ImportKey
  function : Wasm.HostFn Host

def ResolvedHost.contract (resolved : ResolvedHost) : Wasm.HostContract Host :=
  fun initial args result => result = resolved.function.invoke initial args

structure ResolvedHosts where
  hosts : List ResolvedHost

def ResolvedHosts.env (resolved : ResolvedHosts) : Wasm.HostEnv Host :=
  { funcs := resolved.hosts.map (·.function) }

def ResolvedHosts.spec (resolved : ResolvedHosts) : Wasm.HostSpec Host :=
  { contracts := resolved.hosts.map (·.contract) }

/-- The concrete runtime combines each generated value global and its Wasm
initialized flag into one typed optional slot. Derive those slots from the
same cached declarations used by lowering. -/
def cacheDeclarations (source : Fir.Wasm.Module) :
    List (Lean.Name × AbiKind) :=
  source.initializers.toList.filterMap fun name => do
    let signature ← source.callSignature? (.declaration name)
    let kind ← signature.results[0]?
    return (name, kind)

/-- Closure target ids are explicit, retained module metadata. Keeping the
source names in the host table lets checked closure metadata recover the exact
semantic declaration even after the runtime operation that first introduced a
target has been internalized. -/
def closureDispatch (source : Fir.Wasm.Module) :
    Fir.Wasm.Concrete.ClosureDispatchTable :=
  source.closureDispatch

/-- Capture descriptors are explicit, retained module metadata. Resident
`partialApply` helpers still write descriptor ids into closure headers after
their corresponding runtime imports have disappeared. -/
def closureDescriptors (source : Fir.Wasm.Module) :
    Fir.Wasm.Concrete.ClosureDescriptorTable :=
  source.closureDescriptors

/-- Prepare host-owned runtime state for a validated module. Physical Wasm
globals remain in Talos's store; this table is the typed concrete counterpart
used by `cacheSet`. -/
def initialHost (source : Fir.Wasm.Module)
    (externals : Fir.Wasm.Concrete.ConcreteExternalImpl :=
      rejectExternalImpl) : Host :=
  { runtime := {
      globals := Fir.Wasm.Concrete.ConcreteGlobals.declare
        (cacheDeclarations source) }
    closureDispatch := closureDispatch source
    closureDescriptors := closureDescriptors source
    externals }

def initialStore (source : Fir.Wasm.Module) (target : Wasm.Module)
    (externals : Fir.Wasm.Concrete.ConcreteExternalImpl :=
      rejectExternalImpl) :
    Wasm.Store Host :=
  { target.initialStore (α := Host) with host := initialHost source externals }

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
            pure { key := sourceImport.key, function }
        | .external declaration =>
            let some types := sourceImport.externalTypes? |
              throw (.malformedExternalImport index declaration)
            let some resultKind := sourceImport.signature.results[0]? |
              throw (.malformedExternalImport index declaration)
            if types.params.size != sourceImport.signature.params.size ||
                sourceImport.signature.results.size != 1 then
              throw (.malformedExternalImport index declaration)
            let operation : ExternalOperation := {
              name := declaration
              paramTypes := types.params
              resultType := types.result
              signature := sourceImport.signature }
            pure {
              key := sourceImport.key
              function := externalFn operation resultKind }
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
