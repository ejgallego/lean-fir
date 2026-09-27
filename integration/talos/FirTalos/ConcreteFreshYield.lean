import FirTalos.ConcreteBodyResources
import FirTalos.ConcreteRegionTransport

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- A heap-valued initializer at its return boundary. The allocation cutoff is
the initializer's entry, not its current witness or allocation frontier.
Construction evidence belongs to this dynamic state; it is not a promise about
all future results attached to a static lazy frame. Suspended callers are
deliberately separate and are restored only by the publication consumer. -/
structure ConcreteStructuredFreshYieldCore
    (context : Context) (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (entryRuntime : RuntimeState) (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness) (facts : ReuseCapacityFacts) (bytes : Nat)
    (runtime : RuntimeState) (env : Env) (store : Wasm.Store Host)
    (locals : Wasm.Locals) (witness : RefinementWitness)
    (kind : AbiKind) (root : Location) (physical : Wasm.Value)
    (source : MachineState) (target : StructuredWasmState Host) : Prop where
  focus : ConcreteStructuredYieldFocus context sourceFunction runtime env
    (.object (.heap root)) store locals witness kind physical source target
  scope : ConcreteStructuredResourceScope context sourceModule sourceFunction externals
    entryRuntime entryStore entryWitness facts bytes runtime env store locals witness
  region : HeapRegionClosed entryRuntime.nextLocation runtime.heap
  rootBound : entryRuntime.nextLocation ≤ root

/-- Assemble the return relation from the entry scope and the body's actual
operation transports. Neither a post-body resource scope nor a future source
execution is assumed. The producer proves region closure along construction;
ordinary transport alone cannot imply it. -/
theorem ConcreteStructuredFreshYieldCore.of_body
    {context : Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {entryRuntime runtime current : RuntimeState}
    {entryStore store currentStore : Wasm.Store Host}
    {entryWitness witness currentWitness : RefinementWitness}
    {bytes currentBytes : Nat} {env currentEnv : Env} {locals currentLocals : Wasm.Locals}
    {kind : AbiKind} {root : Location} {physical : Wasm.Value}
    {source : MachineState} {target : StructuredWasmState Host}
    (scope : ConcreteStructuredResourceScope context sourceModule sourceFunction externals
      entryRuntime entryStore entryWitness [] bytes runtime env store locals witness)
    (transports : RuntimeStepTransports runtime current store currentStore witness currentWitness)
    (externalsEq : currentStore.host.externals = store.host.externals)
    (focus : ConcreteStructuredYieldFocus context sourceFunction current currentEnv
      (.object (.heap root)) currentStore currentLocals currentWitness kind physical source target)
    (budget : currentStore.host.runtime.heap.AddressSpaceBudget currentBytes)
    (region : HeapRegionClosed entryRuntime.nextLocation current.heap)
    (rootBound : entryRuntime.nextLocation ≤ root) :
    ConcreteStructuredFreshYieldCore context sourceModule sourceFunction externals
      entryRuntime entryStore entryWitness [] currentBytes current currentEnv currentStore
      currentLocals currentWitness kind root physical source target :=
  ⟨focus, scope.afterBody_withoutReuseFacts transports externalsEq
    focus.stateRelated focus.frameAligned budget, region, rootBound⟩

end FirTalos.Concrete
