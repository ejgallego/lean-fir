import FirTalos.ConcreteResidentReplacement
import FirTalos.ConcreteTraceSimulation

namespace FirTalos.Concrete.ResidentBoundaryTests

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure

/-- A memory-only resident implementation cannot satisfy the current
host-runtime state relation after a source external appends an event. This is
a boundary regression, not a counterexample to the conditional replacement
theorem: that theorem explicitly requires the impossible post-state relation
in this situation. A resident linking simulation needs its own representation
and observation bridge. -/
theorem not_stateRelated_after_event_of_host_preserved
    {function : Fir.Wasm.Function} {before after : RuntimeState}
    {beforeEnv afterEnv : Env} {initial final : Wasm.Store Host}
    {beforeLocals afterLocals : Wasm.Locals}
    {beforeWitness afterWitness : RefinementWitness} {event : ExternalEvent}
    (related : StateRelated function before beforeEnv initial beforeLocals beforeWitness)
    (hostPreserved : final.host = initial.host)
    (eventAdded : after.trace = before.trace.push event) :
    ¬ StateRelated function after afterEnv final afterLocals afterWitness := by
  intro next
  have beforeSize := related.1.trace.size
  have afterSize := next.1.trace.size
  rw [hostPreserved, eventAdded, Array.size_push] at afterSize
  omega

/-- Changing the refinement witness cannot conceal the missing event: exact
prefix observation already rules it out, independently of heap or result
representation. This applies to pure Array calls too, since the source
interpreter records their external responses. -/
theorem not_prefixObservationRel_after_event_of_host_preserved
    {before after : MachineState} {initial final : Wasm.Store Host}
    {event : ExternalEvent}
    (related : ConcretePrefixObservationRel
      (sourcePrefixObservation before) (concretePrefixObservation initial))
    (hostPreserved : final.host = initial.host)
    (eventAdded : after.runtime.trace = before.runtime.trace.push event) :
    ¬ ConcretePrefixObservationRel
      (sourcePrefixObservation after) (concretePrefixObservation final) := by
  rintro ⟨_, _, nextTrace⟩
  obtain ⟨_, _, beforeTrace⟩ := related
  have beforeSize := beforeTrace.size
  have afterSize := nextTrace.size
  change final.host.runtime.trace.size = after.runtime.trace.size at afterSize
  change initial.host.runtime.trace.size = before.runtime.trace.size at beforeSize
  rw [hostPreserved, eventAdded, Array.size_push] at afterSize
  omega

end FirTalos.Concrete.ResidentBoundaryTests
