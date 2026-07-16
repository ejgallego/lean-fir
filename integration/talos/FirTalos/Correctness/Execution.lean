import FirTalos.Correctness.Host
import FirTalos.Differential
import Interpreter.Wasm.Spec.Defs

namespace FirTalos.Correctness

open Fir.Wasm
open Fir.LeanIR.Impure

/-- The postcondition used to connect a successful Talos run to W3 observations. -/
def RelatedPost (resultKinds : Array AbiKind) (source : Observation)
    (store : Wasm.Store RuntimeHost) (values : List Wasm.Value) : Prop :=
  ∃ target,
    observeTarget resultKinds (.Success values store) = target ∧
      compareObservations source target = .related source target

/--
A single successful executable witness yields a fuel-free total-correctness
statement whose postcondition is expressed in source/target observations.
-/
theorem terminatesWith_related_of_run
    {env : Wasm.HostEnv RuntimeHost} {module : Wasm.Module} {functionIndex fuel : Nat}
    {initial final : Wasm.Store RuntimeHost} {args values : List Wasm.Value}
    {resultKinds : Array AbiKind} {source : Observation} {target : TargetObservation}
    (runSuccess :
      Wasm.run fuel module functionIndex initial args env = .Success values final)
    (observed : observeTarget resultKinds (.Success values final) = target)
    (related : compareObservations source target = .related source target) :
    Wasm.TerminatesWith env module functionIndex initial args
      (RelatedPost resultKinds source) := by
  apply Wasm.TerminatesWith.of_run fuel values final runSuccess
  exact ⟨target, observed, related⟩

/-- The same executable witness also discharges Talos partial correctness. -/
theorem partiallyMeets_related_of_run
    {env : Wasm.HostEnv RuntimeHost} {module : Wasm.Module} {functionIndex fuel : Nat}
    {initial final : Wasm.Store RuntimeHost} {args values : List Wasm.Value}
    {resultKinds : Array AbiKind} {source : Observation} {target : TargetObservation}
    (runSuccess :
      Wasm.run fuel module functionIndex initial args env = .Success values final)
    (observed : observeTarget resultKinds (.Success values final) = target)
    (related : compareObservations source target = .related source target) :
    Wasm.PartiallyMeets env module functionIndex initial args
      (RelatedPost resultKinds source) :=
  (terminatesWith_related_of_run runSuccess observed related).toPartiallyMeets

end FirTalos.Correctness
