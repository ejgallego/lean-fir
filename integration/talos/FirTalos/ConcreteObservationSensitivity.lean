import FirTalos.ConcreteTraceSimulation
import FirTalos.ConcreteFaultCorrectness
import Fir.Wasm.PrettyFormat

/-!
# Result and fault sensitivity of W6 observations

These theorems test existing public contracts. They add no compiler admission
premise and make no new claim that the whole compiler satisfies a terminal
contract. The reusable consistency lemmas use the actual deterministic
`Wasm.run` semantics at a common sufficient fuel.
-/

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure

/-- The prefix observation deliberately forgets control, including a yielded
result and whether the next source step will return or fault. -/
theorem sourcePrefixObservation_control_irrelevant
    (state : MachineState) (left right : Control) :
    sourcePrefixObservation { state with control := left } =
      sourcePrefixObservation { state with control := right } := rfl

/-- Two terminal source states with the same runtime have the same prefix
observation regardless of their returned scalar. -/
theorem returnedScalar_prefix_indistinguishable
    (state : MachineState) (left right : UInt64) :
    sourcePrefixObservation
        { state with control := .yielded (.scalar (.uint64 left)), frames := [] } =
      sourcePrefixObservation
        { state with control := .yielded (.scalar (.uint64 right)), frames := [] } := rfl

/-- The ordinary source terminal observation does distinguish these values. -/
theorem returnedScalar_outcomes_distinct (left right : UInt64) (different : left ≠ right) :
    Outcome.returned (.scalar (.uint64 left)) ≠
      Outcome.returned (.scalar (.uint64 right)) := by
  intro equal
  cases equal
  exact different rfl

/-- A target with no transitions and no terminal-result interface. It is used
only to test the logical strength of the public prefix package. -/
def stoppedPrefixMachine (store : Wasm.Store Host) : ConcreteResumableMachine where
  State := Unit
  step := fun _ _ => False
  store := fun _ => store

/-- Once the source is terminal, the prefix package requires only world/trace
agreement. It places no constraint on the target's terminal result. This
counterexample concerns the interface, not FIR's generated target relation. -/
theorem finiteTraceCorrect_of_terminal_prefix
    {externals : ExternalImpl} {source : MachineState} {observation : Observation}
    {store : Wasm.Store Host}
    (terminal : executeStep externals source = .done observation)
    (observed : ConcretePrefixObservationRel (sourcePrefixObservation source)
      (concretePrefixObservation store)) :
    ConcreteFiniteTraceCorrect externals (stoppedPrefixMachine store) source () := by
  refine ⟨{
    relation := fun current _ => current = source
    rank := fun _ => 0
    observes := ?_
    advance := ?_ }, rfl⟩
  · intro current target related
    subst current
    exact observed
  · intro before after target related step
    subst before
    rw [terminal] at step
    cases step

/-- Both successful specifications of one invocation hold of one common
execution. No determinism assumption is supplied by the caller: both refer to
the same executable `Wasm.run` at the maximum of their sufficient fuels. -/
theorem ConcreteExportTerminatesWith.postconditions_overlap
    {env : Wasm.HostEnv Host} {module : Wasm.Module} {exportName : String}
    {initial : Wasm.Store Host} {args : List Wasm.Value}
    {left right : Wasm.Store Host → List Wasm.Value → Prop}
    (first : ConcreteExportTerminatesWith env module exportName initial args left)
    (second : ConcreteExportTerminatesWith env module exportName initial args right) :
    ∃ final values, left final values ∧ right final values := by
  obtain ⟨firstIndex, firstFound, firstFuel, firstRuns⟩ := first
  obtain ⟨secondIndex, secondFound, secondFuel, secondRuns⟩ := second
  have indices : firstIndex = secondIndex := Option.some.inj (firstFound.symm.trans secondFound)
  subst secondIndex
  obtain ⟨firstValues, firstStore, firstRun, firstPost⟩ :=
    firstRuns (max firstFuel secondFuel) (Nat.le_max_left _ _)
  obtain ⟨secondValues, secondStore, secondRun, secondPost⟩ :=
    secondRuns (max firstFuel secondFuel) (Nat.le_max_right _ _)
  have equal := firstRun.symm.trans secondRun
  cases equal
  exact ⟨_, _, firstPost, secondPost⟩

/-- Successful termination and trapping are incompatible specifications of
the same exported invocation, including its initial store and host. -/
theorem ConcreteExportTerminatesWith.not_trapsWith
    {env : Wasm.HostEnv Host} {module : Wasm.Module} {exportName : String}
    {initial : Wasm.Store Host} {args : List Wasm.Value}
    {returned : Wasm.Store Host → List Wasm.Value → Prop}
    {trapped : Wasm.Store Host → String → Prop}
    (success : ConcreteExportTerminatesWith env module exportName initial args returned) :
    ¬ ConcreteExportTrapsWith env module exportName initial args trapped := by
  intro failure
  obtain ⟨firstIndex, firstFound, firstFuel, firstRuns⟩ := success
  obtain ⟨secondIndex, secondFound, secondFuel, secondRuns⟩ := failure
  have indices : firstIndex = secondIndex := Option.some.inj (firstFound.symm.trans secondFound)
  subst secondIndex
  obtain ⟨_, _, firstRun, _⟩ :=
    firstRuns (max firstFuel secondFuel) (Nat.le_max_left _ _)
  obtain ⟨_, _, secondRun, _⟩ :=
    secondRuns (max firstFuel secondFuel) (Nat.le_max_right _ _)
  cases firstRun.symm.trans secondRun

/-- A refined UInt64 result determines the actual returned lane independently
of the heap witness. This is a property of W6's existing result relation. -/
theorem RefinedReturnPost.uint64_values
    {runtime : RuntimeState} {value : UInt64}
    {final : Wasm.Store Host} {values : List Wasm.Value}
    (related : RefinedReturnPost runtime (.scalar (.uint64 value)) .uint64 [] final values) :
    values = [.i64 value] := by
  obtain ⟨witness, physical, _, _, related, results⟩ := related
  cases related with
  | word32 related => cases related
  | word64 related => cases related; exact results
  | float32Bits related => cases related
  | float64Bits related => cases related

/-- Regression against a wrong scalar result: an invocation satisfying the
existing refined result contract cannot also satisfy a different UInt64 result. -/
theorem ConcreteExportTerminatesWith.uint64_result_unique
    {env : Wasm.HostEnv Host} {module : Wasm.Module} {exportName : String}
    {initial : Wasm.Store Host} {args : List Wasm.Value}
    {firstRuntime secondRuntime : RuntimeState} {firstValue secondValue : UInt64}
    (first : ConcreteExportTerminatesWith env module exportName initial args
      (RefinedReturnPost firstRuntime (.scalar (.uint64 firstValue)) .uint64 []))
    (second : ConcreteExportTerminatesWith env module exportName initial args
      (RefinedReturnPost secondRuntime (.scalar (.uint64 secondValue)) .uint64 [])) :
    firstValue = secondValue := by
  obtain ⟨_, _, firstPost, secondPost⟩ := first.postconditions_overlap second
  have equal := firstPost.uint64_values.symm.trans secondPost.uint64_values
  simpa using equal

namespace ObservationSensitivity

/- The generated facade's actual result type is used here so the regression
cannot accidentally replace its returned styling list with the runtime trace. -/
#fir_wasm_pretty_trace_facade pretty

def prettyObservation (result : prettyTrace) : String × List prettyEvent :=
  (result.text, result.eventsRev.reverse)

/-- Decoding reverse-chronological storage loses no returned event information. -/
theorem prettyObservation_injective : Function.Injective prettyObservation := by
  intro left right equal
  cases left with
  | mk leftText leftEvents =>
    cases right with
    | mk rightText rightEvents =>
      have textEqual := congrArg Prod.fst equal
      have eventsEqual := congrArg (fun result => result.2.reverse) equal
      simp only [prettyObservation, List.reverse_reverse] at eventsEqual
      simp only [prettyObservation] at textEqual
      cases textEqual
      cases eventsEqual
      rfl

/-- Identical text with different styling is observably different. -/
theorem prettyObservation_distinguishes_styling
    (text : String) (left right : List prettyEvent) (different : left ≠ right) :
    prettyObservation ⟨text, left⟩ ≠ prettyObservation ⟨text, right⟩ := by
  intro equal
  have resultEqual := prettyObservation_injective equal
  exact different (congrArg prettyTrace.eventsRev resultEqual)

end ObservationSensitivity
end FirTalos.Concrete
