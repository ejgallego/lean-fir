import Fir.LeanIR.Passes.ElimDeadProgram

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.NonLockstep.Structural

/-!
The reachable-runtime machine relation for `elimDeadVars`.

Unlike the earlier exact-runtime relation, every control and saved frame
publishes the values that can still be inspected.  These roots feed
`ShadowRuntimeRel`, so source-only garbage may differ while all reachable
objects remain related through an address renaming.
-/

/-- A related control together with its complete runtime roots. -/
inductive ReachableControlRelated (fuel : Nat) (rho : AddressRenaming) :
    Env → JoinEnv → Control → Env → JoinEnv → Control →
      List Value → List Value → Prop where
  | code
      (graph : ShadowCodeGraph fuel used sourceCode targetCode)
      (joins : ShadowJoinEnvRelated fuel used sourceJoins targetJoins)
      (env : EnvRelOn rho used sourceEnv targetEnv) :
      ReachableControlRelated fuel rho
        sourceEnv sourceJoins (.code sourceCode)
        targetEnv targetJoins (.code targetCode)
        (envRootsOn used sourceEnv) (envRootsOn used targetEnv)
  | yielded (value : ValueRel rho sourceValue targetValue) :
      ReachableControlRelated fuel rho
        sourceEnv sourceJoins (.yielded sourceValue)
        targetEnv targetJoins (.yielded targetValue)
        [sourceValue] [targetValue]
  | invokeName (name : Name)
      (arguments : ArrayRel (ValueRel rho) sourceArguments targetArguments) :
      ReachableControlRelated fuel rho
        sourceEnv sourceJoins (.invokeName name sourceArguments)
        targetEnv targetJoins (.invokeName name targetArguments)
        sourceArguments.toList targetArguments.toList
  | invokeValue (function : ValueRel rho sourceFunction targetFunction)
      (arguments : ArrayRel (ValueRel rho) sourceArguments targetArguments) :
      ReachableControlRelated fuel rho
        sourceEnv sourceJoins
          (.invokeValue sourceFunction sourceArguments)
        targetEnv targetJoins
          (.invokeValue targetFunction targetArguments)
        (sourceFunction :: sourceArguments.toList)
        (targetFunction :: targetArguments.toList)

/-- A saved frame together with the values it can inspect when restored. -/
inductive ReachableFrameRelated (fuel : Nat) (rho : AddressRenaming) :
    Frame → Frame → List Value → List Value → Prop where
  | bind
      (graph : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (joins : ShadowJoinEnvRelated fuel used sourceJoins targetJoins)
      (env : EnvRelOn rho used sourceEnv targetEnv) :
      ReachableFrameRelated fuel rho
        (.bind fvarId sourceContinuation sourceEnv sourceJoins)
        (.bind fvarId targetContinuation targetEnv targetJoins)
        (envRootsOn used sourceEnv) (envRootsOn used targetEnv)
  | apply
      (arguments : ArrayRel (ValueRel rho) sourceArguments targetArguments) :
      ReachableFrameRelated fuel rho
        (.apply sourceArguments) (.apply targetArguments)
        sourceArguments.toList targetArguments.toList
  | cache (name : Name) :
      ReachableFrameRelated fuel rho (.cache name) (.cache name) [] []

/-- Pointwise frame relation with concatenated roots in stack order. -/
inductive ReachableFramesRelated (fuel : Nat) (rho : AddressRenaming) :
    List Frame → List Frame → List Value → List Value → Prop where
  | nil : ReachableFramesRelated fuel rho [] [] [] []
  | cons
      (head : ReachableFrameRelated fuel rho
        sourceFrame targetFrame sourceHeadRoots targetHeadRoots)
      (tail : ReachableFramesRelated fuel rho
        sourceFrames targetFrames sourceTailRoots targetTailRoots) :
      ReachableFramesRelated fuel rho
        (sourceFrame :: sourceFrames) (targetFrame :: targetFrames)
        (sourceHeadRoots ++ sourceTailRoots)
        (targetHeadRoots ++ targetTailRoots)

/-- Full machine invariant used by the generalized non-lockstep proof.  The
root lists are existential witnesses because this relation is proof-valued. -/
def ReachableMachineRelated (fuel : Nat) (rho : AddressRenaming)
    (source target : MachineState) : Prop :=
  ∃ sourceControlRoots targetControlRoots sourceFrameRoots targetFrameRoots,
    ProgramRelated (ShadowCodeRelated fuel)
        source.program target.program ∧
    ReachableControlRelated fuel rho
        source.env source.joins source.control
        target.env target.joins target.control
        sourceControlRoots targetControlRoots ∧
    ReachableFramesRelated fuel rho
        source.frames target.frames sourceFrameRoots targetFrameRoots ∧
    ShadowRuntimeRel rho source.runtime target.runtime
        (sourceControlRoots ++ sourceFrameRoots)
        (targetControlRoots ++ targetFrameRoots)

theorem ReachableControlRelated.monoRenaming
    (extension : RenamingExtends smaller larger)
    (related : ReachableControlRelated fuel smaller
      sourceEnv sourceJoins sourceControl
      targetEnv targetJoins targetControl sourceRoots targetRoots) :
    ReachableControlRelated fuel larger
      sourceEnv sourceJoins sourceControl
      targetEnv targetJoins targetControl sourceRoots targetRoots := by
  cases related with
  | code graph joins env =>
      exact .code graph joins (envRelOn_monoRenaming extension env)
  | yielded value => exact .yielded (valueRel_mono extension value)
  | invokeName name arguments =>
      exact .invokeName name (arrayRel_mono (valueRel_mono extension) arguments)
  | invokeValue function arguments =>
      exact .invokeValue (valueRel_mono extension function)
        (arrayRel_mono (valueRel_mono extension) arguments)

theorem ReachableFrameRelated.monoRenaming
    (extension : RenamingExtends smaller larger)
    (related : ReachableFrameRelated fuel smaller
      source target sourceRoots targetRoots) :
    ReachableFrameRelated fuel larger
      source target sourceRoots targetRoots := by
  cases related with
  | bind graph joins env =>
      exact .bind graph joins (envRelOn_monoRenaming extension env)
  | apply arguments =>
      exact .apply (arrayRel_mono (valueRel_mono extension) arguments)
  | cache name => exact .cache name

theorem ReachableFramesRelated.monoRenaming
    (extension : RenamingExtends smaller larger)
    (related : ReachableFramesRelated fuel smaller
      source target sourceRoots targetRoots) :
    ReachableFramesRelated fuel larger
      source target sourceRoots targetRoots := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (head.monoRenaming extension) ih

/-- Transport the entire machine invariant after extending the address
renaming, as happens when both executions retain an allocation. -/
theorem ReachableMachineRelated.monoRenaming
    (related : ReachableMachineRelated fuel smaller source target)
    (extension : RenamingExtends smaller larger)
    (sourceFresh : ∀ location, source.runtime.nextLocation ≤ location →
      larger.forward location = none)
    (targetFresh : ∀ location, target.runtime.nextLocation ≤ location →
      larger.reverse location = none) :
    ReachableMachineRelated fuel larger source target := by
  rcases related with
    ⟨sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  exact ⟨sourceControlRoots, targetControlRoots,
    sourceFrameRoots, targetFrameRoots,
    programs, control.monoRenaming extension,
    frames.monoRenaming extension,
    shadowRuntimeRel_monoRenaming extension runtime sourceFresh targetFresh⟩

/-- Related declaration graphs and entry arguments establish the generalized
machine invariant at the canonical empty-runtime entry state. -/
theorem initialState_reachableMachineRelated
    (programs : ProgramRelated (ShadowCodeRelated fuel) sourceProgram
      targetProgram)
    (arguments : ArrayRel (ValueRel emptyAddressRenaming)
      sourceArguments targetArguments) :
    ReachableMachineRelated fuel emptyAddressRenaming
      (initialState sourceProgram entry sourceArguments)
      (initialState targetProgram entry targetArguments) := by
  unfold ReachableMachineRelated
  refine ⟨sourceArguments.toList, targetArguments.toList, [], [], ?_, ?_, ?_, ?_⟩
  · simpa [initialState] using programs
  · simpa [initialState] using
      ReachableControlRelated.invokeName (sourceEnv := []) (sourceJoins := [])
        (targetEnv := []) (targetJoins := []) entry arguments
  · simpa [initialState] using
      (ReachableFramesRelated.nil :
        ReachableFramesRelated fuel emptyAddressRenaming [] [] [] [])
  · simpa [initialState] using emptyRuntime_shadowRelated_of_roots arguments

/-- Machine-level source-only rule for a deleted value-producing `let`.
The caller supplies the operation-specific reachable-runtime theorem; binder
absence then proves that resuming the source continuation does not change its
published live roots. -/
theorem coreStep_deletedLet_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (absent : used.contains declaration.fvarId = false)
    (evaluated : evalLetValue sourceState declaration =
      .ok (nextRuntime, .value value))
    (runtime : ShadowRuntimeRel rho nextRuntime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    let sourceAfter := {
      sourceState with
      runtime := nextRuntime
      env := bind sourceState.env declaration.fvarId value
      control := .code sourceContinuation }
    coreStep { sourceState with
        control := .code (.let declaration sourceContinuation) } =
        .next sourceAfter ∧
      ReachableMachineRelated fuel rho sourceAfter
        { targetState with control := .code targetContinuation } := by
  dsimp only
  constructor
  · simp only [coreStep]
    rw [evalLetValue_control_eq, evaluated]
  · unfold ReachableMachineRelated
    refine ⟨envRootsOn used (bind sourceState.env declaration.fvarId value),
      envRootsOn used targetState.env,
      sourceFrameRoots, targetFrameRoots, ?_, ?_, ?_, ?_⟩
    · exact programs
    · exact .code continuation joins (env.bindLeft_of_absent absent)
    · exact frames
    · simpa [envRootsOn_bind_of_absent absent] using runtime

/-- A related yielded value on an empty stack projects to the repository's
shared reachable-observation relation. -/
theorem ReachableMachineRelated.yieldedObservation
    (related : ReachableMachineRelated fuel rho source target)
    (sourceControl : source.control = .yielded sourceValue)
    (targetControl : target.control = .yielded targetValue)
    (sourceFrames : source.frames = [])
    (targetFrames : target.frames = []) :
    ObservationRel
      (observe source (.returned sourceValue))
      (observe target (.returned targetValue)) := by
  rcases related with
    ⟨sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  rw [sourceControl, targetControl] at control
  rw [sourceFrames, targetFrames] at frames
  cases control with
  | yielded values =>
      cases frames with
      | nil =>
          have outcomes : OutcomeRel rho
              (.returned sourceValue) (.returned targetValue) := by
            simpa [OutcomeRel] using values
          apply runtime.observationRel outcomes
          · intro value member
            simpa [outcomeRoots] using member
          · intro value member
            simpa [outcomeRoots] using member

end Fir.LeanIR.Passes.ElimDead
