import Fir.LeanIR.Passes.ElimDeadProgram

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.SimpCase
open Fir.LeanIR.Passes.NonLockstep.Structural

/-!
The reachable-runtime machine relation for `elimDeadVars`.

Unlike the earlier exact-runtime relation, every control and saved frame
publishes the values that can still be inspected.  These roots feed
`ShadowRuntimeRel`, so source-only garbage may differ while all reachable
objects remain related through an address renaming.
-/

def withCodeControl (state : MachineState) (code : LCNF.Code .impure) :
    MachineState :=
  { state with control := .code code }

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

/-- Finite-stuttering simulation with a relational terminal contract.  This
is the observation-aware counterpart of `NonLockstep.StutteringSimulation`:
the advance field is identical, while terminal source observations may map to
distinct target observations. -/
structure RelationalStutteringSimulation (externals : ExternalSpec)
    (observationRel : Observation → Observation → Prop)
    (relation : MachineState → MachineState → Prop) : Prop where
  terminal : ∀ {source target sourceObservation}, relation source target →
    coreStep source = .done sourceObservation →
      ∃ targetObservation,
        EvaluatesState externals target targetObservation ∧
        observationRel sourceObservation targetObservation
  advance : ∀ {sourceBefore sourceAfter target},
    relation sourceBefore target →
    Step externals sourceBefore sourceAfter →
      ∃ targetAfter,
        NonLockstep.Reaches externals target targetAfter ∧
        relation sourceAfter targetAfter

/-- A relational stuttering simulation transports every finite terminating
source execution to a related terminating target execution. -/
theorem RelationalStutteringSimulation.evaluatesState
    (simulation : RelationalStutteringSimulation externals observationRel
      relation)
    (related : relation source target)
    (evaluation : EvaluatesState externals source sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals target targetObservation ∧
      observationRel sourceObservation targetObservation := by
  rcases evaluation with ⟨count, final, execution, done⟩
  induction execution generalizing target with
  | refl state => exact simulation.terminal related done
  | step head tail ih =>
      rcases simulation.advance related head with
        ⟨targetAfter, targetPath, afterRelated⟩
      rcases ih afterRelated done with
        ⟨targetObservation, targetEvaluation, observations⟩
      exact ⟨targetObservation,
        NonLockstep.evaluatesState_of_reaches targetPath targetEvaluation,
        observations⟩

/-- One-way, reachable-observation correctness for a same-phase pass.  This
is the compiler-facing statement appropriate for transformations that may
change unreachable heap garbage. -/
def ReachablePassForwardCorrectOn (externals : ExternalSpec)
    (source target : ImpureProgram) (entries : Array Name) : Prop :=
  ∀ entry, entry ∈ entries → ∀ arguments sourceObservation,
    Impure.Evaluates externals source entry arguments sourceObservation →
      ∃ targetObservation,
        Impure.Evaluates externals target entry arguments targetObservation ∧
        ObservationRel sourceObservation targetObservation

theorem reachablePassForwardCorrectOn_of_stuttering
    (simulation : RelationalStutteringSimulation externals ObservationRel
      relation)
    (initial : ∀ entry, entry ∈ entries → ∀ arguments,
      relation (initialState source entry arguments)
        (initialState target entry arguments)) :
    ReachablePassForwardCorrectOn externals source target entries := by
  intro entry member arguments sourceObservation evaluation
  exact simulation.evaluatesState (initial entry member arguments) evaluation

/-- Hide the current address-renaming witness so lockstep allocations may
extend it between simulation states. -/
def SomeReachableMachineRelated (fuel : Nat)
    (source target : MachineState) : Prop :=
  ∃ rho, ReachableMachineRelated fuel rho source target

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

theorem ReachableFrameRelated.roots
    (related : ReachableFrameRelated fuel rho
      source target sourceRoots targetRoots) :
    ListRel (ValueRel rho) sourceRoots targetRoots := by
  cases related with
  | bind graph joins env => exact envRootsOn_related env
  | apply arguments => exact arguments
  | cache name => exact .nil

theorem ReachableFramesRelated.roots
    (related : ReachableFramesRelated fuel rho
      source target sourceRoots targetRoots) :
    ListRel (ValueRel rho) sourceRoots targetRoots := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact listRel_append head.roots ih

/-- Related declaration arguments prepare related apply/cache frame stacks.
Only an apply frame contributes new roots; a cache frame contributes none. -/
theorem ReachableFramesRelated.prepareCall
    (name : Name) (params : Array (LCNF.Param .impure))
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (extraArguments : ArrayRel (ValueRel rho)
      sourceExtraArguments targetExtraArguments)
    (related : ReachableFramesRelated fuel rho
      sourceFrames targetFrames sourceRoots targetRoots) :
    ReachableFramesRelated fuel rho
      (let frames := if sourceExtraArguments.isEmpty then sourceFrames
        else .apply sourceExtraArguments :: sourceFrames
       if params.isEmpty && sourceArguments.isEmpty then
          .cache name :: frames
       else frames)
      (let frames := if targetExtraArguments.isEmpty then targetFrames
        else .apply targetExtraArguments :: targetFrames
       if params.isEmpty && targetArguments.isEmpty then
          .cache name :: frames
       else frames)
      (if sourceExtraArguments.isEmpty then sourceRoots
        else sourceExtraArguments.toList ++ sourceRoots)
      (if targetExtraArguments.isEmpty then targetRoots
        else targetExtraArguments.toList ++ targetRoots) := by
  have extraSize := arrayRel_size_eq extraArguments
  have argumentSize := arrayRel_size_eq arguments
  have extraEmptyEq : sourceExtraArguments.isEmpty =
      targetExtraArguments.isEmpty := by
    simp [Array.isEmpty, extraSize]
  have argumentsEmptyEq : sourceArguments.isEmpty =
      targetArguments.isEmpty := by
    simp [Array.isEmpty, argumentSize]
  rw [← extraEmptyEq, ← argumentsEmptyEq]
  by_cases extraEmpty : sourceExtraArguments.isEmpty
  · by_cases cache : params.isEmpty && sourceArguments.isEmpty
    · simpa [extraEmpty, cache] using
        ReachableFramesRelated.cons
          (ReachableFrameRelated.cache (fuel := fuel) (rho := rho) name)
          related
    · simpa [extraEmpty, cache] using related
  · by_cases cache : params.isEmpty && sourceArguments.isEmpty
    · simpa [extraEmpty, cache] using
        ReachableFramesRelated.cons
          (ReachableFrameRelated.cache (fuel := fuel) (rho := rho) name)
          (ReachableFramesRelated.cons
            (ReachableFrameRelated.apply extraArguments) related)
    · simpa [extraEmpty, cache] using
        ReachableFramesRelated.cons
          (ReachableFrameRelated.apply extraArguments) related

/-- Entering related internal declaration bodies after argument splitting and
parameter binding preserves the reachable machine relation.  The new control
roots come from call arguments; the prepared frame roots come from extra
arguments and the old stack, so the runtime relation can be restricted from
the original invocation roots. -/
theorem enterInternalDecl_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceFrames targetFrames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (body : ShadowCodeGraph fuel used sourceCode targetCode)
    (sourceBinding : bindParams params
      (sourceArguments.extract 0 params.size) = .ok sourceEnv)
    (targetBinding : bindParams params
      (targetArguments.extract 0 params.size) = .ok targetEnv)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    let sourceExtraArguments :=
      sourceArguments.extract params.size sourceArguments.size
    let targetExtraArguments :=
      targetArguments.extract params.size targetArguments.size
    let sourcePreparedFrames :=
      let frames := if sourceExtraArguments.isEmpty then sourceFrames
        else .apply sourceExtraArguments :: sourceFrames
      if params.isEmpty && sourceArguments.isEmpty then
        .cache name :: frames
      else frames
    let targetPreparedFrames :=
      let frames := if targetExtraArguments.isEmpty then targetFrames
        else .apply targetExtraArguments :: targetFrames
      if params.isEmpty && targetArguments.isEmpty then
        .cache name :: frames
      else frames
    ReachableMachineRelated fuel rho
      { sourceState with
        env := sourceEnv
        joins := []
        frames := sourcePreparedFrames
        control := .code sourceCode }
      { targetState with
        env := targetEnv
        joins := []
        frames := targetPreparedFrames
        control := .code targetCode } := by
  dsimp only
  have callArguments : ArrayRel (ValueRel rho)
      (sourceArguments.extract 0 params.size)
      (targetArguments.extract 0 params.size) :=
    arrayRel_extract arguments 0 params.size
  have argumentSize := arrayRel_size_eq arguments
  have extraArguments : ArrayRel (ValueRel rho)
      (sourceArguments.extract params.size sourceArguments.size)
      (targetArguments.extract params.size targetArguments.size) := by
    simpa [argumentSize] using
      arrayRel_extract arguments params.size sourceArguments.size
  have binding := bindParams_relOn (rho := rho) (params := params)
    used callArguments
  rw [sourceBinding, targetBinding] at binding
  cases binding with
  | ok envRelated =>
      have preparedFrames := frames.prepareCall name params arguments
        extraArguments
      have sourcePartition :=
        array_extract_partition sourceArguments params.size
      have targetPartition :=
        array_extract_partition targetArguments params.size
      have sourceSubset : RootSubset
          (envRootsOn used sourceEnv ++
            (if (sourceArguments.extract params.size sourceArguments.size).isEmpty
              then sourceFrameRoots
              else (sourceArguments.extract params.size
                sourceArguments.size).toList ++ sourceFrameRoots))
          (sourceArguments.toList ++ sourceFrameRoots) := by
        intro root member
        rcases List.mem_append.mp member with boundRoot | preparedRoot
        · apply List.mem_append_left
          rw [← sourcePartition]
          exact List.mem_append_left _
            (envRootsOn_bindParams_subset sourceBinding root boundRoot)
        · by_cases empty :
              (sourceArguments.extract params.size
                sourceArguments.size).isEmpty
          · simp [empty] at preparedRoot
            exact List.mem_append_right _ preparedRoot
          · have preparedRoot' : root ∈
                (sourceArguments.extract params.size
                  sourceArguments.size).toList ++ sourceFrameRoots := by
              simpa only [empty, Bool.false_eq_true, if_false] using
                preparedRoot
            rcases List.mem_append.mp preparedRoot' with
              extraRoot | frameRoot
            · apply List.mem_append_left
              rw [← sourcePartition]
              exact List.mem_append_right _ extraRoot
            · exact List.mem_append_right _ frameRoot
      have targetSubset : RootSubset
          (envRootsOn used targetEnv ++
            (if (targetArguments.extract params.size targetArguments.size).isEmpty
              then targetFrameRoots
              else (targetArguments.extract params.size
                targetArguments.size).toList ++ targetFrameRoots))
          (targetArguments.toList ++ targetFrameRoots) := by
        intro root member
        rcases List.mem_append.mp member with boundRoot | preparedRoot
        · apply List.mem_append_left
          rw [← targetPartition]
          exact List.mem_append_left _
            (envRootsOn_bindParams_subset targetBinding root boundRoot)
        · by_cases empty :
              (targetArguments.extract params.size
                targetArguments.size).isEmpty
          · simp [empty] at preparedRoot
            exact List.mem_append_right _ preparedRoot
          · have preparedRoot' : root ∈
                (targetArguments.extract params.size
                  targetArguments.size).toList ++ targetFrameRoots := by
              simpa only [empty, Bool.false_eq_true, if_false] using
                preparedRoot
            rcases List.mem_append.mp preparedRoot' with
              extraRoot | frameRoot
            · apply List.mem_append_left
              rw [← targetPartition]
              exact List.mem_append_right _ extraRoot
            · exact List.mem_append_right _ frameRoot
      have nextRuntime := runtime.restrictExtra
        (listRel_append (envRootsOn_related envRelated)
          preparedFrames.roots)
        sourceSubset targetSubset
      unfold ReachableMachineRelated
      exact ⟨envRootsOn used sourceEnv, envRootsOn used targetEnv,
        (if (sourceArguments.extract params.size
            sourceArguments.size).isEmpty
          then sourceFrameRoots
          else (sourceArguments.extract params.size
            sourceArguments.size).toList ++ sourceFrameRoots),
        (if (targetArguments.extract params.size
            targetArguments.size).isEmpty
          then targetFrameRoots
          else (targetArguments.extract params.size
            targetArguments.size).toList ++ targetFrameRoots),
        programs, .code body (.empty fuel used) envRelated,
        preparedFrames, nextRuntime⟩

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

theorem initialState_someReachableMachineRelated
    (programs : ProgramRelated (ShadowCodeRelated fuel) sourceProgram
      targetProgram)
    (arguments : ArrayRel (ValueRel emptyAddressRenaming)
      sourceArguments targetArguments) :
    SomeReachableMachineRelated fuel
      (initialState sourceProgram entry sourceArguments)
      (initialState targetProgram entry targetArguments) :=
  ⟨emptyAddressRenaming,
    initialState_reachableMachineRelated programs arguments⟩

/-- A retained return narrows the active runtime roots from the complete live
environment to the returned value, while keeping all saved-frame roots. -/
theorem coreStep_return_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (member : used.contains result = true)
    (sourceRead : lookup sourceState.env result = some sourceValue)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    ∃ targetValue,
      let sourceAfter := {
        sourceState with control := .yielded sourceValue }
      let targetAfter := {
        targetState with control := .yielded targetValue }
      lookup targetState.env result = some targetValue ∧
        ValueRel rho sourceValue targetValue ∧
        coreStep { sourceState with control := .code (.return result) } =
          .next sourceAfter ∧
        coreStep { targetState with control := .code (.return result) } =
          .next targetAfter ∧
        ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  have looked := env result member
  rw [sourceRead] at looked
  generalize targetRead : lookup targetState.env result = targetResult at looked
  cases targetResult with
  | none => cases looked
  | some targetValue =>
      cases looked with
      | some values =>
          dsimp only
          have sourceRoot : sourceValue ∈
              envRootsOn used sourceState.env :=
            lookup_mem_envRootsOn member sourceRead
          have targetRoot : targetValue ∈
              envRootsOn used targetState.env :=
            lookup_mem_envRootsOn member targetRead
          have extra : ListRel (ValueRel rho)
              ([sourceValue] ++ sourceFrameRoots)
              ([targetValue] ++ targetFrameRoots) :=
            listRel_append (.cons values .nil) frames.roots
          have sourceSubset : RootSubset
              ([sourceValue] ++ sourceFrameRoots)
              (envRootsOn used sourceState.env ++ sourceFrameRoots) := by
            intro value live
            simp only [List.mem_append, List.mem_singleton] at live ⊢
            rcases live with same | framed
            · subst value
              exact Or.inl sourceRoot
            · exact Or.inr framed
          have targetSubset : RootSubset
              ([targetValue] ++ targetFrameRoots)
              (envRootsOn used targetState.env ++ targetFrameRoots) := by
            intro value live
            simp only [List.mem_append, List.mem_singleton] at live ⊢
            rcases live with same | framed
            · subst value
              exact Or.inl targetRoot
            · exact Or.inr framed
          have nextRuntime := runtime.restrictExtra extra
            sourceSubset targetSubset
          refine ⟨targetValue, rfl, values, ?_, ?_, ?_⟩
          · simp [coreStep, lookupValue, sourceRead]
          · simp [coreStep, lookupValue, targetRead]
          · unfold ReachableMachineRelated
            exact ⟨[sourceValue], [targetValue],
              sourceFrameRoots, targetFrameRoots,
              programs, .yielded values, frames, nextRuntime⟩

/-- State-level retained-return rule obtained by inverting the existential
roots carried by `ReachableMachineRelated`. -/
theorem ReachableMachineRelated.returnStep
    (related : ReachableMachineRelated fuel rho source target)
    (sourceControl : source.control = .code (.return result))
    (targetControl : target.control = .code (.return result))
    (sourceRead : lookup source.env result = some sourceValue) :
    ∃ targetValue,
      let sourceAfter := { source with control := .yielded sourceValue }
      let targetAfter := { target with control := .yielded targetValue }
      lookup target.env result = some targetValue ∧
        ValueRel rho sourceValue targetValue ∧
        coreStep source = .next sourceAfter ∧
        coreStep target = .next targetAfter ∧
        ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases related with
    ⟨sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  rw [sourceControl, targetControl] at control
  cases control with
  | code graph joins env =>
      cases graph.covered with
      | ret member =>
          have progress := coreStep_return_reachableRelated source target
            programs frames env member sourceRead runtime
          have sourceSame :
              { source with control := .code (.return result) } = source := by
            cases source
            simp_all
          have targetSame :
              { target with control := .code (.return result) } = target := by
            cases target
            simp_all
          rw [sourceSame, targetSame] at progress
          exact progress

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
  · simp only [withCodeControl, coreStep]
    rw [evalLetValue_control_eq, evaluated]
  · unfold ReachableMachineRelated
    refine ⟨envRootsOn used (bind sourceState.env declaration.fvarId value),
      envRootsOn used targetState.env,
      sourceFrameRoots, targetFrameRoots, ?_, ?_, ?_, ?_⟩
    · exact programs
    · exact .code continuation joins (env.bindLeft_of_absent absent)
    · exact frames
    · simpa [envRootsOn_bind_of_absent absent] using runtime

/-- Every deleted literal is machine-safe under reachable observations:
immediates are neutral and heap-backed literals allocate only dead garbage. -/
theorem coreStep_deletedLiteral_reachableRelated
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
    (absent : used.contains fvarId = false)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    let declaration : LCNF.LetDecl .impure := {
      fvarId
      binderName
      type
      value := .lit literalValue }
    ∃ nextRuntime value,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        env := bind sourceState.env fvarId value
        control := .code sourceContinuation }
      coreStep { sourceState with
          control := .code (.let declaration sourceContinuation) } =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  dsimp only
  rcases runtime.evalLetValueLiteralLeftGarbage
      (fvarId := fvarId) (binderName := binderName) (type := type) with
    ⟨nextRuntime, value, evaluated, next⟩
  exact ⟨nextRuntime, value,
    coreStep_deletedLet_reachableRelated sourceState targetState
      programs frames continuation joins env absent evaluated next⟩

/-- Successful argument evaluation and constructor arity are the operational
well-formedness facts needed for a deleted constructor allocation. -/
inductive DeletedCtorReadyAt (state : MachineState) (info : LCNF.CtorInfo)
    (arguments : Array (LCNF.Arg .impure)) : Prop where
  | mk (values : Array Value)
      (argumentsRead : evalArgs state.env arguments = .ok values)
      (arity : values.size = info.size) :
      DeletedCtorReadyAt state info arguments

/-- A deleted constructor is immediate or allocates one unreachable cell, so
its source step preserves the reachable machine relation. -/
theorem coreStep_deletedCtor_of_ready
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
    (absent : used.contains fvarId = false)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedCtorReadyAt sourceState info arguments) :
    let declaration : LCNF.LetDecl .impure := {
      fvarId
      binderName
      type
      value := .ctor info arguments }
    ∃ nextRuntime value,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        env := bind sourceState.env fvarId value
        control := .code sourceContinuation }
      coreStep { sourceState with
          control := .code (.let declaration sourceContinuation) } =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  dsimp only
  rcases ready with ⟨values, argumentsRead, arity⟩
  rcases runtime.evalLetValueCtorLeftGarbage
      (fvarId := fvarId) (binderName := binderName) (type := type)
      argumentsRead arity with
    ⟨nextRuntime, value, evaluated, next⟩
  exact ⟨nextRuntime, value,
    coreStep_deletedLet_reachableRelated sourceState targetState
      programs frames continuation joins env absent evaluated next⟩

/-- Operational well-formedness needed to execute a deleted partial
application: its fixed arguments resolve, its declaration exists, and the
application is genuinely partial. -/
inductive DeletedPapReadyAt (state : MachineState) (name : Name)
    (arguments : Array (LCNF.Arg .impure)) : Prop where
  | mk (target : LCNF.Decl .impure) (values : Array Value)
      (argumentsRead : evalArgs state.env arguments = .ok values)
      (targetFound : state.program.findDecl? name = some target)
      (underapplied : values.size < target.params.size) :
      DeletedPapReadyAt state name arguments

/-- A deleted partial application takes one source step, allocates only
unreachable closure garbage, and leaves the target at its continuation. -/
theorem coreStep_deletedPap_of_ready
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
    (absent : used.contains fvarId = false)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedPapReadyAt sourceState name arguments) :
    let declaration : LCNF.LetDecl .impure := {
      fvarId
      binderName
      type
      value := .pap name arguments }
    ∃ nextRuntime value,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        env := bind sourceState.env fvarId value
        control := .code sourceContinuation }
      coreStep { sourceState with
          control := .code (.let declaration sourceContinuation) } =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  dsimp only
  rcases ready with
    ⟨declaration, values, argumentsRead, targetFound, underapplied⟩
  rcases runtime.evalLetValuePapLeftGarbage
      (fvarId := fvarId) (binderName := binderName) (type := type)
      argumentsRead targetFound underapplied with
    ⟨nextRuntime, value, evaluated, next⟩
  exact ⟨nextRuntime, value,
    coreStep_deletedLet_reachableRelated sourceState targetState
      programs frames continuation joins env absent evaluated next⟩

/-- Proof-visible successful operand shape for a deleted box operation. -/
inductive DeletedBoxReadyAt (state : MachineState) (input : FVarId) : Prop where
  | scalar (value : ScalarValue)
      (inputRead : lookupValue state.env input = .ok (.scalar value)) :
      DeletedBoxReadyAt state input
  | usize (value : UInt64)
      (inputRead : lookupValue state.env input = .ok (.usize value)) :
      DeletedBoxReadyAt state input

/-- A deleted box is immediate or allocates one unreachable boxed cell,
according to the payload range; both shapes permit target stuttering. -/
theorem coreStep_deletedBox_of_ready
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
    (absent : used.contains fvarId = false)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedBoxReadyAt sourceState input) :
    let declaration : LCNF.LetDecl .impure := {
      fvarId
      binderName
      type := resultType
      value := .box boxedType input }
    ∃ nextRuntime value,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        env := bind sourceState.env fvarId value
        control := .code sourceContinuation }
      coreStep { sourceState with
          control := .code (.let declaration sourceContinuation) } =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  dsimp only
  cases ready with
  | scalar scalar inputRead =>
      rcases runtime.boxScalarLeftGarbage boxedType scalar with
        ⟨nextRuntime, value, boxed, next⟩
      have evaluated : evalLetValue sourceState {
          fvarId
          binderName
          type := resultType
          value := .box boxedType input
        } = .ok (nextRuntime, .value value) := by
        simp only [evalLetValue, inputRead, Bind.bind, Except.bind]
        rw [boxed]
        rfl
      exact ⟨nextRuntime, value,
        coreStep_deletedLet_reachableRelated sourceState targetState
          programs frames continuation joins env absent evaluated next⟩
  | usize word inputRead =>
      rcases runtime.boxUSizeLeftGarbage boxedType word with
        ⟨nextRuntime, value, boxed, next⟩
      have evaluated : evalLetValue sourceState {
          fvarId
          binderName
          type := resultType
          value := .box boxedType input
        } = .ok (nextRuntime, .value value) := by
        simp only [evalLetValue, inputRead, Bind.bind, Except.bind]
        rw [boxed]
        rfl
      exact ⟨nextRuntime, value,
        coreStep_deletedLet_reachableRelated sourceState targetState
          programs frames continuation joins env absent evaluated next⟩

/-- Resume related residual continuations after a source-only runtime update
whose reachable roots are unchanged. -/
theorem continueCode_reachableRelated
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
    (runtime : ShadowRuntimeRel rho nextRuntime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    ReachableMachineRelated fuel rho
      { sourceState with
        runtime := nextRuntime
        control := .code sourceContinuation }
      { targetState with control := .code targetContinuation } := by
  unfold ReachableMachineRelated
  exact ⟨envRootsOn used sourceState.env,
    envRootsOn used targetState.env,
    sourceFrameRoots, targetFrameRoots,
    programs, .code continuation joins env, frames, runtime⟩

/-- Deleted object-field write: the source updates an unreachable cell and
the target stutters at the transformed continuation. -/
theorem coreStep_deletedObjectSet_reachableRelated
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
    (objectRead : lookupValue sourceState.env object = .ok objectValue)
    (fieldRead : evalArg sourceState.env field = .ok fieldValue)
    (effect : setObjectField sourceState.runtime objectValue index fieldValue =
      .ok nextRuntime)
    (runtime : ShadowRuntimeRel rho nextRuntime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    let sourceAfter := {
      sourceState with
      runtime := nextRuntime
      control := .code sourceContinuation }
    coreStep (withCodeControl sourceState
        (.oset object index field sourceContinuation)) =
        .next sourceAfter ∧
      ReachableMachineRelated fuel rho sourceAfter
        { targetState with control := .code targetContinuation } := by
  dsimp only
  constructor
  · unfold withCodeControl
    simp only [coreStep]
    rw [objectRead, fieldRead]
    simp only
    rw [effect]
  · exact continueCode_reachableRelated sourceState targetState programs
      frames continuation joins env runtime

/-- Deleted unboxed-word write under the same unreachable-target premise. -/
theorem coreStep_deletedUSizeSet_reachableRelated
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
    (objectRead : lookupValue sourceState.env object = .ok objectValue)
    (fieldRead : lookupValue sourceState.env field = .ok fieldValue)
    (effect : setUSizeField sourceState.runtime objectValue index fieldValue =
      .ok nextRuntime)
    (runtime : ShadowRuntimeRel rho nextRuntime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    let sourceAfter := {
      sourceState with
      runtime := nextRuntime
      control := .code sourceContinuation }
    coreStep (withCodeControl sourceState
        (.uset object index field sourceContinuation)) =
        .next sourceAfter ∧
      ReachableMachineRelated fuel rho sourceAfter
        { targetState with control := .code targetContinuation } := by
  dsimp only
  constructor
  · unfold withCodeControl
    simp only [coreStep]
    rw [objectRead, fieldRead]
    simp only
    rw [effect]
  · exact continueCode_reachableRelated sourceState targetState programs
      frames continuation joins env runtime

/-- Deleted scalar-field write under the same unreachable-target premise. -/
theorem coreStep_deletedScalarSet_reachableRelated
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
    (objectRead : lookupValue sourceState.env object = .ok objectValue)
    (fieldRead : lookupValue sourceState.env field = .ok fieldValue)
    (effect : setScalarField sourceState.runtime objectValue width offset
      fieldValue = .ok nextRuntime)
    (runtime : ShadowRuntimeRel rho nextRuntime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    let sourceAfter := {
      sourceState with
      runtime := nextRuntime
      control := .code sourceContinuation }
    coreStep (withCodeControl sourceState
        (.sset object width offset field type sourceContinuation)) =
        .next sourceAfter ∧
      ReachableMachineRelated fuel rho sourceAfter
        { targetState with control := .code targetContinuation } := by
  dsimp only
  constructor
  · unfold withCodeControl
    simp only [coreStep]
    rw [objectRead, fieldRead]
    simp only
    rw [effect]
  · exact continueCode_reachableRelated sourceState targetState programs
      frames continuation joins env runtime

/-- Proof-visible well-formedness/ownership obligation for deleting an
object-field write.  In particular, dead syntactic liveness alone is not used
as a substitute for semantic unreachability in the presence of aliases. -/
def DeletedObjectSetReadyAt (state : MachineState) (roots : List Value)
    (object : FVarId) (index : Nat) (field : LCNF.Arg .impure) : Prop :=
  ∃ location cell constructor fieldValue,
    lookupValue state.env object = .ok (.object (.heap location)) ∧
    evalArg state.env field = .ok fieldValue ∧
    findCell? state.runtime.heap location = some cell ∧
    cell.live = true ∧
    cell.object = .ctor constructor ∧
    index < constructor.objectFields.size ∧
    ¬Reachable state.runtime.heap roots location

def DeletedUSizeSetReadyAt (state : MachineState) (roots : List Value)
    (object : FVarId) (index : Nat) (field : FVarId) : Prop :=
  ∃ location cell constructor fieldValue,
    lookupValue state.env object = .ok (.object (.heap location)) ∧
    lookupValue state.env field = .ok (.usize fieldValue) ∧
    findCell? state.runtime.heap location = some cell ∧
    cell.live = true ∧
    cell.object = .ctor constructor ∧
    index < constructor.usizeFields.size ∧
    ¬Reachable state.runtime.heap roots location

def DeletedScalarSetReadyAt (state : MachineState) (roots : List Value)
    (object field : FVarId) : Prop :=
  ∃ location cell constructor fieldValue,
    lookupValue state.env object = .ok (.object (.heap location)) ∧
    lookupValue state.env field = .ok (.scalar fieldValue) ∧
    findCell? state.runtime.heap location = some cell ∧
    cell.live = true ∧
    cell.object = .ctor constructor ∧
    ¬Reachable state.runtime.heap roots location

theorem coreStep_deletedObjectSet_of_ready
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedObjectSetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      object index field) :
    ∃ nextRuntime,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        control := .code sourceContinuation }
      coreStep (withCodeControl sourceState
          (.oset object index field sourceContinuation)) =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  rcases ready with
    ⟨location, cell, constructor, fieldValue,
      objectRead, fieldRead, found, live, objectEq, bounded, unreachable⟩
  rcases runtime.setObjectFieldLeftUnreachable found live objectEq bounded
      unreachable fieldValue with
    ⟨nextRuntime, effect, next⟩
  exact ⟨nextRuntime,
    coreStep_deletedObjectSet_reachableRelated sourceState targetState
      programs frames continuation joins env objectRead fieldRead effect next⟩

theorem coreStep_deletedUSizeSet_of_ready
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedUSizeSetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      object index field) :
    ∃ nextRuntime,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        control := .code sourceContinuation }
      coreStep (withCodeControl sourceState
          (.uset object index field sourceContinuation)) =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  rcases ready with
    ⟨location, cell, constructor, fieldValue,
      objectRead, fieldRead, found, live, objectEq, bounded, unreachable⟩
  rcases runtime.setUSizeFieldLeftUnreachable found live objectEq bounded
      unreachable fieldValue with
    ⟨nextRuntime, effect, next⟩
  exact ⟨nextRuntime,
    coreStep_deletedUSizeSet_reachableRelated sourceState targetState
      programs frames continuation joins env objectRead fieldRead effect next⟩

theorem coreStep_deletedScalarSet_of_ready
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedScalarSetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      object field) :
    ∃ nextRuntime,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        control := .code sourceContinuation }
      coreStep (withCodeControl sourceState
          (.sset object width offset field type sourceContinuation)) =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  rcases ready with
    ⟨location, cell, constructor, fieldValue,
      objectRead, fieldRead, found, live, objectEq, unreachable⟩
  rcases runtime.setScalarFieldLeftUnreachable found live objectEq
      unreachable width offset fieldValue with
    ⟨nextRuntime, effect, next⟩
  exact ⟨nextRuntime,
    coreStep_deletedScalarSet_reachableRelated sourceState targetState
      programs frames continuation joins env objectRead fieldRead effect next⟩

/-- Operational ownership split for a deleted `reuse`: a `none` token may
allocate fresh garbage, while a concrete token may overwrite only an
unreachable compiler-owned constructor cell. -/
inductive DeletedReuseReadyAt (state : MachineState) (roots : List Value)
    (token : FVarId) (info : LCNF.CtorInfo)
    (arguments : Array (LCNF.Arg .impure)) : Prop where
  | none (values : Array Value)
      (tokenRead : lookupValue state.env token = .ok (.reuseToken none))
      (argumentsRead : evalArgs state.env arguments = .ok values)
      (arity : values.size = info.size) :
      DeletedReuseReadyAt state roots token info arguments
  | some (location : Location) (cell : HeapCell)
      (oldObject : ConstructorObject) (values : Array Value)
      (tokenRead : lookupValue state.env token =
        .ok (.reuseToken (some location)))
      (argumentsRead : evalArgs state.env arguments = .ok values)
      (found : findCell? state.runtime.heap location = some cell)
      (live : cell.live = true)
      (objectEq : cell.object = .ctor oldObject)
      (arity : values.size = info.size)
      (unreachable : ¬Reachable state.runtime.heap roots location) :
      DeletedReuseReadyAt state roots token info arguments

/-- Machine-level deleted-`reuse` rule.  Both token branches execute one
source step and preserve the reachable runtime while the target stutters. -/
theorem coreStep_deletedReuse_of_ready
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
    (absent : used.contains fvarId = false)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedReuseReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      token info arguments) :
    let declaration : LCNF.LetDecl .impure := {
      fvarId
      binderName
      type
      value := .reuse token info updateHeader arguments }
    ∃ nextRuntime value,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        env := bind sourceState.env fvarId value
        control := .code sourceContinuation }
      coreStep { sourceState with
          control := .code (.let declaration sourceContinuation) } =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  dsimp only
  cases ready with
  | none values tokenRead argumentsRead arity =>
      rcases runtime.evalLetValueReuseNoneLeftGarbage
          (fvarId := fvarId) (binderName := binderName) (type := type)
          tokenRead argumentsRead arity with
        ⟨nextRuntime, value, evaluated, next⟩
      exact ⟨nextRuntime, value,
        coreStep_deletedLet_reachableRelated sourceState targetState
          programs frames continuation joins env absent evaluated next⟩
  | some location cell oldObject values tokenRead argumentsRead found live
      objectEq arity unreachable =>
      rcases runtime.evalLetValueReuseSomeLeftUnreachable
          (fvarId := fvarId) (binderName := binderName) (type := type)
          tokenRead argumentsRead found live objectEq unreachable arity with
        ⟨nextRuntime, evaluated, next⟩
      exact ⟨nextRuntime, .object (.heap location),
        coreStep_deletedLet_reachableRelated sourceState targetState
          programs frames continuation joins env absent evaluated next⟩

/-- Proof-visible ownership contract for deleting a `reset`.  The interpreter
effect must succeed and preserve every heap cell reachable from the active
runtime roots; recursively adjusted garbage remains unconstrained. -/
inductive DeletedResetReadyAt (state : MachineState) (roots : List Value)
    (count : Nat) (object : FVarId) : Prop where
  | mk (objectValue token : Value) (nextRuntime : RuntimeState)
      (objectRead : lookupValue state.env object = .ok objectValue)
      (effect : reset state.runtime count objectValue =
        .ok (nextRuntime, token))
      (frame : RuntimeReachableFrame state.runtime nextRuntime roots) :
      DeletedResetReadyAt state roots count object

/-- Machine-level deleted-`reset` rule under the explicit ownership frame. -/
theorem coreStep_deletedReset_of_ready
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
    (absent : used.contains fvarId = false)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedResetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      count object) :
    let declaration : LCNF.LetDecl .impure := {
      fvarId
      binderName
      type
      value := .reset count object }
    ∃ nextRuntime token,
      let sourceAfter := {
        sourceState with
        runtime := nextRuntime
        env := bind sourceState.env fvarId token
        control := .code sourceContinuation }
      coreStep { sourceState with
          control := .code (.let declaration sourceContinuation) } =
          .next sourceAfter ∧
        ReachableMachineRelated fuel rho sourceAfter
          { targetState with control := .code targetContinuation } := by
  dsimp only
  rcases ready with
    ⟨objectValue, token, nextRuntime, objectRead, effect, frame⟩
  have evaluated : evalLetValue sourceState {
      fvarId
      binderName
      type
      value := .reset count object
    } = .ok (nextRuntime, .value token) := by
    simp only [evalLetValue, objectRead, Bind.bind, Except.bind]
    rw [effect]
    rfl
  have next := runtime.frameLeft frame
  exact ⟨nextRuntime, token,
    coreStep_deletedLet_reachableRelated sourceState targetState
      programs frames continuation joins env absent evaluated next⟩

/-- Unified operational certificate for every locally stutterable deleted
let-value shape.  `runtimeNeutral` covers successful erased/projection/unbox/
`isShared` reads (and other unchanged-runtime values); the remaining
constructors expose the allocation or ownership facts used above.

There is intentionally no nullary `.fap` constructor: evaluating it starts a
possibly observable declaration invocation rather than producing a local
value step.  See `FIR-BUG-impure-elimDeadVars-nullary-fap-effects`. -/
inductive DeletedLetReadyAt (state : MachineState) (roots : List Value) :
    LCNF.LetDecl .impure → Prop where
  | runtimeNeutral (declaration : LCNF.LetDecl .impure) (value : Value)
      (evaluated : evalLetValue state declaration =
        .ok (state.runtime, .value value)) :
      DeletedLetReadyAt state roots declaration
  | literal (fvarId : FVarId) (binderName : Name) (type : Expr)
      (literalValue : LCNF.LitValue) :
      DeletedLetReadyAt state roots {
        fvarId, binderName, type, value := .lit literalValue }
  | constructor (fvarId : FVarId) (binderName : Name) (type : Expr)
      (info : LCNF.CtorInfo) (arguments : Array (LCNF.Arg .impure))
      (ready : DeletedCtorReadyAt state info arguments) :
      DeletedLetReadyAt state roots {
        fvarId, binderName, type, value := .ctor info arguments }
  | partialApplication (fvarId : FVarId) (binderName : Name)
      (type : Expr) (name : Name) (arguments : Array (LCNF.Arg .impure))
      (ready : DeletedPapReadyAt state name arguments) :
      DeletedLetReadyAt state roots {
        fvarId, binderName, type, value := .pap name arguments }
  | box (fvarId : FVarId) (binderName : Name) (resultType boxedType : Expr)
      (input : FVarId) (ready : DeletedBoxReadyAt state input) :
      DeletedLetReadyAt state roots {
        fvarId, binderName, type := resultType, value := .box boxedType input }
  | reset (fvarId : FVarId) (binderName : Name) (type : Expr)
      (count : Nat) (object : FVarId)
      (ready : DeletedResetReadyAt state roots count object) :
      DeletedLetReadyAt state roots {
        fvarId, binderName, type, value := .reset count object }
  | reuse (fvarId : FVarId) (binderName : Name) (type : Expr)
      (token : FVarId) (info : LCNF.CtorInfo) (updateHeader : Bool)
      (arguments : Array (LCNF.Arg .impure))
      (ready : DeletedReuseReadyAt state roots token info arguments) :
      DeletedLetReadyAt state roots {
        fvarId, binderName, type,
        value := .reuse token info updateHeader arguments }

/-- Readiness for a let edge in the reachable-runtime graph.  Retained lets
need no additional semantic premise: their operands are covered by the live
environment relation and both machines will execute them.  A deleted let
must instead carry the operation-specific certificate consumed by the
source-only rule below. -/
inductive ReachableLetReadyAt (fuel : Nat) (used : UsedLocals)
    (declaration : LCNF.LetDecl .impure)
    (sourceContinuation : LCNF.Code .impure) (state : MachineState)
    (roots : List Value) :
    {target : LCNF.Code .impure} →
      ShadowLetResidual fuel used declaration sourceContinuation target →
        Prop where
  | retained (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (covered : LetValueCovered used declaration.value) :
      ReachableLetReadyAt fuel used declaration sourceContinuation state roots
        (.retained targetContinuation continuation covered)
  | deleted (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (absent : used.contains declaration.fvarId = false)
      (ready : DeletedLetReadyAt state roots declaration) :
      ReachableLetReadyAt fuel used declaration sourceContinuation state roots
        (.deleted targetContinuation continuation)

/-- Reachable-runtime readiness for a conditionally deleted object write. -/
inductive ReachableObjectSetReadyAt (fuel : Nat) (used : UsedLocals)
    (object : FVarId) (index : Nat) (field : LCNF.Arg .impure)
    (sourceContinuation : LCNF.Code .impure) (state : MachineState)
    (roots : List Value) :
    {target : LCNF.Code .impure} →
      ShadowObjectSetResidual fuel used object index field sourceContinuation
        target → Prop where
  | retained (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (objectMember : used.contains object = true)
      (fieldCovered : ArgCovered used field) :
      ReachableObjectSetReadyAt fuel used object index field
        sourceContinuation state roots
        (.retained targetContinuation continuation objectMember fieldCovered)
  | deleted (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (ready : DeletedObjectSetReadyAt state roots object index field) :
      ReachableObjectSetReadyAt fuel used object index field
        sourceContinuation state roots
        (.deleted targetContinuation continuation)

/-- Reachable-runtime readiness for a conditionally deleted unboxed write. -/
inductive ReachableUSizeSetReadyAt (fuel : Nat) (used : UsedLocals)
    (object : FVarId) (index : Nat) (field : FVarId)
    (sourceContinuation : LCNF.Code .impure) (state : MachineState)
    (roots : List Value) :
    {target : LCNF.Code .impure} →
      ShadowUSizeSetResidual fuel used object index field sourceContinuation
        target → Prop where
  | retained (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (objectMember : used.contains object = true)
      (fieldMember : used.contains field = true) :
      ReachableUSizeSetReadyAt fuel used object index field
        sourceContinuation state roots
        (.retained targetContinuation continuation objectMember fieldMember)
  | deleted (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (ready : DeletedUSizeSetReadyAt state roots object index field) :
      ReachableUSizeSetReadyAt fuel used object index field
        sourceContinuation state roots
        (.deleted targetContinuation continuation)

/-- Reachable-runtime readiness for a conditionally deleted scalar write. -/
inductive ReachableScalarSetReadyAt (fuel : Nat) (used : UsedLocals)
    (object : FVarId) (width offset : Nat) (field : FVarId) (type : Expr)
    (sourceContinuation : LCNF.Code .impure) (state : MachineState)
    (roots : List Value) :
    {target : LCNF.Code .impure} →
      ShadowScalarSetResidual fuel used object width offset field type
        sourceContinuation target → Prop where
  | retained (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (objectMember : used.contains object = true)
      (fieldMember : used.contains field = true) :
      ReachableScalarSetReadyAt fuel used object width offset field type
        sourceContinuation state roots
        (.retained targetContinuation continuation objectMember fieldMember)
  | deleted (targetContinuation : LCNF.Code .impure)
      (continuation : ShadowCodeGraph fuel used
        sourceContinuation targetContinuation)
      (ready : DeletedScalarSetReadyAt state roots object field) :
      ReachableScalarSetReadyAt fuel used object width offset field type
        sourceContinuation state roots
        (.deleted targetContinuation continuation)

/-- Operational certificate for the active node of a transparent graph.
The graph determines whether a conditional node was retained or deleted;
the certificate adds exactly the semantic premises needed by that branch. -/
inductive ReachableCodeReadyAt (fuel : Nat) (used : UsedLocals)
    (state : MachineState) (roots : List Value) :
    {source target : LCNF.Code .impure} →
      ShadowCodeGraph fuel used source target → Prop where
  | letE
      (graph : ShadowCodeGraph fuel used
        (.let declaration sourceContinuation) target)
      (ready : ReachableLetReadyAt fuel used declaration sourceContinuation
        state roots graph.letResidual) :
      ReachableCodeReadyAt fuel used state roots graph
  | join
      (graph : ShadowCodeGraph fuel used
        (.jp declaration sourceContinuation) target)
      (ready : ShadowJoinReadyAt fuel used declaration sourceContinuation
        graph.joinResidual) :
      ReachableCodeReadyAt fuel used state roots graph
  | cases
      (graph : ShadowCodeGraph fuel used (.cases caseInfo) target) :
      ReachableCodeReadyAt fuel used state roots graph
  | jump
      (graph : ShadowCodeGraph fuel used (.jmp join arguments) target) :
      ReachableCodeReadyAt fuel used state roots graph
  | ret
      (graph : ShadowCodeGraph fuel used (.return value) target) :
      ReachableCodeReadyAt fuel used state roots graph
  | unreachable
      (graph : ShadowCodeGraph fuel used (.unreach type) target) :
      ReachableCodeReadyAt fuel used state roots graph
  | setTag
      (graph : ShadowCodeGraph fuel used
        (.setTag object tag continuation) target) :
      ReachableCodeReadyAt fuel used state roots graph
  | increment
      (graph : ShadowCodeGraph fuel used
        (.inc object amount check persistent continuation) target) :
      ReachableCodeReadyAt fuel used state roots graph
  | decrement
      (graph : ShadowCodeGraph fuel used
        (.dec object amount check persistent objects continuation) target) :
      ReachableCodeReadyAt fuel used state roots graph
  | delete
      (graph : ShadowCodeGraph fuel used (.del object continuation) target) :
      ReachableCodeReadyAt fuel used state roots graph
  | objectSet
      (graph : ShadowCodeGraph fuel used
        (.oset object index field continuation) target)
      (ready : ReachableObjectSetReadyAt fuel used object index field
        continuation state roots graph.objectSetResidual) :
      ReachableCodeReadyAt fuel used state roots graph
  | usizeSet
      (graph : ShadowCodeGraph fuel used
        (.uset object index field continuation) target)
      (ready : ReachableUSizeSetReadyAt fuel used object index field
        continuation state roots graph.usizeSetResidual) :
      ReachableCodeReadyAt fuel used state roots graph
  | scalarSet
      (graph : ShadowCodeGraph fuel used
        (.sset object width offset field type continuation) target)
      (ready : ReachableScalarSetReadyAt fuel used object width offset field
        type continuation state roots graph.scalarSetResidual) :
      ReachableCodeReadyAt fuel used state roots graph

/-- Readiness for an arbitrary related control.  Invocation and yielded
controls impose no local operation premise; code controls expose the exact
graph and complete source runtime roots used by deletion certificates. -/
def ReachableControlReadyAt (fuel : Nat) (sourceState : MachineState)
    (sourceFrameRoots : List Value) (sourceControl targetControl : Control) :
    Prop :=
  ∀ {used sourceCode targetCode},
    sourceControl = .code sourceCode →
    targetControl = .code targetCode →
    (graph : ShadowCodeGraph fuel used sourceCode targetCode) →
      ReachableCodeReadyAt fuel used sourceState
        (runtimeRoots sourceState.runtime
          (envRootsOn used sourceState.env ++ sourceFrameRoots)) graph

/-- Pair-level form used by the eventual simulation laws.  It is universal
over the proof-valued root witnesses hidden by `ReachableMachineRelated`, so
readiness cannot depend on choosing a more convenient decomposition. -/
def ReachableMachineReadyAt (fuel : Nat) (source target : MachineState) :
    Prop :=
  ∀ {rho sourceControlRoots targetControlRoots
      sourceFrameRoots targetFrameRoots},
    ProgramRelated (ShadowCodeRelated fuel) source.program target.program →
    ReachableControlRelated fuel rho
      source.env source.joins source.control
      target.env target.joins target.control
      sourceControlRoots targetControlRoots →
    ReachableFramesRelated fuel rho source.frames target.frames
      sourceFrameRoots targetFrameRoots →
    ShadowRuntimeRel rho source.runtime target.runtime
      (sourceControlRoots ++ sourceFrameRoots)
      (targetControlRoots ++ targetFrameRoots) →
    ReachableControlReadyAt fuel source sourceFrameRoots
      source.control target.control

/-- Structural reachability plus a separately maintained semantic invariant.
The invariant will supply active readiness and be preserved across the
finite paths chosen by the non-lockstep simulation. -/
structure ReachableMachineRelatedWith (fuel : Nat)
    (invariant : MachineState → MachineState → Prop)
    (source target : MachineState) : Prop where
  structural : SomeReachableMachineRelated fuel source target
  invariant : invariant source target

/-- Laws expected from compiler well-formedness and ownership analysis.  In
particular, `ready` makes the nullary-FAP discrepancy an explicit unprovable
obligation rather than an assumption inside the operational proof. -/
structure ReachableInvariantLaws (externals : ExternalSpec) (fuel : Nat)
    (invariant : MachineState → MachineState → Prop) : Prop where
  ready : ∀ {source target},
    SomeReachableMachineRelated fuel source target →
    invariant source target → ReachableMachineReadyAt fuel source target
  stable : ∀ {sourceBefore targetBefore sourceAfter targetAfter},
    invariant sourceBefore targetBefore →
    SomeReachableMachineRelated fuel sourceBefore targetBefore →
    NonLockstep.Reaches externals sourceBefore sourceAfter →
    NonLockstep.Reaches externals targetBefore targetAfter →
    SomeReachableMachineRelated fuel sourceAfter targetAfter →
      invariant sourceAfter targetAfter

/-- A nullary full application can never satisfy the local deleted-let
certificate: evaluating it produces an invocation action, not a value. -/
theorem DeletedLetReadyAt.not_nullaryFap
    (ready : DeletedLetReadyAt state roots {
      fvarId, binderName, type, value := .fap name #[] }) : False := by
  cases ready with
  | runtimeNeutral declaration value evaluated =>
      have empty : evalArgs state.env #[] = .ok #[] := by
        unfold evalArgs
        rw [Array.mapM_empty]
        rfl
      simp only [evalLetValue] at evaluated
      rw [empty] at evaluated
      change Except.ok (state.runtime, LetAction.invokeName name #[]) =
        Except.ok (state.runtime, LetAction.value value) at evaluated
      cases evaluated

/-- General deleted-let stuttering rule.  Once the transparent graph supplies
the related continuation and binder absence, `DeletedLetReadyAt` dispatches
all locally value-producing safe-elimination shapes to one source step and
zero target steps. -/
theorem coreStep_deletedLet_of_ready
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedLetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      declaration) :
    ∃ nextRuntime value,
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
  cases ready with
  | runtimeNeutral declaration value evaluated =>
      exact ⟨sourceState.runtime, value,
        coreStep_deletedLet_reachableRelated sourceState targetState
          programs frames continuation joins env absent evaluated runtime⟩
  | literal fvarId binderName type literalValue =>
      exact coreStep_deletedLiteral_reachableRelated
        (literalValue := literalValue) sourceState targetState
        programs frames continuation joins env absent runtime
  | constructor fvarId binderName type info arguments ready =>
      exact coreStep_deletedCtor_of_ready sourceState targetState
        programs frames continuation joins env absent runtime ready
  | partialApplication fvarId binderName type name arguments ready =>
      exact coreStep_deletedPap_of_ready sourceState targetState
        programs frames continuation joins env absent runtime ready
  | box fvarId binderName resultType boxedType input ready =>
      exact coreStep_deletedBox_of_ready sourceState targetState
        programs frames continuation joins env absent runtime ready
  | reset fvarId binderName type count object ready =>
      exact coreStep_deletedReset_of_ready sourceState targetState
        programs frames continuation joins env absent runtime ready
  | reuse fvarId binderName type token info updateHeader arguments ready =>
      exact coreStep_deletedReuse_of_ready sourceState targetState
        programs frames continuation joins env absent runtime ready

/-- Semantic-step form of the unified deleted-let rule.  Determinism forces
any source `Step` at this control to be the internal step exhibited above;
the target matches it with the reflexive (zero-step) path required by a
non-lockstep simulation. -/
theorem match_deletedLetStep_of_ready
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedLetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      declaration)
    (step : Step externals
      { sourceState with
        control := .code (.let declaration sourceContinuation) }
      sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetContinuation }
        targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases coreStep_deletedLet_of_ready sourceState targetState programs frames
      continuation joins env absent runtime ready with
    ⟨nextRuntime, value, transition, afterRelated⟩
  cases step with
  | internal actual =>
      rw [transition] at actual
      cases actual
      exact ⟨_, NonLockstep.reaches_refl _, afterRelated⟩
  | external actual externalProof =>
      rw [transition] at actual
      contradiction

/-- Determinism turns any exhibited source-only core transition into the
zero-target-step branch of the relational simulation. -/
theorem match_sourceOnlyCoreStep
    (transition : coreStep source = .next expectedSourceAfter)
    (related : ReachableMachineRelated fuel rho expectedSourceAfter target)
    (step : Step externals source sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals target targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  cases step with
  | internal actual =>
      rw [transition] at actual
      cases actual
      exact ⟨target, NonLockstep.reaches_refl target, related⟩
  | external actual externalProof =>
      rw [transition] at actual
      contradiction

/-- Determinism also packages an exhibited pair of internal transitions as a
one-step target match. -/
theorem match_internalCoreSteps
    (sourceTransition : coreStep source = .next expectedSourceAfter)
    (targetTransition : coreStep target = .next targetAfter)
    (related : ReachableMachineRelated fuel rho
      expectedSourceAfter targetAfter)
    (step : Step externals source sourceAfter) :
    NonLockstep.Reaches externals target targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  cases step with
  | internal actual =>
      rw [sourceTransition] at actual
      cases actual
      exact ⟨NonLockstep.reaches_of_step (.internal targetTransition), related⟩
  | external actual externalProof =>
      rw [sourceTransition] at actual
      contradiction

/-- Restoring related bind frames installs the yielded values in the saved
environments and narrows the runtime extras to the resumed code and remaining
stack. -/
theorem coreStep_yieldedBind_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho sourceFrames targetFrames
      sourceFrameRoots targetFrameRoots)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used sourceJoins targetJoins)
    (env : EnvRelOn rho used sourceEnv targetEnv)
    (value : ValueRel rho sourceValue targetValue)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ([sourceValue] ++
        (envRootsOn used sourceEnv ++ sourceFrameRoots))
      ([targetValue] ++
        (envRootsOn used targetEnv ++ targetFrameRoots))) :
    let sourceAfter := {
      sourceState with
      env := bind sourceEnv binder sourceValue
      joins := sourceJoins
      frames := sourceFrames
      control := .code sourceContinuation }
    let targetAfter := {
      targetState with
      env := bind targetEnv binder targetValue
      joins := targetJoins
      frames := targetFrames
      control := .code targetContinuation }
    coreStep { sourceState with
        frames := .bind binder sourceContinuation sourceEnv sourceJoins ::
          sourceFrames
        control := .yielded sourceValue } = .next sourceAfter ∧
      coreStep { targetState with
        frames := .bind binder targetContinuation targetEnv targetJoins ::
          targetFrames
        control := .yielded targetValue } = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
  have nextEnv := env.bindBoth (binder := binder) value
  have extra : ListRel (ValueRel rho)
      (envRootsOn used (bind sourceEnv binder sourceValue) ++
        sourceFrameRoots)
      (envRootsOn used (bind targetEnv binder targetValue) ++
        targetFrameRoots) :=
    listRel_append (envRootsOn_related nextEnv) frames.roots
  have sourceSubset : RootSubset
      (envRootsOn used (bind sourceEnv binder sourceValue) ++
        sourceFrameRoots)
      ([sourceValue] ++
        (envRootsOn used sourceEnv ++ sourceFrameRoots)) := by
    intro root member
    simp only [List.mem_append, List.mem_singleton] at member ⊢
    rcases member with changed | framed
    · have rooted := envRootsOn_bind_subset root changed
      simp only [List.mem_cons] at rooted
      rcases rooted with same | old
      · exact Or.inl same
      · exact Or.inr (Or.inl old)
    · exact Or.inr (Or.inr framed)
  have targetSubset : RootSubset
      (envRootsOn used (bind targetEnv binder targetValue) ++
        targetFrameRoots)
      ([targetValue] ++
        (envRootsOn used targetEnv ++ targetFrameRoots)) := by
    intro root member
    simp only [List.mem_append, List.mem_singleton] at member ⊢
    rcases member with changed | framed
    · have rooted := envRootsOn_bind_subset root changed
      simp only [List.mem_cons] at rooted
      rcases rooted with same | old
      · exact Or.inl same
      · exact Or.inr (Or.inl old)
    · exact Or.inr (Or.inr framed)
  have nextRuntime := runtime.restrictExtra extra sourceSubset targetSubset
  unfold ReachableMachineRelated
  exact ⟨envRootsOn used (bind sourceEnv binder sourceValue),
    envRootsOn used (bind targetEnv binder targetValue),
    sourceFrameRoots, targetFrameRoots,
    programs, .code continuation joins nextEnv, frames, nextRuntime⟩

/-- Restoring related apply frames turns the yielded values into related
function positions and retains the saved argument roots. -/
theorem coreStep_yieldedApply_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho sourceFrames targetFrames
      sourceFrameRoots targetFrameRoots)
    (value : ValueRel rho sourceValue targetValue)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ([sourceValue] ++ (sourceArguments.toList ++ sourceFrameRoots))
      ([targetValue] ++ (targetArguments.toList ++ targetFrameRoots))) :
    let sourceAfter := {
      sourceState with
      frames := sourceFrames
      control := .invokeValue sourceValue sourceArguments }
    let targetAfter := {
      targetState with
      frames := targetFrames
      control := .invokeValue targetValue targetArguments }
    coreStep { sourceState with
        frames := .apply sourceArguments :: sourceFrames
        control := .yielded sourceValue } = .next sourceAfter ∧
      coreStep { targetState with
        frames := .apply targetArguments :: targetFrames
        control := .yielded targetValue } = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
  unfold ReachableMachineRelated
  exact ⟨sourceValue :: sourceArguments.toList,
    targetValue :: targetArguments.toList,
    sourceFrameRoots, targetFrameRoots,
    programs, .invokeValue value arguments, frames, by simpa using runtime⟩

/-- Semantic-step wrapper for restoring related bind frames. -/
theorem match_yieldedBindStep
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho sourceFrames targetFrames
      sourceFrameRoots targetFrameRoots)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used sourceJoins targetJoins)
    (env : EnvRelOn rho used sourceEnv targetEnv)
    (value : ValueRel rho sourceValue targetValue)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ([sourceValue] ++
        (envRootsOn used sourceEnv ++ sourceFrameRoots))
      ([targetValue] ++
        (envRootsOn used targetEnv ++ targetFrameRoots)))
    (step : Step externals
      { sourceState with
        frames := .bind binder sourceContinuation sourceEnv sourceJoins ::
          sourceFrames
        control := .yielded sourceValue } sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with
          frames := .bind binder targetContinuation targetEnv targetJoins ::
            targetFrames
          control := .yielded targetValue } targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases coreStep_yieldedBind_reachableRelated sourceState targetState
      programs frames continuation joins env value runtime with
    ⟨sourceTransition, targetTransition, afterRelated⟩
  exact ⟨_, match_internalCoreSteps sourceTransition targetTransition
    afterRelated step⟩

/-- Semantic-step wrapper for restoring related apply frames. -/
theorem match_yieldedApplyStep
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho sourceFrames targetFrames
      sourceFrameRoots targetFrameRoots)
    (value : ValueRel rho sourceValue targetValue)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ([sourceValue] ++ (sourceArguments.toList ++ sourceFrameRoots))
      ([targetValue] ++ (targetArguments.toList ++ targetFrameRoots)))
    (step : Step externals
      { sourceState with
        frames := .apply sourceArguments :: sourceFrames
        control := .yielded sourceValue } sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with
          frames := .apply targetArguments :: targetFrames
          control := .yielded targetValue } targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases coreStep_yieldedApply_reachableRelated sourceState targetState
      programs frames value arguments runtime with
    ⟨sourceTransition, targetTransition, afterRelated⟩
  exact ⟨_, match_internalCoreSteps sourceTransition targetTransition
    afterRelated step⟩

/-- A retained join declaration takes the same administrative step on both
sides and installs related declaration bodies under the common identifier. -/
theorem coreStep_retainedJoin_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (declaration : ShadowFunDeclRelated fuel used
      sourceDeclaration targetDeclaration)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    let sourceAfter := {
      sourceState with
      joins := (sourceDeclaration.fvarId, sourceDeclaration) ::
        sourceState.joins
      control := .code sourceContinuation }
    let targetAfter := {
      targetState with
      joins := (targetDeclaration.fvarId, targetDeclaration) ::
        targetState.joins
      control := .code targetContinuation }
    coreStep { sourceState with
        control := .code (.jp sourceDeclaration sourceContinuation) } =
        .next sourceAfter ∧
      coreStep { targetState with
        control := .code (.jp targetDeclaration targetContinuation) } =
        .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
  unfold ReachableMachineRelated
  exact ⟨envRootsOn used sourceState.env,
    envRootsOn used targetState.env,
    sourceFrameRoots, targetFrameRoots,
    programs,
    .code continuation
      (joins.consBothOfKeys declaration.fvarId_eq declaration) env,
    frames, runtime⟩

/-- Semantic-step form of a retained join declaration. -/
theorem match_retainedJoinStep
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (declaration : ShadowFunDeclRelated fuel used
      sourceDeclaration targetDeclaration)
    (continuation : ShadowCodeGraph fuel used
      sourceContinuation targetContinuation)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (step : Step externals
      { sourceState with
        control := .code (.jp sourceDeclaration sourceContinuation) }
      sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with
          control := .code (.jp targetDeclaration targetContinuation) }
        targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases coreStep_retainedJoin_reachableRelated sourceState targetState
      programs frames declaration continuation joins env runtime with
    ⟨sourceTransition, targetTransition, related⟩
  exact ⟨_, match_internalCoreSteps sourceTransition targetTransition
    related step⟩

/-- Any semantic step from related retained returns is matched by one target
return step.  A missing source lookup is terminal and therefore cannot have
supplied the `Step` premise. -/
theorem SomeReachableMachineRelated.matchReturnStep
    (related : SomeReachableMachineRelated fuel source target)
    (sourceControl : source.control = .code (.return result))
    (targetControl : target.control = .code (.return result))
    (step : Step externals source sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals target targetAfter ∧
      SomeReachableMachineRelated fuel sourceAfter targetAfter := by
  rcases related with ⟨rho, related⟩
  generalize sourceReadEq : lookup source.env result = sourceRead
  cases sourceRead with
  | none =>
      have sourceDone : coreStep source =
          .done (observe source (.fault (.unknownVar result))) := by
        simp [coreStep, sourceControl, lookupValue, sourceReadEq, fail]
      cases step with
      | internal actual =>
          rw [sourceDone] at actual
          contradiction
      | external actual externalProof =>
          rw [sourceDone] at actual
          contradiction
  | some sourceValue =>
      rcases related.returnStep sourceControl targetControl sourceReadEq with
        ⟨targetValue, targetRead, values,
          sourceTransition, targetTransition, afterRelated⟩
      rcases match_internalCoreSteps sourceTransition targetTransition
          afterRelated step with ⟨targetPath, finalRelated⟩
      exact ⟨_, targetPath, ⟨rho, finalRelated⟩⟩

/-- Graph-level dispatcher for retained returns. -/
theorem match_returnCodeStep
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (graph : ShadowCodeGraph fuel used (.return result) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (step : Step externals
      { sourceState with control := .code (.return result) } sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetCode } targetAfter ∧
      SomeReachableMachineRelated fuel sourceAfter targetAfter := by
  have targetEq := graph.returnTarget
  subst targetCode
  let sourceCurrent :=
    { sourceState with control := .code (.return result) }
  let targetCurrent :=
    { targetState with control := .code (.return result) }
  have currentRelated : ReachableMachineRelated fuel rho
      sourceCurrent targetCurrent := by
    unfold ReachableMachineRelated
    exact ⟨envRootsOn used sourceState.env,
      envRootsOn used targetState.env,
      sourceFrameRoots, targetFrameRoots,
      programs, .code graph joins env, frames, runtime⟩
  have matched :=
    (SomeReachableMachineRelated.matchReturnStep
      (source := sourceCurrent) (target := targetCurrent)
      ⟨rho, currentRelated⟩ rfl rfl (by simpa [sourceCurrent] using step))
  simpa [sourceCurrent, targetCurrent] using matched

/-- A deleted join declaration installs one source-only join entry.  Its
identifier is absent from the active liveness set, so all resumable join
lookups and all reachable runtime roots remain unchanged. -/
theorem coreStep_deletedJoin_reachableRelated
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    let sourceAfter := {
      sourceState with
      joins := (declaration.fvarId, declaration) :: sourceState.joins
      control := .code sourceContinuation }
    coreStep { sourceState with
        control := .code (.jp declaration sourceContinuation) } =
        .next sourceAfter ∧
      ReachableMachineRelated fuel rho sourceAfter
        { targetState with control := .code targetContinuation } := by
  dsimp only
  constructor
  · rfl
  · unfold ReachableMachineRelated
    exact ⟨envRootsOn used sourceState.env,
      envRootsOn used targetState.env,
      sourceFrameRoots, targetFrameRoots,
      programs, .code continuation (joins.consSourceOfAbsent absent) env,
      frames, runtime⟩

/-- Semantic-step form of the deleted-join rule. -/
theorem match_deletedJoinStep
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (step : Step externals
      { sourceState with
        control := .code (.jp declaration sourceContinuation) }
      sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetContinuation }
        targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  have progress := coreStep_deletedJoin_reachableRelated
    sourceState targetState programs frames continuation joins env absent
      runtime
  exact match_sourceOnlyCoreStep progress.1 progress.2 step

/-- Complete graph-level join dispatcher.  The syntactic residual and its
readiness proof choose either the one-step retained match or the zero-step
deleted match. -/
theorem match_joinCodeStep
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (graph : ShadowCodeGraph fuel used
      (.jp sourceDeclaration sourceContinuation) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : ShadowJoinReadyAt fuel used sourceDeclaration
      sourceContinuation graph.joinResidual)
    (step : Step externals
      { sourceState with
        control := .code (.jp sourceDeclaration sourceContinuation) }
      sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetCode } targetAfter ∧
      SomeReachableMachineRelated fuel sourceAfter targetAfter := by
  cases ready with
  | retained targetDeclaration targetContinuation declaration continuation =>
      rcases match_retainedJoinStep sourceState targetState programs frames
          declaration continuation joins env runtime step with
        ⟨targetAfter, targetPath, afterRelated⟩
      exact ⟨targetAfter, targetPath, ⟨rho, afterRelated⟩⟩
  | deleted targetContinuation continuation absent =>
      rcases match_deletedJoinStep sourceState targetState programs frames
          continuation joins env absent runtime step with
        ⟨targetAfter, targetPath, afterRelated⟩
      exact ⟨targetAfter, targetPath, ⟨rho, afterRelated⟩⟩

/-- Semantic-step form of a certified deleted object-field write. -/
theorem match_deletedObjectSetStep_of_ready
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedObjectSetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      object index field)
    (step : Step externals
      (withCodeControl sourceState
        (.oset object index field sourceContinuation)) sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetContinuation }
        targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases coreStep_deletedObjectSet_of_ready sourceState targetState
      programs frames continuation joins env runtime ready with
    ⟨nextRuntime, transition, related⟩
  exact match_sourceOnlyCoreStep transition related step

/-- Semantic-step form of a certified deleted unboxed-field write. -/
theorem match_deletedUSizeSetStep_of_ready
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedUSizeSetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      object index field)
    (step : Step externals
      (withCodeControl sourceState
        (.uset object index field sourceContinuation)) sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetContinuation }
        targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases coreStep_deletedUSizeSet_of_ready sourceState targetState
      programs frames continuation joins env runtime ready with
    ⟨nextRuntime, transition, related⟩
  exact match_sourceOnlyCoreStep transition related step

/-- Semantic-step form of a certified deleted scalar-field write. -/
theorem match_deletedScalarSetStep_of_ready
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
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : DeletedScalarSetReadyAt sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      object field)
    (step : Step externals
      (withCodeControl sourceState
        (.sset object width offset field type sourceContinuation)) sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetContinuation }
        targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases coreStep_deletedScalarSet_of_ready sourceState targetState
      programs frames continuation joins env runtime ready with
    ⟨nextRuntime, transition, related⟩
  exact match_sourceOnlyCoreStep transition related step

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

theorem SomeReachableMachineRelated.yieldedObservation
    (related : SomeReachableMachineRelated fuel source target)
    (sourceControl : source.control = .yielded sourceValue)
    (targetControl : target.control = .yielded targetValue)
    (sourceFrames : source.frames = [])
    (targetFrames : target.frames = []) :
    ObservationRel
      (observe source (.returned sourceValue))
      (observe target (.returned targetValue)) := by
  rcases related with ⟨rho, related⟩
  exact related.yieldedObservation sourceControl targetControl
    sourceFrames targetFrames

end Fir.LeanIR.Passes.ElimDead
