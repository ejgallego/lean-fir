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

/-- A pair of immediate equal-fault results discharges the relational
terminal contract from the reachable runtime invariant. -/
theorem relatedFault_terminal
    (runtime : ShadowRuntimeRel rho source.runtime target.runtime
      sourceRoots targetRoots)
    (sourceDone : coreStep source =
      .done (observe source (.fault fault)))
    (targetDone : coreStep target =
      .done (observe target (.fault fault)))
    (done : coreStep source = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals target targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  have observations : ObservationRel
      (observe source (.fault fault))
      (observe target (.fault fault)) := by
    apply runtime.observationRel
        (leftOutcome := .fault fault) (rightOutcome := .fault fault)
    · rfl
    · intro value member
      simp [outcomeRoots] at member
    · intro value member
      simp [outcomeRoots] at member
  have observationEq : sourceObservation =
      observe source (.fault fault) := by
    rw [sourceDone] at done
    exact (CoreResult.done.inj done).symm
  refine ⟨observe target (.fault fault), ?_, ?_⟩
  · exact ⟨0, target, .refl target, targetDone⟩
  · simpa [observationEq] using observations

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

/-- A successful, fully applied call to related internal declarations takes
one interpreter step on each side and enters states covered by the reachable
machine relation.  Lookup and binding equations are kept explicit so the
later `coreStep` matcher can recover them from source progress. -/
theorem invokeDecl_code_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (body : ShadowCodeGraph fuel used sourceCode targetCode)
    (paramsEq : sourceDeclaration.params = targetDeclaration.params)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (targetFound : targetState.program.findDecl? name =
      some targetDeclaration)
    (sourceValue : sourceDeclaration.value = .code sourceCode)
    (targetValue : targetDeclaration.value = .code targetCode)
    (sourceEnough : ¬ sourceArguments.size < sourceDeclaration.params.size)
    (sourceBinding : bindParams sourceDeclaration.params
      (sourceArguments.extract 0 sourceDeclaration.params.size) =
        .ok sourceEnv)
    (targetBinding : bindParams targetDeclaration.params
      (targetArguments.extract 0 targetDeclaration.params.size) =
        .ok targetEnv)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    let sourceExtraArguments := sourceArguments.extract
      sourceDeclaration.params.size sourceArguments.size
    let targetExtraArguments := targetArguments.extract
      targetDeclaration.params.size targetArguments.size
    let sourcePreparedFrames :=
      let frames := if sourceExtraArguments.isEmpty then sourceState.frames
        else .apply sourceExtraArguments :: sourceState.frames
      if sourceDeclaration.params.isEmpty && sourceArguments.isEmpty then
        .cache name :: frames
      else frames
    let targetPreparedFrames :=
      let frames := if targetExtraArguments.isEmpty then targetState.frames
        else .apply targetExtraArguments :: targetState.frames
      if targetDeclaration.params.isEmpty && targetArguments.isEmpty then
        .cache name :: frames
      else frames
    let sourceAfter := {
      sourceState with
      env := sourceEnv
      joins := []
      frames := sourcePreparedFrames
      control := .code sourceCode }
    let targetAfter := {
      targetState with
      env := targetEnv
      joins := []
      frames := targetPreparedFrames
      control := .code targetCode }
    invokeDecl sourceState name sourceArguments = .next sourceAfter ∧
      invokeDecl targetState name targetArguments = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  dsimp only
  have argumentSize := arrayRel_size_eq arguments
  have targetEnough :
      ¬ targetArguments.size < targetDeclaration.params.size := by
    rw [← paramsEq, ← argumentSize]
    exact sourceEnough
  have sourceStep : invokeDecl sourceState name sourceArguments =
      .next {
        sourceState with
        env := sourceEnv
        joins := []
        frames :=
          (let extraArguments := sourceArguments.extract
              sourceDeclaration.params.size sourceArguments.size
           let frames := if extraArguments.isEmpty then sourceState.frames
             else .apply extraArguments :: sourceState.frames
           if sourceDeclaration.params.isEmpty && sourceArguments.isEmpty then
             .cache name :: frames
           else frames)
        control := .code sourceCode } := by
    unfold invokeDecl
    rw [sourceFound]
    simp only
    rw [if_neg sourceEnough, sourceBinding, sourceValue]
  have targetStep : invokeDecl targetState name targetArguments =
      .next {
        targetState with
        env := targetEnv
        joins := []
        frames :=
          (let extraArguments := targetArguments.extract
              targetDeclaration.params.size targetArguments.size
           let frames := if extraArguments.isEmpty then targetState.frames
             else .apply extraArguments :: targetState.frames
           if targetDeclaration.params.isEmpty && targetArguments.isEmpty then
             .cache name :: frames
           else frames)
        control := .code targetCode } := by
    unfold invokeDecl
    rw [targetFound]
    simp only
    rw [if_neg targetEnough, targetBinding, targetValue]
  refine ⟨sourceStep, targetStep, ?_⟩
  have targetBinding' : bindParams sourceDeclaration.params
      (targetArguments.extract 0 sourceDeclaration.params.size) =
        .ok targetEnv := by
    simpa [paramsEq] using targetBinding
  have entered := enterInternalDecl_reachableRelated
    (fuel := fuel) (rho := rho) (used := used) (name := name)
    sourceState targetState programs frames arguments body
    sourceBinding targetBinding' runtime
  simpa [paramsEq] using entered

/-- Under-applied related declarations allocate matching closures.  Their
fresh locations extend the address renaming, while the fixed arguments become
reachable through the newly yielded closure rather than remaining explicit
machine roots. -/
theorem invokeDecl_partial_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (paramsEq : sourceDeclaration.params = targetDeclaration.params)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (targetFound : targetState.program.findDecl? name =
      some targetDeclaration)
    (sourceTooFew : sourceArguments.size < sourceDeclaration.params.size)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    ∃ larger sourceAfter targetAfter,
      RenamingExtends rho larger ∧
      invokeDecl sourceState name sourceArguments = .next sourceAfter ∧
      invokeDecl targetState name targetArguments = .next targetAfter ∧
      ReachableMachineRelated fuel larger sourceAfter targetAfter := by
  let sourceObject : HeapObject := .closure name
    sourceDeclaration.params.size sourceArguments
  let targetObject : HeapObject := .closure name
    targetDeclaration.params.size targetArguments
  have objects : HeapObjectRel rho sourceObject targetObject := by
    rw [show sourceObject = .closure name sourceDeclaration.params.size
      sourceArguments from rfl]
    rw [show targetObject = .closure name targetDeclaration.params.size
      targetArguments from rfl]
    rw [← paramsEq]
    exact .closure arguments
  have sourceOwned : RootSubset sourceObject.ownedValues.toList
      (runtimeRoots sourceState.runtime
        (sourceArguments.toList ++ sourceFrameRoots)) := by
    intro value member
    apply extra_subset_runtimeRoots
    apply List.mem_append_left
    simpa [sourceObject, HeapObject.ownedValues] using member
  have targetOwned : RootSubset targetObject.ownedValues.toList
      (runtimeRoots targetState.runtime
        (targetArguments.toList ++ targetFrameRoots)) := by
    intro value member
    apply extra_subset_runtimeRoots
    apply List.mem_append_left
    simpa [targetObject, HeapObject.ownedValues] using member
  rcases runtime.allocBoth objects sourceOwned targetOwned false with
    ⟨larger, extension, values, allocatedRuntime⟩
  let sourceRuntime := (alloc sourceState.runtime sourceObject).1
  let targetRuntime := (alloc targetState.runtime targetObject).1
  let sourceValue : Value := .object
    (alloc sourceState.runtime sourceObject).2
  let targetValue : Value := .object
    (alloc targetState.runtime targetObject).2
  have largerFrames := frames.monoRenaming extension
  have sourceSubset : RootSubset
      (sourceValue :: sourceFrameRoots)
      (sourceValue :: sourceArguments.toList ++ sourceFrameRoots) := by
    intro value member
    simp only [List.mem_cons] at member ⊢
    rcases member with same | frameRoot
    · subst value
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (List.mem_append_right _ frameRoot)
  have targetSubset : RootSubset
      (targetValue :: targetFrameRoots)
      (targetValue :: targetArguments.toList ++ targetFrameRoots) := by
    intro value member
    simp only [List.mem_cons] at member ⊢
    rcases member with same | frameRoot
    · subst value
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (List.mem_append_right _ frameRoot)
  have nextRuntime : ShadowRuntimeRel larger sourceRuntime targetRuntime
      (sourceValue :: sourceFrameRoots)
      (targetValue :: targetFrameRoots) := by
    apply allocatedRuntime.restrictExtra
    · exact .cons values largerFrames.roots
    · exact sourceSubset
    · exact targetSubset
  let sourceAfter := sourceState.withValue sourceRuntime sourceValue
  let targetAfter := targetState.withValue targetRuntime targetValue
  have argumentSize := arrayRel_size_eq arguments
  have targetTooFew :
      targetArguments.size < targetDeclaration.params.size := by
    rw [← paramsEq, ← argumentSize]
    exact sourceTooFew
  have sourceStep : invokeDecl sourceState name sourceArguments =
      .next sourceAfter := by
    unfold invokeDecl
    rw [sourceFound]
    simp only
    rw [if_pos sourceTooFew]
  have targetStep : invokeDecl targetState name targetArguments =
      .next targetAfter := by
    unfold invokeDecl
    rw [targetFound]
    simp only
    rw [if_pos targetTooFew]
  refine ⟨larger, sourceAfter, targetAfter, extension, sourceStep,
    targetStep, ?_⟩
  unfold ReachableMachineRelated
  exact ⟨[sourceValue], [targetValue], sourceFrameRoots, targetFrameRoots,
    programs, .yielded values, largerFrames, nextRuntime⟩

/-- Related program lookup supplies the target declaration and matching arity
for the retained partial-application allocation. -/
theorem invokeDecl_foundPartial_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceTooFew : sourceArguments.size < sourceDeclaration.params.size)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    ∃ larger sourceAfter targetAfter,
      RenamingExtends rho larger ∧
      invokeDecl sourceState name sourceArguments = .next sourceAfter ∧
      invokeDecl targetState name targetArguments = .next targetAfter ∧
      ReachableMachineRelated fuel larger sourceAfter targetAfter := by
  have found := programs.findDecl? name
  rw [sourceFound] at found
  generalize targetFound : targetState.program.findDecl? name = targetResult
    at found
  cases found with
  | some declarations =>
      exact invokeDecl_partial_reachableRelated sourceState targetState
        programs frames arguments declarations.params_eq sourceFound
        targetFound sourceTooFew runtime

/-- Related programs agree that a declaration is absent.  Both direct
invocations therefore terminate with the same fault and related observable
runtime state. -/
theorem invokeDecl_unknown_reachableObservation
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (sourceFound : sourceState.program.findDecl? name = none)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      sourceRoots targetRoots) :
    targetState.program.findDecl? name = none ∧
      invokeDecl sourceState name sourceArguments =
        .done (observe sourceState (.fault (.unknownDecl name))) ∧
      invokeDecl targetState name targetArguments =
        .done (observe targetState (.fault (.unknownDecl name))) ∧
      ObservationRel
        (observe sourceState (.fault (.unknownDecl name)))
        (observe targetState (.fault (.unknownDecl name))) := by
  have found := programs.findDecl? name
  rw [sourceFound] at found
  cases targetFound : targetState.program.findDecl? name with
  | some targetDeclaration =>
      rw [targetFound] at found
      cases found
  | none =>
      rw [targetFound] at found
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp [invokeDecl, sourceFound, fail]
      · simp [invokeDecl, targetFound, fail]
      · apply runtime.observationRel
          (leftOutcome := .fault (.unknownDecl name))
          (rightOutcome := .fault (.unknownDecl name))
        · rfl
        · intro value member
          simp [outcomeRoots] at member
        · intro value member
          simp [outcomeRoots] at member

/-- Related declarations and argument arrays produce the same parameter
binding fault before declaration bodies or external metadata are inspected. -/
theorem invokeDecl_bindingFault_reachableObservation
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceEnough : ¬ sourceArguments.size < sourceDeclaration.params.size)
    (sourceBinding : bindParams sourceDeclaration.params
      (sourceArguments.extract 0 sourceDeclaration.params.size) =
        .error fault)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      sourceRoots targetRoots) :
    ∃ targetDeclaration,
      targetState.program.findDecl? name = some targetDeclaration ∧
      invokeDecl sourceState name sourceArguments =
        .done (observe sourceState (.fault fault)) ∧
      invokeDecl targetState name targetArguments =
        .done (observe targetState (.fault fault)) ∧
      ObservationRel
        (observe sourceState (.fault fault))
        (observe targetState (.fault fault)) := by
  have found := programs.findDecl? name
  rw [sourceFound] at found
  generalize targetFound : targetState.program.findDecl? name = targetResult
    at found
  cases found with
  | some declarations =>
      rename_i targetDeclaration
      have argumentSize := arrayRel_size_eq arguments
      have targetEnough :
          ¬ targetArguments.size < targetDeclaration.params.size := by
        rw [← declarations.params_eq, ← argumentSize]
        exact sourceEnough
      have callArguments : ArrayRel (ValueRel rho)
          (sourceArguments.extract 0 sourceDeclaration.params.size)
          (targetArguments.extract 0 sourceDeclaration.params.size) :=
        arrayRel_extract arguments 0 sourceDeclaration.params.size
      have binding := bindParams_relOn (rho := rho)
        (params := sourceDeclaration.params) ({} : UsedLocals) callArguments
      rw [sourceBinding] at binding
      generalize targetBinding : bindParams sourceDeclaration.params
          (targetArguments.extract 0 sourceDeclaration.params.size) =
            targetBindingResult at binding
      cases targetBindingResult with
      | ok targetEnv => cases binding
      | error targetFault =>
          cases binding with
          | error =>
              have targetBinding' : bindParams targetDeclaration.params
                  (targetArguments.extract 0 targetDeclaration.params.size) =
                    .error fault := by
                simpa [← declarations.params_eq] using targetBinding
              refine ⟨targetDeclaration, rfl, ?_, ?_, ?_⟩
              · unfold invokeDecl
                rw [sourceFound]
                simp only
                rw [if_neg sourceEnough, sourceBinding]
                rfl
              · unfold invokeDecl
                rw [targetFound]
                simp only
                rw [if_neg targetEnough, targetBinding']
                rfl
              · apply runtime.observationRel
                    (leftOutcome := .fault fault)
                    (rightOutcome := .fault fault)
                · rfl
                · intro value member
                  simp [outcomeRoots] at member
                · intro value member
                  simp [outcomeRoots] at member

/-- The named-call dispatcher reaches `invokeDecl` either because arguments
are nonempty or because an empty call missed the global cache. -/
inductive InvokeNameDeclReady (runtime : RuntimeState) (name : Name)
    (arguments : Array Value) : Prop where
  | nonempty (ready : arguments.isEmpty = false) :
      InvokeNameDeclReady runtime name arguments
  | cacheMiss (empty : arguments.isEmpty = true)
      (miss : findGlobal? runtime.globals name = none) :
      InvokeNameDeclReady runtime name arguments

theorem InvokeNameDeclReady.related
    (ready : InvokeNameDeclReady sourceRuntime name sourceArguments)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (globals : ListRel (NamedValueRel rho)
      sourceRuntime.globals targetRuntime.globals) :
    InvokeNameDeclReady targetRuntime name targetArguments := by
  have argumentSize := arrayRel_size_eq arguments
  cases ready with
  | nonempty sourceNonempty =>
      exact .nonempty (by
        simpa [Array.isEmpty, argumentSize] using sourceNonempty)
  | cacheMiss sourceEmpty sourceMiss =>
      have targetEmpty : targetArguments.isEmpty = true := by
        simpa [Array.isEmpty, argumentSize] using sourceEmpty
      have found := findGlobal?_related globals name
      rw [sourceMiss] at found
      cases targetFound : findGlobal? targetRuntime.globals name with
      | none => exact .cacheMiss targetEmpty targetFound
      | some targetValue =>
          rw [targetFound] at found
          cases found

/-- Once both dispatchers are known to reach declaration invocation, matched
`invokeDecl` transitions are exactly matched `coreStep` transitions. -/
theorem coreStep_invokeName_of_declReady
    (sourceState targetState sourceAfter targetAfter : MachineState)
    (sourceReady : InvokeNameDeclReady sourceState.runtime name
      sourceArguments)
    (targetReady : InvokeNameDeclReady targetState.runtime name
      targetArguments)
    (sourceStep : invokeDecl
      { sourceState with control := .invokeName name sourceArguments }
      name sourceArguments = .next sourceAfter)
    (targetStep : invokeDecl
      { targetState with control := .invokeName name targetArguments }
      name targetArguments = .next targetAfter) :
    coreStep { sourceState with
      control := .invokeName name sourceArguments } = .next sourceAfter ∧
    coreStep { targetState with
      control := .invokeName name targetArguments } = .next targetAfter := by
  constructor
  · cases sourceReady with
    | nonempty nonempty => simpa [coreStep, nonempty] using sourceStep
    | cacheMiss empty miss =>
        simpa [coreStep, empty, miss] using sourceStep
  · cases targetReady with
    | nonempty nonempty => simpa [coreStep, nonempty] using targetStep
    | cacheMiss empty miss =>
        simpa [coreStep, empty, miss] using targetStep

/-- A declaration-ready named call to an unknown declaration satisfies the
terminal simulation contract immediately. -/
theorem coreStep_invokeName_unknown_terminal
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceReady : InvokeNameDeclReady sourceState.runtime name
      sourceArguments)
    (sourceFound : sourceState.program.findDecl? name = none)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      sourceRoots targetRoots)
    (done : coreStep { sourceState with
      control := .invokeName name sourceArguments } = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with
          control := .invokeName name targetArguments }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  let sourceInvoke := {
    sourceState with control := .invokeName name sourceArguments }
  let targetInvoke := {
    targetState with control := .invokeName name targetArguments }
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFound : sourceInvoke.program.findDecl? name = none := by
    simpa [sourceInvoke] using sourceFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime sourceRoots targetRoots := by
    simpa [sourceInvoke, targetInvoke] using runtime
  rcases invokeDecl_unknown_reachableObservation
      (sourceArguments := sourceArguments) (targetArguments := targetArguments)
      sourceInvoke targetInvoke invokePrograms invokeFound invokeRuntime with
    ⟨targetFound, sourceFault, targetFault, observations⟩
  have targetReady := sourceReady.related arguments runtime.globals
  have sourceCore : coreStep sourceInvoke =
      .done (observe sourceInvoke (.fault (.unknownDecl name))) := by
    cases sourceReady with
    | nonempty nonempty =>
        simpa [sourceInvoke, coreStep, nonempty] using sourceFault
    | cacheMiss empty miss =>
        simpa [sourceInvoke, coreStep, empty, miss] using sourceFault
  have targetCore : coreStep targetInvoke =
      .done (observe targetInvoke (.fault (.unknownDecl name))) := by
    cases targetReady with
    | nonempty nonempty =>
        simpa [targetInvoke, coreStep, nonempty] using targetFault
    | cacheMiss empty miss =>
        simpa [targetInvoke, coreStep, empty, miss] using targetFault
  have observationEq : sourceObservation =
      observe sourceInvoke (.fault (.unknownDecl name)) := by
    rw [sourceCore] at done
    exact (CoreResult.done.inj done).symm
  refine ⟨observe targetInvoke (.fault (.unknownDecl name)), ?_, ?_⟩
  · exact ⟨0, targetInvoke, .refl targetInvoke, targetCore⟩
  · simpa [sourceInvoke, targetInvoke, observationEq] using observations

/-- A declaration-ready named call whose source parameter binding fails
satisfies the terminal simulation contract with the same target fault. -/
theorem coreStep_invokeName_bindingFault_terminal
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceReady : InvokeNameDeclReady sourceState.runtime name
      sourceArguments)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceEnough : ¬ sourceArguments.size < sourceDeclaration.params.size)
    (sourceBinding : bindParams sourceDeclaration.params
      (sourceArguments.extract 0 sourceDeclaration.params.size) =
        .error fault)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      sourceRoots targetRoots)
    (done : coreStep { sourceState with
      control := .invokeName name sourceArguments } = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with
          control := .invokeName name targetArguments }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  let sourceInvoke := {
    sourceState with control := .invokeName name sourceArguments }
  let targetInvoke := {
    targetState with control := .invokeName name targetArguments }
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFound : sourceInvoke.program.findDecl? name =
      some sourceDeclaration := by
    simpa [sourceInvoke] using sourceFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime sourceRoots targetRoots := by
    simpa [sourceInvoke, targetInvoke] using runtime
  rcases invokeDecl_bindingFault_reachableObservation
      sourceInvoke targetInvoke invokePrograms arguments invokeFound
      sourceEnough sourceBinding invokeRuntime with
    ⟨targetDeclaration, targetFound, sourceFault, targetFault, observations⟩
  have targetReady := sourceReady.related arguments runtime.globals
  have sourceCore : coreStep sourceInvoke =
      .done (observe sourceInvoke (.fault fault)) := by
    cases sourceReady with
    | nonempty nonempty =>
        simpa [sourceInvoke, coreStep, nonempty] using sourceFault
    | cacheMiss empty miss =>
        simpa [sourceInvoke, coreStep, empty, miss] using sourceFault
  have targetCore : coreStep targetInvoke =
      .done (observe targetInvoke (.fault fault)) := by
    cases targetReady with
    | nonempty nonempty =>
        simpa [targetInvoke, coreStep, nonempty] using targetFault
    | cacheMiss empty miss =>
        simpa [targetInvoke, coreStep, empty, miss] using targetFault
  have terminal := relatedFault_terminal
    (externals := externals) invokeRuntime sourceCore targetCore
    (by simpa [sourceInvoke] using done)
  simpa [targetInvoke] using terminal

/-- A retained under-application is matched at `coreStep` whenever named-call
dispatch is known to reach `invokeDecl`; this includes both nonempty calls and
empty cache misses. -/
theorem coreStep_invokeName_foundPartial_of_declReady_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceReady : InvokeNameDeclReady sourceState.runtime name
      sourceArguments)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceTooFew : sourceArguments.size < sourceDeclaration.params.size)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    ∃ larger sourceAfter targetAfter,
      RenamingExtends rho larger ∧
      coreStep { sourceState with
        control := .invokeName name sourceArguments } = .next sourceAfter ∧
      coreStep { targetState with
        control := .invokeName name targetArguments } = .next targetAfter ∧
      ReachableMachineRelated fuel larger sourceAfter targetAfter := by
  let sourceInvoke := {
    sourceState with control := .invokeName name sourceArguments }
  let targetInvoke := {
    targetState with control := .invokeName name targetArguments }
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFrames : ReachableFramesRelated fuel rho
      sourceInvoke.frames targetInvoke.frames sourceFrameRoots
      targetFrameRoots := by
    simpa [sourceInvoke, targetInvoke] using frames
  have invokeFound : sourceInvoke.program.findDecl? name =
      some sourceDeclaration := by
    simpa [sourceInvoke] using sourceFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using runtime
  rcases invokeDecl_foundPartial_reachableRelated
      (fuel := fuel) (rho := rho) sourceInvoke targetInvoke invokePrograms
      invokeFrames arguments invokeFound sourceTooFew invokeRuntime with
    ⟨larger, sourceAfter, targetAfter, extension, sourceStep, targetStep,
      nextRelated⟩
  have targetReady := sourceReady.related arguments runtime.globals
  have steps := coreStep_invokeName_of_declReady
    sourceState targetState sourceAfter targetAfter sourceReady targetReady
    (by simpa [sourceInvoke] using sourceStep)
    (by simpa [targetInvoke] using targetStep)
  exact ⟨larger, sourceAfter, targetAfter, extension, steps.1, steps.2,
    nextRelated⟩

/-- Nonempty under-applied named calls take one allocating `coreStep` on each
side and re-establish the machine invariant under an extended renaming. -/
theorem coreStep_invokeName_nonempty_foundPartial_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceNonempty : sourceArguments.isEmpty = false)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceTooFew : sourceArguments.size < sourceDeclaration.params.size)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    ∃ larger sourceAfter targetAfter,
      RenamingExtends rho larger ∧
      coreStep { sourceState with
        control := .invokeName name sourceArguments } = .next sourceAfter ∧
      coreStep { targetState with
        control := .invokeName name targetArguments } = .next targetAfter ∧
      ReachableMachineRelated fuel larger sourceAfter targetAfter := by
  let sourceInvoke := {
    sourceState with control := .invokeName name sourceArguments }
  let targetInvoke := {
    targetState with control := .invokeName name targetArguments }
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFrames : ReachableFramesRelated fuel rho
      sourceInvoke.frames targetInvoke.frames sourceFrameRoots
      targetFrameRoots := by
    simpa [sourceInvoke, targetInvoke] using frames
  have invokeFound : sourceInvoke.program.findDecl? name =
      some sourceDeclaration := by
    simpa [sourceInvoke] using sourceFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using runtime
  rcases invokeDecl_foundPartial_reachableRelated
      (fuel := fuel) (rho := rho) sourceInvoke targetInvoke invokePrograms
      invokeFrames arguments invokeFound sourceTooFew invokeRuntime with
    ⟨larger, sourceAfter, targetAfter, extension, sourceStep, targetStep,
      nextRelated⟩
  have argumentSize := arrayRel_size_eq arguments
  have targetNonempty : targetArguments.isEmpty = false := by
    simpa [Array.isEmpty, argumentSize] using sourceNonempty
  refine ⟨larger, sourceAfter, targetAfter, extension, ?_, ?_, nextRelated⟩
  · simpa [sourceInvoke, coreStep, sourceNonempty] using sourceStep
  · simpa [targetInvoke, coreStep, targetNonempty] using targetStep

/-- Program relatedness turns a successful source lookup of an internal
declaration into the matching target lookup, body graph, and parameter
binding needed by `invokeDecl_code_reachableRelated`. -/
theorem invokeDecl_foundCode_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceValue : sourceDeclaration.value = .code sourceCode)
    (sourceEnough : ¬ sourceArguments.size < sourceDeclaration.params.size)
    (sourceBinding : bindParams sourceDeclaration.params
      (sourceArguments.extract 0 sourceDeclaration.params.size) =
        .ok sourceEnv)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    ∃ targetDeclaration targetCode, ∃ targetEnv : Env,
      ∃ sourceAfter targetAfter,
      targetState.program.findDecl? name = some targetDeclaration ∧
      targetDeclaration.value = .code targetCode ∧
      invokeDecl sourceState name sourceArguments = .next sourceAfter ∧
      invokeDecl targetState name targetArguments = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  have found := programs.findDecl? name
  rw [sourceFound] at found
  generalize targetFound : targetState.program.findDecl? name = targetResult
    at found
  cases found with
  | some declarations =>
      rename_i targetDeclaration
      have valueRelated := declarations.value
      generalize targetValueEq : targetDeclaration.value = targetDeclValue
        at valueRelated
      rw [sourceValue] at valueRelated
      cases valueRelated with
      | code bodyRelated =>
          rename_i targetCode
          rcases bodyRelated with ⟨used, body⟩
          have callArguments : ArrayRel (ValueRel rho)
              (sourceArguments.extract 0 sourceDeclaration.params.size)
              (targetArguments.extract 0 sourceDeclaration.params.size) :=
            arrayRel_extract arguments 0 sourceDeclaration.params.size
          have binding := bindParams_relOn (rho := rho)
            (params := sourceDeclaration.params) used callArguments
          rw [sourceBinding] at binding
          generalize targetBinding : bindParams sourceDeclaration.params
              (targetArguments.extract 0 sourceDeclaration.params.size) =
                targetBindingResult at binding
          cases targetBindingResult with
          | error fault => cases binding
          | ok targetEnv =>
              cases binding with
              | ok envRelated =>
                  have targetBinding' : bindParams targetDeclaration.params
                      (targetArguments.extract 0
                        targetDeclaration.params.size) = .ok targetEnv := by
                    simpa [← declarations.params_eq] using targetBinding
                  have progress := invokeDecl_code_reachableRelated
                    (fuel := fuel) (rho := rho) (used := used)
                    sourceState targetState programs frames arguments body
                    declarations.params_eq sourceFound targetFound
                    sourceValue targetValueEq sourceEnough sourceBinding
                    targetBinding'
                    runtime
                  rcases progress with
                    ⟨sourceStep, targetStep, nextRelated⟩
                  exact ⟨targetDeclaration, targetCode, targetEnv, _, _,
                    rfl, targetValueEq, sourceStep, targetStep,
                    nextRelated⟩

/-- A fully applied internal declaration is matched at `coreStep` for either
form of declaration-ready named dispatch: nonempty arguments or an empty
cache miss. -/
theorem coreStep_invokeName_foundCode_of_declReady_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceReady : InvokeNameDeclReady sourceState.runtime name
      sourceArguments)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceValue : sourceDeclaration.value = .code sourceCode)
    (sourceEnough : ¬ sourceArguments.size < sourceDeclaration.params.size)
    (sourceBinding : bindParams sourceDeclaration.params
      (sourceArguments.extract 0 sourceDeclaration.params.size) =
        .ok sourceEnv)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    ∃ sourceAfter targetAfter,
      coreStep { sourceState with
        control := .invokeName name sourceArguments } = .next sourceAfter ∧
      coreStep { targetState with
        control := .invokeName name targetArguments } = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  let sourceInvoke := {
    sourceState with control := .invokeName name sourceArguments }
  let targetInvoke := {
    targetState with control := .invokeName name targetArguments }
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFrames : ReachableFramesRelated fuel rho
      sourceInvoke.frames targetInvoke.frames sourceFrameRoots
      targetFrameRoots := by
    simpa [sourceInvoke, targetInvoke] using frames
  have invokeFound : sourceInvoke.program.findDecl? name =
      some sourceDeclaration := by
    simpa [sourceInvoke] using sourceFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using runtime
  rcases invokeDecl_foundCode_reachableRelated
      (fuel := fuel) (rho := rho) sourceInvoke targetInvoke invokePrograms
      invokeFrames arguments invokeFound sourceValue sourceEnough sourceBinding
      invokeRuntime with
    ⟨targetDeclaration, targetCode, targetEnv, sourceAfter, targetAfter,
      targetFound, targetValue, sourceStep, targetStep, nextRelated⟩
  have targetReady := sourceReady.related arguments runtime.globals
  have steps := coreStep_invokeName_of_declReady
    sourceState targetState sourceAfter targetAfter sourceReady targetReady
    (by simpa [sourceInvoke] using sourceStep)
    (by simpa [targetInvoke] using targetStep)
  exact ⟨sourceAfter, targetAfter, steps.1, steps.2, nextRelated⟩

/-- A nonempty named call bypasses the global cache on both sides.  When its
source declaration is an internal body and parameter binding succeeds, the
actual `coreStep` transitions enter related transformed declaration bodies. -/
theorem coreStep_invokeName_nonempty_foundCode_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceNonempty : sourceArguments.isEmpty = false)
    (sourceFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceValue : sourceDeclaration.value = .code sourceCode)
    (sourceEnough : ¬ sourceArguments.size < sourceDeclaration.params.size)
    (sourceBinding : bindParams sourceDeclaration.params
      (sourceArguments.extract 0 sourceDeclaration.params.size) =
        .ok sourceEnv)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    ∃ sourceAfter targetAfter,
      coreStep { sourceState with
        control := .invokeName name sourceArguments } = .next sourceAfter ∧
      coreStep { targetState with
        control := .invokeName name targetArguments } = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  let sourceInvoke := {
    sourceState with control := .invokeName name sourceArguments }
  let targetInvoke := {
    targetState with control := .invokeName name targetArguments }
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFrames : ReachableFramesRelated fuel rho
      sourceInvoke.frames targetInvoke.frames sourceFrameRoots
      targetFrameRoots := by
    simpa [sourceInvoke, targetInvoke] using frames
  have invokeFound : sourceInvoke.program.findDecl? name =
      some sourceDeclaration := by
    simpa [sourceInvoke] using sourceFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using runtime
  rcases invokeDecl_foundCode_reachableRelated
      (fuel := fuel) (rho := rho) sourceInvoke targetInvoke invokePrograms
      invokeFrames arguments invokeFound sourceValue sourceEnough sourceBinding
      invokeRuntime with
    ⟨targetDeclaration, targetCode, targetEnv, sourceAfter, targetAfter,
      targetFound, targetValue, sourceStep, targetStep, nextRelated⟩
  have argumentSize := arrayRel_size_eq arguments
  have targetNonempty : targetArguments.isEmpty = false := by
    simpa [Array.isEmpty, argumentSize] using sourceNonempty
  refine ⟨sourceAfter, targetAfter, ?_, ?_, nextRelated⟩
  · simpa [sourceInvoke, coreStep, sourceNonempty] using sourceStep
  · simpa [targetInvoke, coreStep, targetNonempty] using targetStep

/-- Empty named calls consult related global tables in lockstep.  A cache hit
publishes related yielded values without changing either runtime; those values
were already live through the global roots. -/
theorem coreStep_invokeName_cacheHit_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (sourceEmpty : sourceArguments.isEmpty = true)
    (sourceGlobal : findGlobal? sourceState.runtime.globals name =
      some sourceValue)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (sourceArguments.toList ++ sourceFrameRoots)
      (targetArguments.toList ++ targetFrameRoots)) :
    ∃ targetValue sourceAfter targetAfter,
      findGlobal? targetState.runtime.globals name = some targetValue ∧
      coreStep { sourceState with
        control := .invokeName name sourceArguments } = .next sourceAfter ∧
      coreStep { targetState with
        control := .invokeName name targetArguments } = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  have globals := findGlobal?_related runtime.globals name
  rw [sourceGlobal] at globals
  cases targetGlobal : findGlobal? targetState.runtime.globals name with
  | none =>
      rw [targetGlobal] at globals
      cases globals
  | some targetValue =>
      rw [targetGlobal] at globals
      cases globals with
      | some values =>
          have published := runtime.prependGlobal values sourceGlobal
            targetGlobal
          have sourceSubset : RootSubset
              (sourceValue :: sourceFrameRoots)
              (sourceValue :: sourceArguments.toList ++ sourceFrameRoots) := by
            intro value member
            simp only [List.mem_cons] at member ⊢
            rcases member with same | frameRoot
            · subst value
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _
                (List.mem_append_right _ frameRoot)
          have targetSubset : RootSubset
              (targetValue :: targetFrameRoots)
              (targetValue :: targetArguments.toList ++ targetFrameRoots) := by
            intro value member
            simp only [List.mem_cons] at member ⊢
            rcases member with same | frameRoot
            · subst value
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _
                (List.mem_append_right _ frameRoot)
          have nextRuntime := published.restrictExtra
            (.cons values frames.roots) sourceSubset targetSubset
          let sourceAfter := {
            sourceState with control := .yielded sourceValue }
          let targetAfter := {
            targetState with control := .yielded targetValue }
          have argumentSize := arrayRel_size_eq arguments
          have targetEmpty : targetArguments.isEmpty = true := by
            simpa [Array.isEmpty, argumentSize] using sourceEmpty
          have sourceStep : coreStep { sourceState with
              control := .invokeName name sourceArguments } =
              .next sourceAfter := by
            simp [coreStep, sourceEmpty, sourceGlobal, sourceAfter]
          have targetStep : coreStep { targetState with
              control := .invokeName name targetArguments } =
              .next targetAfter := by
            simp [coreStep, targetEmpty, targetGlobal, targetAfter]
          refine ⟨targetValue, sourceAfter, targetAfter, rfl,
            sourceStep, targetStep, ?_⟩
          unfold ReachableMachineRelated
          exact ⟨[sourceValue], [targetValue], sourceFrameRoots,
            targetFrameRoots, programs, .yielded values, frames, nextRuntime⟩

/-- Invoking a reachable mapped closure reads related fixed arguments from
the two heaps, appends the fresh argument arrays, and enters related internal
declaration bodies through the ordinary declaration-invocation theorem. -/
theorem coreStep_invokeValue_closure_foundCode_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (mapping : rho.forward sourceLocation = some targetLocation)
    (sourceCellFound : findCell? sourceState.runtime.heap sourceLocation =
      some sourceCell)
    (sourceLive : sourceCell.live = true)
    (sourceObject : sourceCell.object =
      .closure name arity sourceFixed)
    (sourceDeclFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceDeclValue : sourceDeclaration.value = .code sourceCode)
    (sourceEnough : ¬ (sourceFixed ++ sourceArguments).size <
      sourceDeclaration.params.size)
    (sourceBinding : bindParams sourceDeclaration.params
      ((sourceFixed ++ sourceArguments).extract 0
        sourceDeclaration.params.size) = .ok sourceEnv)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ((.object (.heap sourceLocation) :: sourceArguments.toList) ++
        sourceFrameRoots)
      ((.object (.heap targetLocation) :: targetArguments.toList) ++
        targetFrameRoots)) :
    ∃ sourceAfter targetAfter,
      coreStep { sourceState with
        control := .invokeValue (.object (.heap sourceLocation))
          sourceArguments } = .next sourceAfter ∧
      coreStep { targetState with
        control := .invokeValue (.object (.heap targetLocation))
          targetArguments } = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  rcases runtime.readMappedClosure mapping sourceCellFound sourceLive
      sourceObject arguments frames.roots with
    ⟨targetCell, targetFixed, targetCellFound, targetLive, targetObject,
      fixed, invocationRuntime⟩
  let sourceInvoke := {
    sourceState with
    control := .invokeValue (.object (.heap sourceLocation)) sourceArguments }
  let targetInvoke := {
    targetState with
    control := .invokeValue (.object (.heap targetLocation)) targetArguments }
  have combinedArguments : ArrayRel (ValueRel rho)
      (sourceFixed ++ sourceArguments) (targetFixed ++ targetArguments) :=
    arrayRel_append fixed arguments
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFrames : ReachableFramesRelated fuel rho
      sourceInvoke.frames targetInvoke.frames sourceFrameRoots
      targetFrameRoots := by
    simpa [sourceInvoke, targetInvoke] using frames
  have invokeFound : sourceInvoke.program.findDecl? name =
      some sourceDeclaration := by
    simpa [sourceInvoke] using sourceDeclFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      ((sourceFixed ++ sourceArguments).toList ++ sourceFrameRoots)
      ((targetFixed ++ targetArguments).toList ++ targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using invocationRuntime
  rcases invokeDecl_foundCode_reachableRelated
      (fuel := fuel) (rho := rho) sourceInvoke targetInvoke invokePrograms
      invokeFrames combinedArguments invokeFound sourceDeclValue sourceEnough
      sourceBinding invokeRuntime with
    ⟨targetDeclaration, targetCode, targetEnv, sourceAfter, targetAfter,
      targetDeclFound, targetDeclValue, sourceStep, targetStep, nextRelated⟩
  have sourceRead : getLiveCell sourceState.runtime sourceLocation =
      .ok sourceCell := by
    simp [getLiveCell, sourceCellFound, sourceLive]
  have targetRead : getLiveCell targetState.runtime targetLocation =
      .ok targetCell := by
    simp [getLiveCell, targetCellFound, targetLive]
  refine ⟨sourceAfter, targetAfter, ?_, ?_, nextRelated⟩
  · simpa [sourceInvoke, coreStep, invokeClosure, sourceRead,
      sourceObject] using sourceStep
  · simpa [targetInvoke, coreStep, invokeClosure, targetRead,
      targetObject] using targetStep

/-- The same reachable closure read supports retained under-application: the
combined fixed/fresh arguments allocate related closures and extend the
address renaming. -/
theorem coreStep_invokeValue_closure_foundPartial_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (mapping : rho.forward sourceLocation = some targetLocation)
    (sourceCellFound : findCell? sourceState.runtime.heap sourceLocation =
      some sourceCell)
    (sourceLive : sourceCell.live = true)
    (sourceObject : sourceCell.object =
      .closure name arity sourceFixed)
    (sourceDeclFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceTooFew : (sourceFixed ++ sourceArguments).size <
      sourceDeclaration.params.size)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ((.object (.heap sourceLocation) :: sourceArguments.toList) ++
        sourceFrameRoots)
      ((.object (.heap targetLocation) :: targetArguments.toList) ++
        targetFrameRoots)) :
    ∃ larger sourceAfter targetAfter,
      RenamingExtends rho larger ∧
      coreStep { sourceState with
        control := .invokeValue (.object (.heap sourceLocation))
          sourceArguments } = .next sourceAfter ∧
      coreStep { targetState with
        control := .invokeValue (.object (.heap targetLocation))
          targetArguments } = .next targetAfter ∧
      ReachableMachineRelated fuel larger sourceAfter targetAfter := by
  rcases runtime.readMappedClosure mapping sourceCellFound sourceLive
      sourceObject arguments frames.roots with
    ⟨targetCell, targetFixed, targetCellFound, targetLive, targetObject,
      fixed, invocationRuntime⟩
  let sourceInvoke := {
    sourceState with
    control := .invokeValue (.object (.heap sourceLocation)) sourceArguments }
  let targetInvoke := {
    targetState with
    control := .invokeValue (.object (.heap targetLocation)) targetArguments }
  have combinedArguments : ArrayRel (ValueRel rho)
      (sourceFixed ++ sourceArguments) (targetFixed ++ targetArguments) :=
    arrayRel_append fixed arguments
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFrames : ReachableFramesRelated fuel rho
      sourceInvoke.frames targetInvoke.frames sourceFrameRoots
      targetFrameRoots := by
    simpa [sourceInvoke, targetInvoke] using frames
  have invokeFound : sourceInvoke.program.findDecl? name =
      some sourceDeclaration := by
    simpa [sourceInvoke] using sourceDeclFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      ((sourceFixed ++ sourceArguments).toList ++ sourceFrameRoots)
      ((targetFixed ++ targetArguments).toList ++ targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using invocationRuntime
  rcases invokeDecl_foundPartial_reachableRelated
      (fuel := fuel) (rho := rho) sourceInvoke targetInvoke invokePrograms
      invokeFrames combinedArguments invokeFound sourceTooFew invokeRuntime with
    ⟨larger, sourceAfter, targetAfter, extension, sourceStep, targetStep,
      nextRelated⟩
  have sourceRead : getLiveCell sourceState.runtime sourceLocation =
      .ok sourceCell := by
    simp [getLiveCell, sourceCellFound, sourceLive]
  have targetRead : getLiveCell targetState.runtime targetLocation =
      .ok targetCell := by
    simp [getLiveCell, targetCellFound, targetLive]
  refine ⟨larger, sourceAfter, targetAfter, extension, ?_, ?_, nextRelated⟩
  · simpa [sourceInvoke, coreStep, invokeClosure, sourceRead,
      sourceObject] using sourceStep
  · simpa [targetInvoke, coreStep, invokeClosure, targetRead,
      targetObject] using targetStep

/-- A reachable mapped closure whose declaration is absent on the source has
an absent declaration on the target as well.  Reading the closure and
combining its fixed and fresh arguments therefore exposes the same
address-free `unknownDecl` terminal observation on both sides. -/
theorem coreStep_invokeValue_closure_unknown_terminal
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (mapping : rho.forward sourceLocation = some targetLocation)
    (sourceCellFound : findCell? sourceState.runtime.heap sourceLocation =
      some sourceCell)
    (sourceLive : sourceCell.live = true)
    (sourceObject : sourceCell.object =
      .closure name arity sourceFixed)
    (sourceDeclFound : sourceState.program.findDecl? name = none)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ((.object (.heap sourceLocation) :: sourceArguments.toList) ++
        sourceFrameRoots)
      ((.object (.heap targetLocation) :: targetArguments.toList) ++
        targetFrameRoots))
    (done : coreStep { sourceState with
      control := .invokeValue (.object (.heap sourceLocation))
        sourceArguments } = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with
          control := .invokeValue (.object (.heap targetLocation))
            targetArguments }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  rcases runtime.readMappedClosure mapping sourceCellFound sourceLive
      sourceObject arguments frames.roots with
    ⟨targetCell, targetFixed, targetCellFound, targetLive, targetObject,
      fixed, invocationRuntime⟩
  let sourceInvoke := {
    sourceState with
    control := .invokeValue (.object (.heap sourceLocation)) sourceArguments }
  let targetInvoke := {
    targetState with
    control := .invokeValue (.object (.heap targetLocation)) targetArguments }
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFound : sourceInvoke.program.findDecl? name = none := by
    simpa [sourceInvoke] using sourceDeclFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      ((sourceFixed ++ sourceArguments).toList ++ sourceFrameRoots)
      ((targetFixed ++ targetArguments).toList ++ targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using invocationRuntime
  rcases invokeDecl_unknown_reachableObservation
      (fuel := fuel) sourceInvoke targetInvoke invokePrograms invokeFound
      invokeRuntime with
    ⟨targetDeclFound, sourceFault, targetFault, _observations⟩
  have sourceRead : getLiveCell sourceState.runtime sourceLocation =
      .ok sourceCell := by
    simp [getLiveCell, sourceCellFound, sourceLive]
  have targetRead : getLiveCell targetState.runtime targetLocation =
      .ok targetCell := by
    simp [getLiveCell, targetCellFound, targetLive]
  have sourceCore : coreStep sourceInvoke =
      .done (observe sourceInvoke (.fault (.unknownDecl name))) := by
    simpa [sourceInvoke, coreStep, invokeClosure, sourceRead,
      sourceObject] using sourceFault
  have targetCore : coreStep targetInvoke =
      .done (observe targetInvoke (.fault (.unknownDecl name))) := by
    simpa [targetInvoke, coreStep, invokeClosure, targetRead,
      targetObject] using targetFault
  have terminal := relatedFault_terminal
    (externals := externals) invokeRuntime sourceCore targetCore
    (by simpa [sourceInvoke] using done)
  simpa [targetInvoke] using terminal

/-- A reachable mapped closure whose combined fixed and fresh arguments fail
parameter binding terminates with the same address-free binding fault on both
sides. -/
theorem coreStep_invokeValue_closure_bindingFault_terminal
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (arguments : ArrayRel (ValueRel rho)
      sourceArguments targetArguments)
    (mapping : rho.forward sourceLocation = some targetLocation)
    (sourceCellFound : findCell? sourceState.runtime.heap sourceLocation =
      some sourceCell)
    (sourceLive : sourceCell.live = true)
    (sourceObject : sourceCell.object =
      .closure name arity sourceFixed)
    (sourceDeclFound : sourceState.program.findDecl? name =
      some sourceDeclaration)
    (sourceEnough : ¬ (sourceFixed ++ sourceArguments).size <
      sourceDeclaration.params.size)
    (sourceBinding : bindParams sourceDeclaration.params
      ((sourceFixed ++ sourceArguments).extract 0
        sourceDeclaration.params.size) = .error fault)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ((.object (.heap sourceLocation) :: sourceArguments.toList) ++
        sourceFrameRoots)
      ((.object (.heap targetLocation) :: targetArguments.toList) ++
        targetFrameRoots))
    (done : coreStep { sourceState with
      control := .invokeValue (.object (.heap sourceLocation))
        sourceArguments } = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with
          control := .invokeValue (.object (.heap targetLocation))
            targetArguments }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  rcases runtime.readMappedClosure mapping sourceCellFound sourceLive
      sourceObject arguments frames.roots with
    ⟨targetCell, targetFixed, targetCellFound, targetLive, targetObject,
      fixed, invocationRuntime⟩
  let sourceInvoke := {
    sourceState with
    control := .invokeValue (.object (.heap sourceLocation)) sourceArguments }
  let targetInvoke := {
    targetState with
    control := .invokeValue (.object (.heap targetLocation)) targetArguments }
  have combinedArguments : ArrayRel (ValueRel rho)
      (sourceFixed ++ sourceArguments) (targetFixed ++ targetArguments) :=
    arrayRel_append fixed arguments
  have invokePrograms : ProgramRelated (ShadowCodeRelated fuel)
      sourceInvoke.program targetInvoke.program := by
    simpa [sourceInvoke, targetInvoke] using programs
  have invokeFound : sourceInvoke.program.findDecl? name =
      some sourceDeclaration := by
    simpa [sourceInvoke] using sourceDeclFound
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      ((sourceFixed ++ sourceArguments).toList ++ sourceFrameRoots)
      ((targetFixed ++ targetArguments).toList ++ targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using invocationRuntime
  rcases invokeDecl_bindingFault_reachableObservation
      (fuel := fuel) sourceInvoke targetInvoke invokePrograms
      combinedArguments invokeFound sourceEnough sourceBinding invokeRuntime with
    ⟨targetDeclaration, targetDeclFound, sourceFault, targetFault,
      _observations⟩
  have sourceRead : getLiveCell sourceState.runtime sourceLocation =
      .ok sourceCell := by
    simp [getLiveCell, sourceCellFound, sourceLive]
  have targetRead : getLiveCell targetState.runtime targetLocation =
      .ok targetCell := by
    simp [getLiveCell, targetCellFound, targetLive]
  have sourceCore : coreStep sourceInvoke =
      .done (observe sourceInvoke (.fault fault)) := by
    simpa [sourceInvoke, coreStep, invokeClosure, sourceRead,
      sourceObject] using sourceFault
  have targetCore : coreStep targetInvoke =
      .done (observe targetInvoke (.fault fault)) := by
    simpa [targetInvoke, coreStep, invokeClosure, targetRead,
      targetObject] using targetFault
  have terminal := relatedFault_terminal
    (externals := externals) invokeRuntime sourceCore targetCore
    (by simpa [sourceInvoke] using done)
  simpa [targetInvoke] using terminal

/-- Related immediate values and reuse tokens are equally invalid as closure
callees.  Their invocation terminates with the address-free
`expectedClosure` fault on both sides. -/
theorem coreStep_invokeValue_nonHeap_terminal
    (sourceState targetState : MachineState)
    (function : ValueRel rho sourceFunction targetFunction)
    (sourceNotHeap : ∀ location,
      sourceFunction ≠ .object (.heap location))
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      sourceRoots targetRoots)
    (done : coreStep { sourceState with
      control := .invokeValue sourceFunction sourceArguments } =
        .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with
          control := .invokeValue targetFunction targetArguments }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  let sourceInvoke := {
    sourceState with control := .invokeValue sourceFunction sourceArguments }
  let targetInvoke := {
    targetState with control := .invokeValue targetFunction targetArguments }
  have faults :
      coreStep sourceInvoke =
          .done (observe sourceInvoke (.fault .expectedClosure)) ∧
        coreStep targetInvoke =
          .done (observe targetInvoke (.fault .expectedClosure)) := by
    cases function <;>
      simp_all [sourceInvoke, targetInvoke, coreStep, invokeClosure, fail]
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime sourceRoots targetRoots := by
    simpa [sourceInvoke, targetInvoke] using runtime
  have terminal := relatedFault_terminal
    (externals := externals) invokeRuntime faults.1 faults.2
    (by simpa [sourceInvoke] using done)
  simpa [targetInvoke] using terminal

/-- A live mapped heap cell whose object is not a closure has a related live
non-closure target cell, so both invocations terminate with
`expectedClosure`. -/
theorem coreStep_invokeValue_liveNonClosure_terminal
    (sourceState targetState : MachineState)
    (mapping : rho.forward sourceLocation = some targetLocation)
    (sourceCellFound : findCell? sourceState.runtime.heap sourceLocation =
      some sourceCell)
    (sourceLive : sourceCell.live = true)
    (sourceNotClosure : ∀ name arity fixed,
      sourceCell.object ≠ .closure name arity fixed)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      ((.object (.heap sourceLocation) :: sourceArguments.toList) ++
        sourceFrameRoots)
      ((.object (.heap targetLocation) :: targetArguments.toList) ++
        targetFrameRoots))
    (done : coreStep { sourceState with
      control := .invokeValue (.object (.heap sourceLocation))
        sourceArguments } = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with
          control := .invokeValue (.object (.heap targetLocation))
            targetArguments }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  rcases runtime.readMappedCell mapping sourceCellFound with
    ⟨targetCell, targetCellFound, cells⟩
  have targetLive : targetCell.live = true := by
    rw [← cells.2.2.1]
    exact sourceLive
  have objects := cells.2.2.2
  generalize sourceObjectEq : sourceCell.object = sourceObject at objects
  generalize targetObjectEq : targetCell.object = targetObject at objects
  let sourceInvoke := {
    sourceState with
    control := .invokeValue (.object (.heap sourceLocation)) sourceArguments }
  let targetInvoke := {
    targetState with
    control := .invokeValue (.object (.heap targetLocation)) targetArguments }
  have sourceRead : getLiveCell sourceState.runtime sourceLocation =
      .ok sourceCell := by
    simp [getLiveCell, sourceCellFound, sourceLive]
  have targetRead : getLiveCell targetState.runtime targetLocation =
      .ok targetCell := by
    simp [getLiveCell, targetCellFound, targetLive]
  have faults :
      coreStep sourceInvoke =
          .done (observe sourceInvoke (.fault .expectedClosure)) ∧
        coreStep targetInvoke =
          .done (observe targetInvoke (.fault .expectedClosure)) := by
    cases objects <;>
      simp_all [sourceInvoke, targetInvoke, coreStep, invokeClosure,
        sourceRead, targetRead, fail]
  have invokeRuntime : ShadowRuntimeRel rho
      sourceInvoke.runtime targetInvoke.runtime
      ((.object (.heap sourceLocation) :: sourceArguments.toList) ++
        sourceFrameRoots)
      ((.object (.heap targetLocation) :: targetArguments.toList) ++
        targetFrameRoots) := by
    simpa [sourceInvoke, targetInvoke] using runtime
  have terminal := relatedFault_terminal
    (externals := externals) invokeRuntime faults.1 faults.2
    (by simpa [sourceInvoke] using done)
  simpa [targetInvoke] using terminal

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

/-- A retained return whose covered result is absent from the source
environment has an absent target lookup as well.  Both machines therefore
terminate with the same address-free `unknownVar` fault. -/
theorem coreStep_return_unknown_terminal
    (sourceState targetState : MachineState)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (member : used.contains result = true)
    (sourceRead : lookup sourceState.env result = none)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (done : coreStep { sourceState with
      control := .code (.return result) } = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with control := .code (.return result) }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  have looked := env result member
  rw [sourceRead] at looked
  generalize targetRead : lookup targetState.env result = targetResult at looked
  cases targetResult with
  | some targetValue => cases looked
  | none =>
      let sourceReturn := {
        sourceState with control := .code (.return result) }
      let targetReturn := {
        targetState with control := .code (.return result) }
      have sourceFault : coreStep sourceReturn =
          .done (observe sourceReturn (.fault (.unknownVar result))) := by
        simp [sourceReturn, coreStep, lookupValue, sourceRead, fail]
      have targetFault : coreStep targetReturn =
          .done (observe targetReturn (.fault (.unknownVar result))) := by
        simp [targetReturn, coreStep, lookupValue, targetRead, fail]
      have returnRuntime : ShadowRuntimeRel rho
          sourceReturn.runtime targetReturn.runtime
          (envRootsOn used sourceState.env ++ sourceFrameRoots)
          (envRootsOn used targetState.env ++ targetFrameRoots) := by
        simpa [sourceReturn, targetReturn] using runtime
      have terminal := relatedFault_terminal
        (externals := externals) returnRuntime sourceFault targetFault
        (by simpa [sourceReturn] using done)
      simpa [targetReturn] using terminal

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

/-- State-level terminal rule for a retained return whose covered result is
missing from both related environments. -/
theorem ReachableMachineRelated.returnFault_terminal
    (related : ReachableMachineRelated fuel rho source target)
    (sourceControl : source.control = .code (.return result))
    (targetControl : target.control = .code (.return result))
    (sourceRead : lookup source.env result = none)
    (done : coreStep source = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals target targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  rcases related with
    ⟨sourceControlRoots, targetControlRoots,
      sourceFrameRoots, targetFrameRoots,
      programs, control, frames, runtime⟩
  rw [sourceControl, targetControl] at control
  cases control with
  | code graph joins env =>
      cases graph.covered with
      | ret member =>
          have sourceSame :
              { source with control := .code (.return result) } = source := by
            cases source
            simp_all
          have targetSame :
              { target with control := .code (.return result) } = target := by
            cases target
            simp_all
          have terminal := coreStep_return_unknown_terminal
            (externals := externals) source target env member sourceRead runtime
            (by simpa [sourceSame] using done)
          simpa [targetSame] using terminal

/-- An explicit `unreach` node is retained by the transparent pass graph and
terminates both related machines with the same address-free fault. -/
theorem coreStep_unreach_terminal
    (sourceState targetState : MachineState)
    (graph : ShadowCodeGraph fuel used (.unreach type) targetCode)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      sourceRoots targetRoots)
    (done : coreStep { sourceState with
      control := .code (.unreach type) } = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with control := .code targetCode }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  have targetEq := graph.unreachTarget
  subst targetCode
  let sourceUnreach := {
    sourceState with control := .code (.unreach type) }
  let targetUnreach := {
    targetState with control := .code (.unreach type) }
  have sourceFault : coreStep sourceUnreach =
      .done (observe sourceUnreach (.fault .unreachable)) := by
    simp [sourceUnreach, coreStep, fail]
  have targetFault : coreStep targetUnreach =
      .done (observe targetUnreach (.fault .unreachable)) := by
    simp [targetUnreach, coreStep, fail]
  have unreachRuntime : ShadowRuntimeRel rho
      sourceUnreach.runtime targetUnreach.runtime sourceRoots targetRoots := by
    simpa [sourceUnreach, targetUnreach] using runtime
  have terminal := relatedFault_terminal
    (externals := externals) unreachRuntime sourceFault targetFault
    (by simpa [sourceUnreach] using done)
  simpa [targetUnreach] using terminal

/-- Every terminal branch of a retained jump is address-free.  Extensional
join lookup, covered argument evaluation, and relational parameter binding
show that the target raises the same unknown-join, unknown-variable, or arity
fault.  Successful binding is impossible under the source `done` premise. -/
theorem coreStep_jump_terminal
    (sourceState targetState : MachineState)
    (graph : ShadowCodeGraph fuel used (.jmp join arguments) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (done : coreStep { sourceState with
      control := .code (.jmp join arguments) } = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals
        { targetState with control := .code targetCode }
        targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  have targetEq := graph.jumpTarget
  subst targetCode
  have covered := graph.covered
  cases covered with
  | jump targetMember argumentsCovered =>
      let sourceJump := {
        sourceState with control := .code (.jmp join arguments) }
      let targetJump := {
        targetState with control := .code (.jmp join arguments) }
      have jumpRuntime : ShadowRuntimeRel rho
          sourceJump.runtime targetJump.runtime
          (envRootsOn used sourceState.env ++ sourceFrameRoots)
          (envRootsOn used targetState.env ++ targetFrameRoots) := by
        simpa [sourceJump, targetJump] using runtime
      have found := joins join targetMember
      generalize sourceFoundEq :
        findJoinPoint? sourceState.joins join = sourceFound at found
      generalize targetFoundEq :
        findJoinPoint? targetState.joins join = targetFound at found
      cases found with
      | none =>
          have sourceFault : coreStep sourceJump =
              .done (observe sourceJump
                (.fault (.unknownJoinPoint join))) := by
            simp [sourceJump, coreStep, sourceFoundEq, fail]
          have targetFault : coreStep targetJump =
              .done (observe targetJump
                (.fault (.unknownJoinPoint join))) := by
            simp [targetJump, coreStep, targetFoundEq, fail]
          have terminal := relatedFault_terminal
            (externals := externals) jumpRuntime sourceFault targetFault
            (by simpa [sourceJump] using done)
          simpa [targetJump] using terminal
      | some declarations =>
          rename_i sourceDeclaration targetDeclaration
          have evaluated := evalArgs_relOn env argumentsCovered
          generalize sourceArgumentsEq :
            evalArgs sourceState.env arguments = sourceArguments at evaluated
          generalize targetArgumentsEq :
            evalArgs targetState.env arguments = targetArguments at evaluated
          cases evaluated with
          | error fault =>
              have sourceFault : coreStep sourceJump =
                  .done (observe sourceJump (.fault fault)) := by
                simp [sourceJump, coreStep, sourceFoundEq,
                  sourceArgumentsEq, fail]
              have targetFault : coreStep targetJump =
                  .done (observe targetJump (.fault fault)) := by
                simp [targetJump, coreStep, targetFoundEq,
                  targetArgumentsEq, fail]
              have terminal := relatedFault_terminal
                (externals := externals) jumpRuntime sourceFault targetFault
                (by simpa [sourceJump] using done)
              simpa [targetJump] using terminal
          | @ok sourceArguments targetArguments values =>
              have binding := bindParamsOver_relOn (rho := rho) used env values
                (params := sourceDeclaration.params)
              generalize sourceBindingEq :
                bindParamsOver sourceState.env sourceDeclaration.params
                  sourceArguments = sourceBinding at binding
              generalize targetBindingEq :
                bindParamsOver targetState.env sourceDeclaration.params
                  targetArguments = targetBinding at binding
              cases binding with
              | error fault =>
                  have targetBindingActual :
                      bindParamsOver targetState.env targetDeclaration.params
                        targetArguments = .error fault := by
                    simpa [← declarations.params_eq] using targetBindingEq
                  have sourceFault : coreStep sourceJump =
                      .done (observe sourceJump (.fault fault)) := by
                    simp [sourceJump, coreStep, sourceFoundEq,
                      sourceArgumentsEq, sourceBindingEq, fail]
                  have targetFault : coreStep targetJump =
                      .done (observe targetJump (.fault fault)) := by
                    simp [targetJump, coreStep, targetFoundEq,
                      targetArgumentsEq, targetBindingActual, fail]
                  have terminal := relatedFault_terminal
                    (externals := externals) jumpRuntime sourceFault targetFault
                    (by simpa [sourceJump] using done)
                  simpa [targetJump] using terminal
              | @ok sourceNextEnv targetNextEnv nextEnv =>
                  have sourceStep : coreStep sourceJump = .next {
                      sourceJump with
                      env := sourceNextEnv
                      control := .code sourceDeclaration.value } := by
                    simp [sourceJump, coreStep, sourceFoundEq,
                      sourceArgumentsEq, sourceBindingEq]
                  have sourceDone : coreStep sourceJump =
                      .done sourceObservation := by
                    simpa [sourceJump] using done
                  rw [sourceStep] at sourceDone
                  contradiction

/-- A successful retained jump evaluates related argument arrays, binds them
over the related live environments, and enters the recursively related join
bodies.  Publishing `.erased` temporarily is sufficient to justify every
new environment root without adding heap reachability. -/
theorem coreStep_jump_reachableRelated
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (graph : ShadowCodeGraph fuel used (.jmp join arguments) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (sourceFound : findJoinPoint? sourceState.joins join =
      some sourceDeclaration)
    (sourceEvaluated : evalArgs sourceState.env arguments =
      .ok sourceValues)
    (sourceBinding : bindParamsOver sourceState.env sourceDeclaration.params
      sourceValues = .ok sourceNextEnv)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    ∃ targetDeclaration targetValues targetNextEnv sourceAfter targetAfter,
      findJoinPoint? targetState.joins join = some targetDeclaration ∧
      evalArgs targetState.env arguments = .ok targetValues ∧
      bindParamsOver targetState.env targetDeclaration.params targetValues =
        .ok targetNextEnv ∧
      coreStep { sourceState with
        control := .code (.jmp join arguments) } = .next sourceAfter ∧
      coreStep { targetState with
        control := .code targetCode } = .next targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  have targetEq := graph.jumpTarget
  subst targetCode
  have covered := graph.covered
  cases covered with
  | jump targetMember argumentsCovered =>
      have found := joins join targetMember
      rw [sourceFound] at found
      generalize targetFoundEq :
        findJoinPoint? targetState.joins join = targetFound at found
      cases found with
      | some declarations =>
          rename_i targetDeclaration
          have evaluated := evalArgs_relOn env argumentsCovered
          rw [sourceEvaluated] at evaluated
          generalize targetEvaluatedEq :
            evalArgs targetState.env arguments = targetEvaluation at evaluated
          cases evaluated with
          | @ok _ targetValues values =>
              have binding := bindParamsOver_relOn (rho := rho) used env values
                (params := sourceDeclaration.params)
              rw [sourceBinding] at binding
              generalize targetBindingEq :
                bindParamsOver targetState.env sourceDeclaration.params
                  targetValues = targetBinding at binding
              cases binding with
              | @ok _ targetNextEnv nextEnv =>
                  have targetBindingActual :
                      bindParamsOver targetState.env targetDeclaration.params
                        targetValues = .ok targetNextEnv := by
                    simpa [← declarations.params_eq] using targetBindingEq
                  let sourceAfter := {
                    sourceState with
                    env := sourceNextEnv
                    control := .code sourceDeclaration.value }
                  let targetAfter := {
                    targetState with
                    env := targetNextEnv
                    control := .code targetDeclaration.value }
                  have sourceBoundRoots :=
                    envRootsOn_bindParamsOver_subset
                      (used := used) sourceBinding
                  have targetBoundRoots :=
                    envRootsOn_bindParamsOver_subset
                      (used := used) targetBindingActual
                  have sourceArgumentRoots :=
                    evalArgs_values_subset argumentsCovered sourceEvaluated
                  have targetArgumentRoots :=
                    evalArgs_values_subset argumentsCovered targetEvaluatedEq
                  have sourceSubset : RootSubset
                      (envRootsOn used sourceNextEnv ++ sourceFrameRoots)
                      (.erased ::
                        (envRootsOn used sourceState.env ++ sourceFrameRoots)) := by
                    intro root member
                    simp only [List.mem_append, List.mem_cons] at member ⊢
                    rcases member with nextRoot | frameRoot
                    · have rooted := sourceBoundRoots root nextRoot
                      simp only [List.mem_append] at rooted
                      rcases rooted with argumentRoot | oldRoot
                      · have argumentRooted :=
                          sourceArgumentRoots root argumentRoot
                        simp only [List.mem_cons] at argumentRooted
                        rcases argumentRooted with erased | oldRoot
                        · exact Or.inl erased
                        · exact Or.inr (Or.inl oldRoot)
                      · exact Or.inr (Or.inl oldRoot)
                    · exact Or.inr (Or.inr frameRoot)
                  have targetSubset : RootSubset
                      (envRootsOn used targetNextEnv ++ targetFrameRoots)
                      (.erased ::
                        (envRootsOn used targetState.env ++ targetFrameRoots)) := by
                    intro root member
                    simp only [List.mem_append, List.mem_cons] at member ⊢
                    rcases member with nextRoot | frameRoot
                    · have rooted := targetBoundRoots root nextRoot
                      simp only [List.mem_append] at rooted
                      rcases rooted with argumentRoot | oldRoot
                      · have argumentRooted :=
                          targetArgumentRoots root argumentRoot
                        simp only [List.mem_cons] at argumentRooted
                        rcases argumentRooted with erased | oldRoot
                        · exact Or.inl erased
                        · exact Or.inr (Or.inl oldRoot)
                      · exact Or.inr (Or.inl oldRoot)
                    · exact Or.inr (Or.inr frameRoot)
                  have nextRuntime := runtime.prependErased.restrictExtra
                    (listRel_append (envRootsOn_related nextEnv) frames.roots)
                    sourceSubset targetSubset
                  have sourceStep : coreStep { sourceState with
                      control := .code (.jmp join arguments) } =
                      .next sourceAfter := by
                    simp [sourceAfter, coreStep, sourceFound,
                      sourceEvaluated, sourceBinding]
                  have targetStep : coreStep { targetState with
                      control := .code (.jmp join arguments) } =
                      .next targetAfter := by
                    simp [targetAfter, coreStep, targetFoundEq,
                      targetEvaluatedEq, targetBindingActual]
                  have nextRelated : ReachableMachineRelated fuel rho
                      sourceAfter targetAfter := by
                    unfold ReachableMachineRelated
                    exact ⟨envRootsOn used sourceNextEnv,
                      envRootsOn used targetNextEnv,
                      sourceFrameRoots, targetFrameRoots,
                      programs, .code declarations.value joins nextEnv,
                      frames, nextRuntime⟩
                  exact ⟨targetDeclaration, targetValues, targetNextEnv,
                    sourceAfter, targetAfter, rfl, rfl, targetBindingActual,
                    sourceStep, targetStep, nextRelated⟩

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

/-- Successful interpreter lookup is equivalent to the underlying environment
lookup used by the relational liveness invariant. -/
theorem lookupValue_eq_ok_iff :
    lookupValue env fvarId = .ok value ↔ lookup env fvarId = some value := by
  unfold lookupValue
  cases foundEq : lookup env fvarId <;> simp_all

/-- A retained absolute-slot write succeeds on both related machines and
preserves the reachable machine relation. -/
theorem coreStep_retainedUSizeSet_reachableRelated
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
    (objectMember : used.contains object = true)
    (fieldMember : used.contains field = true)
    (objectRead : lookupValue sourceState.env object = .ok objectValue)
    (fieldRead : lookupValue sourceState.env field = .ok fieldValue)
    (effect : setUSizeSlot sourceState.runtime objectValue index fieldValue =
      .ok sourceNextRuntime)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots)) :
    ∃ targetObjectValue targetFieldValue targetNextRuntime,
      lookupValue targetState.env object = .ok targetObjectValue ∧
      lookupValue targetState.env field = .ok targetFieldValue ∧
      setUSizeSlot targetState.runtime targetObjectValue index
          targetFieldValue = .ok targetNextRuntime ∧
      let sourceAfter := {
        sourceState with
        runtime := sourceNextRuntime
        control := .code sourceContinuation }
      let targetAfter := {
        targetState with
        runtime := targetNextRuntime
        control := .code targetContinuation }
      coreStep (withCodeControl sourceState
          (.uset object index field sourceContinuation)) =
          .next sourceAfter ∧
        coreStep (withCodeControl targetState
          (.uset object index field targetContinuation)) =
          .next targetAfter ∧
        ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  have sourceObjectLookup :=
    lookupValue_eq_ok_iff.mp objectRead
  have objects := env object objectMember
  generalize targetObjectLookup :
    lookup targetState.env object = targetObjectOption at objects
  rw [sourceObjectLookup] at objects
  cases objects with
  | some objectValues =>
      rename_i targetObjectValue
      have targetObjectRead :
          lookupValue targetState.env object = .ok targetObjectValue :=
        lookupValue_eq_ok_iff.mpr targetObjectLookup
      have sourceFieldLookup :=
        lookupValue_eq_ok_iff.mp fieldRead
      have fields := env field fieldMember
      generalize targetFieldLookup :
        lookup targetState.env field = targetFieldOption at fields
      rw [sourceFieldLookup] at fields
      cases fields with
      | some fieldValues =>
          rename_i targetFieldValue
          have targetFieldRead :
              lookupValue targetState.env field = .ok targetFieldValue :=
            lookupValue_eq_ok_iff.mpr targetFieldLookup
          have objectRoot :
              objectValue ∈
                envRootsOn used sourceState.env ++ sourceFrameRoots := by
            exact List.mem_append_left _
              (lookup_mem_envRootsOn objectMember sourceObjectLookup)
          rcases runtime.setUSizeSlotBoth_of_related objectRoot objectValues
              fieldValues effect with
            ⟨targetNextRuntime, targetEffect, nextRuntime⟩
          refine ⟨targetObjectValue, targetFieldValue, targetNextRuntime,
            targetObjectRead, targetFieldRead, targetEffect, ?_⟩
          dsimp only
          refine ⟨?_, ?_, ?_⟩
          · unfold withCodeControl
            simp only [coreStep]
            rw [objectRead, fieldRead]
            simp only
            rw [effect]
          · unfold withCodeControl
            simp only [coreStep]
            rw [targetObjectRead, targetFieldRead]
            simp only
            rw [targetEffect]
          · unfold ReachableMachineRelated
            exact ⟨envRootsOn used sourceState.env,
              envRootsOn used targetState.env,
              sourceFrameRoots, targetFrameRoots,
              programs, .code continuation joins env, frames, nextRuntime⟩

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
    (effect : setUSizeSlot sourceState.runtime objectValue index fieldValue =
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
    constructor.objectFields.size ≤ index ∧
    index - constructor.objectFields.size < constructor.usizeFields.size ∧
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
      objectRead, fieldRead, found, live, objectEq, lower, bounded, unreachable⟩
  rcases runtime.setUSizeSlotLeftUnreachable found live objectEq lower bounded
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

/-- Graph-level semantic-step dispatcher for retained jumps.  Every failure
branch is terminal and contradicts the `Step` premise; successful lookup,
evaluation, and binding use the reachable successor theorem above. -/
theorem match_jumpCodeStep
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (graph : ShadowCodeGraph fuel used (.jmp join arguments) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (step : Step externals
      { sourceState with control := .code (.jmp join arguments) } sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetCode } targetAfter ∧
      SomeReachableMachineRelated fuel sourceAfter targetAfter := by
  have targetEq := graph.jumpTarget
  subst targetCode
  let sourceCurrent := {
    sourceState with control := .code (.jmp join arguments) }
  let targetCurrent := {
    targetState with control := .code (.jmp join arguments) }
  have noStep {observation : Observation}
      (sourceDone : coreStep sourceCurrent = .done observation) :
      False := by
    cases step with
    | internal transition =>
        rw [show { sourceState with
          control := .code (.jmp join arguments) } = sourceCurrent by
            rfl] at transition
        rw [sourceDone] at transition
        contradiction
    | external transition externalProof =>
        rw [show { sourceState with
          control := .code (.jmp join arguments) } = sourceCurrent by
            rfl] at transition
        rw [sourceDone] at transition
        contradiction
  generalize sourceFoundEq :
    findJoinPoint? sourceState.joins join = sourceFound
  cases sourceFound with
  | none =>
      have sourceDone : coreStep sourceCurrent =
          .done (observe sourceCurrent
            (.fault (.unknownJoinPoint join))) := by
        simp [sourceCurrent, coreStep, sourceFoundEq, fail]
      exact (noStep sourceDone).elim
  | some sourceDeclaration =>
      generalize sourceEvaluatedEq :
        evalArgs sourceState.env arguments = sourceEvaluation
      cases sourceEvaluation with
      | error fault =>
          have sourceDone : coreStep sourceCurrent =
              .done (observe sourceCurrent (.fault fault)) := by
            simp [sourceCurrent, coreStep, sourceFoundEq,
              sourceEvaluatedEq, fail]
          exact (noStep sourceDone).elim
      | ok sourceValues =>
          generalize sourceBindingEq :
            bindParamsOver sourceState.env sourceDeclaration.params
              sourceValues = sourceBinding
          cases sourceBinding with
          | error fault =>
              have sourceDone : coreStep sourceCurrent =
                  .done (observe sourceCurrent (.fault fault)) := by
                simp [sourceCurrent, coreStep, sourceFoundEq,
                  sourceEvaluatedEq, sourceBindingEq, fail]
              exact (noStep sourceDone).elim
          | ok sourceNextEnv =>
              rcases coreStep_jump_reachableRelated
                  (rho := rho) sourceState targetState programs frames graph
                  joins env sourceFoundEq sourceEvaluatedEq sourceBindingEq
                  runtime with
                ⟨targetDeclaration, targetValues, targetNextEnv,
                  computedSourceAfter, computedTargetAfter,
                  targetFound, targetEvaluated, targetBinding,
                  sourceTransition, targetTransition, afterRelated⟩
              rcases match_internalCoreSteps sourceTransition targetTransition
                  afterRelated step with ⟨targetPath, finalRelated⟩
              exact ⟨computedTargetAfter, targetPath, ⟨rho, finalRelated⟩⟩

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

/-- Semantic-step form of a retained absolute-slot write. Every source fault is
terminal; the successful branch is matched by one target write. -/
theorem match_retainedUSizeSetStep
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
    (objectMember : used.contains object = true)
    (fieldMember : used.contains field = true)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (step : Step externals
      (withCodeControl sourceState
        (.uset object index field sourceContinuation)) sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        (withCodeControl targetState
          (.uset object index field targetContinuation)) targetAfter ∧
      ReachableMachineRelated fuel rho sourceAfter targetAfter := by
  let sourceCurrent := withCodeControl sourceState
    (.uset object index field sourceContinuation)
  have noStep {observation : Observation}
      (done : coreStep sourceCurrent = .done observation) : False := by
    cases step with
    | internal transition =>
        rw [show withCodeControl sourceState
          (.uset object index field sourceContinuation) = sourceCurrent by
            rfl] at transition
        rw [done] at transition
        contradiction
    | external transition externalProof =>
        rw [show withCodeControl sourceState
          (.uset object index field sourceContinuation) = sourceCurrent by
            rfl] at transition
        rw [done] at transition
        contradiction
  generalize objectRead :
    lookupValue sourceState.env object = objectResult
  cases objectResult with
  | error fault =>
      have done : coreStep sourceCurrent =
          .done (observe sourceCurrent (.fault fault)) := by
        simp [sourceCurrent, withCodeControl, coreStep, objectRead, fail]
      exact (noStep done).elim
  | ok objectValue =>
      generalize fieldRead :
        lookupValue sourceState.env field = fieldResult
      cases fieldResult with
      | error fault =>
          have done : coreStep sourceCurrent =
              .done (observe sourceCurrent (.fault fault)) := by
            simp [sourceCurrent, withCodeControl, coreStep, objectRead,
              fieldRead, fail]
          exact (noStep done).elim
      | ok fieldValue =>
          generalize effect :
            setUSizeSlot sourceState.runtime objectValue index fieldValue =
              effectResult
          cases effectResult with
          | error fault =>
              have done : coreStep sourceCurrent =
                  .done (observe sourceCurrent (.fault fault)) := by
                simp [sourceCurrent, withCodeControl, coreStep, objectRead,
                  fieldRead, effect, fail]
              exact (noStep done).elim
          | ok sourceNextRuntime =>
              rcases coreStep_retainedUSizeSet_reachableRelated
                  sourceState targetState programs frames continuation joins
                  env objectMember fieldMember objectRead fieldRead effect
                  runtime with
                ⟨targetObjectValue, targetFieldValue, targetNextRuntime,
                  targetObjectRead, targetFieldRead, targetEffect,
                  sourceTransition, targetTransition, afterRelated⟩
              rcases match_internalCoreSteps sourceTransition targetTransition
                  afterRelated step with
                ⟨targetPath, finalRelated⟩
              exact ⟨_, targetPath, finalRelated⟩

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

/-- Complete graph-level dispatcher for an absolute-slot write. The retained
branch takes one target step; the deleted unreachable branch stutters. -/
theorem match_uSizeSetCodeStep
    (sourceState targetState : MachineState)
    (programs : ProgramRelated (ShadowCodeRelated fuel)
      sourceState.program targetState.program)
    (frames : ReachableFramesRelated fuel rho
      sourceState.frames targetState.frames sourceFrameRoots targetFrameRoots)
    (graph : ShadowCodeGraph fuel used
      (.uset object index field sourceContinuation) targetCode)
    (joins : ShadowJoinEnvRelated fuel used
      sourceState.joins targetState.joins)
    (env : EnvRelOn rho used sourceState.env targetState.env)
    (runtime : ShadowRuntimeRel rho sourceState.runtime targetState.runtime
      (envRootsOn used sourceState.env ++ sourceFrameRoots)
      (envRootsOn used targetState.env ++ targetFrameRoots))
    (ready : ReachableUSizeSetReadyAt fuel used object index field
      sourceContinuation sourceState
      (runtimeRoots sourceState.runtime
        (envRootsOn used sourceState.env ++ sourceFrameRoots))
      graph.usizeSetResidual)
    (step : Step externals
      (withCodeControl sourceState
        (.uset object index field sourceContinuation)) sourceAfter) :
    ∃ targetAfter,
      NonLockstep.Reaches externals
        { targetState with control := .code targetCode } targetAfter ∧
      SomeReachableMachineRelated fuel sourceAfter targetAfter := by
  cases ready with
  | retained targetContinuation continuation objectMember fieldMember =>
      rcases match_retainedUSizeSetStep sourceState targetState programs
          frames continuation joins env objectMember fieldMember runtime step
        with ⟨targetAfter, targetPath, afterRelated⟩
      exact ⟨targetAfter, targetPath, ⟨rho, afterRelated⟩⟩
  | deleted targetContinuation continuation deletedReady =>
      rcases match_deletedUSizeSetStep_of_ready sourceState targetState
          programs frames continuation joins env runtime deletedReady step with
        ⟨targetAfter, targetPath, afterRelated⟩
      exact ⟨targetAfter, targetPath, ⟨rho, afterRelated⟩⟩

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

/-- A related yielded value on empty stacks discharges the relational
terminal contract with zero target steps. -/
theorem ReachableMachineRelated.yielded_terminal
    (related : ReachableMachineRelated fuel rho source target)
    (sourceControl : source.control = .yielded sourceValue)
    (targetControl : target.control = .yielded targetValue)
    (sourceFrames : source.frames = [])
    (targetFrames : target.frames = [])
    (done : coreStep source = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals target targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  have sourceDone : coreStep source =
      .done (observe source (.returned sourceValue)) := by
    simp [coreStep, sourceControl, sourceFrames]
  have targetDone : coreStep target =
      .done (observe target (.returned targetValue)) := by
    simp [coreStep, targetControl, targetFrames]
  have observations := related.yieldedObservation sourceControl targetControl
    sourceFrames targetFrames
  have observationEq : sourceObservation =
      observe source (.returned sourceValue) := by
    rw [sourceDone] at done
    exact (CoreResult.done.inj done).symm
  refine ⟨observe target (.returned targetValue), ?_, ?_⟩
  · exact ⟨0, target, .refl target, targetDone⟩
  · simpa [observationEq] using observations

theorem SomeReachableMachineRelated.yielded_terminal
    (related : SomeReachableMachineRelated fuel source target)
    (sourceControl : source.control = .yielded sourceValue)
    (targetControl : target.control = .yielded targetValue)
    (sourceFrames : source.frames = [])
    (targetFrames : target.frames = [])
    (done : coreStep source = .done sourceObservation) :
    ∃ targetObservation,
      EvaluatesState externals target targetObservation ∧
      ObservationRel sourceObservation targetObservation := by
  rcases related with ⟨rho, related⟩
  exact related.yielded_terminal sourceControl targetControl
    sourceFrames targetFrames done

end Fir.LeanIR.Passes.ElimDead
