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
