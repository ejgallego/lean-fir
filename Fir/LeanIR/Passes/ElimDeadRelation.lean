import Fir.LeanIR.Passes.ElimDeadLiveness

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure

/-!
The execution relation for backwards liveness.

An exact context carries identical environments and needs no syntactic
coverage evidence.  A live context permits the environments to differ, but
records one used set that covers the active code and every installed join
body.  Saved bind frames retain the same distinction.  This is precisely the
information needed when deleting a let introduces one extra binding on only
one side of an otherwise identical execution.
-/

/-- Every installed join body is covered by the same used set as the active
code.  Join environments themselves remain syntactically identical in this
single-program relation. -/
def JoinEnvCovered (used : UsedLocals) (joins : JoinEnv) : Prop :=
  ∀ entry, entry ∈ joins → CodeCovered used entry.2.value

theorem JoinEnvCovered.mono
    (subset : UsedSubset smaller larger)
    (covered : JoinEnvCovered smaller joins) :
    JoinEnvCovered larger joins := by
  intro entry member
  exact (covered entry member).mono subset

theorem JoinEnvCovered.cons
    (bodyCovered : CodeCovered used declaration.value)
    (restCovered : JoinEnvCovered used joins) :
    JoinEnvCovered used ((key, declaration) :: joins) := by
  intro entry member
  simp only [List.mem_cons] at member
  cases member with
  | inl same =>
      subst entry
      exact bodyCovered
  | inr tail => exact restCovered entry tail

/-- A successful join lookup inherits coverage from the installed join
environment. -/
theorem JoinEnvCovered.findJoinPoint
    (covered : JoinEnvCovered used joins)
    (found : findJoinPoint? joins target = some declaration) :
    CodeCovered used declaration.value := by
  induction joins with
  | nil => simp [findJoinPoint?] at found
  | cons entry rest ih =>
      obtain ⟨key, head⟩ := entry
      by_cases sameName : key.name == target.name
      · simp [findJoinPoint?, sameName] at found
        subst declaration
        exact covered (key, head) (by simp)
      · simp [findJoinPoint?, sameName] at found
        apply ih
        · intro candidate member
          exact covered candidate (by simp [member])
        · exact found

/-- Repeatedly binding equal parameter values on both sides preserves live
environment agreement. -/
theorem EnvsAgreeOn.bindPairsBoth
    (agree : EnvsAgreeOn used left right)
    (bindings : List (LCNF.Param .impure × Value)) :
    EnvsAgreeOn used
      (bindings.foldl
        (fun env pair => bind env pair.1.fvarId pair.2) left)
      (bindings.foldl
        (fun env pair => bind env pair.1.fvarId pair.2) right) := by
  induction bindings generalizing left right with
  | nil => exact agree
  | cons binding rest ih =>
      simp only [List.foldl_cons]
      exact ih agree.bindBoth

inductive EnvResultRelated (used : UsedLocals) :
    Except RuntimeFault Env → Except RuntimeFault Env → Prop where
  | error (fault : RuntimeFault) :
      EnvResultRelated used (.error fault) (.error fault)
  | ok (agree : EnvsAgreeOn used left right) :
      EnvResultRelated used (.ok left) (.ok right)

/-- Binding the same evaluated argument array to the same parameter array
either raises the same arity fault or produces agreeing environments. -/
theorem bindParamsOver_liveRelated
    (agree : EnvsAgreeOn used left right) :
    EnvResultRelated used
      (bindParamsOver left params arguments)
      (bindParamsOver right params arguments) := by
  unfold bindParamsOver
  by_cases arity : (params.size == arguments.size) = true
  · simp only [arity, ↓reduceIte]
    exact .ok (agree.bindPairsBoth (params.toList.zip arguments.toList))
  · simp only [arity, ↓reduceIte]
    exact .error _

/-- Let-value evaluation ignores control, joins, and frames. -/
theorem evalLetValue_eq_of_program_runtime_env
    (programEq : left.program = right.program)
    (runtimeEq : left.runtime = right.runtime)
    (envEq : left.env = right.env) :
    evalLetValue left declaration = evalLetValue right declaration := by
  cases left
  cases right
  simp only [MachineState.program, MachineState.runtime, MachineState.env]
    at programEq runtimeEq envEq
  subst_vars
  rfl

/-- Covered let-value evaluation is equal in live-related state fragments. -/
theorem evalLetValue_eq_of_live_env
    (programEq : left.program = right.program)
    (runtimeEq : left.runtime = right.runtime)
    (agree : EnvsAgreeOn used left.env right.env)
    (covered : LetValueCovered used declaration.value) :
    evalLetValue left declaration = evalLetValue right declaration := by
  calc
    evalLetValue left declaration =
        evalLetValue { right with env := left.env } declaration :=
      evalLetValue_eq_of_program_runtime_env programEq runtimeEq rfl
    _ = evalLetValue { right with env := right.env } declaration :=
      evalLetValue_eq_of_covered right agree covered
    _ = evalLetValue right declaration :=
      evalLetValue_eq_of_program_runtime_env rfl rfl rfl

theorem findCtorAlt_member
    (found : findCtorAlt tag alternatives = some code) :
    ∃ alternative, alternative ∈ alternatives ∧
      alternative.getCode = code := by
  induction alternatives with
  | nil => simp [findCtorAlt] at found
  | cons alternative rest ih =>
      cases alternative with
      | ctorAlt info body =>
          by_cases tagEq : info.cidx == tag
          · simp [findCtorAlt, tagEq] at found
            subst code
            exact ⟨.ctorAlt info body, by simp, rfl⟩
          · simp [findCtorAlt, tagEq] at found
            obtain ⟨candidate, member, codeEq⟩ := ih found
            exact ⟨candidate, by simp [member], codeEq⟩
      | default body =>
          simp only [findCtorAlt] at found
          obtain ⟨candidate, member, codeEq⟩ := ih found
          exact ⟨candidate, by simp [member], codeEq⟩
      | alt _ _ _ impossible => nomatch impossible

theorem findDefaultAlt_member
    (found : findDefaultAlt alternatives = some code) :
    ∃ alternative, alternative ∈ alternatives ∧
      alternative.getCode = code := by
  induction alternatives with
  | nil => simp [findDefaultAlt] at found
  | cons alternative rest ih =>
      cases alternative with
      | ctorAlt info body =>
          simp only [findDefaultAlt] at found
          obtain ⟨candidate, member, codeEq⟩ := ih found
          exact ⟨candidate, by simp [member], codeEq⟩
      | default body =>
          simp [findDefaultAlt] at found
          subst code
          exact ⟨.default body, by simp, rfl⟩
      | alt _ _ _ impossible => nomatch impossible

/-- Selecting an arm from a covered case table produces covered code. -/
theorem codeCovered_chooseAlt
    (covered : ∀ alternative, alternative ∈ alternatives →
      CodeCovered used alternative.getCode)
    (selected : chooseAlt tag alternatives = some code) :
    CodeCovered used code := by
  unfold chooseAlt at selected
  cases ctorResult : findCtorAlt tag alternatives with
  | some ctorCode =>
      simp [ctorResult] at selected
      subst code
      obtain ⟨alternative, member, codeEq⟩ :=
        findCtorAlt_member ctorResult
      simpa [codeEq] using covered alternative member
  | none =>
      simp [ctorResult] at selected
      obtain ⟨alternative, member, codeEq⟩ :=
        findDefaultAlt_member selected
      simpa [codeEq] using covered alternative member

/-- Saved continuations are either literally identical, or retain the
liveness evidence and environment agreement needed when they resume. -/
inductive LiveFrameRelated : Frame → Frame → Prop where
  | bindExact (fvarId : FVarId) (continuation : LCNF.Code .impure)
      (env : Env) (joins : JoinEnv) :
      LiveFrameRelated
        (.bind fvarId continuation env joins)
        (.bind fvarId continuation env joins)
  | bindLive
      (continuationCovered : CodeCovered used continuation)
      (joinsCovered : JoinEnvCovered used joins)
      (agree : EnvsAgreeOn used leftEnv rightEnv) :
      LiveFrameRelated
        (.bind fvarId continuation leftEnv joins)
        (.bind fvarId continuation rightEnv joins)
  | apply (arguments : Array Value) :
      LiveFrameRelated (.apply arguments) (.apply arguments)
  | cache (name : Name) :
      LiveFrameRelated (.cache name) (.cache name)

def LiveFramesRelated (left right : List Frame) : Prop :=
  ListRel LiveFrameRelated left right

theorem LiveFrameRelated.symm
    (related : LiveFrameRelated left right) :
    LiveFrameRelated right left := by
  cases related with
  | bindExact fvarId continuation env joins =>
      exact .bindExact fvarId continuation env joins
  | bindLive continuation joins agree =>
      exact .bindLive continuation joins agree.symm
  | apply arguments => exact .apply arguments
  | cache name => exact .cache name

theorem LiveFramesRelated.symm
    (related : LiveFramesRelated left right) :
    LiveFramesRelated right left := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.symm ih

theorem LiveFrameRelated.refl (frame : Frame) :
    LiveFrameRelated frame frame := by
  cases frame with
  | bind fvarId continuation env joins =>
      exact .bindExact fvarId continuation env joins
  | apply arguments => exact .apply arguments
  | cache name => exact .cache name

theorem LiveFramesRelated.refl (frames : List Frame) :
    LiveFramesRelated frames frames := by
  induction frames with
  | nil => exact .nil
  | cons frame rest ih => exact .cons (.refl frame) ih

/-- Active controls are identical.  Code controls additionally distinguish
an exact environment from one that agrees only on a covered used set.  The
current environment and joins are irrelevant while a value or invocation is
in flight; any resumable lexical context lives in the frame stack. -/
inductive LiveControlRelated :
    Env → JoinEnv → Control → Env → JoinEnv → Control → Prop where
  | codeExact (env : Env) (joins : JoinEnv) (code : LCNF.Code .impure) :
      LiveControlRelated env joins (.code code) env joins (.code code)
  | codeLive
      (covered : CodeCovered used code)
      (joinsCovered : JoinEnvCovered used joins)
      (agree : EnvsAgreeOn used leftEnv rightEnv) :
      LiveControlRelated leftEnv joins (.code code)
        rightEnv joins (.code code)
  | yielded (value : Value) :
      LiveControlRelated leftEnv leftJoins (.yielded value)
        rightEnv rightJoins (.yielded value)
  | invokeName (name : Name) (arguments : Array Value) :
      LiveControlRelated leftEnv leftJoins (.invokeName name arguments)
        rightEnv rightJoins (.invokeName name arguments)
  | invokeValue (function : Value) (arguments : Array Value) :
      LiveControlRelated leftEnv leftJoins (.invokeValue function arguments)
        rightEnv rightJoins (.invokeValue function arguments)

theorem LiveControlRelated.symm
    (related : LiveControlRelated leftEnv leftJoins leftControl
      rightEnv rightJoins rightControl) :
    LiveControlRelated rightEnv rightJoins rightControl
      leftEnv leftJoins leftControl := by
  cases related with
  | codeExact => exact .codeExact _ _ _
  | codeLive covered joins agree =>
      exact .codeLive covered joins agree.symm
  | yielded value => exact .yielded value
  | invokeName name arguments => exact .invokeName name arguments
  | invokeValue function arguments => exact .invokeValue function arguments

theorem LiveControlRelated.refl
    (env : Env) (joins : JoinEnv) (control : Control) :
    LiveControlRelated env joins control env joins control := by
  cases control with
  | code code => exact .codeExact env joins code
  | yielded value => exact .yielded value
  | invokeName name arguments => exact .invokeName name arguments
  | invokeValue function arguments => exact .invokeValue function arguments

/-- Machine states for the same program and runtime whose only permitted
difference is in liveness-irrelevant lexical environments. -/
structure LiveMachineRelated (left right : MachineState) : Prop where
  program_eq : left.program = right.program
  runtime_eq : left.runtime = right.runtime
  frames : LiveFramesRelated left.frames right.frames
  control : LiveControlRelated left.env left.joins left.control
    right.env right.joins right.control

theorem LiveMachineRelated.symm
    (related : LiveMachineRelated left right) :
    LiveMachineRelated right left := {
  program_eq := related.program_eq.symm
  runtime_eq := related.runtime_eq.symm
  frames := related.frames.symm
  control := related.control.symm
}

@[refl] theorem LiveMachineRelated.refl (state : MachineState) :
    LiveMachineRelated state state := {
  program_eq := rfl
  runtime_eq := rfl
  frames := .refl state.frames
  control := .refl state.env state.joins state.control
}

/-- Core-step results preserve the live machine relation; external requests
must agree exactly because they are observable. -/
inductive LiveCoreResultRelated : CoreResult → CoreResult → Prop where
  | next (related : LiveMachineRelated left right) :
      LiveCoreResultRelated (.next left) (.next right)
  | external (request : ExternalRequest)
      (related : LiveMachineRelated left right) :
      LiveCoreResultRelated
        (.external request left) (.external request right)
  | done (observation : Observation) :
      LiveCoreResultRelated (.done observation) (.done observation)

theorem LiveCoreResultRelated.symm
    (related : LiveCoreResultRelated left right) :
    LiveCoreResultRelated right left := by
  cases related with
  | next states => exact .next states.symm
  | external request states => exact .external request states.symm
  | done observation => exact .done observation

theorem LiveCoreResultRelated.done_right
    (related : LiveCoreResultRelated (.done observation) right) :
    right = .done observation := by
  cases related
  rfl

theorem observe_eq_of_runtime_eq_live
    (runtimeEq : left.runtime = right.runtime) :
    observe left outcome = observe right outcome := by
  cases left
  cases right
  simp only [MachineState.runtime] at runtimeEq
  subst_vars
  rfl

theorem fail_liveRelated
    (runtimeEq : left.runtime = right.runtime) (fault : RuntimeFault) :
    LiveCoreResultRelated (fail left fault) (fail right fault) := by
  unfold fail
  rw [observe_eq_of_runtime_eq_live runtimeEq]
  exact .done _

/-- Feeding equal external responses to related waiting states restores a
related yielded state. -/
theorem resumeExternal_liveRelated
    (related : LiveMachineRelated left right) :
    LiveMachineRelated
      (resumeExternal request left response)
      (resumeExternal request right response) := by
  refine {
    program_eq := related.program_eq
    runtime_eq := ?_
    frames := related.frames
    control := .yielded response.value
  }
  simp only [resumeExternal, MachineState.withValue]
  rw [related.runtime_eq]

/-- One interpreter step from two live code contexts produces related core
results.  Every environment read is discharged by `CodeCovered`; successful
continuations retain the same global used set. -/
theorem coreStep_codeLive_related
    (leftState rightState : MachineState)
    (programEq : leftState.program = rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (framesRelated : LiveFramesRelated leftState.frames rightState.frames)
    (covered : CodeCovered used code)
    (joinsCovered : JoinEnvCovered used joins)
    (agree : EnvsAgreeOn used leftState.env rightState.env) :
    LiveCoreResultRelated
      (coreStep { leftState with joins, control := .code code })
      (coreStep { rightState with joins, control := .code code }) := by
  let leftMachine := { leftState with joins, control := .code code }
  let rightMachine := { rightState with joins, control := .code code }
  have failure (fault : RuntimeFault) :
      LiveCoreResultRelated (fail leftMachine fault) (fail rightMachine fault) :=
    fail_liveRelated (left := leftMachine) (right := rightMachine) runtimeEq fault
  cases covered with
  | letE valueCovered continuationCovered =>
      rename_i continuation declaration
      have evaluated :
          evalLetValue leftMachine declaration =
            evalLetValue rightMachine declaration :=
        evalLetValue_eq_of_live_env programEq runtimeEq agree valueCovered
      simp only [coreStep]
      rw [evaluated]
      generalize evaluation : evalLetValue rightMachine declaration = result
      cases result with
      | error fault => exact failure fault
      | ok evaluated =>
          obtain ⟨nextRuntime, action⟩ := evaluated
          cases action with
          | value value =>
              exact .next {
                program_eq := programEq
                runtime_eq := rfl
                frames := framesRelated
                control := .codeLive continuationCovered joinsCovered
                  agree.bindBoth
              }
          | invokeName name arguments =>
              have frameRelated : LiveFrameRelated
                  (.bind declaration.fvarId continuation leftState.env joins)
                  (.bind declaration.fvarId continuation rightState.env joins) :=
                .bindLive continuationCovered joinsCovered agree
              have nextRelated : LiveMachineRelated
                  { leftState with
                    runtime := nextRuntime
                    joins := joins
                    frames := .bind declaration.fvarId continuation
                      leftState.env joins :: leftState.frames
                    control := .invokeName name arguments }
                  { rightState with
                    runtime := nextRuntime
                    joins := joins
                    frames := .bind declaration.fvarId continuation
                      rightState.env joins :: rightState.frames
                    control := .invokeName name arguments } := {
                  program_eq := programEq
                  runtime_eq := rfl
                  frames := .cons frameRelated framesRelated
                  control := .invokeName name arguments
                }
              simpa [leftMachine, rightMachine, pushBindFrame] using
                LiveCoreResultRelated.next nextRelated
          | invokeValue function arguments =>
              have frameRelated : LiveFrameRelated
                  (.bind declaration.fvarId continuation leftState.env joins)
                  (.bind declaration.fvarId continuation rightState.env joins) :=
                .bindLive continuationCovered joinsCovered agree
              have nextRelated : LiveMachineRelated
                  { leftState with
                    runtime := nextRuntime
                    joins := joins
                    frames := .bind declaration.fvarId continuation
                      leftState.env joins :: leftState.frames
                    control := .invokeValue function arguments }
                  { rightState with
                    runtime := nextRuntime
                    joins := joins
                    frames := .bind declaration.fvarId continuation
                      rightState.env joins :: rightState.frames
                    control := .invokeValue function arguments } := {
                  program_eq := programEq
                  runtime_eq := rfl
                  frames := .cons frameRelated framesRelated
                  control := .invokeValue function arguments
                }
              simpa [leftMachine, rightMachine, pushBindFrame] using
                LiveCoreResultRelated.next nextRelated
  | join bodyCovered continuationCovered =>
      rename_i declaration continuation
      exact .next {
        program_eq := programEq
        runtime_eq := runtimeEq
        frames := framesRelated
        control := .codeLive continuationCovered
          (joinsCovered.cons bodyCovered) agree
      }
  | cases discrMember alternativesCovered =>
      rename_i caseInfo
      have discrEq := agree _ discrMember
      simp only [coreStep]
      rw [discrEq]
      generalize discrRead : lookupValue rightState.env caseInfo.discr = discrResult
      cases discrResult with
      | error fault =>
          simp only
          exact failure fault
      | ok discr =>
          simp only
          have tagEq : getTag leftState.runtime discr =
              getTag rightState.runtime discr :=
            congrArg (fun runtime => getTag runtime discr) runtimeEq
          rw [tagEq]
          generalize tagRead : getTag rightState.runtime discr = tagResult
          cases tagResult with
          | error fault =>
              simp only
              exact failure fault
          | ok tag =>
              simp only
              generalize selection :
                chooseAlt tag caseInfo.alts.toList = selected
              cases selected with
              | none =>
                  simp only
                  exact failure .invalidCases
              | some branch =>
                  simp only
                  exact .next {
                    program_eq := programEq
                    runtime_eq := runtimeEq
                    frames := framesRelated
                    control := .codeLive
                      (codeCovered_chooseAlt alternativesCovered selection)
                      joinsCovered agree
                  }
  | jump targetMember argumentsCovered =>
      rename_i target arguments
      simp only [coreStep]
      generalize joinRead : findJoinPoint? joins target = joinResult
      cases joinResult with
      | none =>
          simp only
          exact failure (.unknownJoinPoint target)
      | some declaration =>
          simp only
          have bodyCovered := joinsCovered.findJoinPoint joinRead
          rw [evalArgs_eq_of_covered agree argumentsCovered]
          generalize argsRead : evalArgs rightState.env arguments = argsResult
          cases argsResult with
          | error fault =>
              simp only
              exact failure fault
          | ok values =>
              simp only
              unfold bindParamsOver
              by_cases arity :
                  (declaration.params.size == values.size) = true
              · simp only [arity, ↓reduceIte]
                exact .next {
                  program_eq := programEq
                  runtime_eq := runtimeEq
                  frames := framesRelated
                  control := .codeLive bodyCovered joinsCovered
                    (agree.bindPairsBoth
                      (declaration.params.toList.zip values.toList))
                }
              · simp only [arity, ↓reduceIte]
                exact failure
                  (.arityMismatch declaration.params.size values.size)
  | ret resultMember =>
      rename_i result
      have valueEq := agree _ resultMember
      simp only [coreStep]
      rw [valueEq]
      generalize valueRead : lookupValue rightState.env result = valueResult
      cases valueResult with
      | error fault => exact failure fault
      | ok value =>
          exact .next {
            program_eq := programEq
            runtime_eq := runtimeEq
            frames := framesRelated
            control := .yielded value
          }
  | unreachable type =>
      exact failure .unreachable
  | objectSet objectMember fieldCovered continuationCovered =>
      rename_i object field continuation index
      have objectEq := agree _ objectMember
      have fieldEq := evalArg_eq_of_covered agree fieldCovered
      simp only [coreStep]
      rw [objectEq, fieldEq]
      generalize objectRead : lookupValue rightState.env object = objectResult
      generalize fieldRead : evalArg rightState.env field = fieldResult
      cases objectResult with
      | error fault => exact failure fault
      | ok objectValue =>
          cases fieldResult with
          | error fault => exact failure fault
          | ok fieldValue =>
              simp only
              have effectEq :
                  setObjectField leftState.runtime objectValue index fieldValue =
                    setObjectField rightState.runtime objectValue index fieldValue :=
                congrArg
                  (fun runtime => setObjectField runtime objectValue index fieldValue)
                  runtimeEq
              rw [effectEq]
              generalize effectRead :
                setObjectField rightState.runtime objectValue index fieldValue =
                  effectResult
              cases effectResult with
              | error fault => exact failure fault
              | ok nextRuntime =>
                  exact .next {
                    program_eq := programEq
                    runtime_eq := rfl
                    frames := framesRelated
                    control := .codeLive continuationCovered joinsCovered agree
                  }
  | usizeSet objectMember fieldMember continuationCovered =>
      rename_i object field continuation index
      have objectEq := agree _ objectMember
      have fieldEq := agree _ fieldMember
      simp only [coreStep]
      rw [objectEq, fieldEq]
      generalize objectRead : lookupValue rightState.env object = objectResult
      generalize fieldRead : lookupValue rightState.env field = fieldResult
      cases objectResult with
      | error fault => exact failure fault
      | ok objectValue =>
          cases fieldResult with
          | error fault => exact failure fault
          | ok fieldValue =>
              simp only
              have effectEq :
                  setUSizeField leftState.runtime objectValue index fieldValue =
                    setUSizeField rightState.runtime objectValue index fieldValue :=
                congrArg
                  (fun runtime => setUSizeField runtime objectValue index fieldValue)
                  runtimeEq
              rw [effectEq]
              generalize effectRead :
                setUSizeField rightState.runtime objectValue index fieldValue =
                  effectResult
              cases effectResult with
              | error fault => exact failure fault
              | ok nextRuntime =>
                  exact .next {
                    program_eq := programEq
                    runtime_eq := rfl
                    frames := framesRelated
                    control := .codeLive continuationCovered joinsCovered agree
                  }
  | scalarSet objectMember fieldMember continuationCovered =>
      rename_i object field continuation width offset type
      have objectEq := agree _ objectMember
      have fieldEq := agree _ fieldMember
      simp only [coreStep]
      rw [objectEq, fieldEq]
      generalize objectRead : lookupValue rightState.env object = objectResult
      generalize fieldRead : lookupValue rightState.env field = fieldResult
      cases objectResult with
      | error fault => exact failure fault
      | ok objectValue =>
          cases fieldResult with
          | error fault => exact failure fault
          | ok fieldValue =>
              simp only
              have effectEq :
                  setScalarField leftState.runtime objectValue width offset fieldValue =
                    setScalarField rightState.runtime objectValue width offset fieldValue :=
                congrArg
                  (fun runtime =>
                    setScalarField runtime objectValue width offset fieldValue)
                  runtimeEq
              rw [effectEq]
              generalize effectRead :
                setScalarField rightState.runtime objectValue width offset fieldValue =
                  effectResult
              cases effectResult with
              | error fault => exact failure fault
              | ok nextRuntime =>
                  exact .next {
                    program_eq := programEq
                    runtime_eq := rfl
                    frames := framesRelated
                    control := .codeLive continuationCovered joinsCovered agree
                  }
  | tagSet objectMember continuationCovered =>
      rename_i object continuation tag
      have objectEq := agree _ objectMember
      simp only [coreStep]
      rw [objectEq]
      generalize objectRead : lookupValue rightState.env object = objectResult
      cases objectResult with
      | error fault => exact failure fault
      | ok objectValue =>
          simp only
          have effectEq : setTag leftState.runtime objectValue tag =
              setTag rightState.runtime objectValue tag :=
            congrArg (fun runtime => setTag runtime objectValue tag) runtimeEq
          rw [effectEq]
          generalize effectRead :
            setTag rightState.runtime objectValue tag = effectResult
          cases effectResult with
          | error fault => exact failure fault
          | ok nextRuntime =>
              exact .next {
                program_eq := programEq
                runtime_eq := rfl
                frames := framesRelated
                control := .codeLive continuationCovered joinsCovered agree
              }
  | increment objectMember continuationCovered =>
      rename_i object continuation amount check persistent
      cases persistent with
      | true =>
          exact .next {
            program_eq := programEq
            runtime_eq := runtimeEq
            frames := framesRelated
            control := .codeLive continuationCovered joinsCovered agree
          }
      | false =>
          have objectEq := agree _ objectMember
          simp only [coreStep, Bool.false_eq_true, ↓reduceIte]
          rw [objectEq]
          generalize objectRead : lookupValue rightState.env object = objectResult
          cases objectResult with
          | error fault => exact failure fault
          | ok objectValue =>
              simp only
              have effectEq :
                  incValue leftState.runtime objectValue amount check =
                    incValue rightState.runtime objectValue amount check :=
                congrArg
                  (fun runtime => incValue runtime objectValue amount check)
                  runtimeEq
              rw [effectEq]
              generalize effectRead :
                incValue rightState.runtime objectValue amount check = effectResult
              cases effectResult with
              | error fault => exact failure fault
              | ok nextRuntime =>
                  exact .next {
                    program_eq := programEq
                    runtime_eq := rfl
                    frames := framesRelated
                    control := .codeLive continuationCovered joinsCovered agree
                  }
  | decrement objectMember continuationCovered =>
      rename_i object continuation amount check persistent objects
      cases persistent with
      | true =>
          exact .next {
            program_eq := programEq
            runtime_eq := runtimeEq
            frames := framesRelated
            control := .codeLive continuationCovered joinsCovered agree
          }
      | false =>
          have objectEq := agree _ objectMember
          simp only [coreStep, Bool.false_eq_true, ↓reduceIte]
          rw [objectEq]
          generalize objectRead : lookupValue rightState.env object = objectResult
          cases objectResult with
          | error fault => exact failure fault
          | ok objectValue =>
              simp only
              have effectEq :
                  decValue leftState.runtime objectValue amount check =
                    decValue rightState.runtime objectValue amount check :=
                congrArg
                  (fun runtime => decValue runtime objectValue amount check)
                  runtimeEq
              rw [effectEq]
              generalize effectRead :
                decValue rightState.runtime objectValue amount check = effectResult
              cases effectResult with
              | error fault => exact failure fault
              | ok nextRuntime =>
                  exact .next {
                    program_eq := programEq
                    runtime_eq := rfl
                    frames := framesRelated
                    control := .codeLive continuationCovered joinsCovered agree
                  }
  | delete objectMember continuationCovered =>
      rename_i object continuation
      have objectEq := agree _ objectMember
      simp only [coreStep]
      rw [objectEq]
      generalize objectRead : lookupValue rightState.env object = objectResult
      cases objectResult with
      | error fault => exact failure fault
      | ok objectValue =>
          simp only
          have effectEq : deleteValue leftState.runtime objectValue =
              deleteValue rightState.runtime objectValue :=
            congrArg (fun runtime => deleteValue runtime objectValue) runtimeEq
          rw [effectEq]
          generalize effectRead :
            deleteValue rightState.runtime objectValue = effectResult
          cases effectResult with
          | error fault => exact failure fault
          | ok nextRuntime =>
              exact .next {
                program_eq := programEq
                runtime_eq := rfl
                frames := framesRelated
                control := .codeLive continuationCovered joinsCovered agree
              }

/-- Yielding either terminates equally or restores the exact/live context
stored by the top related frame. -/
theorem coreStep_yielded_liveRelated
    (leftState rightState : MachineState)
    (programEq : leftState.program = rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (framesRelated : LiveFramesRelated leftFrames rightFrames) :
    LiveCoreResultRelated
      (coreStep { leftState with
        frames := leftFrames, control := .yielded value })
      (coreStep { rightState with
        frames := rightFrames, control := .yielded value }) := by
  cases framesRelated with
  | nil =>
      simp only [coreStep]
      rw [observe_eq_of_runtime_eq_live
        (left := { leftState with frames := [], control := .yielded value })
        (right := { rightState with frames := [], control := .yielded value })
        runtimeEq]
      exact .done _
  | cons frameRelated restRelated =>
      cases frameRelated with
      | bindExact fvarId continuation env joins =>
          exact .next {
            program_eq := programEq
            runtime_eq := runtimeEq
            frames := restRelated
            control := .codeExact (bind env fvarId value) joins continuation
          }
      | bindLive continuationCovered joinsCovered agree =>
          exact .next {
            program_eq := programEq
            runtime_eq := runtimeEq
            frames := restRelated
            control := .codeLive continuationCovered joinsCovered
              agree.bindBoth
          }
      | apply arguments =>
          exact .next {
            program_eq := programEq
            runtime_eq := runtimeEq
            frames := restRelated
            control := .invokeValue value arguments
          }
      | cache name =>
          exact .next {
            program_eq := programEq
            runtime_eq := congrArg
              (fun runtime => runtime.setGlobal name value) runtimeEq
            frames := restRelated
            control := .yielded value
          }

/-- The direct bridge from backwards liveness to the execution relation:
adding an absent binder on one side preserves every lookup available to the
active code and its installed joins. -/
theorem liveMachineRelated_bindLeft_of_absent
    (state : MachineState) (binder : FVarId) (value : Value)
    (code : LCNF.Code .impure)
    (covered : CodeCovered used code)
    (joinsCovered : JoinEnvCovered used state.joins)
    (absent : used.contains binder = false) :
    LiveMachineRelated
      { state with
        env := bind state.env binder value
        control := .code code }
      { state with control := .code code } := {
  program_eq := rfl
  runtime_eq := rfl
  frames := .refl state.frames
  control := .codeLive covered joinsCovered
    ((EnvsAgreeOn.refl used state.env).bindLeft_of_absent absent)
}

end Fir.LeanIR.Passes.ElimDead
