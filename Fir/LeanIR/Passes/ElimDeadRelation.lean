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
