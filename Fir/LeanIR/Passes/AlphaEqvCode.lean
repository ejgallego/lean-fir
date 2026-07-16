import Fir.LeanIR.Passes.SimpCase

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.SimpCase

/-- The terminal fragment of the proof-facing impure-code relation. -/
inductive TerminalCodeRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) :
    LCNF.Code .impure → LCNF.Code .impure → Prop where
  | ret (related : ScopedFVarRelated rho leftScope rightScope leftId rightId) :
      TerminalCodeRelated rho leftScope rightScope (.return leftId) (.return rightId)
  | unreachable :
      TerminalCodeRelated rho leftScope rightScope (.unreach leftType) (.unreach rightType)

/--
The proof-facing code relation, initially covering terminal code and value
bindings. The recursive `let` case records the same scope extension performed
by Lean's alpha-equivalence checker.
-/
inductive CodeRelated :
    FVarIdMap FVarId → List FVarId → List FVarId →
      LCNF.Code .impure → LCNF.Code .impure → Prop where
  | terminal
      (related : TerminalCodeRelated rho leftScope rightScope left right) :
      CodeRelated rho leftScope rightScope left right
  | letE
      (declaration : LetDeclValueRelated rho leftScope rightScope leftDecl rightDecl)
      (leftFresh : FreshForScope leftDecl.fvarId leftScope)
      (rightFresh : FreshForScope rightDecl.fvarId rightScope)
      (continuation :
        CodeRelated (rho.insert rightDecl.fvarId leftDecl.fvarId)
          (leftDecl.fvarId :: leftScope) (rightDecl.fvarId :: rightScope)
          leftContinuation rightContinuation) :
      CodeRelated rho leftScope rightScope
        (.let leftDecl leftContinuation) (.let rightDecl rightContinuation)

/--
Saved continuations are related when they remember agreeing environments and
resume with related code under the binders they introduce. Apply and cache
frames carry no alpha-sensitive syntax yet and therefore agree literally.
-/
inductive FrameRelated : Frame → Frame → Prop where
  | bind
      (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
      (renamingScoped : RenamingScoped rho leftScope rightScope)
      (leftFresh : FreshForScope leftId leftScope)
      (rightFresh : FreshForScope rightId rightScope)
      (continuation :
        CodeRelated (rho.insert rightId leftId)
          (leftId :: leftScope) (rightId :: rightScope)
          leftContinuation rightContinuation) :
      FrameRelated
        (.bind leftId leftContinuation leftEnv joins)
        (.bind rightId rightContinuation rightEnv joins)
  | apply (args : Array Value) :
      FrameRelated (.apply args) (.apply args)
  | cache (name : Name) :
      FrameRelated (.cache name) (.cache name)

abbrev FramesRelated (left right : List Frame) : Prop :=
  ListRel FrameRelated left right

/-- Machine controls that carry equal runtime data or related residual code. -/
inductive ControlRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) : Control → Control → Prop where
  | code (related : CodeRelated rho leftScope rightScope left right) :
      ControlRelated rho leftScope rightScope (.code left) (.code right)
  | yielded (value : Value) :
      ControlRelated rho leftScope rightScope (.yielded value) (.yielded value)
  | invokeName (name : Name) (args : Array Value) :
      ControlRelated rho leftScope rightScope
        (.invokeName name args) (.invokeName name args)
  | invokeValue (function : Value) (args : Array Value) :
      ControlRelated rho leftScope rightScope
        (.invokeValue function args) (.invokeValue function args)

/--
The state invariant used by the declarative simulation. Program, runtime, and
join-point state are currently shared literally; environments, frames, and
code are related structurally.
-/
structure MachineStateRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) (left right : MachineState) : Prop where
  program_eq : left.program = right.program
  runtime_eq : left.runtime = right.runtime
  joins_eq : left.joins = right.joins
  frames : FramesRelated left.frames right.frames
  envs : EnvsAgree rho leftScope rightScope left.env right.env
  renaming_scoped : RenamingScoped rho leftScope rightScope
  control : ControlRelated rho leftScope rightScope left.control right.control

/-- Core-step results related by the machine invariant. -/
inductive CoreResultRelated : CoreResult → CoreResult → Prop where
  | next
      (related : MachineStateRelated rho leftScope rightScope left right) :
      CoreResultRelated (.next left) (.next right)
  | external (request : ExternalRequest)
      (related : MachineStateRelated rho leftScope rightScope left right) :
      CoreResultRelated (.external request left) (.external request right)
  | done (observation : Observation) :
      CoreResultRelated (.done observation) (.done observation)

/-- `evalLetValue` observes only a state's program, runtime, and environment. -/
theorem evalLetValue_eq_of_state_fields
    (programEq : left.program = right.program)
    (runtimeEq : left.runtime = right.runtime)
    (envEq : left.env = right.env) :
    evalLetValue left declaration = evalLetValue right declaration := by
  cases left
  cases right
  simp_all only
  rcases declaration with ⟨fvarId, binderName, type, value⟩
  cases value <;> rfl

/-- Evaluate related declarations in two states satisfying the machine fields. -/
theorem evalLetValue_eq_of_related_states
    (programEq : left.program = right.program)
    (runtimeEq : left.runtime = right.runtime)
    (agree : EnvsAgree rho leftScope rightScope left.env right.env)
    (related : LetDeclValueRelated rho leftScope rightScope leftDecl rightDecl) :
    evalLetValue left leftDecl = evalLetValue right rightDecl := by
  calc
    evalLetValue left leftDecl =
        evalLetValue ({ left with env := right.env }) rightDecl := by
      simpa using evalLetValue_eq_of_related left agree related
    _ = evalLetValue right rightDecl := by
      exact evalLetValue_eq_of_state_fields
        (left := { left with env := right.env }) (right := right)
        programEq runtimeEq rfl

theorem observe_eq_of_runtime_eq
    (runtimeEq : left.runtime = right.runtime) (outcome : Outcome) :
    observe left outcome = observe right outcome := by
  cases left
  cases right
  simp_all [observe]

/--
One interpreter step preserves the declarative machine relation for the
terminal and `let` code fragment. In particular, the three successful let
actions either extend the current environments immediately or save the same
extension invariant in a pair of bind frames.
-/
theorem coreStep_code_related
    (leftState rightState : MachineState)
    (programEq : leftState.program = rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (joinsEq : leftState.joins = rightState.joins)
    (framesRelated : FramesRelated leftState.frames rightState.frames)
    (agree : EnvsAgree rho leftScope rightScope leftState.env rightState.env)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (related : CodeRelated rho leftScope rightScope leftCode rightCode) :
    CoreResultRelated
      (coreStep { leftState with control := .code leftCode })
      (coreStep { rightState with control := .code rightCode }) := by
  cases related with
  | terminal terminal =>
      cases terminal with
      | ret fvarRelated =>
          obtain ⟨value, leftFound, rightFound⟩ :=
            agree _ fvarRelated.1 _ fvarRelated.2.1 fvarRelated.2.2
          have nextRelated :
              MachineStateRelated rho leftScope rightScope
                { leftState with control := .yielded value }
                { rightState with control := .yielded value } := {
            program_eq := programEq
            runtime_eq := runtimeEq
            joins_eq := joinsEq
            frames := framesRelated
            envs := agree
            renaming_scoped := renamingScoped
            control := .yielded value
          }
          simpa [coreStep, lookupValue, leftFound, rightFound] using
            CoreResultRelated.next nextRelated
      | unreachable =>
          have observed := observe_eq_of_runtime_eq
            (left := leftState) (right := rightState) runtimeEq
            (.fault .unreachable)
          simp only [coreStep, fail]
          change CoreResultRelated
            (.done (observe leftState (.fault .unreachable)))
            (.done (observe rightState (.fault .unreachable)))
          rw [observed]
          exact .done _
  | letE declaration leftFresh rightFresh continuation =>
      rename_i leftDecl rightDecl leftContinuation rightContinuation
      have evaluated :
          evalLetValue
              { leftState with
                control := .code (.let leftDecl leftContinuation) }
              leftDecl =
            evalLetValue
              { rightState with
                control := .code (.let rightDecl rightContinuation) }
              rightDecl :=
        evalLetValue_eq_of_related_states programEq runtimeEq agree declaration
      simp only [coreStep]
      rw [evaluated]
      generalize rightEvaluation :
        evalLetValue
            { rightState with
              control := .code (.let rightDecl rightContinuation) }
            rightDecl = result
      cases result with
      | error fault =>
          have observed := observe_eq_of_runtime_eq
            (left := leftState) (right := rightState) runtimeEq (.fault fault)
          simp only [fail]
          change CoreResultRelated
            (.done (observe leftState (.fault fault)))
            (.done (observe rightState (.fault fault)))
          rw [observed]
          exact .done _
      | ok evaluated =>
          rcases evaluated with ⟨nextRuntime, action⟩
          cases action with
          | value value =>
              have nextRelated :
                  MachineStateRelated
                    (rho.insert rightDecl.fvarId leftDecl.fvarId)
                    (leftDecl.fvarId :: leftScope) (rightDecl.fvarId :: rightScope)
                    { leftState with
                      runtime := nextRuntime
                      env := bind leftState.env leftDecl.fvarId value
                      control := .code leftContinuation }
                    { rightState with
                      runtime := nextRuntime
                      env := bind rightState.env rightDecl.fvarId value
                      control := .code rightContinuation } := {
                program_eq := programEq
                runtime_eq := rfl
                joins_eq := joinsEq
                frames := framesRelated
                envs := envsAgree_bind agree renamingScoped leftFresh rightFresh
                renaming_scoped := renamingScoped_insert renamingScoped rightFresh
                control := .code continuation
              }
              exact CoreResultRelated.next nextRelated
          | invokeName name args =>
              have bindFrameRelated :
                  FrameRelated
                    (.bind leftDecl.fvarId leftContinuation
                      leftState.env leftState.joins)
                    (.bind rightDecl.fvarId rightContinuation
                      rightState.env rightState.joins) := by
                rw [joinsEq]
                exact .bind agree renamingScoped leftFresh rightFresh continuation
              have nextRelated :
                  MachineStateRelated rho leftScope rightScope
                    { leftState with
                      runtime := nextRuntime
                      frames := .bind leftDecl.fvarId leftContinuation
                        leftState.env leftState.joins :: leftState.frames
                      control := .invokeName name args }
                    { rightState with
                      runtime := nextRuntime
                      frames := .bind rightDecl.fvarId rightContinuation
                        rightState.env rightState.joins :: rightState.frames
                      control := .invokeName name args } := {
                program_eq := programEq
                runtime_eq := rfl
                joins_eq := joinsEq
                frames := .cons bindFrameRelated framesRelated
                envs := agree
                renaming_scoped := renamingScoped
                control := .invokeName name args
              }
              simpa [pushBindFrame] using CoreResultRelated.next nextRelated
          | invokeValue function args =>
              have bindFrameRelated :
                  FrameRelated
                    (.bind leftDecl.fvarId leftContinuation
                      leftState.env leftState.joins)
                    (.bind rightDecl.fvarId rightContinuation
                      rightState.env rightState.joins) := by
                rw [joinsEq]
                exact .bind agree renamingScoped leftFresh rightFresh continuation
              have nextRelated :
                  MachineStateRelated rho leftScope rightScope
                    { leftState with
                      runtime := nextRuntime
                      frames := .bind leftDecl.fvarId leftContinuation
                        leftState.env leftState.joins :: leftState.frames
                      control := .invokeValue function args }
                    { rightState with
                      runtime := nextRuntime
                      frames := .bind rightDecl.fvarId rightContinuation
                        rightState.env rightState.joins :: rightState.frames
                      control := .invokeValue function args } := {
                program_eq := programEq
                runtime_eq := rfl
                joins_eq := joinsEq
                frames := .cons bindFrameRelated framesRelated
                envs := agree
                renaming_scoped := renamingScoped
                control := .invokeValue function args
              }
              simpa [pushBindFrame] using CoreResultRelated.next nextRelated

/-- A related pair of saved bind continuations resumes under the new binders. -/
theorem coreStep_yielded_bind_related
    (leftState rightState : MachineState)
    (programEq : leftState.program = rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (restFrames : FramesRelated leftFrames rightFrames)
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (leftFresh : FreshForScope leftId leftScope)
    (rightFresh : FreshForScope rightId rightScope)
    (continuation :
      CodeRelated (rho.insert rightId leftId)
        (leftId :: leftScope) (rightId :: rightScope)
        leftContinuation rightContinuation) :
    CoreResultRelated
      (coreStep
        { leftState with
          control := .yielded value
          frames := .bind leftId leftContinuation leftEnv joins :: leftFrames })
      (coreStep
        { rightState with
          control := .yielded value
          frames := .bind rightId rightContinuation rightEnv joins :: rightFrames }) := by
  have nextRelated :
      MachineStateRelated (rho.insert rightId leftId)
        (leftId :: leftScope) (rightId :: rightScope)
        { leftState with
          control := .code leftContinuation
          env := bind leftEnv leftId value
          joins := joins
          frames := leftFrames }
        { rightState with
          control := .code rightContinuation
          env := bind rightEnv rightId value
          joins := joins
          frames := rightFrames } := {
    program_eq := programEq
    runtime_eq := runtimeEq
    joins_eq := rfl
    frames := restFrames
    envs := envsAgree_bind agree renamingScoped leftFresh rightFresh
    renaming_scoped := renamingScoped_insert renamingScoped rightFresh
    control := .code continuation
  }
  simpa [coreStep] using CoreResultRelated.next nextRelated

/-- The matching immediate outcomes of two related terminal instructions. -/
inductive TerminalResultRelated (leftEnv rightEnv : Env) (state : MachineState) :
    CoreResult → CoreResult → Prop where
  | yielded (value : Value) :
      TerminalResultRelated leftEnv rightEnv state
        (.next { state with env := leftEnv, control := .yielded value })
        (.next { state with env := rightEnv, control := .yielded value })
  | done (observation : Observation) :
      TerminalResultRelated leftEnv rightEnv state (.done observation) (.done observation)

theorem coreStep_terminal_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : TerminalCodeRelated rho leftScope rightScope left right) :
    TerminalResultRelated leftEnv rightEnv state
      (coreStep { state with env := leftEnv, control := .code left })
      (coreStep { state with env := rightEnv, control := .code right }) := by
  cases related with
  | ret related =>
      obtain ⟨value, leftFound, rightFound⟩ :=
        agree _ related.1 _ related.2.1 related.2.2
      simpa [coreStep, lookupValue, leftFound, rightFound] using
        TerminalResultRelated.yielded (state := state)
          (leftEnv := leftEnv) (rightEnv := rightEnv) value
  | unreachable =>
      simpa [coreStep, fail, observe] using
        TerminalResultRelated.done (state := state)
          (leftEnv := leftEnv) (rightEnv := rightEnv)
          (observe state (.fault .unreachable))

/-- A machine state whose core step is already done has exactly one observation. -/
theorem evaluatesState_done_iff
    (done : coreStep initial = .done result) :
    EvaluatesState externals initial observation ↔ result = observation := by
  constructor
  · rintro ⟨count, final, execution, finalDone⟩
    cases execution with
    | refl _ => simpa [done] using finalDone
    | step head _ =>
        cases head with
        | internal transition => simp [done] at transition
        | external transition _ => simp [done] at transition
  · rintro rfl
    exact ⟨0, initial, .refl initial, done⟩

theorem unreach_codeEquivalentAt (leftType rightType : Expr) :
    CodeEquivalentAt externals state (.unreach leftType) (.unreach rightType) := by
  intro observation
  have leftDone :
      coreStep { state with control := .code (.unreach leftType) } =
        .done (observe state (.fault .unreachable)) := by
    simp [coreStep, fail, observe]
  have rightDone :
      coreStep { state with control := .code (.unreach rightType) } =
        .done (observe state (.fault .unreachable)) := by
    simp [coreStep, fail, observe]
  rw [evaluatesState_done_iff leftDone, evaluatesState_done_iff rightDone]

theorem terminalCodeRelated_empty_sound
    (related : TerminalCodeRelated ({} : FVarIdMap FVarId) scope scope left right) :
    CodeEquivalentAt externals state left right := by
  cases related with
  | ret related =>
      rename_i leftId rightId
      have ids : leftId = rightId := by
        have fvarRelated := related.2.2
        change (leftId == rightId) = true at fvarRelated
        cases leftId with
        | mk leftName =>
            cases rightId with
            | mk rightName =>
                congr
                exact Name.beq_iff_eq.mp fvarRelated
      subst rightId
      exact codeEquivalentAt_refl
  | unreachable => exact unreach_codeEquivalentAt _ _

/--
Reduce executable terminal alpha-soundness to the missing checker-to-relation
bridge. Lean 4.32 exposes `LCNF.AlphaEqv.eqv` as an opaque `partial def`, so
that bridge cannot currently be proved by unfolding the checker.
-/
theorem alphaEqvSoundAt_of_terminal_bridge
    (bridge : left.alphaEqv right = true →
      TerminalCodeRelated ({} : FVarIdMap FVarId) scope scope left right) :
    AlphaEqvSoundAt externals state left right := by
  intro accepted
  exact terminalCodeRelated_empty_sound (bridge accepted)

end Fir.LeanIR.Passes.AlphaEqv
