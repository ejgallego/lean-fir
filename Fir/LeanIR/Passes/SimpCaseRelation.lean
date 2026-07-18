import Fir.LeanIR.Passes.Structural

namespace Fir.LeanIR.Passes.SimpCaseRelation

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.SimpCase
open Fir.LeanIR.Passes.NonLockstep
open Fir.LeanIR.Passes.NonLockstep.Structural

/-!
`CodeRel` is a proof-facing graph for recursive `simpCase` traversals.  It is
deliberately independent of Lean's private `Code.simpCase` implementation:
compiler conformance is a separate boundary.

The graph distinguishes head-aligned code from an eliminated case prefix.
Head-aligned nodes take the same kind of interpreter step; an eliminated case
may take one source step while the target stutters.  Recursive occurrences in
continuations, join bodies, and selected case branches use `CodeRel` again.
-/

mutual

  /-- Recursive relation between source code and its `simpCase` target. -/
  inductive CodeRel
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      LCNF.Code .impure → LCNF.Code .impure → Prop where
    | aligned (related : HeadRel validCase left right) :
        CodeRel validCase left right
    | eliminate
        (cases : LCNF.Cases .impure)
        (target : LCNF.Code .impure)
        (selected : ∀ tag, validCase cases tag →
          ElimSelectionRel validCase target
            (chooseAlt tag cases.alts.toList)) :
        CodeRel validCase (.cases cases) target

  /-- Code whose outer interpreter action is aligned on both sides. -/
  inductive HeadRel
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      LCNF.Code .impure → LCNF.Code .impure → Prop where
    | let (decl : LCNF.LetDecl .impure)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.let decl left) (.let decl right)
    | jp (fvarId : FVarId) (binderName : Name)
        (params : Array (LCNF.Param .impure)) (type : Expr)
        (body : CodeRel validCase leftBody rightBody)
        (continuation : CodeRel validCase leftContinuation rightContinuation) :
        HeadRel validCase
          (.jp (.mk fvarId binderName params type leftBody) leftContinuation)
          (.jp (.mk fvarId binderName params type rightBody) rightContinuation)
    | jmp (fvarId : FVarId) (args : Array (LCNF.Arg .impure)) :
        HeadRel validCase (.jmp fvarId args) (.jmp fvarId args)
    | cases (typeName : Name) (resultType : Expr) (discr : FVarId)
        (leftAlts rightAlts : Array (LCNF.Alt .impure))
        (selected : ∀ tag,
          validCase (.mk typeName resultType discr leftAlts) tag →
          SelectionRel validCase (chooseAlt tag leftAlts.toList)
            (chooseAlt tag rightAlts.toList)) :
        HeadRel validCase
          (.cases (.mk typeName resultType discr leftAlts))
          (.cases (.mk typeName resultType discr rightAlts))
    | return (fvarId : FVarId) :
        HeadRel validCase (.return fvarId) (.return fvarId)
    | unreach (type : Expr) :
        HeadRel validCase (.unreach type) (.unreach type)
    | oset (fvarId : FVarId) (index : Nat) (value : LCNF.Arg .impure)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.oset fvarId index value left)
          (.oset fvarId index value right)
    | uset (fvarId : FVarId) (index : Nat) (value : FVarId)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.uset fvarId index value left)
          (.uset fvarId index value right)
    | sset (fvarId : FVarId) (width offset : Nat) (value : FVarId)
        (type : Expr) (continuation : CodeRel validCase left right) :
        HeadRel validCase (.sset fvarId width offset value type left)
          (.sset fvarId width offset value type right)
    | setTag (fvarId : FVarId) (tag : Nat)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.setTag fvarId tag left) (.setTag fvarId tag right)
    | inc (fvarId : FVarId) (amount : Nat) (check persistent : Bool)
        (continuation : CodeRel validCase left right) :
        HeadRel validCase (.inc fvarId amount check persistent left)
          (.inc fvarId amount check persistent right)
    | dec (fvarId : FVarId) (amount : Nat) (check persistent : Bool)
        (objects : Option Nat) (continuation : CodeRel validCase left right) :
        HeadRel validCase (.dec fvarId amount check persistent objects left)
          (.dec fvarId amount check persistent objects right)
    | del (fvarId : FVarId) (continuation : CodeRel validCase left right) :
        HeadRel validCase (.del fvarId left) (.del fvarId right)

  /-- Selected alternatives are either both absent or recursively related. -/
  inductive SelectionRel
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      Option (LCNF.Code .impure) → Option (LCNF.Code .impure) → Prop where
    | none : SelectionRel validCase none none
    | some (related : CodeRel validCase left right) :
        SelectionRel validCase (some left) (some right)

  /-- An eliminated case must select a recursively related source branch for
  every tag permitted by its phase invariant. -/
  inductive ElimSelectionRel
      (validCase : LCNF.Cases .impure → Nat → Prop) :
      LCNF.Code .impure → Option (LCNF.Code .impure) → Prop where
    | some (related : CodeRel validCase source target) :
        ElimSelectionRel validCase target (some source)

end

/-- Lift an aligned head into the full recursive relation. -/
theorem HeadRel.codeRel (related : HeadRel validCase left right) :
    CodeRel validCase left right :=
  .aligned related

/-- Runtime obligation for the currently active related code.  Every source
case must have a readable discriminator and permitted tag.  This deliberately
strong phase invariant also covers the ambiguous syntax where an eliminated
case is replaced by another case expression. -/
def CodeReadyAt
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (state : MachineState) (left _right : LCNF.Code .impure) : Prop :=
  match left with
  | .cases cases =>
      ∃ value tag,
        lookupValue state.env cases.discr = .ok value ∧
        getTag state.runtime value = .ok tag ∧
        validCase cases tag
  | _ => True

theorem CodeReadyAt.valid
    (ready : CodeReadyAt validCase state (.cases cases) target)
    (lookupEq : lookupValue state.env cases.discr = .ok value)
    (tagEq : getTag state.runtime value = .ok tag) :
    validCase cases tag := by
  rcases ready with
    ⟨readyValue, readyTag, readyLookup, readyTagRead, allowed⟩
  rw [readyLookup] at lookupEq
  cases lookupEq
  rw [readyTagRead] at tagEq
  cases tagEq
  exact allowed

/-- Readiness for the active control pair in a structural machine relation. -/
def ControlReadyAt
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (state : MachineState) (left right : Control) : Prop :=
  match left, right with
  | .code left, .code right => CodeReadyAt validCase state left right
  | _, _ => True

/-- A semantic invariant used with `MachineRelatedWith` must establish active
case readiness and remain true along matched finite paths.  The path-stability
field is a typing-preservation obligation, not a simulation assumption: the
structural proof still has to construct both matching paths. -/
structure InvariantLaws (externals : ExternalSpec)
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (invariant : MachineState → MachineState → Prop) : Prop where
  ready : ∀ {left right}
    (_ : MachineRelated (CodeRel validCase) left right),
    invariant left right →
    ControlReadyAt validCase left left.control right.control
  stable : ∀ {leftBefore rightBefore leftAfter rightAfter},
    invariant leftBefore rightBefore →
    MachineRelated (CodeRel validCase) leftBefore rightBefore →
    Reaches externals leftBefore leftAfter →
    Reaches externals rightBefore rightAfter →
    MachineRelated (CodeRel validCase) leftAfter rightAfter →
    invariant leftAfter rightAfter

/-- The direct readiness predicate can be used as one component of a stronger
typed-machine invariant.  Its preservation is intentionally not automatic:
the phase proof must show that future case discriminants remain valid. -/
def AllCasesReady
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (left right : MachineState) : Prop :=
  ControlReadyAt validCase left left.control right.control

/-- Core-step results preserve the structural recursive relation. -/
inductive CoreResultRelated
    (validCase : LCNF.Cases .impure → Nat → Prop) :
    CoreResult → CoreResult → Prop where
  | next (related : MachineRelated (CodeRel validCase) left right) :
      CoreResultRelated validCase (.next left) (.next right)
  | external (request : ExternalRequest)
      (related : MachineRelated (CodeRel validCase) left right) :
      CoreResultRelated validCase (.external request left)
        (.external request right)
  | done (observation : Observation) :
      CoreResultRelated validCase (.done observation) (.done observation)

theorem CoreResultRelated.done_right
    (related : CoreResultRelated validCase (.done observation) right) :
    right = .done observation := by
  cases related
  rfl

theorem observe_eq_of_runtime_eq
    (runtimeEq : left.runtime = right.runtime) (outcome : Outcome) :
    observe left outcome = observe right outcome := by
  simp only [observe]
  rw [runtimeEq]

theorem fail_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fault : RuntimeFault) :
    CoreResultRelated validCase (fail left fault) (fail right fault) := by
  unfold fail
  rw [observe_eq_of_runtime_eq related.runtime_eq (.fault fault)]
  exact .done _

/-- A shared runtime operation either faults on both sides or resumes related
continuations with its common updated runtime. -/
theorem runtimeResult_related
    (related : MachineRelated (CodeRel validCase) left right)
    (continuation : CodeRel validCase leftContinuation rightContinuation)
    (result : Except RuntimeFault RuntimeState) :
    CoreResultRelated validCase
      (match result with
      | .ok runtime => .next
          { left with runtime, control := .code leftContinuation }
      | .error fault => fail left fault)
      (match result with
      | .ok runtime => .next
          { right with runtime, control := .code rightContinuation }
      | .error fault => fail right fault) := by
  cases result with
  | error fault => exact fail_related related fault
  | ok runtime =>
      exact .next {
        programs := related.programs
        runtime_eq := rfl
        env_eq := related.env_eq
        joins := related.joins
        frames := related.frames
        control := .code continuation
      }

theorem machineRelated_withControl
    (related : MachineRelated codeRel left right)
    (control : ControlRelated codeRel leftControl rightControl) :
    MachineRelated codeRel
      { left with control := leftControl }
      { right with control := rightControl } := {
  programs := related.programs
  runtime_eq := related.runtime_eq
  env_eq := related.env_eq
  joins := related.joins
  frames := related.frames
  control
}

/-- Applying the interpreter's extra-argument and nullary-cache frame policy
to structurally related stacks preserves the relation. -/
theorem framesRelated_prepare_call
    (name : Name) (params : Array (LCNF.Param .impure))
    (args extraArgs : Array Value)
    (related : FramesRelated codeRel leftFrames rightFrames) :
    FramesRelated codeRel
      (let frames := if extraArgs.isEmpty then leftFrames
        else .apply extraArgs :: leftFrames
       if params.isEmpty && args.isEmpty then .cache name :: frames else frames)
      (let frames := if extraArgs.isEmpty then rightFrames
        else .apply extraArgs :: rightFrames
       if params.isEmpty && args.isEmpty then .cache name :: frames else frames) := by
  unfold FramesRelated at related ⊢
  by_cases extraEmpty : extraArgs.isEmpty
  · by_cases cache : params.isEmpty && args.isEmpty
    · simpa [extraEmpty, cache] using
        ListRel.cons (FrameRelated.cache name) related
    · simpa [extraEmpty, cache] using related
  · by_cases cache : params.isEmpty && args.isEmpty
    · simpa [extraEmpty, cache] using
        ListRel.cons (FrameRelated.cache name)
          (ListRel.cons (FrameRelated.apply extraArgs) related)
    · simpa [extraEmpty, cache] using
        ListRel.cons (FrameRelated.apply extraArgs) related

/-- Pointwise-related join environments return related declarations for the
same join identifier. -/
theorem JoinEnvRelated.findJoinPoint?
    (related : JoinEnvRelated codeRel left right) (target : FVarId) :
    OptionalRel (FunDeclRelated codeRel)
      (Impure.findJoinPoint? left target) (Impure.findJoinPoint? right target) := by
  unfold JoinEnvRelated at related
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      rename_i leftHead rightHead leftTail rightTail
      have predicateEq :
          (leftHead.1.name == target.name) =
            (rightHead.1.name == target.name) := by
        exact congrArg (fun id : FVarId => id.name == target.name) head.key_eq
      change OptionalRel (FunDeclRelated codeRel)
        (if leftHead.1.name == target.name then some leftHead.2
          else Impure.findJoinPoint? leftTail target)
        (if rightHead.1.name == target.name then some rightHead.2
          else Impure.findJoinPoint? rightTail target)
      rw [predicateEq]
      cases found : rightHead.1.name == target.name with
      | false => simpa [found] using ih
      | true => simpa [found] using OptionalRel.some head.declaration

/-- Calling related top-level declarations preserves the recursive machine
relation across partial application, internal entry, external waiting, and
faults. -/
theorem invokeDecl_related
    (related : MachineRelated (CodeRel validCase) left right) :
    CoreResultRelated validCase
      (invokeDecl left name args) (invokeDecl right name args) := by
  have found := related.programs.findDecl? name
  generalize leftFoundEq : left.program.findDecl? name = leftFound at found
  generalize rightFoundEq : right.program.findDecl? name = rightFound at found
  unfold invokeDecl
  rw [leftFoundEq, rightFoundEq]
  cases found with
  | none => exact fail_related related (.unknownDecl name)
  | some declarations =>
      rename_i leftDecl rightDecl
      rcases declarations with
        ⟨nameEq, levelParamsEq, typeEq, paramsEq, safeEq, valueRel,
          recursiveEq, inlineAttrEq⟩
      simp only
      rw [paramsEq]
      by_cases tooFew : args.size < rightDecl.params.size
      · simp only [tooFew, ↓reduceIte]
        rw [related.runtime_eq]
        generalize allocation :
          alloc right.runtime (.closure name rightDecl.params.size args) = allocated
        rcases allocated with ⟨nextRuntime, reference⟩
        exact .next {
          programs := related.programs
          runtime_eq := rfl
          env_eq := related.env_eq
          joins := related.joins
          frames := related.frames
          control := .yielded (.object reference)
        }
      · simp only [tooFew, ↓reduceIte]
        let callArgs := args.extract 0 rightDecl.params.size
        let extraArgs := args.extract rightDecl.params.size args.size
        let leftPreparedFrames :=
          let frames := if extraArgs.isEmpty then left.frames
            else .apply extraArgs :: left.frames
          if rightDecl.params.isEmpty && args.isEmpty then
            .cache name :: frames else frames
        let rightPreparedFrames :=
          let frames := if extraArgs.isEmpty then right.frames
            else .apply extraArgs :: right.frames
          if rightDecl.params.isEmpty && args.isEmpty then
            .cache name :: frames else frames
        have preparedFrames :
            FramesRelated (CodeRel validCase)
              leftPreparedFrames rightPreparedFrames := by
          exact framesRelated_prepare_call name rightDecl.params args extraArgs
            related.frames
        generalize binding : bindParams rightDecl.params callArgs = bound
        cases bound with
        | error fault => exact fail_related related fault
        | ok env =>
            generalize leftValueEq : leftDecl.value = leftValue at valueRel ⊢
            generalize rightValueEq : rightDecl.value = rightValue at valueRel ⊢
            cases valueRel with
            | code body =>
                exact .next {
                  programs := related.programs
                  runtime_eq := related.runtime_eq
                  env_eq := rfl
                  joins := .nil
                  frames := preparedFrames
                  control := .code body
                }
            | extern metadata =>
                rw [typeEq]
                exact .external {
                  name
                  paramTypes := rightDecl.params.map (·.type)
                  resultType := rightDecl.type
                  args := callArgs
                } {
                  programs := related.programs
                  runtime_eq := related.runtime_eq
                  env_eq := rfl
                  joins := .nil
                  frames := preparedFrames
                  control := related.control
                }

/-- Closure invocation reads the same heap cell and delegates to related
top-level declaration lookup when the cell is a closure. -/
theorem invokeClosure_related
    (related : MachineRelated (CodeRel validCase) left right)
    (function : Value) (args : Array Value) :
    CoreResultRelated validCase
      (invokeClosure { left with control := .invokeValue function args }
        function args)
      (invokeClosure { right with control := .invokeValue function args }
        function args) := by
  let leftInvoke := { left with control := .invokeValue function args }
  let rightInvoke := { right with control := .invokeValue function args }
  have invokeRelated :
      MachineRelated (CodeRel validCase) leftInvoke rightInvoke := {
    programs := related.programs
    runtime_eq := related.runtime_eq
    env_eq := related.env_eq
    joins := related.joins
    frames := related.frames
    control := .invokeValue function args
  }
  have failRelated (fault : RuntimeFault) :
      CoreResultRelated validCase (fail leftInvoke fault) (fail rightInvoke fault) :=
    fail_related invokeRelated fault
  unfold invokeClosure
  cases function with
  | object reference =>
      cases reference with
      | tagged payload =>
          simp only
          exact failRelated .expectedClosure
      | heap location =>
          simp only
          have cellEq :
              getLiveCell left.runtime location = getLiveCell right.runtime location :=
            congrArg (fun runtime => getLiveCell runtime location) related.runtime_eq
          rw [cellEq]
          generalize cellRead : getLiveCell right.runtime location = result
          cases result with
          | error fault =>
              simp only
              exact failRelated fault
          | ok cell =>
              simp only
              cases cell.object with
              | closure name arity fixed =>
                  exact invokeDecl_related
                    (left := leftInvoke) (right := rightInvoke)
                    (name := name) (args := fixed ++ args) invokeRelated
              | ctor object => exact failRelated .expectedClosure
              | boxed type value => exact failRelated .expectedClosure
              | string value => exact failRelated .expectedClosure
              | natural value => exact failRelated .expectedClosure
              | integer value => exact failRelated .expectedClosure
              | byteArray value => exact failRelated .expectedClosure
              | «opaque» typeName => exact failRelated .expectedClosure
  | usize value =>
      simp only
      exact failRelated .expectedClosure
  | scalar value =>
      simp only
      exact failRelated .expectedClosure
  | erased =>
      simp only
      exact failRelated .expectedClosure
  | reuseToken location =>
      simp only
      exact failRelated .expectedClosure

/-- Yielding the same runtime value pops related frames in lockstep. -/
theorem coreStep_yielded_related
    (related : MachineRelated (CodeRel validCase) left right)
    (value : Value) :
    CoreResultRelated validCase
      (coreStep { left with control := .yielded value })
      (coreStep { right with control := .yielded value }) := by
  have framesRelated := related.frames
  unfold FramesRelated at framesRelated
  generalize leftFramesEq : left.frames = leftFrames at framesRelated ⊢
  generalize rightFramesEq : right.frames = rightFrames at framesRelated ⊢
  cases framesRelated with
  | nil =>
      simp only [coreStep]
      rw [observe_eq_of_runtime_eq
        (left := { left with control := .yielded value, frames := [] })
        (right := { right with control := .yielded value, frames := [] })
        related.runtime_eq (.returned value)]
      exact .done _
  | cons frame rest =>
      rename_i leftFrame rightFrame leftRest rightRest
      cases frame with
      | bind continuation joinEnvs =>
          simp only [coreStep]
          exact .next {
            programs := related.programs
            runtime_eq := related.runtime_eq
            env_eq := rfl
            joins := joinEnvs
            frames := rest
            control := .code continuation
          }
      | apply args =>
          simp only [coreStep]
          exact .next {
            programs := related.programs
            runtime_eq := related.runtime_eq
            env_eq := related.env_eq
            joins := related.joins
            frames := rest
            control := .invokeValue value args
          }
      | cache name =>
          simp only [coreStep]
          exact .next {
            programs := related.programs
            runtime_eq := congrArg
              (fun runtime => runtime.setGlobal name value) related.runtime_eq
            env_eq := related.env_eq
            joins := related.joins
            frames := rest
            control := .yielded value
          }

/-- Let-value evaluation is insensitive to recursively related code.  The
only program-sensitive form is partial application; related declarations have
the same parameter array, so it also allocates the same closure. -/
theorem evalLetValue_related
    (related : MachineRelated (CodeRel validCase) left right)
    (decl : LCNF.LetDecl .impure) :
    evalLetValue left decl = evalLetValue right decl := by
  rcases decl with ⟨fvarId, binderName, type, value⟩
  cases value with
  | pap name args =>
      simp only [evalLetValue]
      rw [related.env_eq]
      generalize argsEq : evalArgs right.env args = evaluatedArgs
      cases evaluatedArgs with
      | error fault => rfl
      | ok arguments =>
          have found := related.programs.findDecl? name
          generalize leftFoundEq : left.program.findDecl? name = leftFound at found ⊢
          generalize rightFoundEq : right.program.findDecl? name = rightFound at found ⊢
          cases found with
          | none => rfl
          | some declarations =>
              dsimp
              rw [declarations.params_eq, related.runtime_eq]
  | _ =>
      simp only [evalLetValue, related.runtime_eq, related.env_eq]

theorem coreStep_let_related
    (related : MachineRelated (CodeRel validCase) left right)
    (decl : LCNF.LetDecl .impure)
    (continuation : CodeRel validCase leftContinuation rightContinuation) :
    CoreResultRelated validCase
      (coreStep { left with control := .code (.let decl leftContinuation) })
      (coreStep { right with control := .code (.let decl rightContinuation) }) := by
  let leftCurrent := { left with control := .code (.let decl leftContinuation) }
  let rightCurrent := { right with control := .code (.let decl rightContinuation) }
  have current : MachineRelated (CodeRel validCase) leftCurrent rightCurrent :=
    machineRelated_withControl related (.code (.aligned (.let decl continuation)))
  have evaluationEq :
      evalLetValue leftCurrent decl = evalLetValue rightCurrent decl := by
    exact evalLetValue_related current decl
  simp only [coreStep]
  rw [evaluationEq]
  generalize evaluation : evalLetValue rightCurrent decl = result
  cases result with
  | error fault => exact fail_related current fault
  | ok result =>
      rcases result with ⟨nextRuntime, action⟩
      cases action with
      | value value =>
          have nextRelated : MachineRelated (CodeRel validCase)
              { left with
                runtime := nextRuntime
                env := bind left.env decl.fvarId value
                control := .code leftContinuation }
              { right with
                runtime := nextRuntime
                env := bind right.env decl.fvarId value
                control := .code rightContinuation } := {
            programs := related.programs
            runtime_eq := rfl
            env_eq := congrArg
              (fun env => bind env decl.fvarId value) related.env_eq
            joins := related.joins
            frames := related.frames
            control := .code continuation
          }
          exact .next nextRelated
      | invokeName name args =>
          have bindFrameRelated : FrameRelated (CodeRel validCase)
              (.bind decl.fvarId leftContinuation left.env left.joins)
              (.bind decl.fvarId rightContinuation right.env right.joins) := by
            rw [related.env_eq]
            exact .bind continuation related.joins
          have nextRelated : MachineRelated (CodeRel validCase)
              { left with
                runtime := nextRuntime
                frames := .bind decl.fvarId leftContinuation left.env left.joins ::
                  left.frames
                control := .invokeName name args }
              { right with
                runtime := nextRuntime
                frames := .bind decl.fvarId rightContinuation right.env right.joins ::
                  right.frames
                control := .invokeName name args } := {
            programs := related.programs
            runtime_eq := rfl
            env_eq := related.env_eq
            joins := related.joins
            frames := .cons bindFrameRelated related.frames
            control := .invokeName name args
          }
          simpa [pushBindFrame] using CoreResultRelated.next nextRelated
      | invokeValue function args =>
          have bindFrameRelated : FrameRelated (CodeRel validCase)
              (.bind decl.fvarId leftContinuation left.env left.joins)
              (.bind decl.fvarId rightContinuation right.env right.joins) := by
            rw [related.env_eq]
            exact .bind continuation related.joins
          have nextRelated : MachineRelated (CodeRel validCase)
              { left with
                runtime := nextRuntime
                frames := .bind decl.fvarId leftContinuation left.env left.joins ::
                  left.frames
                control := .invokeValue function args }
              { right with
                runtime := nextRuntime
                frames := .bind decl.fvarId rightContinuation right.env right.joins ::
                  right.frames
                control := .invokeValue function args } := {
            programs := related.programs
            runtime_eq := rfl
            env_eq := related.env_eq
            joins := related.joins
            frames := .cons bindFrameRelated related.frames
            control := .invokeValue function args
          }
          simpa [pushBindFrame] using CoreResultRelated.next nextRelated

theorem coreStep_return_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId) :
    CoreResultRelated validCase
      (coreStep { left with control := .code (.return fvarId) })
      (coreStep { right with control := .code (.return fvarId) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned (HeadRel.return fvarId)))
  simp only [coreStep]
  rw [related.env_eq]
  generalize valueRead : lookupValue right.env fvarId = result
  cases result with
  | error fault => exact fail_related current fault
  | ok value =>
      exact .next {
        programs := related.programs
        runtime_eq := related.runtime_eq
        env_eq := rfl
        joins := related.joins
        frames := related.frames
        control := .yielded value
      }

theorem coreStep_unreach_related
    (related : MachineRelated (CodeRel validCase) left right)
    (type : Expr) :
    CoreResultRelated validCase
      (coreStep { left with control := .code (.unreach type) })
      (coreStep { right with control := .code (.unreach type) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned (HeadRel.unreach type)))
  simpa only [coreStep] using fail_related current .unreachable

theorem coreStep_jp_related
    (related : MachineRelated (CodeRel validCase) left right)
    (body : CodeRel validCase leftBody rightBody)
    (continuation : CodeRel validCase leftContinuation rightContinuation)
    (fvarId : FVarId) (binderName : Name)
    (params : Array (LCNF.Param .impure)) (type : Expr) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.jp (.mk fvarId binderName params type leftBody)
          leftContinuation)) })
      (coreStep { right with control :=
        (.code (.jp (.mk fvarId binderName params type rightBody)
          rightContinuation)) }) := by
  have declaration : FunDeclRelated (CodeRel validCase)
      (.mk fvarId binderName params type leftBody)
      (.mk fvarId binderName params type rightBody) := {
    fvarId_eq := rfl
    binderName_eq := rfl
    params_eq := rfl
    type_eq := rfl
    value := body
  }
  have joins : JoinEnvRelated (CodeRel validCase)
      ((fvarId, .mk fvarId binderName params type leftBody) :: left.joins)
      ((fvarId, .mk fvarId binderName params type rightBody) :: right.joins) := by
    have oldJoins := related.joins
    unfold JoinEnvRelated at oldJoins ⊢
    exact .cons { key_eq := rfl, declaration } oldJoins
  simp only [coreStep]
  exact .next {
    programs := related.programs
    runtime_eq := related.runtime_eq
    env_eq := related.env_eq
    joins
    frames := related.frames
    control := .code continuation
  }

theorem coreStep_jmp_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId) (args : Array (LCNF.Arg .impure)) :
    CoreResultRelated validCase
      (coreStep { left with control := .code (.jmp fvarId args) })
      (coreStep { right with control := .code (.jmp fvarId args) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned (HeadRel.jmp fvarId args)))
  have found := JoinEnvRelated.findJoinPoint? related.joins fvarId
  generalize leftFoundEq : Impure.findJoinPoint? left.joins fvarId = leftFound
    at found
  generalize rightFoundEq : Impure.findJoinPoint? right.joins fvarId = rightFound
    at found
  simp only [coreStep]
  rw [leftFoundEq, rightFoundEq]
  cases found with
  | none => exact fail_related current (.unknownJoinPoint fvarId)
  | some declaration =>
      rename_i leftDecl rightDecl
      dsimp
      have argsEvaluationEq :
          evalArgs left.env args = evalArgs right.env args :=
        congrArg (fun env => evalArgs env args) related.env_eq
      rw [argsEvaluationEq]
      generalize argsEq : evalArgs right.env args = evaluatedArgs
      cases evaluatedArgs with
      | error fault => exact fail_related current fault
      | ok values =>
          dsimp
          have bindingEvaluationEq :
              bindParamsOver left.env leftDecl.params values =
                bindParamsOver right.env rightDecl.params values := by
            rw [related.env_eq, declaration.params_eq]
          rw [bindingEvaluationEq]
          generalize bindingEq :
            bindParamsOver right.env rightDecl.params values = binding
          cases binding with
          | error fault => exact fail_related current fault
          | ok env =>
              exact .next {
                programs := related.programs
                runtime_eq := related.runtime_eq
                env_eq := rfl
                joins := related.joins
                frames := related.frames
                control := .code declaration.value
              }

theorem coreStep_cases_related
    (related : MachineRelated (CodeRel validCase) left right)
    (typeName : Name) (resultType : Expr) (discr : FVarId)
    (leftAlts rightAlts : Array (LCNF.Alt .impure))
    (selected : ∀ tag,
      validCase (.mk typeName resultType discr leftAlts) tag →
      SelectionRel validCase (chooseAlt tag leftAlts.toList)
        (chooseAlt tag rightAlts.toList))
    (ready : ∀ value tag,
      lookupValue left.env
        (LCNF.Cases.mk typeName resultType discr leftAlts).discr = .ok value →
      getTag left.runtime value = .ok tag →
      validCase (.mk typeName resultType discr leftAlts) tag) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.cases (.mk typeName resultType discr leftAlts))) })
      (coreStep { right with control :=
        (.code (.cases (.mk typeName resultType discr rightAlts))) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned
      (HeadRel.cases typeName resultType discr leftAlts rightAlts selected)))
  simp only [coreStep]
  have lookupEvaluationEq :
      lookupValue left.env (LCNF.Cases.mk typeName resultType discr leftAlts).discr =
        lookupValue right.env
          (LCNF.Cases.mk typeName resultType discr rightAlts).discr :=
    congrArg (fun env => lookupValue env discr) related.env_eq
  rw [lookupEvaluationEq]
  generalize lookupEq :
    lookupValue right.env
      (LCNF.Cases.mk typeName resultType discr rightAlts).discr = lookupResult
  cases lookupResult with
  | error fault => exact fail_related current fault
  | ok value =>
      dsimp
      have tagEvaluationEq :
          getTag left.runtime value = getTag right.runtime value :=
        congrArg (fun runtime => getTag runtime value) related.runtime_eq
      rw [tagEvaluationEq]
      generalize tagEq : getTag right.runtime value = tagResult
      cases tagResult with
      | error fault => exact fail_related current fault
      | ok tag =>
          dsimp
          have allowed : validCase (.mk typeName resultType discr leftAlts) tag :=
            ready value tag (lookupEvaluationEq.trans lookupEq)
              (tagEvaluationEq.trans tagEq)
          generalize leftChoiceEq :
            chooseAlt tag
              (LCNF.Cases.mk typeName resultType discr leftAlts).alts.toList =
                leftChoice
          generalize rightChoiceEq :
            chooseAlt tag
              (LCNF.Cases.mk typeName resultType discr rightAlts).alts.toList =
                rightChoice
          have alternatives : SelectionRel validCase leftChoice rightChoice := by
            rw [← leftChoiceEq, ← rightChoiceEq]
            exact selected tag allowed
          cases alternatives with
          | none => exact fail_related current .invalidCases
          | some code =>
              exact .next {
                programs := related.programs
                runtime_eq := related.runtime_eq
                env_eq := related.env_eq
                joins := related.joins
                frames := related.frames
                control := .code code
              }

theorem coreStep_oset_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId) (index : Nat) (arg : LCNF.Arg .impure)
    (continuation : CodeRel validCase leftContinuation rightContinuation) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.oset fvarId index arg leftContinuation)) })
      (coreStep { right with control :=
        (.code (.oset fvarId index arg rightContinuation)) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned
      (HeadRel.oset fvarId index arg continuation)))
  have objectEvaluationEq :
      lookupValue left.env fvarId = lookupValue right.env fvarId :=
    congrArg (fun env => lookupValue env fvarId) related.env_eq
  have fieldEvaluationEq :
      evalArg left.env arg = evalArg right.env arg :=
    congrArg (fun env => evalArg env arg) related.env_eq
  simp only [coreStep]
  rw [objectEvaluationEq, fieldEvaluationEq]
  generalize objectEq : lookupValue right.env fvarId = objectResult
  cases objectResult with
  | error fault => exact fail_related current fault
  | ok object =>
      generalize fieldEq : evalArg right.env arg = fieldResult
      cases fieldResult with
      | error fault => exact fail_related current fault
      | ok field =>
          dsimp
          have updateEq :
              setObjectField left.runtime object index field =
                setObjectField right.runtime object index field :=
            congrArg
              (fun runtime => setObjectField runtime object index field)
              related.runtime_eq
          rw [updateEq]
          exact runtimeResult_related current continuation
            (setObjectField right.runtime object index field)

theorem coreStep_uset_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId) (index : Nat) (fieldId : FVarId)
    (continuation : CodeRel validCase leftContinuation rightContinuation) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.uset fvarId index fieldId leftContinuation)) })
      (coreStep { right with control :=
        (.code (.uset fvarId index fieldId rightContinuation)) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned
      (HeadRel.uset fvarId index fieldId continuation)))
  have objectEvaluationEq :
      lookupValue left.env fvarId = lookupValue right.env fvarId :=
    congrArg (fun env => lookupValue env fvarId) related.env_eq
  have fieldEvaluationEq :
      lookupValue left.env fieldId = lookupValue right.env fieldId :=
    congrArg (fun env => lookupValue env fieldId) related.env_eq
  simp only [coreStep]
  rw [objectEvaluationEq, fieldEvaluationEq]
  generalize objectEq : lookupValue right.env fvarId = objectResult
  cases objectResult with
  | error fault => exact fail_related current fault
  | ok object =>
      generalize fieldEq : lookupValue right.env fieldId = fieldResult
      cases fieldResult with
      | error fault => exact fail_related current fault
      | ok field =>
          dsimp
          have updateEq :
              setUSizeField left.runtime object index field =
                setUSizeField right.runtime object index field :=
            congrArg
              (fun runtime => setUSizeField runtime object index field)
              related.runtime_eq
          rw [updateEq]
          exact runtimeResult_related current continuation
            (setUSizeField right.runtime object index field)

theorem coreStep_sset_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId) (width offset : Nat) (fieldId : FVarId) (type : Expr)
    (continuation : CodeRel validCase leftContinuation rightContinuation) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.sset fvarId width offset fieldId type leftContinuation)) })
      (coreStep { right with control :=
        (.code (.sset fvarId width offset fieldId type rightContinuation)) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned
      (HeadRel.sset fvarId width offset fieldId type continuation)))
  have objectEvaluationEq :
      lookupValue left.env fvarId = lookupValue right.env fvarId :=
    congrArg (fun env => lookupValue env fvarId) related.env_eq
  have fieldEvaluationEq :
      lookupValue left.env fieldId = lookupValue right.env fieldId :=
    congrArg (fun env => lookupValue env fieldId) related.env_eq
  simp only [coreStep]
  rw [objectEvaluationEq, fieldEvaluationEq]
  generalize objectEq : lookupValue right.env fvarId = objectResult
  cases objectResult with
  | error fault => exact fail_related current fault
  | ok object =>
      generalize fieldEq : lookupValue right.env fieldId = fieldResult
      cases fieldResult with
      | error fault => exact fail_related current fault
      | ok field =>
          dsimp
          have updateEq :
              setScalarField left.runtime object width offset field =
                setScalarField right.runtime object width offset field :=
            congrArg
              (fun runtime => setScalarField runtime object width offset field)
              related.runtime_eq
          rw [updateEq]
          exact runtimeResult_related current continuation
            (setScalarField right.runtime object width offset field)

theorem coreStep_setTag_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId) (tag : Nat)
    (continuation : CodeRel validCase leftContinuation rightContinuation) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.setTag fvarId tag leftContinuation)) })
      (coreStep { right with control :=
        (.code (.setTag fvarId tag rightContinuation)) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned
      (HeadRel.setTag fvarId tag continuation)))
  have objectEvaluationEq :
      lookupValue left.env fvarId = lookupValue right.env fvarId :=
    congrArg (fun env => lookupValue env fvarId) related.env_eq
  simp only [coreStep]
  rw [objectEvaluationEq]
  generalize objectEq : lookupValue right.env fvarId = objectResult
  cases objectResult with
  | error fault => exact fail_related current fault
  | ok object =>
      dsimp
      have updateEq :
          setTag left.runtime object tag = setTag right.runtime object tag :=
        congrArg (fun runtime => setTag runtime object tag) related.runtime_eq
      rw [updateEq]
      exact runtimeResult_related current continuation
        (setTag right.runtime object tag)

theorem coreStep_inc_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId) (amount : Nat) (check persistent : Bool)
    (continuation : CodeRel validCase leftContinuation rightContinuation) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.inc fvarId amount check persistent leftContinuation)) })
      (coreStep { right with control :=
        (.code (.inc fvarId amount check persistent rightContinuation)) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned
      (HeadRel.inc fvarId amount check persistent continuation)))
  cases persistent with
  | true =>
      simp only [coreStep, ↓reduceIte]
      exact .next {
        programs := related.programs
        runtime_eq := related.runtime_eq
        env_eq := related.env_eq
        joins := related.joins
        frames := related.frames
        control := .code continuation
      }
  | false =>
      have valueEvaluationEq :
          lookupValue left.env fvarId = lookupValue right.env fvarId :=
        congrArg (fun env => lookupValue env fvarId) related.env_eq
      simp only [coreStep, Bool.false_eq_true, ↓reduceIte]
      rw [valueEvaluationEq]
      generalize valueEq : lookupValue right.env fvarId = valueResult
      cases valueResult with
      | error fault => exact fail_related current fault
      | ok value =>
          dsimp
          have updateEq :
              incValue left.runtime value amount check =
                incValue right.runtime value amount check :=
            congrArg
              (fun runtime => incValue runtime value amount check)
              related.runtime_eq
          rw [updateEq]
          exact runtimeResult_related current continuation
            (incValue right.runtime value amount check)

theorem coreStep_dec_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId) (amount : Nat) (check persistent : Bool)
    (objects : Option Nat)
    (continuation : CodeRel validCase leftContinuation rightContinuation) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.dec fvarId amount check persistent objects leftContinuation)) })
      (coreStep { right with control :=
        (.code (.dec fvarId amount check persistent objects rightContinuation)) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned
      (HeadRel.dec fvarId amount check persistent objects continuation)))
  cases persistent with
  | true =>
      simp only [coreStep, ↓reduceIte]
      exact .next {
        programs := related.programs
        runtime_eq := related.runtime_eq
        env_eq := related.env_eq
        joins := related.joins
        frames := related.frames
        control := .code continuation
      }
  | false =>
      have valueEvaluationEq :
          lookupValue left.env fvarId = lookupValue right.env fvarId :=
        congrArg (fun env => lookupValue env fvarId) related.env_eq
      simp only [coreStep, Bool.false_eq_true, ↓reduceIte]
      rw [valueEvaluationEq]
      generalize valueEq : lookupValue right.env fvarId = valueResult
      cases valueResult with
      | error fault => exact fail_related current fault
      | ok value =>
          dsimp
          have updateEq :
              decValue left.runtime value amount check =
                decValue right.runtime value amount check :=
            congrArg
              (fun runtime => decValue runtime value amount check)
              related.runtime_eq
          rw [updateEq]
          exact runtimeResult_related current continuation
            (decValue right.runtime value amount check)

theorem coreStep_del_related
    (related : MachineRelated (CodeRel validCase) left right)
    (fvarId : FVarId)
    (continuation : CodeRel validCase leftContinuation rightContinuation) :
    CoreResultRelated validCase
      (coreStep { left with control :=
        (.code (.del fvarId leftContinuation)) })
      (coreStep { right with control :=
        (.code (.del fvarId rightContinuation)) }) := by
  have current := machineRelated_withControl related
    (ControlRelated.code (CodeRel.aligned
      (HeadRel.del fvarId continuation)))
  have valueEvaluationEq :
      lookupValue left.env fvarId = lookupValue right.env fvarId :=
    congrArg (fun env => lookupValue env fvarId) related.env_eq
  simp only [coreStep]
  rw [valueEvaluationEq]
  generalize valueEq : lookupValue right.env fvarId = valueResult
  cases valueResult with
  | error fault => exact fail_related current fault
  | ok value =>
      dsimp
      have updateEq :
          deleteValue left.runtime value = deleteValue right.runtime value :=
        congrArg (fun runtime => deleteValue runtime value) related.runtime_eq
      rw [updateEq]
      exact runtimeResult_related current continuation
        (deleteValue right.runtime value)

/-- Every head-aligned recursive node takes one lockstep core transition.
Case dispatch is the sole aligned head that consumes the phase-readiness
obligation. -/
theorem coreStep_aligned_related
    (related : MachineRelated (CodeRel validCase) left right)
    (head : HeadRel validCase leftCode rightCode)
    (ready : CodeReadyAt validCase left leftCode rightCode) :
    CoreResultRelated validCase
      (coreStep { left with control := .code leftCode })
      (coreStep { right with control := .code rightCode }) := by
  cases head with
  | «let» decl continuation =>
      exact coreStep_let_related related decl continuation
  | jp fvarId binderName params type body continuation =>
      exact coreStep_jp_related related body continuation
        fvarId binderName params type
  | jmp fvarId args =>
      exact coreStep_jmp_related related fvarId args
  | cases typeName resultType discr leftAlts rightAlts selected =>
      exact coreStep_cases_related related typeName resultType discr
        leftAlts rightAlts selected (by
          intro value tag lookupEq tagEq
          exact CodeReadyAt.valid ready lookupEq tagEq)
  | «return» fvarId =>
      exact coreStep_return_related related fvarId
  | unreach type =>
      exact coreStep_unreach_related related type
  | oset fvarId index arg continuation =>
      exact coreStep_oset_related related fvarId index arg continuation
  | uset fvarId index fieldId continuation =>
      exact coreStep_uset_related related fvarId index fieldId continuation
  | sset fvarId width offset fieldId type continuation =>
      exact coreStep_sset_related related fvarId width offset fieldId type
        continuation
  | setTag fvarId tag continuation =>
      exact coreStep_setTag_related related fvarId tag continuation
  | inc fvarId amount check persistent continuation =>
      exact coreStep_inc_related related fvarId amount check persistent continuation
  | dec fvarId amount check persistent objects continuation =>
      exact coreStep_dec_related related fvarId amount check persistent objects
        continuation
  | del fvarId continuation =>
      exact coreStep_del_related related fvarId continuation

theorem coreStep_invokeName_related
    (related : MachineRelated (CodeRel validCase) left right)
    (name : Name) (args : Array Value) :
    CoreResultRelated validCase
      (coreStep { left with control := .invokeName name args })
      (coreStep { right with control := .invokeName name args }) := by
  have current := machineRelated_withControl related
    (ControlRelated.invokeName name args)
  by_cases argsEmpty : args.isEmpty
  · simp only [coreStep, argsEmpty]
    have globalEq :
        findGlobal? left.runtime.globals name =
          findGlobal? right.runtime.globals name :=
      congrArg (fun runtime => findGlobal? runtime.globals name)
        related.runtime_eq
    rw [globalEq]
    generalize globalRead : findGlobal? right.runtime.globals name = global
    cases global with
    | none => exact invokeDecl_related current
    | some value =>
        exact .next {
          programs := related.programs
          runtime_eq := related.runtime_eq
          env_eq := related.env_eq
          joins := related.joins
          frames := related.frames
          control := .yielded value
        }
  · simp only [coreStep, argsEmpty]
    exact invokeDecl_related current

theorem coreStep_invokeValue_related
    (related : MachineRelated (CodeRel validCase) left right)
    (function : Value) (args : Array Value) :
    CoreResultRelated validCase
      (coreStep { left with control := .invokeValue function args })
      (coreStep { right with control := .invokeValue function args }) := by
  simpa only [coreStep] using
    invokeClosure_related related function args

/-- An eliminated case is the unique non-lockstep node: source selects its
permitted branch in one internal step while target remains at the recursively
related replacement code. -/
theorem coreStep_eliminate
    (related : MachineRelated (CodeRel validCase) left right)
    (cases : LCNF.Cases .impure) (target : LCNF.Code .impure)
    (selected : ∀ tag, validCase cases tag →
      ElimSelectionRel validCase target
        (chooseAlt tag cases.alts.toList))
    (ready : CodeReadyAt validCase left (.cases cases) target) :
    ∃ leftAfter,
      coreStep { left with control := .code (.cases cases) } = .next leftAfter ∧
      MachineRelated (CodeRel validCase) leftAfter
        { right with control := .code target } := by
  rcases ready with ⟨value, tag, lookupEq, tagEq, allowed⟩
  have selection := selected tag allowed
  generalize choiceEq : chooseAlt tag cases.alts.toList = choice at selection
  cases selection with
  | some code =>
      rename_i source
      refine ⟨{ left with control := .code source }, ?_, ?_⟩
      · simp only [coreStep, lookupEq, tagEq, choiceEq]
      · exact machineRelated_withControl related (.code code)

/-- Applying one common external response to related waiting states preserves
the structural relation. -/
theorem resumeExternal_related
    (related : MachineRelated (CodeRel validCase) left right)
    (request : ExternalRequest) (response : ExternalResponse) :
    MachineRelated (CodeRel validCase)
      (resumeExternal request left response)
      (resumeExternal request right response) := by
  exact {
    programs := related.programs
    runtime_eq := by
      unfold resumeExternal
      simp only [MachineState.withValue]
      rw [related.runtime_eq]
    env_eq := related.env_eq
    joins := related.joins
    frames := related.frames
    control := .yielded response.value
  }

/-- A lockstep-related pair of core results matches any semantic source step
with one target step, including a common externally supplied response. -/
theorem match_coreResult
    (beforeRelated : MachineRelated (CodeRel validCase) leftBefore rightBefore)
    (results : CoreResultRelated validCase
      (coreStep leftBefore) (coreStep rightBefore))
    (step : Step externals leftBefore leftAfter) :
    ∃ rightAfter, Reaches externals rightBefore rightAfter ∧
      MachineRelated (CodeRel validCase) leftAfter rightAfter := by
  generalize leftResultEq : coreStep leftBefore = leftResult at results
  generalize rightResultEq : coreStep rightBefore = rightResult at results
  cases results with
  | next afterRelated =>
      cases step with
      | internal transition =>
          rw [leftResultEq] at transition
          cases transition
          exact ⟨_, reaches_of_step (.internal rightResultEq), afterRelated⟩
      | external transition externalProof =>
          rw [leftResultEq] at transition
          contradiction
  | external request waitingRelated =>
      rename_i leftWaiting rightWaiting
      cases step with
      | internal transition =>
          rw [leftResultEq] at transition
          contradiction
      | external transition externalProof =>
          rw [leftResultEq] at transition
          cases transition
          rename_i response
          have targetExternal :
              externals request rightBefore.runtime response := by
            rw [← beforeRelated.runtime_eq]
            exact externalProof
          exact ⟨resumeExternal request rightWaiting response,
            reaches_of_step (.external rightResultEq targetExternal),
            resumeExternal_related waitingRelated request response⟩
  | done observation =>
      cases step with
      | internal transition =>
          rw [leftResultEq] at transition
          contradiction
      | external transition externalProof =>
          rw [leftResultEq] at transition
          contradiction

/-- Equal related terminal core results give a zero-step evaluation on the
target. -/
theorem terminal_coreResult
    (results : CoreResultRelated validCase
      (coreStep left) (coreStep right))
    (done : coreStep left = .done observation) :
    EvaluatesState externals right observation := by
  generalize leftResultEq : coreStep left = leftResult at results
  generalize rightResultEq : coreStep right = rightResult at results
  cases results with
  | next related =>
      rw [leftResultEq] at done
      contradiction
  | external request related =>
      rw [leftResultEq] at done
      contradiction
  | done result =>
      rw [leftResultEq] at done
      cases done
      exact ⟨0, right, .refl right, rightResultEq⟩

/-- Symmetric operational use of a lockstep-related core result: a target
step is matched by one source step while retaining the original orientation
of the structural relation. -/
theorem match_coreResult_right
    (beforeRelated : MachineRelated (CodeRel validCase) leftBefore rightBefore)
    (results : CoreResultRelated validCase
      (coreStep leftBefore) (coreStep rightBefore))
    (step : Step externals rightBefore rightAfter) :
    ∃ leftAfter, Reaches externals leftBefore leftAfter ∧
      MachineRelated (CodeRel validCase) leftAfter rightAfter := by
  generalize leftResultEq : coreStep leftBefore = leftResult at results
  generalize rightResultEq : coreStep rightBefore = rightResult at results
  cases results with
  | next afterRelated =>
      cases step with
      | internal transition =>
          rw [rightResultEq] at transition
          cases transition
          exact ⟨_, reaches_of_step (.internal leftResultEq), afterRelated⟩
      | external transition externalProof =>
          rw [rightResultEq] at transition
          contradiction
  | external request waitingRelated =>
      rename_i leftWaiting rightWaiting
      cases step with
      | internal transition =>
          rw [rightResultEq] at transition
          contradiction
      | external transition externalProof =>
          rw [rightResultEq] at transition
          cases transition
          rename_i response
          have sourceExternal :
              externals request leftBefore.runtime response := by
            rw [beforeRelated.runtime_eq]
            exact externalProof
          exact ⟨resumeExternal request leftWaiting response,
            reaches_of_step (.external leftResultEq sourceExternal),
            resumeExternal_related waitingRelated request response⟩
  | done observation =>
      cases step with
      | internal transition =>
          rw [rightResultEq] at transition
          contradiction
      | external transition externalProof =>
          rw [rightResultEq] at transition
          contradiction

/-- A terminal target core result gives a zero-step source evaluation when
the results are lockstep-related. -/
theorem terminal_coreResult_right
    (results : CoreResultRelated validCase
      (coreStep left) (coreStep right))
    (done : coreStep right = .done observation) :
    EvaluatesState externals left observation := by
  generalize leftResultEq : coreStep left = leftResult at results
  generalize rightResultEq : coreStep right = rightResult at results
  cases results with
  | next related =>
      rw [rightResultEq] at done
      contradiction
  | external request related =>
      rw [rightResultEq] at done
      contradiction
  | done result =>
      rw [rightResultEq] at done
      cases done
      exact ⟨0, left, .refl left, leftResultEq⟩

/-- One related machine pair either exposes lockstep-related core results or
performs one source-only eliminated-case step. -/
inductive MachineProgress
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (left right : MachineState) : Prop where
  | lockstep
      (results : CoreResultRelated validCase (coreStep left) (coreStep right)) :
      MachineProgress validCase left right
  | eliminate (leftAfter : MachineState)
      (transition : coreStep left = .next leftAfter)
      (related : MachineRelated (CodeRel validCase) leftAfter right) :
      MachineProgress validCase left right

theorem machineProgress_withControl
    (related : MachineRelated (CodeRel validCase) left right)
    (control : ControlRelated (CodeRel validCase) leftControl rightControl)
    (ready : ControlReadyAt validCase left leftControl rightControl) :
    MachineProgress validCase
      { left with control := leftControl }
      { right with control := rightControl } := by
  cases control with
  | code code =>
      cases code with
      | aligned head =>
          exact .lockstep (coreStep_aligned_related related head ready)
      | eliminate cases _ =>
          rename_i selection
          rcases coreStep_eliminate related cases _ selection ready with
            ⟨leftAfter, transition, afterRelated⟩
          exact .eliminate leftAfter transition afterRelated
  | yielded value =>
      exact .lockstep (coreStep_yielded_related related value)
  | invokeName name args =>
      exact .lockstep (coreStep_invokeName_related related name args)
  | invokeValue function args =>
      exact .lockstep (coreStep_invokeValue_related related function args)

theorem machineProgress
    (related : MachineRelated (CodeRel validCase) left right)
    (ready : ControlReadyAt validCase left left.control right.control) :
    MachineProgress validCase left right := by
  simpa using machineProgress_withControl related related.control ready

/-- Forward finite-stuttering simulation for the recursive graph.  Aligned
nodes match one step; eliminated cases match zero target steps. -/
theorem recursiveForward
    (laws : InvariantLaws externals validCase invariant) :
    StutteringSimulation externals
      (MachineRelatedWith (CodeRel validCase) invariant) where
  terminal := by
    intro left right observation refined done
    have ready := laws.ready refined.structural refined.invariant
    have progress := machineProgress refined.structural ready
    cases progress with
    | lockstep results =>
        exact terminal_coreResult results done
    | eliminate leftAfter transition afterRelated =>
        rw [transition] at done
        contradiction
  advance := by
    intro leftBefore leftAfter right refined step
    have ready := laws.ready refined.structural refined.invariant
    have progress := machineProgress refined.structural ready
    cases progress with
    | lockstep results =>
        rcases match_coreResult refined.structural results step with
          ⟨rightAfter, rightPath, afterStructural⟩
        have leftPath := reaches_of_step step
        have afterInvariant := laws.stable refined.invariant refined.structural
          leftPath rightPath afterStructural
        exact ⟨rightAfter, rightPath, {
          structural := afterStructural
          invariant := afterInvariant
        }⟩
    | eliminate expected transition afterStructural =>
        cases step with
        | internal actual =>
            rw [transition] at actual
            cases actual
            have leftPath : Reaches externals leftBefore leftAfter :=
              reaches_of_step (externals := externals) (Step.internal transition)
            have rightPath : Reaches externals right right :=
              reaches_refl right
            have afterInvariant := laws.stable refined.invariant refined.structural
              leftPath rightPath afterStructural
            exact ⟨right, rightPath, {
              structural := afterStructural
              invariant := afterInvariant
            }⟩
        | external actual externalProof =>
            rw [transition] at actual
            contradiction

/-- Source-side administrative normalization ending at a lockstep-related
pair of core results. -/
def LockstepNormalizes (externals : ExternalSpec)
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (invariant : MachineState → MachineState → Prop)
    (left right : MachineState) : Prop :=
  ∃ leftNormal,
    Reaches externals left leftNormal ∧
    MachineRelatedWith (CodeRel validCase) invariant leftNormal right ∧
    CoreResultRelated validCase (coreStep leftNormal) (coreStep right)

/-- Code-indexed presentation of source normalization. -/
def CodeLockstepNormalizes (externals : ExternalSpec)
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (invariant : MachineState → MachineState → Prop)
    (source target : LCNF.Code .impure) : Prop :=
  ∀ (left right : MachineState),
    MachineRelatedWith (CodeRel validCase) invariant
      { left with control := .code source }
      { right with control := .code target } →
    LockstepNormalizes externals validCase invariant
      { left with control := .code source }
      { right with control := .code target }

/-- The mutual selection motive exposes both its recursive code proof and its
normalization theorem once the selected option is known. -/
def ElimSelectionNormalization (externals : ExternalSpec)
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (invariant : MachineState → MachineState → Prop)
    (target : LCNF.Code .impure) : Option (LCNF.Code .impure) → Prop
  | none => False
  | some source =>
      CodeRel validCase source target ∧
      CodeLockstepNormalizes externals validCase invariant source target

theorem code_lockstepNormalizes
    (laws : InvariantLaws externals validCase invariant)
    (code : CodeRel validCase source target) :
    CodeLockstepNormalizes externals validCase invariant source target := by
  exact CodeRel.rec
    (motive_1 := fun source target _ =>
      CodeLockstepNormalizes externals validCase invariant source target)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun target choice _ =>
      ElimSelectionNormalization externals validCase invariant target choice)
    (aligned := by
      intro leftCode rightCode head headIH left right refined
      have ready := laws.ready refined.structural refined.invariant
      have results : CoreResultRelated validCase
          (coreStep { left with control := .code leftCode })
          (coreStep { right with control := .code rightCode }) := by
        apply coreStep_aligned_related refined.structural head
        simpa only [ControlReadyAt] using ready
      exact ⟨_, reaches_refl _, refined, results⟩)
    (eliminate := by
      intro cases target selected selectionIH left right refined
      have ready := laws.ready refined.structural refined.invariant
      change CodeReadyAt validCase
        { left with control := .code (.cases cases) } (.cases cases) target at ready
      rcases ready with ⟨value, tag, lookupEq, tagEq, allowed⟩
      have selectionNormalization := selectionIH tag allowed
      generalize choiceEq : chooseAlt tag cases.alts.toList = choice
        at selectionNormalization
      cases choice with
      | none => exact selectionNormalization.elim
      | some source =>
          rcases selectionNormalization with ⟨branchCode, normalizeBranch⟩
          let leftAfter := { left with control := .code source }
          have transition :
              coreStep { left with control := .code (.cases cases) } =
                .next leftAfter := by
            simp only [coreStep, lookupEq, tagEq, choiceEq, leftAfter]
          have afterStructural : MachineRelated (CodeRel validCase)
              leftAfter { right with control := .code target } := by
            simpa [leftAfter] using
              machineRelated_withControl refined.structural (.code branchCode)
          have leftPath : Reaches externals
              { left with control := .code (.cases cases) } leftAfter :=
            reaches_of_step (externals := externals) (.internal transition)
          have rightPath : Reaches externals
              { right with control := .code target }
              { right with control := .code target } := reaches_refl _
          have afterInvariant := laws.stable refined.invariant refined.structural
            leftPath rightPath afterStructural
          have afterRefined : MachineRelatedWith (CodeRel validCase) invariant
              leftAfter { right with control := .code target } := {
            structural := afterStructural
            invariant := afterInvariant
          }
          rcases normalizeBranch left right afterRefined with
            ⟨leftNormal, normalizedPath, normalized, results⟩
          exact ⟨leftNormal, leftPath.trans normalizedPath, normalized, results⟩)
    («let» := by intros; trivial)
    (jp := by intros; trivial)
    (jmp := by intros; trivial)
    (cases := by intros; trivial)
    («return» := by intros; trivial)
    (unreach := by intros; trivial)
    (oset := by intros; trivial)
    (uset := by intros; trivial)
    (sset := by intros; trivial)
    (setTag := by intros; trivial)
    (inc := by intros; trivial)
    (dec := by intros; trivial)
    (del := by intros; trivial)
    (none := trivial)
    (some := by intros; trivial)
    (by
      intro source target related normalize
      exact ⟨related, normalize⟩)
    code

/-- Normalize the source side of an arbitrary refined machine relation.  Only
code controls can stutter; runtime controls are already lockstep. -/
theorem machine_lockstepNormalizes
    (laws : InvariantLaws externals validCase invariant)
    (refined : MachineRelatedWith (CodeRel validCase) invariant left right) :
    LockstepNormalizes externals validCase invariant left right := by
  let leftMachine := left
  let rightMachine := right
  cases left
  cases right
  rcases refined with ⟨structural, invariantProof⟩
  rcases structural with
    ⟨programs, runtimeEq, envEq, joins, frames, control⟩
  cases control with
  | code code =>
      have current : MachineRelatedWith (CodeRel validCase) invariant
          leftMachine rightMachine := {
        structural := {
          programs, runtime_eq := runtimeEq, env_eq := envEq, joins, frames
          control := .code code
        }
        invariant := invariantProof
      }
      have normalized := code_lockstepNormalizes laws code
        leftMachine rightMachine (by simpa using current)
      simpa using normalized
  | yielded value =>
      have current : MachineRelatedWith (CodeRel validCase) invariant
          leftMachine rightMachine := {
        structural := {
          programs, runtime_eq := runtimeEq, env_eq := envEq, joins, frames
          control := .yielded value
        }
        invariant := invariantProof
      }
      have results := coreStep_yielded_related current.structural value
      exact ⟨leftMachine, reaches_refl leftMachine, current,
        by simpa using results⟩
  | invokeName name args =>
      have current : MachineRelatedWith (CodeRel validCase) invariant
          leftMachine rightMachine := {
        structural := {
          programs, runtime_eq := runtimeEq, env_eq := envEq, joins, frames
          control := .invokeName name args
        }
        invariant := invariantProof
      }
      have results :=
        coreStep_invokeName_related current.structural name args
      exact ⟨leftMachine, reaches_refl leftMachine, current,
        by simpa using results⟩
  | invokeValue function args =>
      have current : MachineRelatedWith (CodeRel validCase) invariant
          leftMachine rightMachine := {
        structural := {
          programs, runtime_eq := runtimeEq, env_eq := envEq, joins, frames
          control := .invokeValue function args
        }
        invariant := invariantProof
      }
      have results :=
        coreStep_invokeValue_related current.structural function args
      exact ⟨leftMachine, reaches_refl leftMachine, current,
        by simpa using results⟩

/-- Backward finite-stuttering simulation.  The source first normalizes any
finite chain of eliminated cases, then matches the target step in lockstep. -/
theorem recursiveBackward
    (laws : InvariantLaws externals validCase invariant) :
    StutteringSimulation externals
      (fun right left =>
        MachineRelatedWith (CodeRel validCase) invariant left right) where
  terminal := by
    intro right left observation refined done
    rcases machine_lockstepNormalizes laws refined with
      ⟨leftNormal, leftPath, normalized, results⟩
    exact evaluatesState_of_reaches leftPath
      (terminal_coreResult_right results done)
  advance := by
    intro rightBefore rightAfter left refined step
    rcases machine_lockstepNormalizes laws refined with
      ⟨leftNormal, normalizedPath, normalized, results⟩
    rcases match_coreResult_right normalized.structural results step with
      ⟨leftAfter, leftMatch, afterStructural⟩
    have rightPath := reaches_of_step step
    have afterInvariant := laws.stable normalized.invariant normalized.structural
      leftMatch rightPath afterStructural
    exact ⟨leftAfter, normalizedPath.trans leftMatch, {
      structural := afterStructural
      invariant := afterInvariant
    }⟩

/-- Generic non-lockstep bisimulation for the recursive simpCase graph. -/
theorem recursiveBisimulation
    (laws : InvariantLaws externals validCase invariant) :
    StutteringBisimulation externals
      (MachineRelatedWith (CodeRel validCase) invariant) where
  forward := recursiveForward laws
  backward := recursiveBackward laws

/-- Canonical hereditary invariant: every pair of structurally related future
states reachable from the current pair has a readable, permitted active case.
Its preservation follows by path composition. -/
def ReachablyReady (externals : ExternalSpec)
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (left right : MachineState) : Prop :=
  ∀ leftAfter rightAfter,
    Reaches externals left leftAfter →
    Reaches externals right rightAfter →
    MachineRelated (CodeRel validCase) leftAfter rightAfter →
    ControlReadyAt validCase leftAfter leftAfter.control rightAfter.control

theorem reachablyReadyLaws :
    InvariantLaws externals validCase (ReachablyReady externals validCase) where
  ready := by
    intro left right structural hereditary
    exact hereditary left right (reaches_refl left) (reaches_refl right) structural
  stable := by
    intro leftBefore rightBefore leftAfter rightAfter hereditary beforeStructural
      leftPath rightPath afterStructural
    intro leftFuture rightFuture leftTail rightTail futureStructural
    exact hereditary leftFuture rightFuture (leftPath.trans leftTail)
      (rightPath.trans rightTail) futureStructural

/-- Entry predicate corresponding exactly to the canonical hereditary
readiness invariant. -/
def ReachablyReadyAdmissible (externals : ExternalSpec)
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (before after : ImpureProgram) (entry : Name) (args : Array Value) : Prop :=
  ReachablyReady externals validCase
    (initialState before entry args) (initialState after entry args)

theorem initialInvariant_reachablyReady :
    InitialInvariantOn
      (ReachablyReadyAdmissible externals validCase before after)
      (ReachablyReady externals validCase) before after entries := by
  intro entry member args accepted
  exact accepted

/-- Whole-program correctness for any recursively related programs whose
entry invariant supplies readable, permitted case discriminants. -/
theorem samePhaseCorrectOn
    (programs : ProgramRelated (CodeRel validCase) before after)
    (initialInvariant :
      InitialInvariantOn admissible invariant before after entries)
    (laws : InvariantLaws externals validCase invariant) :
    SamePhaseCorrectOn (Impure.semantics externals)
      before after entries admissible :=
  samePhaseCorrectOn_of_refined_machine_bisimulation
    programs initialInvariant (recursiveBisimulation laws)

/-- Turn only the recursive program graph into a pass theorem by using the
canonical hereditary readiness condition as entry admissibility. -/
theorem samePhaseCorrectOn_reachablyReady
    (programs : ProgramRelated (CodeRel validCase) before after) :
    SamePhaseCorrectOn (Impure.semantics externals) before after entries
      (ReachablyReadyAdmissible externals validCase before after) :=
  samePhaseCorrectOn programs initialInvariant_reachablyReady
    reachablyReadyLaws

end Fir.LeanIR.Passes.SimpCaseRelation
