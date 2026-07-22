import Fir.LeanIR.Runtime

namespace Fir.LeanIR

namespace Impure

open Lean
open Lean.Compiler

abbrev JoinEnv := List (FVarId × LCNF.FunDecl .impure)

def findJoinPoint? : JoinEnv → FVarId → Option (LCNF.FunDecl .impure)
  | [], _ => none
  | (candidate, decl) :: rest, fvarId =>
      if candidate.name == fvarId.name then some decl else findJoinPoint? rest fvarId

def bindParamsOver (env : Env) (params : Array (LCNF.Param .impure)) (args : Array Value) :
    Except RuntimeFault Env :=
  if params.size == args.size then
    .ok <| (params.toList.zip args.toList).foldl
      (fun env pair => bind env pair.fst.fvarId pair.snd) env
  else
    .error (.arityMismatch params.size args.size)

inductive Control where
  | code (code : LCNF.Code .impure)
  | yielded (value : Value)
  | invokeName (name : Name) (args : Array Value)
  | invokeValue (function : Value) (args : Array Value)

inductive Frame where
  | bind (fvarId : FVarId) (continuation : LCNF.Code .impure) (env : Env) (joins : JoinEnv)
  | apply (args : Array Value)
  | cache (name : Name)

structure MachineState where
  program : ImpureProgram
  control : Control
  env : Env := []
  joins : JoinEnv := []
  frames : List Frame := []
  runtime : RuntimeState := {}

inductive CoreResult where
  | next (state : MachineState)
  | external (request : ExternalRequest) (waiting : MachineState)
  | done (observation : Observation)

def observe (state : MachineState) (outcome : Outcome) : Observation :=
  { outcome
    heap := state.runtime.heap
    world := state.runtime.world
    trace := state.runtime.trace }

def fail (state : MachineState) (fault : RuntimeFault) : CoreResult :=
  .done (observe state (.fault fault))

def MachineState.withValue (state : MachineState) (runtime : RuntimeState) (value : Value) :
    MachineState :=
  { state with runtime, control := .yielded value }

def MachineState.continueWith (state : MachineState) (runtime : RuntimeState)
    (env : Env) (code : LCNF.Code .impure) : MachineState :=
  { state with runtime, env, control := .code code }

def pushBindFrame (state : MachineState) (decl : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure) : MachineState :=
  { state with frames := .bind decl.fvarId continuation state.env state.joins :: state.frames }

inductive LetAction where
  | value (value : Value)
  | invokeName (name : Name) (args : Array Value)
  | invokeValue (function : Value) (args : Array Value)

def lookupValue (env : Env) (fvarId : FVarId) : Except RuntimeFault Value :=
  match lookup env fvarId with
  | some value => .ok value
  | none => .error (.unknownVar fvarId)

def evalLetValue (state : MachineState) (decl : LCNF.LetDecl .impure) :
    Except RuntimeFault (RuntimeState × LetAction) := do
  match decl.value with
  | .lit literalValue =>
      let (runtime, value) := literal state.runtime literalValue
      return (runtime, .value value)
  | .erased =>
      return (state.runtime, .value .erased)
  | .proj _ _ _ h => nomatch h
  | .const _ _ _ h => nomatch h
  | .fvar fvarId args =>
      let function ← lookupValue state.env fvarId
      let args ← evalArgs state.env args
      if args.isEmpty then
        return (state.runtime, .value function)
      return (state.runtime, .invokeValue function args)
  | .ctor info args =>
      let args ← evalArgs state.env args
      let (runtime, value) ← allocCtor state.runtime info args
      return (runtime, .value value)
  | .oproj index fvarId =>
      let object ← lookupValue state.env fvarId
      let value ← getObjectField state.runtime object index
      return (state.runtime, .value value)
  | .uproj index fvarId =>
      let object ← lookupValue state.env fvarId
      let value ← getUSizeSlot state.runtime object index
      return (state.runtime, .value value)
  | .sproj width offset fvarId =>
      let object ← lookupValue state.env fvarId
      let value ← getScalarField state.runtime object width offset
      return (state.runtime, .value value)
  | .fap name args =>
      let args ← evalArgs state.env args
      return (state.runtime, .invokeName name args)
  | .pap name args =>
      let args ← evalArgs state.env args
      let some target := state.program.findDecl? name | throw (.unknownDecl name)
      if args.size >= target.params.size then
        throw (.malformed s!"partial application {name} fixes {args.size} of {target.params.size} parameters")
      let (runtime, reference) := alloc state.runtime (.closure name target.params.size args)
      return (runtime, .value (.object reference))
  | .reset count fvarId =>
      let object ← lookupValue state.env fvarId
      let (runtime, token) ← reset state.runtime count object
      return (runtime, .value token)
  | .reuse fvarId info updateHeader args =>
      let token ← lookupValue state.env fvarId
      let args ← evalArgs state.env args
      let (runtime, value) ← reuse state.runtime token info updateHeader args
      return (runtime, .value value)
  | .box type fvarId =>
      let scalar ← lookupValue state.env fvarId
      let (runtime, value) ← box state.runtime type scalar
      return (runtime, .value value)
  | .unbox fvarId =>
      let object ← lookupValue state.env fvarId
      let value ← unbox state.runtime decl.type object
      return (state.runtime, .value value)
  | .isShared fvarId =>
      let object ← lookupValue state.env fvarId
      let value ← isShared state.runtime object
      return (state.runtime, .value value)

def findCtorAlt (tag : Nat) : List (LCNF.Alt .impure) → Option (LCNF.Code .impure)
  | [] => none
  | .ctorAlt info code :: rest =>
      if info.cidx == tag then some code else findCtorAlt tag rest
  | .default _ :: rest => findCtorAlt tag rest
  | .alt _ _ _ h :: _ => nomatch h

def findDefaultAlt : List (LCNF.Alt .impure) → Option (LCNF.Code .impure)
  | [] => none
  | .ctorAlt _ _ :: rest => findDefaultAlt rest
  | .default code :: _ => some code
  | .alt _ _ _ h :: _ => nomatch h

def chooseAlt (tag : Nat) (alts : List (LCNF.Alt .impure)) : Option (LCNF.Code .impure) :=
  (findCtorAlt tag alts).orElse fun _ => findDefaultAlt alts

def invokeDecl (state : MachineState) (name : Name) (args : Array Value) : CoreResult :=
  match state.program.findDecl? name with
  | none => fail state (.unknownDecl name)
  | some decl =>
      if args.size < decl.params.size then
        let (runtime, reference) := alloc state.runtime (.closure name decl.params.size args)
        .next (state.withValue runtime (.object reference))
      else
        let callArgs := args.extract 0 decl.params.size
        let extraArgs := args.extract decl.params.size args.size
        match bindParams decl.params callArgs with
        | .error fault => fail state fault
        | .ok env =>
            let frames :=
              let frames := if extraArgs.isEmpty then state.frames else .apply extraArgs :: state.frames
              if decl.params.isEmpty && args.isEmpty then .cache name :: frames else frames
            let state := { state with env, joins := [], frames }
            match decl.value with
            | .code code => .next { state with control := .code code }
            | .extern _ =>
                let request : ExternalRequest := {
                  name
                  paramTypes := decl.params.map (·.type)
                  resultType := decl.type
                  args := callArgs }
                .external request state

def invokeClosure (state : MachineState) (function : Value) (args : Array Value) : CoreResult :=
  match function with
  | .object (.heap location) =>
      match getLiveCell state.runtime location with
      | .error fault => fail state fault
      | .ok cell =>
          match cell.object with
          | .closure name _ fixed => invokeDecl state name (fixed ++ args)
          | _ => fail state .expectedClosure
  | _ => fail state .expectedClosure

def resumeExternal (request : ExternalRequest) (waiting : MachineState)
    (response : ExternalResponse) : MachineState :=
  let event : ExternalEvent := { name := request.name, args := request.args, result := response.value }
  let runtime : RuntimeState := {
    waiting.runtime with
    heap := response.heap
    nextLocation := response.nextLocation
    world := response.world
    trace := waiting.runtime.trace.push event }
  waiting.withValue runtime response.value

def coreStep (state : MachineState) : CoreResult :=
  match state.control with
  | .yielded value =>
      match state.frames with
      | [] => .done (observe state (.returned value))
      | .bind fvarId continuation env joins :: frames =>
          .next { state with
            control := .code continuation
            env := bind env fvarId value
            joins
            frames }
      | .apply args :: frames =>
          .next { state with control := .invokeValue value args, frames }
      | .cache name :: frames =>
          .next { state with
            runtime := state.runtime.setGlobal name value
            frames
            control := .yielded value }
  | .invokeName name args =>
      if args.isEmpty then
        match findGlobal? state.runtime.globals name with
        | some value => .next { state with control := .yielded value }
        | none => invokeDecl state name args
      else
        invokeDecl state name args
  | .invokeValue function args => invokeClosure state function args
  | .code code =>
      match code with
      | .let decl continuation =>
          match evalLetValue state decl with
          | .error fault => fail state fault
          | .ok (runtime, .value value) =>
              .next { state with
                runtime
                env := bind state.env decl.fvarId value
                control := .code continuation }
          | .ok (runtime, .invokeName name args) =>
              let state := pushBindFrame { state with runtime } decl continuation
              .next { state with control := .invokeName name args }
          | .ok (runtime, .invokeValue function args) =>
              let state := pushBindFrame { state with runtime } decl continuation
              .next { state with control := .invokeValue function args }
      | .fun _ _ h => nomatch h
      | .jp decl continuation =>
          .next { state with
            joins := (decl.fvarId, decl) :: state.joins
            control := .code continuation }
      | .jmp fvarId args =>
          match findJoinPoint? state.joins fvarId with
          | none => fail state (.unknownJoinPoint fvarId)
          | some decl =>
              match evalArgs state.env args with
              | .error fault => fail state fault
              | .ok args =>
                  match bindParamsOver state.env decl.params args with
                  | .error fault => fail state fault
                  | .ok env => .next { state with env, control := .code decl.value }
      | .cases cases =>
          match lookupValue state.env cases.discr with
          | .error fault => fail state fault
          | .ok discr =>
              match getTag state.runtime discr with
              | .error fault => fail state fault
              | .ok tag =>
                  match chooseAlt tag cases.alts.toList with
                  | some code => .next { state with control := .code code }
                  | none => fail state .invalidCases
      | .return fvarId =>
          match lookupValue state.env fvarId with
          | .ok value => .next { state with control := .yielded value }
          | .error fault => fail state fault
      | .unreach _ => fail state .unreachable
      | .oset fvarId index arg continuation =>
          match lookupValue state.env fvarId, evalArg state.env arg with
          | .ok object, .ok field =>
              match setObjectField state.runtime object index field with
              | .ok runtime => .next { state with runtime, control := .code continuation }
              | .error fault => fail state fault
          | .error fault, _ | _, .error fault => fail state fault
      | .uset fvarId index fieldId continuation =>
          match lookupValue state.env fvarId, lookupValue state.env fieldId with
          | .ok object, .ok field =>
              match setUSizeSlot state.runtime object index field with
              | .ok runtime => .next { state with runtime, control := .code continuation }
              | .error fault => fail state fault
          | .error fault, _ | _, .error fault => fail state fault
      | .sset fvarId width offset fieldId _ continuation =>
          match lookupValue state.env fvarId, lookupValue state.env fieldId with
          | .ok object, .ok field =>
              match setScalarField state.runtime object width offset field with
              | .ok runtime => .next { state with runtime, control := .code continuation }
              | .error fault => fail state fault
          | .error fault, _ | _, .error fault => fail state fault
      | .setTag fvarId tag continuation =>
          match lookupValue state.env fvarId with
          | .error fault => fail state fault
          | .ok object =>
              match setTag state.runtime object tag with
              | .ok runtime => .next { state with runtime, control := .code continuation }
              | .error fault => fail state fault
      | .inc fvarId amount check persistent continuation =>
          if persistent then
            .next { state with control := .code continuation }
          else
            match lookupValue state.env fvarId with
            | .error fault => fail state fault
            | .ok value =>
                match incValue state.runtime value amount check with
                | .ok runtime => .next { state with runtime, control := .code continuation }
                | .error fault => fail state fault
      | .dec fvarId amount check persistent _ continuation =>
          if persistent then
            .next { state with control := .code continuation }
          else
            match lookupValue state.env fvarId with
            | .error fault => fail state fault
            | .ok value =>
                match decValue state.runtime value amount check with
                | .ok runtime => .next { state with runtime, control := .code continuation }
                | .error fault => fail state fault
      | .del fvarId continuation =>
          match lookupValue state.env fvarId with
          | .error fault => fail state fault
          | .ok value =>
              match deleteValue state.runtime value with
              | .ok runtime => .next { state with runtime, control := .code continuation }
              | .error fault => fail state fault

/-- Canonical relational small-step semantics, parameterized by extern behavior. -/
inductive Step (externals : ExternalSpec) : MachineState → MachineState → Prop where
  | internal {before after : MachineState}
      (transition : coreStep before = .next after) : Step externals before after
  | external {before waiting : MachineState} {request : ExternalRequest}
      {response : ExternalResponse}
      (transition : coreStep before = .external request waiting)
      (external : externals request before.runtime response) :
      Step externals before (resumeExternal request waiting response)

inductive Steps (externals : ExternalSpec) : Nat → MachineState → MachineState → Prop where
  | refl (state : MachineState) : Steps externals 0 state state
  | step {count : Nat} {first second last : MachineState}
      (head : Step externals first second)
      (tail : Steps externals count second last) :
      Steps externals (count + 1) first last

/-- A state diverges when it can take arbitrarily many semantic steps. -/
def Diverges (externals : ExternalSpec) (initial : MachineState) : Prop :=
  ∀ count, ∃ state, Steps externals count initial state

inductive ExecResult where
  | next (state : MachineState)
  | done (observation : Observation)

def executeStep (externals : ExternalImpl) (state : MachineState) : ExecResult :=
  match coreStep state with
  | .next state => .next state
  | .done observation => .done observation
  | .external request waiting =>
      match externals.call request state.runtime with
      | .ok response => .next (resumeExternal request waiting response)
      | .error fault => .done (observe waiting (.fault fault))

inductive RunResult where
  | done (observation : Observation)
  | outOfFuel (state : MachineState)

inductive ExecSteps (externals : ExternalImpl) : Nat → MachineState → MachineState → Prop where
  | refl (state : MachineState) : ExecSteps externals 0 state state
  | step {count : Nat} {first second last : MachineState}
      (head : executeStep externals first = .next second)
      (tail : ExecSteps externals count second last) :
      ExecSteps externals (count + 1) first last

def ExecEvaluates (externals : ExternalImpl) (initial : MachineState)
    (observation : Observation) : Prop :=
  ∃ count final,
    ExecSteps externals count initial final ∧
    executeStep externals final = .done observation

def run (fuel : Nat) (externals : ExternalImpl) (state : MachineState) : RunResult :=
  match fuel with
  | 0 => .outOfFuel state
  | fuel + 1 =>
      match executeStep externals state with
      | .done observation => .done observation
      | .next state => run fuel externals state

theorem run_done_sound (externals : ExternalImpl) (observation : Observation) :
    ∀ fuel state, run fuel externals state = .done observation →
      ExecEvaluates externals state observation
  | 0, state, execution => by
      simp [run] at execution
  | fuel + 1, state, execution => by
      rw [run] at execution
      cases transition : executeStep externals state with
      | done result =>
          rw [transition] at execution
          cases execution
          exact ⟨0, state, .refl state, transition⟩
      | next next =>
          rw [transition] at execution
          obtain ⟨count, final, steps, done⟩ :=
            run_done_sound externals observation fuel next execution
          exact ⟨count + 1, final, .step transition steps, done⟩

def initialState (program : ImpureProgram) (entry : Name) (args : Array Value)
    (runtime : RuntimeState := {}) : MachineState :=
  { program, control := .invokeName entry args, runtime }

def runProgram (fuel : Nat) (externals : ExternalImpl) (program : ImpureProgram)
    (entry : Name) (args : Array Value) (runtime : RuntimeState := {}) : RunResult :=
  run fuel externals (initialState program entry args runtime)

theorem executeStep_sound {externals : ExternalSpec} {implementation : ExternalImpl}
    (implements : implementation.Implements externals) {before after : MachineState}
    (execution : executeStep implementation before = .next after) :
    Step externals before after := by
  unfold executeStep at execution
  split at execution
  next transition =>
    cases execution
    exact .internal transition
  next transition => contradiction
  next request waiting transition =>
    split at execution
    next response responseEq =>
      cases execution
      exact .external transition (implements request before.runtime response responseEq)
    next fault responseEq => contradiction

theorem execSteps_sound {specification : ExternalSpec} {implementation : ExternalImpl}
    (implements : implementation.Implements specification) :
    ExecSteps implementation count before after →
      Steps specification count before after := by
  intro execution
  induction execution with
  | refl state => exact .refl state
  | step head tail ih =>
      exact .step (executeStep_sound implements head) ih

@[simp] theorem run_zero (externals : ExternalImpl) (state : MachineState) :
    run 0 externals state = .outOfFuel state := rfl

end Impure

end Fir.LeanIR
