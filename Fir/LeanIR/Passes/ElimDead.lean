import Fir.LeanIR.Passes.NonLockstep

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.SimpCase

/-!
Proof kernels for Lean 4.33's impure `elimDeadVars` pass.

The upstream pass combines two independent obligations when it removes a
binding: evaluating the unused value must have no observable effect, and the
new binding must be irrelevant to the continuation.  Keeping those obligations
separate is useful both for the backwards liveness proof and for transformations
whose only runtime difference is unreachable heap garbage.
-/

/-- Audited local copy of Lean 4.33's impure `LetValue.safeToElim` predicate.
This is deliberately syntax-only; semantic safety is stated separately below. -/
def safeToElim : LCNF.LetValue .impure → Bool
  | .ctor .. | .reset .. | .reuse .. | .oproj .. | .uproj .. | .sproj ..
  | .lit .. | .pap .. | .box .. | .unbox .. | .erased .. | .isShared .. => true
  | .fap _ args => args.isEmpty
  | .fvar .. => false

/-- The syntax-only part of the safe-elimination policy whose successful
evaluation produces a local value in one interpreter step.  Operational
readiness (successful reads, arities, and ownership) remains a separate
semantic premise. -/
def locallyValueProducingSafeToElim : LCNF.LetValue .impure → Bool
  | .ctor .. | .reset .. | .reuse .. | .oproj .. | .uproj .. | .sproj ..
  | .lit .. | .pap .. | .box .. | .unbox .. | .erased .. | .isShared .. => true
  | .fap .. | .fvar .. => false

/-- Audit of Lean 4.33's eliminable impure let-value shapes.  The only
`safeToElim` case outside the locally value-producing family is a full
application whose argument array is empty. -/
theorem safeToElim_local_or_nullaryFap
    (value : LCNF.LetValue .impure)
    (safe : safeToElim value = true) :
    locallyValueProducingSafeToElim value = true ∨
      ∃ name arguments,
        value = .fap name arguments ∧ arguments.isEmpty = true := by
  cases value <;>
    simp_all [safeToElim, locallyValueProducingSafeToElim] <;>
    contradiction

/-! ## Transparent backwards liveness traversal -/

/-- SHA-256 of `Lean/Compiler/LCNF/ElimDead.lean` in Lean 4.33.0. -/
def lean433ElimDeadSourceSha256 : String :=
  "c5a22e15eab79ebd6ef1e8f302095c69aeaccb12275f7468b505b03cde97a582"

/-- Proof-facing finite set used by the transparent traversal. Lean 4.33's
upstream `UsedLocalDecls` is an `FVarIdSet` tree set; the traversal observes it
only through `contains` and `insert`, so this hash-set spelling retains the
same extensional behavior while keeping the proof interface transparent. -/
abbrev UsedLocals := Std.HashSet FVarId

def collectArg (used : UsedLocals) (argument : LCNF.Arg pu) : UsedLocals :=
  match argument with
  | .fvar fvarId => used.insert fvarId
  | .type _ _ | .erased => used

def collectArgList (used : UsedLocals) : List (LCNF.Arg pu) → UsedLocals
  | [] => used
  | argument :: rest => collectArgList (collectArg used argument) rest

def collectArgs (used : UsedLocals) (arguments : Array (LCNF.Arg pu)) :
    UsedLocals :=
  collectArgList used arguments.toList

def collectLetValue (used : UsedLocals) (value : LCNF.LetValue pu) :
    UsedLocals :=
  match value with
  | .erased | .lit .. => used
  | .proj _ _ fvarId _ | .reset _ fvarId _ | .sproj _ _ fvarId _
  | .uproj _ fvarId _ | .oproj _ fvarId _ | .box _ fvarId _
  | .unbox fvarId _ | .isShared fvarId _ => used.insert fvarId
  | .const _ _ arguments _ => collectArgs used arguments
  | .fvar fvarId arguments | .reuse fvarId _ _ arguments _ =>
      collectArgs (used.insert fvarId) arguments
  | .fap _ arguments _ | .pap _ arguments _ | .ctor _ arguments _ =>
      collectArgs used arguments

abbrev ShadowResult := LCNF.Code .impure × UsedLocals

/-- Transparent impure specialization of the compiler's opaque
`LCNF.Alt.updateCode`. -/
def updateAltCode (alternative : LCNF.Alt .impure)
    (code : LCNF.Code .impure) : LCNF.Alt .impure :=
  match alternative with
  | .ctorAlt info _ => .ctorAlt info code
  | .default _ => .default code
  | .alt _ _ _ impossible => nomatch impossible

/-- Transform case alternatives left-to-right while threading the backwards
used set.  Keeping this list recursion outside `shadowCode?` makes the exact
case traversal available to the coverage proof. -/
def shadowAltList?
    (transformCode : UsedLocals → LCNF.Code .impure → Option ShadowResult)
    (used : UsedLocals) :
    List (LCNF.Alt .impure) →
      Option (List (LCNF.Alt .impure) × UsedLocals)
  | [] => some ([], used)
  | alternative :: rest => do
      let (code, used) ← transformCode used alternative.getCode
      let alternative := updateAltCode alternative code
      let (rest, used) ← shadowAltList? transformCode used rest
      return (alternative :: rest, used)

/-- Fuel-indexed transparent copy of the output-producing part of Lean 4.33's
private `Code.elimDead`.  The compiler's `eraseLetDecl`/`eraseFunDecl` calls
update only its local context and are intentionally absent.  Every recursive
code call consumes fuel; terminal nodes remain available at zero fuel. -/
def shadowCode? : Nat → UsedLocals → LCNF.Code .impure → Option ShadowResult
  | 0, used, .jmp target arguments =>
      some (.jmp target arguments,
        collectArgs (used.insert target) arguments)
  | 0, used, .return result => some (.return result, used.insert result)
  | 0, used, .unreach type => some (.unreach type, used)
  | 0, _, _ => none
  | fuel + 1, used, code =>
      match code with
      | .let declaration continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          if used.contains declaration.fvarId || !safeToElim declaration.value then
            return (.let declaration continuation,
              collectLetValue used declaration.value)
          else
            return (continuation, used)
      | .jp (.mk fvarId binderName params type body) continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          if used.contains fvarId then
            let (body, used) ← shadowCode? fuel used body
            return (.jp (.mk fvarId binderName params type body) continuation,
              used)
          else
            return (continuation, used)
      | .cases (.mk typeName resultType discr alternatives) => do
          let (alternatives, used) ←
            shadowAltList? (shadowCode? fuel) used alternatives.toList
          return (.cases (.mk typeName resultType discr alternatives.toArray),
            used.insert discr)
      | .jmp target arguments =>
          some (.jmp target arguments,
            collectArgs (used.insert target) arguments)
      | .return result => some (.return result, used.insert result)
      | .unreach type => some (.unreach type, used)
      | .oset object index field continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          if used.contains object then
            return (.oset object index field continuation,
              collectArg used field)
          else
            return (continuation, used)
      | .uset object index field continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          if used.contains object then
            return (.uset object index field continuation, used.insert field)
          else
            return (continuation, used)
      | .sset object width offset field type continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          if used.contains object then
            return (.sset object width offset field type continuation,
              used.insert field)
          else
            return (continuation, used)
      | .setTag object tag continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          return (.setTag object tag continuation, used.insert object)
      | .inc object amount check persistent continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          return (.inc object amount check persistent continuation,
            used.insert object)
      | .dec object amount check persistent objects continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          return (.dec object amount check persistent objects continuation,
            used.insert object)
      | .del object continuation => do
          let (continuation, used) ← shadowCode? fuel used continuation
          return (.del object continuation, used.insert object)
      | .fun _ _ impossible => nomatch impossible

def shadowDecl? (fuel : Nat) (declaration : LCNF.Decl .impure) :
    Option (LCNF.Decl .impure) :=
  match declaration.value with
  | .extern _ => some declaration
  | .code code => do
      let (code, _) ← shadowCode? fuel {} code
      return { declaration with value := .code code }

def shadowDecls? (fuel : Nat) :
    List (LCNF.Decl .impure) → Option (List (LCNF.Decl .impure))
  | [] => some []
  | declaration :: rest => do
      return (← shadowDecl? fuel declaration) :: (← shadowDecls? fuel rest)

def shadowProgram? (fuel : Nat) (program : ImpureProgram) :
    Option ImpureProgram := do
  let declarations ← shadowDecls? fuel program.decls.toList
  return { decls := declarations.toArray }

/-! ## Conservative executable nullary policy -/

/-- Recognize the one syntax-only `safeToElim` case that is not locally
value-producing under FIR's impure interpreter. -/
def isNullaryFap : LCNF.LetValue .impure → Bool
  | .fap _ arguments => arguments.isEmpty
  | _ => false

/-- Logical characterization used by the checked traversal's proof layer. -/
theorem isNullaryFap_eq_true_iff
    (value : LCNF.LetValue .impure) :
    isNullaryFap value = true ↔
      ∃ name arguments,
        value = .fap name arguments ∧ arguments.isEmpty = true := by
  cases value <;> simp [isNullaryFap]

/-- Pass-aware policy checker for the audited transparent traversal.

This computes exactly the same result as `shadowCode?` on accepted inputs, but
fails closed when the pass would delete a zero-argument full application.
Unlike a source-wide ban, retained nullary applications remain accepted. -/
def nullarySafeShadowCode? :
    Nat → UsedLocals → LCNF.Code .impure → Option ShadowResult
  | 0, used, .jmp target arguments =>
      some (.jmp target arguments,
        collectArgs (used.insert target) arguments)
  | 0, used, .return result =>
      some (.return result, used.insert result)
  | 0, used, .unreach type => some (.unreach type, used)
  | 0, _, _ => none
  | fuel + 1, used, code =>
      match code with
      | .let declaration continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          if used.contains declaration.fvarId ||
              !safeToElim declaration.value then
            return (.let declaration continuation,
              collectLetValue used declaration.value)
          else if isNullaryFap declaration.value then
            none
          else
            return (continuation, used)
      | .jp (.mk fvarId binderName params type body) continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          if used.contains fvarId then
            let (body, used) ←
              nullarySafeShadowCode? fuel used body
            return (.jp (.mk fvarId binderName params type body)
              continuation, used)
          else
            return (continuation, used)
      | .cases (.mk typeName resultType discr alternatives) => do
          let (alternatives, used) ←
            shadowAltList? (nullarySafeShadowCode? fuel)
              used alternatives.toList
          return (.cases
            (.mk typeName resultType discr alternatives.toArray),
              used.insert discr)
      | .jmp target arguments =>
          some (.jmp target arguments,
            collectArgs (used.insert target) arguments)
      | .return result =>
          some (.return result, used.insert result)
      | .unreach type => some (.unreach type, used)
      | .oset object index field continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          if used.contains object then
            return (.oset object index field continuation,
              collectArg used field)
          else
            return (continuation, used)
      | .uset object index field continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          if used.contains object then
            return (.uset object index field continuation,
              used.insert field)
          else
            return (continuation, used)
      | .sset object width offset field type continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          if used.contains object then
            return (.sset object width offset field type continuation,
              used.insert field)
          else
            return (continuation, used)
      | .setTag object tag continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          return (.setTag object tag continuation, used.insert object)
      | .inc object amount check persistent continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          return (.inc object amount check persistent continuation,
            used.insert object)
      | .dec object amount check persistent objects continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          return (.dec object amount check persistent objects continuation,
            used.insert object)
      | .del object continuation => do
          let (continuation, used) ←
            nullarySafeShadowCode? fuel used continuation
          return (.del object continuation, used.insert object)
      | .fun _ _ impossible => nomatch impossible

/-- Lift the executable conservative policy through one declaration. -/
def nullarySafeShadowDecl? (fuel : Nat)
    (declaration : LCNF.Decl .impure) :
    Option (LCNF.Decl .impure) :=
  match declaration.value with
  | .extern _ => some declaration
  | .code code => do
      let (code, _) ← nullarySafeShadowCode? fuel {} code
      return { declaration with value := .code code }

/-- Lift the executable conservative policy through declaration lists. -/
def nullarySafeShadowDecls? (fuel : Nat) :
    List (LCNF.Decl .impure) →
      Option (List (LCNF.Decl .impure))
  | [] => some []
  | declaration :: rest => do
      return (← nullarySafeShadowDecl? fuel declaration) ::
        (← nullarySafeShadowDecls? fuel rest)

/-- Whole-program conservative checker. A successful result is intended to
serve as the auditable compiler-side certificate consumed by the semantic
correctness endpoint. -/
def nullarySafeShadowProgram? (fuel : Nat)
    (program : ImpureProgram) : Option ImpureProgram := do
  let declarations ←
    nullarySafeShadowDecls? fuel program.decls.toList
  return { decls := declarations.toArray }

/-- State-indexed semantic kernel for an eliminable value whose evaluation is
successful, returns an ordinary value, and leaves the runtime unchanged.  This
is the exact subset compatible with FIR's current raw-observation equality. -/
def RuntimeNeutralAt (state : MachineState)
    (declaration : LCNF.LetDecl .impure) : Prop :=
  ∃ value, evalLetValue state declaration =
    .ok (state.runtime, .value value)

/-- Semantic form of the backwards liveness obligation: extending the current
environment with the eliminated result does not affect the continuation. -/
def BindingIrrelevantAt (externals : ExternalSpec) (state : MachineState)
    (declaration : LCNF.LetDecl .impure) (value : Value)
    (continuation : LCNF.Code .impure) : Prop :=
  ∀ observation,
    EvaluatesState externals
        { state with
          env := bind state.env declaration.fvarId value
          control := .code continuation } observation ↔
      EvaluatesState externals
        { state with control := .code continuation } observation

/-- A runtime-neutral let evaluates by one internal step to its continuation
with the result added to the environment. -/
theorem evalLetValue_control_eq
    (state : MachineState) (control : Control)
    (declaration : LCNF.LetDecl .impure) :
    evalLetValue { state with control } declaration =
      evalLetValue state declaration := by
  cases declaration with
  | mk fvarId binderName type value =>
      cases value <;> rfl

theorem coreStep_runtimeNeutralLet
    (evaluated : evalLetValue state declaration =
      .ok (state.runtime, .value value)) :
    coreStep
        { state with control := .code (.let declaration continuation) } =
      .next
        { state with
          env := bind state.env declaration.fvarId value
          control := .code continuation } := by
  simp only [coreStep]
  rw [evalLetValue_control_eq, evaluated]

/-- First reusable elimination theorem.  The source takes one internal step,
the target stutters, and backwards liveness discharges the resulting extra
environment binding. -/
theorem eliminateLet_correct_of_runtimeNeutral
    (evaluated : evalLetValue state declaration =
      .ok (state.runtime, .value value))
    (irrelevant : BindingIrrelevantAt externals state declaration value
      continuation) :
    EvaluatesState externals
        { state with control := .code (.let declaration continuation) }
        observation ↔
      EvaluatesState externals
        { state with control := .code continuation } observation := by
  rw [evaluatesState_internal_iff
    (coreStep_runtimeNeutralLet (state := state) (declaration := declaration)
      (continuation := continuation) evaluated)]
  exact irrelevant observation

/-- Local form of the terminal-state characterization. -/
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

/-- An unreachable continuation observes neither the current lexical
environment nor the value of the eliminated binding. -/
theorem bindingIrrelevantAt_unreach
    (state : MachineState) (declaration : LCNF.LetDecl .impure)
    (value : Value) (type : Expr) :
    BindingIrrelevantAt externals state declaration value (.unreach type) := by
  intro observation
  let result := observe state (.fault .unreachable)
  have leftDone :
      coreStep
          { state with
            env := bind state.env declaration.fvarId value
            control := .code (.unreach type) } = .done result := by
    simp [coreStep, fail, result, observe]
  have rightDone :
      coreStep { state with control := .code (.unreach type) } =
        .done result := by
    simp [coreStep, fail, result, observe]
  rw [evaluatesState_done_iff leftDone, evaluatesState_done_iff rightDone]

/-- Executing an erased value is runtime-neutral in every state. -/
theorem erased_runtimeNeutralAt
    (state : MachineState) (fvarId : FVarId) (binderName : Name)
    (type : Expr) :
    RuntimeNeutralAt state
      { fvarId, binderName, type, value := .erased } := by
  exact ⟨.erased, rfl⟩

def erasedLetDecl (fvarId : FVarId) (binderName : Name) (type : Expr) :
    LCNF.LetDecl .impure :=
  { fvarId, binderName, type, value := .erased }

/-- Concrete kernel regression: an unused erased binding before `unreach` may
be deleted, with the source's administrative step matched by target stutter. -/
theorem eliminate_erased_before_unreach
    (state : MachineState) (fvarId : FVarId) (binderName : Name)
    (valueType resultType : Expr) :
    EvaluatesState externals
        { state with control := .code (.let
          (erasedLetDecl fvarId binderName valueType)
          (.unreach resultType)) } observation ↔
      EvaluatesState externals
        { state with control := .code (.unreach resultType) } observation := by
  apply eliminateLet_correct_of_runtimeNeutral
    (value := .erased)
  · rfl
  · exact bindingIrrelevantAt_unreach state
      (erasedLetDecl fvarId binderName valueType)
      .erased resultType

/-! ## Reachable-observation evidence for the whole pass -/

/-- The empty address renaming is sufficient when neither observation exposes
a heap location. -/
def emptyAddressRenaming : AddressRenaming where
  forward := fun _ => none
  reverse := fun _ => none
  leftInverse := by simp
  rightInverse := by simp

theorem not_reachable_from_erased
    (reachable : Reachable heap [.erased] location) : False := by
  induction reachable with
  | root member => simp at member
  | child _ _ _ _ parentImpossible => exact parentImpossible

/-- `ObservationRel` already expresses the equivalence needed for deleting a
dead allocation: arbitrary heaps are related when the only observable result
is erased and there are no external events. -/
theorem observationRel_returned_erased_ignore_heap
    (leftHeap rightHeap : Heap) (world : Nat) :
    ObservationRel
      { outcome := .returned .erased
        heap := leftHeap
        world
        trace := #[] }
      { outcome := .returned .erased
        heap := rightHeap
        world
        trace := #[] } := by
  refine ⟨emptyAddressRenaming, .erased, rfl, .nil, ?_⟩
  constructor
  · intro location reachable
    exact (not_reachable_from_erased reachable).elim
  · intro location reachable
    exact (not_reachable_from_erased reachable).elim

end Fir.LeanIR.Passes.ElimDead
