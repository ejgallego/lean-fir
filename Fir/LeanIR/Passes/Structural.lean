import Fir.LeanIR.Passes.NonLockstep

namespace Fir.LeanIR.Passes.NonLockstep.Structural

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.NonLockstep

/-- Same-phase correctness restricted to entry arguments satisfying an
explicit phase invariant. This is the appropriate boundary for transformations
whose validity relies on runtime typing information. -/
def SamePhaseCorrectOn (semantics : PhaseSemantics phase)
    (before after : Program phase) (entries : Array Name)
    (admissible : Name → Array semantics.Value → Prop) : Prop :=
  ∀ entry, entry ∈ entries → ∀ args, admissible entry args → ∀ observation,
    semantics.Evaluates before entry args observation ↔
      semantics.Evaluates after entry args observation

theorem SamePhaseCorrect.on
    {phaseSemantics : PhaseSemantics phase}
    {admissible : Name → Array phaseSemantics.Value → Prop}
    (correct : SamePhaseCorrect phaseSemantics before after entries) :
    SamePhaseCorrectOn phaseSemantics before after entries admissible := by
  intro entry member args accepted observation
  exact correct entry member args observation

theorem samePhaseCorrect_of_all_admissible
    {phaseSemantics : PhaseSemantics phase}
    (correct : SamePhaseCorrectOn phaseSemantics before after entries
      (fun _ _ => True)) :
    SamePhaseCorrect phaseSemantics before after entries := by
  intro entry member args observation
  exact correct entry member args trivial observation

/-- Entry-state relatedness restricted by the same phase invariant used in
`SamePhaseCorrectOn`. -/
def InitialStatesRelatedOn
    (admissible : Name → Array Value → Prop)
    (relation : MachineState → MachineState → Prop)
    (before after : ImpureProgram) (entries : Array Name) : Prop :=
  ∀ entry, entry ∈ entries → ∀ args, admissible entry args →
    relation (initialState before entry args) (initialState after entry args)

theorem samePhaseCorrectOn_of_stuttering
    (bisimulation : StutteringBisimulation externals relation)
    (initial : InitialStatesRelatedOn admissible relation before after entries) :
    SamePhaseCorrectOn (Impure.semantics externals)
      before after entries admissible := by
  intro entry member args accepted observation
  exact bisimulation.evaluatesState_iff
    (initial entry member args accepted)

/-- Optional values related pointwise, used for declaration lookup. -/
inductive OptionalRel (relation : α → β → Prop) :
    Option α → Option β → Prop where
  | none : OptionalRel relation none none
  | some (related : relation left right) :
      OptionalRel relation (some left) (some right)

/-- Declaration values either contain related code or the same external
declaration metadata. -/
inductive DeclValueRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop) :
    LCNF.DeclValue .impure → LCNF.DeclValue .impure → Prop where
  | code (related : codeRel left right) :
      DeclValueRelated codeRel (.code left) (.code right)
  | extern (metadata : ExternAttrData) :
      DeclValueRelated codeRel (.extern metadata) (.extern metadata)

/-- Two top-level declarations have identical calling conventions and related
bodies. The pass may change code but not declaration identity or ABI. -/
structure DeclRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop)
    (left right : LCNF.Decl .impure) : Prop where
  name_eq : left.name = right.name
  levelParams_eq : left.levelParams = right.levelParams
  type_eq : left.type = right.type
  params_eq : left.params = right.params
  safe_eq : left.safe = right.safe
  value : DeclValueRelated codeRel left.value right.value
  recursive_eq : left.recursive = right.recursive
  inlineAttr_eq : left.inlineAttr? = right.inlineAttr?

/-- Ordered declaration groups related pointwise. This supports any number of
declarations and makes lookup alignment provable without assuming name
uniqueness a second time. -/
def ProgramRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop)
    (left right : ImpureProgram) : Prop :=
  ListRel (DeclRelated codeRel) left.decls.toList right.decls.toList

/-- Join declarations retain their binder and calling convention while their
bodies follow the same code relation as top-level declarations. -/
structure FunDeclRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop)
    (left right : LCNF.FunDecl .impure) : Prop where
  fvarId_eq : left.fvarId = right.fvarId
  binderName_eq : left.binderName = right.binderName
  params_eq : left.params = right.params
  type_eq : left.type = right.type
  value : codeRel left.value right.value

structure JoinEntryRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop)
    (left right : FVarId × LCNF.FunDecl .impure) : Prop where
  key_eq : left.1 = right.1
  declaration : FunDeclRelated codeRel left.2 right.2

def JoinEnvRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop)
    (left right : JoinEnv) : Prop :=
  ListRel (JoinEntryRelated codeRel) left right

/-- Saved bind continuations use related code and related captured join-point
environments. Apply and cache frames are unchanged. -/
inductive FrameRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop) :
    Frame → Frame → Prop where
  | bind
      (continuation : codeRel leftContinuation rightContinuation)
      (joins : JoinEnvRelated codeRel leftJoins rightJoins) :
      FrameRelated codeRel
        (.bind fvarId leftContinuation env leftJoins)
        (.bind fvarId rightContinuation env rightJoins)
  | apply (args : Array Value) :
      FrameRelated codeRel (.apply args) (.apply args)
  | cache (name : Name) :
      FrameRelated codeRel (.cache name) (.cache name)

def FramesRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop)
    (left right : List Frame) : Prop :=
  ListRel (FrameRelated codeRel) left right

/-- Controls either carry related residual code or identical runtime data. -/
inductive ControlRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop) :
    Control → Control → Prop where
  | code (related : codeRel left right) :
      ControlRelated codeRel (.code left) (.code right)
  | yielded (value : Value) :
      ControlRelated codeRel (.yielded value) (.yielded value)
  | invokeName (name : Name) (args : Array Value) :
      ControlRelated codeRel (.invokeName name args) (.invokeName name args)
  | invokeValue (function : Value) (args : Array Value) :
      ControlRelated codeRel
        (.invokeValue function args) (.invokeValue function args)

/-- Program-aware structural machine relation. Runtime values and lexical
environments are still equal; every location that can store code is related. -/
structure MachineRelated
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop)
    (left right : MachineState) : Prop where
  programs : ProgramRelated codeRel left.program right.program
  runtime_eq : left.runtime = right.runtime
  env_eq : left.env = right.env
  joins : JoinEnvRelated codeRel left.joins right.joins
  frames : FramesRelated codeRel left.frames right.frames
  control : ControlRelated codeRel left.control right.control

/-- Refine the structural relation with a semantic invariant, such as runtime
typing or case-discriminant validity. The invariant may mention both states and
must be preserved by the eventual simulation proof. -/
structure MachineRelatedWith
    (codeRel : LCNF.Code .impure → LCNF.Code .impure → Prop)
    (invariant : MachineState → MachineState → Prop)
    (left right : MachineState) : Prop where
  structural : MachineRelated codeRel left right
  invariant : invariant left right

/-- An entry admissibility predicate establishes the semantic invariant on the
two initial states. -/
def InitialInvariantOn
    (admissible : Name → Array Value → Prop)
    (invariant : MachineState → MachineState → Prop)
    (before after : ImpureProgram) (entries : Array Name) : Prop :=
  ∀ entry, entry ∈ entries → ∀ args, admissible entry args →
    invariant (initialState before entry args) (initialState after entry args)

theorem initialState_related
    (programs : ProgramRelated codeRel before after) :
    MachineRelated codeRel
      (initialState before entry args) (initialState after entry args) := {
  programs := programs
  runtime_eq := rfl
  env_eq := rfl
  joins := .nil
  frames := .nil
  control := .invokeName entry args
}

theorem initialStatesRelated
    (programs : ProgramRelated codeRel before after) :
    InitialStatesRelated (MachineRelated codeRel) before after entries := by
  intro entry member args
  exact initialState_related programs

theorem initialStatesRelatedOn
    (programs : ProgramRelated codeRel before after) :
    InitialStatesRelatedOn admissible (MachineRelated codeRel)
      before after entries := by
  intro entry member args accepted
  exact initialState_related programs

theorem refinedInitialStatesRelatedOn
    (programs : ProgramRelated codeRel before after)
    (initialInvariant :
      InitialInvariantOn admissible invariant before after entries) :
    InitialStatesRelatedOn admissible (MachineRelatedWith codeRel invariant)
      before after entries := by
  intro entry member args accepted
  exact {
    structural := initialState_related programs
    invariant := initialInvariant entry member args accepted
  }

/-- Once the structural relation is proved to be a bisimulation, declaration
entry and admissible-argument plumbing are discharged generically. -/
theorem samePhaseCorrectOn_of_machine_bisimulation
    (programs : ProgramRelated codeRel before after)
    (bisimulation :
      StutteringBisimulation externals (MachineRelated codeRel)) :
    SamePhaseCorrectOn (Impure.semantics externals)
      before after entries admissible :=
  samePhaseCorrectOn_of_stuttering bisimulation
    (initialStatesRelatedOn programs)

/-- Typed/open transformations use this boundary: admissible entry arguments
establish an invariant, and the non-lockstep proof preserves that invariant. -/
theorem samePhaseCorrectOn_of_refined_machine_bisimulation
    (programs : ProgramRelated codeRel before after)
    (initialInvariant :
      InitialInvariantOn admissible invariant before after entries)
    (bisimulation : StutteringBisimulation externals
      (MachineRelatedWith codeRel invariant)) :
    SamePhaseCorrectOn (Impure.semantics externals)
      before after entries admissible :=
  samePhaseCorrectOn_of_stuttering bisimulation
    (refinedInitialStatesRelatedOn programs initialInvariant)

theorem samePhaseCorrect_of_machine_bisimulation
    (programs : ProgramRelated codeRel before after)
    (bisimulation :
      StutteringBisimulation externals (MachineRelated codeRel)) :
    SamePhaseCorrect (Impure.semantics externals) before after entries :=
  samePhaseCorrect_of_stuttering bisimulation
    (initialStatesRelated programs)

theorem decl_update_code_related
    {declaration : LCNF.Decl .impure}
    (related : codeRel leftCode rightCode) :
    DeclRelated codeRel
      { declaration with value := .code leftCode }
      { declaration with value := .code rightCode } := {
  name_eq := rfl
  levelParams_eq := rfl
  type_eq := rfl
  params_eq := rfl
  safe_eq := rfl
  value := .code related
  recursive_eq := rfl
  inlineAttr_eq := rfl
}

/-- Small regression showing that the program relation is genuinely
multi-declaration rather than a wrapper specialized to the first fixture. -/
theorem two_code_declarations_related
    {firstDeclaration secondDeclaration : LCNF.Decl .impure}
    (first : codeRel firstLeft firstRight)
    (second : codeRel secondLeft secondRight) :
    ProgramRelated codeRel
      { decls := #[
          { firstDeclaration with value := .code firstLeft },
          { secondDeclaration with value := .code secondLeft }] }
      { decls := #[
          { firstDeclaration with value := .code firstRight },
          { secondDeclaration with value := .code secondRight }] } := by
  exact .cons (decl_update_code_related first)
    (.cons (decl_update_code_related second) .nil)

theorem findDeclList_related
    (related : ListRel (DeclRelated codeRel) left right) :
    OptionalRel (DeclRelated codeRel)
      (left.find? (fun declaration => declaration.name == name))
      (right.find? (fun declaration => declaration.name == name)) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      rename_i leftHead rightHead leftTail rightTail
      have predicateEq :
          (leftHead.name == name) = (rightHead.name == name) := by
        rw [head.name_eq]
      simp only [List.find?_cons]
      rw [predicateEq]
      cases rightHead.name == name with
      | false => exact ih
      | true => exact .some head

/-- Pointwise-related programs return related declarations for every name. -/
theorem ProgramRelated.findDecl?
    (related : ProgramRelated codeRel left right) (name : Name) :
    OptionalRel (DeclRelated codeRel)
      (left.findDecl? name) (right.findDecl? name) := by
  simpa only [Program.findDecl?, ← Array.find?_toList] using
    findDeclList_related (name := name) related

end Fir.LeanIR.Passes.NonLockstep.Structural
