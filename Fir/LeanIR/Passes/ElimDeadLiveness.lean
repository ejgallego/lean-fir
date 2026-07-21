import Fir.LeanIR.Passes.ElimDead
import Std.Data.HashSet.Lemmas

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.AlphaEqv

/-!
The proof-facing liveness layer for `elimDeadVars`.

The compiler's `UsedLocals` set is an over-approximation of the variables a
transformed suffix may inspect.  `EnvsAgreeOn` turns that syntactic set into a
semantic invariant: two runtime environments may differ elsewhere, but every
lookup recorded by the backwards traversal agrees.
-/

private theorem fvarId_beq_iff_eq {left right : FVarId} :
    left == right ↔ left = right := by
  constructor
  · intro equal
    cases left with
    | mk leftName =>
        cases right with
        | mk rightName =>
            apply congrArg FVarId.mk
            change leftName == rightName at equal
            exact Name.beq_iff_eq.mp equal
  · intro equal
    subst right
    cases left with
    | mk name =>
        change name == name
        exact Name.beq_iff_eq.mpr rfl

/-- Lean 4.32 derives `BEq` and `Hashable` for `FVarId` but does not ship the
lawfulness instance required by the extensional `HashSet` lemmas. -/
instance fvarIdLawfulBEq : LawfulBEq FVarId where
  eq_of_beq := fvarId_beq_iff_eq.mp
  rfl := fvarId_beq_iff_eq.mpr rfl

def UsedSubset (left right : UsedLocals) : Prop :=
  ∀ fvarId, left.contains fvarId = true → right.contains fvarId = true

@[refl] theorem UsedSubset.refl (used : UsedLocals) : UsedSubset used used := by
  intro fvarId member
  exact member

theorem UsedSubset.trans
    (first : UsedSubset left middle) (second : UsedSubset middle right) :
    UsedSubset left right := by
  intro fvarId member
  exact second fvarId (first fvarId member)

theorem usedSubset_insert (used : UsedLocals) (inserted : FVarId) :
    UsedSubset used (used.insert inserted) := by
  intro fvarId member
  simp only [Std.HashSet.contains_insert, Bool.or_eq_true]
  exact Or.inr member

theorem collectArg_subset (used : UsedLocals) (argument : LCNF.Arg pu) :
    UsedSubset used (collectArg used argument) := by
  cases argument with
  | erased => exact .refl used
  | fvar fvarId => exact usedSubset_insert used fvarId
  | type _ impossible => exact .refl used

theorem collectArgList_subset
    (used : UsedLocals) (arguments : List (LCNF.Arg pu)) :
    UsedSubset used (collectArgList used arguments) := by
  induction arguments generalizing used with
  | nil => exact .refl used
  | cons argument rest ih =>
      exact (collectArg_subset used argument).trans
        (ih (collectArg used argument))

theorem collectArgs_subset
    (used : UsedLocals) (arguments : Array (LCNF.Arg pu)) :
    UsedSubset used (collectArgs used arguments) :=
  collectArgList_subset used arguments.toList

def ArgCovered (used : UsedLocals) : LCNF.Arg .impure → Prop
  | .erased => True
  | .fvar fvarId => used.contains fvarId = true
  | .type _ impossible => nomatch impossible

def ArgsCovered (used : UsedLocals)
    (arguments : Array (LCNF.Arg .impure)) : Prop :=
  ∀ argument, argument ∈ arguments.toList → ArgCovered used argument

theorem ArgCovered.mono
    (subset : UsedSubset left right)
    (covered : ArgCovered left argument) : ArgCovered right argument := by
  cases argument with
  | erased => trivial
  | fvar fvarId => exact subset fvarId covered
  | type _ impossible => nomatch impossible

theorem argCovered_collectArg
    (used : UsedLocals) (argument : LCNF.Arg .impure) :
    ArgCovered (collectArg used argument) argument := by
  cases argument with
  | erased => trivial
  | fvar fvarId =>
      simp [collectArg, ArgCovered, Std.HashSet.contains_insert]
  | type _ impossible => nomatch impossible

theorem collectArgList_covers_member
    (member : argument ∈ arguments) :
    ArgCovered (collectArgList used arguments) argument := by
  induction arguments generalizing used with
  | nil => simp at member
  | cons head rest ih =>
      simp only [List.mem_cons] at member
      simp only [collectArgList]
      cases member with
      | inl same =>
          subst argument
          exact (argCovered_collectArg used head).mono
            (collectArgList_subset (collectArg used head) rest)
      | inr tail => exact ih (used := collectArg used head) tail

theorem collectArgs_covers
    (used : UsedLocals) (arguments : Array (LCNF.Arg .impure)) :
    ArgsCovered (collectArgs used arguments) arguments := by
  intro argument member
  exact collectArgList_covers_member member

def LetValueCovered (used : UsedLocals) : LCNF.LetValue .impure → Prop
  | .lit _ | .erased => True
  | .fvar fvarId arguments =>
      used.contains fvarId = true ∧ ArgsCovered used arguments
  | .ctor _ arguments | .fap _ arguments | .pap _ arguments =>
      ArgsCovered used arguments
  | .oproj _ fvarId | .uproj _ fvarId | .sproj _ _ fvarId
  | .reset _ fvarId | .box _ fvarId | .unbox fvarId | .isShared fvarId =>
      used.contains fvarId = true
  | .reuse fvarId _ _ arguments =>
      used.contains fvarId = true ∧ ArgsCovered used arguments
  | .proj _ _ _ impossible | .const _ _ _ impossible => nomatch impossible

theorem ArgsCovered.mono
    (subset : UsedSubset left right)
    (covered : ArgsCovered left arguments) : ArgsCovered right arguments := by
  intro argument member
  exact (covered argument member).mono subset

theorem LetValueCovered.mono
    (subset : UsedSubset left right)
    (covered : LetValueCovered left value) : LetValueCovered right value := by
  cases value with
  | lit _ | erased => trivial
  | fvar fvarId arguments =>
      exact ⟨subset fvarId covered.1, ArgsCovered.mono subset covered.2⟩
  | ctor info arguments => exact ArgsCovered.mono subset covered
  | oproj index fvarId | uproj index fvarId | sproj index offset fvarId
  | reset index fvarId | box type fvarId | unbox fvarId | isShared fvarId =>
      exact subset fvarId covered
  | fap name arguments | pap name arguments =>
      exact ArgsCovered.mono subset covered
  | reuse fvarId info updateHeader arguments =>
      exact ⟨subset fvarId covered.1, ArgsCovered.mono subset covered.2⟩
  | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible

theorem collectLetValue_covers
    (used : UsedLocals) (value : LCNF.LetValue .impure) :
    LetValueCovered (collectLetValue used value) value := by
  cases value with
  | lit _ | erased => trivial
  | fvar fvarId arguments =>
      have subset := collectArgs_subset (used.insert fvarId) arguments
      exact ⟨subset fvarId (by simp), collectArgs_covers _ _⟩
  | ctor info arguments | fap name arguments | pap name arguments =>
      exact collectArgs_covers used arguments
  | oproj index fvarId | uproj index fvarId | sproj index offset fvarId
  | reset index fvarId | box type fvarId | unbox fvarId | isShared fvarId =>
      simp [collectLetValue, LetValueCovered, Std.HashSet.contains_insert]
  | reuse fvarId info updateHeader arguments =>
      have subset := collectArgs_subset (used.insert fvarId) arguments
      exact ⟨subset fvarId (by simp), collectArgs_covers _ _⟩
  | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible

def EnvsAgreeOn (used : UsedLocals) (left right : Env) : Prop :=
  ∀ fvarId, used.contains fvarId = true →
    lookupValue left fvarId = lookupValue right fvarId

@[refl] theorem EnvsAgreeOn.refl (used : UsedLocals) (env : Env) :
    EnvsAgreeOn used env env := by
  intro fvarId member
  rfl

theorem EnvsAgreeOn.symm (agree : EnvsAgreeOn used left right) :
    EnvsAgreeOn used right left := by
  intro fvarId member
  exact (agree fvarId member).symm

theorem EnvsAgreeOn.mono
    (subset : UsedSubset smaller larger)
    (agree : EnvsAgreeOn larger left right) :
    EnvsAgreeOn smaller left right := by
  intro fvarId member
  exact agree fvarId (subset fvarId member)

theorem fvarId_name_ne_of_contains_of_absent
    (used : UsedLocals) (candidate binder : FVarId)
    (member : used.contains candidate = true)
    (absent : used.contains binder = false) :
    binder.name ≠ candidate.name := by
  intro namesEqual
  have idsEqual : binder = candidate := by
    cases binder with
    | mk binderName =>
        cases candidate with
        | mk candidateName => simp_all
  subst candidate
  simp_all

theorem lookupValue_bind_of_name_ne
    (env : Env) (binder fvarId : FVarId) (value : Value)
    (different : binder.name ≠ fvarId.name) :
    lookupValue (bind env binder value) fvarId = lookupValue env fvarId := by
  unfold lookupValue
  rw [lookup_bind_of_name_ne different]

theorem EnvsAgreeOn.bindLeft_of_absent
    (agree : EnvsAgreeOn used left right)
    (absent : used.contains binder = false) :
    EnvsAgreeOn used (bind left binder value) right := by
  intro fvarId member
  rw [lookupValue_bind_of_name_ne left binder fvarId value
    (fvarId_name_ne_of_contains_of_absent used fvarId binder member absent)]
  exact agree fvarId member

theorem EnvsAgreeOn.bindRight_of_absent
    (agree : EnvsAgreeOn used left right)
    (absent : used.contains binder = false) :
    EnvsAgreeOn used left (bind right binder value) :=
  (agree.symm.bindLeft_of_absent absent).symm

theorem evalArg_eq_of_covered
    (agree : EnvsAgreeOn used leftEnv rightEnv)
    (covered : ArgCovered used argument) :
    evalArg leftEnv argument = evalArg rightEnv argument := by
  cases argument with
  | erased => rfl
  | fvar fvarId =>
      change lookupValue leftEnv fvarId = lookupValue rightEnv fvarId
      exact agree fvarId covered
  | type _ impossible => nomatch impossible

theorem evalArgList_eq_of_covered
    (arguments : List (LCNF.Arg .impure))
    (agree : EnvsAgreeOn used leftEnv rightEnv)
    (covered : ∀ argument, argument ∈ arguments → ArgCovered used argument) :
    arguments.mapM (evalArg leftEnv) = arguments.mapM (evalArg rightEnv) := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      simp only [List.mapM_cons]
      rw [evalArg_eq_of_covered agree
        (covered argument List.mem_cons_self)]
      rw [ih (fun item member =>
        covered item (List.mem_cons_of_mem argument member))]

theorem evalArgs_eq_of_covered
    (agree : EnvsAgreeOn used leftEnv rightEnv)
    (covered : ArgsCovered used arguments) :
    evalArgs leftEnv arguments = evalArgs rightEnv arguments := by
  simp only [evalArgs, Array.mapM_eq_mapM_toList]
  exact congrArg (fun result => List.toArray <$> result)
    (evalArgList_eq_of_covered arguments.toList agree covered)

/-- Evaluation of an impure let value depends only on the variables recorded
by its liveness coverage.  Program and runtime are shared; environments may
differ arbitrarily outside the used set. -/
theorem evalLetValue_eq_of_covered
    (state : MachineState)
    (agree : EnvsAgreeOn used leftEnv rightEnv)
    (covered : LetValueCovered used declaration.value) :
    evalLetValue { state with env := leftEnv } declaration =
      evalLetValue { state with env := rightEnv } declaration := by
  cases declaration with
  | mk fvarId binderName type value =>
      cases value with
      | lit value | erased => rfl
      | fvar function arguments =>
          simp only [evalLetValue]
          rw [agree function covered.1]
          rw [evalArgs_eq_of_covered agree covered.2]
      | ctor info arguments =>
          simp only [evalLetValue]
          rw [evalArgs_eq_of_covered agree covered]
      | oproj index object | uproj index object | sproj index offset object
      | reset index object | box type object | unbox object | isShared object =>
          simp only [evalLetValue]
          rw [agree object covered]
      | fap name arguments | pap name arguments =>
          simp only [evalLetValue]
          rw [evalArgs_eq_of_covered agree covered]
      | reuse token info updateHeader arguments =>
          simp only [evalLetValue]
          rw [agree token covered.1]
          rw [evalArgs_eq_of_covered agree covered.2]
      | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible

end Fir.LeanIR.Passes.ElimDead
