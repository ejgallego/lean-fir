import Fir.LeanIR.PassCorrectness
import Lean.Compiler.LCNF.AlphaEqv
import Std.Tactic.Do

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.ImpureHygiene

/-- Lean's right-to-left free-variable lookup, exposed as a proposition. -/
def FVarRelated (rho : FVarIdMap FVarId) (left right : FVarId) : Prop :=
  (LCNF.AlphaEqv.eqvFVar left right).run rho = true

/-- Every variable in a syntactic scope has a runtime value. -/
def EnvCovers (scope : List FVarId) (env : Env) : Prop :=
  ∀ fvarId, scope.contains fvarId = true → ∃ value, lookup env fvarId = some value

/--
Two runtime environments agree on every alpha-related pair in their current
syntactic scopes. Values, unlike identifiers, are unchanged by alpha-renaming.
-/
def EnvsAgree (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) (left right : Env) : Prop :=
  ∀ leftId, leftScope.contains leftId = true →
    ∀ rightId, rightScope.contains rightId = true →
      FVarRelated rho leftId rightId →
        ∃ value, lookup left leftId = some value ∧ lookup right rightId = some value

def ArgRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    (left right : LCNF.Arg .impure) : Prop :=
  argScoped leftScope left = true ∧
    argScoped rightScope right = true ∧
    (LCNF.AlphaEqv.eqvArg left right).run rho = true

def ArgsRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    (left right : Array (LCNF.Arg .impure)) : Prop :=
  ListRel (ArgRelated rho leftScope rightScope) left.toList right.toList

private theorem listRel_length_eq
    (related : ListRel relation left right) : left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem subarray_toList_eq_nil_of_next?_eq_none
    {stream : Subarray α} (next : Std.Stream.next? stream = none) :
    stream.toList = [] := by
  simp only [Std.Stream.next?] at next
  split at next
  · contradiction
  · apply List.eq_nil_of_length_eq_zero
    rw [Subarray.length_toList, Subarray.size_eq]
    omega

private theorem subarray_toList_eq_cons_of_next?_eq_some
    {stream rest : Subarray α} {head : α}
    (next : Std.Stream.next? stream = some (head, rest)) :
    stream.toList = head :: rest.toList := by
  simp only [Std.Stream.next?] at next
  split at next
  · rename_i inBounds
    change stream.internalRepresentation.start < stream.internalRepresentation.stop at inBounds
    have arrayBound := stream.stop_le_array_size
    change stream.internalRepresentation.stop ≤ stream.internalRepresentation.array.size at arrayBound
    simp only [Option.some.injEq, Prod.mk.injEq] at next
    rcases next with ⟨rfl, rfl⟩
    rw [Subarray.toList_eq_drop_take]
    rw [Subarray.toList_eq_drop_take]
    simp only [Subarray.array, Subarray.start, Subarray.stop]
    rw [List.drop_eq_getElem_cons]
    · rw [List.getElem_take, Array.getElem_toList]
    · simp only [List.length_take, Array.length_toList]
      omega
  · contradiction

open Std.Do in
set_option mvcgen.warning false in
/-- Lean's executable parallel-array checker accepts every pointwise-related argument array. -/
theorem eqvArgs_true_of_related
    (related : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
    (LCNF.AlphaEqv.eqvArgs leftArgs rightArgs).run rho = true := by
  have sizes : leftArgs.size = rightArgs.size := by
    simpa using listRel_length_eq related
  generalize h : (LCNF.AlphaEqv.eqvArgs leftArgs rightArgs).run rho = result
  apply ReaderM.of_wp_run_eq h
  simp only [LCNF.AlphaEqv.eqvArgs, sizes, ↓reduceIte, WP.bind, SPred.entails_nil,
    SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 => Invariant.withEarlyReturnNewDo
      (fun cursor stream current =>
        ⌜current = rho ∧
          ListRel (ArgRelated rho leftScope rightScope) cursor.suffix stream.toList⌝)
      (fun _ _ _ => ⌜False⌝)
  next _ _ _ _ state streamEnd _ invariant =>
    rcases invariant with ⟨_, _, relatedSuffix⟩ | returned
    · rw [subarray_toList_eq_nil_of_next?_eq_none streamEnd] at relatedSuffix
      cases relatedSuffix
    · simp_all
  next _ leftArg _ _ state rightArg rest streamNext current invariant =>
    rcases invariant with ⟨_, currentEq, relatedSuffix⟩ | returned
    · subst current
      rw [subarray_toList_eq_cons_of_next?_eq_some streamNext] at relatedSuffix
      cases relatedSuffix with
      | cons headRelated tailRelated =>
          rcases headRelated with ⟨_, _, check⟩
          cases leftArg with
          | erased =>
              cases rightArg with
              | erased => simp_all [LCNF.AlphaEqv.eqvArg]
              | fvar _ => simp [LCNF.AlphaEqv.eqvArg] at check
              | type _ impossible => nomatch impossible
          | fvar leftId =>
              cases rightArg with
              | erased => simp [LCNF.AlphaEqv.eqvArg] at check
              | fvar rightId =>
                  change (leftId == (rho.get? rightId).getD rightId) = true at check
                  simp [LCNF.AlphaEqv.eqvArg, LCNF.AlphaEqv.eqvFVar, check,
                    tailRelated]
              | type _ impossible => nomatch impossible
          | type _ impossible => nomatch impossible
    · simp_all
  next =>
    refine Or.inl ⟨True.intro, True.intro, ?_⟩
    change ListRel (ArgRelated rho leftScope rightScope)
      leftArgs.toList rightArgs.toList at related
    simpa [Std.toStream] using related
  next => simp_all

def ScopedFVarRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) (left right : FVarId) : Prop :=
  leftScope.contains left = true ∧
    rightScope.contains right = true ∧
    FVarRelated rho left right

/--
The semantic fragment of impure `LetValue` alpha-equivalence. Constructor
metadata that affects the interpreter is deliberately required to be equal;
the remaining proof obligation is to derive this relation from Lean's
executable `LCNF.AlphaEqv.eqvLetValue` checker.
-/
inductive LetValueRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) :
    LCNF.LetValue .impure → LCNF.LetValue .impure → Prop where
  | lit (value : LCNF.LitValue) : LetValueRelated rho leftScope rightScope (.lit value) (.lit value)
  | erased : LetValueRelated rho leftScope rightScope .erased .erased
  | fvar (related : ScopedFVarRelated rho leftScope rightScope leftFn rightFn)
      (args : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
      LetValueRelated rho leftScope rightScope (.fvar leftFn leftArgs) (.fvar rightFn rightArgs)
  | ctor (args : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
      LetValueRelated rho leftScope rightScope (.ctor info leftArgs) (.ctor info rightArgs)
  | oproj (related : ScopedFVarRelated rho leftScope rightScope leftVar rightVar) :
      LetValueRelated rho leftScope rightScope (.oproj index leftVar) (.oproj index rightVar)
  | uproj (related : ScopedFVarRelated rho leftScope rightScope leftVar rightVar) :
      LetValueRelated rho leftScope rightScope (.uproj index leftVar) (.uproj index rightVar)
  | sproj (related : ScopedFVarRelated rho leftScope rightScope leftVar rightVar) :
      LetValueRelated rho leftScope rightScope
        (.sproj width offset leftVar) (.sproj width offset rightVar)
  | fap (args : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
      LetValueRelated rho leftScope rightScope (.fap name leftArgs) (.fap name rightArgs)
  | pap (args : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
      LetValueRelated rho leftScope rightScope (.pap name leftArgs) (.pap name rightArgs)
  | reset (related : ScopedFVarRelated rho leftScope rightScope leftVar rightVar) :
      LetValueRelated rho leftScope rightScope (.reset count leftVar) (.reset count rightVar)
  | reuse (related : ScopedFVarRelated rho leftScope rightScope leftVar rightVar)
      (args : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
      LetValueRelated rho leftScope rightScope
        (.reuse leftVar info updateHeader leftArgs) (.reuse rightVar info updateHeader rightArgs)
  | box (related : ScopedFVarRelated rho leftScope rightScope leftVar rightVar) :
      LetValueRelated rho leftScope rightScope (.box type leftVar) (.box type rightVar)
  | unbox (related : ScopedFVarRelated rho leftScope rightScope leftVar rightVar) :
      LetValueRelated rho leftScope rightScope (.unbox leftVar) (.unbox rightVar)
  | isShared (related : ScopedFVarRelated rho leftScope rightScope leftVar rightVar) :
      LetValueRelated rho leftScope rightScope (.isShared leftVar) (.isShared rightVar)

/-- Declaration data inspected while evaluating a `let` value. -/
structure LetDeclValueRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    (left right : LCNF.LetDecl .impure) : Prop where
  type_eq : left.type = right.type
  value : LetValueRelated rho leftScope rightScope left.value right.value

/-- A fresh binder does not reuse the runtime lookup name of an older scope entry. -/
def FreshForScope (fvarId : FVarId) (scope : List FVarId) : Prop :=
  ∀ oldId, scope.contains oldId = true → fvarId.name ≠ oldId.name

theorem lookup_bind_of_name_ne
    (different : binder.name ≠ fvarId.name) :
    lookup (bind env binder value) fvarId = lookup env fvarId := by
  cases binder with
  | mk binderName =>
      cases fvarId with
      | mk fvarName =>
          simp [Fir.LeanIR.Impure.bind, Fir.LeanIR.Impure.lookup, different]

theorem envsAgree_refl_of_covers
    (covers : EnvCovers scope env) :
    EnvsAgree {} scope scope env env := by
  intro leftId leftScoped rightId rightScoped related
  have ids : leftId = rightId := by
    change (leftId == rightId) = true at related
    cases leftId with
    | mk leftName =>
        cases rightId with
        | mk rightName =>
            congr
            exact eq_of_beq related
  subst rightId
  obtain ⟨value, found⟩ := covers leftId leftScoped
  exact ⟨value, found, found⟩

theorem lookupValue_eq_of_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (leftScoped : leftScope.contains leftId = true)
    (rightScoped : rightScope.contains rightId = true)
    (related : FVarRelated rho leftId rightId) :
    lookupValue leftEnv leftId = lookupValue rightEnv rightId := by
  obtain ⟨value, leftFound, rightFound⟩ :=
    agree leftId leftScoped rightId rightScoped related
  simp [lookupValue, leftFound, rightFound]

theorem lookupValue_eq_of_scoped_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : ScopedFVarRelated rho leftScope rightScope leftId rightId) :
    lookupValue leftEnv leftId = lookupValue rightEnv rightId := by
  exact lookupValue_eq_of_related agree related.1 related.2.1 related.2.2

/--
Extend related environments with one equal runtime value. The `classify`
hypothesis is the exact syntactic obligation later discharged from
`withFVar`, alpha-equivalence, and declaration-wide hygiene: every related pair
in the extended scopes is either the new binder pair or an old related pair.
-/
theorem envsAgree_bind_of_classified
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (leftFresh : FreshForScope leftId leftScope)
    (rightFresh : FreshForScope rightId rightScope)
    (classify :
      ∀ candidateLeft, (leftId :: leftScope).contains candidateLeft = true →
        ∀ candidateRight, (rightId :: rightScope).contains candidateRight = true →
          FVarRelated extended candidateLeft candidateRight →
            (candidateLeft = leftId ∧ candidateRight = rightId) ∨
              (leftScope.contains candidateLeft = true ∧
                rightScope.contains candidateRight = true ∧
                FVarRelated rho candidateLeft candidateRight)) :
    EnvsAgree extended (leftId :: leftScope) (rightId :: rightScope)
      (bind leftEnv leftId value) (bind rightEnv rightId value) := by
  intro candidateLeft candidateLeftScoped candidateRight candidateRightScoped related
  rcases classify candidateLeft candidateLeftScoped candidateRight candidateRightScoped related with
    newPair | oldPair
  · rcases newPair with ⟨rfl, rfl⟩
    exact ⟨value, lookup_bind_self _ _ _, lookup_bind_self _ _ _⟩
  · rcases oldPair with ⟨leftScoped, rightScoped, oldRelated⟩
    obtain ⟨oldValue, leftFound, rightFound⟩ :=
      agree candidateLeft leftScoped candidateRight rightScoped oldRelated
    refine ⟨oldValue, ?_, ?_⟩
    · rw [lookup_bind_of_name_ne (leftFresh candidateLeft leftScoped)]
      exact leftFound
    · rw [lookup_bind_of_name_ne (rightFresh candidateRight rightScoped)]
      exact rightFound

theorem evalArg_eq_of_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : ArgRelated rho leftScope rightScope leftArg rightArg) :
    evalArg leftEnv leftArg = evalArg rightEnv rightArg := by
  rcases related with ⟨leftScoped, rightScoped, related⟩
  cases leftArg with
  | erased =>
      cases rightArg with
      | erased => rfl
      | fvar _ => simp [LCNF.AlphaEqv.eqvArg] at related
      | type _ impossible => nomatch impossible
  | fvar leftId =>
      cases rightArg with
      | erased => simp [LCNF.AlphaEqv.eqvArg] at related
      | fvar rightId =>
          have values := lookupValue_eq_of_related agree leftScoped rightScoped related
          change lookupValue leftEnv leftId = lookupValue rightEnv rightId
          exact values
      | type _ impossible => nomatch impossible
  | type _ impossible => nomatch impossible

theorem evalArgList_eq_of_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : ListRel (ArgRelated rho leftScope rightScope) left right) :
    left.mapM (evalArg leftEnv) = right.mapM (evalArg rightEnv) := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      simp [evalArg_eq_of_related agree head, ih]

theorem evalArgs_eq_of_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
    evalArgs leftEnv leftArgs = evalArgs rightEnv rightArgs := by
  simp only [evalArgs, Array.mapM_eq_mapM_toList]
  rw [evalArgList_eq_of_related agree related]

/--
Evaluation of the semantic `LetValue` fragment is invariant under
alpha-renaming. Both executions share the program and runtime state; only the
free-variable environment and related declaration syntax differ.
-/
theorem evalLetValue_eq_of_related
    (state : MachineState)
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : LetDeclValueRelated rho leftScope rightScope leftDecl rightDecl) :
    evalLetValue ({ state with env := leftEnv }) leftDecl =
      evalLetValue ({ state with env := rightEnv }) rightDecl := by
  cases leftDecl
  cases rightDecl
  rcases related with ⟨typeEq, valueRelated⟩
  cases typeEq
  cases valueRelated with
  | lit value => rfl
  | erased => rfl
  | fvar varRelated argsRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]
      rw [evalArgs_eq_of_related agree argsRelated]
  | ctor argsRelated =>
      simp only [evalLetValue]
      rw [evalArgs_eq_of_related agree argsRelated]
  | oproj varRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]
  | uproj varRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]
  | sproj varRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]
  | fap argsRelated =>
      simp only [evalLetValue]
      rw [evalArgs_eq_of_related agree argsRelated]
  | pap argsRelated =>
      simp only [evalLetValue]
      rw [evalArgs_eq_of_related agree argsRelated]
  | reset varRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]
  | reuse varRelated argsRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]
      rw [evalArgs_eq_of_related agree argsRelated]
  | box varRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]
  | unbox varRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]
  | isShared varRelated =>
      simp only [evalLetValue]
      rw [lookupValue_eq_of_scoped_related agree varRelated]

end Fir.LeanIR.Passes.AlphaEqv
