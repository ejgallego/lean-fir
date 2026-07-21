import Fir.LeanIR.Passes.SimpCase
import Fir.LeanIR.Passes.SimpCaseWellFormed
import Fir.LeanIR.Passes.SimpCaseCorrectness
import Fir.LeanIR.InterpreterExamples
import Lean.Elab.Command

namespace Fir.LeanIR.Passes.SimpCaseExamples

open Lean
open Lean.Elab.Command
open Lean.Compiler
open Fir.LeanIR.InterpreterExamples
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.SimpCase
open Fir.LeanIR.Passes.SimpCaseAlphaBridge
open Fir.LeanIR.Passes.SimpCaseCompilerBridge
open Fir.LeanIR.Passes.SimpCaseCorrectness
open Fir.LeanIR.Passes.SimpCaseScopedBridge
open Fir.LeanIR.Passes.SimpCaseWellFormed
open Fir.LeanIR.Passes.NonLockstep.Structural
open Fir.LeanIR.Passes.SimpCaseRelation

def selectedBranch : LCNF.Code .impure :=
  .return x

def singletonDefaultCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[.default selectedBranch]

def singletonDefaultCode : LCNF.Code .impure :=
  .cases singletonDefaultCases

def filterUnreachableCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .ctorAlt falseInfo (.unreach objType),
    .ctorAlt trueInfo selectedBranch]

def filterUnreachableCode : LCNF.Code .impure :=
  .cases filterUnreachableCases

def alphaLeftId : FVarId := ⟨`alphaLeft⟩

def alphaRightId : FVarId := ⟨`alphaRight⟩

def alphaLeft : LCNF.Code .impure :=
  .let (letDecl alphaLeftId objType (.lit (.nat 5))) (.return alphaLeftId)

def alphaRight : LCNF.Code .impure :=
  .let (letDecl alphaRightId objType (.lit (.nat 5))) (.return alphaRightId)

#guard alphaLeft.alphaEqv alphaRight

def thirdInfo : LCNF.CtorInfo :=
  { name := `Third, cidx := 2, size := 0, usize := 0, ssize := 0 }

def alphaFoldBeforeCases : LCNF.Cases .impure :=
  .mk `Three objType c #[
    .ctorAlt falseInfo alphaLeft,
    .ctorAlt trueInfo alphaRight,
    .ctorAlt thirdInfo selectedBranch]

def alphaFoldAfterCases : LCNF.Cases .impure :=
  .mk `Three objType c #[
    .ctorAlt thirdInfo selectedBranch,
    .default alphaLeft]

def alphaFoldCode : LCNF.Code .impure :=
  .cases alphaFoldBeforeCases

def alphaFoldExpected : LCNF.Code .impure :=
  .cases alphaFoldAfterCases

/-- Partial-fold regression: the transparent preparation keeps one distinct
constructor and replaces the two alpha-equivalent constructors by a default,
so this exercises the retained-table branch rather than singleton collapse. -/
theorem alphaFoldPrepared_size_eq_two :
    (shadowPrepareAlts alphaFoldBeforeCases).size = 2 := by
  native_decide

theorem alphaFoldPrepared_is_retained :
    (shadowPrepareAlts alphaFoldBeforeCases).size ≠ 0 ∧
      (shadowPrepareAlts alphaFoldBeforeCases).size ≠ 1 := by
  native_decide

theorem alphaFoldDefaultFold_changed :
    shadowAddDefaultAlt
        (shadowFilterUnreachable alphaFoldBeforeCases.alts) ≠
      shadowFilterUnreachable alphaFoldBeforeCases.alts := by
  intro unchanged
  have preparedSize :
      (shadowAddDefaultAlt
        (shadowFilterUnreachable alphaFoldBeforeCases.alts)).size = 2 := by
    native_decide
  have filteredSize :
      (shadowFilterUnreachable alphaFoldBeforeCases.alts).size = 3 := by
    native_decide
  rw [unchanged, filteredSize] at preparedSize
  omega

/-- Two alpha-equivalent arms exercise the path where `addDefaultAlt` first
folds the table to one default and `simplifyCases` then eliminates that
singleton in the same local rewrite. -/
def alphaSingletonFoldCases : LCNF.Cases .impure :=
  .mk `Bool objType c #[
    .ctorAlt falseInfo alphaLeft,
    .ctorAlt trueInfo alphaRight]

def alphaSingletonFoldCode : LCNF.Code .impure :=
  .cases alphaSingletonFoldCases

/-- Structural preparation retains the two distinct bodies while replacing
the second constructor selector by a default. This makes all raw selections
line up with the following alpha fold. -/
def alphaSingletonStructuralCases : LCNF.Cases .impure :=
  .mk `Bool objType c #[
    .ctorAlt falseInfo alphaLeft,
    .default alphaRight]

/-- The alpha phase chooses the representative retained by Lean's fold. -/
def alphaSingletonFoldedCases : LCNF.Cases .impure :=
  .mk `Bool objType c #[.default alphaLeft]

def alphaSingletonFoldValidCase
    (cases : LCNF.Cases .impure) (tag : Nat) : Prop :=
  (cases = alphaSingletonFoldCases ∨
      cases = alphaSingletonStructuralCases ∨
      cases = alphaSingletonFoldedCases) ∧
    (tag = 0 ∨ tag = 1)

#guard shadowSimplifyCases alphaSingletonFoldCases == alphaLeft

/-- Nested phase-depth fixture. Recursive traversal first turns the false arm
from a folded singleton into `alphaLeft`; the parent table then alpha-folds
that result with `alphaRight` and eliminates its own singleton. -/
def nestedPhaseDepthCases : LCNF.Cases .impure :=
  .mk `NestedBool objType c #[
    .ctorAlt falseInfo alphaSingletonFoldCode,
    .ctorAlt trueInfo alphaRight]

def nestedPhaseDepthCode : LCNF.Code .impure :=
  .cases nestedPhaseDepthCases

#guard shadowCode? 3 nestedPhaseDepthCode == some alphaLeft

/-!
`Code.alphaEqv` relies on the compiler invariant that every local `FVarId` is
globally fresh within a declaration. Reusing `x` below makes the Boolean test
accept programs with different observations; this is the minimized witness in
`FIR-BUG-impure-simpCase-alpha-hygiene`.
-/
def nonHygienicAlphaLeft : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 5))) <|
  .let (letDecl x objType (.lit (.nat 6))) <|
  .return x

def nonHygienicAlphaRight : LCNF.Code .impure :=
  .let (letDecl y objType (.lit (.nat 5))) <|
  .let (letDecl z objType (.lit (.nat 6))) <|
  .return y

#guard nonHygienicAlphaLeft.alphaEqv nonHygienicAlphaRight

def localMatchesUpstream (left right : LCNF.Code .impure) : Bool :=
  Local.check 512 left right == left.alphaEqv right

/-!
The local copy is executable despite the opacity of Lean's recursive checker.
These guards compare both implementations over alpha-renamed, rejected, and
compiler-shape fixtures spanning every impure `Code` constructor.
-/
#guard Local.check 512 alphaLeft alphaRight
#guard localMatchesUpstream alphaLeft alphaRight
#guard localMatchesUpstream nonHygienicAlphaLeft nonHygienicAlphaRight
#guard localMatchesUpstream alphaLeft selectedBranch

theorem alphaCodeSideConditions :
    CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] [] alphaLeft alphaRight := by
  apply CodeSideConditions.letE
  · rfl
  · rfl
  · rfl
  · trivial
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · apply CodeSideConditions.ret
    · native_decide
    · native_decide

theorem alphaCodeSideConditionsReverse :
    CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] [] alphaRight alphaLeft := by
  apply CodeSideConditions.letE
  · rfl
  · rfl
  · rfl
  · trivial
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · apply CodeSideConditions.ret
    · native_decide
    · native_decide

/-- The transparent checker closes the complete alpha-renamed `let` fixture. -/
theorem alphaLocalCodeRelated :
    CodeRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] [] alphaLeft alphaRight :=
  codeRelated_of_local_accepts alphaCodeSideConditions ⟨2, by native_decide⟩

def alphaProofState : MachineState := {
  program := { decls := #[] }
  control := .code alphaLeft
}

/-- Bidirectional local acceptance closes a genuine alpha-renamed fixture all
the way to interpreter observational equivalence. -/
theorem alphaLocalCodeEquivalent :
    CodeEquivalentAt externals alphaProofState alphaLeft alphaRight := by
  apply codeEquivalentAt_of_local_accepts_both
    alphaCodeSideConditions alphaCodeSideConditionsReverse
    (by exact ⟨2, by native_decide⟩)
    (by exact ⟨2, by native_decide⟩)
  · intro fvarId member
    simp at member
  · exact .nil
  · intro name decl found
    simp [alphaProofState, Program.findDecl?] at found

def alphaFoldProofState : MachineState := {
  program := { decls := #[] }
  control := .code alphaFoldCode
  env := bind [] c (.object (.tagged 1))
}

/-- The actual default-folding fixture is semantically correct at the `True`
constructor tag, where the pass replaces `alphaRight` by `alphaLeft`. -/
theorem alphaFoldTrueCodeEquivalent :
    CodeEquivalentAt externals alphaFoldProofState
      alphaFoldCode alphaFoldExpected := by
  intro observation
  apply fold_to_default_correct_of_local_alpha
    (scope := []) (discr := .object (.tagged 1)) (tag := 1)
    (beforeBranch := alphaRight) (representative := alphaLeft)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact alphaCodeSideConditionsReverse
  · exact alphaCodeSideConditions
  · exact ⟨2, by native_decide⟩
  · exact ⟨2, by native_decide⟩
  · intro fvarId member
    simp at member
  · exact .nil
  · intro name decl found
    simp [alphaFoldProofState, Program.findDecl?] at found

def singletonDefaultProofState : MachineState := {
  program := { decls := #[] }
  control := .code singletonDefaultCode
  env := bind (bind [] c (.object (.tagged 0))) x .erased
}

/-- The actual singleton-default fixture is equivalent to its surviving arm. -/
theorem singletonDefaultCodeEquivalent :
    CodeEquivalentAt externals singletonDefaultProofState
      singletonDefaultCode selectedBranch := by
  apply singleton_default_codeEquivalent
    (discr := .object (.tagged 0)) (tag := 0)
  · rfl
  · rfl
  · rfl

def filterUnreachableProofState : MachineState := {
  program := { decls := #[] }
  control := .code filterUnreachableCode
  env := bind (bind [] c (.object (.tagged 1))) x .erased
}

/-- The actual unreachable-filter fixture first removes the dead arm and then
eliminates the surviving singleton constructor arm. -/
theorem filterUnreachableCodeEquivalent :
    CodeEquivalentAt externals filterUnreachableProofState
      filterUnreachableCode selectedBranch := by
  intro observation
  calc
    EvaluatesState externals
        { filterUnreachableProofState with
          control := .code filterUnreachableCode } observation ↔
      EvaluatesState externals
        { filterUnreachableProofState with
          control := .code (.cases
            (removeUnreachableCases filterUnreachableCases)) } observation :=
      remove_unreachable_codeEquivalent_of_selected
        (discr := .object (.tagged 1)) (tag := 1)
        (branch := selectedBranch) (by rfl) (by rfl) (by rfl) (by rfl)
        observation
    _ ↔ EvaluatesState externals
        { filterUnreachableProofState with
          control := .code selectedBranch } observation :=
      singleton_constructor_codeEquivalent
        (caseInfo := removeUnreachableCases filterUnreachableCases)
        (discr := .object (.tagged 1)) (info := trueInfo)
        (branch := selectedBranch) (by rfl) (by rfl) (by rfl) observation

def proofCaseTable : LCNF.Cases .impure :=
  .mk ``Bool objType c #[]

def proofCaseCode : LCNF.Code .impure :=
  .cases proofCaseTable

theorem proofCaseDeterministic :
    CaseTableDeterministic proofCaseTable.alts.toList := by
  constructor
  · intro tag left right leftHas rightHas
    exfalso
    simp [proofCaseTable, LCNF.Cases.alts, HasCtorAlt] at leftHas
  · intro left right leftHas rightHas
    exfalso
    simp [proofCaseTable, LCNF.Cases.alts, HasDefaultAlt] at leftHas

theorem proofCaseNormalization : proofCaseTable.alts.toList.Perm
    (LCNF.AlphaEqv.sortAlts proofCaseTable.alts).toList := by
  exact sortAlts_perm proofCaseTable.alts

theorem proofCaseNormalizationInvariant :
    CaseTableNormalizationInvariant proofCaseTable.alts :=
  ⟨proofCaseDeterministic⟩

theorem proofCaseBranches :
    CaseBranchesSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [c, x] [c, x]
      proofCaseTable.alts.toList proofCaseTable.alts.toList := by
  constructor
  · intro tag left right leftHas rightHas
    exfalso
    simp [proofCaseTable, LCNF.Cases.alts, HasCtorAlt] at leftHas
  · intro left right leftHas rightHas
    exfalso
    simp [proofCaseTable, LCNF.Cases.alts, HasDefaultAlt] at leftHas

/-- The local checker proves that equal empty case tables fail selection alike. -/
theorem proofCaseLocalCodeRelated :
    CodeRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [c, x] [c, x]
      proofCaseCode proofCaseCode := by
  apply codeRelated_cases_of_local_accepts
  · native_decide
  · native_decide
  · exact proofCaseNormalizationInvariant
  · exact proofCaseNormalizationInvariant
  · exact proofCaseBranches
  · exact ⟨1, by native_decide⟩

theorem ctorDefaultCaseTableDeterministic
    (info : LCNF.CtorInfo) (ctorCode defaultCode : LCNF.Code .impure) :
    CaseTableDeterministic [.ctorAlt info ctorCode, .default defaultCode] := by
  constructor
  · intro tag left right leftHas rightHas
    rcases leftHas with ⟨leftInfo, leftMember, leftTag⟩
    rcases rightHas with ⟨rightInfo, rightMember, rightTag⟩
    simp at leftMember rightMember
    simp_all
  · intro left right leftHas rightHas
    simp [HasDefaultAlt] at leftHas rightHas
    simp_all

theorem defaultCtorCaseTableDeterministic
    (info : LCNF.CtorInfo) (ctorCode defaultCode : LCNF.Code .impure) :
    CaseTableDeterministic [.default defaultCode, .ctorAlt info ctorCode] := by
  constructor
  · intro tag left right leftHas rightHas
    rcases leftHas with ⟨leftInfo, leftMember, leftTag⟩
    rcases rightHas with ⟨rightInfo, rightMember, rightTag⟩
    simp at leftMember rightMember
    simp_all
  · intro left right leftHas rightHas
    simp [HasDefaultAlt] at leftHas rightHas
    simp_all

/-!
The whole-program alpha-fold regression factors the compiler result through an
intermediate default that retains the source's selected `alphaRight` body.
The recursive relation handles source-to-intermediate stuttering at tag `1`;
the program-aware alpha relation then renames that default to `alphaLeft`.
-/

def alphaFoldIntermediateCases : LCNF.Cases .impure :=
  .mk `Three objType c #[
    .ctorAlt thirdInfo selectedBranch,
    .default alphaRight]

def alphaFoldIntermediate : LCNF.Code .impure :=
  .cases alphaFoldIntermediateCases

def alphaFoldValidCase (cases : LCNF.Cases .impure) (tag : Nat) : Prop :=
  cases = alphaFoldBeforeCases ∧ tag = 1

abbrev AlphaFoldStructuralRel := CodeRel alphaFoldValidCase

theorem alphaFoldRightStructuralRefl :
    AlphaFoldStructuralRel alphaRight alphaRight := by
  exact .aligned (.let (letDecl alphaRightId objType (.lit (.nat 5)))
    (.aligned (.return alphaRightId)))

theorem alphaFoldStructuralCodeRelated :
    AlphaFoldStructuralRel alphaFoldCode alphaFoldIntermediate := by
  apply CodeRel.aligned
  apply HeadRel.cases
  intro tag valid
  rcases valid with ⟨_, rfl⟩
  change SelectionRel alphaFoldValidCase (some alphaRight) (some alphaRight)
  exact .some alphaFoldRightStructuralRefl

def alphaFoldDeclWith (code : LCNF.Code .impure) : LCNF.Decl .impure :=
  decl `main #[param c, param x] objType (.code code)

def alphaFoldProgramWith (code : LCNF.Code .impure) : ImpureProgram :=
  { decls := #[alphaFoldDeclWith code] }

def alphaFoldBeforeProgram : ImpureProgram :=
  alphaFoldProgramWith alphaFoldCode

def alphaFoldIntermediateProgram : ImpureProgram :=
  alphaFoldProgramWith alphaFoldIntermediate

def alphaFoldAfterProgram : ImpureProgram :=
  alphaFoldProgramWith alphaFoldExpected

def alphaFoldEntries : Array Name := #[`main]

theorem alphaFoldStructuralProgramsRelated :
    ProgramRelated AlphaFoldStructuralRel
      alphaFoldBeforeProgram alphaFoldIntermediateProgram := by
  exact .cons {
    name_eq := rfl
    levelParams_eq := rfl
    type_eq := rfl
    params_eq := rfl
    safe_eq := rfl
    value := .code alphaFoldStructuralCodeRelated
    recursive_eq := rfl
    inlineAttr_eq := rfl
  } .nil

theorem alphaFoldStructuralCorrect :
    SamePhaseCorrectOn (Impure.semantics externals)
      alphaFoldBeforeProgram alphaFoldIntermediateProgram alphaFoldEntries
      (ReachablyReadyAdmissible externals alphaFoldValidCase
        alphaFoldBeforeProgram alphaFoldIntermediateProgram) :=
  samePhaseCorrectOn_reachablyReady alphaFoldStructuralProgramsRelated

def alphaFoldParamRho : FVarIdMap FVarId :=
  (({} : FVarIdMap FVarId).insert c c).insert x x

theorem alphaFoldIntermediateNormalization :
    CaseTableNormalizationInvariant alphaFoldIntermediateCases.alts := by
  exact ⟨ctorDefaultCaseTableDeterministic
    thirdInfo selectedBranch alphaRight⟩

theorem alphaFoldExpectedNormalization :
    CaseTableNormalizationInvariant alphaFoldAfterCases.alts := by
  exact ⟨ctorDefaultCaseTableDeterministic
    thirdInfo selectedBranch alphaLeft⟩

theorem alphaRightFreshForParams : FreshForScope alphaRightId [x, c] := by
  intro old oldScoped
  simp at oldScoped
  rcases oldScoped with oldIsX | oldIsC
  · have oldEq : old = x := fvar_eq_of_beq oldIsX
    subst old
    native_decide
  · have oldEq : old = c := fvar_eq_of_beq oldIsC
    subst old
    native_decide

theorem alphaLeftFreshForParams : FreshForScope alphaLeftId [x, c] := by
  intro old oldScoped
  simp at oldScoped
  rcases oldScoped with oldIsX | oldIsC
  · have oldEq : old = x := fvar_eq_of_beq oldIsX
    subst old
    native_decide
  · have oldEq : old = c := fvar_eq_of_beq oldIsC
    subst old
    native_decide

theorem xFreshForC : FreshForScope x [c] := by
  intro old oldScoped
  simp at oldScoped
  have oldEq : old = c := fvar_eq_of_beq oldScoped
  subst old
  native_decide

theorem alphaRightLeftSideConditionsAtParams :
    CodeSideConditions (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c] alphaRight alphaLeft := by
  apply CodeSideConditions.letE
  · rfl
  · rfl
  · rfl
  · trivial
  · exact alphaRightFreshForParams
  · exact alphaLeftFreshForParams
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · apply CodeSideConditions.ret <;> native_decide

theorem alphaLeftRightSideConditionsAtParams :
    CodeSideConditions (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c] alphaLeft alphaRight := by
  apply CodeSideConditions.letE
  · rfl
  · rfl
  · rfl
  · trivial
  · exact alphaLeftFreshForParams
  · exact alphaRightFreshForParams
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · apply CodeSideConditions.ret <;> native_decide

theorem alphaFoldCaseBranchesForward :
    CaseBranchesSideConditions (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      alphaFoldIntermediateCases.alts.toList alphaFoldAfterCases.alts.toList := by
  constructor
  · intro tag leftCode rightCode leftHas rightHas
    simp [HasCtorAlt, alphaFoldIntermediateCases, alphaFoldAfterCases,
      LCNF.Cases.alts]
      at leftHas rightHas
    rcases leftHas with ⟨_, ⟨rfl, rfl⟩, _⟩
    rcases rightHas with ⟨_, ⟨rfl, rfl⟩, _⟩
    exact .ret (by native_decide) (by native_decide)
  · intro leftCode rightCode leftHas rightHas
    simp [HasDefaultAlt, alphaFoldIntermediateCases, alphaFoldAfterCases,
      LCNF.Cases.alts]
      at leftHas rightHas
    subst leftCode
    subst rightCode
    exact alphaRightLeftSideConditionsAtParams

theorem alphaFoldCaseBranchesBackward :
    CaseBranchesSideConditions (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      alphaFoldAfterCases.alts.toList alphaFoldIntermediateCases.alts.toList := by
  constructor
  · intro tag leftCode rightCode leftHas rightHas
    simp [HasCtorAlt, alphaFoldIntermediateCases, alphaFoldAfterCases,
      LCNF.Cases.alts]
      at leftHas rightHas
    rcases leftHas with ⟨_, ⟨rfl, rfl⟩, _⟩
    rcases rightHas with ⟨_, ⟨rfl, rfl⟩, _⟩
    exact .ret (by native_decide) (by native_decide)
  · intro leftCode rightCode leftHas rightHas
    simp [HasDefaultAlt, alphaFoldIntermediateCases, alphaFoldAfterCases,
      LCNF.Cases.alts]
      at leftHas rightHas
    subst leftCode
    subst rightCode
    exact alphaLeftRightSideConditionsAtParams

theorem alphaFoldCasesAlphaForward :
    CodeRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      alphaFoldIntermediate alphaFoldExpected := by
  apply codeRelated_cases_of_local_accepts
  · native_decide
  · native_decide
  · exact alphaFoldIntermediateNormalization
  · exact alphaFoldExpectedNormalization
  · exact alphaFoldCaseBranchesForward
  · exact ⟨4, by native_decide⟩

theorem alphaFoldCasesAlphaBackward :
    CodeRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      alphaFoldExpected alphaFoldIntermediate := by
  apply codeRelated_cases_of_local_accepts
  · native_decide
  · native_decide
  · exact alphaFoldExpectedNormalization
  · exact alphaFoldIntermediateNormalization
  · exact alphaFoldCaseBranchesBackward
  · exact ⟨4, by native_decide⟩

def alphaFoldScopeIndex : ScopeIndex := {
  forwardRho := alphaFoldParamRho
  backwardRho := alphaFoldParamRho
  forwardEmpty := by
    unfold alphaFoldParamRho
    exact ((resolverEquivalent_refl {}).insertSelf_of_empty c).insertSelf_of_empty x
  backwardEmpty := by
    unfold alphaFoldParamRho
    exact ((resolverEquivalent_refl {}).insertSelf_of_empty c).insertSelf_of_empty x
  sourceScope := [x, c]
  targetScope := [x, c]
  scopesEq := rfl
  sourceJoins := []
  targetJoins := []
  joinsEq := rfl
}

/-- The current structural-then-alpha singleton interface is too strong for
the compiler's combined fold-and-eliminate path. Both valid source tags must
share one structural intermediate, but `CodeRel` cannot rename their distinct
leading binders. -/
theorem alphaSingletonFold_hasNoStructuralConvergence :
    ¬ Nonempty (ScopedSingletonSelectionConvergence
      alphaSingletonFoldValidCase alphaFoldScopeIndex
      alphaSingletonFoldCases alphaLeft) := by
  rintro ⟨converges⟩
  have falseSelected :=
    converges.structuralSelected 0 ⟨Or.inl rfl, Or.inl rfl⟩
  have trueSelected :=
    converges.structuralSelected 1 ⟨Or.inl rfl, Or.inr rfl⟩
  change ElimSelectionRel alphaSingletonFoldValidCase converges.middle
    (some alphaLeft) at falseSelected
  change ElimSelectionRel alphaSingletonFoldValidCase converges.middle
    (some alphaRight) at trueSelected
  cases falseSelected with
  | some falseRelated =>
      cases trueSelected with
      | some trueRelated =>
          rcases codeRel_let_target_shape falseRelated with ⟨left, leftEq⟩
          rcases codeRel_let_target_shape trueRelated with ⟨right, rightEq⟩
          rw [rightEq] at leftEq
          injection leftEq with declarationEq continuationEq
          have identifiers : alphaRightId = alphaLeftId := congrArg
            (fun declaration : LCNF.LetDecl .impure => declaration.fvarId)
            declarationEq
          have names := congrArg FVarId.name identifiers
          exact absurd names (by native_decide)

theorem alphaLeftAlphaBireflexiveAtFoldScope :
    ScopedAlphaBireflexive alphaFoldScopeIndex alphaLeft := by
  constructor
  · apply CodeRelated.letE
    · exact ⟨rfl, .lit (.nat 5)⟩
    · exact alphaLeftFreshForParams
    · exact alphaLeftFreshForParams
    · intro old oldScoped
      simp [alphaFoldScopeIndex] at oldScoped
    · intro old oldScoped
      simp [alphaFoldScopeIndex] at oldScoped
    · exact .terminal (.ret ⟨by native_decide, by native_decide,
        fVarRelated_insert_self alphaFoldParamRho alphaLeftId alphaLeftId⟩)
  · apply CodeRelated.letE
    · exact ⟨rfl, .lit (.nat 5)⟩
    · exact alphaLeftFreshForParams
    · exact alphaLeftFreshForParams
    · intro old oldScoped
      simp [alphaFoldScopeIndex] at oldScoped
    · intro old oldScoped
      simp [alphaFoldScopeIndex] at oldScoped
    · exact .terminal (.ret ⟨by native_decide, by native_decide,
        fVarRelated_insert_self alphaFoldParamRho alphaLeftId alphaLeftId⟩)

theorem alphaRightAlphaBireflexiveAtFoldScope :
    ScopedAlphaBireflexive alphaFoldScopeIndex alphaRight := by
  constructor
  · apply CodeRelated.letE
    · exact ⟨rfl, .lit (.nat 5)⟩
    · exact alphaRightFreshForParams
    · exact alphaRightFreshForParams
    · intro old oldScoped
      simp [alphaFoldScopeIndex] at oldScoped
    · intro old oldScoped
      simp [alphaFoldScopeIndex] at oldScoped
    · exact .terminal (.ret ⟨by native_decide, by native_decide,
        fVarRelated_insert_self alphaFoldParamRho alphaRightId alphaRightId⟩)
  · apply CodeRelated.letE
    · exact ⟨rfl, .lit (.nat 5)⟩
    · exact alphaRightFreshForParams
    · exact alphaRightFreshForParams
    · intro old oldScoped
      simp [alphaFoldScopeIndex] at oldScoped
    · intro old oldScoped
      simp [alphaFoldScopeIndex] at oldScoped
    · exact .terminal (.ret ⟨by native_decide, by native_decide,
        fVarRelated_insert_self alphaFoldParamRho alphaRightId alphaRightId⟩)

theorem cRelatedAtFoldScope :
    ScopedFVarRelated alphaFoldParamRho [x, c] [x, c] c c := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  unfold alphaFoldParamRho
  apply (fVarRelated_insert_of_name_ne
    (({} : FVarIdMap FVarId).insert c c) x x c c
    (by native_decide)).2
  exact fVarRelated_insert_self ({} : FVarIdMap FVarId) c c

theorem alphaSingletonFoldAlphaBireflexive :
    ScopedAlphaBireflexive alphaFoldScopeIndex alphaSingletonFoldCode := by
  constructor
  · apply CodeRelated.cases cRelatedAtFoldScope
    intro tag
    exact chooseAlt_related (.cons
      (.ctor alphaLeftAlphaBireflexiveAtFoldScope.forward)
      (.cons (.ctor alphaRightAlphaBireflexiveAtFoldScope.forward) .nil))
  · apply CodeRelated.cases cRelatedAtFoldScope
    intro tag
    exact chooseAlt_related (.cons
      (.ctor alphaLeftAlphaBireflexiveAtFoldScope.backward)
      (.cons (.ctor alphaRightAlphaBireflexiveAtFoldScope.backward) .nil))

theorem alphaRightLeftCodeRelatedAtFoldScope :
    CodeRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c] alphaRight alphaLeft :=
  codeRelated_of_local_accepts alphaRightLeftSideConditionsAtParams
    ⟨2, by native_decide⟩

theorem alphaLeftRightCodeRelatedAtFoldScope :
    CodeRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c] alphaLeft alphaRight :=
  codeRelated_of_local_accepts alphaLeftRightSideConditionsAtParams
    ⟨2, by native_decide⟩

theorem alphaSingletonStructuralBefore :
    CodeRel alphaSingletonFoldValidCase alphaSingletonFoldCode
      (.cases alphaSingletonStructuralCases) := by
  apply CodeRel.aligned
  apply HeadRel.cases
  intro tag valid
  rcases valid.2 with rfl | rfl
  · change SelectionRel alphaSingletonFoldValidCase
      (some alphaLeft) (some alphaLeft)
    exact .some (.aligned (.let
      (letDecl alphaLeftId objType (.lit (.nat 5)))
      (.aligned (.return alphaLeftId))))
  · change SelectionRel alphaSingletonFoldValidCase
      (some alphaRight) (some alphaRight)
    exact .some (.aligned (.let
      (letDecl alphaRightId objType (.lit (.nat 5)))
      (.aligned (.return alphaRightId))))

theorem alphaSingletonAlphaForward :
    CodeRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      (.cases alphaSingletonStructuralCases)
      (.cases alphaSingletonFoldedCases) := by
  apply CodeRelated.cases
  · refine ⟨by native_decide, by native_decide, ?_⟩
    unfold alphaFoldParamRho
    apply (fVarRelated_insert_of_name_ne
      (({} : FVarIdMap FVarId).insert c c) x x c c
      (by native_decide)).2
    exact fVarRelated_insert_self ({} : FVarIdMap FVarId) c c
  · intro tag
    by_cases zero : tag = 0
    · subst tag
      change CaseSelectionRelated (leftJoins := []) (rightJoins := [])
        alphaFoldParamRho [x, c] [x, c]
        (some alphaLeft) (some alphaLeft)
      exact .some alphaLeftAlphaBireflexiveAtFoldScope.forward
    · have zeroSymm : 0 ≠ tag := Ne.symm zero
      simpa [alphaSingletonStructuralCases, alphaSingletonFoldedCases,
        LCNF.Cases.alts, chooseAlt, findCtorAlt, findDefaultAlt,
        falseInfo, zeroSymm]
        using CaseSelectionRelated.some
          alphaRightLeftCodeRelatedAtFoldScope

theorem alphaSingletonAlphaBackward :
    CodeRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      (.cases alphaSingletonFoldedCases)
      (.cases alphaSingletonStructuralCases) := by
  apply CodeRelated.cases
  · refine ⟨by native_decide, by native_decide, ?_⟩
    unfold alphaFoldParamRho
    apply (fVarRelated_insert_of_name_ne
      (({} : FVarIdMap FVarId).insert c c) x x c c
      (by native_decide)).2
    exact fVarRelated_insert_self ({} : FVarIdMap FVarId) c c
  · intro tag
    by_cases zero : tag = 0
    · subst tag
      change CaseSelectionRelated (leftJoins := []) (rightJoins := [])
        alphaFoldParamRho [x, c] [x, c]
        (some alphaLeft) (some alphaLeft)
      exact .some alphaLeftAlphaBireflexiveAtFoldScope.backward
    · have zeroSymm : 0 ≠ tag := Ne.symm zero
      simpa [alphaSingletonStructuralCases, alphaSingletonFoldedCases,
        LCNF.Cases.alts, chooseAlt, findCtorAlt, findDefaultAlt,
        falseInfo, zeroSymm]
        using CaseSelectionRelated.some
          alphaLeftRightCodeRelatedAtFoldScope

theorem alphaSingletonFilteredAlts_eq :
    shadowFilterUnreachable alphaSingletonFoldCases.alts =
      alphaSingletonFoldCases.alts := by
  rfl

theorem alphaSingletonFiltered_size_ne_one :
    (shadowFilterUnreachable alphaSingletonFoldCases.alts).size ≠ 1 := by
  native_decide

theorem alphaSingletonPrepared_size_eq_one :
    (shadowPrepareAlts alphaSingletonFoldCases).size = 1 := by
  native_decide

/-- The generic compiler-shape theorem classifies the concrete alpha fixture
without requiring kernel reduction of Lean's opaque `Code.alphaEqv`. -/
theorem alphaSingletonPrepared_is_singleton_default :
    ∃ body,
      shadowAddDefaultAlt
          (shadowFilterUnreachable alphaSingletonFoldCases.alts) =
        #[.default body] :=
  shadowAddDefaultAlt_eq_singleton_default_of_created
    alphaSingletonFiltered_size_ne_one alphaSingletonPrepared_size_eq_one

theorem alphaSingletonStructuralSelection
    (selected : chooseAlt tag alphaSingletonFoldCases.alts.toList =
      some branch) :
    chooseAlt tag alphaSingletonStructuralCases.alts.toList = some branch := by
  by_cases zero : tag = 0
  · subst tag
    simpa [alphaSingletonFoldCases, alphaSingletonStructuralCases,
      LCNF.Cases.alts, chooseAlt, findCtorAlt, findDefaultAlt,
      falseInfo, trueInfo] using selected
  · by_cases one : tag = 1
    · subst tag
      simpa [alphaSingletonFoldCases, alphaSingletonStructuralCases,
        LCNF.Cases.alts, chooseAlt, findCtorAlt, findDefaultAlt,
        falseInfo, trueInfo] using selected
    · have zeroSymm : 0 ≠ tag := Ne.symm zero
      have oneSymm : 1 ≠ tag := Ne.symm one
      simp [alphaSingletonFoldCases, LCNF.Cases.alts, chooseAlt,
        findCtorAlt, findDefaultAlt, falseInfo, trueInfo, zeroSymm,
        oneSymm] at selected

theorem alphaSingletonFoldAddDefaultEvidence :
    shadowAddDefaultAlt
        (shadowFilterUnreachable alphaSingletonFoldCases.alts) =
      alphaSingletonFoldedCases.alts →
    ScopedAddDefaultSelectionEvidence alphaFoldScopeIndex
      alphaSingletonStructuralCases.alts
      (shadowFilterUnreachable alphaSingletonFoldCases.alts) := by
  intro preparedEq
  exact {
    forward := by
      intro tag
      rw [preparedEq]
      exact codeRelated_cases_selected alphaSingletonAlphaForward tag
    backward := by
      intro tag
      rw [preparedEq]
      exact codeRelated_cases_selected alphaSingletonAlphaBackward tag
  }

/-- Focused regression for the reduced fold contract: the fixture supplies a
selection-preserving proof intermediate and only the alpha-changing selected
branch relation, rather than a preassembled three-phase factor. -/
def alphaSingletonFoldedAlphaEvidence
    (preparedEq : shadowAddDefaultAlt
        (shadowFilterUnreachable alphaSingletonFoldCases.alts) =
      alphaSingletonFoldedCases.alts) :
    ScopedFoldedAlphaEvidence alphaFoldScopeIndex
      alphaSingletonFoldCases.alts := {
  middleAlts := alphaSingletonStructuralCases.alts
  sourceSelection := by
    intro tag branch selected reachable
    exact alphaSingletonStructuralSelection selected
  folded := alphaSingletonFoldAddDefaultEvidence preparedEq
}

theorem alphaSingletonStructuralAfter :
    CodeRel alphaSingletonFoldValidCase
      (.cases alphaSingletonFoldedCases) alphaLeft := by
  apply CodeRel.eliminate alphaSingletonFoldedCases alphaLeft
  intro tag valid
  change ElimSelectionRel alphaSingletonFoldValidCase alphaLeft
    (some alphaLeft)
  exact .some (.aligned (.let
    (letDecl alphaLeftId objType (.lit (.nat 5)))
    (.aligned (.return alphaLeftId))))

/-- Positive counterpart to the negative convergence theorem: the exact
compiler path is representable once the final singleton elimination is a
separate structural phase. -/
def alphaSingletonFoldThreePhaseFactor :
    ScopedCodeTrifactor alphaSingletonFoldValidCase alphaFoldScopeIndex
      alphaSingletonFoldCode alphaLeft := {
  structuralMiddle := .cases alphaSingletonStructuralCases
  alphaMiddle := .cases alphaSingletonFoldedCases
  structuralBefore := alphaSingletonStructuralBefore
  alphaForward := alphaSingletonAlphaForward
  alphaBackward := alphaSingletonAlphaBackward
  structuralAfter := alphaSingletonStructuralAfter
}

theorem alphaSingletonFoldThreePhased :
    ScopedCodeThreePhased alphaSingletonFoldValidCase alphaFoldScopeIndex
      alphaSingletonFoldCode alphaLeft :=
  alphaSingletonFoldThreePhaseFactor.threePhased

def alphaSingletonFoldPhaseEvidence :
    ScopedSingletonPhaseEvidence alphaSingletonFoldValidCase
      alphaFoldScopeIndex alphaSingletonFoldCases alphaLeft :=
  .folded alphaSingletonFoldThreePhaseFactor

theorem alphaSingletonFoldPhaseFactored :
    ScopedCodePhaseFactored alphaSingletonFoldValidCase alphaFoldScopeIndex
      alphaSingletonFoldCode alphaLeft :=
  alphaSingletonFoldPhaseEvidence.phaseFactored

theorem alphaLeftStructuralRefl :
    CodeRel alphaSingletonFoldValidCase alphaLeft alphaLeft :=
  .aligned (.let (letDecl alphaLeftId objType (.lit (.nat 5)))
    (.aligned (.return alphaLeftId)))

/-- Traversal-ready form of the local folded-singleton witness. The target
identity is ordinary evidence used only to align phase schedules. -/
def alphaSingletonFoldPhaseResult :
    ScopedCodePhaseResult alphaSingletonFoldValidCase alphaFoldScopeIndex
      alphaSingletonFoldCode alphaLeft := {
  factor := .threePhase alphaSingletonFoldThreePhaseFactor
  targetRefl := alphaLeftStructuralRefl
  targetAlpha := alphaLeftAlphaBireflexiveAtFoldScope
}

def alphaSingletonFoldPhaseResultEvidence :
    ScopedSingletonPhaseResultEvidence alphaSingletonFoldValidCase
      alphaFoldScopeIndex alphaSingletonFoldCases alphaLeft := {
  phase := alphaSingletonFoldPhaseEvidence
  identities := alphaSingletonFoldPhaseResult.identities
}

/-- Fold-created singleton witness through the new phase-shape packaging. -/
def alphaSingletonFoldPhaseShapeResult :
    ScopedCodePhaseResult alphaSingletonFoldValidCase alphaFoldScopeIndex
      alphaSingletonFoldCode alphaLeft :=
  alphaSingletonFoldPhaseResultEvidence.result

def alphaSingletonFoldTrace :
    ScopedCodePhaseTrace alphaSingletonFoldValidCase alphaFoldScopeIndex
      alphaSingletonFoldCode alphaLeft :=
  alphaSingletonFoldPhaseResult.trace

def alphaSingletonFoldPaddedTrace :
    ScopedCodePhaseTrace alphaSingletonFoldValidCase alphaFoldScopeIndex
      alphaSingletonFoldCode alphaLeft :=
  alphaSingletonFoldTrace.pad

#guard alphaSingletonFoldTrace.rounds == 1
#guard alphaSingletonFoldPaddedTrace.rounds == 2

theorem alphaSingletonFoldPaddedTrace_endpointStructural :
    CodeRel alphaSingletonFoldValidCase alphaLeft alphaLeft :=
  alphaSingletonFoldPaddedTrace.targetRefl

theorem alphaSingletonFoldPaddedTrace_endpointAlpha :
    ScopedAlphaBireflexive alphaFoldScopeIndex alphaLeft :=
  alphaSingletonFoldPaddedTrace.targetAlpha

/-!
The nested-depth regression uses one validity predicate for both the inner
and outer Boolean tables. This keeps every structural selection obligation
non-vacuous while the trace records the two local simplifier rounds.
-/

def nestedPhaseDepthValidCase
    (_cases : LCNF.Cases .impure) (tag : Nat) : Prop :=
  tag = 0 ∨ tag = 1

def nestedPhaseDepthRecursiveCases : LCNF.Cases .impure :=
  .mk `NestedBool objType c #[
    .ctorAlt falseInfo alphaLeft,
    .ctorAlt trueInfo alphaRight]

def nestedPhaseDepthStructuralCases : LCNF.Cases .impure :=
  .mk `NestedBool objType c #[
    .ctorAlt falseInfo alphaLeft,
    .default alphaRight]

def nestedPhaseDepthFoldedCases : LCNF.Cases .impure :=
  .mk `NestedBool objType c #[.default alphaLeft]

#guard shadowSimplifyCases nestedPhaseDepthRecursiveCases == alphaLeft

theorem nestedAlphaLeftStructuralRefl :
    CodeRel nestedPhaseDepthValidCase alphaLeft alphaLeft :=
  .aligned (.let (letDecl alphaLeftId objType (.lit (.nat 5)))
    (.aligned (.return alphaLeftId)))

theorem nestedAlphaRightStructuralRefl :
    CodeRel nestedPhaseDepthValidCase alphaRight alphaRight :=
  .aligned (.let (letDecl alphaRightId objType (.lit (.nat 5)))
    (.aligned (.return alphaRightId)))

theorem nestedInnerStructuralBefore :
    CodeRel nestedPhaseDepthValidCase alphaSingletonFoldCode
      (.cases alphaSingletonStructuralCases) := by
  apply CodeRel.aligned
  apply HeadRel.cases
  intro tag valid
  rcases valid with rfl | rfl
  · change SelectionRel nestedPhaseDepthValidCase
      (some alphaLeft) (some alphaLeft)
    exact .some nestedAlphaLeftStructuralRefl
  · change SelectionRel nestedPhaseDepthValidCase
      (some alphaRight) (some alphaRight)
    exact .some nestedAlphaRightStructuralRefl

theorem nestedInnerStructuralAfter :
    CodeRel nestedPhaseDepthValidCase
      (.cases alphaSingletonFoldedCases) alphaLeft := by
  apply CodeRel.eliminate alphaSingletonFoldedCases alphaLeft
  intro tag valid
  change ElimSelectionRel nestedPhaseDepthValidCase alphaLeft
    (some alphaLeft)
  exact .some nestedAlphaLeftStructuralRefl

def nestedInnerPhaseResult :
    ScopedCodePhaseResult nestedPhaseDepthValidCase alphaFoldScopeIndex
      alphaSingletonFoldCode alphaLeft := {
  factor := .threePhase {
    structuralMiddle := .cases alphaSingletonStructuralCases
    alphaMiddle := .cases alphaSingletonFoldedCases
    structuralBefore := nestedInnerStructuralBefore
    alphaForward := alphaSingletonAlphaForward
    alphaBackward := alphaSingletonAlphaBackward
    structuralAfter := nestedInnerStructuralAfter
  }
  targetRefl := nestedAlphaLeftStructuralRefl
  targetAlpha := alphaLeftAlphaBireflexiveAtFoldScope
}

def nestedAlphaRightIdentityResult :
    ScopedCodePhaseResult nestedPhaseDepthValidCase alphaFoldScopeIndex
      alphaRight alphaRight :=
  .identity nestedAlphaRightStructuralRefl
    alphaRightAlphaBireflexiveAtFoldScope

def nestedPhaseDepthAlternativesTrace :
    ScopedAltsPhaseTrace nestedPhaseDepthValidCase alphaFoldScopeIndex
      nestedPhaseDepthCases.alts.toList
      nestedPhaseDepthRecursiveCases.alts.toList := by
  exact nestedInnerPhaseResult.trace.consCtor
    (nestedAlphaRightIdentityResult.trace.consCtor (.single .nil))

#guard nestedPhaseDepthAlternativesTrace.rounds == 1

theorem nestedPhaseDepthAlphaBireflexive :
    ScopedAlphaBireflexive alphaFoldScopeIndex nestedPhaseDepthCode := by
  constructor
  · apply CodeRelated.cases cRelatedAtFoldScope
    intro tag
    exact chooseAlt_related (.cons
      (.ctor alphaSingletonFoldAlphaBireflexive.forward)
      (.cons (.ctor alphaRightAlphaBireflexiveAtFoldScope.forward) .nil))
  · apply CodeRelated.cases cRelatedAtFoldScope
    intro tag
    exact chooseAlt_related (.cons
      (.ctor alphaSingletonFoldAlphaBireflexive.backward)
      (.cons (.ctor alphaRightAlphaBireflexiveAtFoldScope.backward) .nil))

def nestedPhaseDepthRecursiveTrace :
    ScopedCodePhaseTrace nestedPhaseDepthValidCase alphaFoldScopeIndex
      nestedPhaseDepthCode (.cases nestedPhaseDepthRecursiveCases) := by
  simpa [nestedPhaseDepthCode, nestedPhaseDepthCases,
    nestedPhaseDepthRecursiveCases, LCNF.Cases.alts] using
    nestedPhaseDepthAlternativesTrace.casesTrace
      `NestedBool objType c nestedPhaseDepthAlphaBireflexive

theorem nestedParentStructuralBefore :
    CodeRel nestedPhaseDepthValidCase
      (.cases nestedPhaseDepthRecursiveCases)
      (.cases nestedPhaseDepthStructuralCases) := by
  apply CodeRel.aligned
  apply HeadRel.cases
  intro tag valid
  rcases valid with rfl | rfl
  · change SelectionRel nestedPhaseDepthValidCase
      (some alphaLeft) (some alphaLeft)
    exact .some nestedAlphaLeftStructuralRefl
  · change SelectionRel nestedPhaseDepthValidCase
      (some alphaRight) (some alphaRight)
    exact .some nestedAlphaRightStructuralRefl

theorem nestedParentAlphaForward :
    CodeRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      (.cases nestedPhaseDepthStructuralCases)
      (.cases nestedPhaseDepthFoldedCases) := by
  apply CodeRelated.cases cRelatedAtFoldScope
  intro tag
  by_cases zero : tag = 0
  · subst tag
    change CaseSelectionRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      (some alphaLeft) (some alphaLeft)
    exact .some alphaLeftAlphaBireflexiveAtFoldScope.forward
  · have zeroSymm : 0 ≠ tag := Ne.symm zero
    simpa [nestedPhaseDepthStructuralCases, nestedPhaseDepthFoldedCases,
      LCNF.Cases.alts, chooseAlt, findCtorAlt, findDefaultAlt,
      falseInfo, zeroSymm]
      using CaseSelectionRelated.some alphaRightLeftCodeRelatedAtFoldScope

theorem nestedParentAlphaBackward :
    CodeRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      (.cases nestedPhaseDepthFoldedCases)
      (.cases nestedPhaseDepthStructuralCases) := by
  apply CodeRelated.cases cRelatedAtFoldScope
  intro tag
  by_cases zero : tag = 0
  · subst tag
    change CaseSelectionRelated (leftJoins := []) (rightJoins := [])
      alphaFoldParamRho [x, c] [x, c]
      (some alphaLeft) (some alphaLeft)
    exact .some alphaLeftAlphaBireflexiveAtFoldScope.backward
  · have zeroSymm : 0 ≠ tag := Ne.symm zero
    simpa [nestedPhaseDepthStructuralCases, nestedPhaseDepthFoldedCases,
      LCNF.Cases.alts, chooseAlt, findCtorAlt, findDefaultAlt,
      falseInfo, zeroSymm]
      using CaseSelectionRelated.some alphaLeftRightCodeRelatedAtFoldScope

theorem nestedParentStructuralAfter :
    CodeRel nestedPhaseDepthValidCase
      (.cases nestedPhaseDepthFoldedCases) alphaLeft := by
  apply CodeRel.eliminate nestedPhaseDepthFoldedCases alphaLeft
  intro tag valid
  change ElimSelectionRel nestedPhaseDepthValidCase alphaLeft
    (some alphaLeft)
  exact .some nestedAlphaLeftStructuralRefl

def nestedParentPhaseResult :
    ScopedCodePhaseResult nestedPhaseDepthValidCase alphaFoldScopeIndex
      (.cases nestedPhaseDepthRecursiveCases) alphaLeft := {
  factor := .threePhase {
    structuralMiddle := .cases nestedPhaseDepthStructuralCases
    alphaMiddle := .cases nestedPhaseDepthFoldedCases
    structuralBefore := nestedParentStructuralBefore
    alphaForward := nestedParentAlphaForward
    alphaBackward := nestedParentAlphaBackward
    structuralAfter := nestedParentStructuralAfter
  }
  targetRefl := nestedAlphaLeftStructuralRefl
  targetAlpha := alphaLeftAlphaBireflexiveAtFoldScope
}

/-- The original nested fixture now has an honest two-round trace: one round
for recursive alternative traversal and one for the parent simplifier. -/
def nestedPhaseDepthTrace :
    ScopedCodePhaseTrace nestedPhaseDepthValidCase alphaFoldScopeIndex
      nestedPhaseDepthCode alphaLeft :=
  nestedPhaseDepthRecursiveTrace.append nestedParentPhaseResult.trace

#guard nestedPhaseDepthTrace.rounds == 2

theorem nestedPhaseDepthTraced :
    ScopedCodePhaseTraced nestedPhaseDepthValidCase alphaFoldScopeIndex
      nestedPhaseDepthCode alphaLeft :=
  nestedPhaseDepthTrace.traced

/-- Concrete phase-aware case boundary for the compiler's combined
fold-and-eliminate result. -/
theorem alphaSingletonFoldPhaseBoundaryAt :
    ScopedCaseBoundaryAt
      (ScopedCodePhaseResultOnAlphaReflexive alphaSingletonFoldValidCase)
      alphaFoldScopeIndex 1 alphaSingletonFoldCases alphaLeft := by
  intro run reflexive
  exact ⟨alphaSingletonFoldPhaseResult⟩

def nestedAlphaSingletonFoldCode : LCNF.Code .impure :=
  .setTag c 7 alphaSingletonFoldCode

def nestedAlphaSingletonFoldExpected : LCNF.Code .impure :=
  .setTag c 7 alphaLeft

theorem nestedAlphaSingletonFoldAlphaBireflexive :
    ScopedAlphaBireflexive alphaFoldScopeIndex
      nestedAlphaSingletonFoldCode := {
  forward := .setTag cRelatedAtFoldScope
    alphaSingletonFoldAlphaBireflexive.forward
  backward := .setTag cRelatedAtFoldScope
    alphaSingletonFoldAlphaBireflexive.backward
}

#guard shadowCode? 3 nestedAlphaSingletonFoldCode ==
  some nestedAlphaSingletonFoldExpected

/-- The actual three-phase singleton kernel now crosses surrounding recursive
syntax through the generic phase traversal laws. -/
theorem nestedAlphaSingletonFoldPhaseFactored :
    ScopedCodePhaseFactored alphaSingletonFoldValidCase alphaFoldScopeIndex
      nestedAlphaSingletonFoldCode nestedAlphaSingletonFoldExpected := by
  have related : ScopedCodePhaseResultOnAlphaReflexive
      alphaSingletonFoldValidCase alphaFoldScopeIndex
      nestedAlphaSingletonFoldCode nestedAlphaSingletonFoldExpected :=
    scopedCodePhaseResultOnAlphaReflexive_traversalLaws.setTag
      (fun _ => ⟨alphaSingletonFoldPhaseResult⟩)
  rcases related nestedAlphaSingletonFoldAlphaBireflexive with ⟨result⟩
  exact result.phaseFactored

def mixedPhaseJoinId : FVarId := ⟨`mixedPhaseJoin⟩

def mixedPhaseJoinSource : LCNF.Code .impure :=
  .jp (.mk mixedPhaseJoinId `mixedPhaseJoin #[] objType
    alphaSingletonFoldCode) (.unreach objType)

def mixedPhaseJoinTarget : LCNF.Code .impure :=
  .jp (.mk mixedPhaseJoinId `mixedPhaseJoin #[] objType alphaLeft)
    (.unreach objType)

theorem mixedPhaseJoinFresh :
    FreshJoinBinder mixedPhaseJoinId [x, c] [] := by
  constructor
  · intro old oldScoped
    simp at oldScoped
    rcases oldScoped with oldIsX | oldIsC
    · have oldEq : old = x := fvar_eq_of_beq oldIsX
      subst old
      native_decide
    · have oldEq : old = c := fvar_eq_of_beq oldIsC
      subst old
      native_decide
  · intro old oldScoped
    simp at oldScoped

theorem mixedPhaseJoinAlphaBireflexive :
    ScopedAlphaBireflexive alphaFoldScopeIndex mixedPhaseJoinSource := {
  forward := .jp mixedPhaseJoinFresh mixedPhaseJoinFresh
    (.nil alphaSingletonFoldAlphaBireflexive.forward)
    (.terminal .unreachable)
  backward := .jp mixedPhaseJoinFresh mixedPhaseJoinFresh
    (.nil alphaSingletonFoldAlphaBireflexive.backward)
    (.terminal .unreachable)
}

#guard shadowCode? 3 mixedPhaseJoinSource == some mixedPhaseJoinTarget

/-- Mixed-schedule regression: the join body needs three phases while its
unchanged continuation starts with a two-phase identity. Target structural
identity pads the continuation and lets the generic `jp` law combine them. -/
theorem mixedPhaseJoinFactored :
    ScopedCodePhaseFactored alphaSingletonFoldValidCase alphaFoldScopeIndex
      mixedPhaseJoinSource mixedPhaseJoinTarget := by
  have body : ScopedCodePhaseResultOnAlphaReflexive
      alphaSingletonFoldValidCase
      (alphaFoldScopeIndex.pushParams #[])
      alphaSingletonFoldCode alphaLeft := by
    unfold ScopedCodePhaseResultOnAlphaReflexive
    simpa [ScopeIndex.pushParams, ScopeIndex.pushParamList] using
      (fun _ => ⟨alphaSingletonFoldPhaseResult⟩)
  have continuation : ScopedCodePhaseResultOnAlphaReflexive
      alphaSingletonFoldValidCase
      (alphaFoldScopeIndex.pushJoin mixedPhaseJoinId)
      (.unreach objType) (.unreach objType) :=
    scopedCodePhaseResultOnAlphaReflexive_traversalLaws.unreach
      (alphaFoldScopeIndex.pushJoin mixedPhaseJoinId) objType
  have related : ScopedCodePhaseResultOnAlphaReflexive
      alphaSingletonFoldValidCase alphaFoldScopeIndex
      mixedPhaseJoinSource mixedPhaseJoinTarget :=
    scopedCodePhaseResultOnAlphaReflexive_traversalLaws.jp body continuation
  rcases related mixedPhaseJoinAlphaBireflexive with ⟨result⟩
  exact result.phaseFactored

/-- Unequal-depth trace regression: the join body carries a real phase round
plus one padded round, while the unchanged continuation carries one round.
The generic join-point trace law pads only the continuation before zipping. -/
theorem mixedDepthJoinTraced :
    ScopedCodePhaseTraced alphaSingletonFoldValidCase alphaFoldScopeIndex
      mixedPhaseJoinSource mixedPhaseJoinTarget := by
  have body : ScopedCodePhaseTracedOnAlphaReflexive
      alphaSingletonFoldValidCase
      (alphaFoldScopeIndex.pushParams #[])
      alphaSingletonFoldCode alphaLeft := by
    intro _
    simpa [ScopeIndex.pushParams, ScopeIndex.pushParamList] using
      alphaSingletonFoldPaddedTrace.traced
  have continuation : ScopedCodePhaseTracedOnAlphaReflexive
      alphaSingletonFoldValidCase
      (alphaFoldScopeIndex.pushJoin mixedPhaseJoinId)
      (.unreach objType) (.unreach objType) :=
    scopedCodePhaseTracedOnAlphaReflexive_of_result
      (scopedCodePhaseResultOnAlphaReflexive_traversalLaws.unreach
        (alphaFoldScopeIndex.pushJoin mixedPhaseJoinId) objType)
  exact (scopedCodePhaseTracedOnAlphaReflexive_traversalLaws.jp
    body continuation) mixedPhaseJoinAlphaBireflexive

theorem selectedBranchAlphaBireflexiveAtFoldScope :
    ScopedAlphaBireflexive alphaFoldScopeIndex selectedBranch := {
  forward := .terminal (.ret ⟨by native_decide, by native_decide,
    fVarRelated_insert_self
      (({} : FVarIdMap FVarId).insert c c) x x⟩)
  backward := .terminal (.ret ⟨by native_decide, by native_decide,
    fVarRelated_insert_self
      (({} : FVarIdMap FVarId).insert c c) x x⟩)
}

def singletonDefaultValidCase
    (_ : LCNF.Cases .impure) (_ : Nat) : Prop :=
  True

/-- Non-vacuous canonical-validity regression: the default arm is a reachable
selection for every runtime tag. -/
theorem singletonDefaultReachableCaseTag (tag : Nat) :
    ReachableCaseTag singletonDefaultCases tag := by
  exact ⟨selectedBranch, by rfl, by rfl⟩

def singletonDefaultScopedCodeFactor :
    ScopedCodeBifactor singletonDefaultValidCase alphaFoldScopeIndex
      selectedBranch selectedBranch := {
  middle := selectedBranch
  structural := .aligned (.return x)
  alphaForward := selectedBranchAlphaBireflexiveAtFoldScope.forward
  alphaBackward := selectedBranchAlphaBireflexiveAtFoldScope.backward
}

theorem singletonDefaultAltsFactored :
    ScopedAltsFactored singletonDefaultValidCase alphaFoldScopeIndex
      singletonDefaultCases.alts.toList singletonDefaultCases.alts.toList :=
  .cons (.default singletonDefaultScopedCodeFactor.factored) .nil

/-- A nonempty regression for existential intermediate materialization. -/
theorem singletonDefaultAltsMaterialized :
    Nonempty (ScopedAltsBifactor singletonDefaultValidCase
      alphaFoldScopeIndex singletonDefaultCases.alts.toList
      singletonDefaultCases.alts.toList) :=
  scopedAltsBifactor_of_factored singletonDefaultAltsFactored

theorem singletonDefaultPrepared_eq :
    shadowPrepareAlts singletonDefaultCases = singletonDefaultCases.alts := by
  rfl

/-- Pointwise endpoint identities available after recursive traversal of the
singleton default table, instantiated at canonical reachable validity. -/
def singletonDefaultReachableAltsIdentity :
    ScopedAltsPhaseResult ReachableCaseTag alphaFoldScopeIndex
      singletonDefaultCases.alts.toList
      singletonDefaultCases.alts.toList :=
  .default
    (.identity (.aligned (.return x))
      selectedBranchAlphaBireflexiveAtFoldScope)
    .nil

/-- The generic direct-singleton theorem reconstructs convergence without a
fixture-specific convergence assumption. -/
theorem singletonDefaultDirectConvergenceDerived :
    Nonempty (ScopedSingletonSelectionConvergence ReachableCaseTag
      alphaFoldScopeIndex singletonDefaultCases
      (shadowFilterUnreachable singletonDefaultCases.alts)[0]!.getCode) :=
  scopedDirectSingletonSelectionConvergence
    reachableCaseTag_selectionLaws singletonDefaultReachableAltsIdentity
    (by rfl)

def singletonDefaultSelectionConvergence :
    ScopedSingletonSelectionConvergence singletonDefaultValidCase
      alphaFoldScopeIndex singletonDefaultCases selectedBranch := {
  middle := selectedBranch
  structuralSelected := by
    intro tag valid
    change ElimSelectionRel singletonDefaultValidCase selectedBranch
      (some selectedBranch)
    exact .some (.aligned (.return x))
  alphaForward := selectedBranchAlphaBireflexiveAtFoldScope.forward
  alphaBackward := selectedBranchAlphaBireflexiveAtFoldScope.backward
}

def singletonDefaultDirectPhaseEvidence :
    ScopedSingletonPhaseEvidence singletonDefaultValidCase
      alphaFoldScopeIndex singletonDefaultCases selectedBranch :=
  .direct singletonDefaultSelectionConvergence

theorem singletonDefaultTargetIdentities :
    ScopedCodeTargetIdentities singletonDefaultValidCase
      alphaFoldScopeIndex selectedBranch := {
  structural := singletonDefaultScopedCodeFactor.structural
  alpha := selectedBranchAlphaBireflexiveAtFoldScope
}

def singletonDefaultPhaseResultEvidence :
    ScopedSingletonPhaseResultEvidence singletonDefaultValidCase
      alphaFoldScopeIndex singletonDefaultCases selectedBranch := {
  phase := singletonDefaultDirectPhaseEvidence
  identities := singletonDefaultTargetIdentities
}

/-- Direct singleton witness through the same phase-shape packaging used by
fold-created singletons. -/
def singletonDefaultPhaseShapeResult :
    ScopedCodePhaseResult singletonDefaultValidCase alphaFoldScopeIndex
      singletonDefaultCode selectedBranch :=
  singletonDefaultPhaseResultEvidence.result

theorem singletonDefaultDirectPhaseFactored :
    ScopedCodePhaseFactored singletonDefaultValidCase alphaFoldScopeIndex
      singletonDefaultCode selectedBranch :=
  singletonDefaultDirectPhaseEvidence.phaseFactored

theorem singletonDefaultPreparedSelectionConverges :
    Nonempty (ScopedSingletonSelectionConvergence singletonDefaultValidCase
      alphaFoldScopeIndex singletonDefaultCases
      (shadowPrepareAlts singletonDefaultCases)[0]!.getCode) := by
  rw [singletonDefaultPrepared_eq]
  exact ⟨singletonDefaultSelectionConvergence⟩

theorem singletonDefaultAddDefaultSelectionEvidence :
    ScopedAddDefaultSelectionEvidence alphaFoldScopeIndex
      singletonDefaultCases.alts singletonDefaultCases.alts := by
  apply scopedAddDefaultSelectionEvidence_of_eq
    (shadowAddDefaultAlt_eq_of_small (by
      simp [singletonDefaultCases, LCNF.Cases.alts]))
  · exact .cons
      (.default selectedBranchAlphaBireflexiveAtFoldScope.forward) .nil
  · exact .cons
      (.default selectedBranchAlphaBireflexiveAtFoldScope.backward) .nil

theorem retainedIdentityAlphaBireflexive :
    ScopedAlphaBireflexive alphaFoldScopeIndex
      (.cases alphaSingletonStructuralCases) := by
  constructor
  · apply CodeRelated.cases cRelatedAtFoldScope
    intro tag
    exact chooseAlt_related (.cons
      (.ctor alphaLeftAlphaBireflexiveAtFoldScope.forward)
      (.cons (.default alphaRightAlphaBireflexiveAtFoldScope.forward) .nil))
  · apply CodeRelated.cases cRelatedAtFoldScope
    intro tag
    exact chooseAlt_related (.cons
      (.ctor alphaLeftAlphaBireflexiveAtFoldScope.backward)
      (.cons (.default alphaRightAlphaBireflexiveAtFoldScope.backward) .nil))

theorem retainedIdentityStructuralRefl :
    CodeRel nestedPhaseDepthValidCase
      (.cases alphaSingletonStructuralCases)
      (.cases alphaSingletonStructuralCases) := by
  apply CodeRel.aligned
  apply HeadRel.cases
  intro tag valid
  exact structuralChooseAlt_related (.cons
    (.ctor nestedAlphaLeftStructuralRefl)
    (.cons (.default nestedAlphaRightStructuralRefl) .nil))

theorem retainedIdentityTargetIdentities :
    ScopedCodeTargetIdentities nestedPhaseDepthValidCase alphaFoldScopeIndex
      (.cases alphaSingletonStructuralCases) := {
  structural := retainedIdentityStructuralRefl
  alpha := retainedIdentityAlphaBireflexive
}

theorem retainedIdentityFilter_eq :
    shadowFilterUnreachable alphaSingletonStructuralCases.alts =
      alphaSingletonStructuralCases.alts := by
  rfl

theorem retainedIdentityAddDefault_eq :
    shadowAddDefaultAlt alphaSingletonStructuralCases.alts =
      alphaSingletonStructuralCases.alts := by
  apply shadowAddDefaultAlt_eq_of_hasDefault
  native_decide

theorem retainedIdentityPreparedCases_eq :
    alphaSingletonStructuralCases.updateAlts
      (shadowAddDefaultAlt
        (shadowFilterUnreachable alphaSingletonStructuralCases.alts)) =
      alphaSingletonStructuralCases := by
  rw [retainedIdentityFilter_eq, retainedIdentityAddDefault_eq]
  rfl

def retainedIdentityPhaseEvidence :
    ScopedRetainedPhaseEvidence nestedPhaseDepthValidCase alphaFoldScopeIndex
      alphaSingletonStructuralCases alphaSingletonStructuralCases.alts := {
  middleAlts := alphaSingletonStructuralCases.alts
  structuralSelected := by
    intro tag valid
    exact structuralChooseAlt_related (.cons
      (.ctor nestedAlphaLeftStructuralRefl)
      (.cons (.default nestedAlphaRightStructuralRefl) .nil))
  folded := by
    rw [retainedIdentityFilter_eq]
    exact scopedAddDefaultSelectionEvidence_of_eq
      retainedIdentityAddDefault_eq
      (.cons (.ctor alphaLeftAlphaBireflexiveAtFoldScope.forward)
        (.cons (.default alphaRightAlphaBireflexiveAtFoldScope.forward) .nil))
      (.cons (.ctor alphaLeftAlphaBireflexiveAtFoldScope.backward)
        (.cons (.default alphaRightAlphaBireflexiveAtFoldScope.backward) .nil))
}

def retainedIdentityPhaseResultEvidence :
    ScopedRetainedPhaseResultEvidence nestedPhaseDepthValidCase
      alphaFoldScopeIndex alphaSingletonStructuralCases
      alphaSingletonStructuralCases.alts := {
  phase := retainedIdentityPhaseEvidence
  identities := by
    rw [retainedIdentityPreparedCases_eq]
    exact retainedIdentityTargetIdentities
}

/-- Retained-table witness through the phase-shape packaging. Filtering and
default insertion are both transparently inert for this constructor/default
table. -/
def retainedIdentityPhaseShapeResult :
    ScopedCodePhaseResult nestedPhaseDepthValidCase alphaFoldScopeIndex
      (.cases alphaSingletonStructuralCases)
      (.cases alphaSingletonStructuralCases) := by
  simpa only [retainedIdentityPreparedCases_eq] using
    retainedIdentityPhaseResultEvidence.result
      retainedIdentityAlphaBireflexive

/-- The traversal index reconstructs the declaration-body scope from its
parameters in the same order as `ParamBodyRelated`. -/
theorem alphaFoldScopeIndex_fromParams :
    ScopeIndex.empty.pushParams #[param c, param x] = alphaFoldScopeIndex := by
  rfl

def alphaFoldScopedCodeFactor :
    ScopedCodeBifactor alphaFoldValidCase alphaFoldScopeIndex
      alphaFoldCode alphaFoldExpected := {
  middle := alphaFoldIntermediate
  structural := alphaFoldStructuralCodeRelated
  alphaForward := alphaFoldCasesAlphaForward
  alphaBackward := alphaFoldCasesAlphaBackward
}

/-- The alpha-default fixture through the selection-local admissibility
interface used by the universal case-kernel theorem. -/
def alphaFoldAlignedEvidence :
    ScopedAlignedCaseEvidence alphaFoldValidCase alphaFoldScopeIndex
      alphaFoldBeforeCases alphaFoldAfterCases := {
  middleAlts := alphaFoldIntermediateCases.alts
  structuralSelected := by
    intro tag valid
    rcases valid with ⟨_, rfl⟩
    change SelectionRel alphaFoldValidCase (some alphaRight) (some alphaRight)
    exact .some alphaFoldRightStructuralRefl
  alphaForwardDiscr :=
    codeRelated_cases_discr
      (left := alphaFoldIntermediateCases) (right := alphaFoldAfterCases)
      alphaFoldCasesAlphaForward
  alphaForwardSelected :=
    codeRelated_cases_selected alphaFoldCasesAlphaForward
  alphaBackwardDiscr :=
    codeRelated_cases_discr
      (left := alphaFoldAfterCases) (right := alphaFoldIntermediateCases)
      alphaFoldCasesAlphaBackward
  alphaBackwardSelected :=
    codeRelated_cases_selected alphaFoldCasesAlphaBackward
}

/-- Once the private/default-fold output equation is supplied, the new phase
interface reconstructs every selected-branch alpha obligation from the
existing declarative case proofs. -/
theorem alphaFoldAddDefaultSelectionEvidence_of_output
    (output : shadowAddDefaultAlt
      (shadowFilterUnreachable alphaFoldBeforeCases.alts) =
        alphaFoldAfterCases.alts) :
    ScopedAddDefaultSelectionEvidence alphaFoldScopeIndex
      alphaFoldIntermediateCases.alts
      (shadowFilterUnreachable alphaFoldBeforeCases.alts) := {
  forward := by
    intro tag
    rw [output]
    exact codeRelated_cases_selected alphaFoldCasesAlphaForward tag
  backward := by
    intro tag
    rw [output]
    exact codeRelated_cases_selected alphaFoldCasesAlphaBackward tag
}

/-- The complete retained-table phase witness for the alpha-fold fixture. Its
sole premise is the private output equation isolated above. -/
def alphaFoldRetainedPhaseEvidence_of_output
    (output : shadowAddDefaultAlt
      (shadowFilterUnreachable alphaFoldBeforeCases.alts) =
        alphaFoldAfterCases.alts) :
    ScopedRetainedPhaseEvidence alphaFoldValidCase alphaFoldScopeIndex
      alphaFoldBeforeCases alphaFoldBeforeCases.alts := {
  middleAlts := alphaFoldIntermediateCases.alts
  structuralSelected := alphaFoldAlignedEvidence.structuralSelected
  folded := alphaFoldAddDefaultSelectionEvidence_of_output output
}

theorem alphaFoldCaseFactorEvidence :
    ScopedCaseFactorEvidence alphaFoldValidCase alphaFoldScopeIndex
      alphaFoldBeforeCases alphaFoldExpected :=
  .aligned alphaFoldAlignedEvidence

theorem alphaFoldAdmissibilityFactor :
    ScopedCodeFactored alphaFoldValidCase alphaFoldScopeIndex
      alphaFoldCode alphaFoldExpected :=
  alphaFoldCaseFactorEvidence.factored

#guard shadowCode? 2 alphaFoldCode == some alphaFoldExpected

/-- Unlike the old scope-free `CaseBoundarySound`, the scoped case contract
can state this structural-then-alpha result directly. -/
theorem alphaFoldScopedCaseBoundary :
    ScopedCaseBoundaryAt (ScopedCodeFactored alphaFoldValidCase)
      alphaFoldScopeIndex 1 alphaFoldBeforeCases alphaFoldExpected := by
  intro run
  exact alphaFoldScopedCodeFactor.factored

/-- The concrete case factor, exposed through the hygiene-indexed relation
consumed by generic recursive traversal. -/
theorem alphaFoldFactoredOnAlphaReflexive :
    ScopedCodeFactoredOnAlphaReflexive alphaFoldValidCase alphaFoldScopeIndex
      alphaFoldCode alphaFoldExpected := by
  intro reflexive
  exact alphaFoldScopedCodeFactor.factored

def nestedAlphaFoldCode : LCNF.Code .impure :=
  .setTag x 0 alphaFoldCode

def nestedAlphaFoldExpected : LCNF.Code .impure :=
  .setTag x 0 alphaFoldExpected

def nestedAlphaFoldIntermediate : LCNF.Code .impure :=
  .setTag x 0 alphaFoldIntermediate

#guard shadowCode? 3 nestedAlphaFoldCode == some nestedAlphaFoldExpected

/-- A non-case parent lifts the alpha-changing case factor through the proved
generic closure laws. Alpha reflexivity supplies the scoped `setTag` operand
when this relation is consumed. -/
theorem nestedAlphaFoldScopedTraversal :
    ScopedCodeFactoredOnAlphaReflexive alphaFoldValidCase alphaFoldScopeIndex
      nestedAlphaFoldCode nestedAlphaFoldExpected := by
  exact scopedCodeFactoredOnAlphaReflexive_traversalLaws.setTag
    alphaFoldFactoredOnAlphaReflexive

/-!
Hygiene alone cannot justify a universal case boundary for an unconstrained
phase predicate. An empty case table is alpha-reflexive, but declaring every
tag valid makes its simplification to `unreach` impossible to justify through
`CodeRel.eliminate`: there is no source arm to select.
-/

def emptyCaseTable : LCNF.Cases .impure :=
  .mk `Empty objType c #[]

/-- Canonical validity rejects every tag for a genuinely empty source table. -/
theorem emptyCaseNotReachableCaseTag (tag : Nat) :
    ¬ ReachableCaseTag emptyCaseTable tag := by
  simp [ReachableCaseTag, emptyCaseTable, LCNF.Cases.alts, chooseAlt,
    findCtorAlt, findDefaultAlt]

def emptyCaseScopeIndex : ScopeIndex := {
  forwardRho := {}
  backwardRho := {}
  forwardEmpty := resolverEquivalent_refl {}
  backwardEmpty := resolverEquivalent_refl {}
  sourceScope := [c]
  targetScope := [c]
  scopesEq := rfl
  sourceJoins := []
  targetJoins := []
  joinsEq := rfl
}

def everyCaseTagValid (_ : LCNF.Cases .impure) (_ : Nat) : Prop :=
  True

theorem emptyCaseAlphaBireflexive :
    ScopedAlphaBireflexive emptyCaseScopeIndex (.cases emptyCaseTable) := by
  constructor
  · apply CodeRelated.cases
    · exact ⟨by rfl, by rfl, by rfl⟩
    · intro tag
      exact .none
  · apply CodeRelated.cases
    · exact ⟨by rfl, by rfl, by rfl⟩
    · intro tag
      exact .none

theorem emptyCaseAlphaTree :
    ScopedAlphaBireflexiveTree emptyCaseScopeIndex
      (.cases emptyCaseTable) :=
  .cases emptyCaseAlphaBireflexive .nil

theorem emptyCaseAddDefaultSelectionEvidence :
    ScopedAddDefaultSelectionEvidence emptyCaseScopeIndex
      emptyCaseTable.alts emptyCaseTable.alts :=
  scopedAddDefaultSelectionEvidence_of_eq
    (shadowAddDefaultAlt_eq_of_small (by
      simp [emptyCaseTable, LCNF.Cases.alts])) .nil .nil

theorem emptyCaseShadowRun :
    shadowCode? 1 (.cases emptyCaseTable) = some (.unreach objType) := by
  rfl

theorem emptyCaseNotFactored :
    ¬ ScopedCodeFactored everyCaseTagValid emptyCaseScopeIndex
      (.cases emptyCaseTable) (.unreach objType) := by
  rintro ⟨⟨middle, structural, alphaForward, alphaBackward⟩⟩
  have middleUnreach : ∃ type, middle = .unreach type := by
    cases alphaForward with
    | terminal related =>
        cases related with
        | unreachable => exact ⟨_, rfl⟩
  rcases middleUnreach with ⟨type, rfl⟩
  cases structural with
  | aligned related => cases related
  | eliminate cases target selected =>
      have impossible := selected 0 trivial
      have noSelection :
          chooseAlt 0 emptyCaseTable.alts.toList = none := by rfl
      rw [noSelection] at impossible
      cases impossible

/-- Regression for the missing phase premise: the proposed unconditional
boundary is refutable in the kernel, not merely difficult to prove. -/
theorem scopedCaseBoundaryNotUnconditional :
    ¬ ScopedCaseBoundarySound
      (ScopedCodeFactoredOnAlphaReflexive everyCaseTagValid) := by
  intro boundary
  have factored := boundary 0 emptyCaseScopeIndex emptyCaseTable
    (.unreach objType) emptyCaseShadowRun emptyCaseAlphaBireflexive
  exact emptyCaseNotFactored factored

/-- Full syntactic hygiene covers every arm, but it cannot manufacture a
selected arm for an inconsistent phase predicate. -/
theorem scopedCaseBoundaryTreeNotUnconditional :
    ¬ ScopedCaseBoundarySound
      (ScopedCodeFactoredOnAlphaTree everyCaseTagValid) := by
  intro boundary
  have factored := boundary 0 emptyCaseScopeIndex emptyCaseTable
    (.unreach objType) emptyCaseShadowRun emptyCaseAlphaTree
  exact emptyCaseNotFactored factored

def noCaseTagValid (_ : LCNF.Cases .impure) (_ : Nat) : Prop :=
  False

/-- The deliberately empty phase predicate refines canonical selection. -/
theorem noCaseReachableSelectionLaws :
    ScopedCaseReachableSelectionLaws noCaseTagValid where
  selected := by
    intro _ _ impossible
    exact False.elim impossible

/-- Concrete empty-selection component derived through the generic reachable
selection theorem, rather than supplied directly. -/
theorem noCaseEmptySelectionLaws :
    ScopedCaseEmptySelectionLaws noCaseTagValid :=
  scopedCaseEmptySelectionLaws_of_reachableSelection
    noCaseReachableSelectionLaws

theorem emptyCaseAltsFactored :
    ScopedAltsFactored noCaseTagValid emptyCaseScopeIndex
      emptyCaseTable.alts.toList emptyCaseTable.alts.toList :=
  .nil

theorem emptyCaseAltsMaterialized :
    Nonempty (ScopedAltsBifactor noCaseTagValid emptyCaseScopeIndex
      emptyCaseTable.alts.toList emptyCaseTable.alts.toList) :=
  scopedAltsBifactor_of_factored emptyCaseAltsFactored

/-- Empty-output regression: phase validity alone rules out every source tag;
the generic constructor supplies the fixed `unreach` intermediate. -/
theorem emptyCaseDerivedEliminationEvidence :
    Nonempty (ScopedEliminatedCaseEvidence noCaseTagValid
      emptyCaseScopeIndex emptyCaseTable (.unreach objType)) :=
  scopedEmptyCaseEvidence_of_noValid
    (noCaseEmptySelectionLaws.empty (by rfl))

theorem emptyCaseFactoredFromNoValid :
    ScopedCodeFactored noCaseTagValid emptyCaseScopeIndex
      (.cases emptyCaseTable) (.unreach objType) := by
  rcases emptyCaseDerivedEliminationEvidence with ⟨evidence⟩
  exact evidence.factored

/-- The same kernel result becomes admissible when the phase predicate makes
the empty source table unreachable. -/
def emptyCaseEliminationEvidence :
    ScopedEliminatedCaseEvidence noCaseTagValid emptyCaseScopeIndex
      emptyCaseTable (.unreach objType) := {
  middle := .unreach objType
  structuralSelected := by
    intro tag impossible
    exact False.elim impossible
  alphaForward := .terminal .unreachable
  alphaBackward := .terminal .unreachable
}

/-- Empty-table witness through the automatic unreachable endpoint
identities used by the phase-shape assembly. -/
def emptyCasePhaseShapeResult :
    ScopedCodePhaseResult noCaseTagValid emptyCaseScopeIndex
      (.cases emptyCaseTable) (.unreach objType) :=
  emptyCaseEliminationEvidence.phaseResult
    (scopedUnreachTargetIdentities noCaseTagValid emptyCaseScopeIndex objType)

theorem emptyCaseFactoredWithPhaseEvidence :
    ScopedCodeFactored noCaseTagValid emptyCaseScopeIndex
      (.cases emptyCaseTable) (.unreach objType) :=
  emptyCaseEliminationEvidence.factored

def nestedEmptyCaseCode : LCNF.Code .impure :=
  .setTag c 0 (.cases emptyCaseTable)

def nestedEmptyCaseExpected : LCNF.Code .impure :=
  .setTag c 0 (.unreach objType)

theorem nestedEmptyCaseAlphaTree :
    ScopedAlphaBireflexiveTree emptyCaseScopeIndex nestedEmptyCaseCode :=
  .setTag {
    forward := .setTag ⟨by rfl, by rfl, by rfl⟩
      emptyCaseAlphaBireflexive.forward
    backward := .setTag ⟨by rfl, by rfl, by rfl⟩
      emptyCaseAlphaBireflexive.backward
  } emptyCaseAlphaTree

/-- Complete source certificate for the empty case, including the vacuous
selector-normalization and branch-side obligations. -/
theorem emptyCaseTargetCertificate :
    ScopedCodeTargetCertificate noCaseTagValid emptyCaseScopeIndex
      (.cases emptyCaseTable) := by
  have normalization : CaseTableNormalizationInvariant emptyCaseTable.alts := by
    constructor
    constructor
    · intro tag left right leftHas rightHas
      simp [HasCtorAlt, emptyCaseTable, LCNF.Cases.alts] at leftHas
    · intro left right leftHas rightHas
      simp [HasDefaultAlt, emptyCaseTable, LCNF.Cases.alts] at leftHas
  refine {
    structural := ?_
    alpha := emptyCaseAlphaBireflexive
    side := ?_
    canonical := .cases (by
      intro alt member
      simp [emptyCaseTable, LCNF.Cases.alts] at member)
  }
  · apply CodeRel.aligned
    apply HeadRel.cases
    intro tag valid
    exact .none
  · unfold ScopedCodeSideReflexive
    apply CodeSideConditions.cases
    · native_decide
    · native_decide
    · exact normalization
    · exact normalization
    · intro tag left right leftHas rightHas
      simp [HasCtorAlt, emptyCaseTable, LCNF.Cases.alts] at leftHas
    · intro left right leftHas rightHas
      simp [HasDefaultAlt, emptyCaseTable, LCNF.Cases.alts] at leftHas

/-- The enclosing instruction preserves the complete source certificate. -/
theorem nestedEmptyCaseTargetCertificate :
    ScopedCodeTargetCertificate noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode := by
  refine {
    structural := .aligned (.setTag c 0 emptyCaseTargetCertificate.structural)
    alpha := nestedEmptyCaseAlphaTree.root
    side := ?_
    canonical := .setTag emptyCaseTargetCertificate.canonical
  }
  exact .setTag (by native_decide) (by native_decide)
    emptyCaseTargetCertificate.side

theorem nestedEmptyCaseCertificateTree :
    ScopedCodeTargetCertificateTree noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode :=
  .setTag nestedEmptyCaseTargetCertificate
    (.cases emptyCaseTargetCertificate .nil)

theorem nestedEmptyCaseShadowRun :
    shadowCode? 2 nestedEmptyCaseCode = some nestedEmptyCaseExpected := by
  rfl

/-- Regression for the certified arbitrary-depth endpoint: every ordinary
phase round is retained, while the actual transformed target carries the full
side certificate. -/
theorem nestedEmptyCaseEndpointCertified
    (phases : ScopedLocalCaseCertifiedPhaseLaws noCaseTagValid) :
    Nonempty (ScopedCodePhaseEndpointCertifiedTrace noCaseTagValid
      emptyCaseScopeIndex nestedEmptyCaseCode nestedEmptyCaseExpected) :=
  shadowCode_scopedPhaseEndpointCertifiedTree phases
    nestedEmptyCaseCertificateTree nestedEmptyCaseShadowRun

/-- Regression for the full assembly path: independently supplied case-shape
laws cross a non-case parent and discharge a recursive shadow run. -/
theorem nestedEmptyCaseFactored_of_shapes
    (shapes : ScopedCaseShapeLaws noCaseTagValid) :
    ScopedCodeFactored noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode nestedEmptyCaseExpected :=
  shadowCode_scopedFactoredTree_of_shapes shapes nestedEmptyCaseAlphaTree
    nestedEmptyCaseShadowRun

/-- The recursive empty-table regression through the phase-aware shape
assembly, with no direct `ScopedLocalCasePhaseLaws` premise. -/
theorem nestedEmptyCaseTraced_of_phaseShapes
    (shapes : ScopedCasePhaseShapeLaws noCaseTagValid) :
    ScopedCodePhaseTraced noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode nestedEmptyCaseExpected :=
  shadowCode_scopedPhaseTracedTree_of_phaseShapes shapes
    nestedEmptyCaseAlphaTree nestedEmptyCaseShadowRun

/-- Regression for the unbundled assembly API. The four local obligations
remain separate all the way to the recursive trace theorem. -/
theorem nestedEmptyCaseTraced_of_phaseComponents
    (emptySelection : ScopedCaseEmptySelectionLaws noCaseTagValid)
    (singletonPhases : ScopedCaseSingletonPhaseLaws noCaseTagValid)
    (retainedPhases : ScopedCaseRetainedPhaseLaws noCaseTagValid)
    (targetIdentities :
      ScopedCasePhaseTargetIdentityLaws noCaseTagValid) :
    ScopedCodePhaseTraced noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode nestedEmptyCaseExpected :=
  shadowCode_scopedPhaseTracedTree_of_phaseComponents emptySelection
    singletonPhases retainedPhases targetIdentities nestedEmptyCaseAlphaTree
    nestedEmptyCaseShadowRun

/-- The same recursive regression after discharging the empty component from
reachable-selection refinement. Only the three nonempty-output components
remain as premises. -/
theorem nestedEmptyCaseTraced_of_reachableSelection
    (singletonPhases : ScopedCaseSingletonPhaseLaws noCaseTagValid)
    (retainedPhases : ScopedCaseRetainedPhaseLaws noCaseTagValid)
    (targetIdentities :
      ScopedCasePhaseTargetIdentityLaws noCaseTagValid) :
    ScopedCodePhaseTraced noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode nestedEmptyCaseExpected :=
  shadowCode_scopedPhaseTracedTree_of_reachableSelection
    noCaseReachableSelectionLaws singletonPhases retainedPhases
    targetIdentities nestedEmptyCaseAlphaTree nestedEmptyCaseShadowRun

/-- Reduced recursive endpoint after the ordinary direct-singleton path has
also been derived. Only genuine folded singletons remain as singleton input. -/
theorem nestedEmptyCaseTraced_of_foldedSingletons
    (foldedSingletons :
      ScopedCaseFoldedSingletonPhaseLaws noCaseTagValid)
    (retainedPhases : ScopedCaseRetainedPhaseLaws noCaseTagValid)
    (targetIdentities :
      ScopedCasePhaseTargetIdentityLaws noCaseTagValid) :
    ScopedCodePhaseTraced noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode nestedEmptyCaseExpected :=
  shadowCode_scopedPhaseTracedTree_of_foldedSingletons
    noCaseReachableSelectionLaws foldedSingletons retainedPhases
    targetIdentities nestedEmptyCaseAlphaTree nestedEmptyCaseShadowRun

/-- Preferred reduced recursive endpoint: the broad folded-trifactor premise
has been replaced by the fold's selected-branch alpha presentation. -/
theorem nestedEmptyCaseTraced_of_foldedAlpha
    (foldAlpha : ScopedCaseFoldedAlphaLaws noCaseTagValid)
    (retainedPhases : ScopedCaseRetainedPhaseLaws noCaseTagValid)
    (targetIdentities :
      ScopedCasePhaseTargetIdentityLaws noCaseTagValid) :
    ScopedCodePhaseTraced noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode nestedEmptyCaseExpected :=
  shadowCode_scopedPhaseTracedTree_of_foldedAlpha
    noCaseReachableSelectionLaws foldAlpha retainedPhases targetIdentities
    nestedEmptyCaseAlphaTree nestedEmptyCaseShadowRun

/-- The same recursive empty-table regression through the reduced two-phase
interface. This path consults neither singleton nor retained folding evidence. -/
theorem nestedEmptyCaseFactored_of_selectionSurvival
    (survival : ScopedCaseSelectionSurvivalLaws noCaseTagValid)
    (retained : ScopedRetainedCaseShapeLaws noCaseTagValid) :
    ScopedCodeFactored noCaseTagValid emptyCaseScopeIndex
      nestedEmptyCaseCode nestedEmptyCaseExpected :=
  shadowCode_scopedFactoredTree_of_selectionSurvival survival retained
    nestedEmptyCaseAlphaTree nestedEmptyCaseShadowRun

theorem alphaFoldParamBodyForward :
    ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param c, param x].toList #[param c, param x].toList
      alphaFoldIntermediate alphaFoldExpected := by
  apply ParamBodyRelated.cons
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · apply ParamBodyRelated.cons
    · exact xFreshForC
    · exact xFreshForC
    · intro old oldScoped; simp at oldScoped
    · intro old oldScoped; simp at oldScoped
    · exact .nil alphaFoldScopedCodeFactor.alphaForward

theorem alphaFoldParamBodyBackward :
    ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param c, param x].toList #[param c, param x].toList
      alphaFoldExpected alphaFoldIntermediate := by
  apply ParamBodyRelated.cons
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · apply ParamBodyRelated.cons
    · exact xFreshForC
    · exact xFreshForC
    · intro old oldScoped; simp at oldScoped
    · intro old oldScoped; simp at oldScoped
    · exact .nil alphaFoldScopedCodeFactor.alphaBackward

theorem alphaFoldProgramsRelatedOfParamBody
    (body : ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param c, param x].toList #[param c, param x].toList leftCode rightCode) :
    ProgramsRelated (alphaFoldProgramWith leftCode)
      (alphaFoldProgramWith rightCode) := by
  intro name
  by_cases isMain : name = `main
  · subst name
    simpa [alphaFoldProgramWith, alphaFoldDeclWith, Program.findDecl?, decl] using
      OptionalProgramDeclRelated.some
        (ProgramDeclRelated.code
          (alphaFoldDeclWith leftCode) (alphaFoldDeclWith rightCode)
          leftCode rightCode body)
  · simpa [alphaFoldProgramWith, alphaFoldDeclWith, Program.findDecl?, decl,
      isMain, Ne.symm isMain] using OptionalProgramDeclRelated.none

theorem alphaSingletonParamBodyForward :
    ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param c, param x].toList #[param c, param x].toList
      (.cases alphaSingletonStructuralCases)
      (.cases alphaSingletonFoldedCases) := by
  apply ParamBodyRelated.cons
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · apply ParamBodyRelated.cons
    · exact xFreshForC
    · exact xFreshForC
    · intro old oldScoped; simp at oldScoped
    · intro old oldScoped; simp at oldScoped
    · exact .nil alphaSingletonAlphaForward

theorem alphaSingletonParamBodyBackward :
    ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param c, param x].toList #[param c, param x].toList
      (.cases alphaSingletonFoldedCases)
      (.cases alphaSingletonStructuralCases) := by
  apply ParamBodyRelated.cons
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · apply ParamBodyRelated.cons
    · exact xFreshForC
    · exact xFreshForC
    · intro old oldScoped; simp at oldScoped
    · intro old oldScoped; simp at oldScoped
    · exact .nil alphaSingletonAlphaBackward

def alphaSingletonBeforeProgram : ImpureProgram :=
  alphaFoldProgramWith alphaSingletonFoldCode

def alphaSingletonStructuralProgram : ImpureProgram :=
  alphaFoldProgramWith (.cases alphaSingletonStructuralCases)

def alphaSingletonAlphaProgram : ImpureProgram :=
  alphaFoldProgramWith (.cases alphaSingletonFoldedCases)

def alphaSingletonAfterProgram : ImpureProgram :=
  alphaFoldProgramWith alphaLeft

theorem alphaSingletonStructuralBeforeProgramsRelated :
    ProgramRelated (CodeRel alphaSingletonFoldValidCase)
      alphaSingletonBeforeProgram alphaSingletonStructuralProgram := by
  exact .cons {
    name_eq := rfl
    levelParams_eq := rfl
    type_eq := rfl
    params_eq := rfl
    safe_eq := rfl
    value := .code alphaSingletonStructuralBefore
    recursive_eq := rfl
    inlineAttr_eq := rfl
  } .nil

theorem alphaSingletonAlphaProgramsBirelated :
    ProgramsBirelated alphaSingletonStructuralProgram
      alphaSingletonAlphaProgram := {
  forward := alphaFoldProgramsRelatedOfParamBody alphaSingletonParamBodyForward
  backward := alphaFoldProgramsRelatedOfParamBody alphaSingletonParamBodyBackward
}

theorem alphaSingletonStructuralAfterProgramsRelated :
    ProgramRelated (CodeRel alphaSingletonFoldValidCase)
      alphaSingletonAlphaProgram alphaSingletonAfterProgram := by
  exact .cons {
    name_eq := rfl
    levelParams_eq := rfl
    type_eq := rfl
    params_eq := rfl
    safe_eq := rfl
    value := .code alphaSingletonStructuralAfter
    recursive_eq := rfl
    inlineAttr_eq := rfl
  } .nil

def alphaSingletonStructuralAlphaStructural :
    StructuralAlphaStructuralPrograms alphaSingletonFoldValidCase
      alphaSingletonBeforeProgram alphaSingletonAfterProgram := {
  structuralMiddle := alphaSingletonStructuralProgram
  alphaMiddle := alphaSingletonAlphaProgram
  structuralBefore := alphaSingletonStructuralBeforeProgramsRelated
  alpha := alphaSingletonAlphaProgramsBirelated
  structuralAfter := alphaSingletonStructuralAfterProgramsRelated
}

/-- Whole-program semantic consumer for the exact folded-singleton
structural/alpha/structural witness. -/
theorem alphaSingletonComposedCorrect :
    SamePhaseCorrectOn (Impure.semantics externals)
      alphaSingletonBeforeProgram alphaSingletonAfterProgram alphaFoldEntries
      (StructuralAlphaStructuralAdmissible externals
        alphaSingletonStructuralAlphaStructural) :=
  structuralAlphaStructuralSamePhaseCorrectOn
    alphaSingletonStructuralAlphaStructural

theorem alphaLeftParamBodyReflexiveForward :
    ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param c, param x].toList #[param c, param x].toList
      alphaLeft alphaLeft := by
  apply ParamBodyRelated.cons
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · apply ParamBodyRelated.cons
    · exact xFreshForC
    · exact xFreshForC
    · intro old oldScoped; simp at oldScoped
    · intro old oldScoped; simp at oldScoped
    · exact .nil alphaLeftAlphaBireflexiveAtFoldScope.forward

theorem alphaLeftParamBodyReflexiveBackward :
    ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param c, param x].toList #[param c, param x].toList
      alphaLeft alphaLeft := by
  apply ParamBodyRelated.cons
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · intro old oldScoped; simp at oldScoped
  · apply ParamBodyRelated.cons
    · exact xFreshForC
    · exact xFreshForC
    · intro old oldScoped; simp at oldScoped
    · intro old oldScoped; simp at oldScoped
    · exact .nil alphaLeftAlphaBireflexiveAtFoldScope.backward

theorem alphaSingletonAfterProgramsStructuralRefl :
    ProgramRelated (CodeRel alphaSingletonFoldValidCase)
      alphaSingletonAfterProgram alphaSingletonAfterProgram := by
  exact .cons {
    name_eq := rfl
    levelParams_eq := rfl
    type_eq := rfl
    params_eq := rfl
    safe_eq := rfl
    value := .code alphaLeftStructuralRefl
    recursive_eq := rfl
    inlineAttr_eq := rfl
  } .nil

theorem alphaSingletonAfterProgramsAlphaBirelated :
    ProgramsBirelated alphaSingletonAfterProgram
      alphaSingletonAfterProgram := {
  forward := alphaFoldProgramsRelatedOfParamBody
    alphaLeftParamBodyReflexiveForward
  backward := alphaFoldProgramsRelatedOfParamBody
    alphaLeftParamBodyReflexiveBackward
}

def alphaSingletonIdentityRound :
    StructuralAlphaStructuralPrograms alphaSingletonFoldValidCase
      alphaSingletonAfterProgram alphaSingletonAfterProgram := {
  structuralMiddle := alphaSingletonAfterProgram
  alphaMiddle := alphaSingletonAfterProgram
  structuralBefore := alphaSingletonAfterProgramsStructuralRefl
  alpha := alphaSingletonAfterProgramsAlphaBirelated
  structuralAfter := alphaSingletonAfterProgramsStructuralRefl
}

def alphaSingletonTwoRoundTrace :
    StructuralAlphaStructuralTrace alphaSingletonFoldValidCase
      alphaSingletonBeforeProgram alphaSingletonAfterProgram :=
  .trans alphaSingletonStructuralAlphaStructural
    (.single alphaSingletonIdentityRound)

#guard alphaSingletonTwoRoundTrace.rounds == 2

/-- Multi-round semantic regression: the real folded-singleton round composes
with an explicit identity round without collapsing either phase boundary. -/
theorem alphaSingletonTwoRoundCorrect :
    SamePhaseCorrectOn (Impure.semantics externals)
      alphaSingletonBeforeProgram alphaSingletonAfterProgram alphaFoldEntries
      (alphaSingletonTwoRoundTrace.Admissible externals) :=
  structuralAlphaStructuralTraceSamePhaseCorrectOn
    alphaSingletonTwoRoundTrace

/-- The unchanged declaration parameters expose the nested source's scoped
alpha identity at the final body position. -/
theorem nestedPhaseDepthParamBodyReflexive :
    ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param c, param x].toList #[param c, param x].toList
      nestedPhaseDepthCode nestedPhaseDepthCode := by
  apply paramBodyRelated_replaceCode (index := ScopeIndex.empty)
    alphaLeftParamBodyReflexiveForward
  simpa only [← alphaFoldScopeIndex_fromParams, ScopeIndex.pushParams] using
    nestedPhaseDepthAlphaBireflexive.forward

/-- Concrete arbitrary-depth program lift. Both genuine scoped simplifier
rounds survive as distinct structural/alpha/structural program rounds. -/
def nestedPhaseDepthProgramTrace :
    StructuralAlphaStructuralTrace nestedPhaseDepthValidCase
      (singletonCodeProgram (alphaFoldDeclWith nestedPhaseDepthCode)
        nestedPhaseDepthCode)
      (singletonCodeProgram (alphaFoldDeclWith nestedPhaseDepthCode)
        alphaLeft) := by
  have trace : ScopedCodePhaseTrace nestedPhaseDepthValidCase
      (ScopeIndex.empty.pushParams
        (alphaFoldDeclWith nestedPhaseDepthCode).params)
      nestedPhaseDepthCode alphaLeft := by
    simpa [alphaFoldDeclWith, decl, alphaFoldScopeIndex_fromParams] using
      nestedPhaseDepthTrace
  exact trace.singletonProgramTrace
    (by simpa [alphaFoldDeclWith, decl] using
      nestedPhaseDepthParamBodyReflexive)

#guard nestedPhaseDepthProgramTrace.rounds == 2

/-- The automatically lifted two-round trace reaches the whole-program
semantic consumer without a fixture-specific phase reconstruction. -/
theorem nestedPhaseDepthProgramCorrect :
    SamePhaseCorrectOn (Impure.semantics externals)
      (singletonCodeProgram (alphaFoldDeclWith nestedPhaseDepthCode)
        nestedPhaseDepthCode)
      (singletonCodeProgram (alphaFoldDeclWith nestedPhaseDepthCode)
        alphaLeft)
      alphaFoldEntries
      (nestedPhaseDepthProgramTrace.Admissible externals) :=
  structuralAlphaStructuralTraceSamePhaseCorrectOn
    nestedPhaseDepthProgramTrace

/-- Root endpoint certificate used to keep the transformed two-round
declaration fixed while a later declaration takes its own phase round. -/
theorem nestedPhaseDepthAlphaLeftTargetCertificate :
    ScopedCodeTargetCertificate nestedPhaseDepthValidCase
      alphaFoldScopeIndex alphaLeft := {
  structural := nestedAlphaLeftStructuralRefl
  alpha := alphaLeftAlphaBireflexiveAtFoldScope
  side := by
    apply CodeSideConditions.letE
    · rfl
    · rfl
    · rfl
    · trivial
    · exact alphaLeftFreshForParams
    · exact alphaLeftFreshForParams
    · exact by
        intro old oldScoped
        simp [alphaFoldScopeIndex] at oldScoped
    · exact by
        intro old oldScoped
        simp [alphaFoldScopeIndex] at oldScoped
    · apply CodeSideConditions.ret <;> native_decide
  canonical := .letE {
    resultType := .object
    boxType := trivial
  } .ret
}

def unequalDepthBaseDecl : LCNF.Decl .impure :=
  alphaFoldDeclWith nestedPhaseDepthCode

def unequalDepthSourceDecl : LCNF.Decl .impure :=
  { unequalDepthBaseDecl with value := .code nestedPhaseDepthCode }

def unequalDepthTargetDecl : LCNF.Decl .impure :=
  { unequalDepthBaseDecl with value := .code alphaLeft }

def unequalDepthExternMetadata : ExternAttrData := { entries := [] }

def unequalDepthExternBaseDecl : LCNF.Decl .impure :=
  decl `unequalDepthExtern #[] objType (.extern unequalDepthExternMetadata)

def unequalDepthExternDecl : LCNF.Decl .impure :=
  { unequalDepthExternBaseDecl with value := .extern unequalDepthExternMetadata }

def unequalDepthExternEndpoint :
    ScopedDeclEndpointCertificate nestedPhaseDepthValidCase
      unequalDepthExternDecl := by
  exact ScopedDeclEndpointCertificate.extern
    (validCase := nestedPhaseDepthValidCase)
    unequalDepthExternBaseDecl unequalDepthExternMetadata

def unequalDepthTargetEndpoint :
    ScopedDeclEndpointCertificate nestedPhaseDepthValidCase
      unequalDepthTargetDecl := by
  apply ScopedDeclEndpointCertificate.code unequalDepthBaseDecl alphaLeft
  · simpa [unequalDepthBaseDecl, alphaFoldDeclWith, decl,
      alphaFoldScopeIndex_fromParams] using
      nestedPhaseDepthAlphaLeftTargetCertificate
  · simpa [unequalDepthBaseDecl, alphaFoldDeclWith, decl] using
      alphaLeftParamBodyReflexiveForward

def unequalDepthHeadTrace :
    StructuralAlphaStructuralDeclTrace nestedPhaseDepthValidCase
      unequalDepthSourceDecl unequalDepthTargetDecl := by
  have trace : ScopedCodePhaseTrace nestedPhaseDepthValidCase
      (ScopeIndex.empty.pushParams unequalDepthBaseDecl.params)
      nestedPhaseDepthCode alphaLeft := by
    simpa [unequalDepthBaseDecl, alphaFoldDeclWith, decl,
      alphaFoldScopeIndex_fromParams] using nestedPhaseDepthTrace
  exact
    trace.declarationTrace (by
      simpa [unequalDepthBaseDecl, alphaFoldDeclWith, decl] using
        nestedPhaseDepthParamBodyReflexive)

def unequalDepthTailTrace :
    StructuralAlphaStructuralDeclListTrace nestedPhaseDepthValidCase
      [unequalDepthExternDecl] [unequalDepthExternDecl] :=
  .single (.cons unequalDepthExternEndpoint.identityRound .nil)

/-- Unequal-depth multi-declaration regression: the first declaration keeps
its two genuine nested simpCase rounds, then the external declaration takes
one identity round under the certified transformed head. -/
def unequalDepthDeclListTrace :
    StructuralAlphaStructuralDeclListTrace nestedPhaseDepthValidCase
      [unequalDepthSourceDecl, unequalDepthExternDecl]
      [unequalDepthTargetDecl, unequalDepthExternDecl] :=
  (unequalDepthHeadTrace.withTail
      (.cons unequalDepthExternEndpoint .nil)).append
    (unequalDepthTailTrace.withHead unequalDepthTargetEndpoint)

#guard unequalDepthHeadTrace.rounds == 2
#guard unequalDepthTailTrace.rounds == 1
#guard unequalDepthDeclListTrace.rounds == 3

def unequalDepthProgramTrace :
    StructuralAlphaStructuralTrace nestedPhaseDepthValidCase
      ({ decls := #[unequalDepthSourceDecl, unequalDepthExternDecl] } :
        ImpureProgram)
      ({ decls := #[unequalDepthTargetDecl, unequalDepthExternDecl] } :
        ImpureProgram) := by
  simpa using unequalDepthDeclListTrace.programTrace

theorem unequalDepthProgramCorrect :
    SamePhaseCorrectOn (Impure.semantics externals)
      ({ decls := #[unequalDepthSourceDecl, unequalDepthExternDecl] } :
        ImpureProgram)
      ({ decls := #[unequalDepthTargetDecl, unequalDepthExternDecl] } :
        ImpureProgram)
      alphaFoldEntries (unequalDepthProgramTrace.Admissible externals) :=
  structuralAlphaStructuralTraceSamePhaseCorrectOn unequalDepthProgramTrace

theorem alphaFoldAlphaProgramsBirelated :
    ProgramsBirelated alphaFoldIntermediateProgram alphaFoldAfterProgram := {
  forward := alphaFoldProgramsRelatedOfParamBody alphaFoldParamBodyForward
  backward := alphaFoldProgramsRelatedOfParamBody alphaFoldParamBodyBackward
}

theorem alphaFoldAlphaCorrect :
    SamePhaseCorrect (Impure.semantics externals)
      alphaFoldIntermediateProgram alphaFoldAfterProgram alphaFoldEntries :=
  samePhaseCorrect_of_programsBirelated alphaFoldAlphaProgramsBirelated

def alphaFoldStructuralThenAlpha :
    StructuralThenAlphaPrograms alphaFoldValidCase
      alphaFoldBeforeProgram alphaFoldAfterProgram := {
  middle := alphaFoldIntermediateProgram
  structural := alphaFoldStructuralProgramsRelated
  alpha := alphaFoldAlphaProgramsBirelated
}

/-- The reusable structural/alpha compiler boundary closes alpha-default
folding at whole-program scope. -/
theorem alphaFoldComposedCorrect :
    SamePhaseCorrectOn (Impure.semantics externals)
      alphaFoldBeforeProgram alphaFoldAfterProgram alphaFoldEntries
      (ReachablyReadyAdmissible externals alphaFoldValidCase
        alphaFoldBeforeProgram alphaFoldIntermediateProgram) := by
  intro entry member args admissible observation
  exact structuralThenAlphaSamePhaseCorrectOn
    (externals := externals) (entries := alphaFoldEntries)
    alphaFoldStructuralThenAlpha entry member args admissible observation

def nestedInnerLeftCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .ctorAlt falseInfo (.return x),
    .default (.unreach objType)]

def nestedInnerRightCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.unreach objType),
    .ctorAlt falseInfo (.return x)]

def nestedInnerDefaultMismatchCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.return x),
    .ctorAlt falseInfo (.return x)]

def nestedInnerCtorMismatchCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.unreach objType),
    .ctorAlt falseInfo (.unreach objType)]

def nestedOuterLeftCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .ctorAlt falseInfo (.cases nestedInnerLeftCases),
    .default (.return x)]

def nestedOuterRightCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.return x),
    .ctorAlt falseInfo (.cases nestedInnerRightCases)]

def nestedOuterDefaultMismatchCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.return x),
    .ctorAlt falseInfo (.cases nestedInnerDefaultMismatchCases)]

def nestedOuterCtorMismatchCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.return x),
    .ctorAlt falseInfo (.cases nestedInnerCtorMismatchCases)]

def nestedLeftCode : LCNF.Code .impure :=
  .cases nestedOuterLeftCases

def nestedRightCode : LCNF.Code .impure :=
  .cases nestedOuterRightCases

def nestedDefaultMismatchCode : LCNF.Code .impure :=
  .cases nestedOuterDefaultMismatchCases

def nestedCtorMismatchCode : LCNF.Code .impure :=
  .cases nestedOuterCtorMismatchCases

theorem nestedInnerLeftNormalization :
    CaseTableNormalizationInvariant nestedInnerLeftCases.alts := by
  constructor
  simpa [nestedInnerLeftCases, LCNF.Cases.alts] using
    ctorDefaultCaseTableDeterministic falseInfo (.return x) (.unreach objType)

theorem nestedInnerRightNormalization :
    CaseTableNormalizationInvariant nestedInnerRightCases.alts := by
  constructor
  simpa [nestedInnerRightCases, LCNF.Cases.alts] using
    defaultCtorCaseTableDeterministic falseInfo (.return x) (.unreach objType)

theorem nestedOuterLeftNormalization :
    CaseTableNormalizationInvariant nestedOuterLeftCases.alts := by
  constructor
  simpa [nestedOuterLeftCases, LCNF.Cases.alts] using
    ctorDefaultCaseTableDeterministic falseInfo
      (.cases nestedInnerLeftCases) (.return x)

theorem nestedOuterRightNormalization :
    CaseTableNormalizationInvariant nestedOuterRightCases.alts := by
  constructor
  simpa [nestedOuterRightCases, LCNF.Cases.alts] using
    defaultCtorCaseTableDeterministic falseInfo
      (.cases nestedInnerRightCases) (.return x)

theorem nestedInnerCodeSideConditions :
    CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [c, x] [c, x]
      (.cases nestedInnerLeftCases) (.cases nestedInnerRightCases) := by
  apply CodeSideConditions.cases
  · native_decide
  · native_decide
  · exact nestedInnerLeftNormalization
  · exact nestedInnerRightNormalization
  · intro tag left right leftHas rightHas
    rcases leftHas with ⟨leftInfo, leftMember, leftTag⟩
    rcases rightHas with ⟨rightInfo, rightMember, rightTag⟩
    simp [nestedInnerLeftCases, LCNF.Cases.alts] at leftMember
    simp [nestedInnerRightCases, LCNF.Cases.alts] at rightMember
    rcases leftMember with ⟨rfl, rfl⟩
    rcases rightMember with ⟨rfl, rfl⟩
    exact .ret (by native_decide) (by native_decide)
  · intro left right leftHas rightHas
    simp [HasDefaultAlt, nestedInnerLeftCases, nestedInnerRightCases,
      LCNF.Cases.alts] at leftHas rightHas
    subst left
    subst right
    exact .unreachable

theorem nestedCodeSideConditions :
    CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [c, x] [c, x]
      nestedLeftCode nestedRightCode := by
  unfold nestedLeftCode nestedRightCode
  apply CodeSideConditions.cases
  · native_decide
  · native_decide
  · exact nestedOuterLeftNormalization
  · exact nestedOuterRightNormalization
  · intro tag left right leftHas rightHas
    rcases leftHas with ⟨leftInfo, leftMember, leftTag⟩
    rcases rightHas with ⟨rightInfo, rightMember, rightTag⟩
    simp [nestedOuterLeftCases, LCNF.Cases.alts] at leftMember
    simp [nestedOuterRightCases, LCNF.Cases.alts] at rightMember
    rcases leftMember with ⟨rfl, rfl⟩
    rcases rightMember with ⟨rfl, rfl⟩
    exact nestedInnerCodeSideConditions
  · intro left right leftHas rightHas
    simp [HasDefaultAlt, nestedOuterLeftCases, nestedOuterRightCases,
      LCNF.Cases.alts] at leftHas rightHas
    subst left
    subst right
    exact .ret (by native_decide) (by native_decide)

/-- Recursive side conditions close two normalized nested case tables. -/
theorem nestedLocalCodeRelated :
    CodeRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [c, x] [c, x]
      nestedLeftCode nestedRightCode :=
  codeRelated_of_local_accepts nestedCodeSideConditions
    ⟨8, by native_decide⟩

theorem nestedDefaultMismatchRejected :
    Local.check 8 nestedLeftCode nestedDefaultMismatchCode = false := by
  native_decide

theorem nestedCtorMismatchRejected :
    Local.check 8 nestedLeftCode nestedCtorMismatchCode = false := by
  native_decide

#guard Local.check 8 nestedLeftCode nestedRightCode
#guard !Local.check 8 nestedLeftCode nestedDefaultMismatchCode
#guard !Local.check 8 nestedLeftCode nestedCtorMismatchCode
#guard localMatchesUpstream nestedLeftCode nestedRightCode
#guard localMatchesUpstream nestedLeftCode nestedDefaultMismatchCode
#guard localMatchesUpstream nestedLeftCode nestedCtorMismatchCode

def joinLeftId : FVarId := ⟨`joinLeft⟩
def joinRightId : FVarId := ⟨`joinRight⟩
def joinWrongId : FVarId := ⟨`joinWrong⟩
def joinLeftParam : FVarId := ⟨`joinLeftParam⟩
def joinRightParam : FVarId := ⟨`joinRightParam⟩
def joinLeftArg : FVarId := ⟨`joinLeftArg⟩
def joinRightArg : FVarId := ⟨`joinRightArg⟩

def joinLeftBodyCases : LCNF.Cases .impure :=
  .mk ``Bool objType joinLeftParam #[
    .ctorAlt falseInfo (.return joinLeftParam),
    .default (.unreach objType)]

def joinRightBodyCases : LCNF.Cases .impure :=
  .mk ``Bool objType joinRightParam #[
    .default (.unreach objType),
    .ctorAlt falseInfo (.return joinRightParam)]

def joinLeftDecl : LCNF.FunDecl .impure :=
  .mk joinLeftId `joinLeft #[param joinLeftParam] objType
    (.cases joinLeftBodyCases)

def joinRightDecl : LCNF.FunDecl .impure :=
  .mk joinRightId `joinRight #[param joinRightParam] objType
    (.cases joinRightBodyCases)

def joinAlphaLeft : LCNF.Code .impure :=
  .jp joinLeftDecl <|
    .let (letDecl joinLeftArg objType (.lit (.nat 41))) <|
      .jmp joinLeftId #[.fvar joinLeftArg]

def joinAlphaRight : LCNF.Code .impure :=
  .jp joinRightDecl <|
    .let (letDecl joinRightArg objType (.lit (.nat 41))) <|
      .jmp joinRightId #[.fvar joinRightArg]

def joinBodyMismatch : LCNF.Code .impure :=
  .jp (.mk joinRightId `joinRight #[param joinRightParam] objType
      (.return joinRightParam)) <|
    .let (letDecl joinRightArg objType (.lit (.nat 41))) <|
      .jmp joinRightId #[.fvar joinRightArg]

def joinTargetMismatch : LCNF.Code .impure :=
  .jp (.mk joinRightId `joinRight #[param joinRightParam] objType
      (.cases joinRightBodyCases)) <|
    .let (letDecl joinRightArg objType (.lit (.nat 41))) <|
      .jmp joinWrongId #[.fvar joinRightArg]

def joinArityMismatch : LCNF.Code .impure :=
  .jp (.mk joinRightId `joinRight #[param joinRightParam] objType
      (.cases joinRightBodyCases)) <|
    .let (letDecl joinRightArg objType (.lit (.nat 41))) <|
      .jmp joinRightId #[]

def joinArgumentMismatch : LCNF.Code .impure :=
  .jp (.mk joinRightId `joinRight #[param joinRightParam] objType
      (.cases joinRightBodyCases)) <|
    .let (letDecl joinRightArg objType (.lit (.nat 41))) <|
      .jmp joinRightId #[.erased]

theorem joinBodyMismatchRejected :
    Local.check 8 joinAlphaLeft joinBodyMismatch = false := by
  native_decide

theorem joinTargetMismatchRejected :
    Local.check 8 joinAlphaLeft joinTargetMismatch = false := by
  native_decide

theorem joinArityMismatchRejected :
    Local.check 8 joinAlphaLeft joinArityMismatch = false := by
  native_decide

theorem joinArgumentMismatchRejected :
    Local.check 8 joinAlphaLeft joinArgumentMismatch = false := by
  native_decide

theorem joinLeftBodyNormalization :
    CaseTableNormalizationInvariant joinLeftBodyCases.alts := by
  constructor
  simpa [joinLeftBodyCases, LCNF.Cases.alts] using
    ctorDefaultCaseTableDeterministic falseInfo
      (.return joinLeftParam) (.unreach objType)

theorem joinRightBodyNormalization :
    CaseTableNormalizationInvariant joinRightBodyCases.alts := by
  constructor
  simpa [joinRightBodyCases, LCNF.Cases.alts] using
    defaultCtorCaseTableDeterministic falseInfo
      (.return joinRightParam) (.unreach objType)

theorem joinBodyCodeSideConditions :
    CodeSideConditions (leftJoins := []) (rightJoins := [])
      (({} : FVarIdMap FVarId).insert joinRightParam joinLeftParam)
      [joinLeftParam] [joinRightParam]
      (.cases joinLeftBodyCases) (.cases joinRightBodyCases) := by
  apply CodeSideConditions.cases
  · native_decide
  · native_decide
  · exact joinLeftBodyNormalization
  · exact joinRightBodyNormalization
  · intro tag left right leftHas rightHas
    rcases leftHas with ⟨leftInfo, leftMember, leftTag⟩
    rcases rightHas with ⟨rightInfo, rightMember, rightTag⟩
    simp [joinLeftBodyCases, LCNF.Cases.alts] at leftMember
    simp [joinRightBodyCases, LCNF.Cases.alts] at rightMember
    rcases leftMember with ⟨rfl, rfl⟩
    rcases rightMember with ⟨rfl, rfl⟩
    exact .ret (by native_decide) (by native_decide)
  · intro left right leftHas rightHas
    simp [HasDefaultAlt, joinLeftBodyCases, joinRightBodyCases,
      LCNF.Cases.alts] at leftHas rightHas
    subst left
    subst right
    exact .unreachable

theorem joinParamBodySideConditions :
    ParamBodySideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param joinLeftParam].toList #[param joinRightParam].toList
      (.cases joinLeftBodyCases) (.cases joinRightBodyCases) := by
  apply ParamBodySideConditions.cons
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · exact .nil joinBodyCodeSideConditions

/--
The transparent parameter loop constructs the recursively related join body,
including normalized case selection beneath the alpha-renamed parameters.
-/
theorem joinParamBodyRelated :
    ParamBodyRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      #[param joinLeftParam].toList #[param joinRightParam].toList
      (.cases joinLeftBodyCases) (.cases joinRightBodyCases) :=
  paramBodyRelated_of_local_check joinParamBodySideConditions
    (fuel := 4) (by
      change Id.run ((Local.withParamListsUsing
        (Local.eqv 4 (.cases joinLeftBodyCases) (.cases joinRightBodyCases))
        #[param joinLeftParam].toList #[param joinRightParam].toList).run
          ({} : FVarIdMap FVarId)) = true
      native_decide)

theorem joinCodeSideConditions :
    CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] [] joinAlphaLeft joinAlphaRight := by
  unfold joinAlphaLeft joinAlphaRight
  apply CodeSideConditions.jp
  · constructor
    · intro old oldScoped
      simp at oldScoped
    · intro old oldScoped
      simp at oldScoped
  · constructor
    · intro old oldScoped
      simp at oldScoped
    · intro old oldScoped
      simp at oldScoped
  · exact joinParamBodySideConditions
  · apply CodeSideConditions.letE
    · rfl
    · rfl
    · rfl
    · trivial
    · intro old oldScoped
      simp at oldScoped
    · intro old oldScoped
      simp at oldScoped
    · intro old oldScoped
      simp at oldScoped
      have oldEq := fvar_eq_of_beq oldScoped
      subst old
      native_decide
    · intro old oldScoped
      simp at oldScoped
      have oldEq := fvar_eq_of_beq oldScoped
      subst old
      native_decide
    · apply CodeSideConditions.jmp <;> native_decide

/--
The declarative relation covers an alpha-renamed join declaration, its
parameterized case body, and the jump through the active join scope.
-/
theorem joinLocalCodeRelated :
    CodeRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] [] joinAlphaLeft joinAlphaRight :=
  codeRelated_of_local_accepts joinCodeSideConditions
    ⟨8, by native_decide⟩

def joinProofState (code : LCNF.Code .impure) : MachineState := {
  program := { decls := #[] }
  control := .code code
}

theorem emptyProgramBodiesRelated :
    ProgramBodiesRelated ({ decls := #[] } : ImpureProgram) := by
  intro name declaration found
  simp [Program.findDecl?] at found

/-- Installing alpha-renamed join declarations preserves the machine relation. -/
theorem joinInstallationCoreStepRelated :
    CoreResultRelated
      (coreStep (joinProofState joinAlphaLeft))
      (coreStep (joinProofState joinAlphaRight)) := by
  apply coreStep_code_related
    (rho := ({} : FVarIdMap FVarId))
    (leftScope := []) (rightScope := [])
    (leftJoins := []) (rightJoins := [])
    (leftState := joinProofState joinAlphaLeft)
    (rightState := joinProofState joinAlphaRight)
  · exact programsRelated_refl emptyProgramBodiesRelated
  · rfl
  · exact .empty
  · exact .nil
  · intro left leftScoped
    simp at leftScoped
  · exact renamingScoped_empty []
  · exact renamingScoped_empty []
  · exact joinLocalCodeRelated
  · trivial

def joinJumpLeftState : MachineState := {
  program := { decls := #[] }
  control := .code (.jmp joinLeftId #[.fvar joinLeftArg])
  env := bind [] joinLeftArg .erased
  joins := [(joinLeftId, joinLeftDecl)]
}

def joinJumpRightState : MachineState := {
  program := { decls := #[] }
  control := .code (.jmp joinRightId #[.fvar joinRightArg])
  env := bind [] joinRightArg .erased
  joins := [(joinRightId, joinRightDecl)]
}

/-- Invoking the installed alpha-renamed joins binds their parameters alike. -/
theorem joinInvocationCoreStepRelated :
    CoreResultRelated
      (coreStep joinJumpLeftState)
      (coreStep joinJumpRightState) := by
  let joinRho := ({} : FVarIdMap FVarId).insert joinRightId joinLeftId
  let finalRho := joinRho.insert joinRightArg joinLeftArg
  have leftJoinFresh : FreshJoinBinder joinLeftId [] [] := by
    constructor <;> intro old oldScoped <;> simp at oldScoped
  have rightJoinFresh : FreshJoinBinder joinRightId [] [] := by
    constructor <;> intro old oldScoped <;> simp at oldScoped
  have leftArgFresh : FreshForScope joinLeftArg [] := by
    intro old oldScoped
    simp at oldScoped
  have rightArgFresh : FreshForScope joinRightArg [] := by
    intro old oldScoped
    simp at oldScoped
  have leftArgJoinFresh : FreshForScope joinLeftArg [joinLeftId] := by
    intro old oldScoped
    simp at oldScoped
    have oldEq := fvar_eq_of_beq oldScoped
    subst old
    native_decide
  have rightArgJoinFresh : FreshForScope joinRightArg [joinRightId] := by
    intro old oldScoped
    simp at oldScoped
    have oldEq := fvar_eq_of_beq oldScoped
    subst old
    native_decide
  have emptyAgree : EnvsAgree ({} : FVarIdMap FVarId) [] [] [] [] := by
    intro left leftScoped
    simp at leftScoped
  have emptyRenaming := renamingScoped_empty ([] : List FVarId)
  have joinedAgree : EnvsAgree joinRho [] [] [] [] :=
    envsAgree_insert_preserve (leftId := joinLeftId)
      emptyAgree rightJoinFresh.variables
  have joinedVariableRenaming : RenamingScoped joinRho [] [] :=
    renamingScoped_insert_preserve (leftId := joinLeftId)
      emptyRenaming rightJoinFresh.variables
  have joinedJoinRenaming :
      RenamingScoped joinRho [joinLeftId] [joinRightId] :=
    renamingScoped_insert emptyRenaming rightJoinFresh.joins
  have installedJoins :
      JoinEnvsRelated joinRho [] [] [joinLeftId] [joinRightId]
        [(joinLeftId, joinLeftDecl)] [(joinRightId, joinRightDecl)] :=
    JoinEnvsRelated.join (leftDecl := joinLeftDecl) (rightDecl := joinRightDecl)
      .empty emptyRenaming emptyRenaming leftJoinFresh rightJoinFresh
      joinParamBodyRelated
  have jump :
      CodeRelated (leftJoins := [joinLeftId]) (rightJoins := [joinRightId])
        finalRho [joinLeftArg] [joinRightArg]
        (.jmp joinLeftId #[.fvar joinLeftArg])
        (.jmp joinRightId #[.fvar joinRightArg]) := by
    apply CodeRelated.jmp
    · refine ⟨by native_decide, by native_decide, ?_⟩
      change FVarRelated finalRho joinLeftId joinRightId
      apply (fVarRelated_insert_of_name_ne joinRho
        joinLeftArg joinRightArg joinLeftId joinRightId (by native_decide)).mpr
      exact fVarRelated_insert_self ({} : FVarIdMap FVarId)
        joinLeftId joinRightId
    · apply ListRel.cons
      · refine ⟨by native_decide, by native_decide, ?_⟩
        change FVarRelated finalRho joinLeftArg joinRightArg
        exact fVarRelated_insert_self joinRho joinLeftArg joinRightArg
      · exact .nil
  apply coreStep_code_related
    (rho := finalRho)
    (leftScope := [joinLeftArg]) (rightScope := [joinRightArg])
    (leftJoins := [joinLeftId]) (rightJoins := [joinRightId])
    (leftState := joinJumpLeftState)
    (rightState := joinJumpRightState)
  · exact programsRelated_refl emptyProgramBodiesRelated
  · rfl
  · exact .bind installedJoins joinedVariableRenaming joinedJoinRenaming
      leftArgFresh rightArgFresh leftArgJoinFresh rightArgJoinFresh
  · exact .nil
  · exact envsAgree_bind joinedAgree joinedVariableRenaming
      leftArgFresh rightArgFresh
  · exact renamingScoped_insert joinedVariableRenaming rightArgFresh
  · exact renamingScoped_insert_preserve joinedJoinRenaming rightArgJoinFresh
  · exact jump
  · trivial

def callProofProgram : ImpureProgram := { decls := #[idDecl] }

theorem idDeclBodyRelated : DeclBodyRelated idDecl := by
  change ParamBodyRelated (leftJoins := []) (rightJoins := [])
    ({} : FVarIdMap FVarId) [] []
    #[param x].toList #[param x].toList (.return x) (.return x)
  apply ParamBodyRelated.cons
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · intro old oldScoped
    simp at oldScoped
  · apply ParamBodyRelated.nil
    apply CodeRelated.terminal
    apply TerminalCodeRelated.ret
    exact ⟨by native_decide, by native_decide,
      fVarRelated_insert_self ({} : FVarIdMap FVarId) x x⟩

theorem callProofProgramBodiesRelated : ProgramBodiesRelated callProofProgram := by
  intro name foundDecl found
  simp [callProofProgram, Program.findDecl?] at found
  rcases found with ⟨_, rfl⟩
  exact idDeclBodyRelated

def namedCallProofState : MachineState := {
  program := callProofProgram
  control := .invokeName `id #[.erased]
}

theorem namedCallMachineRelated :
    MachineStateRelated
      (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] []
      namedCallProofState namedCallProofState := {
  programs := programsRelated_refl callProofProgramBodiesRelated
  runtime_eq := rfl
  joins := .empty
  frames := .nil
  envs := envsAgree_empty_scopes ({} : FVarIdMap FVarId) [] []
  renaming_scoped := renamingScoped_empty []
  join_renaming_scoped := renamingScoped_empty []
  control := .invokeName `id #[.erased]
}

theorem namedCallStatesRelated :
    StatesRelated namedCallProofState namedCallProofState :=
  ⟨_, _, _, _, _, namedCallMachineRelated⟩

theorem namedCallStatesBisimilar :
    StatesBisimilar namedCallProofState namedCallProofState :=
  ⟨namedCallStatesRelated, namedCallStatesRelated⟩

/-- Named declaration entry is covered by the full control-step simulation. -/
theorem namedCallCoreStepRelated :
    CoreResultRelated
      (coreStep namedCallProofState) (coreStep namedCallProofState) := by
  exact coreStep_machine_related namedCallMachineRelated

/-- The execution-level API composes declaration entry through arbitrarily
many internal or external steps. -/
theorem namedCallEvaluatesForward
    (evaluation : EvaluatesState externals namedCallProofState observation) :
    EvaluatesState externals namedCallProofState observation :=
  evaluatesState_forward namedCallStatesRelated evaluation

/-- The bidirectional execution boundary yields observational equivalence. -/
theorem namedCallEvaluatesIff :
    EvaluatesState externals namedCallProofState observation ↔
      EvaluatesState externals namedCallProofState observation :=
  evaluatesState_iff_of_bisimilar namedCallStatesBisimilar

def closureProofRuntime : RuntimeState := {
  heap := [(0, { object := .closure `id 1 #[] })]
  nextLocation := 1
}

def closureProofState : MachineState := {
  program := callProofProgram
  control := .invokeValue (.object (.heap 0)) #[.erased]
  runtime := closureProofRuntime
}

/-- Closure lookup delegates to the same declaration-entry simulation. -/
theorem closureCallCoreStepRelated :
    CoreResultRelated
      (coreStep closureProofState) (coreStep closureProofState) := by
  apply coreStep_machine_related
    (rho := ({} : FVarIdMap FVarId))
    (leftScope := []) (rightScope := [])
    (leftJoins := []) (rightJoins := [])
  · exact {
      programs := programsRelated_refl callProofProgramBodiesRelated
      runtime_eq := rfl
      joins := .empty
      frames := .nil
      envs := envsAgree_empty_scopes ({} : FVarIdMap FVarId) [] []
      renaming_scoped := renamingScoped_empty []
      join_renaming_scoped := renamingScoped_empty []
      control := .invokeValue (.object (.heap 0)) #[.erased]
    }

#guard Local.check 8 joinAlphaLeft joinAlphaRight
#guard !Local.check 8 joinAlphaLeft joinBodyMismatch
#guard !Local.check 8 joinAlphaLeft joinTargetMismatch
#guard !Local.check 8 joinAlphaLeft joinArityMismatch
#guard !Local.check 8 joinAlphaLeft joinArgumentMismatch
#guard localMatchesUpstream joinAlphaLeft joinAlphaRight
#guard localMatchesUpstream joinAlphaLeft joinBodyMismatch
#guard localMatchesUpstream joinAlphaLeft joinTargetMismatch
#guard localMatchesUpstream joinAlphaLeft joinArityMismatch
#guard localMatchesUpstream joinAlphaLeft joinArgumentMismatch

def callLeftResult : FVarId := ⟨`callLeftResult⟩
def callRightResult : FVarId := ⟨`callRightResult⟩

def callAlphaLeft : LCNF.Code .impure :=
  .let (letDecl joinLeftArg objType (.lit (.nat 43))) <|
    .let (letDecl callLeftResult objType (.fap `id #[.fvar joinLeftArg])) <|
      .return callLeftResult

def callAlphaRight : LCNF.Code .impure :=
  .let (letDecl joinRightArg objType (.lit (.nat 43))) <|
    .let (letDecl callRightResult objType (.fap `id #[.fvar joinRightArg])) <|
      .return callRightResult

def callTargetMismatch : LCNF.Code .impure :=
  .let (letDecl joinRightArg objType (.lit (.nat 43))) <|
    .let (letDecl callRightResult objType (.fap `first #[.fvar joinRightArg])) <|
      .return callRightResult

def callArgumentMismatch : LCNF.Code .impure :=
  .let (letDecl joinRightArg objType (.lit (.nat 43))) <|
    .let (letDecl callRightResult objType (.fap `id #[.erased])) <|
      .return callRightResult

theorem callTargetMismatchRejected :
    Local.check 8 callAlphaLeft callTargetMismatch = false := by
  native_decide

theorem callArgumentMismatchRejected :
    Local.check 8 callAlphaLeft callArgumentMismatch = false := by
  native_decide

#guard Local.check 8 callAlphaLeft callAlphaRight
#guard !Local.check 8 callAlphaLeft callTargetMismatch
#guard !Local.check 8 callAlphaLeft callArgumentMismatch
#guard localMatchesUpstream callAlphaLeft callAlphaRight
#guard localMatchesUpstream callAlphaLeft callTargetMismatch
#guard localMatchesUpstream callAlphaLeft callArgumentMismatch

def populatedCaseAlts : List (LCNF.Alt .impure) := [
  .ctorAlt falseInfo (.return x),
  .default (.unreach objType)]

def reorderedCaseAlts : List (LCNF.Alt .impure) :=
  populatedCaseAlts.reverse

theorem populatedCaseAltsPermutation :
    populatedCaseAlts.Perm reorderedCaseAlts := by
  simpa [reorderedCaseAlts] using (List.reverse_perm populatedCaseAlts).symm

theorem populatedCaseAltsDeterministic :
    CaseTableDeterministic populatedCaseAlts := by
  constructor
  · intro tag left right leftHas rightHas
    rcases leftHas with ⟨leftInfo, leftMember, leftTag⟩
    rcases rightHas with ⟨rightInfo, rightMember, rightTag⟩
    simp [populatedCaseAlts] at leftMember rightMember
    simp_all
  · intro left right leftHas rightHas
    simp [HasDefaultAlt, populatedCaseAlts] at leftHas rightHas
    simp_all

/-- Constructor and default selection survive a populated table reordering. -/
theorem populatedCaseSelectionOrderIndependent (tag : Nat) :
    chooseAlt tag populatedCaseAlts = chooseAlt tag reorderedCaseAlts :=
  chooseAlt_eq_of_perm populatedCaseAltsDeterministic
    populatedCaseAltsPermutation

def alphaEqvRegressionCodes : Array (LCNF.Code .impure) := #[
  literalCode,
  erasedCode,
  ctorProjectionCode,
  caseCode,
  directCallCode,
  closureCallCode,
  joinCode,
  scalarBoxCode,
  mutationCode,
  usizeProjectionCode,
  objectMutationCode,
  tagMutationCode,
  defaultCaseCode,
  rcCode,
  persistentRcCode,
  isSharedCaseCode,
  resetReuseCode,
  sharedResetCode,
  deletedCode,
  externalCode,
  .unreach objType
]

#guard alphaEqvRegressionCodes.all fun code => localMatchesUpstream code code

def nonHygienicAlphaLeftProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code nonHygienicAlphaLeft)] }

def nonHygienicAlphaRightProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code nonHygienicAlphaRight)] }

#guard returned? (runMain nonHygienicAlphaLeftProgram) (.object (.tagged 6))
#guard returned? (runMain nonHygienicAlphaRightProgram) (.object (.tagged 5))

def fixtureDecl (name : Name) (code : LCNF.Code .impure) : LCNF.Decl .impure :=
  decl name #[param c, param x] objType (.code code)

def checkActualSimpCase (name : Name) (before expected : LCNF.Code .impure) : CoreM Unit := do
  let beforeProgram : ImpureProgram :=
    { decls := #[fixtureDecl name before] }
  checkActualAgreement 512 beforeProgram
  let output ← LCNF.CompilerM.run
    (LCNF.simpCase.run beforeProgram.decls) (phase := .impure)
  let some after := output[0]? | throwError "simpCase fixture {name} produced no declaration"
  let .code actual := after.value | throwError "simpCase fixture {name} ceased to be code"
  unless actual == expected do
    throwError "simpCase fixture {name} did not produce the specification result"

/-- One declaration per impure code constructor used by the alpha-equivalence
regression corpus.  The pass and shadow must agree across the whole array. -/
def recursiveTraversalCorpus : ImpureProgram :=
  { decls := alphaEqvRegressionCodes.mapIdx fun index code =>
      fixtureDecl (Name.mkSimple s!"simpCaseShadow{index}") code }

def checkFixtures : CoreM Unit := do
  checkActualSimpCase `singletonDefault singletonDefaultCode selectedBranch
  checkActualSimpCase `filterUnreachable filterUnreachableCode selectedBranch
  checkActualSimpCase `foldAlphaEquivalent alphaFoldCode alphaFoldExpected
  checkActualSimpCase `foldAlphaSingleton alphaSingletonFoldCode alphaLeft
  checkActualSimpCase `nestedFoldAlphaSingleton nestedAlphaSingletonFoldCode
    nestedAlphaSingletonFoldExpected
  checkActualSimpCase `mixedPhaseJoin mixedPhaseJoinSource mixedPhaseJoinTarget
  checkActualSimpCase `nestedPhaseDepth nestedPhaseDepthCode alphaLeft
  checkActualAgreement 512 recursiveTraversalCorpus

elab "#check_simp_case_fixtures" : command =>
  liftCoreM checkFixtures

#check_simp_case_fixtures

/-! ## Compiler-facing well-formedness regressions -/

def checkerParamIndex : ScopeIndex :=
  ScopeIndex.empty.pushParams #[param c]

/-- Duplicate selectors are permitted precisely when they select the same
body; the normalization invariant remains deterministic. -/
def deterministicShadowedCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.return c),
    .default (.return c)]

#guard scopedCodeCheck checkerParamIndex (.cases deterministicShadowedCases)

theorem deterministicShadowedNormalization :
    CaseTableNormalizationInvariant deterministicShadowedCases.alts := by
  constructor
  constructor <;>
    simp_all [HasCtorAlt, HasDefaultAlt,
      deterministicShadowedCases, LCNF.Cases.alts]

/-- The local checker visits syntactically shadowed alternatives rather than
only the branch returned by `chooseAlt`. -/
def malformedShadowedCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.return c),
    .default (.return x)]

#guard !scopedCodeCheck checkerParamIndex (.cases malformedShadowedCases)

def duplicateParamDeclaration : LCNF.Decl .impure :=
  decl `duplicateParams #[param x, param x] objType (.code (.return x))

#guard !declScopedCheck duplicateParamDeclaration
#guard !declScopedCheck
  (decl `duplicateLets #[] objType (.code nonHygienicAlphaLeft))
#guard !declScopedCheck
  (decl `outOfScope #[] objType (.code (.return x)))

/-- Repeated constructor selectors with different bodies violate the
deterministic normalization contract. -/
def nondeterministicCtorCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .ctorAlt falseInfo (.return c),
    .ctorAlt falseInfo (.unreach objType)]

theorem nondeterministicCtorCases_rejected :
    ¬CaseTableNormalizationInvariant nondeterministicCtorCases.alts := by
  intro normalization
  have equal := normalization.deterministic.ctor 0
    (.return c) (.unreach objType)
    ⟨falseInfo, by
      simp [nondeterministicCtorCases, LCNF.Cases.alts], by native_decide⟩
    ⟨falseInfo, by
      simp [nondeterministicCtorCases, LCNF.Cases.alts], by native_decide⟩
  cases equal

/-- Repeated defaults with different bodies are rejected for the same
reason. -/
def nondeterministicDefaultCases : LCNF.Cases .impure :=
  .mk ``Bool objType c #[
    .default (.return c),
    .default (.unreach objType)]

theorem nondeterministicDefaultCases_rejected :
    ¬CaseTableNormalizationInvariant nondeterministicDefaultCases.alts := by
  intro normalization
  have equal := normalization.deterministic.default
    (.return c) (.unreach objType)
    (by simp [HasDefaultAlt, nondeterministicDefaultCases,
      LCNF.Cases.alts])
    (by simp [HasDefaultAlt, nondeterministicDefaultCases,
      LCNF.Cases.alts])
  cases equal

def noncanonicalRuntimeType : Expr := .fvar x

def noncanonicalRuntimeCode : LCNF.Code .impure :=
  .let (letDecl x noncanonicalRuntimeType (.lit (.nat 0))) (.return x)

theorem noncanonicalRuntimeCode_rejected :
    ¬CodeRuntimeTypesCanonical noncanonicalRuntimeCode := by
  intro canonical
  cases canonical with
  | letE declarationTypes _ =>
      cases declarationTypes.resultType

def wellFormedReturnDeclaration : LCNF.Decl .impure :=
  decl `wellFormedReturn #[param x] objType (.code (.return x))

def wellFormedReturnProgram : ImpureProgram :=
  { decls := #[wellFormedReturnDeclaration] }

theorem wellFormedReturnProgram_source :
    ProgramWellFormed wellFormedReturnProgram := by
  apply ProgramWellFormed.ofCompilerInvariants
  · apply WellFormedAt.impure
    · simp [Program.NamesUnique, wellFormedReturnProgram]
    · unfold Program.ImpureHygienic
      native_decide
  · native_decide
  · intro declaration member
    simp [wellFormedReturnProgram] at member
    subst declaration
    exact .ret
  · intro declaration member
    simp [wellFormedReturnProgram] at member
    subst declaration
    exact .ret

noncomputable def wellFormedReturnCertificates :
    ScopedDeclTargetCertificateList ReachableCaseTag
      wellFormedReturnProgram.decls.toList :=
  wellFormedReturnProgram_source.certificates

/-- Positive API check: semantic correctness no longer mentions a source
certificate list. -/
theorem wellFormedReturn_preferredApi
    (bridge : UpstreamBridge)
    (run : shadowProgram? fuel wellFormedReturnProgram = some after) :
    ∃ result : ScopedProgramPhaseEndpointCertifiedTrace
        ReachableCaseTag wellFormedReturnProgram after,
      SamePhaseCorrectOn (Impure.semantics externals)
        wellFormedReturnProgram after entries
        (result.trace.Admissible externals) :=
  shadowProgram_samePhaseCorrectOn_reachableCaseTag_of_programWellFormed
    bridge wellFormedReturnProgram_source run

end Fir.LeanIR.Passes.SimpCaseExamples
