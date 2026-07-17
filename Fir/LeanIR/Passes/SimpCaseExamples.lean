import Fir.LeanIR.Passes.SimpCase
import Fir.LeanIR.Passes.AlphaEqvTrusted
import Fir.LeanIR.InterpreterExamples
import Lean.Elab.Command

namespace Fir.LeanIR.Passes.SimpCaseExamples

open Lean
open Lean.Elab.Command
open Lean.Compiler
open Fir.LeanIR.InterpreterExamples
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.AlphaEqv

def selectedBranch : LCNF.Code .impure :=
  .return x

def singletonDefaultCode : LCNF.Code .impure :=
  .cases (.mk ``Bool objType c #[.default selectedBranch])

def filterUnreachableCode : LCNF.Code .impure :=
  .cases (.mk ``Bool objType c #[
    .ctorAlt falseInfo (.unreach objType),
    .ctorAlt trueInfo selectedBranch])

def alphaLeftId : FVarId := ⟨`alphaLeft⟩

def alphaRightId : FVarId := ⟨`alphaRight⟩

def alphaLeft : LCNF.Code .impure :=
  .let (letDecl alphaLeftId objType (.lit (.nat 5))) (.return alphaLeftId)

def alphaRight : LCNF.Code .impure :=
  .let (letDecl alphaRightId objType (.lit (.nat 5))) (.return alphaRightId)

#guard alphaLeft.alphaEqv alphaRight

def thirdInfo : LCNF.CtorInfo :=
  { name := `Third, cidx := 2, size := 0, usize := 0, ssize := 0 }

def alphaFoldCode : LCNF.Code .impure :=
  .cases (.mk `Three objType c #[
    .ctorAlt falseInfo alphaLeft,
    .ctorAlt trueInfo alphaRight,
    .ctorAlt thirdInfo selectedBranch])

def alphaFoldExpected : LCNF.Code .impure :=
  .cases (.mk `Three objType c #[
    .ctorAlt thirdInfo selectedBranch,
    .default alphaLeft])

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

/-- The transparent checker closes the complete alpha-renamed `let` fixture. -/
theorem alphaLocalCodeRelated :
    CodeRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] [] alphaLeft alphaRight :=
  codeRelated_of_local_accepts alphaCodeSideConditions ⟨2, by native_decide⟩

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
  · rfl
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
  · rfl
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

/-- Named declaration entry is covered by the full control-step simulation. -/
theorem namedCallCoreStepRelated :
    CoreResultRelated
      (coreStep namedCallProofState) (coreStep namedCallProofState) := by
  apply coreStep_machine_related
    (rho := ({} : FVarIdMap FVarId))
    (leftScope := []) (rightScope := [])
    (leftJoins := []) (rightJoins := [])
  · exact {
      program_eq := rfl
      runtime_eq := rfl
      joins := .empty
      frames := .nil
      envs := envsAgree_empty_scopes ({} : FVarIdMap FVarId) [] []
      renaming_scoped := renamingScoped_empty []
      join_renaming_scoped := renamingScoped_empty []
      control := .invokeName `id #[.erased]
    }
  · exact callProofProgramBodiesRelated

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
      program_eq := rfl
      runtime_eq := rfl
      joins := .empty
      frames := .nil
      envs := envsAgree_empty_scopes ({} : FVarIdMap FVarId) [] []
      renaming_scoped := renamingScoped_empty []
      join_renaming_scoped := renamingScoped_empty []
      control := .invokeValue (.object (.heap 0)) #[.erased]
    }
  · exact callProofProgramBodiesRelated

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
  let output ← LCNF.CompilerM.run
    (LCNF.simpCase.run #[fixtureDecl name before]) (phase := .impure)
  let some after := output[0]? | throwError "simpCase fixture {name} produced no declaration"
  let .code actual := after.value | throwError "simpCase fixture {name} ceased to be code"
  unless actual == expected do
    throwError "simpCase fixture {name} did not produce the specification result"

def checkFixtures : CoreM Unit := do
  checkActualSimpCase `singletonDefault singletonDefaultCode selectedBranch
  checkActualSimpCase `filterUnreachable filterUnreachableCode selectedBranch
  checkActualSimpCase `foldAlphaEquivalent alphaFoldCode alphaFoldExpected

elab "#check_simp_case_fixtures" : command =>
  liftCoreM checkFixtures

#check_simp_case_fixtures

end Fir.LeanIR.Passes.SimpCaseExamples
