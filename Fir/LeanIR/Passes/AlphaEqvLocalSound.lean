import Fir.LeanIR.Passes.AlphaEqvCode

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.ImpureHygiene

/--
Well-formedness and runtime-metadata premises not supplied by executable
alpha-equivalence. Constructor and instruction metadata equality deliberately
remain the local checker's responsibility.
-/
inductive CodeSideConditions :
    FVarIdMap FVarId → List FVarId → List FVarId →
      LCNF.Code .impure → LCNF.Code .impure → Prop where
  | ret
      (leftScoped : leftScope.contains leftId = true)
      (rightScoped : rightScope.contains rightId = true) :
      CodeSideConditions rho leftScope rightScope
        (.return leftId) (.return rightId)
  | unreachable :
      CodeSideConditions rho leftScope rightScope
        (.unreach leftType) (.unreach rightType)
  | letE
      (typeEq : leftDecl.type = rightDecl.type)
      (leftValueScoped : letValueScoped leftScope leftDecl.value = true)
      (rightValueScoped : letValueScoped rightScope rightDecl.value = true)
      (boxTypesEq : LetValueBoxTypesEq leftDecl.value rightDecl.value)
      (leftFresh : FreshForScope leftDecl.fvarId leftScope)
      (rightFresh : FreshForScope rightDecl.fvarId rightScope)
      (continuation :
        CodeSideConditions (rho.insert rightDecl.fvarId leftDecl.fvarId)
          (leftDecl.fvarId :: leftScope) (rightDecl.fvarId :: rightScope)
          leftContinuation rightContinuation) :
      CodeSideConditions rho leftScope rightScope
        (.let leftDecl leftContinuation) (.let rightDecl rightContinuation)
  | oset
      (leftObjectScoped : leftScope.contains leftObject = true)
      (rightObjectScoped : rightScope.contains rightObject = true)
      (leftFieldScoped : argScoped leftScope leftField = true)
      (rightFieldScoped : argScoped rightScope rightField = true)
      (continuation :
        CodeSideConditions rho leftScope rightScope
          leftContinuation rightContinuation) :
      CodeSideConditions rho leftScope rightScope
        (.oset leftObject leftIndex leftField leftContinuation)
        (.oset rightObject rightIndex rightField rightContinuation)
  | uset
      (leftObjectScoped : leftScope.contains leftObject = true)
      (rightObjectScoped : rightScope.contains rightObject = true)
      (leftFieldScoped : leftScope.contains leftField = true)
      (rightFieldScoped : rightScope.contains rightField = true)
      (continuation :
        CodeSideConditions rho leftScope rightScope
          leftContinuation rightContinuation) :
      CodeSideConditions rho leftScope rightScope
        (.uset leftObject leftIndex leftField leftContinuation)
        (.uset rightObject rightIndex rightField rightContinuation)
  | sset
      (leftObjectScoped : leftScope.contains leftObject = true)
      (rightObjectScoped : rightScope.contains rightObject = true)
      (leftFieldScoped : leftScope.contains leftField = true)
      (rightFieldScoped : rightScope.contains rightField = true)
      (continuation :
        CodeSideConditions rho leftScope rightScope
          leftContinuation rightContinuation) :
      CodeSideConditions rho leftScope rightScope
        (.sset leftObject leftWidth leftOffset leftField leftType leftContinuation)
        (.sset rightObject rightWidth rightOffset rightField rightType rightContinuation)
  | setTag
      (leftObjectScoped : leftScope.contains leftObject = true)
      (rightObjectScoped : rightScope.contains rightObject = true)
      (continuation :
        CodeSideConditions rho leftScope rightScope
          leftContinuation rightContinuation) :
      CodeSideConditions rho leftScope rightScope
        (.setTag leftObject leftTag leftContinuation)
        (.setTag rightObject rightTag rightContinuation)
  | inc
      (leftObjectScoped : leftScope.contains leftObject = true)
      (rightObjectScoped : rightScope.contains rightObject = true)
      (continuation :
        CodeSideConditions rho leftScope rightScope
          leftContinuation rightContinuation) :
      CodeSideConditions rho leftScope rightScope
        (.inc leftObject leftAmount leftCheck leftPersistent leftContinuation)
        (.inc rightObject rightAmount rightCheck rightPersistent rightContinuation)
  | dec
      (leftObjectScoped : leftScope.contains leftObject = true)
      (rightObjectScoped : rightScope.contains rightObject = true)
      (continuation :
        CodeSideConditions rho leftScope rightScope
          leftContinuation rightContinuation) :
      CodeSideConditions rho leftScope rightScope
        (.dec leftObject leftAmount leftCheck leftPersistent leftObjects leftContinuation)
        (.dec rightObject rightAmount rightCheck rightPersistent rightObjects rightContinuation)
  | del
      (leftObjectScoped : leftScope.contains leftObject = true)
      (rightObjectScoped : rightScope.contains rightObject = true)
      (continuation :
        CodeSideConditions rho leftScope rightScope
          leftContinuation rightContinuation) :
      CodeSideConditions rho leftScope rightScope
        (.del leftObject leftContinuation) (.del rightObject rightContinuation)

private theorem reader_andM_run_eq_true_iff
    (left right : ReaderM ρ Bool) (env : ρ) :
    (left <&&> right).run env = true ↔
      left.run env = true ∧ right.run env = true := by
  unfold andM
  simp only [ReaderT.run, ReaderT.bind, Bind.bind, Pure.pure]
  cases h : left env <;> simp [ToBool.toBool, ReaderT.pure]

/--
For the code fragment represented by `CodeRelated`, transparent local
acceptance plus the explicit side conditions constructs the declarative
relation. This theorem is independent of the upstream correspondence axiom.
-/
theorem codeRelated_of_local_accepts
    (side : CodeSideConditions rho leftScope rightScope left right)
    (accepted : Local.AcceptsAt rho left right) :
    CodeRelated rho leftScope rightScope left right := by
  induction side with
  | ret leftScoped rightScoped =>
      exact .terminal
        (terminalCodeRelated_of_local_return leftScoped rightScoped accepted)
  | unreachable => exact .terminal .unreachable
  | letE typeEq leftValueScoped rightValueScoped boxTypesEq
      leftFresh rightFresh continuation continuation_ih =>
      rename_i leftScope' rightScope' leftContinuation rightContinuation
        rho' leftDecl rightDecl
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (LCNF.AlphaEqv.eqvType leftDecl.type rightDecl.type <&&>
            LCNF.AlphaEqv.eqvLetValue leftDecl.value rightDecl.value <&&>
            LCNF.AlphaEqv.withFVar leftDecl.fvarId rightDecl.fvarId
              (Local.eqv fuel leftContinuation rightContinuation)).run rho' = true
            at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [withFVar_run] at accepted
        apply CodeRelated.letE
        · exact letDeclValueRelated_of_eqvLetValue_true typeEq
            leftValueScoped rightValueScoped boxTypesEq accepted.2.1
        · exact leftFresh
        · exact rightFresh
        · exact continuation_ih ⟨fuel, accepted.2.2⟩
  | oset leftObjectScoped rightObjectScoped leftFieldScoped rightFieldScoped
      continuation continuation_ih =>
      rename_i leftScope' leftField rightScope' rightField rho'
        leftContinuation rightContinuation leftObject leftIndex rightObject rightIndex
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (pure (leftIndex == rightIndex) <&&>
            LCNF.AlphaEqv.eqvFVar leftObject rightObject <&&>
            LCNF.AlphaEqv.eqvArg leftField rightField <&&>
            Local.eqv fuel leftContinuation rightContinuation).run rho' = true
            at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        have indexEq : leftIndex = rightIndex := eq_of_beq accepted.1
        subst rightIndex
        apply CodeRelated.oset
        · exact ⟨leftObjectScoped, rightObjectScoped, accepted.2.1⟩
        · exact ⟨leftFieldScoped, rightFieldScoped, accepted.2.2.1⟩
        · exact continuation_ih ⟨fuel, accepted.2.2.2⟩
  | uset leftObjectScoped rightObjectScoped leftFieldScoped rightFieldScoped
      continuation continuation_ih =>
      rename_i rho' leftScope' rightScope' leftContinuation rightContinuation
        leftObject leftIndex leftField rightObject rightIndex rightField
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (pure (leftIndex == rightIndex) <&&>
            LCNF.AlphaEqv.eqvFVar leftObject rightObject <&&>
            LCNF.AlphaEqv.eqvFVar leftField rightField <&&>
            Local.eqv fuel leftContinuation rightContinuation).run rho' = true
            at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        have indexEq : leftIndex = rightIndex := eq_of_beq accepted.1
        subst rightIndex
        apply CodeRelated.uset
        · exact ⟨leftObjectScoped, rightObjectScoped, accepted.2.1⟩
        · exact ⟨leftFieldScoped, rightFieldScoped, accepted.2.2.1⟩
        · exact continuation_ih ⟨fuel, accepted.2.2.2⟩
  | sset leftObjectScoped rightObjectScoped leftFieldScoped rightFieldScoped
      continuation continuation_ih =>
      rename_i rho' leftScope' rightScope' leftContinuation rightContinuation
        leftObject leftWidth leftOffset leftField leftType
        rightObject rightWidth rightOffset rightField rightType
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (pure (leftWidth == rightWidth) <&&>
            pure (leftOffset == rightOffset) <&&>
            LCNF.AlphaEqv.eqvFVar leftObject rightObject <&&>
            LCNF.AlphaEqv.eqvFVar leftField rightField <&&>
            LCNF.AlphaEqv.eqvType leftType rightType <&&>
            Local.eqv fuel leftContinuation rightContinuation).run rho' = true
            at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        have widthEq : leftWidth = rightWidth := eq_of_beq accepted.1
        have offsetEq : leftOffset = rightOffset := eq_of_beq accepted.2.1
        subst rightWidth
        subst rightOffset
        apply CodeRelated.sset
        · exact ⟨leftObjectScoped, rightObjectScoped, accepted.2.2.1⟩
        · exact ⟨leftFieldScoped, rightFieldScoped, accepted.2.2.2.1⟩
        · exact continuation_ih ⟨fuel, accepted.2.2.2.2.2⟩
  | setTag leftObjectScoped rightObjectScoped continuation continuation_ih =>
      rename_i rho' leftScope' rightScope' leftContinuation rightContinuation
        leftObject leftTag rightObject rightTag
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (pure (leftTag == rightTag) <&&>
            LCNF.AlphaEqv.eqvFVar leftObject rightObject <&&>
            Local.eqv fuel leftContinuation rightContinuation).run rho' = true
            at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        have tagEq : leftTag = rightTag := eq_of_beq accepted.1
        subst rightTag
        apply CodeRelated.setTag
        · exact ⟨leftObjectScoped, rightObjectScoped, accepted.2.1⟩
        · exact continuation_ih ⟨fuel, accepted.2.2⟩
  | inc leftObjectScoped rightObjectScoped continuation continuation_ih =>
      rename_i rho' leftScope' rightScope' leftContinuation rightContinuation
        leftObject leftAmount leftCheck leftPersistent
        rightObject rightAmount rightCheck rightPersistent
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (pure (leftAmount == rightAmount) <&&>
            pure (leftCheck == rightCheck) <&&>
            pure (leftPersistent == rightPersistent) <&&>
            LCNF.AlphaEqv.eqvFVar leftObject rightObject <&&>
            Local.eqv fuel leftContinuation rightContinuation).run rho' = true
            at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        have amountEq : leftAmount = rightAmount := eq_of_beq accepted.1
        have checkEq : leftCheck = rightCheck := eq_of_beq accepted.2.1
        have persistentEq : leftPersistent = rightPersistent :=
          eq_of_beq accepted.2.2.1
        subst rightAmount
        subst rightCheck
        subst rightPersistent
        apply CodeRelated.inc
        · exact ⟨leftObjectScoped, rightObjectScoped, accepted.2.2.2.1⟩
        · exact continuation_ih ⟨fuel, accepted.2.2.2.2⟩
  | dec leftObjectScoped rightObjectScoped continuation continuation_ih =>
      rename_i rho' leftScope' rightScope' leftContinuation rightContinuation
        leftObject leftAmount leftCheck leftPersistent leftObjects
        rightObject rightAmount rightCheck rightPersistent rightObjects
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (pure (leftAmount == rightAmount) <&&>
            pure (leftCheck == rightCheck) <&&>
            pure (leftPersistent == rightPersistent) <&&>
            pure (leftObjects == rightObjects) <&&>
            LCNF.AlphaEqv.eqvFVar leftObject rightObject <&&>
            Local.eqv fuel leftContinuation rightContinuation).run rho' = true
            at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        have amountEq : leftAmount = rightAmount := eq_of_beq accepted.1
        have checkEq : leftCheck = rightCheck := eq_of_beq accepted.2.1
        have persistentEq : leftPersistent = rightPersistent :=
          eq_of_beq accepted.2.2.1
        have objectsEq : leftObjects = rightObjects :=
          eq_of_beq accepted.2.2.2.1
        subst rightAmount
        subst rightCheck
        subst rightPersistent
        subst rightObjects
        apply CodeRelated.dec
        · exact ⟨leftObjectScoped, rightObjectScoped, accepted.2.2.2.2.1⟩
        · exact continuation_ih ⟨fuel, accepted.2.2.2.2.2⟩
  | del leftObjectScoped rightObjectScoped continuation continuation_ih =>
      rename_i rho' leftScope' rightScope' leftContinuation rightContinuation
        leftObject rightObject
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (LCNF.AlphaEqv.eqvFVar leftObject rightObject <&&>
            Local.eqv fuel leftContinuation rightContinuation).run rho' = true
            at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        apply CodeRelated.del
        · exact ⟨leftObjectScoped, rightObjectScoped, accepted.1⟩
        · exact continuation_ih ⟨fuel, accepted.2⟩

end Fir.LeanIR.Passes.AlphaEqv
