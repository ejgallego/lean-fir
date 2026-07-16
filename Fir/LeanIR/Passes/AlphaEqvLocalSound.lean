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
  | cases
      (leftDiscrScoped : leftScope.contains leftCases.discr = true)
      (rightDiscrScoped : rightScope.contains rightCases.discr = true)
      (leftNormalization : CaseTableNormalizationInvariant leftCases.alts)
      (rightNormalization : CaseTableNormalizationInvariant rightCases.alts)
      (ctorBranches : ∀ tag leftCode rightCode,
        HasCtorAlt tag leftCode leftCases.alts.toList →
        HasCtorAlt tag rightCode rightCases.alts.toList →
        CodeSideConditions rho leftScope rightScope leftCode rightCode)
      (defaultBranches : ∀ leftCode rightCode,
        HasDefaultAlt leftCode leftCases.alts.toList →
        HasDefaultAlt rightCode rightCases.alts.toList →
        CodeSideConditions rho leftScope rightScope leftCode rightCode) :
      CodeSideConditions rho leftScope rightScope
        (.cases leftCases) (.cases rightCases)
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

/-- Side conditions for one impure case alternative. -/
inductive AltSideConditions (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) :
    LCNF.Alt .impure → LCNF.Alt .impure → Prop where
  | ctor
      (code : CodeSideConditions rho leftScope rightScope leftCode rightCode) :
      AltSideConditions rho leftScope rightScope
        (.ctorAlt leftInfo leftCode) (.ctorAlt rightInfo rightCode)
  | default
      (code : CodeSideConditions rho leftScope rightScope leftCode rightCode) :
      AltSideConditions rho leftScope rightScope
        (.default leftCode) (.default rightCode)

/-- Pointwise side conditions for an ordered impure alternative table. -/
abbrev AltsSideConditions (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    (left right : List (LCNF.Alt .impure)) : Prop :=
  ListRel (AltSideConditions rho leftScope rightScope) left right

/--
Branch side conditions indexed by the selectors observed by the interpreter.
Unlike a pointwise list relation, this remains applicable after alternatives
are reordered for comparison.
-/
structure CaseBranchesSideConditions (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    (left right : List (LCNF.Alt .impure)) : Prop where
  ctor : ∀ tag leftCode rightCode,
    HasCtorAlt tag leftCode left → HasCtorAlt tag rightCode right →
      CodeSideConditions rho leftScope rightScope leftCode rightCode
  default : ∀ leftCode rightCode,
    HasDefaultAlt leftCode left → HasDefaultAlt rightCode right →
      CodeSideConditions rho leftScope rightScope leftCode rightCode

private theorem reader_andM_run_eq_true_iff
    (left right : ReaderM ρ Bool) (env : ρ) :
    (left <&&> right).run env = true ↔
      left.run env = true ∧ right.run env = true := by
  unfold andM
  simp only [ReaderT.run, ReaderT.bind, Bind.bind, Pure.pure]
  cases h : left env <;> simp [ToBool.toBool, ReaderT.pure]

private theorem ctorInfo_eq_of_beq_local {left right : LCNF.CtorInfo}
    (equal : (left == right) = true) : left = right := by
  change LCNF.instBEqCtorInfo.beq left right = true at equal
  cases left
  cases right
  simp_all [LCNF.instBEqCtorInfo.beq]

/--
Internal ordered-alternative proof parameterized by soundness callbacks for
selected branch bodies. Keeping the callbacks abstract lets the main code
proof use its structural induction hypotheses when a branch is itself a case.
-/
private theorem altsRelated_of_local_check_by_selector_using
    (ctorSound : ∀ tag leftCode rightCode,
      HasCtorAlt tag leftCode originalLeft →
      HasCtorAlt tag rightCode originalRight →
      Local.AcceptsAt rho leftCode rightCode →
      CodeRelated rho leftScope rightScope leftCode rightCode)
    (defaultSound : ∀ leftCode rightCode,
      HasDefaultAlt leftCode originalLeft →
      HasDefaultAlt rightCode originalRight →
      Local.AcceptsAt rho leftCode rightCode →
      CodeRelated rho leftScope rightScope leftCode rightCode)
    (leftSubset : ∀ alt, alt ∈ left → alt ∈ originalLeft)
    (rightSubset : ∀ alt, alt ∈ right → alt ∈ originalRight)
    (accepted :
      (Local.eqvAltListsUsing (Local.eqv fuel) left right).run rho = true) :
    AltsRelated rho leftScope rightScope left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons rightAlt rightTail =>
          simp [Local.eqvAltListsUsing] at accepted
  | cons leftAlt leftTail ih =>
      cases right with
      | nil => simp [Local.eqvAltListsUsing] at accepted
      | cons rightAlt rightTail =>
          cases leftAlt with
          | alt =>
              rename_i ctorName params code purity
              contradiction
          | ctorAlt =>
              rename_i leftInfo leftCode purity
              cases rightAlt with
              | alt =>
                  rename_i ctorName params code impossible
                  contradiction
              | ctorAlt =>
                  rename_i rightInfo rightCode rightPurity
                  simp only [Local.eqvAltListsUsing] at accepted
                  rw [reader_andM_run_eq_true_iff] at accepted
                  rw [reader_andM_run_eq_true_iff] at accepted
                  have infoEq : leftInfo = rightInfo :=
                    ctorInfo_eq_of_beq_local accepted.1
                  subst rightInfo
                  have leftHas :
                      HasCtorAlt leftInfo.cidx leftCode originalLeft :=
                    ⟨leftInfo, leftSubset _ List.mem_cons_self, by simp⟩
                  have rightHas :
                      HasCtorAlt leftInfo.cidx rightCode originalRight :=
                    ⟨leftInfo, rightSubset _ List.mem_cons_self, by simp⟩
                  exact .cons
                    (.ctor (ctorSound leftInfo.cidx leftCode rightCode
                      leftHas rightHas ⟨fuel, accepted.2.1⟩))
                    (ih
                      (fun alt member =>
                        leftSubset alt (List.mem_cons_of_mem _ member))
                      (fun alt member =>
                        rightSubset alt (List.mem_cons_of_mem _ member))
                      accepted.2.2)
              | default => simp [Local.eqvAltListsUsing] at accepted
          | default =>
              rename_i leftCode
              cases rightAlt with
              | alt =>
                  rename_i ctorName params code impossible
                  contradiction
              | ctorAlt => simp [Local.eqvAltListsUsing] at accepted
              | default =>
                  rename_i rightCode
                  simp only [Local.eqvAltListsUsing] at accepted
                  rw [reader_andM_run_eq_true_iff] at accepted
                  have leftHas : HasDefaultAlt leftCode originalLeft :=
                    leftSubset _ List.mem_cons_self
                  have rightHas : HasDefaultAlt rightCode originalRight :=
                    rightSubset _ List.mem_cons_self
                  exact .cons
                    (.default (defaultSound leftCode rightCode leftHas rightHas
                      ⟨fuel, accepted.1⟩))
                    (ih
                      (fun alt member =>
                        leftSubset alt (List.mem_cons_of_mem _ member))
                      (fun alt member =>
                        rightSubset alt (List.mem_cons_of_mem _ member))
                      accepted.2)

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
  | cases leftDiscrScoped rightDiscrScoped leftNormalization rightNormalization
      ctorBranches defaultBranches ctorBranches_ih defaultBranches_ih =>
      rename_i rho' leftScope' rightScope' leftCases rightCases
      rcases accepted with ⟨_ | fuel, accepted⟩
      · simp [Local.checkAt, Local.eqv] at accepted
      · change
          (LCNF.AlphaEqv.eqvFVar leftCases.discr rightCases.discr <&&>
            LCNF.AlphaEqv.eqvType leftCases.resultType rightCases.resultType <&&>
            Local.eqvAltsUsing (Local.eqv fuel) leftCases.alts rightCases.alts).run
              rho' = true at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        rw [reader_andM_run_eq_true_iff] at accepted
        apply CodeRelated.cases
        · exact ⟨leftDiscrScoped, rightDiscrScoped, accepted.1⟩
        · intro tag
          have alternativesAccepted := accepted.2.2
          unfold Local.eqvAltsUsing at alternativesAccepted
          split at alternativesAccepted
          · have alternativesRelated :=
              altsRelated_of_local_check_by_selector_using
                ctorBranches_ih defaultBranches_ih
                (fun alt member =>
                  (sortAlts_perm leftCases.alts).mem_iff.mpr member)
                (fun alt member =>
                  (sortAlts_perm rightCases.alts).mem_iff.mpr member)
                alternativesAccepted
            rw [chooseAlt_sortAlts_eq leftNormalization]
            rw [chooseAlt_sortAlts_eq rightNormalization]
            exact chooseAlt_related alternativesRelated
          · contradiction
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

/--
An accepting transparent comparison of ordered alternatives constructs the
pointwise semantic relation. Alternative bodies may use the complete fragment
covered by `CodeSideConditions`.
-/
theorem altsRelated_of_local_check
    (side : AltsSideConditions rho leftScope rightScope left right)
    (accepted :
      (Local.eqvAltListsUsing (Local.eqv fuel) left right).run rho = true) :
    AltsRelated rho leftScope rightScope left right := by
  induction side with
  | nil => exact .nil
  | cons head tail tail_ih =>
      cases head with
      | ctor code =>
          rename_i leftCode rightCode leftInfo rightInfo
          simp only [Local.eqvAltListsUsing] at accepted
          rw [reader_andM_run_eq_true_iff] at accepted
          rw [reader_andM_run_eq_true_iff] at accepted
          have infoEq : leftInfo = rightInfo :=
            ctorInfo_eq_of_beq_local accepted.1
          subst rightInfo
          exact .cons
            (.ctor (codeRelated_of_local_accepts code ⟨fuel, accepted.2.1⟩))
            (tail_ih accepted.2.2)
      | default code =>
          rename_i leftCode rightCode
          simp only [Local.eqvAltListsUsing] at accepted
          rw [reader_andM_run_eq_true_iff] at accepted
          exact .cons
            (.default (codeRelated_of_local_accepts code ⟨fuel, accepted.1⟩))
            (tail_ih accepted.2)

/--
An accepting ordered comparison constructs related alternatives when recursive
branch premises are supplied by selector. The subset hypotheses connect each
ordered traversal back to its original interpreter table.
-/
theorem altsRelated_of_local_check_by_selector
    (ctorSound : ∀ tag leftCode rightCode,
      HasCtorAlt tag leftCode originalLeft →
      HasCtorAlt tag rightCode originalRight →
      Local.AcceptsAt rho leftCode rightCode →
      CodeRelated rho leftScope rightScope leftCode rightCode)
    (defaultSound : ∀ leftCode rightCode,
      HasDefaultAlt leftCode originalLeft →
      HasDefaultAlt rightCode originalRight →
      Local.AcceptsAt rho leftCode rightCode →
      CodeRelated rho leftScope rightScope leftCode rightCode)
    (leftSubset : ∀ alt, alt ∈ left → alt ∈ originalLeft)
    (rightSubset : ∀ alt, alt ∈ right → alt ∈ originalRight)
    (accepted :
      (Local.eqvAltListsUsing (Local.eqv fuel) left right).run rho = true) :
    AltsRelated rho leftScope rightScope left right :=
  altsRelated_of_local_check_by_selector_using ctorSound defaultSound
    leftSubset rightSubset accepted

/--
Transparent local acceptance is sound for an impure `cases` node whose
selectors determine unique branch bodies. Quicksort's permutation theorem
makes the checker's sorted traversal interchangeable with interpreter order;
the recursive branch side conditions may contain further case nodes.
-/
theorem codeRelated_cases_of_local_accepts
    (leftDiscrScoped : leftScope.contains leftCases.discr = true)
    (rightDiscrScoped : rightScope.contains rightCases.discr = true)
    (leftNormalization : CaseTableNormalizationInvariant leftCases.alts)
    (rightNormalization : CaseTableNormalizationInvariant rightCases.alts)
    (side : CaseBranchesSideConditions rho leftScope rightScope
      leftCases.alts.toList rightCases.alts.toList)
    (accepted : Local.AcceptsAt rho (.cases leftCases) (.cases rightCases)) :
    CodeRelated rho leftScope rightScope (.cases leftCases) (.cases rightCases) :=
  codeRelated_of_local_accepts
    (.cases leftDiscrScoped rightDiscrScoped leftNormalization rightNormalization
      side.ctor side.default)
    accepted

end Fir.LeanIR.Passes.AlphaEqv
