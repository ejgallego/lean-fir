import Fir.LeanIR.Passes.AlphaEqvCodeReverse

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.ImpureHygiene
open Fir.LeanIR.Passes.SimpCase

/-!
`CodeRelated` records the lexical facts needed by the semantic simulation,
but its case constructor deliberately follows only runtime selections.
`CodeSideConditions`, on the other hand, must also justify that every nested
case table is deterministic before the transparent alpha checker can be
converted to `CodeRelated`.

The tree below isolates exactly that missing endpoint invariant.  Non-case
constructors merely expose their recursive children; case nodes additionally
record selector determinism and recurse through every syntactic alternative.
-/

/-- Selector normalization at every case node in an impure-code tree. -/
inductive CodeNormalizationTree : LCNF.Code .impure → Prop where
  | letE
      (continuationTree : CodeNormalizationTree continuation) :
      CodeNormalizationTree (.let declaration continuation)
  | jp
      (body : CodeNormalizationTree declaration.value)
      (continuationTree : CodeNormalizationTree continuation) :
      CodeNormalizationTree (.jp declaration continuation)
  | jmp : CodeNormalizationTree (.jmp target args)
  | cases
      (root : CaseTableNormalizationInvariant cases.alts)
      (branches : ∀ alt, alt ∈ cases.alts.toList →
        CodeNormalizationTree alt.getCode) :
      CodeNormalizationTree (.cases cases)
  | ret : CodeNormalizationTree (.return fvarId)
  | unreach : CodeNormalizationTree (.unreach type)
  | oset
      (continuationTree : CodeNormalizationTree rest) :
      CodeNormalizationTree (.oset object index field rest)
  | uset
      (continuationTree : CodeNormalizationTree rest) :
      CodeNormalizationTree (.uset object index field rest)
  | sset
      (continuationTree : CodeNormalizationTree rest) :
      CodeNormalizationTree (.sset object width offset field type rest)
  | setTag
      (continuationTree : CodeNormalizationTree rest) :
      CodeNormalizationTree (.setTag object tag rest)
  | inc
      (continuationTree : CodeNormalizationTree rest) :
      CodeNormalizationTree (.inc object amount check persistent rest)
  | dec
      (continuationTree : CodeNormalizationTree rest) :
      CodeNormalizationTree
        (.dec object amount check persistent objects rest)
  | del
      (continuationTree : CodeNormalizationTree rest) :
      CodeNormalizationTree (.del object rest)

/-- Every runtime-observed type annotation in an impure-code tree belongs to
the finite canonical universe produced by LCNF lowering. Only `let`
declarations contribute such annotations; the remaining constructors recurse
through every code position so no hidden branch can escape the invariant. -/
inductive CodeRuntimeTypesCanonical : LCNF.Code .impure → Prop where
  | letE
      (declarationTypes : LetDeclRuntimeTypesCanonical declaration)
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical (.let declaration rest)
  | jp
      (body : CodeRuntimeTypesCanonical declaration.value)
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical (.jp declaration rest)
  | jmp : CodeRuntimeTypesCanonical (.jmp target args)
  | cases
      (branches : ∀ alt, alt ∈ cases.alts.toList →
        CodeRuntimeTypesCanonical alt.getCode) :
      CodeRuntimeTypesCanonical (.cases cases)
  | ret : CodeRuntimeTypesCanonical (.return fvarId)
  | unreach : CodeRuntimeTypesCanonical (.unreach type)
  | oset
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical (.oset object index field rest)
  | uset
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical (.uset object index field rest)
  | sset
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical (.sset object width offset field type rest)
  | setTag
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical (.setTag object tag rest)
  | inc
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical (.inc object amount check persistent rest)
  | dec
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical
        (.dec object amount check persistent objects rest)
  | del
      (continuation : CodeRuntimeTypesCanonical rest) :
      CodeRuntimeTypesCanonical (.del object rest)

/-- Determinism turns constructor membership into the concrete constructor
lookup used by `chooseAlt`. -/
theorem findCtorAlt_eq_some_of_has
    (deterministic : CaseTableDeterministic alts)
    (has : HasCtorAlt tag code alts) :
    findCtorAlt tag alts = some code := by
  cases found : findCtorAlt tag alts with
  | none => exact (not_hasCtorAlt_of_findCtorAlt_eq_none found has).elim
  | some selected =>
      have selectedHas := hasCtorAlt_of_findCtorAlt_eq_some found
      have selectedEq := deterministic.ctor tag selected code selectedHas has
      subst selected
      rfl

/-- Determinism turns default membership into the concrete default lookup
used by `chooseAlt`. -/
theorem findDefaultAlt_eq_some_of_has
    (deterministic : CaseTableDeterministic alts)
    (has : HasDefaultAlt code alts) :
    findDefaultAlt alts = some code := by
  cases found : findDefaultAlt alts with
  | none => exact (not_hasDefaultAlt_of_findDefaultAlt_eq_none found has).elim
  | some selected =>
      have selectedHas := hasDefaultAlt_of_findDefaultAlt_eq_some found
      have selectedEq := deterministic.default selected code selectedHas has
      subst selected
      rfl

mutual

  /-- The reader map is a phantom index of side-condition evidence: all map
  observations belong to the executable checker, not to this invariant. -/
  theorem CodeSideConditions.changeResolver
      (side : CodeSideConditions
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope left right)
      (sigma : FVarIdMap FVarId) :
      CodeSideConditions
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        sigma leftScope rightScope left right :=
    match side with
    | .ret leftScoped rightScoped => .ret leftScoped rightScoped
    | .unreachable => .unreachable
    | .letE typeEq leftValueScoped rightValueScoped boxTypesEq
        leftFresh rightFresh leftJoinFresh rightJoinFresh continuation =>
        .letE typeEq leftValueScoped rightValueScoped boxTypesEq
          leftFresh rightFresh leftJoinFresh rightJoinFresh
          (continuation.changeResolver (sigma.insert _ _))
    | .jp leftFresh rightFresh body continuation =>
        .jp leftFresh rightFresh
          (body.changeResolver sigma)
          (continuation.changeResolver (sigma.insert _ _))
    | .jmp leftTargetScoped rightTargetScoped leftArgsScoped rightArgsScoped =>
        .jmp leftTargetScoped rightTargetScoped
          leftArgsScoped rightArgsScoped
    | .cases leftDiscrScoped rightDiscrScoped leftNormalization
        rightNormalization ctorBranches defaultBranches =>
        .cases leftDiscrScoped rightDiscrScoped
          leftNormalization rightNormalization
          (fun tag leftCode rightCode leftHas rightHas =>
            (ctorBranches tag leftCode rightCode leftHas rightHas).changeResolver
              sigma)
          (fun leftCode rightCode leftHas rightHas =>
            (defaultBranches leftCode rightCode leftHas rightHas).changeResolver
              sigma)
    | .oset leftObjectScoped rightObjectScoped leftFieldScoped
        rightFieldScoped continuation =>
        .oset leftObjectScoped rightObjectScoped
          leftFieldScoped rightFieldScoped (continuation.changeResolver sigma)
    | .uset leftObjectScoped rightObjectScoped leftFieldScoped
        rightFieldScoped continuation =>
        .uset leftObjectScoped rightObjectScoped
          leftFieldScoped rightFieldScoped (continuation.changeResolver sigma)
    | .sset leftObjectScoped rightObjectScoped leftFieldScoped
        rightFieldScoped continuation =>
        .sset leftObjectScoped rightObjectScoped
          leftFieldScoped rightFieldScoped (continuation.changeResolver sigma)
    | .setTag leftObjectScoped rightObjectScoped continuation =>
        .setTag leftObjectScoped rightObjectScoped
          (continuation.changeResolver sigma)
    | .inc leftObjectScoped rightObjectScoped continuation =>
        .inc leftObjectScoped rightObjectScoped
          (continuation.changeResolver sigma)
    | .dec leftObjectScoped rightObjectScoped continuation =>
        .dec leftObjectScoped rightObjectScoped
          (continuation.changeResolver sigma)
    | .del leftObjectScoped rightObjectScoped continuation =>
        .del leftObjectScoped rightObjectScoped
          (continuation.changeResolver sigma)

  /-- Parameter-body side conditions are resolver-independent for the same
  reason as code side conditions. -/
  theorem ParamBodySideConditions.changeResolver
      (side : ParamBodySideConditions
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftParams rightParams left right)
      (sigma : FVarIdMap FVarId) :
      ParamBodySideConditions
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        sigma leftScope rightScope leftParams rightParams left right :=
    match side with
    | .nil body => .nil (body.changeResolver sigma)
    | .cons leftFresh rightFresh leftJoinFresh rightJoinFresh rest =>
        .cons leftFresh rightFresh leftJoinFresh rightJoinFresh
          (rest.changeResolver (sigma.insert _ _))

end

/-- One ordered alternative pair whose recursive bodies were accepted by the
transparent checker at the same fuel. -/
inductive AltCheckRelated (fuel : Nat) (rho : FVarIdMap FVarId) :
    LCNF.Alt .impure → LCNF.Alt .impure → Prop where
  | ctor
      (checked : Local.checkAt fuel rho left right = true) :
      AltCheckRelated fuel rho (.ctorAlt info left) (.ctorAlt info right)
  | default
      (checked : Local.checkAt fuel rho left right = true) :
      AltCheckRelated fuel rho (.default left) (.default right)

abbrev AltsCheckRelated (fuel : Nat) (rho : FVarIdMap FVarId) :=
  ListRel (AltCheckRelated fuel rho)

/-- Lookup results whose selected bodies were accepted by the transparent
checker. -/
inductive SelectionCheckRelated (fuel : Nat) (rho : FVarIdMap FVarId) :
    Option (LCNF.Code .impure) → Option (LCNF.Code .impure) → Prop where
  | none : SelectionCheckRelated fuel rho none none
  | some
      (checked : Local.checkAt fuel rho left right = true) :
      SelectionCheckRelated fuel rho (some left) (some right)

private theorem reader_andM_run_eq_true_iff
    (left right : ReaderM ρ Bool) (env : ρ) :
    (left <&&> right).run env = true ↔
      left.run env = true ∧ right.run env = true := by
  unfold andM
  simp only [ReaderT.run, ReaderT.bind, Bind.bind, Pure.pure]
  cases h : left env <;> simp [ToBool.toBool, ReaderT.pure]

private theorem ctorInfo_eq_of_beq {left right : LCNF.CtorInfo}
    (equal : (left == right) = true) : left = right := by
  change LCNF.instBEqCtorInfo.beq left right = true at equal
  cases left
  cases right
  simp_all [LCNF.instBEqCtorInfo.beq]

/-- Expose the recursive body checks hidden inside one accepted ordered
alternative traversal. -/
theorem altsCheckRelated_of_eqvAltLists
    (accepted :
      (Local.eqvAltListsUsing (Local.eqv fuel) left right).run rho = true) :
    AltsCheckRelated fuel rho left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons rightAlt rightRest =>
          simp [Local.eqvAltListsUsing] at accepted
  | cons leftAlt leftRest ih =>
      cases right with
      | nil => simp [Local.eqvAltListsUsing] at accepted
      | cons rightAlt rightRest =>
          cases leftAlt with
          | alt => contradiction
          | ctorAlt =>
              rename_i leftInfo leftCode purity
              cases rightAlt with
              | alt => contradiction
              | ctorAlt =>
                  rename_i rightInfo rightCode rightPurity
                  simp only [Local.eqvAltListsUsing] at accepted
                  rw [reader_andM_run_eq_true_iff] at accepted
                  rw [reader_andM_run_eq_true_iff] at accepted
                  have infoEq : leftInfo = rightInfo :=
                    ctorInfo_eq_of_beq accepted.1
                  subst rightInfo
                  exact .cons (.ctor accepted.2.1) (ih accepted.2.2)
              | default => simp [Local.eqvAltListsUsing] at accepted
          | default =>
              rename_i leftCode
              cases rightAlt with
              | alt => contradiction
              | ctorAlt => simp [Local.eqvAltListsUsing] at accepted
              | default =>
                  rename_i rightCode
                  simp only [Local.eqvAltListsUsing] at accepted
                  rw [reader_andM_run_eq_true_iff] at accepted
                  exact .cons (.default accepted.1) (ih accepted.2)

/-- Constructor lookup preserves the body-check relation. -/
theorem AltsCheckRelated.findCtor
    (related : AltsCheckRelated fuel rho left right) :
    SelectionCheckRelated fuel rho
      (findCtorAlt tag left) (findCtorAlt tag right) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      cases head with
      | ctor checked =>
          rename_i leftCode rightCode info
          by_cases selected : info.cidx = tag
          · simpa [findCtorAlt, selected] using
              SelectionCheckRelated.some checked
          · simpa [findCtorAlt, selected] using ih
      | default checked => simpa [findCtorAlt] using ih

/-- Default lookup preserves the body-check relation. -/
theorem AltsCheckRelated.findDefault
    (related : AltsCheckRelated fuel rho left right) :
    SelectionCheckRelated fuel rho
      (findDefaultAlt left) (findDefaultAlt right) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      cases head with
      | ctor checked => simpa [findDefaultAlt] using ih
      | default checked =>
          simpa [findDefaultAlt] using SelectionCheckRelated.some checked

/-- An accepted normalized case-table comparison accepts the concrete bodies
selected by any shared constructor tag. -/
theorem ctorCheck_of_eqvAltsUsing
    (leftNormalization : CaseTableNormalizationInvariant left)
    (rightNormalization : CaseTableNormalizationInvariant right)
    (accepted : (Local.eqvAltsUsing (Local.eqv fuel) left right).run rho = true)
    (leftHas : HasCtorAlt tag leftCode left.toList)
    (rightHas : HasCtorAlt tag rightCode right.toList) :
    Local.checkAt fuel rho leftCode rightCode = true := by
  unfold Local.eqvAltsUsing at accepted
  split at accepted
  · have related := altsCheckRelated_of_eqvAltLists accepted
    have selected := related.findCtor (tag := tag)
    have leftFound : findCtorAlt tag left.toList = some leftCode :=
      findCtorAlt_eq_some_of_has leftNormalization.deterministic leftHas
    have rightFound : findCtorAlt tag right.toList = some rightCode :=
      findCtorAlt_eq_some_of_has rightNormalization.deterministic rightHas
    have leftSorted :
        findCtorAlt tag (LCNF.AlphaEqv.sortAlts left).toList =
          some leftCode := by
      rw [← findCtorAlt_eq_of_perm leftNormalization.deterministic
        (sortAlts_perm left)]
      exact leftFound
    have rightSorted :
        findCtorAlt tag (LCNF.AlphaEqv.sortAlts right).toList =
          some rightCode := by
      rw [← findCtorAlt_eq_of_perm rightNormalization.deterministic
        (sortAlts_perm right)]
      exact rightFound
    rw [leftSorted, rightSorted] at selected
    cases selected with
    | some checked => exact checked
  · contradiction

/-- An accepted normalized case-table comparison accepts the concrete
default bodies on both sides. -/
theorem defaultCheck_of_eqvAltsUsing
    (leftNormalization : CaseTableNormalizationInvariant left)
    (rightNormalization : CaseTableNormalizationInvariant right)
    (accepted : (Local.eqvAltsUsing (Local.eqv fuel) left right).run rho = true)
    (leftHas : HasDefaultAlt leftCode left.toList)
    (rightHas : HasDefaultAlt rightCode right.toList) :
    Local.checkAt fuel rho leftCode rightCode = true := by
  unfold Local.eqvAltsUsing at accepted
  split at accepted
  · have related := altsCheckRelated_of_eqvAltLists accepted
    have selected := related.findDefault
    have leftFound : findDefaultAlt left.toList = some leftCode :=
      findDefaultAlt_eq_some_of_has leftNormalization.deterministic leftHas
    have rightFound : findDefaultAlt right.toList = some rightCode :=
      findDefaultAlt_eq_some_of_has rightNormalization.deterministic rightHas
    have leftSorted :
        findDefaultAlt (LCNF.AlphaEqv.sortAlts left).toList =
          some leftCode := by
      rw [← findDefaultAlt_eq_of_perm leftNormalization.deterministic
        (sortAlts_perm left)]
      exact leftFound
    have rightSorted :
        findDefaultAlt (LCNF.AlphaEqv.sortAlts right).toList =
          some rightCode := by
      rw [← findDefaultAlt_eq_of_perm rightNormalization.deterministic
        (sortAlts_perm right)]
      exact rightFound
    rw [leftSorted, rightSorted] at selected
    cases selected with
    | some checked => exact checked
  · contradiction

set_option linter.unusedVariables false in
mutual

  /-- The exact runtime-observed type compatibility not recoverable from
  executable alpha equivalence. Structural constructors merely expose the
  recursive positions; value bindings additionally require exact declaration
  result types and exact boxed scalar types. -/
  inductive CodeRuntimeTypesEq :
      LCNF.Code .impure → LCNF.Code .impure → Prop where
    | ret : CodeRuntimeTypesEq (.return left) (.return right)
    | unreach : CodeRuntimeTypesEq (.unreach leftType) (.unreach rightType)
    | letE
        (typeEq : leftDecl.type = rightDecl.type)
        (boxTypesEq : LetValueBoxTypesEq leftDecl.value rightDecl.value)
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq
          (.let leftDecl leftRest) (.let rightDecl rightRest)
    | jp
        (body : ParamRuntimeTypesEq
          leftDecl.params.toList rightDecl.params.toList
          leftDecl.value rightDecl.value)
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq (.jp leftDecl leftRest) (.jp rightDecl rightRest)
    | jmp : CodeRuntimeTypesEq
        (.jmp leftTarget leftArgs) (.jmp rightTarget rightArgs)
    | cases
        (ctorBranches : ∀ tag leftCode rightCode,
          HasCtorAlt tag leftCode leftCases.alts.toList →
          HasCtorAlt tag rightCode rightCases.alts.toList →
          CodeRuntimeTypesEq leftCode rightCode)
        (defaultBranches : ∀ leftCode rightCode,
          HasDefaultAlt leftCode leftCases.alts.toList →
          HasDefaultAlt rightCode rightCases.alts.toList →
          CodeRuntimeTypesEq leftCode rightCode) :
        CodeRuntimeTypesEq (.cases leftCases) (.cases rightCases)
    | oset
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq
          (.oset leftObject leftIndex leftField leftRest)
          (.oset rightObject rightIndex rightField rightRest)
    | uset
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq
          (.uset leftObject leftIndex leftField leftRest)
          (.uset rightObject rightIndex rightField rightRest)
    | sset
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq
          (.sset leftObject leftWidth leftOffset leftField leftType leftRest)
          (.sset rightObject rightWidth rightOffset rightField rightType rightRest)
    | setTag
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq
          (.setTag leftObject leftTag leftRest)
          (.setTag rightObject rightTag rightRest)
    | inc
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq
          (.inc leftObject leftAmount leftCheck leftPersistent leftRest)
          (.inc rightObject rightAmount rightCheck rightPersistent rightRest)
    | dec
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq
          (.dec leftObject leftAmount leftCheck leftPersistent leftObjects leftRest)
          (.dec rightObject rightAmount rightCheck rightPersistent rightObjects rightRest)
    | del
        (continuation : CodeRuntimeTypesEq leftRest rightRest) :
        CodeRuntimeTypesEq
          (.del leftObject leftRest) (.del rightObject rightRest)

  /-- Parameter-list shape for recursive runtime-type compatibility. Parameter
  types themselves are not runtime-observed by the impure interpreter. -/
  inductive ParamRuntimeTypesEq :
      List (LCNF.Param .impure) → List (LCNF.Param .impure) →
      LCNF.Code .impure → LCNF.Code .impure → Prop where
    | nil
        (body : CodeRuntimeTypesEq left right) :
        ParamRuntimeTypesEq [] [] left right
    | cons
        (rest : ParamRuntimeTypesEq leftRest rightRest left right) :
        ParamRuntimeTypesEq
          (leftParam :: leftRest) (rightParam :: rightRest) left right

end

/-- Lift one body compatibility proof through identical parameter lists. -/
theorem ParamRuntimeTypesEq.reflParams
    (params : List (LCNF.Param .impure))
    (body : CodeRuntimeTypesEq left right) :
    ParamRuntimeTypesEq params params left right :=
  match params with
  | [] => .nil body
  | _ :: rest => .cons (reflParams rest body)

/-- Recursive selector normalization is sufficient to make exact runtime-type
compatibility reflexive, including tables with duplicate selectors whose
bodies are definitionally equal by determinism. -/
theorem CodeNormalizationTree.runtimeTypesRefl
    (normalization : CodeNormalizationTree code) :
    CodeRuntimeTypesEq code code :=
  match normalization with
  | .letE continuation =>
      .letE rfl (by
        rename_i rest declaration
        cases declaration.value <;> simp [LetValueBoxTypesEq])
        continuation.runtimeTypesRefl
  | .jp body continuation =>
      .jp (ParamRuntimeTypesEq.reflParams _ body.runtimeTypesRefl)
        continuation.runtimeTypesRefl
  | .jmp => .jmp
  | .cases root branches =>
      .cases
        (fun tag leftCode rightCode leftHas rightHas => by
          have codeEq := root.deterministic.ctor
            tag leftCode rightCode leftHas rightHas
          subst rightCode
          rcases leftHas with ⟨info, member, _⟩
          exact (branches (.ctorAlt info leftCode) member).runtimeTypesRefl)
        (fun leftCode rightCode leftHas rightHas => by
          have codeEq := root.deterministic.default
            leftCode rightCode leftHas rightHas
          subst rightCode
          exact (branches (.default leftCode) leftHas).runtimeTypesRefl)
  | .ret => .ret
  | .unreach => .unreach
  | .oset continuation => .oset continuation.runtimeTypesRefl
  | .uset continuation => .uset continuation.runtimeTypesRefl
  | .sset continuation => .sset continuation.runtimeTypesRefl
  | .setTag continuation => .setTag continuation.runtimeTypesRefl
  | .inc continuation => .inc continuation.runtimeTypesRefl
  | .dec continuation => .dec continuation.runtimeTypesRefl
  | .del continuation => .del continuation.runtimeTypesRefl

mutual

  /-- Combine endpoint well-formedness with only the exact cross-code runtime
  type facts. Every scope, freshness, and normalization premise is inherited
  from the corresponding reflexive endpoint certificate. -/
  theorem CodeRuntimeTypesEq.sideConditions
      (compatible : CodeRuntimeTypesEq left right)
      (leftSelf : CodeSideConditions
        (leftJoins := leftJoins) (rightJoins := leftJoins)
        leftRho leftScope leftScope left left)
      (rightSelf : CodeSideConditions
        (leftJoins := rightJoins) (rightJoins := rightJoins)
        rightRho rightScope rightScope right right) :
      CodeSideConditions
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope left right :=
    match compatible, leftSelf, rightSelf with
    | .ret, .ret leftScoped _, .ret _ rightScoped =>
        .ret leftScoped rightScoped
    | .unreach, .unreachable, .unreachable => .unreachable
    | .letE typeEq boxTypesEq continuation,
        .letE _ leftValueScoped _ _ leftFresh _ leftJoinFresh _ leftRest,
        .letE _ _ rightValueScoped _ _ rightFresh _ rightJoinFresh rightRest =>
        .letE typeEq leftValueScoped rightValueScoped boxTypesEq
          leftFresh rightFresh leftJoinFresh rightJoinFresh
          (continuation.sideConditions leftRest rightRest)
    | .jp body continuation,
        .jp leftFresh _ leftBody leftRest,
        .jp _ rightFresh rightBody rightRest =>
        .jp leftFresh rightFresh
          (body.sideConditions leftBody rightBody)
          (continuation.sideConditions leftRest rightRest)
    | .jmp, .jmp leftTargetScoped _ leftArgsScoped _,
        .jmp _ rightTargetScoped _ rightArgsScoped =>
        .jmp leftTargetScoped rightTargetScoped leftArgsScoped rightArgsScoped
    | .cases ctorCompatible defaultCompatible,
        .cases leftDiscrScoped _ leftNormalization _ leftCtor leftDefault,
        .cases _ rightDiscrScoped _ rightNormalization rightCtor rightDefault =>
        .cases leftDiscrScoped rightDiscrScoped
          leftNormalization rightNormalization
          (fun tag leftCode rightCode leftHas rightHas =>
            (ctorCompatible tag leftCode rightCode leftHas rightHas).sideConditions
              (leftCtor tag leftCode leftCode leftHas leftHas)
              (rightCtor tag rightCode rightCode rightHas rightHas))
          (fun leftCode rightCode leftHas rightHas =>
            (defaultCompatible leftCode rightCode leftHas rightHas).sideConditions
              (leftDefault leftCode leftCode leftHas leftHas)
              (rightDefault rightCode rightCode rightHas rightHas))
    | .oset continuation,
        .oset leftObjectScoped _ leftFieldScoped _ leftRest,
        .oset _ rightObjectScoped _ rightFieldScoped rightRest =>
        .oset leftObjectScoped rightObjectScoped
          leftFieldScoped rightFieldScoped
          (continuation.sideConditions leftRest rightRest)
    | .uset continuation,
        .uset leftObjectScoped _ leftFieldScoped _ leftRest,
        .uset _ rightObjectScoped _ rightFieldScoped rightRest =>
        .uset leftObjectScoped rightObjectScoped
          leftFieldScoped rightFieldScoped
          (continuation.sideConditions leftRest rightRest)
    | .sset continuation,
        .sset leftObjectScoped _ leftFieldScoped _ leftRest,
        .sset _ rightObjectScoped _ rightFieldScoped rightRest =>
        .sset leftObjectScoped rightObjectScoped
          leftFieldScoped rightFieldScoped
          (continuation.sideConditions leftRest rightRest)
    | .setTag continuation,
        .setTag leftObjectScoped _ leftRest,
        .setTag _ rightObjectScoped rightRest =>
        .setTag leftObjectScoped rightObjectScoped
          (continuation.sideConditions leftRest rightRest)
    | .inc continuation,
        .inc leftObjectScoped _ leftRest,
        .inc _ rightObjectScoped rightRest =>
        .inc leftObjectScoped rightObjectScoped
          (continuation.sideConditions leftRest rightRest)
    | .dec continuation,
        .dec leftObjectScoped _ leftRest,
        .dec _ rightObjectScoped rightRest =>
        .dec leftObjectScoped rightObjectScoped
          (continuation.sideConditions leftRest rightRest)
    | .del continuation,
        .del leftObjectScoped _ leftRest,
        .del _ rightObjectScoped rightRest =>
        .del leftObjectScoped rightObjectScoped
          (continuation.sideConditions leftRest rightRest)

  theorem ParamRuntimeTypesEq.sideConditions
      (compatible : ParamRuntimeTypesEq leftParams rightParams left right)
      (leftSelf : ParamBodySideConditions
        (leftJoins := leftJoins) (rightJoins := leftJoins)
        leftRho leftScope leftScope leftParams leftParams left left)
      (rightSelf : ParamBodySideConditions
        (leftJoins := rightJoins) (rightJoins := rightJoins)
        rightRho rightScope rightScope rightParams rightParams right right) :
      ParamBodySideConditions
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftParams rightParams left right :=
    match compatible, leftSelf, rightSelf with
    | .nil body, .nil leftBody, .nil rightBody =>
        .nil (body.sideConditions leftBody rightBody)
    | .cons rest,
        .cons leftFresh _ leftJoinFresh _ leftRest,
        .cons _ rightFresh _ rightJoinFresh rightRest =>
        .cons leftFresh rightFresh leftJoinFresh rightJoinFresh
          (rest.sideConditions leftRest rightRest)

end

mutual

  /-- Forget unary scope and normalization evidence while retaining the exact
  runtime-type compatibility carried by a side-condition proof. -/
  theorem CodeSideConditions.runtimeTypesEq
      (side : CodeSideConditions
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope left right) :
      CodeRuntimeTypesEq left right :=
    match side with
    | .ret _ _ => .ret
    | .unreachable => .unreach
    | .letE typeEq _ _ boxTypesEq _ _ _ _ continuation =>
        .letE typeEq boxTypesEq continuation.runtimeTypesEq
    | .jp _ _ body continuation =>
        .jp body.runtimeTypesEq continuation.runtimeTypesEq
    | .jmp _ _ _ _ => .jmp
    | .cases _ _ _ _ ctorBranches defaultBranches =>
        .cases
          (fun tag leftCode rightCode leftHas rightHas =>
            (ctorBranches tag leftCode rightCode leftHas rightHas).runtimeTypesEq)
          (fun leftCode rightCode leftHas rightHas =>
            (defaultBranches leftCode rightCode leftHas rightHas).runtimeTypesEq)
    | .oset _ _ _ _ continuation => .oset continuation.runtimeTypesEq
    | .uset _ _ _ _ continuation => .uset continuation.runtimeTypesEq
    | .sset _ _ _ _ continuation => .sset continuation.runtimeTypesEq
    | .setTag _ _ continuation => .setTag continuation.runtimeTypesEq
    | .inc _ _ continuation => .inc continuation.runtimeTypesEq
    | .dec _ _ continuation => .dec continuation.runtimeTypesEq
    | .del _ _ continuation => .del continuation.runtimeTypesEq

  theorem ParamBodySideConditions.runtimeTypesEq
      (side : ParamBodySideConditions
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftParams rightParams left right) :
      ParamRuntimeTypesEq leftParams rightParams left right :=
    match side with
    | .nil body => .nil body.runtimeTypesEq
    | .cons _ _ _ _ rest => .cons rest.runtimeTypesEq

end

end Fir.LeanIR.Passes.AlphaEqv
