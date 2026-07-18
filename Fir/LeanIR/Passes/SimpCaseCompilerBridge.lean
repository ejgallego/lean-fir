import Fir.LeanIR.Passes.SimpCaseRelation

namespace Fir.LeanIR.Passes.SimpCaseCompilerBridge

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.NonLockstep.Structural
open Fir.LeanIR.Passes.SimpCaseRelation

/-!
Lean 4.32 exposes `LCNF.simpCase` only as an effectful pass.  Its case
simplifiers and recursive `Code.simpCase` traversal are module-private, and
the latter is also an opaque `partial def`.  Consequently a downstream
kernel theorem cannot mention the actual recursive result.

This module makes that boundary precise without adding an axiom.  The
fuel-indexed shadow below is a transparent copy of the *output-producing*
part of the pinned implementation.  It deliberately omits `eraseCode` calls:
those update compiler bookkeeping but do not contribute to the returned
syntax.  `checkActualAgreement` executes both implementations and rejects a
concrete input when their returned declaration arrays differ.

The kernel theorem `shadowProgram_related` handles arbitrary declarations and
every recursive non-case constructor.  Its sole premise, `CaseBoundarySound`,
is exactly the remaining semantic obligation at each case node.  In
particular, alpha-default folding cannot be hidden in the traversal proof:
the current structural `CodeRel` does not relate alpha-renamed branch binders,
so that obligation must be discharged by a future composed relation.
-/

/-- SHA-256 of `Lean/Compiler/LCNF/SimpCase.lean` in Lean 4.32.0. -/
def lean432SimpCaseSourceSha256 : String :=
  "270df8851deb0a5f4c6a656377e83e2cf237e76f70a36301239781839122620b"

/-- Transparent copy of the private occurrence counter used by `simpCase`. -/
def shadowGetMaxOccs (alts : Array (LCNF.Alt .impure)) :
    LCNF.Alt .impure × Nat := Id.run do
  let mut maxAlt := alts[0]!
  let mut max := getNumOccsOf alts 0
  for h : i in 1...alts.size do
    let curr := getNumOccsOf alts i
    if curr > max then
      maxAlt := alts[i]
      max := curr
  return (maxAlt, max)
where
  getNumOccsOf (alts : Array (LCNF.Alt .impure)) (i : Nat) : Nat := Id.run do
    let code := alts[i]!.getCode
    let mut count := 1
    for h : j in (i + 1)...alts.size do
      if LCNF.Code.alphaEqv alts[j].getCode code then
        count := count + 1
    return count

/-- Pure output projection of Lean's private `addDefaultAlt`. -/
def shadowAddDefaultAlt (alts : Array (LCNF.Alt .impure)) :
    Array (LCNF.Alt .impure) := Id.run do
  if alts.size <= 1 || alts.any (· matches .default ..) then
    return alts
  else
    let (max, occurrences) := shadowGetMaxOccs alts
    if occurrences == 1 then
      return alts
    else
      let mut result := #[]
      let mut first := true
      for alt in alts do
        if LCNF.Code.alphaEqv alt.getCode max.getCode then
          let .ctorAlt _ _ := alt | unreachable!
          if first then
            first := false
        else
          result := result.push alt
      return result.push (.default max.getCode)

theorem shadowAddDefaultAlt_eq_of_small
    (small : alts.size ≤ 1) :
    shadowAddDefaultAlt alts = alts := by
  simp [shadowAddDefaultAlt, small]

theorem shadowAddDefaultAlt_eq_of_hasDefault
    (hasDefault : alts.any (· matches .default ..) = true) :
    shadowAddDefaultAlt alts = alts := by
  by_cases small : alts.size ≤ 1
  · exact shadowAddDefaultAlt_eq_of_small small
  · simp [shadowAddDefaultAlt, small, hasDefault]

/-- Pure output projection of Lean's private unreachable-arm filter. -/
def shadowFilterUnreachable (alts : Array (LCNF.Alt .impure)) :
    Array (LCNF.Alt .impure) :=
  alts.filter (!·.getCode matches .unreach ..)

/-- Alternatives after both nonrecursive table rewrites. -/
def shadowPrepareAlts (cases : LCNF.Cases .impure) :
    Array (LCNF.Alt .impure) :=
  shadowAddDefaultAlt (shadowFilterUnreachable cases.alts)

/-- Pure output projection of Lean's private `simplifyCases`. -/
def shadowSimplifyCases (cases : LCNF.Cases .impure) : LCNF.Code .impure :=
  let alts := shadowPrepareAlts cases
  if alts.size == 0 then
    .unreach cases.resultType
  else if alts.size == 1 then
    alts[0]!.getCode
  else
    .cases (cases.updateAlts alts)

theorem shadowReachablePredicate_eq (code : LCNF.Code .impure) :
    (!code matches .unreach ..) =
      !Fir.LeanIR.Passes.SimpCase.isUnreachable code := by
  cases code <;> rfl

/-- The transparent shadow's array filter is the executable presentation of
FIR's already-proved list specification for unreachable-arm removal. -/
theorem shadowRemoveUnreachable_eq_filter
    (alts : List (LCNF.Alt .impure)) :
    Fir.LeanIR.Passes.SimpCase.removeUnreachable alts =
      alts.filter (fun alt =>
        !Fir.LeanIR.Passes.SimpCase.isUnreachable alt.getCode) := by
  induction alts with
  | nil => rfl
  | cons alt rest ih =>
      cases h : Fir.LeanIR.Passes.SimpCase.isUnreachable alt.getCode <;>
        simp [Fir.LeanIR.Passes.SimpCase.removeUnreachable, h, ih]

theorem shadowFilterUnreachable_toList
    (alts : Array (LCNF.Alt .impure)) :
    (shadowFilterUnreachable alts).toList =
      Fir.LeanIR.Passes.SimpCase.removeUnreachable alts.toList := by
  unfold shadowFilterUnreachable
  rw [Array.toList_filter, shadowRemoveUnreachable_eq_filter]
  apply List.filter_congr
  intro alt member
  exact shadowReachablePredicate_eq alt.getCode

/-- Filtering preserves a concrete selected branch as soon as the phase
evidence rules out that branch being syntactically unreachable. -/
theorem chooseAlt_shadowFilterUnreachable_of_selected
    (selected : chooseAlt tag alts.toList = some branch)
    (reachable : Fir.LeanIR.Passes.SimpCase.isUnreachable branch = false) :
    chooseAlt tag (shadowFilterUnreachable alts).toList = some branch := by
  rw [shadowFilterUnreachable_toList]
  exact Fir.LeanIR.Passes.SimpCase.chooseAlt_removeUnreachable_of_selected
    selected reachable

theorem shadowSimplifyCases_eq_unreach
    (empty : (shadowPrepareAlts cases).size = 0) :
    shadowSimplifyCases cases = .unreach cases.resultType := by
  simp [shadowSimplifyCases, empty]

theorem shadowSimplifyCases_eq_singleton
    (singleton : (shadowPrepareAlts cases).size = 1) :
    shadowSimplifyCases cases =
      (shadowPrepareAlts cases)[0]!.getCode := by
  simp [shadowSimplifyCases, singleton]

theorem shadowSimplifyCases_eq_cases
    (nonempty : (shadowPrepareAlts cases).size ≠ 0)
    (nonsingleton : (shadowPrepareAlts cases).size ≠ 1) :
    shadowSimplifyCases cases =
      .cases (cases.updateAlts (shadowPrepareAlts cases)) := by
  simp [shadowSimplifyCases, nonempty, nonsingleton]

/-- Transform one alternative with a supplied recursive code transformer.
Factoring this nonrecursive layer out makes the case-kernel proof inspectable
without changing the shadow traversal's returned syntax. -/
def shadowAltUsing?
    (recurse : LCNF.Code .impure → Option (LCNF.Code .impure)) :
    LCNF.Alt .impure → Option (LCNF.Alt .impure)
  | .ctorAlt info body =>
      return .ctorAlt info (← recurse body)
  | .default body =>
      return .default (← recurse body)
  | .alt _ _ _ impossible => nomatch impossible

/--
Fuel-indexed, total shadow of the private recursive code traversal.  Running
out of fuel is reported as `none`; no arbitrary syntax is returned.
-/
def shadowCode? : Nat → LCNF.Code .impure → Option (LCNF.Code .impure)
  | 0, .jmp fvarId args => some (.jmp fvarId args)
  | 0, .return fvarId => some (.return fvarId)
  | 0, .unreach type => some (.unreach type)
  | 0, _ => none
  | fuel + 1, code =>
      match code with
      | .cases (.mk typeName resultType discr alts) => do
          let alts ← alts.toList.mapM
            (shadowAltUsing? (shadowCode? fuel))
          return shadowSimplifyCases
            (.mk typeName resultType discr alts.toArray)
      | .jp (.mk fvarId binderName params type body) continuation => do
          let body ← shadowCode? fuel body
          let continuation ← shadowCode? fuel continuation
          return .jp (.mk fvarId binderName params type body) continuation
      | .jmp fvarId args => some (.jmp fvarId args)
      | .return fvarId => some (.return fvarId)
      | .unreach type => some (.unreach type)
      | .let declaration continuation => do
          return .let declaration (← shadowCode? fuel continuation)
      | .oset fvarId index value continuation => do
          return .oset fvarId index value (← shadowCode? fuel continuation)
      | .uset fvarId index value continuation => do
          return .uset fvarId index value (← shadowCode? fuel continuation)
      | .sset fvarId width offset value type continuation => do
          return .sset fvarId width offset value type
            (← shadowCode? fuel continuation)
      | .setTag fvarId tag continuation => do
          return .setTag fvarId tag (← shadowCode? fuel continuation)
      | .inc fvarId amount check persistent continuation => do
          return .inc fvarId amount check persistent
            (← shadowCode? fuel continuation)
      | .dec fvarId amount check persistent objects continuation => do
          return .dec fvarId amount check persistent objects
            (← shadowCode? fuel continuation)
      | .del fvarId continuation => do
          return .del fvarId (← shadowCode? fuel continuation)
      | .fun _ _ impossible => nomatch impossible

def shadowDecl? (fuel : Nat) (declaration : LCNF.Decl .impure) :
    Option (LCNF.Decl .impure) := do
  let value ← declaration.value.mapCodeM (shadowCode? fuel)
  return { declaration with value }

def shadowDecls? (fuel : Nat) :
    List (LCNF.Decl .impure) → Option (List (LCNF.Decl .impure))
  | [] => some []
  | declaration :: rest => do
      return (← shadowDecl? fuel declaration) :: (← shadowDecls? fuel rest)

def shadowProgram? (fuel : Nat) (program : ImpureProgram) :
    Option ImpureProgram := do
  let declarations ← shadowDecls? fuel program.decls.toList
  return { decls := declarations.toArray }

/--
The exact kernel boundary left by the private compiler implementation: every
case result produced by the transparent shadow must inhabit the proof-facing
recursive relation.  All surrounding traversal is proved below.
-/
def CaseBoundarySound
    (validCase : LCNF.Cases .impure → Nat → Prop) : Prop :=
  ∀ fuel cases target,
    shadowCode? (fuel + 1) (.cases cases) = some target →
      CodeRel validCase (.cases cases) target

theorem shadowCode_related
    (caseSound : CaseBoundarySound validCase)
    (run : shadowCode? fuel source = some target) :
    CodeRel validCase source target := by
  induction fuel generalizing source target with
  | zero =>
      cases source <;> simp [shadowCode?] at run
      · subst target
        exact .aligned (.jmp _ _)
      · subst target
        exact .aligned (.return _)
      · subst target
        exact .aligned (.unreach _)
  | succ fuel ih =>
      cases source with
      | «let» declaration continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact .aligned (.let declaration (ih continuationRun))
      | «fun» declaration continuation impossible => nomatch impossible
      | jp declaration continuation =>
          cases declaration with
          | mk fvarId binderName params type body =>
              simp only [shadowCode?] at run
              cases bodyRun : shadowCode? fuel body with
              | none => simp [bodyRun] at run
              | some transformedBody =>
                  cases continuationRun : shadowCode? fuel continuation with
                  | none => simp [bodyRun, continuationRun] at run
                  | some transformedContinuation =>
                      simp [bodyRun, continuationRun] at run
                      subst target
                      exact .aligned (.jp fvarId binderName params type
                        (ih bodyRun) (ih continuationRun))
      | jmp fvarId args =>
          simp [shadowCode?] at run
          subst target
          exact .aligned (.jmp fvarId args)
      | cases cases =>
          exact caseSound fuel cases target run
      | «return» fvarId =>
          simp [shadowCode?] at run
          subst target
          exact .aligned (.return fvarId)
      | unreach type =>
          simp [shadowCode?] at run
          subst target
          exact .aligned (.unreach type)
      | oset fvarId index value continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact .aligned (.oset fvarId index value (ih continuationRun))
      | uset fvarId index value continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact .aligned (.uset fvarId index value (ih continuationRun))
      | sset fvarId width offset value type continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact .aligned
                (.sset fvarId width offset value type (ih continuationRun))
      | setTag fvarId tag continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact .aligned (.setTag fvarId tag (ih continuationRun))
      | inc fvarId amount check persistent continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact .aligned
                (.inc fvarId amount check persistent (ih continuationRun))
      | dec fvarId amount check persistent objects continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact .aligned (.dec fvarId amount check persistent objects
                (ih continuationRun))
      | del fvarId continuation =>
          simp only [shadowCode?] at run
          cases continuationRun : shadowCode? fuel continuation with
          | none => simp [continuationRun] at run
          | some transformed =>
              simp [continuationRun] at run
              subst target
              exact .aligned (.del fvarId (ih continuationRun))

theorem shadowDecl_related
    (caseSound : CaseBoundarySound validCase)
    (run : shadowDecl? fuel source = some target) :
    DeclRelated (CodeRel validCase) source target := by
  rcases source with ⟨signature, value, recursive, inlineAttr⟩
  cases value with
  | code code =>
      cases codeRun : shadowCode? fuel code with
      | none =>
          simp [shadowDecl?, LCNF.DeclValue.mapCodeM, codeRun] at run
      | some transformed =>
          simp [shadowDecl?, LCNF.DeclValue.mapCodeM, codeRun] at run
          subst target
          exact
            (decl_update_code_related
              (declaration := ⟨signature, .code code, recursive, inlineAttr⟩)
              (shadowCode_related caseSound codeRun))
  | extern metadata =>
      simp [shadowDecl?, LCNF.DeclValue.mapCodeM] at run
      subst target
      exact {
        name_eq := rfl
        levelParams_eq := rfl
        type_eq := rfl
        params_eq := rfl
        safe_eq := rfl
        value := .extern metadata
        recursive_eq := rfl
        inlineAttr_eq := rfl
      }

theorem shadowDecls_related
    (caseSound : CaseBoundarySound validCase)
    (run : shadowDecls? fuel source = some target) :
    ListRel (DeclRelated (CodeRel validCase)) source target := by
  induction source generalizing target with
  | nil =>
      simp [shadowDecls?] at run
      subst target
      exact .nil
  | cons declaration rest ih =>
      simp only [shadowDecls?] at run
      cases declarationRun : shadowDecl? fuel declaration with
      | none => simp [declarationRun] at run
      | some transformedDeclaration =>
          cases restRun : shadowDecls? fuel rest with
          | none => simp [declarationRun, restRun] at run
          | some transformedRest =>
              simp [declarationRun, restRun] at run
              subst target
              exact .cons (shadowDecl_related caseSound declarationRun)
                (ih restRun)

/-- Arbitrary-program recursive traversal, reduced to the explicit case edge. -/
theorem shadowProgram_related
    (caseSound : CaseBoundarySound validCase)
    (run : shadowProgram? fuel before = some after) :
    ProgramRelated (CodeRel validCase) before after := by
  unfold shadowProgram? at run
  cases declarationsRun : shadowDecls? fuel before.decls.toList with
  | none => simp [declarationsRun] at run
  | some declarations =>
      simp [declarationsRun] at run
      subst after
      change ListRel (DeclRelated (CodeRel validCase))
        before.decls.toList declarations.toArray.toList
      simpa using shadowDecls_related caseSound declarationsRun

/-- Correctness corollary once the shadow traversal and its case edge close. -/
theorem shadowSamePhaseCorrectOn
    (caseSound : CaseBoundarySound validCase)
    (run : shadowProgram? fuel before = some after) :
    SamePhaseCorrectOn (Impure.semantics externals) before after entries
      (ReachablyReadyAdmissible externals validCase before after) :=
  samePhaseCorrectOn_reachablyReady
    (shadowProgram_related caseSound run)

/--
Execute Lean's actual pass and compare its returned syntax with the transparent
shadow.  This is intentionally executable evidence, not a kernel theorem
about `CoreM`/`IO.RealWorld`.
-/
def checkActualAgreement (fuel : Nat) (before : ImpureProgram) : CoreM Unit := do
  let some expected := shadowProgram? fuel before |
    throwError "simpCase shadow exhausted fuel {fuel}"
  let actual ← LCNF.CompilerM.run
    (LCNF.simpCase.run before.decls) (phase := .impure)
  unless actual == expected.decls do
    throwError "Lean 4.32 simpCase disagrees with FIR's transparent shadow"

end Fir.LeanIR.Passes.SimpCaseCompilerBridge
