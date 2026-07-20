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

/-- Transparent copy of the private occurrence count at one alternative. -/
def shadowGetNumOccs (alts : Array (LCNF.Alt .impure)) (i : Nat) : Nat :=
    Id.run do
  let code := alts[i]!.getCode
  let mut count := 1
  for h : j in (i + 1)...alts.size do
    if LCNF.Code.alphaEqv alts[j].getCode code then
      count := count + 1
  return count

/-- Transparent list recursion for the private maximum-selection loop. -/
def shadowSelectMaxOccs (alts : Array (LCNF.Alt .impure)) :
    List Nat → LCNF.Alt .impure × Nat → LCNF.Alt .impure × Nat
  | [], best => best
  | i :: rest, best =>
      let current := shadowGetNumOccs alts i
      let next := if current > best.2 then (alts[i]!, current) else best
      shadowSelectMaxOccs alts rest next

/-- Transparent copy of the private occurrence counter used by `simpCase`.
The explicit index list is extensionally the compiler's `1...alts.size` loop
and exposes the representative-membership invariant to the kernel. -/
def shadowGetMaxOccs (alts : Array (LCNF.Alt .impure)) :
    LCNF.Alt .impure × Nat :=
  shadowSelectMaxOccs alts (List.range alts.size |>.drop 1)
    (alts[0]!, shadowGetNumOccs alts 0)

theorem shadowSelectMaxOccs_fst_mem
    (bestMem : best.1 ∈ alts)
    (bounded : ∀ i ∈ indices, i < alts.size) :
    (shadowSelectMaxOccs alts indices best).1 ∈ alts := by
  induction indices generalizing best with
  | nil => simpa [shadowSelectMaxOccs] using bestMem
  | cons i rest ih =>
      simp only [shadowSelectMaxOccs]
      apply ih
      · split
        · rw [getElem!_pos alts i (bounded i List.mem_cons_self)]
          exact Array.getElem_mem _
        · exact bestMem
      · intro j member
        exact bounded j (List.mem_cons_of_mem i member)

theorem shadowGetMaxOccs_fst_mem
    (nonempty : alts.size ≠ 0) :
    (shadowGetMaxOccs alts).1 ∈ alts := by
  unfold shadowGetMaxOccs
  apply shadowSelectMaxOccs_fst_mem
  · rw [getElem!_pos alts 0 (by omega)]
    exact Array.getElem_mem _
  · intro i member
    exact List.mem_range.mp (List.mem_of_mem_drop member)

/-- Appending a default cannot change constructor lookup. -/
theorem findCtorAlt_append_default
    (alts : List (LCNF.Alt .impure)) :
    findCtorAlt tag (alts ++ [.default body]) = findCtorAlt tag alts := by
  induction alts with
  | nil => rfl
  | cons alt rest ih =>
      cases alt with
      | alt ctorName params code impossible => nomatch impossible
      | ctorAlt info code _ =>
          simp only [List.cons_append, findCtorAlt]
          split <;> simp_all
      | default code =>
          simpa only [List.cons_append, findCtorAlt] using ih

/-- Once a source default has been found, appending another default leaves the
selected source default unchanged. -/
theorem findDefaultAlt_append_default_of_selected
    (selected : findDefaultAlt alts = some branch) :
    findDefaultAlt (alts ++ [.default body]) = some branch := by
  induction alts with
  | nil => simp [findDefaultAlt] at selected
  | cons alt rest ih =>
      cases alt with
      | alt ctorName params code impossible => nomatch impossible
      | ctorAlt info code _ =>
          simp only [findDefaultAlt] at selected
          simpa only [List.cons_append, findDefaultAlt] using ih selected
      | default code =>
          simpa only [List.cons_append, findDefaultAlt] using selected

theorem findDefaultAlt_append_default_of_none
    (selected : findDefaultAlt alts = none) :
    findDefaultAlt (alts ++ [.default body]) = some body := by
  induction alts with
  | nil => simp [findDefaultAlt]
  | cons alt rest ih =>
      cases alt with
      | alt ctorName params code impossible => nomatch impossible
      | ctorAlt info code _ =>
          simp only [findDefaultAlt] at selected
          simpa only [List.cons_append, findDefaultAlt] using ih selected
      | default code => simp [findDefaultAlt] at selected

theorem exists_mem_getCode_eq_of_findCtorAlt
    (selected : findCtorAlt tag alts = some branch) :
    ∃ alt ∈ alts, alt.getCode = branch := by
  induction alts with
  | nil => simp [findCtorAlt] at selected
  | cons alt rest ih =>
      cases alt with
      | alt ctorName params code impossible => nomatch impossible
      | ctorAlt info code _ =>
          simp only [findCtorAlt] at selected
          split at selected
          · have bodyEq : code = branch := Option.some.inj selected
            exact ⟨.ctorAlt info code, List.mem_cons_self, bodyEq⟩
          · rcases ih selected with ⟨found, member, bodyEq⟩
            exact ⟨found, List.mem_cons_of_mem _ member, bodyEq⟩
      | default code =>
          simp only [findCtorAlt] at selected
          rcases ih selected with ⟨found, member, bodyEq⟩
          exact ⟨found, List.mem_cons_of_mem _ member, bodyEq⟩

theorem exists_mem_getCode_eq_of_findDefaultAlt
    (selected : findDefaultAlt alts = some branch) :
    ∃ alt ∈ alts, alt.getCode = branch := by
  induction alts with
  | nil => simp [findDefaultAlt] at selected
  | cons alt rest ih =>
      cases alt with
      | alt ctorName params code impossible => nomatch impossible
      | ctorAlt info code _ =>
          simp only [findDefaultAlt] at selected
          rcases ih selected with ⟨found, member, bodyEq⟩
          exact ⟨found, List.mem_cons_of_mem _ member, bodyEq⟩
      | default code =>
          simp only [findDefaultAlt, Option.some.injEq] at selected
          subst branch
          exact ⟨.default code, List.mem_cons_self, rfl⟩

/-- Appending a fallback default preserves every already-successful source
selection. This is the structural fact needed by the proof-only fold
intermediate. -/
theorem chooseAlt_append_default_of_selected
    (selected : chooseAlt tag alts = some branch) :
    chooseAlt tag (alts ++ [.default body]) = some branch := by
  unfold chooseAlt at selected ⊢
  rw [findCtorAlt_append_default]
  cases ctor : findCtorAlt tag alts with
  | none =>
      simp only [ctor, Option.orElse_none] at selected ⊢
      exact findDefaultAlt_append_default_of_selected selected
  | some code =>
      simpa only [ctor, Option.orElse_some] using selected

/-- If the source table has no selected constructor or default, appending a
default makes that body the selected fallback. -/
theorem chooseAlt_append_default_of_none
    (selected : chooseAlt tag alts = none) :
    chooseAlt tag (alts ++ [.default body]) = some body := by
  unfold chooseAlt at selected ⊢
  rw [findCtorAlt_append_default]
  cases ctor : findCtorAlt tag alts with
  | some code => simp [ctor] at selected
  | none =>
      simp only [ctor, Option.orElse_none] at selected ⊢
      exact findDefaultAlt_append_default_of_none selected

/-- Every successful table selection is the body of an alternative in the
source list. -/
theorem exists_mem_getCode_eq_of_chooseAlt
    (selected : chooseAlt tag alts = some branch) :
    ∃ alt ∈ alts, alt.getCode = branch := by
  unfold chooseAlt at selected
  cases ctor : findCtorAlt tag alts with
  | some code =>
      have codeEq : code = branch := by simpa [ctor] using selected
      exact exists_mem_getCode_eq_of_findCtorAlt (codeEq ▸ ctor)
  | none =>
      simp only [ctor, Option.orElse_none] at selected
      exact exists_mem_getCode_eq_of_findDefaultAlt selected

/-- Proof-only alpha-fold intermediate. It retains the whole filtered table
and appends the occurrence-count representative as a fallback default. The
compiler output may then remove every constructor alpha-equivalent to that
representative in one isolated alpha step. -/
def shadowAddDefaultMiddle (alts : Array (LCNF.Alt .impure)) :
    Array (LCNF.Alt .impure) :=
  alts.push (.default (shadowGetMaxOccs alts).1.getCode)

theorem chooseAlt_shadowAddDefaultMiddle_of_selected
    (selected : chooseAlt tag alts.toList = some branch) :
    chooseAlt tag (shadowAddDefaultMiddle alts).toList = some branch := by
  simpa [shadowAddDefaultMiddle] using
    chooseAlt_append_default_of_selected
      (body := (shadowGetMaxOccs alts).1.getCode) selected

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
      return (alts.filter fun alt =>
        !LCNF.Code.alphaEqv alt.getCode max.getCode).push
          (.default max.getCode)

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

/-- Default folding never erases the last surviving alternative. In the fold
branch the chosen representative is reintroduced as a default alternative. -/
theorem shadowAddDefaultAlt_size_ne_zero
    (nonempty : alts.size ≠ 0) :
    (shadowAddDefaultAlt alts).size ≠ 0 := by
  unfold shadowAddDefaultAlt
  split
  · simp_all
  · split
    split <;> simp_all

/-- A singleton produced from a non-singleton input is necessarily created by
the folding branch; in particular the input had at least two alternatives. -/
theorem one_lt_size_of_shadowAddDefaultAlt_singleton
    (notSingleton : alts.size ≠ 1)
    (singleton : (shadowAddDefaultAlt alts).size = 1) :
    1 < alts.size := by
  by_cases empty : alts.size = 0
  · have small : alts.size ≤ 1 := by omega
    have unchanged := shadowAddDefaultAlt_eq_of_small (alts := alts) small
    rw [unchanged, empty] at singleton
    omega
  · omega

/-- A singleton created from a non-singleton input is exactly the occurrence
counter's representative reintroduced by the genuine folding branch. -/
theorem shadowAddDefaultAlt_eq_singleton_default_max_of_created
    (notSingleton : alts.size ≠ 1)
    (singleton : (shadowAddDefaultAlt alts).size = 1) :
    shadowAddDefaultAlt alts =
      #[.default (shadowGetMaxOccs alts).1.getCode] := by
  unfold shadowAddDefaultAlt at singleton ⊢
  split
  · simp_all
  · split
    split <;> simp_all
    rename_i pair max occurrences noDefault maxEq occurrencesNe
    have filteredEmpty :
        alts.filter (fun alt =>
          !alt.getCode.alphaEqv max.getCode) = #[] := by
      rw [Array.filter_eq_empty_iff]
      intro alt member
      simp [singleton alt member]
    simp [filteredEmpty]

/-- Every alternative removed by a fold-created singleton is accepted by the
upstream alpha checker against the occurrence-count representative. -/
theorem alphaEqv_shadowGetMaxOccs_of_mem_of_created_singleton
    (notSingleton : alts.size ≠ 1)
    (singleton : (shadowAddDefaultAlt alts).size = 1)
    (member : alt ∈ alts) :
    alt.getCode.alphaEqv (shadowGetMaxOccs alts).1.getCode = true := by
  unfold shadowAddDefaultAlt at singleton
  split at singleton
  · simp_all
  · split at singleton
    split at singleton <;> simp_all

/-- Selector-level presentation of a fold-created singleton. The canonical
middle always selects a body and the folded table always selects the maximum
representative. Their bodies are either definitionally identical (the newly
appended fallback path) or related by the exact upstream alpha check that
caused the source arm to be removed. -/
theorem chooseAlt_foldCreatedSingleton_alpha
    (notSingleton : alts.size ≠ 1)
    (singleton : (shadowAddDefaultAlt alts).size = 1) :
    ∃ middleBody,
      chooseAlt tag (shadowAddDefaultMiddle alts).toList = some middleBody ∧
      chooseAlt tag (shadowAddDefaultAlt alts).toList =
        some (shadowGetMaxOccs alts).1.getCode ∧
      (∃ alt ∈ alts, alt.getCode = middleBody) ∧
      (middleBody = (shadowGetMaxOccs alts).1.getCode ∨
        middleBody.alphaEqv (shadowGetMaxOccs alts).1.getCode = true) := by
  have foldedEq := shadowAddDefaultAlt_eq_singleton_default_max_of_created
    notSingleton singleton
  have foldedSelected :
      chooseAlt tag (shadowAddDefaultAlt alts).toList =
        some (shadowGetMaxOccs alts).1.getCode := by
    simp [foldedEq, chooseAlt, findCtorAlt, findDefaultAlt]
  cases selected : chooseAlt tag alts.toList with
  | none =>
      have nonempty : alts.size ≠ 0 := by
        have bigger := one_lt_size_of_shadowAddDefaultAlt_singleton
          notSingleton singleton
        omega
      refine ⟨(shadowGetMaxOccs alts).1.getCode, ?_, foldedSelected,
        ⟨(shadowGetMaxOccs alts).1,
          shadowGetMaxOccs_fst_mem nonempty, rfl⟩, Or.inl rfl⟩
      simpa [shadowAddDefaultMiddle] using
        chooseAlt_append_default_of_none
          (body := (shadowGetMaxOccs alts).1.getCode) selected
  | some branch =>
      rcases exists_mem_getCode_eq_of_chooseAlt selected with
        ⟨alt, member, bodyEq⟩
      refine ⟨branch, ?_, foldedSelected, ⟨alt, ?_, bodyEq⟩, Or.inr ?_⟩
      · exact chooseAlt_shadowAddDefaultMiddle_of_selected selected
      · simpa using member
      · rw [← bodyEq]
        apply alphaEqv_shadowGetMaxOccs_of_mem_of_created_singleton
          notSingleton singleton
        simpa using member

/-- Existential presentation of the exact representative theorem. -/
theorem shadowAddDefaultAlt_eq_singleton_default_of_created
    (notSingleton : alts.size ≠ 1)
    (singleton : (shadowAddDefaultAlt alts).size = 1) :
    ∃ body, shadowAddDefaultAlt alts = #[.default body] :=
  ⟨(shadowGetMaxOccs alts).1.getCode,
    shadowAddDefaultAlt_eq_singleton_default_max_of_created
      notSingleton singleton⟩

/-- A fold-created singleton selects its sole default body at every tag. -/
theorem chooseAlt_shadowAddDefaultAlt_of_created_singleton
    (notSingleton : alts.size ≠ 1)
    (singleton : (shadowAddDefaultAlt alts).size = 1) :
    chooseAlt tag (shadowAddDefaultAlt alts).toList =
      some (shadowAddDefaultAlt alts)[0]!.getCode := by
  rcases shadowAddDefaultAlt_eq_singleton_default_of_created
      notSingleton singleton with ⟨body, folded⟩
  simp [folded, chooseAlt, findCtorAlt, findDefaultAlt]
  rfl

/-- Pure output projection of Lean's private unreachable-arm filter. -/
def shadowFilterUnreachable (alts : Array (LCNF.Alt .impure)) :
    Array (LCNF.Alt .impure) :=
  alts.filter (!·.getCode matches .unreach ..)

/-- Alternatives after both nonrecursive table rewrites. -/
def shadowPrepareAlts (cases : LCNF.Cases .impure) :
    Array (LCNF.Alt .impure) :=
  shadowAddDefaultAlt (shadowFilterUnreachable cases.alts)

/-- Preparation is exactly unreachable filtering when at most one arm
survives; default folding is inert on that shape. -/
theorem shadowPrepareAlts_eq_filter_of_small
    (small : (shadowFilterUnreachable cases.alts).size ≤ 1) :
    shadowPrepareAlts cases = shadowFilterUnreachable cases.alts := by
  exact shadowAddDefaultAlt_eq_of_small small

/-- The body of a prepared singleton is always inherited from a syntactic
source alternative. In the direct path it is the sole reachable arm; in the
folding path it is the occurrence counter's representative reintroduced as a
default. -/
theorem exists_source_alt_of_shadowPrepareAlts_singleton
    (singleton : (shadowPrepareAlts cases).size = 1) :
    ∃ alt ∈ cases.alts,
      alt.getCode = (shadowPrepareAlts cases)[0]!.getCode := by
  let filtered := shadowFilterUnreachable cases.alts
  have foldedSingleton : (shadowAddDefaultAlt filtered).size = 1 := by
    simpa [shadowPrepareAlts, filtered] using singleton
  by_cases filteredSingleton : filtered.size = 1
  · have small : (shadowFilterUnreachable cases.alts).size ≤ 1 := by
      simpa [filtered] using Nat.le_of_eq filteredSingleton
    have preparedEq : shadowPrepareAlts cases = filtered :=
      shadowPrepareAlts_eq_filter_of_small small
    have member : filtered[0]! ∈ filtered := by
      rw [getElem!_pos filtered 0 (by omega)]
      exact Array.getElem_mem _
    refine ⟨filtered[0]!, ?_, ?_⟩
    · exact Array.mem_of_mem_filter member
    · rw [preparedEq]
  · have filteredNonempty : filtered.size ≠ 0 := by
      intro empty
      have small : filtered.size ≤ 1 := by omega
      have unchanged := shadowAddDefaultAlt_eq_of_small
        (alts := filtered) small
      rw [unchanged, empty] at foldedSingleton
      omega
    have representativeMember : (shadowGetMaxOccs filtered).1 ∈ filtered :=
      shadowGetMaxOccs_fst_mem filteredNonempty
    have foldedEq :=
      shadowAddDefaultAlt_eq_singleton_default_max_of_created
        filteredSingleton foldedSingleton
    refine ⟨(shadowGetMaxOccs filtered).1,
      Array.mem_of_mem_filter representativeMember, ?_⟩
    rw [show shadowPrepareAlts cases = shadowAddDefaultAlt filtered by rfl,
      foldedEq]
    rfl

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

/-- Any successful selection from a singleton alternative list returns that
alternative's body, regardless of whether it is a matching constructor or a
default. -/
theorem chooseAlt_singleton_eq_some_getCode
    (selected : chooseAlt tag [alt] = some branch) :
    branch = alt.getCode := by
  cases alt with
  | alt ctorName params code impossible =>
      cases impossible
  | ctorAlt info code _ =>
      simp [chooseAlt, findCtorAlt, findDefaultAlt] at selected
      change branch = code
      exact selected.2.symm
  | default code =>
      simp [chooseAlt, findCtorAlt, findDefaultAlt] at selected
      change branch = code
      exact selected.symm

/-- A reachable selected arm prevents the complete preparation pipeline from
producing an empty table. Filtering preserves that arm and default folding
cannot erase the last survivor. -/
theorem shadowPrepareAlts_size_ne_zero_of_selected
    (selected : chooseAlt tag cases.alts.toList = some branch)
    (reachable : Fir.LeanIR.Passes.SimpCase.isUnreachable branch = false) :
    (shadowPrepareAlts cases).size ≠ 0 := by
  have selectedFiltered :=
    chooseAlt_shadowFilterUnreachable_of_selected selected reachable
  have filterNonempty : (shadowFilterUnreachable cases.alts).size ≠ 0 := by
    intro empty
    have filterEq : shadowFilterUnreachable cases.alts = #[] :=
      Array.size_eq_zero_iff.mp empty
    rw [filterEq] at selectedFiltered
    simp [chooseAlt, findCtorAlt, findDefaultAlt] at selectedFiltered
  exact shadowAddDefaultAlt_size_ne_zero filterNonempty

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
