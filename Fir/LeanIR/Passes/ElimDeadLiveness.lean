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

/-- Lean 4.33 derives `BEq` and `Hashable` for `FVarId` but does not ship the
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

/-- A collected argument avoids an identifier when it cannot insert that
identifier into the backwards liveness set. -/
def ArgAvoids (forbidden : FVarId) : LCNF.Arg .impure → Prop
  | .erased => True
  | .fvar fvarId => fvarId ≠ forbidden
  | .type _ impossible => nomatch impossible

def ArgsAvoid (forbidden : FVarId)
    (arguments : Array (LCNF.Arg .impure)) : Prop :=
  ∀ argument, argument ∈ arguments.toList → ArgAvoids forbidden argument

/-- Precisely the runtime identifiers that `collectLetValue` may insert,
presented negatively for freshness proofs. -/
def LetValueAvoids (forbidden : FVarId) :
    LCNF.LetValue .impure → Prop
  | .lit _ | .erased => True
  | .fvar fvarId arguments =>
      fvarId ≠ forbidden ∧ ArgsAvoid forbidden arguments
  | .ctor _ arguments | .fap _ arguments | .pap _ arguments =>
      ArgsAvoid forbidden arguments
  | .oproj _ fvarId | .uproj _ fvarId | .sproj _ _ fvarId
  | .reset _ fvarId | .box _ fvarId | .unbox fvarId | .isShared fvarId =>
      fvarId ≠ forbidden
  | .reuse fvarId _ _ arguments =>
      fvarId ≠ forbidden ∧ ArgsAvoid forbidden arguments
  | .proj _ _ _ impossible | .const _ _ _ impossible => nomatch impossible

theorem collectArg_preserves_absent
    (absent : used.contains forbidden = false)
    (avoids : ArgAvoids forbidden argument) :
    (collectArg used argument).contains forbidden = false := by
  cases argument with
  | erased => exact absent
  | fvar fvarId =>
      change fvarId ≠ forbidden at avoids
      simp [collectArg, avoids, absent]
  | type _ impossible => nomatch impossible

theorem collectArgList_preserves_absent
    (absent : used.contains forbidden = false)
    (avoids : ∀ argument, argument ∈ arguments →
      ArgAvoids forbidden argument) :
    (collectArgList used arguments).contains forbidden = false := by
  induction arguments generalizing used with
  | nil => exact absent
  | cons argument rest ih =>
      apply ih
      · exact collectArg_preserves_absent absent
          (avoids argument List.mem_cons_self)
      · intro candidate member
        exact avoids candidate (List.mem_cons_of_mem argument member)

theorem collectArgs_preserves_absent
    (absent : used.contains forbidden = false)
    (avoids : ArgsAvoid forbidden arguments) :
    (collectArgs used arguments).contains forbidden = false :=
  collectArgList_preserves_absent absent avoids

theorem collectLetValue_preserves_absent
    (absent : used.contains forbidden = false)
    (avoids : LetValueAvoids forbidden value) :
    (collectLetValue used value).contains forbidden = false := by
  cases value with
  | lit _ | erased => exact absent
  | fvar fvarId arguments | reuse fvarId _ _ arguments =>
      exact collectArgs_preserves_absent
        (collectArg_preserves_absent (argument := LCNF.Arg.fvar fvarId)
          absent avoids.1)
        avoids.2
  | ctor _ arguments | fap _ arguments | pap _ arguments =>
      exact collectArgs_preserves_absent absent avoids
  | oproj _ fvarId | uproj _ fvarId | sproj _ _ fvarId
  | reset _ fvarId | box _ fvarId | unbox fvarId | isShared fvarId =>
      exact collectArg_preserves_absent
        (argument := LCNF.Arg.fvar fvarId) absent avoids
  | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible

/-- Negative occurrence certificate for every runtime identifier that the
backwards traversal may collect from a code tree.  Binder declarations and
erased type metadata do not occur here because `shadowCode?` never inserts
them merely by visiting their nodes. -/
inductive CodeAvoids (forbidden : FVarId) :
    LCNF.Code .impure → Prop where
  | letE
      (valueAvoids : LetValueAvoids forbidden declaration.value)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden (.let declaration continuation)
  | join
      (bodyAvoids : CodeAvoids forbidden declaration.value)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden (.jp declaration continuation)
  | cases
      (discrAvoids : caseInfo.discr ≠ forbidden)
      (alternativesAvoid : ∀ alternative,
        alternative ∈ caseInfo.alts.toList →
          CodeAvoids forbidden alternative.getCode) :
      CodeAvoids forbidden (.cases caseInfo)
  | jump
      (targetAvoids : target ≠ forbidden)
      (argumentsAvoid : ArgsAvoid forbidden arguments) :
      CodeAvoids forbidden (.jmp target arguments)
  | ret (resultAvoids : result ≠ forbidden) :
      CodeAvoids forbidden (.return result)
  | unreachable (type : Expr) :
      CodeAvoids forbidden (.unreach type)
  | objectSet
      (objectAvoids : object ≠ forbidden)
      (fieldAvoids : ArgAvoids forbidden field)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden (.oset object index field continuation)
  | usizeSet
      (objectAvoids : object ≠ forbidden)
      (fieldAvoids : field ≠ forbidden)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden (.uset object index field continuation)
  | scalarSet
      (objectAvoids : object ≠ forbidden)
      (fieldAvoids : field ≠ forbidden)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden
        (.sset object width offset field type continuation)
  | tagSet
      (objectAvoids : object ≠ forbidden)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden (.setTag object tag continuation)
  | increment
      (objectAvoids : object ≠ forbidden)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden
        (.inc object amount check persistent continuation)
  | decrement
      (objectAvoids : object ≠ forbidden)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden
        (.dec object amount check persistent objects continuation)
  | delete
      (objectAvoids : object ≠ forbidden)
      (continuationAvoids : CodeAvoids forbidden continuation) :
      CodeAvoids forbidden (.del object continuation)

def AltListAvoids (forbidden : FVarId)
    (alternatives : List (LCNF.Alt .impure)) : Prop :=
  ∀ alternative, alternative ∈ alternatives →
    CodeAvoids forbidden alternative.getCode

/-- The transparent alternative loop cannot introduce a forbidden identifier
when neither its seed nor any source alternative can introduce it. -/
theorem shadowAltList_preserves_absent
    (transformCode : UsedLocals → LCNF.Code .impure → Option ShadowResult)
    (transformPreserves : ∀ (initial : UsedLocals)
        (source target : LCNF.Code .impure) (final : UsedLocals),
      initial.contains forbidden = false →
      CodeAvoids forbidden source →
      transformCode initial source = some (target, final) →
        final.contains forbidden = false)
    (initial : UsedLocals) (alternatives : List (LCNF.Alt .impure))
    (transformed : List (LCNF.Alt .impure)) (final : UsedLocals)
    (absent : initial.contains forbidden = false)
    (avoids : AltListAvoids forbidden alternatives)
    (result : shadowAltList? transformCode initial alternatives =
      some (transformed, final)) :
    final.contains forbidden = false := by
  induction alternatives generalizing initial transformed final with
  | nil =>
      simp only [shadowAltList?] at result
      rcases result with ⟨rfl, rfl⟩
      exact absent
  | cons alternative rest ih =>
      cases bodyResult : transformCode initial alternative.getCode with
      | none => simp [shadowAltList?, bodyResult] at result
      | some bodyPair =>
          obtain ⟨body, middle⟩ := bodyPair
          cases restResult : shadowAltList? transformCode middle rest with
          | none => simp [shadowAltList?, bodyResult, restResult] at result
          | some restPair =>
              obtain ⟨transformedRest, finalUsed⟩ := restPair
              have pairEq :
                  (updateAltCode alternative body :: transformedRest,
                    finalUsed) = (transformed, final) := by
                simpa [shadowAltList?, bodyResult, restResult] using result
              have finalEq := congrArg Prod.snd pairEq
              change finalUsed = final at finalEq
              subst final
              apply ih middle transformedRest finalUsed
              · exact transformPreserves initial alternative.getCode
                  body middle absent
                  (avoids alternative List.mem_cons_self) bodyResult
              · intro candidate member
                exact avoids candidate
                  (List.mem_cons_of_mem alternative member)
              · exact restResult

/-- Backwards liveness preserves nonmembership for every identifier avoided
by the entire source tree.  The theorem is deliberately stated for every
successful fuel-bounded traversal, so later graph decompositions can use it
without depending on a particular fuel witness. -/
theorem shadowCode_preserves_absent
    (absent : initial.contains forbidden = false)
    (avoids : CodeAvoids forbidden source)
    (result : shadowCode? fuel initial source = some output) :
    output.2.contains forbidden = false := by
  induction fuel generalizing initial source output with
  | zero =>
      cases source with
      | jmp target arguments =>
          cases avoids with
          | jump targetAvoids argumentsAvoid =>
              simp [shadowCode?] at result
              subst output
              apply collectArgs_preserves_absent
              · simp [targetAvoids, absent]
              · exact argumentsAvoid
      | «return» value =>
          cases avoids with
          | ret resultAvoids =>
              simp [shadowCode?] at result
              subst output
              simp [resultAvoids, absent]
      | unreach type =>
          simp [shadowCode?] at result
          subst output
          exact absent
      | «let» _ _ | jp _ _ | «cases» _ | oset _ _ _ _ | uset _ _ _ _
      | sset _ _ _ _ _ _ | setTag _ _ _ | inc _ _ _ _ _
      | dec _ _ _ _ _ _ | del _ _ | «fun» _ _ _ =>
          simp [shadowCode?] at result
  | succ remaining ih =>
      cases source with
      | «let» declaration continuation =>
          cases avoids with
          | letE valueAvoids continuationAvoids =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationAbsent :=
                    ih absent continuationAvoids continuationResult
                  by_cases keep :
                      declaration.fvarId ∈ continuationOutput.2 ∨
                        safeToElim declaration.value = false
                  · simp [shadowCode?, continuationResult, keep] at result
                    subst output
                    exact collectLetValue_preserves_absent
                      continuationAbsent valueAvoids
                  · simp [shadowCode?, continuationResult, keep] at result
                    subst output
                    exact continuationAbsent
      | jp declaration continuation =>
          cases declaration with
          | mk fvarId binderName params type body =>
              cases avoids with
              | join bodyAvoids continuationAvoids =>
                  cases continuationResult :
                      shadowCode? remaining initial continuation with
                  | none => simp [shadowCode?, continuationResult] at result
                  | some continuationOutput =>
                      have continuationAbsent :=
                        ih absent continuationAvoids continuationResult
                      by_cases keep :
                          continuationOutput.2.contains fvarId = true
                      · cases bodyResult :
                            shadowCode? remaining continuationOutput.2 body with
                        | none =>
                            have keepProp : fvarId ∈ continuationOutput.2 := keep
                            simp [shadowCode?, continuationResult, keepProp,
                              bodyResult] at result
                        | some bodyOutput =>
                            have bodyAbsent :=
                              ih continuationAbsent bodyAvoids bodyResult
                            have keepProp : fvarId ∈ continuationOutput.2 := keep
                            simp [shadowCode?, continuationResult, keepProp,
                              bodyResult] at result
                            subst output
                            exact bodyAbsent
                      · have keepProp : ¬fvarId ∈ continuationOutput.2 := keep
                        simp [shadowCode?, continuationResult, keepProp] at result
                        subst output
                        exact continuationAbsent
      | «cases» caseInfo =>
          cases caseInfo with
          | mk typeName resultType discr alternatives =>
              cases avoids with
              | cases discrAvoids alternativesAvoid =>
                  cases alternativesResult :
                      shadowAltList? (shadowCode? remaining) initial
                        alternatives.toList with
                  | none => simp [shadowCode?, alternativesResult] at result
                  | some alternativesOutput =>
                      obtain ⟨transformed, beforeDiscr⟩ := alternativesOutput
                      have beforeDiscrAbsent :=
                        shadowAltList_preserves_absent
                          (shadowCode? remaining)
                          (fun seed before after final seedAbsent codeAvoids
                              transformedBody =>
                            ih seedAbsent codeAvoids transformedBody)
                          initial alternatives.toList transformed beforeDiscr
                          absent alternativesAvoid alternativesResult
                      simp [shadowCode?, alternativesResult] at result
                      subst output
                      change discr ≠ forbidden at discrAvoids
                      simp [discrAvoids, beforeDiscrAbsent]
      | jmp target arguments =>
          cases avoids with
          | jump targetAvoids argumentsAvoid =>
              simp [shadowCode?] at result
              subst output
              apply collectArgs_preserves_absent
              · simp [targetAvoids, absent]
              · exact argumentsAvoid
      | «return» value =>
          cases avoids with
          | ret resultAvoids =>
              simp [shadowCode?] at result
              subst output
              simp [resultAvoids, absent]
      | unreach type =>
          simp [shadowCode?] at result
          subst output
          exact absent
      | oset object index field continuation =>
          cases avoids with
          | objectSet _ fieldAvoids continuationAvoids =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationAbsent :=
                    ih absent continuationAvoids continuationResult
                  by_cases keep :
                      continuationOutput.2.contains object = true
                  · have keepProp : object ∈ continuationOutput.2 := keep
                    simp [shadowCode?, continuationResult, keepProp] at result
                    subst output
                    exact collectArg_preserves_absent continuationAbsent
                      fieldAvoids
                  · have keepProp : ¬object ∈ continuationOutput.2 := keep
                    simp [shadowCode?, continuationResult, keepProp] at result
                    subst output
                    exact continuationAbsent
      | uset object index field continuation =>
          cases avoids with
          | usizeSet _ fieldAvoids continuationAvoids =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationAbsent :=
                    ih absent continuationAvoids continuationResult
                  by_cases keep :
                      continuationOutput.2.contains object = true
                  · have keepProp : object ∈ continuationOutput.2 := keep
                    simp [shadowCode?, continuationResult, keepProp] at result
                    subst output
                    simp [fieldAvoids, continuationAbsent]
                  · have keepProp : ¬object ∈ continuationOutput.2 := keep
                    simp [shadowCode?, continuationResult, keepProp] at result
                    subst output
                    exact continuationAbsent
      | sset object width offset field type continuation =>
          cases avoids with
          | scalarSet _ fieldAvoids continuationAvoids =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationAbsent :=
                    ih absent continuationAvoids continuationResult
                  by_cases keep :
                      continuationOutput.2.contains object = true
                  · have keepProp : object ∈ continuationOutput.2 := keep
                    simp [shadowCode?, continuationResult, keepProp] at result
                    subst output
                    simp [fieldAvoids, continuationAbsent]
                  · have keepProp : ¬object ∈ continuationOutput.2 := keep
                    simp [shadowCode?, continuationResult, keepProp] at result
                    subst output
                    exact continuationAbsent
      | setTag object tag continuation =>
          cases avoids with
          | tagSet objectAvoids continuationAvoids =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationAbsent :=
                    ih absent continuationAvoids continuationResult
                  simp [shadowCode?, continuationResult] at result
                  subst output
                  simp [objectAvoids, continuationAbsent]
      | inc object amount check persistent continuation =>
          cases avoids with
          | increment objectAvoids continuationAvoids =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationAbsent :=
                    ih absent continuationAvoids continuationResult
                  simp [shadowCode?, continuationResult] at result
                  subst output
                  simp [objectAvoids, continuationAbsent]
      | dec object amount check persistent objects continuation =>
          cases avoids with
          | decrement objectAvoids continuationAvoids =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationAbsent :=
                    ih absent continuationAvoids continuationResult
                  simp [shadowCode?, continuationResult] at result
                  subst output
                  simp [objectAvoids, continuationAbsent]
      | del object continuation =>
          cases avoids with
          | delete objectAvoids continuationAvoids =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationAbsent :=
                    ih absent continuationAvoids continuationResult
                  simp [shadowCode?, continuationResult] at result
                  subst output
                  simp [objectAvoids, continuationAbsent]
      | «fun» _ _ impossible => nomatch impossible

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

theorem collectLetValue_subset
    (used : UsedLocals) (value : LCNF.LetValue .impure) :
    UsedSubset used (collectLetValue used value) := by
  cases value with
  | lit _ | erased => exact .refl used
  | fvar fvarId arguments | reuse fvarId _ _ arguments =>
      exact (usedSubset_insert used fvarId).trans
        (collectArgs_subset (used.insert fvarId) arguments)
  | ctor _ arguments | fap _ arguments | pap _ arguments =>
      exact collectArgs_subset used arguments
  | oproj _ fvarId | uproj _ fvarId | sproj _ _ fvarId
  | reset _ fvarId | box _ fvarId | unbox fvarId | isShared fvarId =>
      exact usedSubset_insert used fvarId
  | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible

/-- Every runtime lookup performed anywhere below a code node is included in
the supplied used set.  Binder metadata and erased type expressions are
deliberately absent: the impure interpreter never inspects them. -/
inductive CodeCovered (used : UsedLocals) : LCNF.Code .impure → Prop where
  | letE
      (valueCovered : LetValueCovered used declaration.value)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used (.let declaration continuation)
  | join
      (bodyCovered : CodeCovered used declaration.value)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used (.jp declaration continuation)
  | cases
      (discrMember : used.contains caseInfo.discr = true)
      (alternativesCovered : ∀ alternative,
        alternative ∈ caseInfo.alts.toList →
          CodeCovered used alternative.getCode) :
      CodeCovered used (.cases caseInfo)
  | jump
      (targetMember : used.contains target = true)
      (argumentsCovered : ArgsCovered used arguments) :
      CodeCovered used (.jmp target arguments)
  | ret (resultMember : used.contains result = true) :
      CodeCovered used (.return result)
  | unreachable (type : Expr) : CodeCovered used (.unreach type)
  | objectSet
      (objectMember : used.contains object = true)
      (fieldCovered : ArgCovered used field)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used (.oset object index field continuation)
  | usizeSet
      (objectMember : used.contains object = true)
      (fieldMember : used.contains field = true)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used (.uset object index field continuation)
  | scalarSet
      (objectMember : used.contains object = true)
      (fieldMember : used.contains field = true)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used (.sset object width offset field type continuation)
  | tagSet
      (objectMember : used.contains object = true)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used (.setTag object tag continuation)
  | increment
      (objectMember : used.contains object = true)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used (.inc object amount check persistent continuation)
  | decrement
      (objectMember : used.contains object = true)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used
        (.dec object amount check persistent objects continuation)
  | delete
      (objectMember : used.contains object = true)
      (continuationCovered : CodeCovered used continuation) :
      CodeCovered used (.del object continuation)

/-- Coverage of an impure case alternative is coverage of its body. -/
def AltCovered (used : UsedLocals) (alternative : LCNF.Alt .impure) : Prop :=
  CodeCovered used alternative.getCode

def AltListCovered (used : UsedLocals)
    (alternatives : List (LCNF.Alt .impure)) : Prop :=
  ∀ alternative, alternative ∈ alternatives → AltCovered used alternative

theorem CodeCovered.mono
    (subset : UsedSubset left right)
    (covered : CodeCovered left code) : CodeCovered right code := by
  induction covered with
  | letE value continuation continuationIH =>
      exact .letE (value.mono subset) continuationIH
  | join body continuation bodyIH continuationIH =>
      exact .join bodyIH continuationIH
  | cases discr alternatives alternativesIH =>
      exact .cases (subset _ discr) fun alternative member =>
        alternativesIH alternative member
  | jump target arguments =>
      exact .jump (subset _ target) (arguments.mono subset)
  | ret result => exact .ret (subset _ result)
  | unreachable type => exact .unreachable type
  | objectSet object field continuation continuationIH =>
      exact .objectSet (subset _ object) (field.mono subset)
        continuationIH
  | usizeSet object field continuation continuationIH =>
      exact .usizeSet (subset _ object) (subset _ field) continuationIH
  | scalarSet object field continuation continuationIH =>
      exact .scalarSet (subset _ object) (subset _ field) continuationIH
  | tagSet object continuation continuationIH =>
      exact .tagSet (subset _ object) continuationIH
  | increment object continuation continuationIH =>
      exact .increment (subset _ object) continuationIH
  | decrement object continuation continuationIH =>
      exact .decrement (subset _ object) continuationIH
  | delete object continuation continuationIH =>
      exact .delete (subset _ object) continuationIH

theorem AltCovered.mono
    (subset : UsedSubset left right)
    (covered : AltCovered left alternative) : AltCovered right alternative := by
  exact CodeCovered.mono subset covered


theorem AltListCovered.mono
    (subset : UsedSubset left right)
    (covered : AltListCovered left alternatives) :
    AltListCovered right alternatives := by
  intro alternative member
  exact (covered alternative member).mono subset

theorem altCovered_updateCode
    (alternative : LCNF.Alt .impure)
    (covered : CodeCovered used code) :
    AltCovered used (updateAltCode alternative code) := by
  cases alternative with
  | ctorAlt info _ => exact covered
  | default _ => exact covered
  | alt _ _ _ impossible => nomatch impossible

/-- The transparent alternative loop preserves both semantic coverage and
monotonic growth of the backwards used set, assuming the same contract for
each transformed body. -/
theorem shadowAltList_spec
    (transformCode : UsedLocals → LCNF.Code .impure → Option ShadowResult)
    (transformSpec : ∀ (initial : UsedLocals)
        (source target : LCNF.Code .impure) (final : UsedLocals),
      transformCode initial source = some (target, final) →
        CodeCovered final target ∧ UsedSubset initial final)
    (initial : UsedLocals) (alternatives : List (LCNF.Alt .impure))
    (transformed : List (LCNF.Alt .impure)) (final : UsedLocals)
    (result : shadowAltList? transformCode initial alternatives =
      some (transformed, final)) :
    AltListCovered final transformed ∧ UsedSubset initial final := by
  induction alternatives generalizing initial transformed final with
  | nil =>
      simp only [shadowAltList?] at result
      cases result
      exact ⟨by intro alternative member; simp at member, .refl initial⟩
  | cons alternative rest ih =>
      cases bodyResult : transformCode initial alternative.getCode with
      | none => simp [shadowAltList?, bodyResult] at result
      | some bodyPair =>
          obtain ⟨body, middle⟩ := bodyPair
          cases restResult : shadowAltList? transformCode middle rest with
          | none => simp [shadowAltList?, bodyResult, restResult] at result
          | some restPair =>
              obtain ⟨transformedRest, finalUsed⟩ := restPair
              have pairEq :
                  (updateAltCode alternative body :: transformedRest,
                    finalUsed) = (transformed, final) := by
                simpa [shadowAltList?, bodyResult, restResult] using result
              have transformedEq := congrArg Prod.fst pairEq
              have finalEq := congrArg Prod.snd pairEq
              simp only [Prod.fst] at transformedEq
              simp only [Prod.snd] at finalEq
              subst transformed
              subst final
              have bodySpec := transformSpec initial alternative.getCode
                body middle bodyResult
              have restSpec := ih middle transformedRest finalUsed restResult
              constructor
              · intro candidate member
                simp only [List.mem_cons] at member
                cases member with
                | inl same =>
                    subst candidate
                    exact (altCovered_updateCode alternative bodySpec.1).mono
                      restSpec.2
                | inr tail => exact restSpec.1 candidate tail
              · exact bodySpec.2.trans restSpec.2

/-- The shadow pass returns a monotone used set that covers every runtime
lookup in the transformed code.  This is the central syntactic invariant
handed to the later environment-insensitive machine simulation. -/
theorem shadowCode_spec
    (result : shadowCode? fuel initial source = some output) :
    CodeCovered output.2 output.1 ∧ UsedSubset initial output.2 := by
  induction fuel generalizing initial source output with
  | zero =>
      cases source with
      | jmp target arguments =>
          simp [shadowCode?] at result
          subst output
          let growth := collectArgs_subset (initial.insert target) arguments
          exact ⟨.jump (growth target (by simp))
              (collectArgs_covers _ _),
            (usedSubset_insert initial target).trans growth⟩
      | «return» value =>
          simp [shadowCode?] at result
          subst output
          exact ⟨.ret (by simp), usedSubset_insert initial value⟩
      | unreach type =>
          simp [shadowCode?] at result
          subst output
          exact ⟨.unreachable type, .refl initial⟩
      | «let» _ _ | jp _ _ | «cases» _ | oset _ _ _ _ | uset _ _ _ _
      | sset _ _ _ _ _ _ | setTag _ _ _ | inc _ _ _ _ _
      | dec _ _ _ _ _ _ | del _ _ | «fun» _ _ _ =>
          simp [shadowCode?] at result
  | succ remaining ih =>
      cases source with
      | «let» declaration continuation =>
          cases continuationResult : shadowCode? remaining initial continuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some continuationOutput =>
              have continuationSpec := ih continuationResult
              by_cases keep : declaration.fvarId ∈ continuationOutput.2 ∨
                  safeToElim declaration.value = false
              · simp [shadowCode?, continuationResult, keep] at result
                subst output
                let growth := collectLetValue_subset continuationOutput.2
                  declaration.value
                exact ⟨.letE (collectLetValue_covers _ _)
                    (continuationSpec.1.mono growth),
                  continuationSpec.2.trans growth⟩
              · simp [shadowCode?, continuationResult, keep] at result
                subst output
                exact continuationSpec
      | jp declaration continuation =>
          cases declaration with
          | mk fvarId binderName params type body =>
              cases continuationResult :
                  shadowCode? remaining initial continuation with
              | none => simp [shadowCode?, continuationResult] at result
              | some continuationOutput =>
                  have continuationSpec := ih continuationResult
                  by_cases keep : continuationOutput.2.contains fvarId = true
                  · cases bodyResult :
                        shadowCode? remaining continuationOutput.2 body with
                    | none =>
                        have keepProp : fvarId ∈ continuationOutput.2 := keep
                        simp [shadowCode?, continuationResult, keepProp, bodyResult]
                          at result
                    | some bodyOutput =>
                        have bodySpec := ih bodyResult
                        have keepProp : fvarId ∈ continuationOutput.2 := keep
                        simp [shadowCode?, continuationResult, keepProp,
                          bodyResult] at result
                        subst output
                        exact ⟨.join bodySpec.1
                            (continuationSpec.1.mono bodySpec.2),
                          continuationSpec.2.trans bodySpec.2⟩
                  · have keepProp : ¬fvarId ∈ continuationOutput.2 := keep
                    simp [shadowCode?, continuationResult, keepProp] at result
                    subst output
                    exact continuationSpec
      | «cases» caseInfo =>
          cases caseInfo with
          | mk typeName resultType discr alternatives =>
              cases alternativesResult :
                  shadowAltList? (shadowCode? remaining) initial
                    alternatives.toList with
              | none => simp [shadowCode?, alternativesResult] at result
              | some alternativesOutput =>
                  obtain ⟨transformed, beforeDiscr⟩ := alternativesOutput
                  simp [shadowCode?, alternativesResult] at result
                  subst output
                  have alternativesSpec := shadowAltList_spec
                    (shadowCode? remaining)
                    (fun seed before after final transformedBody =>
                      ih transformedBody)
                    initial alternatives.toList transformed beforeDiscr
                    alternativesResult
                  let growth := usedSubset_insert beforeDiscr discr
                  constructor
                  · apply CodeCovered.cases
                    · change (beforeDiscr.insert discr).contains discr = true
                      simp
                    intro alternative member
                    have sourceMember : alternative ∈ transformed := by
                      simpa [LCNF.Cases.alts] using member
                    exact (alternativesSpec.1 alternative sourceMember).mono growth
                  · exact alternativesSpec.2.trans growth
      | jmp target arguments =>
          simp [shadowCode?] at result
          subst output
          let growth := collectArgs_subset (initial.insert target) arguments
          exact ⟨.jump (growth target (by simp))
              (collectArgs_covers _ _),
            (usedSubset_insert initial target).trans growth⟩
      | «return» value =>
          simp [shadowCode?] at result
          subst output
          exact ⟨.ret (by simp), usedSubset_insert initial value⟩
      | unreach type =>
          simp [shadowCode?] at result
          subst output
          exact ⟨.unreachable type, .refl initial⟩
      | oset object index field continuation =>
          cases continuationResult : shadowCode? remaining initial continuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some continuationOutput =>
              have continuationSpec := ih continuationResult
              by_cases keep : continuationOutput.2.contains object = true
              · have keepProp : object ∈ continuationOutput.2 := keep
                simp [shadowCode?, continuationResult, keepProp] at result
                subst output
                let growth := collectArg_subset continuationOutput.2 field
                exact ⟨.objectSet (growth object keep)
                    (argCovered_collectArg _ _)
                    (continuationSpec.1.mono growth),
                  continuationSpec.2.trans growth⟩
              · have keepProp : ¬object ∈ continuationOutput.2 := keep
                simp [shadowCode?, continuationResult, keepProp] at result
                subst output
                exact continuationSpec
      | uset object index field continuation =>
          cases continuationResult : shadowCode? remaining initial continuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some continuationOutput =>
              have continuationSpec := ih continuationResult
              by_cases keep : continuationOutput.2.contains object = true
              · have keepProp : object ∈ continuationOutput.2 := keep
                simp [shadowCode?, continuationResult, keepProp] at result
                subst output
                let growth := usedSubset_insert continuationOutput.2 field
                exact ⟨.usizeSet (growth object keep) (by simp)
                    (continuationSpec.1.mono growth),
                  continuationSpec.2.trans growth⟩
              · have keepProp : ¬object ∈ continuationOutput.2 := keep
                simp [shadowCode?, continuationResult, keepProp] at result
                subst output
                exact continuationSpec
      | sset object width offset field type continuation =>
          cases continuationResult : shadowCode? remaining initial continuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some continuationOutput =>
              have continuationSpec := ih continuationResult
              by_cases keep : continuationOutput.2.contains object = true
              · have keepProp : object ∈ continuationOutput.2 := keep
                simp [shadowCode?, continuationResult, keepProp] at result
                subst output
                let growth := usedSubset_insert continuationOutput.2 field
                exact ⟨.scalarSet (growth object keep) (by simp)
                    (continuationSpec.1.mono growth),
                  continuationSpec.2.trans growth⟩
              · have keepProp : ¬object ∈ continuationOutput.2 := keep
                simp [shadowCode?, continuationResult, keepProp] at result
                subst output
                exact continuationSpec
      | setTag object tag continuation =>
          cases continuationResult : shadowCode? remaining initial continuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some continuationOutput =>
              have continuationSpec := ih continuationResult
              simp [shadowCode?, continuationResult] at result
              subst output
              let growth := usedSubset_insert continuationOutput.2 object
              exact ⟨.tagSet (by simp) (continuationSpec.1.mono growth),
                continuationSpec.2.trans growth⟩
      | inc object amount check persistent continuation =>
          cases continuationResult : shadowCode? remaining initial continuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some continuationOutput =>
              have continuationSpec := ih continuationResult
              simp [shadowCode?, continuationResult] at result
              subst output
              let growth := usedSubset_insert continuationOutput.2 object
              exact ⟨.increment (by simp) (continuationSpec.1.mono growth),
                continuationSpec.2.trans growth⟩
      | dec object amount check persistent objects continuation =>
          cases continuationResult : shadowCode? remaining initial continuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some continuationOutput =>
              have continuationSpec := ih continuationResult
              simp [shadowCode?, continuationResult] at result
              subst output
              let growth := usedSubset_insert continuationOutput.2 object
              exact ⟨.decrement (by simp) (continuationSpec.1.mono growth),
                continuationSpec.2.trans growth⟩
      | del object continuation =>
          cases continuationResult : shadowCode? remaining initial continuation with
          | none => simp [shadowCode?, continuationResult] at result
          | some continuationOutput =>
              have continuationSpec := ih continuationResult
              simp [shadowCode?, continuationResult] at result
              subst output
              let growth := usedSubset_insert continuationOutput.2 object
              exact ⟨.delete (by simp) (continuationSpec.1.mono growth),
                continuationSpec.2.trans growth⟩
      | «fun» _ _ impossible => nomatch impossible

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

/-- Binding the same value under the same identifier preserves agreement,
including when that identifier itself is live. -/
theorem EnvsAgreeOn.bindBoth
    (agree : EnvsAgreeOn used left right) :
    EnvsAgreeOn used (bind left binder value) (bind right binder value) := by
  intro fvarId member
  by_cases sameName : binder.name = fvarId.name
  · have sameId : binder = fvarId := by
      cases binder with
      | mk binderName =>
          cases fvarId with
          | mk candidateName => simp_all
    subst fvarId
    simp [lookupValue]
  · rw [lookupValue_bind_of_name_ne left binder fvarId value sameName,
      lookupValue_bind_of_name_ne right binder fvarId value sameName]
    exact agree fvarId member

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
