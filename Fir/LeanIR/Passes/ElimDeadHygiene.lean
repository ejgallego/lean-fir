import Fir.LeanIR.Passes.ElimDeadLiveness
import Fir.LeanIR.Passes.SimpCaseWellFormed

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR.ImpureHygiene
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.SimpCaseScopedBridge
open Fir.LeanIR.Passes.SimpCaseWellFormed

/-!
Proof-facing hygiene consequences for `elimDeadVars`.

The backwards traversal can enlarge one subtree's liveness set with facts
collected from a lexically disjoint subtree.  Local scoping proves that such
facts are references to in-scope identifiers; declaration-wide binder
ownership proves that they cannot name a binder owned by the other subtree.
This module keeps those two obligations explicit.
-/

/-- Every parameter binder has a runtime name different from `forbidden`. -/
def ParamBindersAvoidName (forbidden : FVarId)
    (params : List (LCNF.Param .impure)) : Prop :=
  ∀ param, param ∈ params → forbidden.name ≠ param.fvarId.name

/-- Structural negative ownership certificate for every binder in a code
tree.  Runtime references are intentionally absent; they are supplied by the
separate scoped well-formedness tree. -/
inductive CodeBindersAvoidName (forbidden : FVarId) :
    LCNF.Code .impure → Prop where
  | letE
      (binder : forbidden.name ≠ declaration.fvarId.name)
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.let declaration continuation)
  | join
      (binder : forbidden.name ≠ declaration.fvarId.name)
      (params : ParamBindersAvoidName forbidden declaration.params.toList)
      (bodyAvoids : CodeBindersAvoidName forbidden declaration.value)
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.jp declaration continuation)
  | cases
      (alternatives : ∀ alternative,
        alternative ∈ caseInfo.alts.toList →
          CodeBindersAvoidName forbidden alternative.getCode) :
      CodeBindersAvoidName forbidden (.cases caseInfo)
  | jump : CodeBindersAvoidName forbidden (.jmp target arguments)
  | ret : CodeBindersAvoidName forbidden (.return result)
  | unreachable : CodeBindersAvoidName forbidden (.unreach type)
  | objectSet
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.oset object index field continuation)
  | usizeSet
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.uset object index field continuation)
  | scalarSet
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden
        (.sset object width offset field type continuation)
  | tagSet
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.setTag object tag continuation)
  | increment
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden
        (.inc object amount check persistent continuation)
  | decrement
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden
        (.dec object amount check persistent objects continuation)
  | delete
      (continuationAvoids :
        CodeBindersAvoidName forbidden continuation) :
      CodeBindersAvoidName forbidden (.del object continuation)

private theorem codeAvoidance_caseAlts_sizeOf_lt
    (cases : LCNF.Cases .impure) :
    sizeOf cases.alts.toList < sizeOf (LCNF.Code.cases cases) := by
  rcases cases with ⟨typeName, resultType, discr, alts⟩
  rcases alts with ⟨alts⟩
  simp [LCNF.Cases.alts]
  omega

private theorem codeAvoidance_funDeclValue_sizeOf_lt
    (declaration : LCNF.FunDecl .impure)
    (continuation : LCNF.Code .impure) :
    sizeOf declaration.value <
      sizeOf (LCNF.Code.jp declaration continuation) := by
  cases declaration
  simp_wf
  simp only [LCNF.FunDecl.value]
  omega

private theorem codeAvoidance_altCode_sizeOf_lt_cons
    (alternative : LCNF.Alt .impure)
    (rest : List (LCNF.Alt .impure)) :
    sizeOf alternative.getCode < sizeOf (alternative :: rest) := by
  cases alternative with
  | ctorAlt info code =>
      simp [LCNF.Alt.getCode]
      omega
  | default code =>
      simp [LCNF.Alt.getCode]
      omega
  | alt _ _ _ impossible => nomatch impossible

/- Transparent proof-relevant counterpart of FIR's opaque
`ImpureHygiene.codeBinders`. -/
mutual

  inductive CodeBinderList :
      LCNF.Code .impure → List FVarId → Type where
    | letE
        (continuation : CodeBinderList rest restBinders) :
        CodeBinderList (.let declaration rest)
          (declaration.fvarId :: restBinders)
    | join
        (body : CodeBinderList declaration.value bodyBinders)
        (continuation : CodeBinderList rest restBinders) :
        CodeBinderList (.jp declaration rest)
          (declaration.fvarId ::
            (paramIds declaration.params ++ bodyBinders ++ restBinders))
    | cases
        (alternatives : AltBinderList caseInfo.alts.toList binders) :
        CodeBinderList (.cases caseInfo) binders
    | jump : CodeBinderList (.jmp target arguments) []
    | ret : CodeBinderList (.return result) []
    | unreachable : CodeBinderList (.unreach type) []
    | objectSet
        (continuation : CodeBinderList rest binders) :
        CodeBinderList (.oset object index field rest) binders
    | usizeSet
        (continuation : CodeBinderList rest binders) :
        CodeBinderList (.uset object index field rest) binders
    | scalarSet
        (continuation : CodeBinderList rest binders) :
        CodeBinderList
          (.sset object width offset field type rest) binders
    | tagSet
        (continuation : CodeBinderList rest binders) :
        CodeBinderList (.setTag object tag rest) binders
    | increment
        (continuation : CodeBinderList rest binders) :
        CodeBinderList
          (.inc object amount check persistent rest) binders
    | decrement
        (continuation : CodeBinderList rest binders) :
        CodeBinderList
          (.dec object amount check persistent objects rest) binders
    | delete
        (continuation : CodeBinderList rest binders) :
        CodeBinderList (.del object rest) binders

  inductive AltBinderList :
      List (LCNF.Alt .impure) → List FVarId → Type where
    | nil : AltBinderList [] []
    | ctor
        (body : CodeBinderList code bodyBinders)
        (rest : AltBinderList alternatives restBinders) :
        AltBinderList (.ctorAlt info code :: alternatives)
          (bodyBinders ++ restBinders)
    | default
        (body : CodeBinderList code bodyBinders)
        (rest : AltBinderList alternatives restBinders) :
        AltBinderList (.default code :: alternatives)
          (bodyBinders ++ restBinders)

end

/- Total transparent binder enumeration for a code tree.  The order matches
Lean 4.32's opaque `ImpureHygiene.codeBinders`: declaration binder, join
parameters, join body, then continuation. -/
mutual

  def codeBinderIds : LCNF.Code .impure → List FVarId
    | .let declaration continuation =>
        declaration.fvarId :: codeBinderIds continuation
    | .jp declaration continuation =>
        declaration.fvarId ::
          (paramIds declaration.params ++ codeBinderIds declaration.value ++
            codeBinderIds continuation)
    | .cases caseInfo => altListBinderIds caseInfo.alts.toList
    | .jmp _ _ | .return _ | .unreach _ => []
    | .oset _ _ _ continuation
    | .uset _ _ _ continuation
    | .sset _ _ _ _ _ continuation
    | .setTag _ _ continuation
    | .inc _ _ _ _ continuation
    | .dec _ _ _ _ _ continuation
    | .del _ continuation =>
        codeBinderIds continuation
    | .fun _ _ impossible => nomatch impossible

  termination_by code => sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply codeAvoidance_caseAlts_sizeOf_lt
      | apply codeAvoidance_funDeclValue_sizeOf_lt

  def altListBinderIds :
      List (LCNF.Alt .impure) → List FVarId
    | [] => []
    | alternative :: rest =>
        codeBinderIds alternative.getCode ++ altListBinderIds rest

  termination_by alternatives => sizeOf alternatives
  decreasing_by
    all_goals first
      | apply codeAvoidance_altCode_sizeOf_lt_cons
      | (simp_wf; omega)

end

/- The canonical code enumeration carries its transparent listing witness. -/
mutual

  theorem CodeBinderList.canonicalExists (code : LCNF.Code .impure) :
      Nonempty (CodeBinderList code (codeBinderIds code)) := by
    cases code with
    | «let» declaration continuation =>
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.letE continuationListing⟩
    | jp declaration continuation =>
        rcases CodeBinderList.canonicalExists declaration.value with
          ⟨bodyListing⟩
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.join bodyListing continuationListing⟩
    | cases caseInfo =>
        rcases AltBinderList.canonicalExists caseInfo.alts.toList with
          ⟨alternativesListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.cases alternativesListing⟩
    | jmp target arguments =>
        exact ⟨by
          simpa [codeBinderIds] using
            (CodeBinderList.jump :
              CodeBinderList (.jmp target arguments) [])⟩
    | «return» result =>
        exact ⟨by
          simpa [codeBinderIds] using
            (CodeBinderList.ret :
              CodeBinderList (.return result) [])⟩
    | unreach type =>
        exact ⟨by
          simpa [codeBinderIds] using
            (CodeBinderList.unreachable :
              CodeBinderList (.unreach type) [])⟩
    | oset object index field continuation =>
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.objectSet continuationListing⟩
    | uset object index field continuation =>
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.usizeSet continuationListing⟩
    | sset object width offset field type continuation =>
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.scalarSet continuationListing⟩
    | setTag object tag continuation =>
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.tagSet continuationListing⟩
    | inc object amount check persistent continuation =>
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.increment continuationListing⟩
    | dec object amount check persistent objects continuation =>
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.decrement continuationListing⟩
    | del object continuation =>
        rcases CodeBinderList.canonicalExists continuation with
          ⟨continuationListing⟩
        exact ⟨by
          simpa [codeBinderIds] using
            CodeBinderList.delete continuationListing⟩
    | «fun» _ _ impossible => nomatch impossible

  termination_by sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply codeAvoidance_caseAlts_sizeOf_lt
      | apply codeAvoidance_funDeclValue_sizeOf_lt

  theorem AltBinderList.canonicalExists
      (alternatives : List (LCNF.Alt .impure)) :
      Nonempty
        (AltBinderList alternatives (altListBinderIds alternatives)) := by
    cases alternatives with
    | nil =>
        exact ⟨by
          simpa [altListBinderIds] using
            (AltBinderList.nil : AltBinderList [] [])⟩
    | cons alternative rest =>
        cases alternative with
        | ctorAlt info code =>
            rcases CodeBinderList.canonicalExists code with
              ⟨bodyListing⟩
            rcases AltBinderList.canonicalExists rest with
              ⟨restListing⟩
            exact ⟨by
              simpa [altListBinderIds, LCNF.Alt.getCode] using
                AltBinderList.ctor bodyListing restListing⟩
        | default code =>
            rcases CodeBinderList.canonicalExists code with
              ⟨bodyListing⟩
            rcases AltBinderList.canonicalExists rest with
              ⟨restListing⟩
            exact ⟨by
              simpa [altListBinderIds, LCNF.Alt.getCode] using
                AltBinderList.default bodyListing restListing⟩
        | alt _ _ _ impossible => nomatch impossible

  termination_by sizeOf alternatives
  decreasing_by
    all_goals first
      | apply codeAvoidance_altCode_sizeOf_lt_cons
      | (simp_wf; omega)

end

/- The transparent listing relation is functional: every witness enumerates
exactly the canonical binder list. -/
mutual

  theorem CodeBinderList.binders_eq
      (listing : CodeBinderList code binders) :
      binders = codeBinderIds code := by
    cases listing with
    | letE continuation =>
        rw [continuation.binders_eq]
        simp [codeBinderIds]
    | join body continuation =>
        rw [body.binders_eq, continuation.binders_eq]
        simp [codeBinderIds]
    | cases alternatives =>
        rw [alternatives.binders_eq]
        simp [codeBinderIds]
    | jump => simp [codeBinderIds]
    | ret => simp [codeBinderIds]
    | unreachable => simp [codeBinderIds]
    | objectSet continuation =>
        rw [continuation.binders_eq]
        simp [codeBinderIds]
    | usizeSet continuation =>
        rw [continuation.binders_eq]
        simp [codeBinderIds]
    | scalarSet continuation =>
        rw [continuation.binders_eq]
        simp [codeBinderIds]
    | tagSet continuation =>
        rw [continuation.binders_eq]
        simp [codeBinderIds]
    | increment continuation =>
        rw [continuation.binders_eq]
        simp [codeBinderIds]
    | decrement continuation =>
        rw [continuation.binders_eq]
        simp [codeBinderIds]
    | delete continuation =>
        rw [continuation.binders_eq]
        simp [codeBinderIds]

  termination_by sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply codeAvoidance_caseAlts_sizeOf_lt
      | apply codeAvoidance_funDeclValue_sizeOf_lt

  theorem AltBinderList.binders_eq
      (listing : AltBinderList alternatives binders) :
      binders = altListBinderIds alternatives := by
    cases listing with
    | nil => simp [altListBinderIds]
    | ctor body rest =>
        rw [body.binders_eq, rest.binders_eq]
        simp [altListBinderIds, LCNF.Alt.getCode]
    | default body rest =>
        rw [body.binders_eq, rest.binders_eq]
        simp [altListBinderIds, LCNF.Alt.getCode]

  termination_by sizeOf alternatives
  decreasing_by
    all_goals first
      | apply codeAvoidance_altCode_sizeOf_lt_cons
      | (simp_wf; omega)

end

def BinderNamesAvoid (forbidden : FVarId)
    (binders : List FVarId) : Prop :=
  ∀ binder, binder ∈ binders → forbidden.name ≠ binder.name

def BinderNamesUnique (binders : List FVarId) : Prop :=
  binders.Pairwise (fun left right => left.name ≠ right.name)

/-- Declaration-wide uniqueness includes top-level parameters before the
canonical body enumeration, exactly matching FIR's hygiene policy. -/
def DeclCodeBinderNamesUnique (declaration : LCNF.Decl .impure) : Prop :=
  match declaration.value with
  | .extern _ => BinderNamesUnique (paramIds declaration.params)
  | .code code =>
      BinderNamesUnique
        (paramIds declaration.params ++ codeBinderIds code)

/-- Declaration-body ownership is an exact transparent binder enumeration
plus global runtime-name uniqueness. -/
structure CodeBinderOwnership (code : LCNF.Code .impure) where
  binders : List FVarId
  listing : CodeBinderList code binders
  unique : BinderNamesUnique binders

/-- Canonical ownership requires only the global uniqueness proof; an exact
transparent binder-enumeration witness always exists. -/
theorem CodeBinderOwnership.canonicalExists
    (unique : BinderNamesUnique (codeBinderIds code)) :
    Nonempty (CodeBinderOwnership code) := by
  rcases CodeBinderList.canonicalExists code with ⟨listing⟩
  exact ⟨⟨codeBinderIds code, listing, unique⟩⟩

theorem CodeBinderOwnership.canonicalUnique
    (ownership : CodeBinderOwnership code) :
    BinderNamesUnique (codeBinderIds code) := by
  rw [← ownership.listing.binders_eq]
  exact ownership.unique

/-- Global name uniqueness restricts to the left side of a structural binder
list decomposition. -/
theorem BinderNamesUnique.left_of_append
    (unique : BinderNamesUnique (left ++ right)) :
    BinderNamesUnique left :=
  (List.pairwise_append.mp unique).1

/-- Global name uniqueness restricts to the right side of a structural binder
list decomposition. -/
theorem BinderNamesUnique.right_of_append
    (unique : BinderNamesUnique (left ++ right)) :
    BinderNamesUnique right :=
  (List.pairwise_append.mp unique).2.1

/-- A binder owned by the left subtree is excluded from every binder owned by
the right subtree. -/
theorem BinderNamesUnique.right_avoids_of_mem_left
    (unique : BinderNamesUnique (left ++ right))
    (member : forbidden ∈ left) :
    BinderNamesAvoid forbidden right := by
  intro binder binderMember
  exact unique.rel_of_mem_append member binderMember

/-- A binder owned by the right subtree is excluded from every binder owned by
the left subtree.  This is the reverse traversal direction needed when
backwards liveness has already visited the right subtree. -/
theorem BinderNamesUnique.left_avoids_of_mem_right
    (unique : BinderNamesUnique (left ++ right))
    (member : forbidden ∈ right) :
    BinderNamesAvoid forbidden left := by
  intro binder binderMember
  exact Ne.symm (unique.rel_of_mem_append binderMember member)

/-- The head binder of a structural enumeration is excluded from its tail. -/
theorem BinderNamesUnique.tail_avoids_head
    (unique : BinderNamesUnique (head :: tail)) :
    BinderNamesAvoid head tail := by
  intro binder member
  exact List.rel_of_pairwise_cons unique member

/-- Global name uniqueness restricts to the tail of a structural binder
enumeration. -/
theorem BinderNamesUnique.tail_unique
    (unique : BinderNamesUnique (head :: tail)) :
    BinderNamesUnique tail :=
  List.Pairwise.of_cons unique

theorem codeBinderOwnership_of_declUnique
    (unique :
      BinderNamesUnique (paramIds parameters ++ codeBinderIds code)) :
    Nonempty (CodeBinderOwnership code) :=
  CodeBinderOwnership.canonicalExists unique.right_of_append

/-- A listed alternative inherits exact, unique ownership from the enclosing
alternative list. -/
theorem AltBinderList.ownership_of_mem
    (listing : AltBinderList alternatives binders)
    (unique : BinderNamesUnique binders)
    (member : alternative ∈ alternatives) :
    Nonempty (CodeBinderOwnership alternative.getCode) := by
  cases listing with
  | nil => simp at member
  | ctor body rest =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨⟨_, body, unique.left_of_append⟩⟩
      · exact rest.ownership_of_mem unique.right_of_append member
  | default body rest =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨⟨_, body, unique.left_of_append⟩⟩
      · exact rest.ownership_of_mem unique.right_of_append member

/-- A let continuation inherits ownership from its containing code tree. -/
def CodeBinderOwnership.letContinuation
    (ownership :
      CodeBinderOwnership (.let declaration continuation)) :
    CodeBinderOwnership continuation := by
  rcases ownership with ⟨binders, listing, unique⟩
  cases listing with
  | letE continuationListing =>
      exact ⟨_, continuationListing, unique.tail_unique⟩

/-- A join body and its continuation inherit ownership from their containing
code tree. -/
def CodeBinderOwnership.joinChildren
    (ownership :
      CodeBinderOwnership (.jp declaration continuation)) :
    CodeBinderOwnership declaration.value ×
      CodeBinderOwnership continuation := by
  rcases ownership with ⟨binders, listing, unique⟩
  cases listing with
  | join bodyListing continuationListing =>
      have tailUnique := unique.tail_unique
      have prefixUnique := tailUnique.left_of_append
      exact
        ⟨⟨_, bodyListing, prefixUnique.right_of_append⟩,
          ⟨_, continuationListing, tailUnique.right_of_append⟩⟩

/-- Every case alternative inherits ownership from the enclosing case tree. -/
theorem CodeBinderOwnership.caseAlternative
    (ownership : CodeBinderOwnership (.cases caseInfo))
    (member : alternative ∈ caseInfo.alts.toList) :
    Nonempty (CodeBinderOwnership alternative.getCode) := by
  rcases ownership with ⟨binders, listing, unique⟩
  cases listing with
  | cases alternatives =>
      exact alternatives.ownership_of_mem unique member

theorem binderNamesAvoid_of_not_mem
    (absent : forbidden ∉ binders) :
    BinderNamesAvoid forbidden binders := by
  intro binder member sameName
  apply absent
  have sameId : forbidden = binder := by
    cases forbidden
    cases binder
    simp_all
  exact sameId ▸ member

mutual

  /-- List-level exclusion can be pushed back through the transparent binder
  enumeration to every structural binder occurrence. -/
  theorem CodeBinderList.avoids
      (listing : CodeBinderList code binders)
      (namesAvoid : BinderNamesAvoid forbidden binders) :
      CodeBindersAvoidName forbidden code := by
    cases listing with
    | letE continuation =>
        exact .letE
          (namesAvoid _ (by simp))
          (CodeBinderList.avoids continuation
            (fun binder member => namesAvoid binder (by simp [member])))
    | join body continuation =>
        exact .join
          (namesAvoid _ (by simp))
          (by
            intro param member
            apply namesAvoid param.fvarId
            simp only [List.mem_cons, List.mem_append]
            apply Or.inr
            apply Or.inl
            apply Or.inl
            unfold paramIds
            exact List.mem_map.mpr ⟨param, member, rfl⟩)
          (CodeBinderList.avoids body
            (fun binder member => namesAvoid binder (by simp [member])))
          (CodeBinderList.avoids continuation
            (fun binder member => namesAvoid binder (by simp [member])))
    | cases alternatives =>
        exact .cases (AltBinderList.avoids alternatives namesAvoid)
    | jump => exact .jump
    | ret => exact .ret
    | unreachable => exact .unreachable
    | objectSet continuation =>
        exact .objectSet (CodeBinderList.avoids continuation namesAvoid)
    | usizeSet continuation =>
        exact .usizeSet (CodeBinderList.avoids continuation namesAvoid)
    | scalarSet continuation =>
        exact .scalarSet (CodeBinderList.avoids continuation namesAvoid)
    | tagSet continuation =>
        exact .tagSet (CodeBinderList.avoids continuation namesAvoid)
    | increment continuation =>
        exact .increment (CodeBinderList.avoids continuation namesAvoid)
    | decrement continuation =>
        exact .decrement (CodeBinderList.avoids continuation namesAvoid)
    | delete continuation =>
        exact .delete (CodeBinderList.avoids continuation namesAvoid)

  termination_by sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply codeAvoidance_caseAlts_sizeOf_lt
      | apply codeAvoidance_funDeclValue_sizeOf_lt

  theorem AltBinderList.avoids
      (listing : AltBinderList alternatives binders)
      (namesAvoid : BinderNamesAvoid forbidden binders) :
      ∀ alternative, alternative ∈ alternatives →
        CodeBindersAvoidName forbidden alternative.getCode := by
    intro alternative member
    cases listing with
    | nil => simp at member
    | ctor body rest =>
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact CodeBinderList.avoids body
            (fun binder binderMember =>
              namesAvoid binder (by simp [binderMember]))
        · exact AltBinderList.avoids rest
            (fun binder binderMember =>
              namesAvoid binder (by simp [binderMember]))
            alternative member
    | default body rest =>
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact CodeBinderList.avoids body
            (fun binder binderMember =>
              namesAvoid binder (by simp [binderMember]))
        · exact AltBinderList.avoids rest
            (fun binder binderMember =>
              namesAvoid binder (by simp [binderMember]))
            alternative member

  termination_by sizeOf alternatives
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply codeAvoidance_altCode_sizeOf_lt_cons
      | (simp_wf; omega)

end

theorem CodeBinderList.avoids_of_not_mem
    (listing : CodeBinderList code binders)
    (absent : forbidden ∉ binders) :
    CodeBindersAvoidName forbidden code :=
  listing.avoids (binderNamesAvoid_of_not_mem absent)

theorem CodeBinderOwnership.avoids_of_not_mem
    (ownership : CodeBinderOwnership code)
    (absent : forbidden ∉ ownership.binders) :
    CodeBindersAvoidName forbidden code :=
  ownership.listing.avoids_of_not_mem absent

/-- A subtree structurally avoids a binder owned by a later sibling segment. -/
theorem CodeBinderList.avoids_binder_owned_to_right
    (listing : CodeBinderList code leftBinders)
    (unique : BinderNamesUnique (leftBinders ++ rightBinders))
    (member : forbidden ∈ rightBinders) :
    CodeBindersAvoidName forbidden code :=
  listing.avoids (unique.left_avoids_of_mem_right member)

/-- A subtree structurally avoids a binder owned by an earlier sibling
segment. -/
theorem CodeBinderList.avoids_binder_owned_to_left
    (listing : CodeBinderList code rightBinders)
    (unique : BinderNamesUnique (leftBinders ++ rightBinders))
    (member : forbidden ∈ leftBinders) :
    CodeBindersAvoidName forbidden code :=
  listing.avoids (unique.right_avoids_of_mem_left member)

/-- Every later alternative structurally avoids a binder owned by the current
alternative. -/
theorem AltBinderList.avoids_binder_owned_to_left
    (listing : AltBinderList alternatives rightBinders)
    (unique : BinderNamesUnique (leftBinders ++ rightBinders))
    (member : forbidden ∈ leftBinders) :
    ∀ alternative, alternative ∈ alternatives →
      CodeBindersAvoidName forbidden alternative.getCode :=
  listing.avoids (unique.right_avoids_of_mem_left member)

theorem fvarId_ne_of_freshForScope
    (fresh : FreshForScope forbidden scope)
    (inScope : scope.contains candidate = true) :
    candidate ≠ forbidden := by
  intro same
  subst candidate
  exact (fresh forbidden inScope) rfl

theorem freshForScope_cons
    (fresh : FreshForScope forbidden scope)
    (binder : forbidden.name ≠ inserted.name) :
    FreshForScope forbidden (inserted :: scope) := by
  intro old inScope
  simp only [List.contains_cons, Bool.or_eq_true] at inScope
  rcases inScope with same | oldScoped
  · have oldEq : old = inserted := eq_of_beq same
    subst old
    exact binder
  · exact fresh old oldScoped

theorem freshForScope_pushVar
    {index : ScopeIndex} {forbidden inserted : FVarId}
    (fresh : FreshForScope forbidden index.sourceScope)
    (binder : forbidden.name ≠ inserted.name) :
    FreshForScope forbidden
      (index.pushVar inserted).sourceScope := by
  exact freshForScope_cons fresh binder

theorem freshForScope_pushJoin
    {index : ScopeIndex} {forbidden inserted : FVarId}
    (fresh : FreshForScope forbidden index.sourceJoins)
    (binder : forbidden.name ≠ inserted.name) :
    FreshForScope forbidden
      (index.pushJoin inserted).sourceJoins := by
  exact freshForScope_cons fresh binder

theorem freshForScope_pushParamList
    {index : ScopeIndex} {forbidden : FVarId}
    {params : List (LCNF.Param .impure)}
    (fresh : FreshForScope forbidden index.sourceScope)
    (paramsAvoid : ParamBindersAvoidName forbidden params) :
    FreshForScope forbidden
      (index.pushParamList params).sourceScope := by
  induction params generalizing index with
  | nil => exact fresh
  | cons param rest ih =>
      apply ih
      · exact freshForScope_pushVar fresh
          (paramsAvoid param List.mem_cons_self)
      · intro candidate member
        exact paramsAvoid candidate (List.mem_cons_of_mem param member)

theorem freshForScope_pushParams
    {index : ScopeIndex} {forbidden : FVarId}
    {params : Array (LCNF.Param .impure)}
    (fresh : FreshForScope forbidden index.sourceScope)
    (paramsAvoid :
      ParamBindersAvoidName forbidden params.toList) :
    FreshForScope forbidden
      (index.pushParams params).sourceScope :=
  freshForScope_pushParamList fresh paramsAvoid

theorem pushParamList_sourceJoins
    (index : ScopeIndex) (params : List (LCNF.Param .impure)) :
    (index.pushParamList params).sourceJoins = index.sourceJoins := by
  induction params generalizing index with
  | nil => rfl
  | cons param rest rest_ih =>
      simpa [ScopeIndex.pushParamList, ScopeIndex.pushVar] using
        (rest_ih (index := index.pushVar param.fvarId))

theorem pushParams_sourceJoins
    (index : ScopeIndex) (params : Array (LCNF.Param .impure)) :
    (index.pushParams params).sourceJoins = index.sourceJoins := by
  exact pushParamList_sourceJoins index params.toList

/-- Parameters enter the variable scope from left to right, so their final
scope representation is the reverse parameter-id list followed by the outer
scope. -/
theorem pushParamList_sourceScope
    (index : ScopeIndex) (params : List (LCNF.Param .impure)) :
    (index.pushParamList params).sourceScope =
      (params.map (fun param => param.fvarId)).reverse ++
        index.sourceScope := by
  induction params generalizing index with
  | nil => rfl
  | cons param rest ih =>
      rw [ScopeIndex.pushParamList, ih]
      simp [ScopeIndex.pushVar, List.append_assoc]

theorem pushParams_sourceScope
    (index : ScopeIndex) (params : Array (LCNF.Param .impure)) :
    (index.pushParams params).sourceScope =
      (paramIds params).reverse ++ index.sourceScope := by
  exact pushParamList_sourceScope index params.toList

/-- The original variable scope embeds into the scope extended by one value
binder. -/
theorem scopeSubset_pushVar_sourceScope
    (index : ScopeIndex) (fvarId : FVarId) :
    ScopeSubset index.sourceScope (index.pushVar fvarId).sourceScope := by
  simpa [ScopeIndex.pushVar] using
    (scopeSubset_cons_right
      (scope := index.sourceScope) (fvarId := fvarId))

/-- The original join scope embeds into the scope extended by one join
binder. -/
theorem scopeSubset_pushJoin_sourceJoins
    (index : ScopeIndex) (fvarId : FVarId) :
    ScopeSubset index.sourceJoins (index.pushJoin fvarId).sourceJoins := by
  simpa [ScopeIndex.pushJoin] using
    (scopeSubset_cons_right
      (scope := index.sourceJoins) (fvarId := fvarId))

theorem scopeSubset_pushParamList_sourceScope
    (index : ScopeIndex) (params : List (LCNF.Param .impure)) :
    ScopeSubset index.sourceScope
      (index.pushParamList params).sourceScope := by
  induction params generalizing index with
  | nil =>
      intro candidate member
      exact member
  | cons param rest ih =>
      exact scopeSubset_trans
        (scopeSubset_pushVar_sourceScope index param.fvarId)
        (ih (index := index.pushVar param.fvarId))

theorem scopeSubset_pushParams_sourceScope
    (index : ScopeIndex) (params : Array (LCNF.Param .impure)) :
    ScopeSubset index.sourceScope
      (index.pushParams params).sourceScope :=
  scopeSubset_pushParamList_sourceScope index params.toList

/-- Every checked parameter is fresh for the lexical scopes visible before
the whole parameter list was pushed. -/
theorem scopedParamsWellFormed_memberFreshForOuter
    (wellFormed : ScopedParamsWellFormed index params)
    (member : parameter ∈ params) :
    FreshForScope parameter.fvarId index.sourceScope ∧
      FreshForScope parameter.fvarId index.sourceJoins := by
  induction wellFormed with
  | nil => simp at member
  | cons variableFresh joinFresh tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨variableFresh, joinFresh⟩
      · have child := ih member
        exact
          ⟨freshForScope_of_subset child.1
              (by
                simpa [ScopeIndex.pushVar] using
                  (scopeSubset_cons_right :
                    ScopeSubset _ (_ :: _))),
            by simpa [ScopeIndex.pushVar] using child.2⟩

mutual

  /-- Structural binder enumeration plus checked scoping makes every binder
  fresh for both namespaces visible at the root of its containing subtree. -/
  theorem CodeBinderList.memberFreshForRoot
      (listing : CodeBinderList code binders)
      (wellFormed : ScopedCodeWellFormedTree index code)
      (member : forbidden ∈ binders) :
      FreshForScope forbidden index.sourceScope ∧
        FreshForScope forbidden index.sourceJoins := by
    cases listing with
    | letE continuationListing =>
        cases wellFormed with
        | letE valueScoped variableFresh joinFresh runtimeTypes continuation =>
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨variableFresh, joinFresh⟩
            · have child :=
                CodeBinderList.memberFreshForRoot continuationListing
                  continuation member
              exact
                ⟨freshForScope_of_subset child.1
                    (by
                      simpa [ScopeIndex.pushVar] using
                        (scopeSubset_cons_right :
                          ScopeSubset _ (_ :: _))),
                  by simpa [ScopeIndex.pushVar] using child.2⟩
    | join bodyListing continuationListing =>
        cases wellFormed with
        | @jp fvarId index params bodyCode rest binderName type
            binderFresh paramsFresh bodyTree continuation =>
            simp only [List.mem_cons, List.mem_append] at member
            rcases member with
              rfl | ((parameterMember | bodyMember) | continuationMember)
            · exact ⟨binderFresh.variables, binderFresh.joins⟩
            · unfold paramIds at parameterMember
              have paramIdMember :
                  forbidden ∈
                    params.toList.map (fun param => param.fvarId) := by
                simpa [LCNF.FunDecl.params] using parameterMember
              obtain ⟨parameter, parameterInParams, parameterEq⟩ :=
                List.mem_map.mp paramIdMember
              subst forbidden
              exact scopedParamsWellFormed_memberFreshForOuter
                paramsFresh parameterInParams
            · have child :=
                CodeBinderList.memberFreshForRoot bodyListing bodyTree
                  bodyMember
              exact
                ⟨freshForScope_of_subset child.1
                    (scopeSubset_pushParams_sourceScope index _),
                  by simpa [pushParams_sourceJoins] using child.2⟩
            · have child :=
                CodeBinderList.memberFreshForRoot continuationListing
                  continuation continuationMember
              exact
                ⟨by simpa [ScopeIndex.pushJoin] using child.1,
                  freshForScope_of_subset child.2
                    (by
                      simpa [ScopeIndex.pushJoin] using
                        (scopeSubset_cons_right :
                          ScopeSubset _ (_ :: _)))⟩
    | cases alternativesListing =>
        cases wellFormed with
        | cases discrScoped normalization alternatives =>
            exact AltBinderList.memberFreshForRoot alternativesListing
              alternatives member
    | jump => simp at member
    | ret => simp at member
    | unreachable => simp at member
    | objectSet continuationListing =>
        cases wellFormed with
        | oset objectScoped fieldScoped continuation =>
            exact CodeBinderList.memberFreshForRoot continuationListing
              continuation member
    | usizeSet continuationListing =>
        cases wellFormed with
        | uset objectScoped fieldScoped continuation =>
            exact CodeBinderList.memberFreshForRoot continuationListing
              continuation member
    | scalarSet continuationListing =>
        cases wellFormed with
        | sset objectScoped fieldScoped continuation =>
            exact CodeBinderList.memberFreshForRoot continuationListing
              continuation member
    | tagSet continuationListing =>
        cases wellFormed with
        | setTag objectScoped continuation =>
            exact CodeBinderList.memberFreshForRoot continuationListing
              continuation member
    | increment continuationListing =>
        cases wellFormed with
        | inc objectScoped continuation =>
            exact CodeBinderList.memberFreshForRoot continuationListing
              continuation member
    | decrement continuationListing =>
        cases wellFormed with
        | dec objectScoped continuation =>
            exact CodeBinderList.memberFreshForRoot continuationListing
              continuation member
    | delete continuationListing =>
        cases wellFormed with
        | del objectScoped continuation =>
            exact CodeBinderList.memberFreshForRoot continuationListing
              continuation member

  termination_by sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply codeAvoidance_caseAlts_sizeOf_lt
      | apply codeAvoidance_funDeclValue_sizeOf_lt

  theorem AltBinderList.memberFreshForRoot
      (listing : AltBinderList alternatives binders)
      (wellFormed : ScopedCodeWellFormedAlts index alternatives)
      (member : forbidden ∈ binders) :
      FreshForScope forbidden index.sourceScope ∧
        FreshForScope forbidden index.sourceJoins := by
    cases listing with
    | nil => simp at member
    | ctor bodyListing restListing =>
        cases wellFormed with
        | ctor body rest =>
            simp only [List.mem_append] at member
            rcases member with bodyMember | restMember
            · exact CodeBinderList.memberFreshForRoot bodyListing body
                bodyMember
            · exact AltBinderList.memberFreshForRoot restListing rest
                restMember
    | default bodyListing restListing =>
        cases wellFormed with
        | default body rest =>
            simp only [List.mem_append] at member
            rcases member with bodyMember | restMember
            · exact CodeBinderList.memberFreshForRoot bodyListing body
                bodyMember
            · exact AltBinderList.memberFreshForRoot restListing rest
                restMember

  termination_by sizeOf alternatives
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply codeAvoidance_altCode_sizeOf_lt_cons
      | (simp_wf; omega)

end

theorem CodeBinderOwnership.memberFreshForRoot
    (ownership : CodeBinderOwnership code)
    (wellFormed : ScopedCodeWellFormedTree index code)
    (member : forbidden ∈ ownership.binders) :
    FreshForScope forbidden index.sourceScope ∧
      FreshForScope forbidden index.sourceJoins :=
  ownership.listing.memberFreshForRoot wellFormed member

/-- Compiler-facing canonical spelling of structural binder freshness. -/
theorem codeBinderIds_memberFreshForRoot
    (wellFormed : ScopedCodeWellFormedTree index code)
    (member : forbidden ∈ codeBinderIds code) :
    FreshForScope forbidden index.sourceScope ∧
      FreshForScope forbidden index.sourceJoins := by
  rcases CodeBinderList.canonicalExists code with ⟨listing⟩
  exact listing.memberFreshForRoot wellFormed member

/-- A body binder from a declaration-wide unique enumeration is fresh for
the declaration's initial parameter scope. -/
theorem freshForInitialParameterScope_of_declUnique
    (unique :
      BinderNamesUnique (paramIds parameters ++ codeBinderIds code))
    (member : forbidden ∈ codeBinderIds code) :
    FreshForScope forbidden
      (ScopeIndex.empty.pushParams parameters).sourceScope := by
  have paramsAvoid :
      BinderNamesAvoid forbidden (paramIds parameters) :=
    unique.left_avoids_of_mem_right member
  intro candidate inScope
  rw [pushParams_sourceScope] at inScope
  have candidateMember :
      candidate ∈ (paramIds parameters).reverse := by
    simpa [ScopeIndex.empty, List.contains_iff_mem] using inScope
  exact paramsAvoid candidate (by simpa using candidateMember)

/-- Declaration bodies begin with no join binders, and parameter insertion
does not change the join scope. -/
theorem freshForInitialJoinScope
    (forbidden : FVarId) (parameters : Array (LCNF.Param .impure)) :
    FreshForScope forbidden
      (ScopeIndex.empty.pushParams parameters).sourceJoins := by
  rw [pushParams_sourceJoins]
  intro candidate inScope
  simp [ScopeIndex.empty] at inScope

/-- The only extra declaration premise introduced by the elimDead proof is
transparent global binder uniqueness.  All lexical, normalization, and
runtime-type facts remain those already checked by FIR. -/
structure DeclElimDeadWellFormed
    (declaration : LCNF.Decl .impure) : Prop where
  checked : DeclWellFormed declaration
  transparentUnique : DeclCodeBinderNamesUnique declaration

/-- Proof-facing declaration data consumed by hereditary liveness. -/
def DeclElimDeadCertificate
    (declaration : LCNF.Decl .impure) : Prop :=
  match declaration.value with
  | .extern _ => True
  | .code code =>
      ScopedParamsWellFormed ScopeIndex.empty
          declaration.params.toList ∧
        ScopedCodeWellFormedTree
          (ScopeIndex.empty.pushParams declaration.params) code ∧
        BinderNamesUnique
          (paramIds declaration.params ++ codeBinderIds code)

theorem DeclElimDeadWellFormed.certificate
    (wellFormed : DeclElimDeadWellFormed declaration) :
    DeclElimDeadCertificate declaration := by
  cases declaration with
  | mk signature value recursive inlineAttr =>
      cases value with
      | extern metadata => trivial
      | code code =>
          have checked := wellFormed.checked.localCheck
          simp only [declScopedCheck, Bool.and_eq_true] at checked
          exact
            ⟨ScopedParamsWellFormed.ofCheck checked.1,
              ScopedCodeWellFormedTree.ofCheck checked.2
                wellFormed.checked.normalization
                wellFormed.checked.canonical,
              wellFormed.transparentUnique⟩

def ProgramTransparentBinderNamesUnique
    (program : ImpureProgram) : Prop :=
  ∀ declaration, declaration ∈ program.decls.toList →
    DeclCodeBinderNamesUnique declaration

/-- Compiler-facing whole-program premise.  The transparent uniqueness field
is deliberately separate until the opaque `ImpureHygiene.codeBinders`
interface is repaired. -/
structure ProgramElimDeadWellFormed
    (program : ImpureProgram) : Prop where
  checked : ProgramWellFormed program
  transparentUnique : ProgramTransparentBinderNamesUnique program

theorem ProgramElimDeadWellFormed.declaration
    (wellFormed : ProgramElimDeadWellFormed program)
    {declaration : LCNF.Decl .impure}
    (member : declaration ∈ program.decls.toList) :
    DeclElimDeadWellFormed declaration := {
  checked := wellFormed.checked.declaration member
  transparentUnique := wellFormed.transparentUnique declaration member
}

theorem argAvoids_of_scoped
    (fresh : FreshForScope forbidden scope)
    (inScope : argScoped scope argument = true) :
    ArgAvoids forbidden argument := by
  cases argument with
  | erased => trivial
  | fvar fvarId =>
      exact fvarId_ne_of_freshForScope fresh inScope
  | type _ impossible => nomatch impossible

theorem argsAvoid_of_scoped
    (fresh : FreshForScope forbidden scope)
    (inScope : argsScoped scope arguments = true) :
    ArgsAvoid forbidden arguments := by
  intro argument member
  apply argAvoids_of_scoped fresh
  have memberArray : argument ∈ arguments := by
    simpa using member
  exact (Array.all_eq_true'.mp inScope) argument memberArray

theorem letValueAvoids_of_scoped
    (fresh : FreshForScope forbidden scope)
    (inScope : letValueScoped scope value = true) :
    LetValueAvoids forbidden value := by
  cases value with
  | lit _ | erased => trivial
  | fvar fvarId arguments | reuse fvarId _ _ arguments =>
      simp only [letValueScoped, Bool.and_eq_true] at inScope
      exact ⟨fvarId_ne_of_freshForScope fresh inScope.1,
        argsAvoid_of_scoped fresh inScope.2⟩
  | ctor _ arguments | fap _ arguments | pap _ arguments =>
      exact argsAvoid_of_scoped fresh inScope
  | oproj _ fvarId | uproj _ fvarId | sproj _ _ fvarId
  | reset _ fvarId | unbox fvarId | isShared fvarId =>
      exact fvarId_ne_of_freshForScope fresh inScope
  | box _ fvarId =>
      simp only [letValueScoped, Bool.and_eq_true] at inScope
      exact fvarId_ne_of_freshForScope fresh inScope.2
  | proj _ _ _ impossible | const _ _ _ impossible => nomatch impossible

mutual

  /-- Lexical scope plus negative binder ownership imply that no runtime
  identifier collected from this subtree can name `forbidden`. -/
  theorem ScopedCodeWellFormedTree.codeAvoids
      (wellFormed : ScopedCodeWellFormedTree index code)
      (variablesFresh :
        FreshForScope forbidden index.sourceScope)
      (joinsFresh :
        FreshForScope forbidden index.sourceJoins)
      (binders : CodeBindersAvoidName forbidden code) :
      CodeAvoids forbidden code := by
    cases wellFormed with
    | letE valueScoped _ _ _ continuation =>
        cases binders with
        | letE binderAvoid continuationBinders =>
            exact .letE
              (letValueAvoids_of_scoped variablesFresh valueScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                (freshForScope_pushVar variablesFresh binderAvoid)
                (by simpa [ScopeIndex.pushVar] using joinsFresh)
                continuationBinders)
    | jp _ _ body continuation =>
        cases binders with
        | join binderAvoid paramsAvoid bodyBinders continuationBinders =>
            exact .join
              (ScopedCodeWellFormedTree.codeAvoids body
                (freshForScope_pushParams variablesFresh paramsAvoid)
                (by
                  rw [pushParams_sourceJoins]
                  exact joinsFresh)
                bodyBinders)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                (by simpa [ScopeIndex.pushJoin] using variablesFresh)
                (freshForScope_pushJoin joinsFresh binderAvoid)
                continuationBinders)
    | jmp targetScoped argumentsScoped =>
        exact .jump
          (fvarId_ne_of_freshForScope joinsFresh targetScoped)
          (argsAvoid_of_scoped variablesFresh argumentsScoped)
    | cases discrScoped _ alternatives =>
        cases binders with
        | cases alternativeBinders =>
            exact .cases
              (fvarId_ne_of_freshForScope variablesFresh discrScoped)
              (ScopedCodeWellFormedAlts.codeAvoids alternatives
                variablesFresh joinsFresh
                alternativeBinders)
    | ret resultScoped =>
        exact .ret
          (fvarId_ne_of_freshForScope variablesFresh resultScoped)
    | unreach => exact .unreachable _
    | oset objectScoped fieldScoped continuation =>
        cases binders with
        | objectSet continuationBinders =>
            exact .objectSet
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (argAvoids_of_scoped variablesFresh fieldScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | uset objectScoped fieldScoped continuation =>
        cases binders with
        | usizeSet continuationBinders =>
            exact .usizeSet
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (fvarId_ne_of_freshForScope variablesFresh fieldScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | sset objectScoped fieldScoped continuation =>
        cases binders with
        | scalarSet continuationBinders =>
            exact .scalarSet
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (fvarId_ne_of_freshForScope variablesFresh fieldScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | setTag objectScoped continuation =>
        cases binders with
        | tagSet continuationBinders =>
            exact .tagSet
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | inc objectScoped continuation =>
        cases binders with
        | increment continuationBinders =>
            exact .increment
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | dec objectScoped continuation =>
        cases binders with
        | decrement continuationBinders =>
            exact .decrement
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)
    | del objectScoped continuation =>
        cases binders with
        | delete continuationBinders =>
            exact .delete
              (fvarId_ne_of_freshForScope variablesFresh objectScoped)
              (ScopedCodeWellFormedTree.codeAvoids continuation
                variablesFresh joinsFresh
                continuationBinders)

  termination_by sizeOf code
  decreasing_by
    all_goals simp_all <;> try omega
    all_goals first
      | apply codeAvoidance_caseAlts_sizeOf_lt
      | apply codeAvoidance_funDeclValue_sizeOf_lt

  theorem ScopedCodeWellFormedAlts.codeAvoids
      (wellFormed : ScopedCodeWellFormedAlts index alternatives)
      (variablesFresh :
        FreshForScope forbidden index.sourceScope)
      (joinsFresh :
        FreshForScope forbidden index.sourceJoins)
      (binders : ∀ alternative, alternative ∈ alternatives →
        CodeBindersAvoidName forbidden alternative.getCode) :
      ∀ alternative, alternative ∈ alternatives →
        CodeAvoids forbidden alternative.getCode := by
    intro alternative member
    cases wellFormed with
    | nil => simp at member
    | ctor body rest =>
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ScopedCodeWellFormedTree.codeAvoids body
            variablesFresh joinsFresh
            (binders _ List.mem_cons_self)
        · exact ScopedCodeWellFormedAlts.codeAvoids rest
            variablesFresh joinsFresh
            (fun candidate candidateMember =>
              binders candidate
                (List.mem_cons_of_mem _ candidateMember))
            alternative member
    | default body rest =>
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ScopedCodeWellFormedTree.codeAvoids body
            variablesFresh joinsFresh
            (binders _ List.mem_cons_self)
        · exact ScopedCodeWellFormedAlts.codeAvoids rest
            variablesFresh joinsFresh
            (fun candidate candidateMember =>
              binders candidate
                (List.mem_cons_of_mem _ candidateMember))
            alternative member

  termination_by sizeOf alternatives
  decreasing_by
    all_goals subst_vars
    all_goals first
      | apply codeAvoidance_altCode_sizeOf_lt_cons
      | (simp_wf; omega)

end

/-- Direct checked-hygiene form of the backwards-liveness freshness theorem.
It is the reusable boundary for proving that liveness threaded in from a
disjoint subtree cannot reintroduce a binder owned by the current subtree. -/
theorem shadowCode_preserves_absent_of_wellFormed
    (wellFormed : ScopedCodeWellFormedTree index source)
    (variablesFresh :
      FreshForScope forbidden index.sourceScope)
    (joinsFresh :
      FreshForScope forbidden index.sourceJoins)
    (binders : CodeBindersAvoidName forbidden source)
    (absent : initial.contains forbidden = false)
    (result : shadowCode? fuel initial source = some output) :
    output.2.contains forbidden = false :=
  shadowCode_preserves_absent absent
    (ScopedCodeWellFormedTree.codeAvoids wellFormed variablesFresh
      joinsFresh binders)
    result

/-- Processing a subtree cannot introduce the name of a binder owned by a
later sibling segment. -/
theorem shadowCode_preserves_absent_of_binder_owned_to_right
    (wellFormed : ScopedCodeWellFormedTree index source)
    (variablesFresh :
      FreshForScope forbidden index.sourceScope)
    (joinsFresh :
      FreshForScope forbidden index.sourceJoins)
    (listing : CodeBinderList source leftBinders)
    (unique : BinderNamesUnique (leftBinders ++ rightBinders))
    (member : forbidden ∈ rightBinders)
    (absent : initial.contains forbidden = false)
    (result : shadowCode? fuel initial source = some output) :
    output.2.contains forbidden = false :=
  shadowCode_preserves_absent_of_wellFormed wellFormed variablesFresh
    joinsFresh
    (listing.avoids_binder_owned_to_right unique member)
    absent result

/-- Processing the later alternatives cannot introduce the name of a binder
owned by an earlier alternative segment.  This is the exact widening fact
needed when all alternative graphs share the final liveness set. -/
theorem shadowAltList_preserves_absent_of_binder_owned_to_left
    (wellFormed :
      ScopedCodeWellFormedAlts index alternatives)
    (variablesFresh :
      FreshForScope forbidden index.sourceScope)
    (joinsFresh :
      FreshForScope forbidden index.sourceJoins)
    (listing : AltBinderList alternatives rightBinders)
    (unique : BinderNamesUnique (leftBinders ++ rightBinders))
    (member : forbidden ∈ leftBinders)
    (absent : initial.contains forbidden = false)
    (result :
      shadowAltList? (shadowCode? fuel) initial alternatives =
        some (transformed, final)) :
    final.contains forbidden = false := by
  apply shadowAltList_preserves_absent
    (transformCode := shadowCode? fuel)
    (fun current source target final currentAbsent sourceAvoids sourceResult =>
      shadowCode_preserves_absent currentAbsent sourceAvoids sourceResult)
    initial alternatives transformed final absent
  · exact ScopedCodeWellFormedAlts.codeAvoids wellFormed
      variablesFresh joinsFresh
      (listing.avoids_binder_owned_to_left unique member)
  · exact result

end Fir.LeanIR.Passes.ElimDead
