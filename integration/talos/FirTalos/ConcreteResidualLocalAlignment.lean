import FirTalos.ConcreteReuseCapacityCacheCorrectness

/-!
# Compiler-derived residual local alignment

Production lowering computes one exact list of effective local-kind updates
for a complete final-LCNF function.  Current-node admission needs only the
suffix of that list belonging to the currently executing residual code.  This
module packages that compiler calculation as a small structural view: it is
not a source invariant and contains no semantic execution evidence.

The view deliberately follows `collectEffectiveLocalKindUpdates`, so its
projection rules can be reused by every `let` family rather than being
reproved separately for direct calls, lazy caches, and primitives.
-/

namespace FirTalos.Concrete

open Fir.Wasm

/-- A successful name-directed lookup identifies an entry in the row. -/
private theorem findLocalKind?_eq_some_mem
    {locals : Fir.Wasm.LocalKinds}
    {query : Lean.FVarId} {kind : Fir.Wasm.AbiKind}
    (found : Fir.Wasm.findLocalKind? locals query = some kind) :
    ∃ bound, (bound, kind) ∈ locals ∧ bound.name = query.name := by
  induction locals with
  | nil => simp [Fir.Wasm.findLocalKind?] at found
  | cons entry rest ih =>
      obtain ⟨candidate, candidateKind⟩ := entry
      by_cases same : candidate.name == query.name
      · rw [Fir.Wasm.findLocalKind?, if_pos same] at found
        have kindEq : candidateKind = kind := Option.some.inj found
        subst candidateKind
        exact ⟨candidate, by simp, LawfulBEq.eq_of_beq same⟩
      · rw [Fir.Wasm.findLocalKind?, if_neg same] at found
        obtain ⟨bound, member, names⟩ := ih found
        exact ⟨bound, by simp [member], names⟩

/-- In a name-unique row, membership determines name-directed lookup. -/
private theorem findLocalKind?_eq_some_of_mem
    {locals : Fir.Wasm.LocalKinds}
    {query bound : Lean.FVarId} {kind : Fir.Wasm.AbiKind}
    (unique : (locals.map (·.fst.name)).Nodup)
    (member : (bound, kind) ∈ locals)
    (names : bound.name = query.name) :
    Fir.Wasm.findLocalKind? locals query = some kind := by
  induction locals with
  | nil => simp at member
  | cons entry rest ih =>
      obtain ⟨candidate, candidateKind⟩ := entry
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨candidateFresh, restUnique⟩
      rcases List.mem_cons.mp member with selected | member
      · cases selected
        simp [Fir.Wasm.findLocalKind?, names]
      · have different : candidate.name ≠ query.name := by
          intro same
          apply candidateFresh
          exact List.mem_map.mpr ⟨(bound, kind), member,
            by simp [names, same]⟩
        simp [Fir.Wasm.findLocalKind?, different,
          ih restUnique member]

/-- Reversing a duplicate-free local row does not change a successful
name-directed lookup. -/
theorem findLocalKind?_reverse_eq_some
    {locals : Fir.Wasm.LocalKinds}
    {query : Lean.FVarId} {kind : Fir.Wasm.AbiKind}
    (unique : (locals.map (·.fst.name)).Nodup)
    (found : Fir.Wasm.findLocalKind? locals query = some kind) :
    Fir.Wasm.findLocalKind? locals.reverse query = some kind := by
  obtain ⟨bound, member, names⟩ := findLocalKind?_eq_some_mem found
  apply findLocalKind?_eq_some_of_mem
  · rw [List.map_reverse]
    apply unique.reverse.imp
    intro left right different same
    exact different same.symm
  · simpa using member
  · exact names

/-- A successful lookup in the left row remains successful after appending
any later locals. -/
theorem findLocalKind?_append_eq_some
    {left right : Fir.Wasm.LocalKinds}
    {query : Lean.FVarId} {kind : Fir.Wasm.AbiKind}
    (found : Fir.Wasm.findLocalKind? left query = some kind) :
    Fir.Wasm.findLocalKind? (left ++ right) query = some kind := by
  induction left with
  | nil => simp [Fir.Wasm.findLocalKind?] at found
  | cons entry rest ih =>
      obtain ⟨candidate, candidateKind⟩ := entry
      by_cases same : candidate.name == query.name
      · simpa [Fir.Wasm.findLocalKind?, same] using found
      · have restFound :
            Fir.Wasm.findLocalKind? rest query = some kind := by
          simpa [Fir.Wasm.findLocalKind?, same] using found
        simp [Fir.Wasm.findLocalKind?, same, ih restFound]


/-- The exact production local lookup for every effective update collected
from one residual code node.  The update list is compiler-computed rather than
chosen by a theorem client. -/
inductive ConcreteResidualLocalAlignment
    (context : Fir.Wasm.Context)
    (program : Fir.LeanIR.ImpureProgram)
    (code : Lean.Compiler.LCNF.Code .impure) : Prop where
  | intro
      (updates : List (Lean.FVarId × Fir.Wasm.AbiKind))
      (collected :
        Fir.Wasm.collectEffectiveLocalKindUpdates program code = .ok updates)
      (getLocal_of_mem :
        ∀ {fvarId : Lean.FVarId} {kind : Fir.Wasm.AbiKind},
          (fvarId, kind) ∈ updates →
            Fir.Wasm.getLocal context fvarId =
              .ok (.localGet fvarId, kind))

/-- Transport residual alignment across two code nodes whose production
effective-update computations are definitionally or propositionally equal.
This is the common preservation rule for field mutation, reference-count,
tag, and delete nodes, all of which leave local layout unchanged. -/
theorem ConcreteResidualLocalAlignment.reindexCode
    {context : Fir.Wasm.Context}
    {program : Fir.LeanIR.ImpureProgram}
    {code nextCode : Lean.Compiler.LCNF.Code .impure}
    (aligned : ConcreteResidualLocalAlignment context program code)
    (collectedEq :
      Fir.Wasm.collectEffectiveLocalKindUpdates program nextCode =
        Fir.Wasm.collectEffectiveLocalKindUpdates program code) :
    ConcreteResidualLocalAlignment context program nextCode := by
  rcases aligned with ⟨updates, collected, getLocal_of_mem⟩
  exact .intro updates (collectedEq.trans collected) getLocal_of_mem

/-- The head destination of a residual `let` has exactly the effective kind
selected by production lowering. -/
theorem ConcreteResidualLocalAlignment.letHead
    {context : Fir.Wasm.Context}
    {program : Fir.LeanIR.ImpureProgram}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {kind : Fir.Wasm.AbiKind}
    (aligned : ConcreteResidualLocalAlignment context program
      (.let decl continuation))
    (effective : Fir.Wasm.effectiveLetValueKind program decl = .ok kind) :
    Fir.Wasm.getLocal context decl.fvarId =
      .ok (.localGet decl.fvarId, kind) := by
  rcases aligned with ⟨updates, collected, getLocal_of_mem⟩
  cases restCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program continuation with
  | error fault =>
      simp [Fir.Wasm.collectEffectiveLocalKindUpdates, effective,
        restCollected, Bind.bind, Except.bind] at collected
  | ok rest =>
      have updatesEq :
          (decl.fvarId, kind) :: rest = updates := by
        simpa [Fir.Wasm.collectEffectiveLocalKindUpdates, effective,
          restCollected, Bind.bind, Except.bind, pure, Except.pure] using
          collected
      apply getLocal_of_mem
      rw [← updatesEq]
      simp

/-- Removing a residual `let` exposes the exact compiler alignment for its
continuation.  This is the structural preservation rule used by all let-step
simulation families. -/
theorem ConcreteResidualLocalAlignment.letContinuation
    {context : Fir.Wasm.Context}
    {program : Fir.LeanIR.ImpureProgram}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {kind : Fir.Wasm.AbiKind}
    (aligned : ConcreteResidualLocalAlignment context program
      (.let decl continuation))
    (effective : Fir.Wasm.effectiveLetValueKind program decl = .ok kind) :
    ConcreteResidualLocalAlignment context program continuation := by
  rcases aligned with ⟨updates, collected, getLocal_of_mem⟩
  cases restCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program continuation with
  | error fault =>
      simp [Fir.Wasm.collectEffectiveLocalKindUpdates, effective,
        restCollected, Bind.bind, Except.bind] at collected
  | ok rest =>
      have updatesEq :
          (decl.fvarId, kind) :: rest = updates := by
        simpa [Fir.Wasm.collectEffectiveLocalKindUpdates, effective,
          restCollected, Bind.bind, Except.bind, pure, Except.pure] using
          collected
      refine ⟨rest, restCollected, ?_⟩
      intro fvarId resultKind member
      apply getLocal_of_mem
      rw [← updatesEq]
      simp [member]

/-- Every alternative visited by production's left-to-right case traversal
contributes a sublist of the complete collected update row. -/
private theorem collectEffectiveLocalKindUpdatesAlts_member
    (program : Fir.LeanIR.ImpureProgram)
    {alternatives : List (Lean.Compiler.LCNF.Alt .impure)}
    {updates : List (Lean.FVarId × Fir.Wasm.AbiKind)}
    (collected :
      Fir.Wasm.collectEffectiveLocalKindUpdatesAlts program alternatives =
        .ok updates)
    {alternative : Lean.Compiler.LCNF.Alt .impure}
    (member : alternative ∈ alternatives) :
    ∃ current,
      Fir.Wasm.collectEffectiveLocalKindUpdates program alternative.getCode =
          .ok current ∧
        ∀ {entry}, entry ∈ current → entry ∈ updates := by
  induction alternatives generalizing updates with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      cases currentCollected :
          Fir.Wasm.collectEffectiveLocalKindUpdates program head.getCode with
      | error fault =>
          simp [Fir.Wasm.collectEffectiveLocalKindUpdatesAlts,
            currentCollected, Bind.bind, Except.bind] at collected
      | ok current =>
          cases restCollected :
              Fir.Wasm.collectEffectiveLocalKindUpdatesAlts program tail with
          | error fault =>
              simp [Fir.Wasm.collectEffectiveLocalKindUpdatesAlts,
                currentCollected, restCollected, Bind.bind, Except.bind] at collected
          | ok rest =>
              have updatesEq : current ++ rest = updates := by
                simpa [Fir.Wasm.collectEffectiveLocalKindUpdatesAlts,
                  currentCollected, restCollected, Bind.bind, Except.bind,
                  pure, Except.pure] using collected
              rcases member with rfl | member
              · exact ⟨current, currentCollected, fun entryMember => by
                  rw [← updatesEq]
                  exact List.mem_append_left rest entryMember⟩
              · obtain ⟨selected, selectedCollected, selectedSubset⟩ :=
                  ih restCollected member
                exact ⟨selected, selectedCollected, fun entryMember => by
                  rw [← updatesEq]
                  exact List.mem_append_right current
                    (selectedSubset entryMember)⟩

/-- A selected case alternative inherits its exact compiler local alignment
from the production traversal of the complete `cases` node. -/
theorem ConcreteResidualLocalAlignment.caseAlternative
    {context : Fir.Wasm.Context}
    {program : Fir.LeanIR.ImpureProgram}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    (aligned : ConcreteResidualLocalAlignment context program (.cases cases))
    {alternative : Lean.Compiler.LCNF.Alt .impure}
    (member : alternative ∈ cases.alts.toList) :
    ConcreteResidualLocalAlignment context program alternative.getCode := by
  rcases aligned with ⟨updates, collected, getLocal_of_mem⟩
  have alternativesCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdatesAlts program cases.alts.toList =
        .ok updates := by
    simpa [Fir.Wasm.collectEffectiveLocalKindUpdates] using collected
  obtain ⟨current, currentCollected, currentSubset⟩ :=
    collectEffectiveLocalKindUpdatesAlts_member program alternativesCollected
      member
  exact .intro current currentCollected fun entryMember =>
    getLocal_of_mem (currentSubset entryMember)

/-- Whole-program impure hygiene specializes to the exact declaration found
by the production name lookup.  This is a static phase fact: it carries no
compiler execution, target path, or recursive admission evidence. -/
theorem impureHygienic_declarationOfFind
    {program : Fir.LeanIR.ImpureProgram}
    (hygienic : program.ImpureHygienic)
    {name : Lean.Name} {declaration : Lean.Compiler.LCNF.Decl .impure}
    (found : program.findDecl? name = some declaration) :
    Fir.LeanIR.ImpureHygiene.declHygienic declaration = true := by
  have member : declaration ∈ program.decls := by
    obtain ⟨_, index, inBounds, selected, _⟩ :=
      Array.find?_eq_some_iff_getElem.mp found
    rw [← selected]
    exact Array.getElem_mem inBounds
  unfold Fir.LeanIR.Program.ImpureHygienic at hygienic
  rw [Array.all_eq_true'] at hygienic
  exact hygienic declaration member

/-- Hygiene of a code declaration exposes the exact declaration-wide binder
uniqueness check consumed by the local-collector agreement proof. -/
theorem declHygienic_code_bindersUnique
    {declaration : Lean.Compiler.LCNF.Decl .impure}
    {code : Lean.Compiler.LCNF.Code .impure}
    (body : declaration.value = .code code)
    (hygienic :
      Fir.LeanIR.ImpureHygiene.declHygienic declaration = true) :
    Fir.LeanIR.ImpureHygiene.bindersUnique
      (Fir.LeanIR.ImpureHygiene.paramIds declaration.params ++
        Fir.LeanIR.ImpureHygiene.codeBinders code) = true := by
  unfold Fir.LeanIR.ImpureHygiene.declHygienic at hygienic
  rw [body] at hygienic
  simp only [Bool.and_eq_true] at hygienic
  exact hygienic.1.1

/-- The source declaration selected by one supported-function package inherits
the existing impure phase hygiene invariant.  The explicit premise will be
discharged directly from `WasmSupported` once the shared admission contract
lands. -/
theorem ConcreteSupportedFunction.sourceBodyBindersUnique_of_hygienic
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction target hosts)
    (hygienic : program.ImpureHygienic) :
    Fir.LeanIR.ImpureHygiene.bindersUnique
      (Fir.LeanIR.ImpureHygiene.paramIds spec.sourceDeclaration.params ++
        Fir.LeanIR.ImpureHygiene.codeBinders functionCode) = true := by
  apply declHygienic_code_bindersUnique spec.sourceDeclarationBody
  exact impureHygienic_declarationOfFind hygienic spec.sourceDeclarationFound


/-- Every effective named-call rewrite selected by a real lowered declaration
has its exact ABI kind in the production body-local row.  The proof consumes
the compiler's raw/effective collection equations and source hygiene; it does
not introduce a caller-provided layout certificate. -/
theorem LoweredInternalDeclaration.bodyLocalKind_of_effective_mem
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Lean.Name}
    {declaration : Lean.Compiler.LCNF.Decl .impure}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row : LoweredInternalDeclaration program cachedDeclarations declaration
      sourceCode sourceFunction)
    (hygienic :
      Fir.LeanIR.ImpureHygiene.BinderNamesUnique
        (Fir.LeanIR.ImpureHygiene.codeBinders sourceCode))
    {updates : List (Lean.FVarId × AbiKind)}
    (effectiveCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program sourceCode =
        .ok updates)
    {fvarId : Lean.FVarId} {kind : AbiKind}
    (member : (fvarId, kind) ∈ updates) :
    Fir.Wasm.findLocalKind? row.bodyLocals fvarId = some kind := by
  have localsCollected := row.localsCollected
  unfold Fir.Wasm.collectLocals at localsCollected
  cases rawResult : Fir.Wasm.collectLocalKindInsertions sourceCode with
  | error fault =>
      rw [rawResult] at localsCollected
      contradiction
  | ok insertions =>
      rw [rawResult] at localsCollected
      change Except.ok (Fir.Wasm.applyLocalKindInsertions [] insertions) =
        Except.ok row.rawBodyLocals at localsCollected
      have rawBodyEq :
          row.rawBodyLocals =
            Fir.Wasm.applyLocalKindInsertions [] insertions := by
        exact (Except.ok.inj localsCollected).symm
      have localsRefined := row.localsRefined
      unfold Fir.Wasm.refineNamedCallLocalKinds at localsRefined
      rw [effectiveCollected] at localsRefined
      change Except.ok (Fir.Wasm.applyEffectiveLocalKindUpdates
          row.rawBodyLocals updates) =
        Except.ok row.bodyLocals at localsRefined
      have bodyEq :
          row.bodyLocals =
            Fir.Wasm.applyEffectiveLocalKindUpdates
              row.rawBodyLocals updates := by
        exact (Except.ok.inj localsRefined).symm
      rw [bodyEq, rawBodyEq]
      exact Fir.Wasm.findLocalKind?_of_collected_effective_mem
        program sourceCode [] insertions updates rawResult effectiveCollected
        hygienic fvarId kind member

/-- The final body-local row of every successful lowered declaration has
duplicate-free names. Raw insertion enforces uniqueness and effective
named-call refinement changes only ABI annotations. -/
theorem LoweredInternalDeclaration.bodyLocalNamesNodup
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Lean.Name}
    {declaration : Lean.Compiler.LCNF.Decl .impure}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row : LoweredInternalDeclaration program cachedDeclarations declaration
      sourceCode sourceFunction) :
    (row.bodyLocals.map (·.fst.name)).Nodup := by
  have localsCollected := row.localsCollected
  unfold Fir.Wasm.collectLocals at localsCollected
  cases rawResult : Fir.Wasm.collectLocalKindInsertions sourceCode with
  | error fault =>
      rw [rawResult] at localsCollected
      contradiction
  | ok insertions =>
      rw [rawResult] at localsCollected
      change Except.ok (Fir.Wasm.applyLocalKindInsertions [] insertions) =
        Except.ok row.rawBodyLocals at localsCollected
      have rawBodyEq :
          row.rawBodyLocals =
            Fir.Wasm.applyLocalKindInsertions [] insertions :=
        (Except.ok.inj localsCollected).symm
      have rawUnique :
          (row.rawBodyLocals.map (·.fst.name)).Nodup := by
        rw [rawBodyEq]
        exact Fir.Wasm.applyLocalKindInsertions_names_nodup [] insertions
          (by simp)
      have localsRefined := row.localsRefined
      unfold Fir.Wasm.refineNamedCallLocalKinds at localsRefined
      cases effectiveResult :
          Fir.Wasm.collectEffectiveLocalKindUpdates program sourceCode with
      | error fault =>
          rw [effectiveResult] at localsRefined
          contradiction
      | ok updates =>
          rw [effectiveResult] at localsRefined
          change Except.ok (Fir.Wasm.applyEffectiveLocalKindUpdates
              row.rawBodyLocals updates) =
            Except.ok row.bodyLocals at localsRefined
          have bodyEq :
              row.bodyLocals =
                Fir.Wasm.applyEffectiveLocalKindUpdates
                  row.rawBodyLocals updates :=
            (Except.ok.inj localsRefined).symm
          rw [bodyEq, Fir.Wasm.applyEffectiveLocalKindUpdates_names]
          exact rawUnique

/-- Exact body-local typing is unchanged by the source-order reversal used in
the emitted function and canonical compiler context. -/
theorem LoweredInternalDeclaration.reversedBodyLocalKind_of_effective_mem
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Lean.Name}
    {declaration : Lean.Compiler.LCNF.Decl .impure}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row : LoweredInternalDeclaration program cachedDeclarations declaration
      sourceCode sourceFunction)
    (hygienic :
      Fir.LeanIR.ImpureHygiene.BinderNamesUnique
        (Fir.LeanIR.ImpureHygiene.codeBinders sourceCode))
    {updates : List (Lean.FVarId × AbiKind)}
    (effectiveCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program sourceCode =
        .ok updates)
    {fvarId : Lean.FVarId} {kind : AbiKind}
    (member : (fvarId, kind) ∈ updates) :
    Fir.Wasm.findLocalKind? row.bodyLocals.reverse fvarId = some kind := by
  apply findLocalKind?_reverse_eq_some row.bodyLocalNamesNodup
  exact row.bodyLocalKind_of_effective_mem hygienic effectiveCollected member

/-- A successful lookup in a suffix remains visible through a prefix whose
names avoid the queried binder.  This is the generic lookup rule needed for
compiler contexts, where parameters precede body locals. -/
theorem findLocalKind?_append_eq_some_of_left_avoids
    {left right : Fir.Wasm.LocalKinds}
    {query : Lean.FVarId} {kind : AbiKind}
    (avoids : ∀ entry ∈ left, entry.fst.name ≠ query.name)
    (found : Fir.Wasm.findLocalKind? right query = some kind) :
    Fir.Wasm.findLocalKind? (left ++ right) query = some kind := by
  induction left with
  | nil => simpa using found
  | cons entry rest ih =>
      have different : entry.fst.name ≠ query.name :=
        avoids entry (by simp)
      have tailAvoids : ∀ candidate ∈ rest,
          candidate.fst.name ≠ query.name := by
        intro candidate member
        exact avoids candidate (by simp [member])
      simpa [Fir.Wasm.findLocalKind?, different] using ih tailAvoids

/-- Declaration-wide hygiene lifts an effective named-call destination all
the way into the exact production compiler context.  Parameters are emitted
before body locals, but the source hygiene theorem proves that no parameter
can shadow a body binder. -/
theorem LoweredInternalDeclaration.localKind_of_effective_mem
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Lean.Name}
    {declaration : Lean.Compiler.LCNF.Decl .impure}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row : LoweredInternalDeclaration program cachedDeclarations declaration
      sourceCode sourceFunction)
    (hygienic :
      Fir.LeanIR.ImpureHygiene.BinderNamesUnique
        (Fir.LeanIR.ImpureHygiene.paramIds declaration.params ++
          Fir.LeanIR.ImpureHygiene.codeBinders sourceCode))
    {updates : List (Lean.FVarId × AbiKind)}
    (effectiveCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program sourceCode =
        .ok updates)
    {fvarId : Lean.FVarId} {kind : AbiKind}
    (member : (fvarId, kind) ∈ updates) :
    Fir.Wasm.findLocalKind? row.localKinds fvarId = some kind := by
  have bodyUnique := hygienic.right_of_append
  have bodyFound :
      Fir.Wasm.findLocalKind? row.bodyLocals.reverse fvarId = some kind :=
    row.reversedBodyLocalKind_of_effective_mem bodyUnique effectiveCollected
      member
  have bodyBinderMem :
      fvarId ∈ Fir.LeanIR.ImpureHygiene.codeBinders sourceCode := by
    have localsCollected := row.localsCollected
    unfold Fir.Wasm.collectLocals at localsCollected
    cases rawResult : Fir.Wasm.collectLocalKindInsertions sourceCode with
    | error fault =>
        rw [rawResult] at localsCollected
        contradiction
    | ok insertions =>
        have effectiveNames :=
          Fir.Wasm.collectEffectiveLocalKindUpdates_names_sublist program
            sourceCode insertions updates rawResult effectiveCollected
        have rawNames :=
          Fir.Wasm.collectLocalKindInsertions_names_sublist sourceCode
            insertions rawResult
        apply rawNames.subset
        apply effectiveNames.subset
        exact List.mem_map.mpr ⟨(fvarId, kind), member, rfl⟩
  have parameterAvoids : ∀ entry ∈ row.paramLocals.reverse,
      entry.fst.name ≠ fvarId.name := by
    intro entry entryMem
    have parameterNameMem := row.paramLocalName_mem (by simpa using entryMem)
    obtain ⟨parameter, parameterSourceMem, parameterNameEq⟩ :=
      List.mem_map.mp parameterNameMem
    have parameterBinderMem :
        parameter.fvarId ∈
          Fir.LeanIR.ImpureHygiene.paramIds declaration.params := by
      exact List.mem_map.mpr ⟨parameter, parameterSourceMem, rfl⟩
    have distinct := (List.pairwise_append.mp hygienic).2.2
      parameter.fvarId parameterBinderMem fvarId bodyBinderMem
    intro equalName
    exact distinct (parameterNameEq.trans equalName)
  unfold LoweredInternalDeclaration.localKinds
  exact findLocalKind?_append_eq_some_of_left_avoids parameterAvoids bodyFound

/-- The declaration-local row theorem transfers to the exact context carried
by a real supported function.  This is the compiler-facing equation consumed
by current-node admission: it mentions only production lowering, validation
hygiene, and membership in the effective update traversal. -/
theorem ConcreteSupportedFunction.getLocal_of_effective_mem
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts)
    {updates : List (Lean.FVarId × AbiKind)}
    (effectiveCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program functionCode =
        .ok updates)
    {fvarId : Lean.FVarId} {kind : AbiKind}
    (member : (fvarId, kind) ∈ updates) :
    Fir.Wasm.getLocal context fvarId =
      .ok (.localGet fvarId, kind) := by
  obtain ⟨row⟩ := spec.loweredInternalDeclaration
  have declarationUnique :=
    Fir.LeanIR.ImpureHygiene.bindersUnique_sound
      (spec.sourceBodyBindersUnique_of_hygienic
        spec.programSupported.impureHygienic)
  have rowFound := row.localKind_of_effective_mem declarationUnique
    effectiveCollected member
  have contextLocalsEq : context.localKinds = row.localKinds := by
    rw [spec.localKindsExact]
    exact row.localKindsExact.symm
  unfold Fir.Wasm.getLocal
  rw [contextLocalsEq, rowFound]

/-- A real successfully lowered function supplies the complete compiler local
alignment at its source root.  Success of the production refinement pass also
proves that effective-update collection cannot fail; no caller-selected local
row or per-program certificate appears in the conclusion. -/
theorem ConcreteSupportedFunction.residualLocalAlignment
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts) :
    ConcreteResidualLocalAlignment context program functionCode := by
  obtain ⟨row⟩ := spec.loweredInternalDeclaration
  cases effectiveCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program functionCode with
  | error fault =>
      have localsRefined := row.localsRefined
      unfold Fir.Wasm.refineNamedCallLocalKinds at localsRefined
      rw [effectiveCollected] at localsRefined
      contradiction
  | ok updates =>
      refine .intro updates effectiveCollected ?_
      intro fvarId kind member
      exact spec.getLocal_of_effective_mem effectiveCollected member


end FirTalos.Concrete
