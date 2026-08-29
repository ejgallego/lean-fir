import FirTalos.ConcreteStructuredSimulation

/-!
# Residual source validation for the structured W6 simulation

`WasmSupported` validates a declaration from its root, while the structured
simulation relates an arbitrary currently executing code node.  This module
retains the executable validator's residual state at that node: local kinds,
join declarations, case facts, and guarded-sharing facts.

The state is not an execution or translation certificate.  Its sole field is
the actual `supportedCodeWithJoins` Boolean judgment, its root is reconstructed
from `ConcreteSupportedFunction.validatedBodyAt`, and the transition theorems
below are inversions of the executable validator equations.
-/

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.Wasm.Concrete
open Fir.LeanIR.Impure
open FirTalos.Correctness
open Lean.Compiler

/-- The exact residual state of source validation at one current LCNF node. -/
structure ConcreteStructuredValidationFocus
    (program : Fir.LeanIR.ImpureProgram)
    (joins : Fir.Wasm.JoinPoints)
    (locals : Fir.Wasm.LocalKinds)
    (expectedResult : Option Fir.Wasm.AbiKind)
    (facts : Fir.Wasm.SupportedCaseFacts)
    (sharing : Fir.Wasm.SupportedSharingFacts)
    (code : Lean.Compiler.LCNF.Code .impure) : Prop where
  supported :
    Fir.Wasm.supportedCodeWithJoins program joins locals expectedResult facts
      sharing code = true

/-- One proof-transparent declaration-parameter step of the executable
validator. -/
private def supportedDeclarationParamStep
    (program : Fir.LeanIR.ImpureProgram) (declaration : LCNF.Decl .impure)
    (locals : Fir.Wasm.LocalKinds) (param : LCNF.Param .impure) :
    Option Fir.Wasm.LocalKinds := do
  if !Fir.Wasm.abiTypeKnown param.type then none
  match Fir.Wasm.abiValueKind? param.type with
  | none => some locals
  | some _ => do
      let kind ← Fir.Wasm.declarationParamKind? program declaration param
      some (Fir.Wasm.insertLocal locals param.fvarId kind)

/-- One proof-transparent declaration-parameter step of production lowering. -/
private def loweredDeclarationParamStep
    (program : Fir.LeanIR.ImpureProgram) (declaration : LCNF.Decl .impure)
    (locals : Fir.Wasm.LocalKinds) (param : LCNF.Param .impure) :
    Except Fir.Wasm.CompileError Fir.Wasm.LocalKinds := do
  match ← Fir.Wasm.checkedAbiKind? param.type with
  | none => return locals
  | some kind =>
      let kind :=
        if kind == .tobject &&
            Fir.Wasm.erasedOnlyParameter program declaration param then
          .erased
        else
          kind
      return Fir.Wasm.insertLocal locals param.fvarId kind

/-- A successful validator parameter step is exactly the corresponding
production-lowering step. -/
private theorem supportedDeclarationParamStep_lowered
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {locals next : Fir.Wasm.LocalKinds}
    {param : LCNF.Param .impure}
    (validated : supportedDeclarationParamStep program declaration locals
      param = some next) :
    loweredDeclarationParamStep program declaration locals param = .ok next := by
  unfold supportedDeclarationParamStep at validated
  unfold loweredDeclarationParamStep
  unfold Fir.Wasm.abiTypeKnown Fir.Wasm.abiValueKind?
    Fir.Wasm.declarationParamKind? at validated
  unfold Fir.Wasm.checkedAbiKind?
  cases classified : Fir.Wasm.abiKind? param.type with
  | error error => simp [classified] at validated
  | ok kindOption =>
      cases kindOption with
      | none =>
          have nextEq : next = locals := by
            simpa [classified] using validated.symm
          subst next
          rfl
      | some kind =>
          by_cases erased :
              (kind == .tobject &&
                Fir.Wasm.erasedOnlyParameter program declaration param) = true
          · have nextEq :
                next = Fir.Wasm.insertLocal locals param.fvarId .erased := by
              simpa [classified, erased] using validated.symm
            subst next
            simp [erased, pure, Except.pure, Bind.bind,
              Except.bind]
          · have nextEq :
                next = Fir.Wasm.insertLocal locals param.fvarId kind := by
              simpa [classified, erased] using validated.symm
            subst next
            simp [erased, pure, Except.pure, Bind.bind,
              Except.bind]

/-- Successful root validation and production lowering compute the same
front-inserted parameter row. -/
private theorem supportedDeclarationParamFold_lowered
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {params : List (LCNF.Param .impure)}
    {initial result : Fir.Wasm.LocalKinds}
    (validated :
      params.foldlM
          (supportedDeclarationParamStep program declaration) initial =
        some result) :
    params.foldlM
        (loweredDeclarationParamStep program declaration) initial =
      .ok result := by
  induction params generalizing initial with
  | nil =>
      have resultEq : initial = result := by simpa using validated
      subst result
      rfl
  | cons head tail ih =>
      rw [List.foldlM_cons] at validated ⊢
      cases headValidated :
          supportedDeclarationParamStep program declaration initial head with
      | none => simp [headValidated] at validated
      | some next =>
          rw [headValidated] at validated
          rw [supportedDeclarationParamStep_lowered headValidated]
          exact ih validated

/-- The validator and lowerer use the same complete declaration-parameter
row whenever validation succeeds. -/
theorem addSupportedDeclarationParams?_lowered
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {result : Fir.Wasm.LocalKinds}
    (validated :
      Fir.Wasm.addSupportedDeclarationParams? program declaration =
        some result) :
    Fir.Wasm.addDeclarationParams program declaration = .ok result := by
  unfold Fir.Wasm.addSupportedDeclarationParams? at validated
  unfold Fir.Wasm.addDeclarationParams
  change declaration.params.foldlM
      (supportedDeclarationParamStep program declaration) [] =
        some result at validated
  change declaration.params.foldlM
      (loweredDeclarationParamStep program declaration) [] = .ok result
  rw [← Array.foldlM_toList] at validated ⊢
  exact supportedDeclarationParamFold_lowered validated

/-- Front insertion preserves uniqueness of local names. -/
private theorem insertLocal_namesNodup
    {locals : Fir.Wasm.LocalKinds}
    {fvarId : Lean.FVarId} {kind : Fir.Wasm.AbiKind}
    (unique : (locals.map (·.fst.name)).Nodup) :
    ((Fir.Wasm.insertLocal locals fvarId kind).map (·.fst.name)).Nodup := by
  unfold Fir.Wasm.insertLocal
  simp only [List.map_cons, List.nodup_cons]
  constructor
  · intro present
    obtain ⟨entry, entryMem, nameEq⟩ := List.mem_map.mp present
    have kept := (List.mem_filter.mp entryMem).2
    exact (bne_iff_ne.mp kept) nameEq
  · exact unique.sublist
      ((List.filter_sublist (l := locals)
        (p := fun entry => entry.fst.name != fvarId.name)).map _)

/-- A successful validator parameter fold started from a unique row retains
unique local names. -/
private theorem supportedDeclarationParamFold_namesNodup
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {params : List (LCNF.Param .impure)}
    {initial result : Fir.Wasm.LocalKinds}
    (initialUnique : (initial.map (·.fst.name)).Nodup)
    (validated :
      params.foldlM
          (supportedDeclarationParamStep program declaration) initial =
        some result) :
    (result.map (·.fst.name)).Nodup := by
  induction params generalizing initial with
  | nil =>
      have resultEq : initial = result := by simpa using validated
      subst result
      exact initialUnique
  | cons head tail ih =>
      rw [List.foldlM_cons] at validated
      cases headValidated :
          supportedDeclarationParamStep program declaration initial head with
      | none => simp [headValidated] at validated
      | some next =>
          rw [headValidated] at validated
          have nextUnique : (next.map (·.fst.name)).Nodup := by
            unfold supportedDeclarationParamStep at headValidated
            unfold Fir.Wasm.abiTypeKnown Fir.Wasm.abiValueKind? at headValidated
            cases classified : Fir.Wasm.abiKind? head.type with
            | error error => simp [classified] at headValidated
            | ok kindOption =>
                cases kindOption with
                | none =>
                    have nextEq : next = initial := by
                      simpa [classified] using headValidated.symm
                    simpa [nextEq] using initialUnique
                | some kind =>
                    unfold Fir.Wasm.declarationParamKind? at headValidated
                    by_cases erased :
                        (kind == .tobject &&
                          Fir.Wasm.erasedOnlyParameter program declaration
                            head) = true
                    · have nextEq :
                          next = Fir.Wasm.insertLocal initial head.fvarId
                            .erased := by
                        simpa [classified, erased] using headValidated.symm
                      simpa [nextEq] using
                        insertLocal_namesNodup
                          (fvarId := head.fvarId) (kind := .erased)
                          initialUnique
                    · have nextEq :
                          next = Fir.Wasm.insertLocal initial head.fvarId kind := by
                        simpa [classified, erased] using headValidated.symm
                      simpa [nextEq] using
                        insertLocal_namesNodup
                          (fvarId := head.fvarId) (kind := kind) initialUnique
          exact ih nextUnique validated

/-- Successful declaration-parameter validation produces a name-unique row. -/
theorem addSupportedDeclarationParams?_namesNodup
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {result : Fir.Wasm.LocalKinds}
    (validated :
      Fir.Wasm.addSupportedDeclarationParams? program declaration =
        some result) :
    (result.map (·.fst.name)).Nodup := by
  unfold Fir.Wasm.addSupportedDeclarationParams? at validated
  change declaration.params.foldlM
      (supportedDeclarationParamStep program declaration) [] =
        some result at validated
  rw [← Array.foldlM_toList] at validated
  exact supportedDeclarationParamFold_namesNodup (by simp) validated

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

/-- Agreement between the validator's residual local-kind row and the exact
production compiler context at the current code node.

The validator row is path-sensitive and contains only bindings introduced on
the current source path, whereas the lowering context may also contain locals
collected from other syntax.  Admission only needs agreement for a successful
validator lookup; requiring equality of the two rows would therefore be both
unnecessary and false. -/
def ConcreteStructuredValidationLocalsAgree
    (context : Fir.Wasm.Context) (locals : Fir.Wasm.LocalKinds) : Prop :=
  ∀ {fvarId : Lean.FVarId} {kind : Fir.Wasm.AbiKind},
    Fir.Wasm.findLocalKind? locals fvarId = some kind →
      Fir.Wasm.getLocal context fvarId =
        .ok (.localGet fvarId, kind)

/-- Removing bindings for one different name does not change lookup of the
queried local.  This is the small row lemma behind hereditary validator/
compiler agreement: validator insertion replaces a name, while the production
compiler context already contains its unique final slot. -/
private theorem findLocalKind?_filter_different
    (locals : Fir.Wasm.LocalKinds) (removed query : Lean.FVarId)
    (different : removed.name ≠ query.name) :
    Fir.Wasm.findLocalKind?
        (locals.filter fun entry => entry.fst.name != removed.name) query =
      Fir.Wasm.findLocalKind? locals query := by
  induction locals with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨candidate, candidateKind⟩ := entry
      by_cases candidateRemoved : candidate.name = removed.name
      · have candidateQuery : candidate.name ≠ query.name := by
          simpa [candidateRemoved] using different
        have removedTest : (candidate.name != removed.name) = false := by
          simp [candidateRemoved]
        have queryTest : (candidate.name == query.name) = false :=
          beq_eq_false_iff_ne.mpr candidateQuery
        simp only [List.filter_cons, removedTest, Bool.false_eq_true,
          ↓reduceIte, Fir.Wasm.findLocalKind?, queryTest]
        exact ih
      · have removedTest : (candidate.name != removed.name) = true :=
          bne_iff_ne.mpr candidateRemoved
        simp only [List.filter_cons, removedTest, ↓reduceIte,
          Fir.Wasm.findLocalKind?]
        by_cases candidateQuery : candidate.name = query.name
        · have queryTest : (candidate.name == query.name) = true :=
            beq_iff_eq.mpr candidateQuery
          simp [queryTest]
        · have queryTest : (candidate.name == query.name) = false :=
            beq_eq_false_iff_ne.mpr candidateQuery
          simp [queryTest, ih]

/-- Validator insertion has the expected name-directed lookup behavior. -/
theorem findLocalKind?_insertLocal
    (locals : Fir.Wasm.LocalKinds) (inserted query : Lean.FVarId)
    (kind : Fir.Wasm.AbiKind) :
    Fir.Wasm.findLocalKind? (Fir.Wasm.insertLocal locals inserted kind) query =
      if inserted.name = query.name then some kind
      else Fir.Wasm.findLocalKind? locals query := by
  unfold Fir.Wasm.insertLocal
  by_cases same : inserted.name = query.name
  · simp [Fir.Wasm.findLocalKind?, same]
  · simp [Fir.Wasm.findLocalKind?, same,
      findLocalKind?_filter_different locals inserted query same]

/-- Once the production compiler row contains the binding selected by a
validated insertion, local agreement is preserved for the continuation. -/
theorem ConcreteStructuredValidationLocalsAgree.insert
    {context : Fir.Wasm.Context}
    {locals : Fir.Wasm.LocalKinds}
    {fvarId : Lean.FVarId}
    {kind : Fir.Wasm.AbiKind}
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (compiled : Fir.Wasm.getLocal context fvarId =
      .ok (.localGet fvarId, kind)) :
    ConcreteStructuredValidationLocalsAgree context
      (Fir.Wasm.insertLocal locals fvarId kind) := by
  intro query queryKind found
  rw [findLocalKind?_insertLocal] at found
  by_cases same : fvarId.name = query.name
  · rw [if_pos same] at found
    have queryKindEq : queryKind = kind := Option.some.inj found.symm
    subst queryKind
    have queryEq : query = fvarId := by
      cases query
      cases fvarId
      simp_all
    subst query
    exact compiled
  · rw [if_neg same] at found
    exact agrees found

/-- Residual validation packaged together with its production-local agreement.
This remains purely static: it contains neither a source step nor target
execution evidence. -/
def ConcreteStructuredAlignedValidationState
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (functionResult : Fir.Wasm.AbiKind)
    (code : Lean.Compiler.LCNF.Code .impure) : Prop :=
  ∃ joins : Fir.Wasm.JoinPoints,
    ∃ locals : Fir.Wasm.LocalKinds,
      ∃ facts : Fir.Wasm.SupportedCaseFacts,
        ∃ sharing : Fir.Wasm.SupportedSharingFacts,
          ConcreteStructuredValidationFocus program joins locals
              (some functionResult) facts sharing code ∧
            ConcreteStructuredValidationLocalsAgree context locals

/-- Existential package for the complete residual validator state at an
active generated-function node.  The indices retain only the stable program,
function result, and current code; joins, local kinds, case facts, and sharing
facts are exposed as fields so transition theorems can evolve them without
changing the compiler/resource relation's public indices. -/
def ConcreteStructuredValidationState
    (program : Fir.LeanIR.ImpureProgram)
    (functionResult : Fir.Wasm.AbiKind)
    (code : Lean.Compiler.LCNF.Code .impure) : Prop :=
  ∃ joins : Fir.Wasm.JoinPoints,
    ∃ locals : Fir.Wasm.LocalKinds,
      ∃ facts : Fir.Wasm.SupportedCaseFacts,
        ∃ sharing : Fir.Wasm.SupportedSharingFacts,
          ConcreteStructuredValidationFocus program joins locals
            (some functionResult) facts sharing code

/-- Aligned validation forgets only the compiler-row agreement when viewed as
the pre-existing residual validation state. -/
theorem ConcreteStructuredAlignedValidationState.toValidationState
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {code : Lean.Compiler.LCNF.Code .impure}
    (aligned : ConcreteStructuredAlignedValidationState program context
      functionResult code) :
    ConcreteStructuredValidationState program functionResult code := by
  obtain ⟨joins, locals, facts, sharing, validated, _agrees⟩ := aligned
  exact ⟨joins, locals, facts, sharing, validated⟩

/-- Static validation retained for every suspended source caller.  Direct and
saturated calls have the same source bind frame, so validation intentionally
does not distinguish them; the existing supported-frame stack and its
resource agreement retain that protocol distinction. -/
inductive ConcreteStructuredSuspendedValidation
    (program : Fir.LeanIR.ImpureProgram) :
    Fir.Wasm.AbiKind → Option Fir.Wasm.AbiKind → List Frame → Prop where
  | nil {functionResult : Fir.Wasm.AbiKind} :
      ConcreteStructuredSuspendedValidation program functionResult none []
  | bind
      {calleeResult callerResult kind : Fir.Wasm.AbiKind}
      {tailResult : Option Fir.Wasm.AbiKind}
      {result : Lean.FVarId}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerEnv : Env}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      (continuationValidation :
        ConcreteStructuredValidationState program callerResult continuation)
      (tail : ConcreteStructuredSuspendedValidation program callerResult
        tailResult sourceFrames) :
      ConcreteStructuredSuspendedValidation program calleeResult (some kind)
        (.bind result continuation callerEnv callerJoins :: sourceFrames)
  | lazy
      {calleeResult callerResult kind : Fir.Wasm.AbiKind}
      {tailResult : Option Fir.Wasm.AbiKind}
      {declaration : Lean.Name}
      {result : Lean.FVarId}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerEnv : Env}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      (continuationValidation :
        ConcreteStructuredValidationState program callerResult continuation)
      (tail : ConcreteStructuredSuspendedValidation program callerResult
        tailResult sourceFrames) :
      ConcreteStructuredSuspendedValidation program calleeResult (some kind)
        (.cache declaration ::
          .bind result continuation callerEnv callerJoins :: sourceFrames)

/-- A yielded source state can resume an ordinary caller immediately when its
top source frame is a bind.  Direct and saturated target protocols share this
source shape; lazy misses are deliberately excluded because their cache marker
must be published before the bind can resume. -/
def ConcreteStructuredBindCallerAtHead (frames : List Frame) : Prop :=
  ∃ (result : Lean.FVarId)
      (continuation : Lean.Compiler.LCNF.Code .impure)
      (callerEnv : Env)
      (callerJoins : JoinEnv)
      (tail : List Frame),
    frames = .bind result continuation callerEnv callerJoins :: tail

/-- A yielded lazy result must publish its cache slot before resuming the
caller bind.  This source-only classifier selects exactly the stack shape
whose cache marker is consumed by the seven-step publication protocol. -/
def ConcreteStructuredLazyCallerAtHead (frames : List Frame) : Prop :=
  ∃ (declaration : Lean.Name)
      (result : Lean.FVarId)
      (continuation : Lean.Compiler.LCNF.Code .impure)
      (callerEnv : Env)
      (callerJoins : JoinEnv)
      (tail : List Frame),
    frames = .cache declaration ::
      .bind result continuation callerEnv callerJoins :: tail

/-- The established supported caller stack strengthened by source-validation
provenance for exactly the same source frames.  Target-frame shape and the
direct/saturated/lazy distinction remain owned by the production-supported
stack; this companion adds no target execution or future source step. -/
structure ConcreteStructuredValidatedFrameStack
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (functionResult : Fir.Wasm.AbiKind)
    (expectedResult : Option Fir.Wasm.AbiKind)
    (sourceFrames : List Frame)
    (targetFrames : List StructuredWasmFrame) : Prop where
  supported : ConcreteStructuredSupportedFrameStack program sourceModule
    targetModule hosts functionResult expectedResult sourceFrames targetFrames
  validation : ConcreteStructuredSuspendedValidation program functionResult
    expectedResult sourceFrames

/-- The compiler-produced root has no suspended caller validation. -/
theorem ConcreteStructuredValidatedFrameStack.nil
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {functionResult : Fir.Wasm.AbiKind} :
    ConcreteStructuredValidatedFrameStack program sourceModule targetModule
      hosts functionResult none [] [] :=
  ⟨.nil, .nil⟩

/-- Structured case labels are target-only control frames and leave the
suspended source-validation stack unchanged. -/
theorem ConcreteStructuredValidatedFrameStack.case
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {functionResult : Fir.Wasm.AbiKind}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {sourceFrames : List Frame}
    {targetFrames : List StructuredWasmFrame}
    {belowStack : List Wasm.Value}
    {targetRest : Wasm.Program}
    {testCount : Nat}
    (tail : ConcreteStructuredValidatedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult sourceFrames
      targetFrames) :
    ConcreteStructuredValidatedFrameStack program sourceModule targetModule
      hosts functionResult expectedResult sourceFrames
      (structuredWasmCaseLabels belowStack targetRest testCount ++
        targetFrames) :=
  ⟨.case tail.supported, tail.validation⟩

/-- A production direct-call frame stores precisely the already-validated
caller continuation. -/
theorem ConcreteStructuredValidatedFrameStack.direct
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {callerContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {callerFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {callerEnv : Env}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {calleeResult callerResult kind : Fir.Wasm.AbiKind}
    {resultIndex : Nat}
    {tailResult : Option Fir.Wasm.AbiKind}
    (spec : ConcreteSupportedFunction program callerContext callerCode
      sourceModule callerFunction targetModule hosts)
    (callerResultAt : spec.sourceResultKind = callerResult)
    (contextCaches : callerContext.cachedDeclarations =
      Fir.Wasm.cachedDeclarationNames program)
    (continuationAdapted : CodeAdaptedWithSuffix callerContext sourceModule
      callerFunction labels continuation targetRest)
    (resultFound : findFVar? (functionBindings callerFunction) result =
      some resultIndex)
    (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
      some kind)
    (calleeCompatible : calleeResult.refines kind = true)
    (continuationValidation :
      ConcreteStructuredAlignedValidationState program callerContext
        callerResult continuation)
    (tail : ConcreteStructuredValidatedFrameStack program sourceModule
      targetModule hosts callerResult tailResult sourceFrames targetFrames) :
    ConcreteStructuredValidatedFrameStack program sourceModule targetModule
      hosts calleeResult (some kind)
      (.bind result continuation callerEnv callerJoins :: sourceFrames)
      (.call 1 callerRemainder callerLocals
          (.localSet resultIndex :: targetRest) :: targetFrames) :=
  ⟨.direct spec callerResultAt contextCaches continuationAdapted resultFound
      kindAt calleeCompatible tail.supported,
    .bind continuationValidation.toValidationState tail.validation⟩

/-- Saturated calls share the same source continuation-validation frame while
retaining their distinct generated matcher/label layout. -/
theorem ConcreteStructuredValidatedFrameStack.saturated
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {callerContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {callerFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {callerEnv : Env}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {physicalArgs callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {calleeResult callerResult kind : Fir.Wasm.AbiKind}
    {resultIndex matcherCount : Nat}
    {tailResult : Option Fir.Wasm.AbiKind}
    (spec : ConcreteSupportedFunction program callerContext callerCode
      sourceModule callerFunction targetModule hosts)
    (callerResultAt : spec.sourceResultKind = callerResult)
    (contextCaches : callerContext.cachedDeclarations =
      Fir.Wasm.cachedDeclarationNames program)
    (continuationAdapted : CodeAdaptedWithSuffix callerContext sourceModule
      callerFunction labels continuation targetRest)
    (resultFound : findFVar? (functionBindings callerFunction) result =
      some resultIndex)
    (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
      some kind)
    (calleeCompatible : calleeResult.refines kind = true)
    (continuationValidation :
      ConcreteStructuredAlignedValidationState program callerContext
        callerResult continuation)
    (tail : ConcreteStructuredValidatedFrameStack program sourceModule
      targetModule hosts callerResult tailResult sourceFrames targetFrames) :
    ConcreteStructuredValidatedFrameStack program sourceModule targetModule
      hosts calleeResult (some kind)
      (.bind result continuation callerEnv callerJoins :: sourceFrames)
      (.call 1 callerRemainder
          { callerLocals with
            values := physicalArgs.reverse ++ callerRemainder }
          [.localSet resultIndex] ::
        (List.replicate matcherCount (.label 0 callerRemainder []) ++
          .label 0 callerRemainder
              ([.localGet resultIndex, .localSet resultIndex] ++ targetRest) ::
            targetFrames)) :=
  ⟨.saturated spec callerResultAt contextCaches continuationAdapted resultFound
      kindAt calleeCompatible tail.supported,
    .bind continuationValidation.toValidationState tail.validation⟩

/-- A lazy miss suspends both the cache marker and the validated caller
continuation; cache publication later removes the marker before the bind. -/
theorem ConcreteStructuredValidatedFrameStack.lazy
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {callerContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {callerFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {callerEnv : Env}
    {declaration : Lean.Name}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {calleeResult callerResult kind : Fir.Wasm.AbiKind}
    {cacheIndex cacheSetId resultIndex : Nat}
    {tailResult : Option Fir.Wasm.AbiKind}
    (spec : ConcreteSupportedFunction program callerContext callerCode
      sourceModule callerFunction targetModule hosts)
    (callerResultAt : spec.sourceResultKind = callerResult)
    (contextCaches : callerContext.cachedDeclarations =
      Fir.Wasm.cachedDeclarationNames program)
    (continuationAdapted : CodeAdaptedWithSuffix callerContext sourceModule
      callerFunction labels continuation targetRest)
    (resultFound : findFVar? (functionBindings callerFunction) result =
      some resultIndex)
    (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
      some kind)
    (initializerFound : sourceModule.initializers[cacheIndex]? =
      some declaration)
    (signature :
      (sourceModule.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind)
    (cacheSetCall :
      callIndex? sourceModule (.runtime (.cacheSet declaration kind)) =
        some cacheSetId)
    (notObject : kind ≠ .object)
    (notTObject : kind ≠ .tobject)
    (calleeCompatible : calleeResult.refines kind = true)
    (continuationValidation :
      ConcreteStructuredAlignedValidationState program callerContext
        callerResult continuation)
    (tail : ConcreteStructuredValidatedFrameStack program sourceModule
      targetModule hosts callerResult tailResult sourceFrames targetFrames) :
    ConcreteStructuredValidatedFrameStack program sourceModule targetModule
      hosts calleeResult (some kind)
      (.cache declaration ::
        .bind result continuation callerEnv callerJoins :: sourceFrames)
      (.call 1 callerLocals.values callerLocals [
            .call cacheSetId,
            .globalSet (2 * cacheIndex + 1),
            .const 1,
            .globalSet (2 * cacheIndex)] ::
        .label 0 callerLocals.values
            ([.globalGet (2 * cacheIndex + 1),
              .localSet resultIndex] ++ targetRest) ::
          targetFrames) :=
  ⟨.lazy spec callerResultAt contextCaches continuationAdapted resultFound
      kindAt initializerFound signature cacheSetCall notObject notTObject
      calleeCompatible tail.supported,
    .lazy continuationValidation.toValidationState tail.validation⟩

/-- Branch-exact agreement between the production static/resource stack and
its residual source validation.  The explicit ABI spine is a non-proof index:
it prevents proof irrelevance from forgetting the hidden caller result kinds
when a yielded call is popped. -/
inductive ConcreteStructuredValidatedStackAgreement
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl} :
    List (AbiKind × Option AbiKind) →
    {entryRuntime : RuntimeState} →
    {entryStore : Wasm.Store Host} →
    {entryWitness : RefinementWitness} →
    {functionResult : AbiKind} →
    {expectedResult : Option AbiKind} →
    {sourceFrames : List Frame} →
    {targetFrames : List StructuredWasmFrame} →
    {supported : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult sourceFrames
      targetFrames} →
    {resources : ConcreteStructuredSuspendedResourceStack externals program
      entryRuntime entryStore entryWitness functionResult expectedResult
      sourceFrames targetFrames} →
    supported.Agrees resources →
    ConcreteStructuredSuspendedValidation program functionResult expectedResult
      sourceFrames → Prop where
  | nil
      {entryRuntime : RuntimeState}
      {entryStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind} :
      ConcreteStructuredValidatedStackAgreement []
        (ConcreteStructuredSupportedFrameStack.Agrees.nil
          (program := program) (sourceModule := sourceModule)
          (targetModule := targetModule) (hosts := hosts)
          (externals := externals) (entryRuntime := entryRuntime)
          (entryStore := entryStore) (entryWitness := entryWitness)
          (functionResult := functionResult))
        (.nil (program := program))
  | case
      {spine : List (AbiKind × Option AbiKind)}
      {entryRuntime : RuntimeState}
      {entryStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind}
      {expectedResult : Option AbiKind}
      {sourceFrames : List Frame}
      {targetFrames : List StructuredWasmFrame}
      {belowStack : List Wasm.Value}
      {targetRest : Wasm.Program}
      {testCount : Nat}
      {supportedTail : ConcreteStructuredSupportedFrameStack program
        sourceModule targetModule hosts functionResult expectedResult
        sourceFrames targetFrames}
      {resourceTail : ConcreteStructuredSuspendedResourceStack externals program
        entryRuntime entryStore entryWitness functionResult expectedResult
        sourceFrames targetFrames}
      {tailAgrees : supportedTail.Agrees resourceTail}
      {validation : ConcreteStructuredSuspendedValidation program
        functionResult expectedResult sourceFrames}
      (tailAligned : ConcreteStructuredValidatedStackAgreement spine tailAgrees
        validation) :
      ConcreteStructuredValidatedStackAgreement spine
        (.case (belowStack := belowStack) (targetRest := targetRest)
          (testCount := testCount) supportedTail resourceTail tailAgrees)
        validation
  | direct
      {spine : List (AbiKind × Option AbiKind)}
      {activeEntryRuntime callerEntryRuntime : RuntimeState}
      {activeEntryStore callerEntryStore : Wasm.Store Host}
      {activeEntryWitness callerEntryWitness : RefinementWitness}
      {callerContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {callerFunction : Fir.Wasm.Function}
      {labels : LabelContext}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerEnv : Env}
      {callerLocals : Wasm.Locals}
      {result : Lean.FVarId}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerRemainder : List Wasm.Value}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {calleeResult callerResult kind : AbiKind}
      {resultIndex : Nat}
      {tailResult : Option AbiKind}
      {supportedTail : ConcreteStructuredSupportedFrameStack program
        sourceModule targetModule hosts callerResult tailResult sourceFrames
        targetFrames}
      {resourceTail : ConcreteStructuredSuspendedResourceStack externals program
        callerEntryRuntime callerEntryStore callerEntryWitness callerResult
        tailResult sourceFrames targetFrames}
      {tailAgrees : supportedTail.Agrees resourceTail}
      {tailValidation : ConcreteStructuredSuspendedValidation program
        callerResult tailResult sourceFrames}
      (spec : ConcreteSupportedFunction program callerContext callerCode
        sourceModule callerFunction targetModule hosts)
      (callerResultAt : spec.sourceResultKind = callerResult)
      (contextCaches : callerContext.cachedDeclarations =
        Fir.Wasm.cachedDeclarationNames program)
      (callerScope : ConcreteStructuredResourceScope callerContext sourceModule
        callerFunction externals callerEntryRuntime callerEntryStore
        callerEntryWitness facts remainingBytes activeEntryRuntime callerEnv
        activeEntryStore callerLocals activeEntryWitness)
      (programEq : program = callerContext.program)
      (continuationAdapted : CodeAdaptedWithSuffix callerContext sourceModule
        callerFunction labels continuation targetRest)
      (resultFound : findFVar? (functionBindings callerFunction) result =
        some resultIndex)
      (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some kind)
      (calleeCompatible : calleeResult.refines kind = true)
      (continuationValidation : ConcreteStructuredAlignedValidationState
        program callerContext callerResult continuation)
      (tailAligned : ConcreteStructuredValidatedStackAgreement spine tailAgrees
        tailValidation) :
      ConcreteStructuredValidatedStackAgreement
        ((callerResult, tailResult) :: spine)
        (.direct (callerJoins := callerJoins)
          (callerRemainder := callerRemainder) spec callerResultAt contextCaches
          callerScope programEq continuationAdapted resultFound kindAt
          calleeCompatible supportedTail resourceTail tailAgrees)
        (.bind continuationValidation.toValidationState tailValidation)
  | saturated
      {spine : List (AbiKind × Option AbiKind)}
      {activeEntryRuntime callerEntryRuntime : RuntimeState}
      {activeEntryStore callerEntryStore : Wasm.Store Host}
      {activeEntryWitness callerEntryWitness : RefinementWitness}
      {callerContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {callerFunction : Fir.Wasm.Function}
      {labels : LabelContext}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerEnv : Env}
      {callerLocals : Wasm.Locals}
      {result : Lean.FVarId}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {physicalArgs callerRemainder : List Wasm.Value}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {calleeResult callerResult kind : AbiKind}
      {resultIndex matcherCount : Nat}
      {tailResult : Option AbiKind}
      {supportedTail : ConcreteStructuredSupportedFrameStack program
        sourceModule targetModule hosts callerResult tailResult sourceFrames
        targetFrames}
      {resourceTail : ConcreteStructuredSuspendedResourceStack externals program
        callerEntryRuntime callerEntryStore callerEntryWitness callerResult
        tailResult sourceFrames targetFrames}
      {tailAgrees : supportedTail.Agrees resourceTail}
      {tailValidation : ConcreteStructuredSuspendedValidation program
        callerResult tailResult sourceFrames}
      (spec : ConcreteSupportedFunction program callerContext callerCode
        sourceModule callerFunction targetModule hosts)
      (callerResultAt : spec.sourceResultKind = callerResult)
      (contextCaches : callerContext.cachedDeclarations =
        Fir.Wasm.cachedDeclarationNames program)
      (callerScope : ConcreteStructuredResourceScope callerContext sourceModule
        callerFunction externals callerEntryRuntime callerEntryStore
        callerEntryWitness facts remainingBytes activeEntryRuntime callerEnv
        activeEntryStore
        { callerLocals with
          values := physicalArgs.reverse ++ callerRemainder }
        activeEntryWitness)
      (programEq : program = callerContext.program)
      (continuationAdapted : CodeAdaptedWithSuffix callerContext sourceModule
        callerFunction labels continuation targetRest)
      (resultFound : findFVar? (functionBindings callerFunction) result =
        some resultIndex)
      (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some kind)
      (calleeCompatible : calleeResult.refines kind = true)
      (continuationValidation : ConcreteStructuredAlignedValidationState
        program callerContext callerResult continuation)
      (tailAligned : ConcreteStructuredValidatedStackAgreement spine tailAgrees
        tailValidation) :
      ConcreteStructuredValidatedStackAgreement
        ((callerResult, tailResult) :: spine)
        (.saturated (callerJoins := callerJoins)
          (matcherCount := matcherCount) spec callerResultAt contextCaches
          callerScope programEq continuationAdapted resultFound kindAt
          calleeCompatible supportedTail resourceTail tailAgrees)
        (.bind continuationValidation.toValidationState tailValidation)
  | lazy
      {spine : List (AbiKind × Option AbiKind)}
      {activeEntryRuntime callerEntryRuntime : RuntimeState}
      {activeEntryStore callerEntryStore : Wasm.Store Host}
      {activeEntryWitness callerEntryWitness : RefinementWitness}
      {callerContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {callerFunction : Fir.Wasm.Function}
      {labels : LabelContext}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerEnv : Env}
      {callerLocals : Wasm.Locals}
      {declaration : Lean.Name}
      {result : Lean.FVarId}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {calleeResult callerResult kind : AbiKind}
      {cacheIndex cacheSetId resultIndex : Nat}
      {tailResult : Option AbiKind}
      {supportedTail : ConcreteStructuredSupportedFrameStack program
        sourceModule targetModule hosts callerResult tailResult sourceFrames
        targetFrames}
      {resourceTail : ConcreteStructuredSuspendedResourceStack externals program
        callerEntryRuntime callerEntryStore callerEntryWitness callerResult
        tailResult sourceFrames targetFrames}
      {tailAgrees : supportedTail.Agrees resourceTail}
      {tailValidation : ConcreteStructuredSuspendedValidation program
        callerResult tailResult sourceFrames}
      (spec : ConcreteSupportedFunction program callerContext callerCode
        sourceModule callerFunction targetModule hosts)
      (callerResultAt : spec.sourceResultKind = callerResult)
      (contextCaches : callerContext.cachedDeclarations =
        Fir.Wasm.cachedDeclarationNames program)
      (callerScope : ConcreteStructuredResourceScope callerContext sourceModule
        callerFunction externals callerEntryRuntime callerEntryStore
        callerEntryWitness facts remainingBytes activeEntryRuntime callerEnv
        activeEntryStore callerLocals activeEntryWitness)
      (programEq : program = callerContext.program)
      (continuationAdapted : CodeAdaptedWithSuffix callerContext sourceModule
        callerFunction labels continuation targetRest)
      (resultFound : findFVar? (functionBindings callerFunction) result =
        some resultIndex)
      (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some kind)
      (initializerFound : sourceModule.initializers[cacheIndex]? =
        some declaration)
      (signature :
        (sourceModule.callSignature? (.declaration declaration)).bind
            (·.results[0]?) = some kind)
      (cacheSetCall :
        callIndex? sourceModule (.runtime (.cacheSet declaration kind)) =
          some cacheSetId)
      (notObject : kind ≠ .object)
      (notTObject : kind ≠ .tobject)
      (calleeCompatible : calleeResult.refines kind = true)
      (continuationValidation : ConcreteStructuredAlignedValidationState
        program callerContext callerResult continuation)
      (tailAligned : ConcreteStructuredValidatedStackAgreement spine tailAgrees
        tailValidation) :
      ConcreteStructuredValidatedStackAgreement
        ((callerResult, tailResult) :: spine)
        (.lazy (callerJoins := callerJoins) (cacheIndex := cacheIndex)
          (cacheSetId := cacheSetId) spec callerResultAt contextCaches callerScope
          programEq continuationAdapted resultFound kindAt initializerFound
          signature cacheSetCall notObject notTObject calleeCompatible
          supportedTail resourceTail tailAgrees)
        (.lazy continuationValidation.toValidationState tailValidation)

/-- Existentially hide the caller ABI spine while retaining its branch-exact
alignment. -/
def ConcreteStructuredValidationAgrees
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness}
    {functionResult : AbiKind}
    {expectedResult : Option AbiKind}
    {sourceFrames : List Frame}
    {targetFrames : List StructuredWasmFrame}
    {supported : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult sourceFrames
      targetFrames}
    {resources : ConcreteStructuredSuspendedResourceStack externals program
      entryRuntime entryStore entryWitness functionResult expectedResult
      sourceFrames targetFrames}
    (agrees : supported.Agrees resources)
    (validation : ConcreteStructuredSuspendedValidation program functionResult
      expectedResult sourceFrames) : Prop :=
  ∃ spine, ConcreteStructuredValidatedStackAgreement spine agrees validation

/-- Transport branch-exact validation agreement across frame equalities and
the propositionally irrelevant replacement proofs produced by resource-stack
reindexing. -/
theorem ConcreteStructuredValidationAgrees.reindex
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness}
    {functionResult : AbiKind}
    {expectedResult : Option AbiKind}
    {sourceFrames targetSourceFrames : List Frame}
    {targetFrames targetTargetFrames : List StructuredWasmFrame}
    {supported : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult sourceFrames
      targetFrames}
    {resources : ConcreteStructuredSuspendedResourceStack externals program
      entryRuntime entryStore entryWitness functionResult expectedResult
      sourceFrames targetFrames}
    {agrees : supported.Agrees resources}
    {validation : ConcreteStructuredSuspendedValidation program functionResult
      expectedResult sourceFrames}
    (aligned : ConcreteStructuredValidationAgrees agrees validation)
    (sourceFramesEq : targetSourceFrames = sourceFrames)
    (targetFramesEq : targetTargetFrames = targetFrames)
    {targetSupported : ConcreteStructuredSupportedFrameStack program
      sourceModule targetModule hosts functionResult expectedResult
      targetSourceFrames targetTargetFrames}
    {targetResources : ConcreteStructuredSuspendedResourceStack externals
      program entryRuntime entryStore entryWitness functionResult
      expectedResult targetSourceFrames targetTargetFrames}
    (targetAgrees : targetSupported.Agrees targetResources)
    (targetValidation : ConcreteStructuredSuspendedValidation program
      functionResult expectedResult targetSourceFrames) :
    ConcreteStructuredValidationAgrees targetAgrees targetValidation := by
  subst targetSourceFrames
  subst targetTargetFrames
  have supportedEq : targetSupported = supported := Subsingleton.elim _ _
  subst targetSupported
  have resourcesEq : targetResources = resources := Subsingleton.elim _ _
  subst targetResources
  have agreesEq : targetAgrees = agrees := Subsingleton.elim _ _
  subst targetAgrees
  have validationEq : targetValidation = validation := Subsingleton.elim _ _
  subst targetValidation
  exact aligned

/-- Admission-free compiler/resource core strengthened by the exact residual
validation state of its current source node and its agreement with the
production compiler's local row.  This companion relation is the incremental
bridge to universal compiler admission: it adds no source step, target path,
allocation budget, future admission, or termination evidence. -/
structure ConcreteStructuredValidatedCodeCoreRel
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (externals : ExternalImpl)
    (labels : LabelContext)
    (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness)
    (functionResult : AbiKind)
    (callerExpectedResult : Option AbiKind)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceCode : Lean.Compiler.LCNF.Code .impure)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (targetCode : Wasm.Program)
    (witness : RefinementWitness)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  core : ConcreteStructuredCodeCoreRel program context sourceModule
    sourceFunction externals labels entryRuntime entryStore entryWitness
    functionResult callerExpectedResult facts remainingBytes sourceRuntime
    sourceEnv sourceCode targetStore targetLocals targetCode witness source
    target
  validation : ConcreteStructuredAlignedValidationState program context
    functionResult sourceCode

/-- A closed active-code branch: the current generated node is validated,
every suspended caller continuation is validated, and the established static
caller protocol agrees with the hereditary dynamic resource stack.

Unlike `ConcreteStructuredSupportedOutcome.code`, this relation therefore
contains all source-validation evidence needed to resume either the active
node or any suspended caller.  It still contains no source step, target path,
future admission, or termination evidence. -/
structure ConcreteStructuredValidatedCodeOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (functionCode : Lean.Compiler.LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts)
    (externals : ExternalImpl)
    (labels : LabelContext)
    (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness)
    (functionResult : AbiKind)
    (callerExpectedResult : Option AbiKind)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceCode : Lean.Compiler.LCNF.Code .impure)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (targetCode : Wasm.Program)
    (witness : RefinementWitness)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  contextCaches :
    context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program
  core : ConcreteStructuredValidatedCodeCoreRel program context sourceModule
    sourceFunction externals labels entryRuntime entryStore entryWitness
    functionResult callerExpectedResult facts remainingBytes sourceRuntime
    sourceEnv sourceCode targetStore targetLocals targetCode witness source
    target
  frames : ConcreteStructuredValidatedFrameStack program sourceModule
    targetModule hosts functionResult callerExpectedResult source.frames
    target.frames
  agrees : frames.supported.Agrees core.core.resources.suspended
  validationAgrees :
    ConcreteStructuredValidationAgrees agrees frames.validation

/-- A closed staged named call.  The dynamic ready core retains the caller's
resource state, while this companion retains both the already-validated caller
stack and the residual validation of the continuation that the forthcoming
call frame will suspend. -/
structure ConcreteStructuredValidatedDirectCallReadyOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (callerContext calleeContext : Fir.Wasm.Context)
    (callerCode : Lean.Compiler.LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction calleeFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (spec : ConcreteSupportedFunction program callerContext callerCode
      sourceModule callerFunction targetModule hosts)
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    (site : DirectInternalCallSite callerContext decl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    (externals : ExternalImpl)
    (labels : LabelContext)
    (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness)
    (functionResult : AbiKind)
    (callerExpectedResult : Option AbiKind)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (physicalArgs : List Wasm.Value)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  activeResult : spec.sourceResultKind = functionResult
  contextCaches :
    callerContext.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program
  core : ConcreteStructuredDirectCallReadyCoreRel program callerContext
    calleeContext sourceModule callerFunction calleeFunction targetModule site
    row externals labels entryRuntime entryStore entryWitness functionResult
    callerExpectedResult facts remainingBytes sourceRuntime continuation
    callerJoins sourceFrames targetStore callerLocals callerRemainder targetRest
    targetFrames witness physicalArgs resultIndex source target
  continuationValidation :
    ConcreteStructuredAlignedValidationState program callerContext
      functionResult continuation
  frames : ConcreteStructuredValidatedFrameStack program sourceModule
    targetModule hosts functionResult callerExpectedResult sourceFrames
    targetFrames
  agrees : frames.supported.Agrees core.resources.suspended
  validationAgrees :
    ConcreteStructuredValidationAgrees agrees frames.validation

/-- A closed staged saturated closure call.  Resolution and its retain
capacity law are retained only across the source-only staging stutter; the
validation payload is again just the caller continuation and caller stack. -/
structure ConcreteStructuredValidatedSaturatedCallReadyOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (context calleeContext : Fir.Wasm.Context)
    (callerCode : Lean.Compiler.LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction calleeFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (spec : ConcreteSupportedFunction program context callerCode sourceModule
      sourceFunction targetModule hosts)
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    (site : SaturatedClosureCallSite context decl callerEnv)
    {sourceRuntime : RuntimeState}
    (resolution : SaturatedClosureCallResolution context sourceRuntime site)
    (row : ConcreteGeneratedInternalDeclaration context.program
      resolution.target calleeContext resolution.calleeCode sourceModule
      calleeFunction targetModule)
    (externals : ExternalImpl)
    (labels : LabelContext)
    (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness)
    (functionResult : AbiKind)
    (callerExpectedResult : Option AbiKind)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (targetValue targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  activeResult : spec.sourceResultKind = functionResult
  contextCaches :
    context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program
  sharedCapacity : ∀ parentRuntime,
    setCell sourceRuntime resolution.location
        { resolution.cell with rc := resolution.cell.rc - 1 } =
          .ok parentRuntime →
      ClosureRetainCapacity parentRuntime resolution.captures.toList
  core : ConcreteStructuredSaturatedCallReadyCoreRel program context
    sourceModule sourceFunction targetModule site externals labels entryRuntime
    entryStore entryWitness functionResult callerExpectedResult facts
    remainingBytes sourceRuntime continuation callerJoins sourceFrames
    targetStore callerLocals targetValue targetRest targetFrames witness
    resultIndex source target
  continuationValidation :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation
  frames : ConcreteStructuredValidatedFrameStack program sourceModule
    targetModule hosts functionResult callerExpectedResult sourceFrames
    targetFrames
  agrees : frames.supported.Agrees core.resources.suspended
  validationAgrees :
    ConcreteStructuredValidationAgrees agrees frames.validation

/-- A closed staged lazy-cache call.  The branch-exact hit/miss admission is
retained across the source-only invocation step, together with validation of
the continuation and every suspended caller. -/
structure ConcreteStructuredValidatedLazyCallReadyOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (functionCode : Lean.Compiler.LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts)
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {declaration : Lean.Name}
    {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    (call : LazyCacheCallSupported context decl declaration sourceDeclaration
      resultKind)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    (externals : ExternalImpl)
    (labels : LabelContext)
    (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness)
    (functionResult : AbiKind)
    (callerExpectedResult : Option AbiKind)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState)
    (callerEnv : Env)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (cacheIndex declarationId cacheSetId resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  activeResult : spec.sourceResultKind = functionResult
  contextCaches :
    context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program
  path : ConcreteStructuredLazyReadyAdmission context sourceModule call
    generated sourceRuntime
  core : ConcreteStructuredLazyCallReadyCoreRel program context sourceModule
    sourceFunction externals labels call generated entryRuntime entryStore
    entryWitness functionResult callerExpectedResult facts remainingBytes
    sourceRuntime callerEnv continuation callerJoins sourceFrames targetStore
    callerLocals targetRest targetFrames witness cacheIndex declarationId
    cacheSetId resultIndex source target
  continuationValidation :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation
  frames : ConcreteStructuredValidatedFrameStack program sourceModule
    targetModule hosts functionResult callerExpectedResult sourceFrames
    targetFrames
  agrees : frames.supported.Agrees core.resources.suspended
  validationAgrees :
    ConcreteStructuredValidationAgrees agrees frames.validation

/-- Residual validation at the imported-call boundary.  The source has
entered the named external and the target has evaluated its arguments, but
the one host call and destination write are still pending. -/
structure ConcreteStructuredValidatedExternalCallReadyOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (functionCode : Lean.Compiler.LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts)
    (externals : ExternalImpl)
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {stepCost : Nat}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    (site : PureExternalCallShape context externals sourceRuntime sourceEnv decl
      nextRuntime sourceValue stepCost)
    (operation : ExternalOperation)
    (resolvedResultKind : AbiKind)
    (targetImport : Wasm.ImportDecl)
    (labels : LabelContext)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness)
    (functionResult : AbiKind)
    (callerExpectedResult : Option AbiKind)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (physicalArgs : List Wasm.Value)
    (callIndex resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  activeResult : spec.sourceResultKind = functionResult
  contextCaches :
    context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program
  core : ConcreteStructuredExternalCallReadyCoreRel program context
    sourceModule sourceFunction targetModule hosts externals site operation
    resolvedResultKind targetImport labels continuation callerJoins sourceFrames
    entryRuntime entryStore entryWitness functionResult callerExpectedResult
    facts remainingBytes targetStore callerLocals callerRemainder targetRest
    targetFrames witness physicalArgs callIndex resultIndex source target
  continuationValidation :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation
  frames : ConcreteStructuredValidatedFrameStack program sourceModule
    targetModule hosts functionResult callerExpectedResult sourceFrames
    targetFrames
  agrees : frames.supported.Agrees core.resources.suspended
  validationAgrees :
    ConcreteStructuredValidationAgrees agrees frames.validation

/-- A closed post-call/pre-bind state.  The dynamic core retains the value
that will be installed by `local.set`; the proof companion retains validation
of that continuation and of the unchanged caller tail.  Lazy cache
publication enters this state after removing only its cache marker. -/
structure ConcreteStructuredValidatedExternalBindOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (functionCode : Lean.Compiler.LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts)
    (externals : ExternalImpl)
    (labels : LabelContext)
    (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness)
    (functionResult : AbiKind)
    (callerExpectedResult : Option AbiKind)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState)
    (callerEnv : Env)
    (sourceValue : Value)
    (result : Lean.FVarId)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (kind : AbiKind)
    (physical : Wasm.Value)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  activeResult : spec.sourceResultKind = functionResult
  contextCaches :
    context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program
  core : ConcreteStructuredExternalBindCoreRel program context sourceModule
    sourceFunction externals labels entryRuntime entryStore entryWitness
    functionResult callerExpectedResult facts remainingBytes sourceRuntime
    callerEnv sourceValue result continuation callerJoins sourceFrames
    targetStore callerLocals callerRemainder targetRest targetFrames witness
    kind physical resultIndex source target
  continuationValidation :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation
  frames : ConcreteStructuredValidatedFrameStack program sourceModule
    targetModule hosts functionResult callerExpectedResult sourceFrames
    targetFrames
  agrees : frames.supported.Agrees core.resources.suspended
  validationAgrees :
    ConcreteStructuredValidationAgrees agrees frames.validation

/-- A closed yielded result.  No active code remains to validate; all static
validation needed for a nonterminal successor lives in the suspended caller
stack that will be restored by the pop transition. -/
structure ConcreteStructuredValidatedReturnedOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (functionCode : Lean.Compiler.LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts)
    (externals : ExternalImpl)
    (labels : LabelContext)
    (entryRuntime : RuntimeState)
    (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness)
    (functionResult : AbiKind)
    (callerExpectedResult : Option AbiKind)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (witness : RefinementWitness)
    (kind : AbiKind)
    (physical : Wasm.Value)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  activeResult : spec.sourceResultKind = functionResult
  contextCaches :
    context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program
  yielded : ConcreteStructuredYieldFocus context sourceFunction sourceRuntime
    sourceEnv sourceValue targetStore targetLocals witness kind physical source
    target
  compatible : ConcreteStructuredResultCompatible kind callerExpectedResult
  resources : ConcreteStructuredResourceStack program context sourceModule
    sourceFunction externals entryRuntime sourceRuntime entryStore targetStore
    entryWitness witness facts remainingBytes sourceEnv targetLocals
    functionResult callerExpectedResult source.frames target.frames
  frames : ConcreteStructuredValidatedFrameStack program sourceModule
    targetModule hosts functionResult callerExpectedResult source.frames
    target.frames
  agrees : frames.supported.Agrees resources.suspended
  validationAgrees :
    ConcreteStructuredValidationAgrees agrees frames.validation

/-- Module-wide closed relation for active generated code.  The constructor
hides the current generated function, entry anchor, resource budget, residual
validator state, and compiler focus while retaining the proof that the active
function's selected result ABI is the one validated at its root.

The administrative constructors carry caller-continuation validation across
direct, saturated, lazy-cache, and external staging boundaries; the returned
branch retains the validated suspended stack needed by its next pop. -/
inductive ConcreteStructuredValidatedCodeGlobalOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : ExternalImpl) :
    MachineState → StructuredWasmState Host → Prop where
  | code
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {sourceEnv : Env}
      {sourceCode : Lean.Compiler.LCNF.Code .impure}
      {targetLocals : Wasm.Locals}
      {targetCode : Wasm.Program}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (activeResult : spec.sourceResultKind = functionResult)
      (related : ConcreteStructuredValidatedCodeOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec
        externals labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        sourceCode targetStore targetLocals targetCode witness source target) :
      ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
        targetModule hosts externals source target
  | directReady
      {callerContext calleeContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {callerFunction calleeFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program callerContext callerCode
        sourceModule callerFunction targetModule hosts}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {callerEnv : Env}
      {site : DirectInternalCallSite callerContext decl callerEnv}
      {row : ConcreteGeneratedInternalDeclaration callerContext.program
        site.sourceDeclaration calleeContext site.calleeCode sourceModule
        calleeFunction targetModule}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerLocals : Wasm.Locals}
      {callerRemainder : List Wasm.Value}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {physicalArgs : List Wasm.Value}
      {resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedDirectCallReadyOutcome program
        callerContext calleeContext callerCode sourceModule callerFunction
        calleeFunction targetModule hosts spec site row externals labels
        entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime continuation
        callerJoins sourceFrames targetStore callerLocals callerRemainder
        targetRest targetFrames witness physicalArgs resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
        targetModule hosts externals source target
  | saturatedReady
      {context calleeContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction calleeFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context callerCode sourceModule
        sourceFunction targetModule hosts}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {callerEnv : Env}
      {site : SaturatedClosureCallSite context decl callerEnv}
      {sourceRuntime : RuntimeState}
      {resolution : SaturatedClosureCallResolution context sourceRuntime site}
      {row : ConcreteGeneratedInternalDeclaration context.program
        resolution.target calleeContext resolution.calleeCode sourceModule
        calleeFunction targetModule}
      {labels : LabelContext}
      {entryRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerLocals : Wasm.Locals}
      {targetValue targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedSaturatedCallReadyOutcome program
        context calleeContext callerCode sourceModule sourceFunction
        calleeFunction targetModule hosts spec site resolution row externals
        labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes continuation callerJoins
        sourceFrames targetStore callerLocals targetValue targetRest targetFrames
        witness resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
        targetModule hosts externals source target
  | lazyReady
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {declaration : Lean.Name}
      {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
      {resultKind : AbiKind}
      {call : LazyCacheCallSupported context decl declaration
        sourceDeclaration resultKind}
      {generated : LazyCacheGeneratedEnvironment context sourceModule}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerEnv : Env}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerLocals : Wasm.Locals}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {cacheIndex declarationId cacheSetId resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedLazyCallReadyOutcome program
        context functionCode sourceModule sourceFunction targetModule hosts spec
        call generated externals labels entryRuntime entryStore entryWitness
        functionResult callerExpectedResult facts remainingBytes sourceRuntime
        callerEnv continuation callerJoins sourceFrames targetStore callerLocals
        targetRest targetFrames witness cacheIndex declarationId cacheSetId
        resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
        targetModule hosts externals source target
  | externalReady
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {sourceValue : Value}
      {stepCost : Nat}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {site : PureExternalCallShape context externals sourceRuntime sourceEnv
        decl nextRuntime sourceValue stepCost}
      {operation : ExternalOperation}
      {resolvedResultKind : AbiKind}
      {targetImport : Wasm.ImportDecl}
      {labels : LabelContext}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {entryRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerLocals : Wasm.Locals}
      {callerRemainder : List Wasm.Value}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {physicalArgs : List Wasm.Value}
      {callIndex resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedExternalCallReadyOutcome program
        context functionCode sourceModule sourceFunction targetModule hosts spec
        externals site operation resolvedResultKind targetImport labels
        continuation callerJoins sourceFrames entryRuntime entryStore
        entryWitness functionResult callerExpectedResult facts remainingBytes
        targetStore callerLocals callerRemainder targetRest targetFrames witness
        physicalArgs callIndex resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
        targetModule hosts externals source target
  | externalBind
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerEnv : Env}
      {sourceValue : Value}
      {result : Lean.FVarId}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerLocals : Wasm.Locals}
      {callerRemainder : List Wasm.Value}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {kind : AbiKind}
      {physical : Wasm.Value}
      {resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedExternalBindOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec
        externals labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime callerEnv
        sourceValue result continuation callerJoins sourceFrames targetStore
        callerLocals callerRemainder targetRest targetFrames witness kind
        physical resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
        targetModule hosts externals source target
  | returned
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {sourceEnv : Env}
      {sourceValue : Value}
      {targetLocals : Wasm.Locals}
      {kind : AbiKind}
      {physical : Wasm.Value}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedReturnedOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec
        externals labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        sourceValue targetStore targetLocals witness kind physical source
        target) :
      ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
        targetModule hosts externals source target

/-- Witness-indexed form of the closed validated global relation.

The original relation is `Prop`-valued and therefore cannot expose the
refinement witness hidden by its constructors. This companion keeps that ghost
witness as an explicit index while reusing the same seven validated outcome
structures. It is the uniform boundary required to state constructor-schema
agreement without computing data from proof evidence. -/
inductive ConcreteStructuredValidatedCodeGlobalOutcomeAt
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : ExternalImpl)
    (witness : RefinementWitness) :
    MachineState → StructuredWasmState Host → Prop where
  | code
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {sourceEnv : Env}
      {sourceCode : Lean.Compiler.LCNF.Code .impure}
      {targetLocals : Wasm.Locals}
      {targetCode : Wasm.Program}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (activeResult : spec.sourceResultKind = functionResult)
      (related : ConcreteStructuredValidatedCodeOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec
        externals labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        sourceCode targetStore targetLocals targetCode witness source target) :
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target
  | directReady
      {callerContext calleeContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {callerFunction calleeFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program callerContext callerCode
        sourceModule callerFunction targetModule hosts}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {callerEnv : Env}
      {site : DirectInternalCallSite callerContext decl callerEnv}
      {row : ConcreteGeneratedInternalDeclaration callerContext.program
        site.sourceDeclaration calleeContext site.calleeCode sourceModule
        calleeFunction targetModule}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerLocals : Wasm.Locals}
      {callerRemainder : List Wasm.Value}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {physicalArgs : List Wasm.Value}
      {resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedDirectCallReadyOutcome program
        callerContext calleeContext callerCode sourceModule callerFunction
        calleeFunction targetModule hosts spec site row externals labels
        entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime continuation
        callerJoins sourceFrames targetStore callerLocals callerRemainder
        targetRest targetFrames witness physicalArgs resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target
  | saturatedReady
      {context calleeContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction calleeFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context callerCode sourceModule
        sourceFunction targetModule hosts}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {callerEnv : Env}
      {site : SaturatedClosureCallSite context decl callerEnv}
      {sourceRuntime : RuntimeState}
      {resolution : SaturatedClosureCallResolution context sourceRuntime site}
      {row : ConcreteGeneratedInternalDeclaration context.program
        resolution.target calleeContext resolution.calleeCode sourceModule
        calleeFunction targetModule}
      {labels : LabelContext}
      {entryRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerLocals : Wasm.Locals}
      {targetValue targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedSaturatedCallReadyOutcome program
        context calleeContext callerCode sourceModule sourceFunction
        calleeFunction targetModule hosts spec site resolution row externals
        labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes continuation callerJoins
        sourceFrames targetStore callerLocals targetValue targetRest targetFrames
        witness resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target
  | lazyReady
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {declaration : Lean.Name}
      {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
      {resultKind : AbiKind}
      {call : LazyCacheCallSupported context decl declaration
        sourceDeclaration resultKind}
      {generated : LazyCacheGeneratedEnvironment context sourceModule}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerEnv : Env}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerLocals : Wasm.Locals}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {cacheIndex declarationId cacheSetId resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedLazyCallReadyOutcome program
        context functionCode sourceModule sourceFunction targetModule hosts spec
        call generated externals labels entryRuntime entryStore entryWitness
        functionResult callerExpectedResult facts remainingBytes sourceRuntime
        callerEnv continuation callerJoins sourceFrames targetStore callerLocals
        targetRest targetFrames witness cacheIndex declarationId cacheSetId
        resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target
  | externalReady
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {sourceValue : Value}
      {stepCost : Nat}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {site : PureExternalCallShape context externals sourceRuntime sourceEnv
        decl nextRuntime sourceValue stepCost}
      {operation : ExternalOperation}
      {resolvedResultKind : AbiKind}
      {targetImport : Wasm.ImportDecl}
      {labels : LabelContext}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {entryRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerLocals : Wasm.Locals}
      {callerRemainder : List Wasm.Value}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {physicalArgs : List Wasm.Value}
      {callIndex resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedExternalCallReadyOutcome program
        context functionCode sourceModule sourceFunction targetModule hosts spec
        externals site operation resolvedResultKind targetImport labels
        continuation callerJoins sourceFrames entryRuntime entryStore
        entryWitness functionResult callerExpectedResult facts remainingBytes
        targetStore callerLocals callerRemainder targetRest targetFrames witness
        physicalArgs callIndex resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target
  | externalBind
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {callerEnv : Env}
      {sourceValue : Value}
      {result : Lean.FVarId}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {callerJoins : JoinEnv}
      {sourceFrames : List Frame}
      {callerLocals : Wasm.Locals}
      {callerRemainder : List Wasm.Value}
      {targetRest : Wasm.Program}
      {targetFrames : List StructuredWasmFrame}
      {kind : AbiKind}
      {physical : Wasm.Value}
      {resultIndex : Nat}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedExternalBindOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec
        externals labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime callerEnv
        sourceValue result continuation callerJoins sourceFrames targetStore
        callerLocals callerRemainder targetRest targetFrames witness kind
        physical resultIndex source target) :
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target
  | returned
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {labels : LabelContext}
      {entryRuntime sourceRuntime : RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness : RefinementWitness}
      {functionResult : AbiKind}
      {callerExpectedResult : Option AbiKind}
      {facts : ReuseCapacityFacts}
      {remainingBytes : Nat}
      {sourceEnv : Env}
      {sourceValue : Value}
      {targetLocals : Wasm.Locals}
      {kind : AbiKind}
      {physical : Wasm.Value}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedReturnedOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec
        externals labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        sourceValue targetStore targetLocals witness kind physical source
        target) :
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target


/-- Forget the explicit witness index without changing the validated outcome. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcomeAt.toValidatedGlobal
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals witness source target) :
    ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals source target := by
  cases related with
  | code activeResult related => exact .code activeResult related
  | directReady related => exact .directReady related
  | saturatedReady related => exact .saturatedReady related
  | lazyReady related => exact .lazyReady related
  | externalReady related => exact .externalReady related
  | externalBind related => exact .externalBind related
  | returned related => exact .returned related

/-- Closed validated execution with one existential constructor schema and an
explicitly indexed active witness. Both are ghost proof state. -/
def ConcreteStructuredSchemaValidatedCodeGlobalOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : ExternalImpl)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop :=
  ∃ (schema : ConstructorSchema) (witness : RefinementWitness),
    schema.WitnessAgrees witness ∧
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target

/-- One schema-enriched validated successor together with the exact
source/compiler constructor-schema transition that produced it.

This is the induction-friendly step boundary.  The transition is independent
of concrete target execution; the successor witness remains confined to the
validated compiler relation and agrees with the transition's resulting
schema. -/
def ConcreteStructuredSchemaValidatedCodeStepOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : ExternalImpl)
    (source sourceAfter : MachineState)
    (schema : ConstructorSchema)
    (targetAfter : StructuredWasmState Host) : Prop :=
  ∃ (nextSchema : ConstructorSchema) (nextWitness : RefinementWitness),
    ConstructorSchema.SourceStep externals source sourceAfter schema
        nextSchema ∧
      nextSchema.WitnessAgrees nextWitness ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals nextWitness sourceAfter targetAfter

/-- Forget the retained source schema transition and recover the established
schema-global successor relation. -/
theorem ConcreteStructuredSchemaValidatedCodeStepOutcome.toSchemaGlobal
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {source sourceAfter : MachineState}
    {schema : ConstructorSchema}
    {targetAfter : StructuredWasmState Host}
    (related : ConcreteStructuredSchemaValidatedCodeStepOutcome program
      sourceModule targetModule hosts externals source sourceAfter schema
      targetAfter) :
    ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals sourceAfter targetAfter := by
  obtain ⟨nextSchema, nextWitness, _transition, agrees, validated⟩ := related
  exact ⟨nextSchema, nextWitness, agrees, validated⟩

/-- Any witness-indexed successor with unchanged witness inherits the current
schema agreement directly. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcomeAt.withSchema
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {schema : ConstructorSchema}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals witness source target)
    (agrees : schema.WitnessAgrees witness) :
    ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals source target :=
  ⟨schema, witness, agrees, related⟩

/-- A witness-indexed successor under monotone witness growth inherits the
current schema after transporting agreement through the extension. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcomeAt.withSchemaExtension
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {schema : ConstructorSchema}
    {before after : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals after source target)
    (agrees : schema.WitnessAgrees before)
    (extension : before.Extends after) :
    ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals source target :=
  related.withSchema (agrees.witnessExtension extension)

/-- Lift an indexed validated successor through an explicitly classified
schema-preserving source step. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcomeAt.withSchemaPreservedStep
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {schema : ConstructorSchema}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {targetAfter : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals witness sourceAfter targetAfter)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (noShape : ¬ ∃ nextSchema,
      ConstructorSchema.DirectLetShapeAt source schema nextSchema)
    (agrees : schema.WitnessAgrees witness) :
    ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
      targetModule hosts externals source sourceAfter schema targetAfter :=
  ⟨schema, witness, .preserved sourceStep noShape, agrees, related⟩

/-- Monotone witness growth is orthogonal to an unchanged source schema
transition. -/
theorem
    ConcreteStructuredValidatedCodeGlobalOutcomeAt.withSchemaExtensionPreservedStep
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {schema : ConstructorSchema}
    {before after : RefinementWitness}
    {source sourceAfter : MachineState}
    {targetAfter : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals after sourceAfter targetAfter)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (noShape : ¬ ∃ nextSchema,
      ConstructorSchema.DirectLetShapeAt source schema nextSchema)
    (agrees : schema.WitnessAgrees before)
    (extension : before.Extends after) :
    ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
      targetModule hosts externals source sourceAfter schema targetAfter :=
  related.withSchemaPreservedStep sourceStep noShape
    (agrees.witnessExtension extension)

/-- Erase the constructor-schema ghost layer back to the established global
validated relation. -/
theorem ConcreteStructuredSchemaValidatedCodeGlobalOutcome.toValidatedGlobal
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredSchemaValidatedCodeGlobalOutcome program
      sourceModule targetModule hosts externals source target) :
    ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals source target := by
  obtain ⟨schema, witness, agrees, indexed⟩ := related
  exact indexed.toValidatedGlobal

/-- Forget only the residual source-validation evidence.  The closed code
branch projects to the established recursively stable supported relation
without changing either machine state or any dynamic resource proof. -/
theorem ConcreteStructuredValidatedCodeOutcome.toSupportedOutcome
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target) :
    ConcreteStructuredSupportedOutcome program context functionCode sourceModule
      sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult callerExpectedResult source target :=
  .code related.contextCaches related.core.core related.frames.supported
    related.agrees

/-- Forget validation from a staged named call without changing either
machine or its production-supported administrative branch. -/
theorem ConcreteStructuredValidatedDirectCallReadyOutcome.toSupportedOutcome
    {program : Fir.LeanIR.ImpureProgram}
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program callerContext callerCode
      sourceModule callerFunction targetModule hosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedDirectCallReadyOutcome program
      callerContext calleeContext callerCode sourceModule callerFunction
      calleeFunction targetModule hosts spec site row externals labels
      entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime continuation callerJoins sourceFrames
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs resultIndex source target) :
    ConcreteStructuredSupportedOutcome program callerContext callerCode
      sourceModule callerFunction targetModule hosts spec externals labels
      entryRuntime entryStore entryWitness functionResult callerExpectedResult
      source target :=
  .directReady related.core related.contextCaches related.frames.supported
    related.agrees

/-- Forget validation from a staged saturated call while retaining its exact
resolution, generated row, and closure-capacity law. -/
theorem
    ConcreteStructuredValidatedSaturatedCallReadyOutcome.toSupportedOutcome
    {program : Fir.LeanIR.ImpureProgram}
    {context calleeContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context callerCode sourceModule
      sourceFunction targetModule hosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : SaturatedClosureCallSite context decl callerEnv}
    {sourceRuntime : RuntimeState}
    {resolution : SaturatedClosureCallResolution context sourceRuntime site}
    {row : ConcreteGeneratedInternalDeclaration context.program
      resolution.target calleeContext resolution.calleeCode sourceModule
      calleeFunction targetModule}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {targetValue targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedSaturatedCallReadyOutcome program
      context calleeContext callerCode sourceModule sourceFunction
      calleeFunction targetModule hosts spec site resolution row externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes continuation callerJoins
      sourceFrames targetStore callerLocals targetValue targetRest targetFrames
      witness resultIndex source target) :
    ConcreteStructuredSupportedOutcome program context callerCode sourceModule
      sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult callerExpectedResult source target :=
  .saturatedReady row related.sharedCapacity related.core
    related.contextCaches related.frames.supported related.agrees

/-- Forget validation from a staged lazy call while retaining its exact
hit/miss admission and generated cache protocol. -/
theorem ConcreteStructuredValidatedLazyCallReadyOutcome.toSupportedOutcome
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {declaration : Lean.Name}
    {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    {call : LazyCacheCallSupported context decl declaration sourceDeclaration
      resultKind}
    {generated : LazyCacheGeneratedEnvironment context sourceModule}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {callerEnv : Env}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {cacheIndex declarationId cacheSetId resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedLazyCallReadyOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec call
      generated externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult facts remainingBytes sourceRuntime
      callerEnv continuation callerJoins sourceFrames targetStore callerLocals
      targetRest targetFrames witness cacheIndex declarationId cacheSetId
      resultIndex source target) :
    ConcreteStructuredSupportedOutcome program context functionCode sourceModule
      sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult callerExpectedResult source target :=
  .lazyReady related.path related.core related.contextCaches
    related.frames.supported related.agrees

/-- Forget validation from a staged external call while retaining the exact
dynamic host-call protocol and suspended resource stack. -/
theorem ConcreteStructuredValidatedExternalCallReadyOutcome.toSupportedOutcome
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {stepCost : Nat}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {site : PureExternalCallShape context externals sourceRuntime sourceEnv decl
      nextRuntime sourceValue stepCost}
    {operation : ExternalOperation}
    {resolvedResultKind : AbiKind}
    {targetImport : Wasm.ImportDecl}
    {labels : LabelContext}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {entryRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {physicalArgs : List Wasm.Value}
    {callIndex resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedExternalCallReadyOutcome program
      context functionCode sourceModule sourceFunction targetModule hosts spec
      externals site operation resolvedResultKind targetImport labels
      continuation callerJoins sourceFrames entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs callIndex resultIndex source target) :
    ConcreteStructuredSupportedOutcome program context functionCode sourceModule
      sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult callerExpectedResult source target :=
  .externalReady related.core related.contextCaches related.frames.supported
    related.agrees

/-- Forget validation from a post-call/pre-bind state without changing the
dynamic external-bind protocol. -/
theorem ConcreteStructuredValidatedExternalBindOutcome.toSupportedOutcome
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {callerEnv : Env}
    {sourceValue : Value}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedExternalBindOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec
      externals labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime callerEnv
      sourceValue result continuation callerJoins sourceFrames targetStore
      callerLocals callerRemainder targetRest targetFrames witness kind physical
      resultIndex source target) :
    ConcreteStructuredSupportedOutcome program context functionCode sourceModule
      sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult callerExpectedResult source target :=
  .externalBind related.core related.contextCaches related.frames.supported
    related.agrees

/-- Forget validation from a yielded state while retaining its exact result,
resource stack, and production caller protocol. -/
theorem ConcreteStructuredValidatedReturnedOutcome.toSupportedOutcome
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceValue : Value}
    {targetLocals : Wasm.Locals}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedReturnedOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec
      externals labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceValue targetStore targetLocals witness kind physical source target) :
    ConcreteStructuredSupportedOutcome program context functionCode sourceModule
      sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult callerExpectedResult source target :=
  .returned related.yielded related.compatible related.resources
    related.contextCaches related.frames.supported related.agrees

/-- Attach current-node admission to the closed admission-free relation.  The
admission remains a one-step classifier: it contains neither the source step
nor a target path, and the closed validation evidence is not duplicated in
the older pointwise relation. -/
theorem ConcreteStructuredValidatedCodeOutcome.toPointwise
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {requiredBytes remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
      externals functionResult facts sourceRuntime sourceEnv requiredBytes
      sourceCode)
    (budget : requiredBytes ≤ remainingBytes) :
    ConcreteStructuredCodePointwiseRel program context functionCode sourceModule
      sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult callerExpectedResult facts
      requiredBytes remainingBytes sourceRuntime sourceEnv sourceCode targetStore
      targetLocals targetCode witness source target :=
  ⟨related.contextCaches, related.core.core.focus,
    related.core.core.resources, admitted, budget⟩

/-- The closed global active-code relation strengthens the established
recursively stable supported relation. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcome.toSupportedGlobal
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeGlobalOutcome program
      sourceModule targetModule hosts externals source target) :
    ConcreteStructuredSupportedGlobalOutcome program sourceModule targetModule
      hosts externals source target := by
  cases related with
  | code activeResult code =>
      exact code.toSupportedOutcome.toGlobal activeResult
  | directReady ready =>
      exact ready.toSupportedOutcome.toGlobal ready.activeResult
  | saturatedReady ready =>
      exact ready.toSupportedOutcome.toGlobal ready.activeResult
  | lazyReady ready =>
      exact ready.toSupportedOutcome.toGlobal ready.activeResult
  | externalReady ready =>
      exact ready.toSupportedOutcome.toGlobal ready.activeResult
  | externalBind bind =>
      exact bind.toSupportedOutcome.toGlobal bind.activeResult
  | returned returned =>
      exact returned.toSupportedOutcome.toGlobal returned.activeResult

/-- Reassemble the closed active-code branch after a local core theorem has
advanced both controls and supplied the exact frame equalities.  Static caller
validation is transported only across the source-frame equality; the existing
`Agrees.reindex` theorem transports the production protocol/resource proof
across both equalities. -/
theorem ConcreteStructuredValidatedCodeOutcome.withSuccessor
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore nextStore : Wasm.Store Host}
    {entryWitness witness nextWitness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts nextFacts : ReuseCapacityFacts}
    {remainingBytes nextRemainingBytes : Nat}
    {sourceEnv nextEnv : Env}
    {sourceCode nextCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals nextLocals : Wasm.Locals}
    {targetCode nextTargetCode : Wasm.Program}
    {source nextSource : MachineState}
    {target nextTarget : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (nextCore : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult nextFacts
      nextRemainingBytes nextRuntime nextEnv nextCode nextStore nextLocals
      nextTargetCode nextWitness nextSource nextTarget)
    (sourceFramesEq : nextSource.frames = source.frames)
    (targetFramesEq : nextTarget.frames = target.frames) :
    ConcreteStructuredValidatedCodeOutcome program context functionCode
      sourceModule sourceFunction targetModule hosts spec externals labels
      entryRuntime entryStore entryWitness functionResult callerExpectedResult
      nextFacts nextRemainingBytes nextRuntime nextEnv nextCode nextStore
      nextLocals nextTargetCode nextWitness nextSource nextTarget := by
  obtain ⟨nextSupported, nextAgrees⟩ := related.agrees.reindex
    sourceFramesEq targetFramesEq nextCore.core.resources.suspended
  have nextValidation :
      ConcreteStructuredSuspendedValidation program functionResult
        callerExpectedResult nextSource.frames := by
    rw [sourceFramesEq]
    exact related.frames.validation
  have nextValidationAgrees :
      ConcreteStructuredValidationAgrees nextAgrees nextValidation :=
    related.validationAgrees.reindex sourceFramesEq targetFramesEq nextAgrees
      nextValidation
  exact ⟨related.contextCaches, nextCore,
    ⟨nextSupported, nextValidation⟩, nextAgrees, nextValidationAgrees⟩

/-- Common closed-state transport for an operation theorem that returns a
continued active-code core.  Operation-specific lemmas still derive the exact
source/target executions; this theorem only attaches the already-derived
residual validator state and transports the hereditary caller invariant. -/
theorem ConcreteStructuredValidatedCodeOutcome.advanceCode
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes targetCount : Nat}
    {sourceEnv : Env}
    {sourceCode nextCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (nextValidation : ConcreteStructuredAlignedValidationState program context
      functionResult nextCode)
    (advanced :
      ∃ targetAfter nextStore nextTargetCode,
        FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
            targetCount target targetAfter ∧
          sourceAfter.frames = source.frames ∧
          targetAfter.frames = target.frames ∧
          ConcreteStructuredCodeCoreRel program context sourceModule
            sourceFunction externals labels entryRuntime entryStore entryWitness
            functionResult callerExpectedResult facts remainingBytes nextRuntime
            sourceEnv nextCode nextStore targetLocals nextTargetCode witness
            sourceAfter targetAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          nextCode nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, sourceFramesEq,
      targetFramesEq, nextCore⟩ := advanced
  have validatedCore :
      ConcreteStructuredValidatedCodeCoreRel program context sourceModule
        sourceFunction externals labels entryRuntime entryStore entryWitness
        functionResult callerExpectedResult facts remainingBytes nextRuntime
        sourceEnv nextCode nextStore targetLocals nextTargetCode witness
        sourceAfter targetAfter :=
    ⟨nextCore, nextValidation⟩
  exact ⟨targetAfter, nextStore, nextTargetCode, targetPath,
    related.withSuccessor validatedCore sourceFramesEq targetFramesEq⟩

/-- Attach a dynamically reached core to a separately advanced residual
validator state.  Keeping this operation explicit is important: successor
validation is proved from the current syntax node, never guessed from target
instructions or stored as a future execution certificate. -/
theorem ConcreteStructuredValidatedCodeCoreRel.withSuccessor
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts nextFacts : ReuseCapacityFacts}
    {remainingBytes nextRemainingBytes : Nat}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv nextEnv : Env}
    {sourceCode nextCode : Lean.Compiler.LCNF.Code .impure}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {targetCode nextTargetCode : Wasm.Program}
    {witness nextWitness : RefinementWitness}
    {source nextSource : MachineState}
    {target nextTarget : StructuredWasmState Host}
    (_related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv sourceCode targetStore targetLocals targetCode
      witness source target)
    (nextCore : ConcreteStructuredCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv nextCode nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget)
    (nextValidation : ConcreteStructuredAlignedValidationState program context
      functionResult nextCode) :
    ConcreteStructuredValidatedCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv nextCode nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget :=
  ⟨nextCore, nextValidation⟩

/-- A successful proof-facing ABI classification is the same successful value
classification consumed by production lowering. -/
private theorem checkedAbiKind_of_abiValueKind?
    {type : Lean.Expr} {kind : Fir.Wasm.AbiKind}
    (found : Fir.Wasm.abiValueKind? type = some kind) :
    Fir.Wasm.checkedAbiKind type = .ok kind := by
  unfold Fir.Wasm.abiValueKind? at found
  cases classified : Fir.Wasm.abiKind? type with
  | error error => simp [classified] at found
  | ok kind? =>
      cases kind? with
      | none => simp [classified] at found
      | some actual =>
          have actualEq : actual = kind := by
            simpa [classified] using found
          subst actual
          simp [Fir.Wasm.checkedAbiKind, Fir.Wasm.abiKind, classified,
            Bind.bind, Except.bind, pure, Except.pure]

/-- Successful named-call validation retains the exact compatibility check
that production `effectiveLetValueKind` performs for the selected result. -/
private theorem supportedNamedCall_result_compatible
    {program : Fir.LeanIR.ImpureProgram}
    {locals : Fir.Wasm.LocalKinds}
    {declared result : Fir.Wasm.AbiKind}
    {name : Lean.Name}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {target : Lean.Compiler.LCNF.Decl .impure}
    (supported :
      Fir.Wasm.supportedNamedCall program locals declared name args = true)
    (targetFound : program.findDecl? name = some target)
    (resultFound :
      Fir.Wasm.effectiveDeclarationResultKind? target = some result) :
    result.leanCompatible declared = true := by
  unfold Fir.Wasm.supportedNamedCall at supported
  simp only [targetFound] at supported
  rw [resultFound] at supported
  split at supported <;> simp_all

/-- Refining the public object-family result of a box twice is idempotent. -/
private theorem boxResultKind_idempotent_tobject (type : Lean.Expr) :
    Fir.Wasm.boxResultKind type
      (Fir.Wasm.boxResultKind type .tobject) =
        Fir.Wasm.boxResultKind type .tobject := by
  unfold Fir.Wasm.boxResultKind
  split <;> simp_all

/-- The proof-facing `let` validator and production local-kind refinement
select exactly the same ABI kind.  This factors the common compiler-admission
equation for every direct primitive and both named-call lanes. -/
theorem supportedLetDeclKind?_effectiveLetValueKind
    {program : Fir.LeanIR.ImpureProgram}
    {locals : Fir.Wasm.LocalKinds}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {kind : Fir.Wasm.AbiKind}
    (supported :
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind) :
    Fir.Wasm.effectiveLetValueKind program decl = .ok kind := by
  unfold Fir.Wasm.supportedLetDeclKind? at supported
  cases declaredFound : Fir.Wasm.abiValueKind? decl.type with
  | none => simp [declaredFound] at supported
  | some declared =>
      have checked :
          Fir.Wasm.checkedAbiKind decl.type = .ok declared :=
        checkedAbiKind_of_abiValueKind? declaredFound
      rw [declaredFound] at supported
      unfold Fir.Wasm.effectiveLetValueKind Fir.Wasm.letValueKind
      cases valueFound : decl.value <;>
        simp_all [Bind.bind, Except.bind, pure, Except.pure,
          Option.bind_eq_some_iff] <;>
        aesop (config := { warnOnNonterminal := false })
      all_goals
        first
        | apply supportedNamedCall_result_compatible <;> assumption
        | apply boxResultKind_idempotent_tobject

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

/-- Production validation supplies the root residual state at the active
generated function's exact result ABI. -/
theorem ConcreteSupportedFunction.rootValidation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction target hosts)
    {functionResult : Fir.Wasm.AbiKind}
    (activeResult : spec.sourceResultKind = functionResult) :
    ∃ rootLocals,
      Fir.Wasm.addSupportedDeclarationParams? program spec.sourceDeclaration =
          some rootLocals ∧
        ConcreteStructuredValidationFocus program [] rootLocals
          (some functionResult) [] [] functionCode := by
  obtain ⟨rootLocals, parameters, supported⟩ :=
    spec.validatedBodyAt activeResult
  exact ⟨rootLocals, parameters, ⟨supported⟩⟩

/-- Production lowering and root validation agree on every parameter lookup.

The validator front-inserts parameters while the symbolic function stores
them in source order, so the proof uses name uniqueness to reverse the
validator row.  Body locals may follow the parameters in the compiler context;
they cannot shadow an already successful parameter lookup. -/
theorem ConcreteSupportedFunction.rootAlignedValidationState
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction target hosts)
    {functionResult : Fir.Wasm.AbiKind}
    (activeResult : spec.sourceResultKind = functionResult) :
    ConcreteStructuredAlignedValidationState program context functionResult
      functionCode := by
  obtain ⟨rootLocals, parametersValidated, validated⟩ :=
    spec.rootValidation activeResult
  obtain ⟨row⟩ := spec.loweredInternalDeclaration
  have parametersLowered :
      Fir.Wasm.addDeclarationParams program spec.sourceDeclaration =
        .ok rootLocals :=
    addSupportedDeclarationParams?_lowered parametersValidated
  have parameterLocalsEq : row.paramLocals = rootLocals :=
    Except.ok.inj (row.paramsAdded.symm.trans parametersLowered)
  have sourceParameters :=
    congrArg Fir.Wasm.Function.params row.sourceFunctionEq
  have sourceParameterListEq :
      sourceFunction.params.toList = rootLocals.reverse := by
    simpa [parameterLocalsEq] using congrArg Array.toList sourceParameters
  have rootNamesUnique :=
    addSupportedDeclarationParams?_namesNodup parametersValidated
  have agrees :
      ConcreteStructuredValidationLocalsAgree context rootLocals := by
    intro fvarId kind found
    have reversed :
        Fir.Wasm.findLocalKind? rootLocals.reverse fvarId = some kind :=
      findLocalKind?_reverse_eq_some rootNamesUnique found
    have parameterFound :
        Fir.Wasm.findLocalKind? sourceFunction.params.toList fvarId =
          some kind := by
      rw [sourceParameterListEq]
      exact reversed
    have bindingFound :
        Fir.Wasm.findLocalKind?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            fvarId = some kind :=
      findLocalKind?_append_eq_some parameterFound
    simp [Fir.Wasm.getLocal, spec.localKindsExact,
      FirTalos.Correctness.functionBindings, bindingFound]
  exact ⟨[], rootLocals, [], [], validated, agrees⟩

/-- The production-supported function constructs the packaged validation
state at its generated entry. -/
theorem ConcreteSupportedFunction.rootValidationState
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction target hosts)
    {functionResult : Fir.Wasm.AbiKind}
    (activeResult : spec.sourceResultKind = functionResult) :
    ConcreteStructuredValidationState program functionResult functionCode := by
  obtain ⟨rootLocals, _parameters, validated⟩ :=
    spec.rootValidation activeResult
  exact ⟨[], rootLocals, [], [], validated⟩

/-- Attach production root validation to any compiler/resource core at the
generated function's entry code.  The dynamic core may use arbitrary entry
runtime, budget, and witness indices; validation depends only on the accepted
source declaration and its active result ABI. -/
theorem ConcreteStructuredCodeCoreRel.withRootValidation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts)
    (activeResult : spec.sourceResultKind = functionResult)
    (core : ConcreteStructuredCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult facts remainingBytes sourceRuntime
      sourceEnv functionCode targetStore targetLocals targetCode witness source
      target) :
    ConcreteStructuredValidatedCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult facts remainingBytes sourceRuntime
      sourceEnv functionCode targetStore targetLocals targetCode witness source
      target :=
  ⟨core, spec.rootAlignedValidationState activeResult⟩

/-- A compiler-produced supported export starts in the closed validated
active-code relation.  This strengthens `supportedGlobalRoot` at the same
canonical source and target entries: root validation comes from the accepted
source declaration, both caller stacks are empty, and the ordinary concrete
cache/ABI frame supplies the dynamic resource root. -/
theorem ConcreteSupportedExport.validatedCodeRoot
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction targetModule hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse)
      initialWitness) :
    ConcreteStructuredValidatedCodeOutcome program context sourceCode
      sourceModule sourceFunction targetModule hosts
      spec.toConcreteSupportedFunction externals [] sourceRuntime initial
      initialWitness spec.sourceResultKind none facts remainingBytes
      sourceRuntime sourceEnv sourceCode initial
      (spec.targetFunction.toLocals parameters.reverse)
      spec.targetFunction.body initialWitness
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial
        parameters) := by
  let sourceInitial :=
    sourceCodeState context sourceRuntime sourceEnv sourceCode
  let targetLocals := spec.targetFunction.toLocals parameters.reverse
  let targetInitial :=
    concreteStructuredFunctionEntry spec.targetFunction initial parameters
  have focus :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv sourceCode initial targetLocals
        spec.targetFunction.body initialWitness sourceInitial targetInitial := {
    sourceProgramEq := by simp [sourceInitial, sourceCodeState]
    sourceControlEq := by simp [sourceInitial, sourceCodeState]
    sourceEnvEq := by simp [sourceInitial, sourceCodeState]
    sourceRuntimeEq := by simp [sourceInitial, sourceCodeState]
    targetStoreEq := by
      simp [targetInitial, concreteStructuredFunctionEntry]
    targetControlEq := by
      simp [targetInitial, targetLocals, concreteStructuredFunctionEntry]
    adapted := by
      rw [spec.targetBodyEq]
      exact CodeAdapted.withSuffix spec.bodyAdapted
    stateRelated := invariant.cacheFrame.stateRelated.stateRelated
    frameAligned := invariant.cacheFrame.1.1.1.2.2.1 }
  have scope := ConcreteStructuredResourceScope.root invariant
  have resourcesAtRoot :
      ConcreteStructuredResourceStack program context sourceModule
        sourceFunction externals sourceRuntime sourceRuntime initial initial
        initialWitness initialWitness facts remainingBytes sourceEnv targetLocals
        spec.sourceResultKind none [] [] :=
    ConcreteStructuredResourceStack.root scope
  have resources :
      ConcreteStructuredResourceStack program context sourceModule
        sourceFunction externals sourceRuntime sourceRuntime initial initial
        initialWitness initialWitness facts remainingBytes sourceEnv targetLocals
        spec.sourceResultKind none sourceInitial.frames targetInitial.frames := by
    simpa [sourceInitial, sourceCodeState, targetInitial,
      concreteStructuredFunctionEntry] using resourcesAtRoot
  have core :
      ConcreteStructuredCodeCoreRel program context sourceModule sourceFunction
        externals [] sourceRuntime initial initialWitness spec.sourceResultKind
        none facts remainingBytes sourceRuntime sourceEnv sourceCode initial
        targetLocals spec.targetFunction.body initialWitness sourceInitial
        targetInitial :=
    ⟨focus, resources⟩
  have validatedCore :
      ConcreteStructuredValidatedCodeCoreRel program context sourceModule
        sourceFunction externals [] sourceRuntime initial initialWitness
        spec.sourceResultKind none facts remainingBytes sourceRuntime sourceEnv
        sourceCode initial targetLocals spec.targetFunction.body initialWitness
        sourceInitial targetInitial :=
    ConcreteStructuredCodeCoreRel.withRootValidation
      spec.toConcreteSupportedFunction rfl core
  have frames :
      ConcreteStructuredValidatedFrameStack program sourceModule targetModule
        hosts spec.sourceResultKind none sourceInitial.frames
        targetInitial.frames := by
    simpa [sourceInitial, sourceCodeState, targetInitial,
      concreteStructuredFunctionEntry] using
      (ConcreteStructuredValidatedFrameStack.nil
        (program := program) (sourceModule := sourceModule)
        (targetModule := targetModule) (hosts := hosts)
        (functionResult := spec.sourceResultKind))
  have agrees : frames.supported.Agrees
      validatedCore.core.resources.suspended := by
    simpa [frames, sourceInitial, sourceCodeState, targetInitial,
      concreteStructuredFunctionEntry] using
      (ConcreteStructuredSupportedFrameStack.Agrees.nil
        (program := program) (sourceModule := sourceModule)
        (targetModule := targetModule) (hosts := hosts)
        (externals := externals) (entryRuntime := sourceRuntime)
        (entryStore := initial) (entryWitness := initialWitness)
        (functionResult := spec.sourceResultKind))
  change ConcreteStructuredValidatedCodeOutcome program context sourceCode
    sourceModule sourceFunction targetModule hosts
    spec.toConcreteSupportedFunction externals [] sourceRuntime initial
    initialWitness spec.sourceResultKind none facts remainingBytes sourceRuntime
    sourceEnv sourceCode initial targetLocals spec.targetFunction.body
    initialWitness sourceInitial targetInitial
  have validationAgrees :
      ConcreteStructuredValidationAgrees agrees frames.validation :=
    ⟨[], .nil⟩
  exact ⟨contextCaches, validatedCore, frames, agrees, validationAgrees⟩

/-- The canonical export entry retains its exact initial refinement witness.

This is the indexed root used by constructor-schema provenance.  It is the
same compiler-derived state as `validatedCodeGlobalRoot`; no witness is
recovered from a `Prop`-valued existential and no additional runtime premise
is introduced. -/
theorem ConcreteSupportedExport.validatedCodeGlobalRootAt
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction targetModule hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse)
      initialWitness) :
    ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals initialWitness
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial
        parameters) :=
  .code rfl (spec.validatedCodeRoot contextCaches invariant)

/-- Hide the canonical export-entry indices behind the module-wide closed
active-code relation. -/
theorem ConcreteSupportedExport.validatedCodeGlobalRoot
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction targetModule hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse)
      initialWitness) :
    ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial
        parameters) :=
  (spec.validatedCodeGlobalRootAt contextCaches invariant).toValidatedGlobal

/-- A validated direct `let` exposes the exact kind inserted into the residual
local row and the guarded-sharing update used for its continuation. -/
theorem ConcreteStructuredValidationFocus.let_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.let decl continuation)) :
    ∃ kind,
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind ∧
        ConcreteStructuredValidationFocus program joins
          (Fir.Wasm.insertLocal locals decl.fvarId kind) expectedResult facts
          (match decl.value with
          | .isShared objectId =>
              Fir.Wasm.insertSupportedSharingFact sharing decl.fvarId objectId
          | _ => Fir.Wasm.eraseSupportedSharingFact sharing decl.fvarId)
          continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  cases selected : Fir.Wasm.supportedLetDeclKind? program locals decl with
  | none =>
      rw [selected] at supported
      simp at supported
  | some kind =>
      rw [selected] at supported
      change Fir.Wasm.supportedCodeWithJoins program joins
        (Fir.Wasm.insertLocal locals decl.fvarId kind) expectedResult facts
        (match decl.value with
        | .isShared objectId =>
            Fir.Wasm.insertSupportedSharingFact sharing decl.fvarId objectId
        | _ => Fir.Wasm.eraseSupportedSharingFact sharing decl.fvarId)
        continuation = true at supported
      exact ⟨kind, rfl, ⟨supported⟩⟩

/-- A validated `let` advances the packaged residual state with exactly the
local-kind and guarded-sharing updates performed by the executable validator. -/
theorem ConcreteStructuredValidationState.letContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.let decl continuation)) :
    ∃ kind,
      ∃ locals,
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind ∧
        ConcreteStructuredValidationState program functionResult
          continuation := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  obtain ⟨kind, kindFound, next⟩ := focus.let_eq
  exact ⟨kind, locals, kindFound,
    ⟨joins,
      Fir.Wasm.insertLocal locals decl.fvarId kind,
      facts,
      (match decl.value with
      | .isShared objectId =>
          Fir.Wasm.insertSupportedSharingFact sharing decl.fvarId
            objectId
      | _ =>
          Fir.Wasm.eraseSupportedSharingFact sharing decl.fvarId),
      next⟩⟩

/-- An aligned validated `let` preserves validator/compiler local agreement
when the production compiler row contains the result binding selected by the
validator.  The premise is syntax-local and can be discharged by the existing
operation admission relation; it contains no dynamic execution evidence. -/
theorem ConcreteStructuredAlignedValidationState.letContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.let decl continuation))
    (compiled : ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind)) :
    ∃ kind,
      ∃ locals,
        Fir.Wasm.supportedLetDeclKind? program locals decl = some kind ∧
          Fir.Wasm.getLocal context decl.fvarId =
            .ok (.localGet decl.fvarId, kind) ∧
          ConcreteStructuredAlignedValidationState program context
            functionResult continuation := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  obtain ⟨kind, kindFound, next⟩ := focus.let_eq
  have resultCompiled := compiled kindFound
  exact ⟨kind, locals, kindFound, resultCompiled,
    joins,
    Fir.Wasm.insertLocal locals decl.fvarId kind,
    facts,
    (match decl.value with
    | .isShared objectId =>
        Fir.Wasm.insertSupportedSharingFact sharing decl.fvarId objectId
    | _ => Fir.Wasm.eraseSupportedSharingFact sharing decl.fvarId),
    next,
    agrees.insert resultCompiled⟩

/-- For a non-named `let`, production and executable validation select the
same destination kind.  This is the common compiler-admission bridge for the
entire direct-value family and for closure calls. -/
private theorem compiledLetResult_of_nonNamed
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {actual : Fir.Wasm.AbiKind}
    (valueKind : Fir.Wasm.letValueKind decl = .ok actual)
    (nonNamed : ∀ name args, decl.value ≠ .fap name args)
    (resultCompiled : Fir.Wasm.getLocal context decl.fvarId =
      .ok (.localGet decl.fvarId, actual)) :
    ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
  intro locals kind supported
  have effective := supportedLetDeclKind?_effectiveLetValueKind supported
  unfold Fir.Wasm.effectiveLetValueKind at effective
  rw [valueKind] at effective
  split at effective
  · rename_i name args valueEq
    exact False.elim (nonNamed name args valueEq)
  · have kindEq : actual = kind := Except.ok.inj effective
    subst kind
    exact resultCompiled

/-- Every currently supported direct-value operation exposes the exact
destination equation needed to extend validator/compiler local agreement. -/
private theorem ReuseBudgetedDirectSupported.resultCompiledForValidation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {facts : ReuseCapacityFacts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    (supported : ReuseBudgetedDirectSupported context facts decl) :
    ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
  have boundary :
      ∃ actual,
        Fir.Wasm.letValueKind decl = .ok actual ∧
          (∀ name args, decl.value ≠ .fap name args) ∧
          Fir.Wasm.getLocal context decl.fvarId =
            .ok (.localGet decl.fvarId, actual) := by
    unfold ReuseBudgetedDirectSupported ReuseConstructorBoxSupported
      ReuseReadOnlyConstructorSupported ReuseReadOnlySupported
      ReuseAliasSupported at supported
    aesop (add safe cases [ReuseSupported, LocalAliasSupported,
      ImmediateLiteralSupported, USizeProjectionSupported,
      ObjectProjectionSupported, ScalarProjectionSupported, UnboxSupported,
      IsSharedSupported, NonemptyConstructorSupported, BoxSupported,
      NaturalLiteralSupported, StringLiteralSupported])
  obtain ⟨actual, valueKind, nonNamed, resultCompiled⟩ := boundary
  intro locals kind kindFound
  exact compiledLetResult_of_nonNamed (program := program) valueKind nonNamed
    resultCompiled kindFound

/-- A saturated closure call is also a non-named `let`; its site already
retains the exact destination kind selected by production lowering. -/
private theorem SaturatedClosureCallSite.resultCompiledForValidation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {sourceEnv : Env}
    (site : SaturatedClosureCallSite context decl sourceEnv) :
    ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
  have valueKind :
      Fir.Wasm.letValueKind decl = .ok site.resultKind := by
    simp [Fir.Wasm.letValueKind, site.valueEq, site.kindEq]
  have nonNamed : ∀ name args, decl.value ≠ .fap name args := by
    intro name args
    simp [site.valueEq]
  intro locals kind kindFound
  exact compiledLetResult_of_nonNamed (program := program) valueKind nonNamed
    site.resultCompiled kindFound

/-- Named-call validation and production lowering both retain the callee's
precise result kind in the destination local.  Public result compatibility is
tracked independently by `calleeResultRefines`; it does not weaken exact local
layout agreement. -/
private theorem DirectInternalCallSite.resultCompiledForValidation
    {context : Fir.Wasm.Context}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {sourceEnv : Env}
    (site : DirectInternalCallSite context decl sourceEnv) :
    ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? context.program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
  intro locals kind supported
  have effective := supportedLetDeclKind?_effectiveLetValueKind supported
  have valueKind :
      Fir.Wasm.letValueKind decl = .ok site.resultKind := by
    simp [Fir.Wasm.letValueKind, site.valueEq, site.kindEq]
  have compatible :
      site.calleeResultKind.leanCompatible site.resultKind = true :=
    Fir.Wasm.AbiKind.leanCompatible_of_refines site.calleeResultRefines
  have siteEffective :
      Fir.Wasm.effectiveLetValueKind context.program decl =
        .ok site.calleeResultKind := by
    unfold Fir.Wasm.effectiveLetValueKind
    rw [valueKind, site.valueEq]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    simp [site.declarationFound, site.calleeResult, compatible]
  have kindEq : site.calleeResultKind = kind :=
    Except.ok.inj (siteEffective.symm.trans effective)
  subst kind
  exact site.resultCompiled

/-- Regression for the strict object-family case: when an internal callee's
effective result is `object` but the source `let` is publicly annotated
`tobject`, both executable validation and the compiler local row select the
precise `object` lane.  In particular this case does not require the two kinds
to be equal. -/
theorem DirectInternalCallSite.strictObjectToTObjectValidationRegression
    {context : Fir.Wasm.Context}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {sourceEnv : Env}
    (site : DirectInternalCallSite context decl sourceEnv)
    (calleeObject : site.calleeResultKind = .object)
    (publicTObject : site.resultKind = .tobject)
    {locals : Fir.Wasm.LocalKinds}
    {kind : AbiKind}
    (supported :
      Fir.Wasm.supportedLetDeclKind? context.program locals decl = some kind) :
    kind = .object ∧
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object) ∧
      site.calleeResultKind ≠ site.resultKind := by
  have compiledAtKind := site.resultCompiledForValidation supported
  have compiledAtObject :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object) := by
    simpa [calleeObject] using site.resultCompiled
  have kindEq : kind = .object := by
    rw [compiledAtObject] at compiledAtKind
    injection compiledAtKind with kindEq
    exact congrArg Prod.snd kindEq.symm
  exact ⟨kindEq, compiledAtObject, by simp [calleeObject, publicTObject]⟩

/-- Lazy named calls and executable validation retain the same effective
declaration result kind.  The public `let` ABI remains only a compatibility
boundary and need not equal that precise compiler-local kind. -/
private theorem LazyCacheCallSupported.resultCompiledForValidation
    {context : Fir.Wasm.Context}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {declaration : Lean.Name}
    {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    (call : LazyCacheCallSupported context decl declaration sourceDeclaration
      resultKind) :
    ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? context.program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
  rcases call with
    ⟨valueEq, kindEq, targetEq, targetResultEq, resultRefines, _paramsEq,
      resultCompiled⟩
  rename_i declaredResultKind
  intro locals kind supported
  have effective := supportedLetDeclKind?_effectiveLetValueKind supported
  have valueKind :
      Fir.Wasm.letValueKind decl = .ok declaredResultKind := by
    simp [Fir.Wasm.letValueKind, valueEq, kindEq]
  have compatible :=
    Fir.Wasm.AbiKind.leanCompatible_of_refines resultRefines
  have callEffective :
      Fir.Wasm.effectiveLetValueKind context.program decl = .ok resultKind := by
    unfold Fir.Wasm.effectiveLetValueKind
    rw [valueKind, valueEq]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    simp [targetEq, targetResultEq, compatible]
  have selectedKindEq : resultKind = kind :=
    Except.ok.inj (callEffective.symm.trans effective)
  subst kind
  exact resultCompiled

/-- Recover the exact result ABI selected by an accepted external signature. -/
private theorem externalSignatureResultKind
    {types : Fir.Wasm.ExternalTypes}
    {parameterKinds : Array AbiKind}
    {kind : AbiKind}
    (signature : Fir.Wasm.ExternalTypes.signature types =
      .ok { params := parameterKinds, results := #[kind] }) :
    Fir.Wasm.abiKind? types.result = .ok (some kind) := by
  unfold Fir.Wasm.ExternalTypes.signature at signature
  simp only [Bind.bind, Except.bind] at signature
  split at signature
  · simp_all
  · cases result : Fir.Wasm.abiKind? types.result with
    | error error =>
        simp [Fir.Wasm.resultKinds, result, Bind.bind, Except.bind] at signature
    | ok resultKind =>
        cases resultKind with
        | none =>
            simp [Fir.Wasm.resultKinds, result, Bind.bind, Except.bind, pure,
              Except.pure] at signature
        | some actual =>
            simp [Fir.Wasm.resultKinds, result, Bind.bind, Except.bind, pure,
              Except.pure] at signature
            exact congrArg (fun candidate =>
              (.ok (some candidate) : Except Fir.Wasm.AbiError
                (Option AbiKind))) signature.2

/-- A named external declaration cannot acquire the strict internal-result
refinement used for generated code; its executable and production result
locals therefore agree at the declaration's exact public ABI kind. -/
private theorem externalNamedResultCompiledForValidation
    {context : Fir.Wasm.Context}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {name : Lean.Name}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {target : Lean.Compiler.LCNF.Decl .impure}
    {argumentKinds : Array AbiKind}
    {resultKind : AbiKind}
    (valueEq : decl.value = .fap name args)
    (targetFound : context.program.findDecl? name = some target)
    (targetExternal : ∃ metadata, target.value = .extern metadata)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (signature : Fir.Wasm.ExternalTypes.signature {
        params := target.params.map (·.type)
        result := target.type } =
      .ok { params := argumentKinds, results := #[resultKind] })
    (resultCompiled : Fir.Wasm.getLocal context decl.fvarId =
      .ok (.localGet decl.fvarId, resultKind)) :
    ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? context.program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
  intro locals kind supported
  have effective := supportedLetDeclKind?_effectiveLetValueKind supported
  obtain ⟨metadata, targetExternal⟩ := targetExternal
  have targetResultKind :
      Fir.Wasm.abiKind? target.type = .ok (some resultKind) :=
    externalSignatureResultKind signature
  have compatible : resultKind.leanCompatible resultKind = true := by
    cases resultKind <;> decide
  have callEffective :
      Fir.Wasm.effectiveLetValueKind context.program decl =
        .ok resultKind := by
    unfold Fir.Wasm.effectiveLetValueKind
    rw [valueKind, valueEq]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [targetFound]
    simp [Fir.Wasm.effectiveDeclarationResultKind?, targetResultKind,
      targetExternal, compatible]
  have kindEq : resultKind = kind :=
    Except.ok.inj (callEffective.symm.trans effective)
  subst kind
  exact resultCompiled

/-- The admitted pure-external result families share the same exact named-call
destination theorem. -/
private theorem PureExternalSupported.resultCompiledForValidation
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value}
    {stepCost : Nat}
    (supported : PureExternalSupported context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue stepCost) :
    ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? context.program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
  rcases supported with integer | natural | scalar
  · rcases integer with
      ⟨name, args, _argumentCode, argumentKinds, _semanticArgs, target,
        _value, valueEq, _operation, _nonempty, targetFound, targetExternal,
        valueKind, _argumentsCompiled, _argumentsEvaluated, signature,
        resultCompiled, _semanticCalled, _nextRuntimeEq, _sourceValueEq,
        _stepCostEq⟩
    exact externalNamedResultCompiledForValidation valueEq targetFound
      targetExternal valueKind signature resultCompiled
  · rcases natural with
      ⟨name, args, _argumentCode, argumentKinds, _semanticArgs, target,
        _value, valueEq, _operation, _nonempty, targetFound, targetExternal,
        valueKind, _argumentsCompiled, _argumentsEvaluated, signature,
        resultCompiled, _semanticCalled, _nextRuntimeEq, _sourceValueEq,
        _stepCostEq⟩
    exact externalNamedResultCompiledForValidation valueEq targetFound
      targetExternal valueKind signature resultCompiled
  · rcases scalar with
      ⟨name, args, _argumentCode, argumentKinds, _semanticArgs, target,
        _value, valueEq, _operation, _nonempty, targetFound, targetExternal,
        valueKind, _argumentsCompiled, _argumentsEvaluated, signature,
        resultCompiled, _semanticCalled, _nextRuntimeEq, _sourceValueEq,
        _stepCostEq⟩
    exact externalNamedResultCompiledForValidation valueEq targetFound
      targetExternal valueKind signature resultCompiled

/-- Any compiler/resource successor of a validated direct `let` continuation
inherits the exact residual validator state, even when the concrete operation
changes heap facts, remaining address-space budget, or refinement witness. -/
theorem ConcreteStructuredValidatedCodeCoreRel.letSuccessor
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore nextStore : Wasm.Store Host}
    {entryWitness witness nextWitness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts nextFacts : ReuseCapacityFacts}
    {remainingBytes nextRemainingBytes : Nat}
    {sourceEnv nextEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals nextLocals : Wasm.Locals}
    {targetCode nextTargetCode : Wasm.Program}
    {source nextSource : MachineState}
    {target nextTarget : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv (.let decl continuation) targetStore targetLocals
      targetCode witness source target)
    (compiled : ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind))
    (nextCore : ConcreteStructuredCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv continuation nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget) :
    ConcreteStructuredValidatedCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv continuation nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget := by
  obtain ⟨_kind, _locals, _kindFound, _resultCompiled, nextValidation⟩ :=
    related.validation.letContinuation compiled
  exact related.withSuccessor nextCore nextValidation

/-- A direct-value `let` is a fully closed transition.  Executable validation
supplies the exact residual local-kind and guarded-sharing update, current
admission comes from the source/compiler direct-value predicate, and the
existing concrete theorem reconstructs the dynamic runtime, heap facts,
remaining allocation budget, locals, witness, and positive target path. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_directLet_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (supported : ReuseBudgetedDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextRuntime sourceValue nextStore resumedLocals nextWitness
        nextFacts nextTargetCode targetCount,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult nextFacts
          (remainingBytes - directLetAllocationCost decl) nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation nextStore
          resumedLocals nextTargetCode nextWitness sourceAfter targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.directLet supported) budget
  obtain ⟨targetAfter, nextRuntime, sourceValue, nextStore, resumedLocals,
      nextWitness, nextFacts, nextTargetCode, targetCount, targetPath,
      targetPositive, sourceFramesEq, targetFramesEq, nextCore⟩ :=
    pointwise.advance_directLet_of_step spec supported rfl sourceStep
  have validatedCore := related.core.letSuccessor
    supported.resultCompiledForValidation nextCore
  exact ⟨targetAfter, nextRuntime, sourceValue, nextStore, resumedLocals,
    nextWitness, nextFacts, nextTargetCode, targetCount, targetPath,
    targetPositive,
    related.withSuccessor validatedCore sourceFramesEq targetFramesEq⟩

/-- A successful constructor/reuse direct binding advances the closed
validated relation and evolves the existential constructor schema in lockstep
with the exact successor witness. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_schemaChangingDirectLetSchemaStep_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (supported : SchemaChangingDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter targetCount,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
          targetModule hosts externals source sourceAfter schema targetAfter := by
  have broad := supported.toReuseBudgetedDirectSupported
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.directLet broad) budget
  obtain ⟨targetAfter, nextRuntime, sourceValue, nextStore, resumedLocals,
      nextWitness, nextFacts, nextSchema, nextTargetCode, targetCount,
      targetPath, targetPositive, sourceFramesEq, targetFramesEq, nextCore,
      schemaUpdate⟩ :=
    pointwise.advance_schemaChangingDirectLet_of_step spec schema supported rfl
      sourceStep
  have validatedCore := related.core.letSuccessor
    broad.resultCompiledForValidation nextCore
  have next :=
    related.withSuccessor validatedCore sourceFramesEq targetFramesEq
  have sourceShape :
      ConstructorSchema.DirectLetShapeAt source schema nextSchema := by
    refine ⟨context, decl, continuation,
      related.core.core.focus.sourceControlEq, ?_⟩
    simpa [related.core.core.focus.sourceRuntimeEq,
      related.core.core.focus.sourceEnvEq] using schemaUpdate.shape
  refine ⟨targetAfter, targetCount, targetPath, targetPositive, nextSchema,
    nextWitness, .directLet sourceStep sourceShape,
    schemaUpdate.agrees schemaAgrees, ?_⟩
  exact ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult next

/-- Compatibility projection of the transition-retaining constructor/reuse
successor to the established existential schema-global relation. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_schemaChangingDirectLetSchemaGlobal_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (supported : SchemaChangingDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter targetCount,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
  obtain ⟨targetAfter, targetCount, targetPath, targetPositive, next⟩ :=
    related.advance_schemaChangingDirectLetSchemaStep_of_step activeResult
      schemaAgrees supported budget sourceStep
  exact ⟨targetAfter, targetCount, targetPath, targetPositive,
    next.toSchemaGlobal⟩

/-- A successful schema-preserving direct binding advances the closed
validated relation under the current constructor schema.  Allocating literals
and boxes may extend the concrete refinement witness, so preservation is
transported through the runtime law's explicit monotone extension rather than
requiring witness equality. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_schemaPreservingDirectLetSchemaStep_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (supported : SchemaPreservingDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter targetCount,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
          targetModule hosts externals source sourceAfter schema targetAfter := by
  have broad := supported.toReuseBudgetedDirectSupported
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.directLet broad) budget
  obtain ⟨targetAfter, nextRuntime, sourceValue, nextStore, resumedLocals,
      nextWitness, nextFacts, nextTargetCode, targetCount, targetPath,
      targetPositive, sourceFramesEq, targetFramesEq, nextCore, extension⟩ :=
    pointwise.advance_schemaPreservingDirectLet_of_step spec supported rfl
      sourceStep
  have validatedCore := related.core.letSuccessor
    broad.resultCompiledForValidation nextCore
  have next :=
    related.withSuccessor validatedCore sourceFramesEq targetFramesEq
  have indexed :
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals nextWitness sourceAfter targetAfter :=
    ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult next
  have noShape : ¬ ∃ nextSchema,
      ConstructorSchema.DirectLetShapeAt source schema nextSchema := by
    rintro ⟨nextSchema, otherContext, otherDecl, otherContinuation,
      controlEq, shape⟩
    have codeEq :
        (Lean.Compiler.LCNF.Code.let decl continuation :
            Lean.Compiler.LCNF.Code .impure) =
          .let otherDecl otherContinuation :=
      related.core.core.focus.sourceControlEq.symm.trans controlEq
        |> Control.code.inj
    cases codeEq
    exact supported.noDirectLetShape shape
  exact ⟨targetAfter, targetCount, targetPath, targetPositive, schema,
    nextWitness, .preserved sourceStep noShape,
    schemaAgrees.witnessExtension extension, indexed⟩

/-- Compatibility projection of the transition-retaining monotone direct
successor to the established existential schema-global relation. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_schemaPreservingDirectLetSchemaGlobal_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (supported : SchemaPreservingDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter targetCount,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
  obtain ⟨targetAfter, targetCount, targetPath, targetPositive, next⟩ :=
    related.advance_schemaPreservingDirectLetSchemaStep_of_step activeResult
      schemaAgrees supported budget sourceStep
  exact ⟨targetAfter, targetCount, targetPath, targetPositive,
    next.toSchemaGlobal⟩

/-- Complete schema-global successor for the production direct-value family.
The compiler admission splits constructively into the constructor/reuse branch,
which computes a new schema, and the monotone-witness branch, which transports
the current schema unchanged. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_directLetSchemaStep_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (supported : ReuseBudgetedDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter targetCount,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
          targetModule hosts externals source sourceAfter schema targetAfter := by
  cases supported.schema_cases with
  | inl changing =>
      exact related.advance_schemaChangingDirectLetSchemaStep_of_step
        activeResult schemaAgrees changing budget sourceStep
  | inr preserving =>
      exact related.advance_schemaPreservingDirectLetSchemaStep_of_step
        activeResult schemaAgrees preserving budget sourceStep

/-- Compatibility projection of the complete transition-retaining direct
dispatcher. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_directLetSchemaGlobal_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (supported : ReuseBudgetedDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter targetCount,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
  obtain ⟨targetAfter, targetCount, targetPath, targetPositive, next⟩ :=
    related.advance_directLetSchemaStep_of_step activeResult schemaAgrees
      supported budget sourceStep
  exact ⟨targetAfter, targetCount, targetPath, targetPositive,
    next.toSchemaGlobal⟩

/-- Stage a compiler-generated named call inside the closed relation.  The
production pipeline selects the exact callee row, the concrete theorem runs
the argument prefix, and validation contributes only the caller continuation
that must survive the administrative ready state. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_directCall_stage_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {callerContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program callerContext callerCode
      sourceModule callerFunction targetModule hosts}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program callerContext
      callerCode sourceModule callerFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime callerEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (site : DirectInternalCallSite callerContext decl callerEnv)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ calleeContext calleeFunction,
      ∃ row : ConcreteGeneratedInternalDeclaration callerContext.program
        site.sourceDeclaration calleeContext site.calleeCode sourceModule
        calleeFunction targetModule,
      ∃ (physicalArgs : List Wasm.Value) (resultIndex : Nat)
          (targetArguments targetRest : Wasm.Program)
          (targetAfter : StructuredWasmState Host),
        FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
            targetArguments.length target targetAfter ∧
          ConcreteStructuredValidatedDirectCallReadyOutcome program
            callerContext calleeContext callerCode sourceModule callerFunction
            calleeFunction targetModule hosts spec site row externals labels
            entryRuntime entryStore entryWitness functionResult
            callerExpectedResult facts remainingBytes sourceRuntime continuation
            source.joins source.frames targetStore targetLocals
            targetLocals.values targetRest target.frames witness physicalArgs
            resultIndex sourceAfter targetAfter ∧
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.directCall site) (by omega)
  obtain ⟨calleeContext, calleeFunction, _contexts, ⟨generatedRow⟩⟩ :=
    pointwise.directCallRow site
  have row :
      ConcreteGeneratedInternalDeclaration callerContext.program
        site.sourceDeclaration calleeContext site.calleeCode sourceModule
        calleeFunction targetModule := by
    rw [spec.contextProgram]
    exact generatedRow
  obtain ⟨physicalArgs, resultIndex, targetArguments, targetRest,
      computedAfter, targetAfter, computedStep, targetPath, ready, rank⟩ :=
    related.core.core.advance_directCall_stage_ranked site row spec
  have sourceAfterEq : sourceAfter = computedAfter := by
    rw [sourceStep] at computedStep
    exact ExecResult.next.inj computedStep
  subst computedAfter
  have resultCompiled : ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind →
        Fir.Wasm.getLocal callerContext decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
    intro locals kind kindFound
    apply site.resultCompiledForValidation
    simpa only [spec.contextProgram] using kindFound
  obtain ⟨_kind, _locals, _kindFound, _resultCompiled,
      continuationValidation⟩ :=
    related.core.validation.letContinuation resultCompiled
  exact ⟨calleeContext, calleeFunction, row, physicalArgs, resultIndex,
    targetArguments, targetRest, targetAfter, targetPath,
    ⟨activeResult, related.contextCaches, ready, continuationValidation,
      related.frames, related.agrees, related.validationAgrees⟩,
    rank⟩

/-- Enter a staged named call and close the relation at the selected callee.
The accepted callee declaration reconstructs root validation; the ready state
pushes the previously validated caller continuation in lockstep with the
production call frame and hereditary resource stack. -/
theorem
    ConcreteStructuredValidatedDirectCallReadyOutcome.advance_enter_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program callerContext callerCode
      sourceModule callerFunction targetModule hosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedDirectCallReadyOutcome program
      callerContext calleeContext callerCode sourceModule callerFunction
      calleeFunction targetModule hosts spec site row externals labels
      entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime continuation callerJoins sourceFrames
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs resultIndex source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 1 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals witness sourceAfter targetAfter := by
  obtain ⟨targetAfter, targetPath, nextCore, callerScope, entry⟩ :=
    related.core.advance_enter_of_step (hostEnv := hosts.env)
      spec.contextProgram sourceStep
  have rowAtProgram :
      ConcreteGeneratedInternalDeclaration program site.sourceDeclaration
        calleeContext site.calleeCode sourceModule calleeFunction
        targetModule := by
    simpa only [spec.contextProgram] using row
  let calleeSpec :
      ConcreteSupportedFunction program calleeContext site.calleeCode
        sourceModule calleeFunction targetModule hosts :=
    rowAtProgram.toSupportedFunctionOfFunction spec
  have calleeResultAt :
      calleeSpec.sourceResultKind = site.calleeResultKind := by
    change rowAtProgram.sourceResultKind = site.calleeResultKind
    simpa [site.calleeResult] using rowAtProgram.sourceResultSelected.symm
  have validatedCore :
      ConcreteStructuredValidatedCodeCoreRel program calleeContext sourceModule
        calleeFunction externals [] sourceRuntime targetStore witness
        site.calleeResultKind (some site.calleeResultKind) [] remainingBytes
        sourceRuntime site.calleeEnv site.calleeCode targetStore
        (row.targetFunction.toLocals physicalArgs) row.targetFunction.body
        witness sourceAfter targetAfter :=
    nextCore.withRootValidation calleeSpec calleeResultAt
  let storedCallerLocals : Wasm.Locals :=
    { callerLocals with
      values := physicalArgs.reverse ++ callerRemainder }
  let pushedFrames :=
    ConcreteStructuredValidatedFrameStack.direct
      (callerEnv := callerEnv) (callerJoins := callerJoins)
      (callerLocals := storedCallerLocals)
      (callerRemainder := callerRemainder)
      (calleeResult := site.calleeResultKind)
      (kind := site.calleeResultKind) spec related.activeResult
      related.contextCaches entry.continuationAdapted entry.resultFound
      entry.resultKindAt (by simp [AbiKind.refines])
      related.continuationValidation related.frames
  let pushedResources :=
    ConcreteStructuredSuspendedResourceStack.direct
      (callerEnv := callerEnv) (callerJoins := callerJoins)
      (callerLocals := storedCallerLocals)
      (callerRemainder := callerRemainder)
      (calleeResult := site.calleeResultKind)
      (kind := site.calleeResultKind) callerScope
      spec.contextProgram.symm entry.continuationAdapted entry.resultFound
      entry.resultKindAt (by simp [AbiKind.refines])
      related.core.resources.suspended
  have pushedAgrees : pushedFrames.supported.Agrees pushedResources := by
    exact ConcreteStructuredSupportedFrameStack.Agrees.direct
      (calleeResult := site.calleeResultKind)
      (kind := site.calleeResultKind)
      spec related.activeResult related.contextCaches callerScope
      spec.contextProgram.symm entry.continuationAdapted entry.resultFound
      entry.resultKindAt (by simp [AbiKind.refines]) related.frames.supported
      related.core.resources.suspended related.agrees
  obtain ⟨callerSpine, callerValidationAgrees⟩ :=
    related.validationAgrees
  have pushedValidationAgrees :
      ConcreteStructuredValidationAgrees pushedAgrees
        pushedFrames.validation :=
    ⟨(functionResult, callerExpectedResult) :: callerSpine,
      .direct (callerJoins := callerJoins)
        (callerRemainder := callerRemainder) spec related.activeResult
        related.contextCaches callerScope spec.contextProgram.symm
        entry.continuationAdapted entry.resultFound entry.resultKindAt
        (by simp [AbiKind.refines]) related.continuationValidation
        callerValidationAgrees⟩
  obtain ⟨supportedAfter, agreesAfter⟩ := pushedAgrees.reindex
    entry.sourceFramesEq entry.targetFramesEq
    validatedCore.core.resources.suspended
  have validationAfter :
      ConcreteStructuredSuspendedValidation program site.calleeResultKind
        (some site.calleeResultKind) sourceAfter.frames := by
    rw [entry.sourceFramesEq]
    exact pushedFrames.validation
  have nextFrames :
      ConcreteStructuredValidatedFrameStack program sourceModule targetModule
        hosts site.calleeResultKind (some site.calleeResultKind)
        sourceAfter.frames targetAfter.frames :=
    ⟨supportedAfter, validationAfter⟩
  have nextValidationAgrees :
      ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
    pushedValidationAgrees.reindex entry.sourceFramesEq entry.targetFramesEq
      agreesAfter validationAfter
  have nextOutcome :
      ConcreteStructuredValidatedCodeOutcome program calleeContext
        site.calleeCode sourceModule calleeFunction targetModule hosts
        calleeSpec externals [] sourceRuntime targetStore witness
        site.calleeResultKind (some site.calleeResultKind) [] remainingBytes
        sourceRuntime site.calleeEnv site.calleeCode targetStore
        (row.targetFunction.toLocals physicalArgs) row.targetFunction.body
        witness sourceAfter targetAfter :=
    ⟨rowAtProgram.contextCaches, validatedCore, nextFrames, agreesAfter,
      nextValidationAgrees⟩
  exact ⟨targetAfter, targetPath,
    ConcreteStructuredValidatedCodeGlobalOutcomeAt.code calleeResultAt
      nextOutcome⟩

/-- Stage an exactly saturated closure call inside the closed relation.  The
source changes to closure invocation while the target remains at the generated
dispatcher, so the strict source-rank decrease discharges the zero-step side
condition. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_saturatedCall_stage_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context callerCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      callerCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime callerEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (site : SaturatedClosureCallSite context decl callerEnv)
    (resolution : SaturatedClosureCallResolution context sourceRuntime site)
    (sharedCapacity : ∀ parentRuntime,
      setCell sourceRuntime resolution.location
          { resolution.cell with rc := resolution.cell.rc - 1 } =
            .ok parentRuntime →
        ClosureRetainCapacity parentRuntime resolution.captures.toList)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ calleeContext calleeFunction,
      ∃ row : ConcreteGeneratedInternalDeclaration context.program
        resolution.target calleeContext resolution.calleeCode sourceModule
        calleeFunction targetModule,
      ∃ (targetValue targetRest : Wasm.Program) (resultIndex : Nat),
        FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 0
            target target ∧
          ConcreteStructuredValidatedSaturatedCallReadyOutcome program context
            calleeContext callerCode sourceModule sourceFunction calleeFunction
            targetModule hosts spec site resolution row externals labels
            entryRuntime entryStore entryWitness functionResult
            callerExpectedResult facts remainingBytes continuation source.joins
            source.frames targetStore targetLocals targetValue targetRest
            target.frames witness resultIndex sourceAfter target ∧
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.saturatedCall site resolution
      sharedCapacity)
    (by omega)
  obtain ⟨calleeContext, calleeFunction, _contexts, ⟨generatedRow⟩⟩ :=
    pointwise.saturatedCallRow resolution
  have row :
      ConcreteGeneratedInternalDeclaration context.program resolution.target
        calleeContext resolution.calleeCode sourceModule calleeFunction
        targetModule := by
    rw [spec.contextProgram]
    exact generatedRow
  obtain ⟨targetValue, targetRest, resultIndex, computedAfter, computedStep,
      targetPath, ready, rank⟩ :=
    related.core.core.advance_saturatedCall_stage site spec
  have sourceAfterEq : sourceAfter = computedAfter := by
    rw [sourceStep] at computedStep
    exact ExecResult.next.inj computedStep
  subst computedAfter
  obtain ⟨_kind, _locals, _kindFound, _resultCompiled,
      continuationValidation⟩ :=
    related.core.validation.letContinuation
      (site.resultCompiledForValidation (program := program))
  exact ⟨calleeContext, calleeFunction, row, targetValue, targetRest,
    resultIndex, targetPath,
    ⟨activeResult, related.contextCaches, sharedCapacity, ready,
      continuationValidation, related.frames, related.agrees,
      related.validationAgrees⟩,
    rank⟩

/-- Consume a staged saturated closure call and close the relation at its
selected generated callee.  Closure consumption may change the concrete store
and runtime, but root validation depends only on the accepted callee row; the
validated caller continuation follows the exact matcher/call frame protocol. -/
theorem
    ConcreteStructuredValidatedSaturatedCallReadyOutcome.advance_enter_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context calleeContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context callerCode sourceModule
      sourceFunction targetModule hosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : SaturatedClosureCallSite context decl callerEnv}
    {sourceRuntime : RuntimeState}
    {resolution : SaturatedClosureCallResolution context sourceRuntime site}
    {row : ConcreteGeneratedInternalDeclaration context.program
      resolution.target calleeContext resolution.calleeCode sourceModule
      calleeFunction targetModule}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {targetValue targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {resultIndex : Nat}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedSaturatedCallReadyOutcome program
      context calleeContext callerCode sourceModule sourceFunction
      calleeFunction targetModule hosts spec site resolution row externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes continuation callerJoins
      sourceFrames targetStore callerLocals targetValue targetRest targetFrames
      witness resultIndex source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals witness sourceAfter targetAfter := by
  obtain ⟨targetAfter, nextStore, physicalArgs, matcherCount, argumentCount,
      callRuntime, targetPath, nextCore, callerScope, entry⟩ :=
    related.core.advance_enter_of_step resolution row spec
      related.sharedCapacity sourceStep
  have rowAtProgram :
      ConcreteGeneratedInternalDeclaration program resolution.target
        calleeContext resolution.calleeCode sourceModule calleeFunction
        targetModule := by
    simpa only [spec.contextProgram] using row
  let calleeSpec :
      ConcreteSupportedFunction program calleeContext resolution.calleeCode
        sourceModule calleeFunction targetModule hosts :=
    rowAtProgram.toSupportedFunctionOfFunction spec
  have calleeResultAt :
      calleeSpec.sourceResultKind = resolution.targetResultKind := by
    change rowAtProgram.sourceResultKind = resolution.targetResultKind
    simpa [resolution.targetResult] using
      rowAtProgram.sourceResultSelected.symm
  have validatedCore :
      ConcreteStructuredValidatedCodeCoreRel program calleeContext sourceModule
        calleeFunction externals [] callRuntime nextStore witness
        resolution.targetResultKind (some site.resultKind) [] remainingBytes
        callRuntime resolution.calleeEnv resolution.calleeCode nextStore
        (row.targetFunction.toLocals physicalArgs) row.targetFunction.body
        witness sourceAfter targetAfter :=
    nextCore.withRootValidation calleeSpec calleeResultAt
  let savedCallerScope :=
    callerScope.withValues (physicalArgs.reverse ++ callerLocals.values)
  let pushedFrames :=
    ConcreteStructuredValidatedFrameStack.saturated
      (callerEnv := callerEnv) (callerJoins := callerJoins)
      (callerLocals := callerLocals) (physicalArgs := physicalArgs)
      (callerRemainder := callerLocals.values) (matcherCount := matcherCount)
      spec related.activeResult related.contextCaches
      entry.continuationAdapted entry.resultFound entry.resultKindAt
      resolution.targetResultRefines related.continuationValidation
      related.frames
  let pushedResources :=
    ConcreteStructuredSuspendedResourceStack.saturated
      (callerEnv := callerEnv) (callerJoins := callerJoins)
      (callerLocals := callerLocals) (physicalArgs := physicalArgs)
      (callerRemainder := callerLocals.values) (matcherCount := matcherCount)
      savedCallerScope spec.contextProgram.symm entry.continuationAdapted
      entry.resultFound entry.resultKindAt resolution.targetResultRefines
      related.core.resources.suspended
  have pushedAgrees : pushedFrames.supported.Agrees pushedResources := by
    exact ConcreteStructuredSupportedFrameStack.Agrees.saturated
      spec related.activeResult related.contextCaches savedCallerScope
      spec.contextProgram.symm entry.continuationAdapted entry.resultFound
      entry.resultKindAt resolution.targetResultRefines
      related.frames.supported related.core.resources.suspended related.agrees
  obtain ⟨callerSpine, callerValidationAgrees⟩ :=
    related.validationAgrees
  have pushedValidationAgrees :
      ConcreteStructuredValidationAgrees pushedAgrees
        pushedFrames.validation :=
    ⟨(functionResult, callerExpectedResult) :: callerSpine,
      .saturated (callerJoins := callerJoins) (matcherCount := matcherCount)
        spec related.activeResult related.contextCaches savedCallerScope
        spec.contextProgram.symm entry.continuationAdapted entry.resultFound
        entry.resultKindAt resolution.targetResultRefines
        related.continuationValidation callerValidationAgrees⟩
  obtain ⟨supportedAfter, agreesAfter⟩ := pushedAgrees.reindex
    entry.sourceFramesEq entry.targetFramesEq
    validatedCore.core.resources.suspended
  have validationAfter :
      ConcreteStructuredSuspendedValidation program
        resolution.targetResultKind (some site.resultKind)
        sourceAfter.frames := by
    rw [entry.sourceFramesEq]
    exact pushedFrames.validation
  have nextFrames :
      ConcreteStructuredValidatedFrameStack program sourceModule targetModule
        hosts resolution.targetResultKind (some site.resultKind)
        sourceAfter.frames targetAfter.frames :=
    ⟨supportedAfter, validationAfter⟩
  have nextValidationAgrees :
      ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
    pushedValidationAgrees.reindex entry.sourceFramesEq entry.targetFramesEq
      agreesAfter validationAfter
  have nextOutcome :
      ConcreteStructuredValidatedCodeOutcome program calleeContext
        resolution.calleeCode sourceModule calleeFunction targetModule hosts
        calleeSpec externals [] callRuntime nextStore witness
        resolution.targetResultKind (some site.resultKind) [] remainingBytes
        callRuntime resolution.calleeEnv resolution.calleeCode nextStore
        (row.targetFunction.toLocals physicalArgs) row.targetFunction.body
        witness sourceAfter targetAfter :=
    ⟨rowAtProgram.contextCaches, validatedCore, nextFrames, agreesAfter,
      nextValidationAgrees⟩
  refine ⟨3 * (matcherCount + 1) + argumentCount + 1, targetAfter,
    targetPath, ?_,
    ConcreteStructuredValidatedCodeGlobalOutcomeAt.code calleeResultAt
      nextOutcome⟩
  omega

/-- Stage a validated lazy-cache call while retaining the caller continuation
validation across the source-only invocation step. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_lazy_stage_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {callerEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {declaration : Lean.Name}
    {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec
      externals labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime callerEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (call : LazyCacheCallSupported context decl declaration sourceDeclaration
      resultKind)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    (path : ConcreteStructuredLazyReadyAdmission context sourceModule call
      generated sourceRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ cacheIndex declarationId cacheSetId resultIndex targetRest,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 0
          target target ∧
        ConcreteStructuredValidatedLazyCallReadyOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec call
          generated externals labels entryRuntime entryStore entryWitness
          functionResult callerExpectedResult facts remainingBytes sourceRuntime
          callerEnv continuation source.joins source.frames targetStore
          targetLocals targetRest target.frames witness cacheIndex declarationId
          cacheSetId resultIndex sourceAfter target ∧
        compilerStructuredControlRank sourceAfter <
          compilerStructuredControlRank source := by
  have admitted :
      ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime callerEnv 0
        (.let decl continuation) := by
    cases path with
    | hit sourceValue semanticFound =>
        exact .lazyHit call generated semanticFound
    | miss calleeCode internal resultClassified notObject notTObject
        semanticEmpty =>
        exact .lazyMiss internal generated resultClassified notObject notTObject
          semanticEmpty
  have pointwise := related.toPointwise admitted (by omega)
  obtain ⟨cacheIndex, declarationId, cacheSetId, resultIndex, targetRest,
      targetPath, ready, rank⟩ :=
    pointwise.advance_lazy_stage_of_step call generated sourceStep
  have resultCompiled : ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
    intro locals kind kindFound
    apply call.resultCompiledForValidation
    simpa only [spec.contextProgram] using kindFound
  obtain ⟨_kind, _locals, _kindFound, _resultCompiled,
      continuationValidation⟩ :=
    related.core.validation.letContinuation resultCompiled
  exact ⟨cacheIndex, declarationId, cacheSetId, resultIndex, targetRest,
    targetPath,
    ⟨activeResult, related.contextCaches, path, ready,
      continuationValidation, related.frames, related.agrees,
      related.validationAgrees⟩,
    rank⟩

/-- A populated lazy slot reaches the validated common bind boundary without
changing the caller's residual validation. -/
theorem
    ConcreteStructuredValidatedLazyCallReadyOutcome.advance_hit_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {declaration : Lean.Name}
    {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    {call : LazyCacheCallSupported context decl declaration sourceDeclaration
      resultKind}
    {generated : LazyCacheGeneratedEnvironment context sourceModule}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {callerEnv : Env}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {cacheIndex declarationId cacheSetId resultIndex : Nat}
    {sourceValue : Value}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedLazyCallReadyOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec call
      generated externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult facts remainingBytes sourceRuntime
      callerEnv continuation callerJoins sourceFrames targetStore callerLocals
      targetRest targetFrames witness cacheIndex declarationId cacheSetId
      resultIndex source target)
    (semanticFound :
      findGlobal? sourceRuntime.globals declaration = some sourceValue)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ physical targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 4
          target targetAfter ∧
        ConcreteStructuredValidatedExternalBindOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec
          externals labels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime callerEnv
          sourceValue decl.fvarId continuation callerJoins sourceFrames
          targetStore callerLocals callerLocals.values targetRest targetFrames
          witness resultKind physical resultIndex sourceAfter targetAfter := by
  obtain ⟨physical, targetAfter, targetPath, bindCore⟩ :=
    related.core.advance_hit_of_step semanticFound sourceStep
  have nextAgrees :
      related.frames.supported.Agrees bindCore.resources.suspended := by
    simpa using related.agrees
  have nextValidationAgrees :
      ConcreteStructuredValidationAgrees nextAgrees
        related.frames.validation := by
    obtain ⟨spine, aligned⟩ := related.validationAgrees
    exact ⟨spine, aligned⟩
  exact ⟨physical, targetAfter, targetPath,
    ⟨related.activeResult, related.contextCaches, bindCore,
      related.continuationValidation, related.frames, nextAgrees,
      nextValidationAgrees⟩⟩

/-- An empty lazy slot enters the generated initializer while preserving the
validated caller continuation in the exact cache-publication frame. -/
theorem
    ConcreteStructuredValidatedLazyCallReadyOutcome.advance_miss_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {declaration : Lean.Name}
    {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    {call : LazyCacheCallSupported context decl declaration sourceDeclaration
      resultKind}
    {generated : LazyCacheGeneratedEnvironment context sourceModule}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {callerEnv : Env}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {cacheIndex declarationId cacheSetId resultIndex : Nat}
    {calleeCode : Lean.Compiler.LCNF.Code .impure}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedLazyCallReadyOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec call
      generated externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult facts remainingBytes sourceRuntime
      callerEnv continuation callerJoins sourceFrames targetStore callerLocals
      targetRest targetFrames witness cacheIndex declarationId cacheSetId
      resultIndex source target)
    (internal : LazyCacheInternalMissSupported context decl declaration
      sourceDeclaration resultKind calleeCode)
    (resultClassified :
      Fir.Wasm.abiKind? sourceDeclaration.type = .ok (some resultKind))
    (notObject : resultKind ≠ .object)
    (notTObject : resultKind ≠ .tobject)
    (semanticEmpty :
      findGlobal? sourceRuntime.globals declaration = none)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3
          target targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals witness sourceAfter targetAfter := by
  obtain ⟨calleeContext, calleeFunction, row, targetAfter, targetPath,
      nextCore, sourceFramesEq, targetFramesEq⟩ :=
    related.core.advance_miss_of_step (functionCode := functionCode)
      (targetModule := targetModule) (hosts := hosts) (spec := spec)
      internal resultClassified notObject notTObject semanticEmpty
      related.contextCaches sourceStep
  let calleeSpec : ConcreteSupportedFunction program calleeContext calleeCode
      sourceModule calleeFunction targetModule hosts :=
    row.toSupportedFunctionOfFunction spec
  have calleeResultAt : calleeSpec.sourceResultKind = resultKind := by
    change row.sourceResultKind = resultKind
    simpa [call.effectiveResult] using row.sourceResultSelected.symm
  have validatedCore :
      ConcreteStructuredValidatedCodeCoreRel program calleeContext sourceModule
        calleeFunction externals [] sourceRuntime targetStore witness resultKind
        (some resultKind) [] remainingBytes sourceRuntime [] calleeCode
        targetStore (row.targetFunction.toLocals []) row.targetFunction.body
        witness sourceAfter targetAfter :=
    nextCore.withRootValidation calleeSpec calleeResultAt
  let pushedFrames :=
    ConcreteStructuredValidatedFrameStack.lazy
      (declaration := declaration) (callerEnv := callerEnv)
      (callerJoins := callerJoins) (callerLocals := callerLocals)
      (cacheIndex := cacheIndex) (cacheSetId := cacheSetId)
      (calleeResult := resultKind) (callerResult := functionResult)
      (kind := resultKind) (tailResult := callerExpectedResult)
      spec related.activeResult related.contextCaches
      related.core.ready.continuationAdapted related.core.ready.resultFound
      related.core.ready.resultKindAt related.core.ready.initializerFound
      related.core.ready.signature related.core.ready.cacheSetCall notObject
      notTObject (by cases resultKind <;> decide)
      related.continuationValidation related.frames
  let pushedResources :=
    ConcreteStructuredSuspendedResourceStack.lazy
      (declaration := declaration) (callerEnv := callerEnv)
      (callerJoins := callerJoins) (callerLocals := callerLocals)
      (cacheIndex := cacheIndex) (cacheSetId := cacheSetId)
      (calleeResult := resultKind) (callerResult := functionResult)
      (kind := resultKind) (tailResult := callerExpectedResult)
      related.core.resources.current spec.contextProgram.symm
      related.core.ready.continuationAdapted related.core.ready.resultFound
      related.core.ready.resultKindAt related.core.ready.initializerFound
      related.core.ready.signature related.core.ready.cacheSetCall notObject
      notTObject (by cases resultKind <;> decide)
      related.core.resources.suspended
  have pushedAgrees : pushedFrames.supported.Agrees pushedResources := by
    exact ConcreteStructuredSupportedFrameStack.Agrees.lazy
      spec related.activeResult related.contextCaches
      related.core.resources.current spec.contextProgram.symm
      related.core.ready.continuationAdapted related.core.ready.resultFound
      related.core.ready.resultKindAt related.core.ready.initializerFound
      related.core.ready.signature related.core.ready.cacheSetCall notObject
      notTObject (by cases resultKind <;> decide) related.frames.supported
      related.core.resources.suspended related.agrees
  obtain ⟨callerSpine, callerValidationAgrees⟩ :=
    related.validationAgrees
  have pushedValidationAgrees :
      ConcreteStructuredValidationAgrees pushedAgrees
        pushedFrames.validation :=
    ⟨(functionResult, callerExpectedResult) :: callerSpine,
      .lazy (callerJoins := callerJoins) (cacheIndex := cacheIndex)
        (cacheSetId := cacheSetId) spec related.activeResult
        related.contextCaches related.core.resources.current
        spec.contextProgram.symm related.core.ready.continuationAdapted
        related.core.ready.resultFound related.core.ready.resultKindAt
        related.core.ready.initializerFound related.core.ready.signature
        related.core.ready.cacheSetCall notObject notTObject
        (by cases resultKind <;> decide) related.continuationValidation
        callerValidationAgrees⟩
  obtain ⟨supportedAfter, agreesAfter⟩ := pushedAgrees.reindex
    sourceFramesEq targetFramesEq validatedCore.core.resources.suspended
  have validationAfter :
      ConcreteStructuredSuspendedValidation program resultKind
        (some resultKind) sourceAfter.frames := by
    rw [sourceFramesEq]
    exact pushedFrames.validation
  have nextFrames :
      ConcreteStructuredValidatedFrameStack program sourceModule targetModule
        hosts resultKind (some resultKind) sourceAfter.frames
        targetAfter.frames :=
    ⟨supportedAfter, validationAfter⟩
  have nextValidationAgrees :
      ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
    pushedValidationAgrees.reindex sourceFramesEq targetFramesEq agreesAfter
      validationAfter
  have nextOutcome :
      ConcreteStructuredValidatedCodeOutcome program calleeContext calleeCode
        sourceModule calleeFunction targetModule hosts calleeSpec externals []
        sourceRuntime targetStore witness resultKind (some resultKind) []
        remainingBytes sourceRuntime [] calleeCode targetStore
        (row.targetFunction.toLocals []) row.targetFunction.body witness
        sourceAfter targetAfter :=
    ⟨row.contextCaches, validatedCore, nextFrames, agreesAfter,
      nextValidationAgrees⟩
  exact ⟨targetAfter, targetPath,
    ConcreteStructuredValidatedCodeGlobalOutcomeAt.code calleeResultAt
      nextOutcome⟩

/-- Stage an admitted pure external while retaining precisely the validation
of its destination continuation and unchanged suspended caller stack.  Static
ABI admission and dynamic allocation budget remain separate premises. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_pureExternal_stage
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes stepCost : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (supported : PureExternalSupported context externals sourceRuntime sourceEnv
      decl continuation nextRuntime sourceValue stepCost)
    (budget : stepCost ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ (site : PureExternalCallShape context externals sourceRuntime sourceEnv
        decl nextRuntime sourceValue stepCost)
      (physicalArgs : List Wasm.Value) (operation : ExternalOperation)
      (resolvedResultKind : AbiKind) (targetImport : Wasm.ImportDecl)
      (callIndex resultIndex : Nat) (targetArguments targetRest : Wasm.Program)
      (targetAfter : StructuredWasmState Host),
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetArguments.length target targetAfter ∧
        ConcreteStructuredValidatedExternalCallReadyOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec
          externals site operation resolvedResultKind targetImport labels
          continuation source.joins source.frames entryRuntime entryStore
          entryWitness functionResult callerExpectedResult facts remainingBytes
          targetStore targetLocals targetLocals.values targetRest target.frames
          witness physicalArgs callIndex resultIndex sourceAfter targetAfter ∧
        compilerStructuredControlRank sourceAfter <
          compilerStructuredControlRank source := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.pureExternal supported) budget
  obtain ⟨site, physicalArgs, operation, resolvedResultKind, targetImport,
      callIndex, resultIndex, targetArguments, targetRest, targetAfter,
      targetPath, ready, rank⟩ :=
    pointwise.advance_pureExternal_stage_of_step supported rfl sourceStep
  have resultCompiled : ∀ {locals kind},
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind →
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind) := by
    intro locals kind kindFound
    apply supported.resultCompiledForValidation
    simpa only [spec.contextProgram] using kindFound
  obtain ⟨_kind, _locals, _kindFound, _resultCompiled,
      continuationValidation⟩ :=
    related.core.validation.letContinuation resultCompiled
  exact ⟨site, physicalArgs, operation, resolvedResultKind, targetImport,
    callIndex, resultIndex, targetArguments, targetRest, targetAfter,
    targetPath,
    ⟨activeResult, related.contextCaches, ready, continuationValidation,
      related.frames, related.agrees, related.validationAgrees⟩,
    rank⟩

/-- Execute the one resolved host call and close at the already-validated
common destination-bind boundary. -/
theorem ConcreteStructuredValidatedExternalCallReadyOutcome.advance_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {stepCost : Nat}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {site : PureExternalCallShape context externals sourceRuntime sourceEnv decl
      nextRuntime sourceValue stepCost}
    {operation : ExternalOperation}
    {resolvedResultKind : AbiKind}
    {targetImport : Wasm.ImportDecl}
    {labels : LabelContext}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {entryRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {physicalArgs : List Wasm.Value}
    {callIndex resultIndex : Nat}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedExternalCallReadyOutcome program
      context functionCode sourceModule sourceFunction targetModule hosts spec
      externals site operation resolvedResultKind targetImport labels
      continuation callerJoins sourceFrames entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs callIndex resultIndex source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ nextWitness targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 1
          target targetAfter ∧
        witness.Extends nextWitness ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals nextWitness sourceAfter targetAfter := by
  obtain ⟨nextStore, nextWitness, physicalResult, targetAfter, targetPath,
      witnessExtension, bindCore⟩ :=
    related.core.advance_of_step sourceStep
  have nextAgrees :
      related.frames.supported.Agrees bindCore.resources.suspended := by
    simpa using related.agrees
  have nextValidationAgrees :
      ConcreteStructuredValidationAgrees nextAgrees
        related.frames.validation := by
    obtain ⟨spine, aligned⟩ := related.validationAgrees
    exact ⟨spine, aligned⟩
  let bindValidated :
      ConcreteStructuredValidatedExternalBindOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec
        externals labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts (remainingBytes - stepCost) nextRuntime
        sourceEnv sourceValue decl.fvarId continuation callerJoins sourceFrames
        nextStore callerLocals callerRemainder targetRest targetFrames
        nextWitness site.resultKind physicalResult resultIndex sourceAfter
        targetAfter :=
    ⟨related.activeResult, related.contextCaches, bindCore,
      related.continuationValidation, related.frames, nextAgrees,
      nextValidationAgrees⟩
  exact ⟨nextWitness, targetAfter, targetPath, witnessExtension,
    ConcreteStructuredValidatedCodeGlobalOutcomeAt.externalBind bindValidated⟩

/-- Source-semantic safety of the currently active return, stated solely over
the source machine state and its active function result ABI.

The predicate is vacuous away from a return node.  At a return it says exactly
that the yielded source value has the representation promised by the active
function boundary.  In particular, a physically polymorphic `.tobject` local
returned as `.object` must denote a heap reference, while one returned as
`.tagged` must denote a tagged reference.  It mentions no target module,
physical lane, refinement witness, execution path, or compiler certificate. -/
def ConcreteStructuredReturnValueSafeAt
    (functionResult : AbiKind) (source : MachineState) : Prop :=
  ∀ {result : Lean.FVarId} {sourceValue : Value},
    source.control = .code (.return result) →
      lookup source.env result = some sourceValue →
        SemanticValueAtAbi functionResult sourceValue

/-- Use-site typing of the active return binding supplies the complete
source-only return-safety judgment.

This theorem deliberately asks for the function-result ABI at the use site.
Typing the binding only at a coarser compiler local such as `.tobject` would
not justify returning it through a precise `.object` or `.tagged` boundary. -/
theorem ConcreteStructuredReturnValueSafeAt.of_semanticBinding
    {functionResult : AbiKind} {source : MachineState}
    {result : Lean.FVarId}
    (control : source.control = .code (.return result))
    (typed : SemanticBindingAtAbi source.env result functionResult) :
    ConcreteStructuredReturnValueSafeAt functionResult source := by
  intro actual sourceValue actualControl found
  have codeEq :
      Lean.Compiler.LCNF.Code.return result =
        Lean.Compiler.LCNF.Code.return actual :=
    Control.code.inj (control.symm.trans actualControl)
  injection codeEq with resultEq
  subst actual
  exact typed found

/-- A validated, source-semantically typed return enters the closed yielded
branch without a separately supplied current-node admission object.

Residual production validation recovers the compiled local and its ordinary
object-family carrier compatibility.  `resultSemantic` is the independent
source typing/value-shape fact that makes a reverse object-family transfer
sound.  The concrete return theorem then canonicalizes the physical result at
the active function ABI, after which the existing suspended-resource stack
supplies the caller refinement. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_return_of_semantic_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.return result) targetStore targetLocals targetCode witness source target)
    (resultSemantic :
      ∀ {sourceValue}, lookup sourceEnv result = some sourceValue →
        SemanticValueAtAbi functionResult sourceValue)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
  obtain ⟨joins, locals, validationFacts, sharing, validated, localsAgree⟩ :=
    related.core.validation
  have validatedReturn := validated.supported
  obtain ⟨actualResult, localFound, _carrierCompatible⟩ :
      ∃ actualResult,
        Fir.Wasm.findLocalKind? locals result = some actualResult ∧
          actualResult.leanCompatible functionResult = true := by
    cases localFound : Fir.Wasm.findLocalKind? locals result with
    | none =>
        simp [Fir.Wasm.supportedCodeWithJoins, localFound] at validatedReturn
    | some actualResult =>
        exact ⟨actualResult, rfl, by
          simpa [Fir.Wasm.supportedCodeWithJoins, localFound] using
            validatedReturn⟩
  have resultCompiled :
      Fir.Wasm.getLocal context result =
        .ok (.localGet result, actualResult) :=
    localsAgree localFound
  obtain ⟨targetAfter, sourceValue, physical, targetPath, yielded,
      compatible, resources, sourceFramesEq, targetFramesEq⟩ :=
    related.core.core.advance_return_at_functionResult spec resultCompiled
      resultSemantic sourceStep
  obtain ⟨supportedAfter, agreesAfter⟩ := related.agrees.reindex
    sourceFramesEq targetFramesEq resources.suspended
  have validationAfter :
      ConcreteStructuredSuspendedValidation program functionResult
        callerExpectedResult sourceAfter.frames := by
    rw [sourceFramesEq]
    exact related.frames.validation
  have framesAfter :
      ConcreteStructuredValidatedFrameStack program sourceModule targetModule
        hosts functionResult callerExpectedResult sourceAfter.frames
        targetAfter.frames :=
    ⟨supportedAfter, validationAfter⟩
  have validationAgreesAfter :
      ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
    related.validationAgrees.reindex sourceFramesEq targetFramesEq agreesAfter
      validationAfter
  have returned :
      ConcreteStructuredValidatedReturnedOutcome program context functionCode
        sourceModule sourceFunction targetModule hosts spec externals labels
        entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        sourceValue targetStore targetLocals witness functionResult physical
        sourceAfter targetAfter :=
    ⟨activeResult, related.contextCaches, yielded, compatible, resources,
      framesAfter, agreesAfter, validationAgreesAfter⟩
  exact ⟨targetAfter, targetPath,
    ConcreteStructuredValidatedCodeGlobalOutcome.returned returned⟩

/-- State-indexed form of the validated return theorem.

This is the interface used by a module-wide dispatcher: source typing supplies
one invariant on the current machine state, while the structured compiler
relation recovers the active environment and return variable. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_return_of_source_safe_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.return result) targetStore targetLocals targetCode witness source target)
    (sourceSafe : ConcreteStructuredReturnValueSafeAt functionResult source)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
  apply related.advance_return_of_semantic_step activeResult
    (sourceStep := sourceStep)
  intro sourceValue sourceLookup
  apply sourceSafe related.core.core.focus.sourceControlEq
  simpa only [related.core.core.focus.sourceEnvEq] using sourceLookup

/-- A validated return enters the closed yielded branch at exactly the current
refinement witness. Current-node admission supplies only the compiled result
kind; the concrete theorem derives the semantic/physical result and both
machine paths, while suspended caller validation is transported across the
unchanged-frame equalities. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_returnAt_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.return result) targetStore targetLocals targetCode witness source target)
    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
      externals functionResult facts sourceRuntime sourceEnv 0
      (.return result))
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals witness sourceAfter targetAfter := by
  have pointwise := related.toPointwise admitted (by omega)
  obtain ⟨targetAfter, sourceValue, actualKind, physical, targetPath, yielded,
      compatible, resources, sourceFramesEq, targetFramesEq⟩ :=
    pointwise.advance_return spec sourceStep
  obtain ⟨supportedAfter, agreesAfter⟩ := related.agrees.reindex
    sourceFramesEq targetFramesEq resources.suspended
  have validationAfter :
      ConcreteStructuredSuspendedValidation program functionResult
        callerExpectedResult sourceAfter.frames := by
    rw [sourceFramesEq]
    exact related.frames.validation
  have framesAfter :
      ConcreteStructuredValidatedFrameStack program sourceModule targetModule
        hosts functionResult callerExpectedResult sourceAfter.frames
        targetAfter.frames :=
    ⟨supportedAfter, validationAfter⟩
  have validationAgreesAfter :
      ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
    related.validationAgrees.reindex sourceFramesEq targetFramesEq agreesAfter
      validationAfter
  have returned :
      ConcreteStructuredValidatedReturnedOutcome program context functionCode
        sourceModule sourceFunction targetModule hosts spec externals labels
        entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        sourceValue targetStore targetLocals witness actualKind physical
        sourceAfter targetAfter :=
    ⟨activeResult, related.contextCaches, yielded, compatible, resources,
      framesAfter, agreesAfter, validationAgreesAfter⟩
  exact ⟨targetAfter, targetPath,
    ConcreteStructuredValidatedCodeGlobalOutcomeAt.returned returned⟩

/-- Compatibility projection of the witness-indexed validated return. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_return_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.return result) targetStore targetLocals targetCode witness source target)
    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
      externals functionResult facts sourceRuntime sourceEnv 0
      (.return result))
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
  obtain ⟨targetAfter, targetPath, next⟩ :=
    related.advance_returnAt_of_step activeResult admitted sourceStep
  exact ⟨targetAfter, targetPath, next.toValidatedGlobal⟩

/-- Pop a yielded direct or saturated call back into its validated caller.
Target-only case labels may precede the call frame and are unwound first.  A
lazy cache marker is intentionally outside this theorem: cache publication is
a distinct administrative branch and will restore the same bind validation in
its own transition lemma. -/
theorem ConcreteStructuredValidatedReturnedOutcome.advance_bindCaller_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult actualKind : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceValue : Value}
    {targetLocals : Wasm.Locals}
    {physical : Wasm.Value}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedReturnedOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceValue targetStore targetLocals witness actualKind physical source
      target)
    (bindCaller : ConcreteStructuredBindCallerAtHead source.frames)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals witness sourceAfter targetAfter := by
  rcases related with ⟨_activeResult, _contextCaches, yielded, compatible,
    resources, frames, agrees, validationAgrees⟩
  generalize sourceFramesEq : source.frames = sourceFrames at resources frames agrees validationAgrees
  generalize targetFramesEq : target.frames = targetFrames at resources frames agrees validationAgrees
  rcases resources with ⟨currentScope, resourceStack⟩
  rcases frames with ⟨supported, validation⟩
  change supported.Agrees resourceStack at agrees
  change ConcreteStructuredValidationAgrees agrees validation at validationAgrees
  rcases validationAgrees with ⟨spine, aligned⟩
  induction aligned generalizing target with
  | @case spine _ _ _ _ _ sourceFrames targetFrames belowStack targetRest
      testCount supportedTail resourceTail tailAgrees validation tailAligned
      ih =>
      subst sourceFrames
      let targetPopped : StructuredWasmState Host := {
        store := targetStore
        control := .returning (physical :: targetLocals.values)
        frames := targetFrames }
      have unwindTarget :
          FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
            testCount target targetPopped := by
        rcases target with ⟨actualStore, actualControl, actualFrames⟩
        have storeEq := yielded.targetStoreEq
        change actualStore = targetStore at storeEq
        subst actualStore
        have controlEq := yielded.targetControlEq
        change actualControl = .returning (physical :: targetLocals.values)
          at controlEq
        subst actualControl
        change actualFrames = _ at targetFramesEq
        subst actualFrames
        simpa [targetPopped] using
          (structuredWasmReturnCaseLabelsFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (store := targetStore)
            (values := physical :: targetLocals.values)
            (belowStack := belowStack) (rest := targetRest)
            (frames := targetFrames) testCount)
      have yieldedPopped :
          ConcreteStructuredYieldFocus context sourceFunction sourceRuntime
            sourceEnv sourceValue targetStore targetLocals witness actualKind
            physical source targetPopped := {
        sourceProgramEq := yielded.sourceProgramEq
        sourceControlEq := yielded.sourceControlEq
        sourceEnvEq := yielded.sourceEnvEq
        sourceRuntimeEq := yielded.sourceRuntimeEq
        targetStoreEq := by simp [targetPopped]
        targetControlEq := by simp [targetPopped]
        stateRelated := yielded.stateRelated
        frameAligned := yielded.frameAligned
        valueRelated := yielded.valueRelated }
      obtain ⟨tailCount, targetAfter, tailPath, tailPositive, nextGlobal⟩ :=
        ih _activeResult yieldedPopped compatible (by rfl)
          (by simp [targetPopped]) currentScope
      exact ⟨testCount + tailCount, targetAfter,
        unwindTarget.trans tailPath, by omega, nextGlobal⟩
  | nil =>
      rcases bindCaller with
        ⟨result, continuation, callerEnv, callerJoins, tail, bindEq⟩
      rw [sourceFramesEq] at bindEq
      cases bindEq
  | @direct spine activeEntryRuntime callerEntryRuntime activeEntryStore
      callerEntryStore activeEntryWitness callerEntryWitness callerContext
      callerCode callerFunction callerLabels callerFacts callerBytes callerEnv
      callerLocals result continuation callerJoins sourceFrames
      callerRemainder targetRest targetFrames calleeResult callerResult kind
      resultIndex tailResult supportedTail resourceTail tailAgrees
      tailValidation callerSpec callerResultAt contextCaches callerScope
      programEq continuationAdapted resultFound kindAt calleeCompatible
      continuationValidation tailAligned _ih =>
        have callerStateRelated :
            StateRelated callerFunction sourceRuntime callerEnv targetStore
              callerLocals witness :=
          currentScope.transports.savedStateRelated callerScope.stateRelated
            currentScope.stateRelated
        have callerFrameAligned :
            ConcreteLocalFrameAligned callerFunction sourceRuntime callerEnv
              targetStore callerLocals witness := by
          simpa [ConcreteLocalFrameAligned] using callerScope.frameAligned
        let resumed : ConcreteStructuredBindFrameFocus callerContext sourceModule
            callerFunction callerLabels sourceRuntime callerEnv sourceValue result
            continuation callerJoins sourceFrames targetStore callerLocals
            callerRemainder targetRest targetFrames targetLocals.values witness
            kind physical resultIndex source target := {
          sourceProgramEq := yielded.sourceProgramEq.trans
            (spec.contextProgram.trans programEq)
          sourceControlEq := yielded.sourceControlEq
          sourceRuntimeEq := yielded.sourceRuntimeEq
          sourceFramesEq
          targetStoreEq := yielded.targetStoreEq
          targetControlEq := yielded.targetControlEq
          targetFramesEq
          continuationAdapted
          stateRelated := callerStateRelated
          frameAligned := callerFrameAligned
          resultFound
          kindAt
          valueRelated := yielded.valueRelated.ofRefines compatible }
        have resourceTailAtCaller :
            ConcreteStructuredSuspendedResourceStack externals
              callerContext.program callerEntryRuntime callerEntryStore
              callerEntryWitness callerResult tailResult sourceFrames
              targetFrames := by
          exact programEq ▸ resourceTail
        obtain ⟨computedAfter, targetAfter, resumedLocals, computedStep,
            targetPath, nextCore, sourceFramesAfter, targetFramesAfter⟩ :=
          resumed.advance_popCore (module := targetModule.wasmModule)
            (hostEnv := hosts.env) callerScope currentScope
            (spec.contextProgram.trans programEq) resourceTailAtCaller
        have sourceAfterEq : sourceAfter = computedAfter := by
          rw [sourceStep] at computedStep
          exact ExecResult.next.inj computedStep
        subst computedAfter
        have nextCoreAtProgram :
            ConcreteStructuredCodeCoreRel program callerContext sourceModule
              callerFunction externals callerLabels callerEntryRuntime
              callerEntryStore callerEntryWitness callerResult tailResult
              (eraseReuseCapacityFact callerFacts result) remainingBytes
              sourceRuntime (bind callerEnv result sourceValue) continuation
              targetStore resumedLocals targetRest witness sourceAfter
              targetAfter := by
          simpa only [programEq] using nextCore
        obtain ⟨supportedAfter, agreesAfter⟩ :=
          tailAgrees.reindex sourceFramesAfter targetFramesAfter
            nextCoreAtProgram.resources.suspended
        have validationAfter :
            ConcreteStructuredSuspendedValidation program callerResult
              tailResult sourceAfter.frames := by
          rw [sourceFramesAfter]
          exact tailValidation
        have validatedCore :
            ConcreteStructuredValidatedCodeCoreRel program callerContext
              sourceModule callerFunction externals callerLabels
              callerEntryRuntime callerEntryStore callerEntryWitness
              callerResult tailResult
              (eraseReuseCapacityFact callerFacts result) remainingBytes
              sourceRuntime (bind callerEnv result sourceValue) continuation
              targetStore resumedLocals targetRest witness sourceAfter
              targetAfter :=
          ⟨nextCoreAtProgram, continuationValidation⟩
        have validatedFrames :
            ConcreteStructuredValidatedFrameStack program sourceModule
              targetModule hosts callerResult tailResult sourceAfter.frames
              targetAfter.frames :=
          ⟨supportedAfter, validationAfter⟩
        have validationAgreesAfter :
            ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
          (show ConcreteStructuredValidationAgrees tailAgrees tailValidation
            from ⟨spine, tailAligned⟩).reindex sourceFramesAfter
              targetFramesAfter agreesAfter validationAfter
        let nextActive :
            ConcreteStructuredValidatedCodeOutcome program callerContext
              callerCode sourceModule callerFunction targetModule hosts
              callerSpec externals callerLabels callerEntryRuntime
              callerEntryStore callerEntryWitness callerResult tailResult
              (eraseReuseCapacityFact callerFacts result) remainingBytes
              sourceRuntime (bind callerEnv result sourceValue) continuation
              targetStore resumedLocals targetRest witness sourceAfter
              targetAfter :=
          ⟨contextCaches, validatedCore, validatedFrames, agreesAfter,
            validationAgreesAfter⟩
        exact ⟨2, targetAfter, targetPath, by omega,
          ConcreteStructuredValidatedCodeGlobalOutcomeAt.code callerResultAt
            nextActive⟩
  | @saturated spine activeEntryRuntime callerEntryRuntime activeEntryStore
      callerEntryStore activeEntryWitness callerEntryWitness callerContext
      callerCode callerFunction callerLabels callerFacts callerBytes callerEnv
      callerLocals result continuation callerJoins sourceFrames physicalArgs
      callerRemainder targetRest targetFrames calleeResult callerResult kind
      resultIndex matcherCount tailResult supportedTail resourceTail tailAgrees
      tailValidation callerSpec callerResultAt contextCaches callerScope
      programEq continuationAdapted resultFound kindAt calleeCompatible
      continuationValidation tailAligned _ih =>
        let savedCallerLocals : Wasm.Locals :=
          { callerLocals with
            values := physicalArgs.reverse ++ callerRemainder }
        have callerStateRelated :
            StateRelated callerFunction sourceRuntime callerEnv targetStore
              savedCallerLocals witness := by
          simpa [savedCallerLocals] using
            currentScope.transports.savedStateRelated callerScope.stateRelated
              currentScope.stateRelated
        have callerFrameAligned :
            ConcreteLocalFrameAligned callerFunction sourceRuntime callerEnv
              targetStore savedCallerLocals witness := by
          simpa [savedCallerLocals, ConcreteLocalFrameAligned] using
            callerScope.frameAligned
        let resumed : ConcreteStructuredSaturatedBindFrameFocus callerContext
            sourceModule callerFunction callerLabels sourceRuntime callerEnv
            sourceValue result continuation callerJoins sourceFrames targetStore
            savedCallerLocals targetLocals physicalArgs callerRemainder
            targetRest targetFrames witness kind physical resultIndex
            matcherCount source target := {
          sourceProgramEq := yielded.sourceProgramEq.trans
            (spec.contextProgram.trans programEq)
          sourceControlEq := yielded.sourceControlEq
          sourceRuntimeEq := yielded.sourceRuntimeEq
          sourceFramesEq
          targetStoreEq := yielded.targetStoreEq
          targetControlEq := yielded.targetControlEq
          targetFramesEq := by
            simpa [savedCallerLocals] using targetFramesEq
          continuationAdapted
          stateRelated := callerStateRelated
          frameAligned := callerFrameAligned
          resultFound
          kindAt
          valueRelated := yielded.valueRelated.ofRefines compatible }
        have callerScopeAtSaved :
            ConcreteStructuredResourceScope callerContext sourceModule
              callerFunction externals callerEntryRuntime callerEntryStore
              callerEntryWitness callerFacts callerBytes activeEntryRuntime
              callerEnv activeEntryStore
              { savedCallerLocals with
                values := physicalArgs.reverse ++ callerRemainder }
              activeEntryWitness := by
          simpa [savedCallerLocals] using callerScope
        have resourceTailAtCaller :
            ConcreteStructuredSuspendedResourceStack externals
              callerContext.program callerEntryRuntime callerEntryStore
              callerEntryWitness callerResult tailResult sourceFrames
              targetFrames := by
          exact programEq ▸ resourceTail
        obtain ⟨computedAfter, targetAfter, resumedLocals, computedStep,
            targetPath, nextCore, sourceFramesAfter, targetFramesAfter⟩ :=
          resumed.advance_popCore (module := targetModule.wasmModule)
            (hostEnv := hosts.env) callerScopeAtSaved currentScope
            (spec.contextProgram.trans programEq) resourceTailAtCaller
        have sourceAfterEq : sourceAfter = computedAfter := by
          rw [sourceStep] at computedStep
          exact ExecResult.next.inj computedStep
        subst computedAfter
        have nextCoreAtProgram :
            ConcreteStructuredCodeCoreRel program callerContext sourceModule
              callerFunction externals callerLabels callerEntryRuntime
              callerEntryStore callerEntryWitness callerResult tailResult
              (eraseReuseCapacityFact callerFacts result) remainingBytes
              sourceRuntime (bind callerEnv result sourceValue) continuation
              targetStore resumedLocals targetRest witness sourceAfter
              targetAfter := by
          simpa only [programEq] using nextCore
        obtain ⟨supportedAfter, agreesAfter⟩ :=
          tailAgrees.reindex sourceFramesAfter targetFramesAfter
            nextCoreAtProgram.resources.suspended
        have validationAfter :
            ConcreteStructuredSuspendedValidation program callerResult
              tailResult sourceAfter.frames := by
          rw [sourceFramesAfter]
          exact tailValidation
        have validatedCore :
            ConcreteStructuredValidatedCodeCoreRel program callerContext
              sourceModule callerFunction externals callerLabels
              callerEntryRuntime callerEntryStore callerEntryWitness
              callerResult tailResult
              (eraseReuseCapacityFact callerFacts result) remainingBytes
              sourceRuntime (bind callerEnv result sourceValue) continuation
              targetStore resumedLocals targetRest witness sourceAfter
              targetAfter :=
          ⟨nextCoreAtProgram, continuationValidation⟩
        have validatedFrames :
            ConcreteStructuredValidatedFrameStack program sourceModule
              targetModule hosts callerResult tailResult sourceAfter.frames
              targetAfter.frames :=
          ⟨supportedAfter, validationAfter⟩
        have validationAgreesAfter :
            ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
          (show ConcreteStructuredValidationAgrees tailAgrees tailValidation
            from ⟨spine, tailAligned⟩).reindex sourceFramesAfter
              targetFramesAfter agreesAfter validationAfter
        let nextActive :
            ConcreteStructuredValidatedCodeOutcome program callerContext
              callerCode sourceModule callerFunction targetModule hosts
              callerSpec externals callerLabels callerEntryRuntime
              callerEntryStore callerEntryWitness callerResult tailResult
              (eraseReuseCapacityFact callerFacts result) remainingBytes
              sourceRuntime (bind callerEnv result sourceValue) continuation
              targetStore resumedLocals targetRest witness sourceAfter
              targetAfter :=
          ⟨contextCaches, validatedCore, validatedFrames, agreesAfter,
            validationAgreesAfter⟩
        exact ⟨matcherCount + 5, targetAfter, targetPath, by omega,
          ConcreteStructuredValidatedCodeGlobalOutcomeAt.code callerResultAt
            nextActive⟩
  | @lazy spine activeEntryRuntime callerEntryRuntime activeEntryStore
      callerEntryStore activeEntryWitness callerEntryWitness callerContext
      callerCode callerFunction callerLabels callerFacts callerBytes callerEnv
      callerLocals declaration result continuation callerJoins sourceFrames
      targetRest targetFrames calleeResult callerResult kind cacheIndex
      cacheSetId resultIndex tailResult supportedTail resourceTail tailAgrees
      tailValidation callerSpec callerResultAt contextCaches callerScope
      programEq continuationAdapted resultFound kindAt initializerFound
      signature cacheSetCall notObject notTObject calleeCompatible
      continuationValidation tailAligned _ih =>
      rcases bindCaller with
        ⟨headResult, headContinuation, headEnv, headJoins, tail, bindEq⟩
      rw [sourceFramesEq] at bindEq
      cases bindEq

/-- Publish a yielded lazy value into its concrete cache and resume at the
validated external-bind boundary.  Target-only case labels may precede the
lazy call frame; publication itself is the established seven-step Wasm path.
The cache marker disappears, while validation of the caller continuation and
its hereditary tail is retained exactly. -/
theorem ConcreteStructuredValidatedReturnedOutcome.advance_lazyCache_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult actualKind : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceValue : Value}
    {targetLocals : Wasm.Locals}
    {physical : Wasm.Value}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedReturnedOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceValue targetStore targetLocals witness actualKind physical source
      target)
    (lazyCaller : ConcreteStructuredLazyCallerAtHead source.frames)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals witness sourceAfter targetAfter := by
  rcases related with ⟨activeResult, _contextCaches, yielded, compatible,
    resources, frames, agrees, validationAgrees⟩
  generalize sourceFramesEq : source.frames = sourceFrames at resources frames agrees validationAgrees
  generalize targetFramesEq : target.frames = targetFrames at resources frames agrees validationAgrees
  rcases resources with ⟨currentScope, resourceStack⟩
  rcases frames with ⟨supported, validation⟩
  change supported.Agrees resourceStack at agrees
  change ConcreteStructuredValidationAgrees agrees validation at validationAgrees
  rcases validationAgrees with ⟨spine, aligned⟩
  induction aligned generalizing target with
  | @case spine _ _ _ _ _ sourceFrames targetFrames belowStack targetRest
      testCount supportedTail resourceTail tailAgrees validation tailAligned
      ih =>
      subst sourceFrames
      let targetPopped : StructuredWasmState Host := {
        store := targetStore
        control := .returning (physical :: targetLocals.values)
        frames := targetFrames }
      have unwindTarget :
          FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
            testCount target targetPopped := by
        rcases target with ⟨actualStore, actualControl, actualFrames⟩
        have storeEq := yielded.targetStoreEq
        change actualStore = targetStore at storeEq
        subst actualStore
        have controlEq := yielded.targetControlEq
        change actualControl = .returning (physical :: targetLocals.values)
          at controlEq
        subst actualControl
        change actualFrames = _ at targetFramesEq
        subst actualFrames
        simpa [targetPopped] using
          (structuredWasmReturnCaseLabelsFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (store := targetStore)
            (values := physical :: targetLocals.values)
            (belowStack := belowStack) (rest := targetRest)
            (frames := targetFrames) testCount)
      have yieldedPopped :
          ConcreteStructuredYieldFocus context sourceFunction sourceRuntime
            sourceEnv sourceValue targetStore targetLocals witness actualKind
            physical source targetPopped := {
        sourceProgramEq := yielded.sourceProgramEq
        sourceControlEq := yielded.sourceControlEq
        sourceEnvEq := yielded.sourceEnvEq
        sourceRuntimeEq := yielded.sourceRuntimeEq
        targetStoreEq := by simp [targetPopped]
        targetControlEq := by simp [targetPopped]
        stateRelated := yielded.stateRelated
        frameAligned := yielded.frameAligned
        valueRelated := yielded.valueRelated }
      obtain ⟨tailCount, targetAfter, tailPath, tailPositive, nextGlobal⟩ :=
        ih activeResult yieldedPopped compatible (by rfl)
          (by simp [targetPopped]) currentScope
      exact ⟨testCount + tailCount, targetAfter,
        unwindTarget.trans tailPath, by omega, nextGlobal⟩
  | nil =>
      rcases lazyCaller with
        ⟨declaration, result, continuation, callerEnv, callerJoins, tail,
          lazyEq⟩
      rw [sourceFramesEq] at lazyEq
      cases lazyEq
  | @direct spine activeEntryRuntime callerEntryRuntime activeEntryStore
      callerEntryStore activeEntryWitness callerEntryWitness callerContext
      callerCode callerFunction callerLabels callerFacts callerBytes callerEnv
      callerLocals result continuation callerJoins sourceFrames
      callerRemainder targetRest targetFrames calleeResult callerResult kind
      resultIndex tailResult supportedTail resourceTail tailAgrees
      tailValidation callerSpec callerResultAt contextCaches callerScope
      programEq continuationAdapted resultFound kindAt calleeCompatible
      continuationValidation tailAligned _ih =>
      rcases lazyCaller with
        ⟨declaration, headResult, headContinuation, headEnv, headJoins, tail,
          lazyEq⟩
      rw [sourceFramesEq] at lazyEq
      cases lazyEq
  | @saturated spine activeEntryRuntime callerEntryRuntime activeEntryStore
      callerEntryStore activeEntryWitness callerEntryWitness callerContext
      callerCode callerFunction callerLabels callerFacts callerBytes callerEnv
      callerLocals result continuation callerJoins sourceFrames physicalArgs
      callerRemainder targetRest targetFrames calleeResult callerResult kind
      resultIndex matcherCount tailResult supportedTail resourceTail tailAgrees
      tailValidation callerSpec callerResultAt contextCaches callerScope
      programEq continuationAdapted resultFound kindAt calleeCompatible
      continuationValidation tailAligned _ih =>
      rcases lazyCaller with
        ⟨declaration, headResult, headContinuation, headEnv, headJoins, tail,
          lazyEq⟩
      rw [sourceFramesEq] at lazyEq
      cases lazyEq
  | @lazy spine activeEntryRuntime callerEntryRuntime activeEntryStore
      callerEntryStore activeEntryWitness callerEntryWitness callerContext
      callerCode callerFunction callerLabels callerFacts callerBytes callerEnv
      callerLocals declaration result continuation callerJoins sourceFrames
      targetRest targetFrames calleeResult callerResult kind cacheIndex
      cacheSetId resultIndex tailResult supportedTail resourceTail tailAgrees
      tailValidation callerSpec callerResultAt contextCaches callerScope
      programEq continuationAdapted resultFound kindAt initializerFound
      signature cacheSetCall notObject notTObject calleeCompatible
      continuationValidation tailAligned _ih =>
      have valueRelated :
          PhysicalValueRel witness kind physical sourceValue :=
        yielded.valueRelated.ofRefines compatible
      obtain ⟨cacheSlot, cacheFound, cacheKindEq⟩ :=
        currentScope.1.1.2.1.hostSlot initializerFound signature
      have cacheDescriptorsEq :
          targetStore.host.closureDescriptors = witness.closureDescriptors :=
        currentScope.1.1.1.2
      obtain ⟨runtimeAfter, operation, runtimeAfterRelated,
          _valueStillRelated, _mappedCapacity⟩ :=
        cacheSetStep_of_refines currentScope.stateRelated.1 valueRelated
          cacheFound cacheKindEq cacheDescriptorsEq
      let afterCache := replaceRuntime targetStore runtimeAfter
      have operationEq :
          cacheSetStep declaration kind targetStore [physical] =
            .Return [physical] afterCache := by
        simpa [afterCache] using operation
      obtain ⟨oldFlag, oldValue, flagBefore, valueBefore⟩ :=
        currentScope.1.1.2.1.slotLanesPresent initializerFound signature
      have valueAfterCache :
          afterCache.globals.globals[2 * cacheIndex + 1]? = some oldValue := by
        rw [cacheSetStep_preserves_wasmGlobals operationEq]
        exact valueBefore
      have flagAfterCache :
          afterCache.globals.globals[2 * cacheIndex]? = some oldFlag := by
        rw [cacheSetStep_preserves_wasmGlobals operationEq]
        exact flagBefore
      let valueStore :=
        writeWasmGlobal afterCache (2 * cacheIndex + 1) physical
      have valueStoreEq :
          valueStore =
            writeWasmGlobal afterCache (2 * cacheIndex + 1) physical := rfl
      have flagAfterValue :
          valueStore.globals.globals[2 * cacheIndex]? = some oldFlag := by
        rw [valueStoreEq, writeWasmGlobal_get_ne (by omega)]
        exact flagAfterCache
      let nextStore :=
        writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)
      let nextRuntime := sourceRuntime.setGlobal declaration sourceValue
      let sourcePublished : MachineState := {
        source with
          runtime := nextRuntime
          frames :=
            .bind result continuation callerEnv callerJoins :: sourceFrames }
      have computedStep :
          executeStep externals source = .next sourcePublished := by
        rcases source with
          ⟨sourceProgram, sourceControl, stateEnv, stateJoins, stateFrames,
            stateRuntime⟩
        have controlEq := yielded.sourceControlEq
        change sourceControl = .yielded sourceValue at controlEq
        subst sourceControl
        have runtimeEq := yielded.sourceRuntimeEq
        change stateRuntime = sourceRuntime at runtimeEq
        subst stateRuntime
        change stateFrames = _ at sourceFramesEq
        subst stateFrames
        simp [sourcePublished, nextRuntime, executeStep, coreStep]
      have sourceAfterEq : sourceAfter = sourcePublished := by
        rw [sourceStep] at computedStep
        exact ExecResult.next.inj computedStep
      obtain ⟨imp, importFound, importInBounds, contractFound,
          parameterCount, resultCount⟩ :=
        callerSpec.cacheSetCall cacheSetCall
      let targetAfter : StructuredWasmState Host := {
        store := nextStore
        control := .running
          { callerLocals with
            values := physical :: callerLocals.values }
          (.localSet resultIndex :: targetRest)
        frames := targetFrames }
      have targetPath :
          FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 7
            target targetAfter := by
        rcases target with ⟨stateStore, stateControl, stateFrames⟩
        have storeEq := yielded.targetStoreEq
        change stateStore = targetStore at storeEq
        subst stateStore
        have controlEq := yielded.targetControlEq
        change stateControl = .returning (physical :: targetLocals.values)
          at controlEq
        subst stateControl
        change stateFrames = _ at targetFramesEq
        subst stateFrames
        simpa [targetAfter, nextStore] using
          structuredWasmLazyMissPublicationFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (spec := hosts.spec) (cacheSetId := cacheSetId) (imp := imp)
            (declaration := declaration) (kind := kind)
            (afterCall := targetStore) (afterCache := afterCache)
            (valueStore := valueStore) (callerLocals := callerLocals)
            (calleeLocals := targetLocals) (physical := physical)
            (oldValue := oldValue) (oldFlag := oldFlag)
            (flagIndex := 2 * cacheIndex)
            (valueIndex := 2 * cacheIndex + 1)
            (resultIndex := resultIndex) (rest := targetRest)
            (frames := targetFrames) callerLocals.values importFound
            callerSpec.hostsSatisfy importInBounds contractFound
            parameterCount resultCount operationEq valueAfterCache valueStoreEq
            flagAfterValue (by omega)
      have callerStateAtCurrent :
          StateRelated callerFunction sourceRuntime callerEnv targetStore
            callerLocals witness :=
        currentScope.transports.savedStateRelated callerScope.stateRelated
          currentScope.stateRelated
      have nextStateRelated :
          StateRelated callerFunction nextRuntime callerEnv nextStore
            callerLocals witness := by
        refine ⟨?_, ?_, callerStateAtCurrent.2.2⟩
        · simpa [nextRuntime, nextStore, valueStore, afterCache,
            writeWasmGlobal] using runtimeAfterRelated
        · simp [nextStore, valueStore, afterCache, writeWasmGlobal,
            replaceRuntime, clearFailure]
      have nonHeap : IsNonHeapReference sourceValue :=
        valueRelated.isNonHeapReference_of_kind notObject notTObject
      have publicationOrdinary :
          OrdinaryPersistenceTransport sourceRuntime nextRuntime := by
        apply (OrdinaryPersistenceTransport.refl sourceRuntime).congrAfter
        rw [show nextRuntime = sourceRuntime.setGlobal declaration sourceValue
          by rfl]
        exact
          (RuntimeState.setGlobal_heap_eq_of_nonHeapReference sourceRuntime
            declaration sourceValue nonHeap).symm
      have publicationCapacity :
          HeaderCapacityTransport targetStore.host.runtime.heap
            nextStore.host.runtime.heap witness := by
        simpa [nextStore, writeWasmGlobal, valueStoreEq] using
          cacheSetStep_preserves_mappedHeaderCapacity_of_related
            currentScope.stateRelated.1 valueRelated cacheFound cacheKindEq
            cacheDescriptorsEq operationEq
      have nextReuseRelated :
          ReuseCapacityStateRelated callerFacts callerFunction nextRuntime
            callerEnv nextStore callerLocals witness := by
        have callerAtCurrent :
            ReuseCapacityStateRelated callerFacts callerFunction sourceRuntime
              callerEnv targetStore callerLocals witness :=
          callerScope.1.1.1.1.1.1.transport callerStateAtCurrent
            currentScope.transports.witness currentScope.transports.capacity
        exact callerAtCurrent.transport nextStateRelated
          (WitnessTransport.refl witness) publicationCapacity
      have nextOrdinary :
          ReuseTokenOrdinaryRel callerFacts nextRuntime callerEnv :=
        (callerScope.1.1.1.1.1.2.1.transport
          currentScope.transports.ordinary).transport publicationOrdinary
      have nextAligned :
          ConcreteLocalFrameAligned callerFunction nextRuntime callerEnv
            nextStore callerLocals witness := by
        simpa [ConcreteLocalFrameAligned] using callerScope.frameAligned
      have nextBudget :
          nextStore.host.runtime.heap.AddressSpaceBudget remainingBytes := by
        simpa [nextStore] using
          cachePublication_preserves_addressSpaceBudget operationEq valueStoreEq
            currentScope.1.1.1.1.1.2.2.2
      have publicationExternals :
          nextStore.host.externals = targetStore.host.externals := by
        simp [nextStore, valueStore, afterCache, writeWasmGlobal,
          replaceRuntime, clearFailure]
      have publicationDescriptors :
          nextStore.host.closureDescriptors =
            targetStore.host.closureDescriptors := by
        simp [nextStore, valueStore, afterCache, writeWasmGlobal,
          replaceRuntime, clearFailure]
      have publicationDispatch :
          nextStore.host.closureDispatch = targetStore.host.closureDispatch := by
        simp [nextStore, valueStore, afterCache, writeWasmGlobal,
          replaceRuntime, clearFailure]
      have nextInteger :
          nextStore.host.externals.IntegerResultRefines externals := by
        rw [publicationExternals, currentScope.transports.externals]
        exact callerScope.1.1.1.1.2.1
      have nextNatural :
          FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
            nextStore.host.externals externals := by
        rw [publicationExternals, currentScope.transports.externals]
        exact callerScope.1.1.1.1.2.2.1
      have nextScalar :
          FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
            nextStore.host.externals externals := by
        rw [publicationExternals, currentScope.transports.externals]
        exact callerScope.1.1.1.1.2.2.2
      have nextDescriptors :
          nextStore.host.closureDescriptors = witness.closureDescriptors :=
        publicationDescriptors.trans cacheDescriptorsEq
      have nextCache :
          LazyCacheGlobalsRel witness sourceModule nextRuntime nextStore := by
        have afterHost := currentScope.1.1.2.1.afterCacheSet operationEq
        simpa [nextRuntime, nextStore] using
          afterHost.publish initializerFound signature rfl valueRelated
            valueStoreEq
      have nextClosureTables : ClosureTablesAgree nextStore witness := {
        dispatch :=
          currentScope.1.1.2.2.dispatch.trans publicationDispatch.symm
        descriptors :=
          publicationDescriptors.trans currentScope.1.1.2.2.descriptors }
      have nextBase :
          ConcreteReuseCapacityFrame callerFunction callerFacts remainingBytes
            nextRuntime callerEnv nextStore callerLocals witness :=
        ⟨nextReuseRelated, nextOrdinary, nextAligned, nextBudget⟩
      have nextPure :
          ConcreteReuseCapacityPureExternalFrame callerFunction externals
            callerFacts remainingBytes nextRuntime callerEnv nextStore
            callerLocals witness :=
        ⟨nextBase, nextInteger, nextNatural, nextScalar⟩
      have nextOwnership :
          ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction
            externals callerFacts remainingBytes nextRuntime callerEnv nextStore
            callerLocals witness :=
        ⟨nextPure, nextDescriptors⟩
      have nextFrame :
          ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
            callerFacts remainingBytes nextRuntime callerEnv nextStore
            callerLocals witness :=
        ⟨nextOwnership, nextCache, nextClosureTables⟩
      have publicationTables :
          ClosureTablesTransport targetStore nextStore witness witness := {
        hostDispatchPreserved := publicationDispatch
        witnessDispatchPreserved := rfl
        hostDescriptorsPreserved := publicationDescriptors
        witnessDescriptorsPreserved := rfl }
      have activeToNext :
          ReuseCapacityCodeEntryTransports activeEntryRuntime nextRuntime
            activeEntryStore nextStore activeEntryWitness witness :=
        currentScope.transports.step (WitnessTransport.refl witness)
          (ClosureAllocationsPersistent.refl witness) publicationCapacity
          publicationOrdinary publicationExternals publicationTables
      have nextEntry :
          ReuseCapacityCodeEntryTransports callerEntryRuntime nextRuntime
            callerEntryStore nextStore callerEntryWitness witness :=
        callerScope.transports.step activeToNext.witness
          activeToNext.closureAllocationsPersistent activeToNext.capacity
          activeToNext.ordinary activeToNext.externals
          activeToNext.toClosureTablesTransport
      have nextAbi :
          ClosureAllocationsAbiAligned callerContext.program witness := by
        rw [← programEq, ← spec.contextProgram]
        exact currentScope.2
      have nextScope :
          ConcreteStructuredResourceScope callerContext sourceModule
            callerFunction externals callerEntryRuntime callerEntryStore
            callerEntryWitness callerFacts remainingBytes nextRuntime callerEnv
            nextStore callerLocals witness :=
        ⟨⟨nextFrame, nextEntry⟩, nextAbi⟩
      have bindFocus :
          ConcreteStructuredExternalBindFocus callerContext sourceModule
            callerFunction callerLabels nextRuntime callerEnv sourceValue result
            continuation callerJoins sourceFrames nextStore callerLocals
            callerLocals.values targetRest targetFrames witness kind physical
            resultIndex sourceAfter targetAfter := {
        sourceProgramEq := by
          rw [sourceAfterEq]
          exact yielded.sourceProgramEq.trans
            (spec.contextProgram.trans programEq)
        sourceControlEq := by
          rw [sourceAfterEq]
          simpa [sourcePublished] using yielded.sourceControlEq
        sourceRuntimeEq := by simp [sourceAfterEq, sourcePublished]
        sourceFramesEq := by simp [sourceAfterEq, sourcePublished]
        targetStoreEq := by simp [targetAfter]
        targetControlEq := by simp [targetAfter]
        targetFramesEq := by simp [targetAfter]
        continuationAdapted
        stateRelated := nextStateRelated
        frameAligned := nextAligned
        resultFound
        kindAt
        valueRelated }
      have nextResources :
          ConcreteStructuredResourceStack program callerContext sourceModule
            callerFunction externals callerEntryRuntime nextRuntime
            callerEntryStore nextStore callerEntryWitness witness callerFacts
            remainingBytes callerEnv callerLocals callerResult tailResult
            sourceFrames targetFrames :=
        ⟨nextScope, resourceTail⟩
      have nextAgrees : supportedTail.Agrees nextResources.suspended := by
        simpa using tailAgrees
      let bindCore :
          ConcreteStructuredExternalBindCoreRel program callerContext
            sourceModule callerFunction externals callerLabels callerEntryRuntime
            callerEntryStore callerEntryWitness callerResult tailResult
            callerFacts remainingBytes nextRuntime callerEnv sourceValue result
            continuation callerJoins sourceFrames nextStore callerLocals
            callerLocals.values targetRest targetFrames witness kind physical
            resultIndex sourceAfter targetAfter :=
        ⟨bindFocus, nextResources⟩
      let validatedFrames :
          ConcreteStructuredValidatedFrameStack program sourceModule
            targetModule hosts callerResult tailResult sourceFrames
            targetFrames :=
        ⟨supportedTail, tailValidation⟩
      have nextValidationAgrees :
          ConcreteStructuredValidationAgrees nextAgrees
            validatedFrames.validation := by
        simpa [validatedFrames] using
          (show ConcreteStructuredValidationAgrees tailAgrees tailValidation
            from ⟨spine, tailAligned⟩)
      let bindValidated :
          ConcreteStructuredValidatedExternalBindOutcome program callerContext
            callerCode sourceModule callerFunction targetModule hosts callerSpec
            externals callerLabels callerEntryRuntime callerEntryStore
            callerEntryWitness callerResult tailResult callerFacts
            remainingBytes nextRuntime callerEnv sourceValue result continuation
            callerJoins sourceFrames nextStore callerLocals callerLocals.values
            targetRest targetFrames witness kind physical resultIndex sourceAfter
            targetAfter :=
        ⟨callerResultAt, contextCaches, bindCore, continuationValidation,
          validatedFrames, nextAgrees, nextValidationAgrees⟩
      exact ⟨7, targetAfter, targetPath, by omega,
        ConcreteStructuredValidatedCodeGlobalOutcomeAt.externalBind
          bindValidated⟩

/-- Constructor-complete pop for a validated yielded state.

The suspended validation stack itself classifies the source caller head.  A
plain bind resumes a direct or saturated caller, a cache marker publishes a
lazy result first, and the empty stack is incompatible with a successful
source successor.  This avoids forgetting validation merely to reuse the
older supported-stack dispatcher. -/
theorem ConcreteStructuredValidatedReturnedOutcome.advance_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult actualKind : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceValue : Value}
    {targetLocals : Wasm.Locals}
    {physical : Wasm.Value}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedReturnedOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceValue targetStore targetLocals witness actualKind physical source
      target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals witness sourceAfter targetAfter := by
  generalize sourceFramesEq : source.frames = sourceFrames
  have validationAt :
      ConcreteStructuredSuspendedValidation program functionResult
        callerExpectedResult sourceFrames := by
    rw [← sourceFramesEq]
    exact related.frames.validation
  cases validationAt with
  | nil =>
      rcases source with
        ⟨sourceProgram, sourceControl, stateEnv, stateJoins, stateFrames,
          runtime⟩
      have controlEq := related.yielded.sourceControlEq
      change sourceControl = .yielded sourceValue at controlEq
      subst sourceControl
      change stateFrames = [] at sourceFramesEq
      subst stateFrames
      simp [executeStep, coreStep] at sourceStep
  | bind continuationValidation tail =>
      apply related.advance_bindCaller_of_step
        (bindCaller := ⟨_, _, _, _, _, sourceFramesEq⟩) sourceStep
  | lazy continuationValidation tail =>
      apply related.advance_lazyCache_of_step
        (lazyCaller := ⟨_, _, _, _, _, _, sourceFramesEq⟩) sourceStep

/-- Complete the pending generated destination write and return from the
validated external-bind boundary to ordinary validated compiler code.  The
source bind and target `local.set` each take one step; only the destination's
reuse fact is erased, while the validated caller tail is transported across
the exact frame equalities supplied by the production core theorem. -/
theorem ConcreteStructuredValidatedExternalBindOutcome.advance_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {callerEnv : Env}
    {sourceValue : Value}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedExternalBindOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec
      externals labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime callerEnv
      sourceValue result continuation callerJoins sourceFrames targetStore
      callerLocals callerRemainder targetRest targetFrames witness kind physical
      resultIndex source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 1
          target targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals witness sourceAfter targetAfter := by
  obtain ⟨targetAfter, resumedLocals, targetPath, nextCore, sourceFramesEq,
      targetFramesEq⟩ :=
    related.core.advance_of_step (targetModule := targetModule) (hosts := hosts)
      sourceStep
  obtain ⟨supportedAfter, agreesAfter⟩ :=
    related.agrees.reindex sourceFramesEq targetFramesEq
      nextCore.resources.suspended
  have validationAfter :
      ConcreteStructuredSuspendedValidation program functionResult
        callerExpectedResult sourceAfter.frames := by
    rw [sourceFramesEq]
    exact related.frames.validation
  have validationAgreesAfter :
      ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
    related.validationAgrees.reindex sourceFramesEq targetFramesEq agreesAfter
      validationAfter
  let validatedCore :
      ConcreteStructuredValidatedCodeCoreRel program context sourceModule
        sourceFunction externals labels entryRuntime entryStore entryWitness
        functionResult callerExpectedResult (eraseReuseCapacityFact facts result)
        remainingBytes sourceRuntime (bind callerEnv result sourceValue)
        continuation targetStore resumedLocals targetRest witness sourceAfter
        targetAfter :=
    ⟨nextCore, related.continuationValidation⟩
  let validatedFrames :
      ConcreteStructuredValidatedFrameStack program sourceModule targetModule
        hosts functionResult callerExpectedResult sourceAfter.frames
        targetAfter.frames :=
    ⟨supportedAfter, validationAfter⟩
  let nextActive :
      ConcreteStructuredValidatedCodeOutcome program context functionCode
        sourceModule sourceFunction targetModule hosts spec externals labels
        entryRuntime entryStore entryWitness functionResult
        callerExpectedResult (eraseReuseCapacityFact facts result)
        remainingBytes sourceRuntime (bind callerEnv result sourceValue)
        continuation targetStore resumedLocals targetRest witness sourceAfter
        targetAfter :=
    ⟨related.contextCaches, validatedCore, validatedFrames, agreesAfter,
      validationAgreesAfter⟩
  exact ⟨targetAfter, targetPath,
    ConcreteStructuredValidatedCodeGlobalOutcomeAt.code related.activeResult
      nextActive⟩

/-- Persistent ownership increments are erased by lowering and preserve the
complete residual validator state. -/
theorem ConcreteStructuredValidationFocus.incPersistent
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.inc objectId amount check true continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  exact ⟨by simpa using supported⟩

/-- Persistent ownership decrements preserve the same residual validator
state. -/
theorem ConcreteStructuredValidationFocus.decPersistent
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.dec objectId amount check true objectFields? continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  exact ⟨by simpa using supported⟩

/-- Persistent increments are a complete current-step admission case.  The
source operation remains visible, but production lowering erases it and the
admission judgment therefore needs no heap, target, or allocation premise. -/
theorem ConcreteStructuredAlignedValidationState.admit_incPersistent
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : Fir.Wasm.AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (_validated : ConcreteStructuredAlignedValidationState program context
      expectedResult (.inc objectId amount check true continuation)) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.inc objectId amount check true continuation) := by
  exact .incPersistent

/-- Persistent decrements are likewise admitted directly from the current
validated node.  Recursive release is absent by construction because the
persistent flag makes this source-visible operation compiler-erased. -/
theorem ConcreteStructuredAlignedValidationState.admit_decPersistent
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : Fir.Wasm.AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (_validated : ConcreteStructuredAlignedValidationState program context
      expectedResult
      (.dec objectId amount check true objectFields? continuation)) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.dec objectId amount check true objectFields? continuation) := by
  exact .decPersistent

/-- Validation of an ordinary decrement exposes the exact object-family kind
selected in the residual validator row.  This is the static half of current-
step admission; the successful source step supplies the lookup and update. -/
theorem ConcreteStructuredValidationFocus.decOrdinary_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.dec objectId amount check false objectFields? continuation)) :
    ∃ objectKind,
      Fir.Wasm.findLocalKind? locals objectId = some objectKind ∧
        objectKind.isObjectLike = true := by
  have supported := validated.supported
  simp [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  cases found : Fir.Wasm.findLocalKind? locals objectId with
  | none => simp [found] at supported
  | some objectKind =>
      exact ⟨objectKind, rfl, by simpa [found] using supported.1⟩

/-- Residual-local agreement turns the validator's ordinary-decrement guard
into the exact production `getLocal` equation and directional object-family
refinement consumed by the concrete runtime theorem. -/
theorem ConcreteStructuredValidationFocus.decOrdinary_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.dec objectId amount check false objectFields? continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals) :
    ∃ objectKind,
      Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind) ∧
        objectKind.refines .tobject = true := by
  obtain ⟨objectKind, found, objectLike⟩ := validated.decOrdinary_eq
  refine ⟨objectKind, agrees found, ?_⟩
  cases objectKind <;> simp_all [Fir.Wasm.AbiKind.isObjectLike,
    Fir.Wasm.AbiKind.refines]

/-- A successful source decrement step exposes exactly the semantic lookup
and update stored by ordinary-decrement admission.  This inversion uses only
the current compiler focus to identify the source runtime/environment; it
does not inspect the target transition. -/
theorem ConcreteStructuredCodeFocus.decOrdinary_source_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ sourceObject nextRuntime,
      lookupValue sourceEnv objectId = .ok sourceObject ∧
        decValue sourceRuntime sourceObject amount check = .ok nextRuntime := by
  rcases source with
    ⟨sourceProgram, sourceControl, sourceStateEnv, sourceJoins, sourceFrames,
      sourceStateRuntime⟩
  have sourceControlEq := related.sourceControlEq
  change sourceControl = .code
    (.dec objectId amount check false objectFields? continuation)
    at sourceControlEq
  subst sourceControl
  have sourceEnvEq := related.sourceEnvEq
  change sourceStateEnv = sourceEnv at sourceEnvEq
  subst sourceStateEnv
  have sourceRuntimeEq := related.sourceRuntimeEq
  change sourceStateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceStateRuntime
  cases objectResult : lookupValue sourceEnv objectId with
  | error fault =>
      simp [executeStep, coreStep, objectResult, fail] at sourceStep
  | ok sourceObject =>
      cases updateResult : decValue sourceRuntime sourceObject amount check with
      | error fault =>
          simp [executeStep, coreStep, objectResult, updateResult, fail]
            at sourceStep
      | ok nextRuntime =>
          exact ⟨sourceObject, nextRuntime, rfl, updateResult⟩

/-- First validator-derived dynamic admission slice: an ordinary decrement is
classified from the actual residual validator, its production-local agreement,
and the successful source step.  No target path, continuation admission,
termination evidence, or allocation budget is stored in the result. -/
theorem ConcreteStructuredValidationFocus.admit_decOrdinary_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : AbiKind}
    {validatorFacts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expectedResult) validatorFacts sharing
      (.dec objectId amount check false objectFields? continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.dec objectId amount check false objectFields? continuation) := by
  obtain ⟨objectKind, objectCompiled, objectRefines⟩ :=
    validated.decOrdinary_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.decOrdinary_source_of_step sourceStep
  exact .ordinaryDecrement
    (.dec sourceRuntime nextRuntime sourceEnv objectId amount check
      objectFields? continuation objectKind sourceObject objectCompiled
      objectRefines objectLookup updated)

/-- The aligned residual package discharges ordinary-decrement admission
directly.  This is the proof-facing form consumed by the structured relation:
the caller supplies only the successful current source step. -/
theorem ConcreteStructuredAlignedValidationState.admit_decOrdinary_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult
      (.dec objectId amount check false objectFields? continuation))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.dec objectId amount check false objectFields? continuation) := by
  obtain ⟨joins, locals, validatorFacts, sharing, focus, agrees⟩ := validated
  exact focus.admit_decOrdinary_of_step agrees related sourceStep

/-- Ordinary-increment validation exposes the same object-family local guard
as decrement. -/
theorem ConcreteStructuredValidationFocus.incOrdinary_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.inc objectId amount check false continuation)) :
    ∃ objectKind,
      Fir.Wasm.findLocalKind? locals objectId = some objectKind ∧
        objectKind.isObjectLike = true := by
  have supported := validated.supported
  simp [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  cases found : Fir.Wasm.findLocalKind? locals objectId with
  | none => simp [found] at supported
  | some objectKind =>
      exact ⟨objectKind, rfl, by simpa [found] using supported.1⟩

/-- Residual-local agreement turns the increment validator guard into the
compiler equation used by the concrete operation theorem. -/
theorem ConcreteStructuredValidationFocus.incOrdinary_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.inc objectId amount check false continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals) :
    ∃ objectKind,
      Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind) ∧
        objectKind.refines .tobject = true := by
  obtain ⟨objectKind, found, objectLike⟩ := validated.incOrdinary_eq
  refine ⟨objectKind, agrees found, ?_⟩
  cases objectKind <;> simp_all [Fir.Wasm.AbiKind.isObjectLike,
    Fir.Wasm.AbiKind.refines]

/-- Successful ordinary increment exposes the source lookup and update used
by admission, independently of the target execution. -/
theorem ConcreteStructuredCodeFocus.incOrdinary_source_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.inc objectId amount check false continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ sourceObject nextRuntime,
      lookupValue sourceEnv objectId = .ok sourceObject ∧
        incValue sourceRuntime sourceObject amount check = .ok nextRuntime := by
  rcases source with
    ⟨sourceProgram, sourceControl, sourceStateEnv, sourceJoins, sourceFrames,
      sourceStateRuntime⟩
  have sourceControlEq := related.sourceControlEq
  change sourceControl = .code
    (.inc objectId amount check false continuation) at sourceControlEq
  subst sourceControl
  have sourceEnvEq := related.sourceEnvEq
  change sourceStateEnv = sourceEnv at sourceEnvEq
  subst sourceStateEnv
  have sourceRuntimeEq := related.sourceRuntimeEq
  change sourceStateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceStateRuntime
  cases objectResult : lookupValue sourceEnv objectId with
  | error fault =>
      simp [executeStep, coreStep, objectResult, fail] at sourceStep
  | ok sourceObject =>
      cases updateResult : incValue sourceRuntime sourceObject amount check with
      | error fault =>
          simp [executeStep, coreStep, objectResult, updateResult, fail]
            at sourceStep
      | ok nextRuntime =>
          exact ⟨sourceObject, nextRuntime, rfl, updateResult⟩

/-- Validator-derived ordinary-increment admission under the exact finite
header-count safety premise.  Unlike the decrement case, successful source
execution does not imply that an unbounded semantic reference count still
fits wasm32, so this premise must be discharged by the runtime-safety side of
the final simulation theorem. -/
theorem ConcreteStructuredValidationFocus.admit_incOrdinary_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : AbiKind}
    {validatorFacts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expectedResult) validatorFacts sharing
      (.inc objectId amount check false continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.inc objectId amount check false continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (fits : ∀ (sourceObject : Value) (location : Location) (cell : HeapCell),
      lookupValue sourceEnv objectId = .ok sourceObject →
        sourceObject = .object (.heap location) →
          findCell? sourceRuntime.heap location = some cell →
            cell.rc + amount < UInt32.size) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.inc objectId amount check false continuation) := by
  obtain ⟨objectKind, objectCompiled, objectRefines⟩ :=
    validated.incOrdinary_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.incOrdinary_source_of_step sourceStep
  exact .ordinaryIncrement
    (.inc sourceRuntime nextRuntime sourceEnv objectId amount check continuation
      objectKind sourceObject objectCompiled objectRefines objectLookup updated
      (fun location cell sourceObjectEq found =>
        fits sourceObject location cell objectLookup sourceObjectEq found))

/-- The aligned residual package discharges ordinary-increment admission once
the independent finite-header headroom condition is supplied. -/
theorem ConcreteStructuredAlignedValidationState.admit_incOrdinary_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult (.inc objectId amount check false continuation))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.inc objectId amount check false continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (fits : ∀ (sourceObject : Value) (location : Location) (cell : HeapCell),
      lookupValue sourceEnv objectId = .ok sourceObject →
        sourceObject = .object (.heap location) →
          findCell? sourceRuntime.heap location = some cell →
            cell.rc + amount < UInt32.size) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.inc objectId amount check false continuation) := by
  obtain ⟨joins, locals, validatorFacts, sharing, focus, agrees⟩ := validated
  exact focus.admit_incOrdinary_of_step agrees related sourceStep fits

/-- Both persistent and ordinary increments retain the validator state at
their continuation; the ordinary branch additionally discharges its local
kind guard inside the executable judgment. -/
theorem ConcreteStructuredValidationFocus.incContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.inc objectId amount check persistent continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  cases persistent with
  | false =>
      simp [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
      exact ⟨supported.2⟩
  | true =>
      simp [Fir.Wasm.supportedCodeWithJoins] at supported
      exact ⟨supported⟩

/-- Ownership increment advances only the source code; every residual
validator component is unchanged. -/
theorem ConcreteStructuredValidationState.incContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.inc objectId amount check persistent continuation)) :
    ConcreteStructuredValidationState program functionResult continuation := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.incContinuation⟩

/-- Ownership increment also preserves the compiler/validator local-row
agreement carried by the aligned residual package. -/
theorem ConcreteStructuredAlignedValidationState.incContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.inc objectId amount check persistent continuation)) :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.incContinuation, agrees⟩

/-- Both decrement modes retain the same validator state at their
continuation. -/
theorem ConcreteStructuredValidationFocus.decContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.dec objectId amount check persistent objectFields? continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  cases persistent with
  | false =>
      simp [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
      exact ⟨supported.2⟩
  | true =>
      simp [Fir.Wasm.supportedCodeWithJoins] at supported
      exact ⟨supported⟩

/-- Ownership decrement preserves the complete residual validator state. -/
theorem ConcreteStructuredValidationState.decContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.dec objectId amount check persistent objectFields? continuation)) :
    ConcreteStructuredValidationState program functionResult continuation := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.decContinuation⟩

/-- Ownership decrement also preserves the compiler/validator local-row
agreement carried by the aligned residual package. -/
theorem ConcreteStructuredAlignedValidationState.decContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult
      (.dec objectId amount check persistent objectFields? continuation)) :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.decContinuation, agrees⟩

/-- Uniform successor transport for ownership increments. -/
theorem ConcreteStructuredValidatedCodeCoreRel.incSuccessor
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore nextStore : Wasm.Store Host}
    {entryWitness witness nextWitness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts nextFacts : ReuseCapacityFacts}
    {remainingBytes nextRemainingBytes : Nat}
    {sourceEnv nextEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals nextLocals : Wasm.Locals}
    {targetCode nextTargetCode : Wasm.Program}
    {source nextSource : MachineState}
    {target nextTarget : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv (.inc objectId amount check persistent continuation)
      targetStore targetLocals targetCode witness source target)
    (nextCore : ConcreteStructuredCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv continuation nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget) :
    ConcreteStructuredValidatedCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv continuation nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget :=
  related.withSuccessor nextCore related.validation.incContinuation

/-- Uniform successor transport for ownership decrements. -/
theorem ConcreteStructuredValidatedCodeCoreRel.decSuccessor
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore nextStore : Wasm.Store Host}
    {entryWitness witness nextWitness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts nextFacts : ReuseCapacityFacts}
    {remainingBytes nextRemainingBytes : Nat}
    {sourceEnv nextEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals nextLocals : Wasm.Locals}
    {targetCode nextTargetCode : Wasm.Program}
    {source nextSource : MachineState}
    {target nextTarget : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv
      (.dec objectId amount check persistent objectFields? continuation)
      targetStore targetLocals targetCode witness source target)
    (nextCore : ConcreteStructuredCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv continuation nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget) :
    ConcreteStructuredValidatedCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv continuation nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget :=
  related.withSuccessor nextCore related.validation.decContinuation

/-- A validated persistent increment needs no caller-supplied classifier:
its syntax determines the zero-cost admission, its generated target stutters,
and the residual validator state advances with the source control. -/
theorem ConcreteStructuredValidatedCodeCoreRel.advance_incPersistent_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    (related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv (.inc objectId amount check true continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv 0
        (.inc objectId amount check true continuation) ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      sourceAfter.frames = source.frames ∧
      ConcreteStructuredValidatedCodeCoreRel program context sourceModule
        sourceFunction externals labels entryRuntime entryStore entryWitness
        functionResult callerExpectedResult facts remainingBytes sourceRuntime
        sourceEnv continuation targetStore targetLocals targetCode witness
        sourceAfter target ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source := by
  obtain ⟨computedAfter, computedStep, targetPath, nextFocus, framesEq, rank⟩ :=
    related.core.focus.advance_incPersistent
      (module := module) (hostEnv := hostEnv)
  have afterEq : sourceAfter = computedAfter := by
    rw [sourceStep] at computedStep
    exact ExecResult.next.inj computedStep
  subst computedAfter
  have nextResources :
      ConcreteStructuredResourceStack program context sourceModule
        sourceFunction externals entryRuntime sourceRuntime entryStore
        targetStore entryWitness witness facts remainingBytes sourceEnv
        targetLocals functionResult callerExpectedResult sourceAfter.frames
        target.frames := by
    rw [framesEq]
    exact related.core.resources
  have nextCore :
      ConcreteStructuredCodeCoreRel program context sourceModule
        sourceFunction externals labels entryRuntime entryStore entryWitness
        functionResult callerExpectedResult facts remainingBytes sourceRuntime
        sourceEnv continuation targetStore targetLocals targetCode witness
        sourceAfter target :=
    ⟨nextFocus, nextResources⟩
  exact ⟨.incPersistent, targetPath, framesEq,
    related.incSuccessor nextCore, rank⟩

/-- Persistent decrement has the same admission-producing, validator-
preserving zero-target-step transition. -/
theorem ConcreteStructuredValidatedCodeCoreRel.advance_decPersistent_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    (related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv
      (.dec objectId amount check true objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv 0
        (.dec objectId amount check true objectFields? continuation) ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      sourceAfter.frames = source.frames ∧
      ConcreteStructuredValidatedCodeCoreRel program context sourceModule
        sourceFunction externals labels entryRuntime entryStore entryWitness
        functionResult callerExpectedResult facts remainingBytes sourceRuntime
        sourceEnv continuation targetStore targetLocals targetCode witness
        sourceAfter target ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source := by
  obtain ⟨computedAfter, computedStep, targetPath, nextFocus, framesEq, rank⟩ :=
    related.core.focus.advance_decPersistent
      (module := module) (hostEnv := hostEnv)
  have afterEq : sourceAfter = computedAfter := by
    rw [sourceStep] at computedStep
    exact ExecResult.next.inj computedStep
  subst computedAfter
  have nextResources :
      ConcreteStructuredResourceStack program context sourceModule
        sourceFunction externals entryRuntime sourceRuntime entryStore
        targetStore entryWitness witness facts remainingBytes sourceEnv
        targetLocals functionResult callerExpectedResult sourceAfter.frames
        target.frames := by
    rw [framesEq]
    exact related.core.resources
  have nextCore :
      ConcreteStructuredCodeCoreRel program context sourceModule
        sourceFunction externals labels entryRuntime entryStore entryWitness
        functionResult callerExpectedResult facts remainingBytes sourceRuntime
        sourceEnv continuation targetStore targetLocals targetCode witness
        sourceAfter target :=
    ⟨nextFocus, nextResources⟩
  exact ⟨.decPersistent, targetPath, framesEq,
    related.decSuccessor nextCore, rank⟩

/-- The closed active-code relation is preserved by a persistent increment.
This is the first operation theorem whose conclusion retains validation for
both the active continuation and every suspended caller, while producing the
current-step admission rather than assuming it. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_incPersistent_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check true continuation) targetStore targetLocals
      targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv 0
        (.inc objectId amount check true continuation) ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      sourceAfter.frames = source.frames ∧
      ConcreteStructuredValidatedCodeOutcome program context functionCode
        sourceModule sourceFunction targetModule hosts spec externals labels
        entryRuntime entryStore entryWitness functionResult callerExpectedResult
        facts remainingBytes sourceRuntime sourceEnv continuation targetStore
        targetLocals targetCode witness sourceAfter target ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source := by
  obtain ⟨admitted, targetPath, framesEq, nextCore, rank⟩ :=
    related.core.advance_incPersistent_of_step
      (module := module) (hostEnv := hostEnv) sourceStep
  exact ⟨admitted, targetPath, framesEq,
    related.withSuccessor nextCore framesEq rfl, rank⟩

/-- Persistent decrement preserves the same closed active-and-suspended
validation relation and likewise derives its exact zero-cost admission. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_decPersistent_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check true objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv 0
        (.dec objectId amount check true objectFields? continuation) ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      sourceAfter.frames = source.frames ∧
      ConcreteStructuredValidatedCodeOutcome program context functionCode
        sourceModule sourceFunction targetModule hosts spec externals labels
        entryRuntime entryStore entryWitness functionResult callerExpectedResult
        facts remainingBytes sourceRuntime sourceEnv continuation targetStore
        targetLocals targetCode witness sourceAfter target ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source := by
  obtain ⟨admitted, targetPath, framesEq, nextCore, rank⟩ :=
    related.core.advance_decPersistent_of_step
      (module := module) (hostEnv := hostEnv) sourceStep
  exact ⟨admitted, targetPath, framesEq,
    related.withSuccessor nextCore framesEq rfl, rank⟩

/-- Ordinary increment derives its current-node admission from the successful
source/compiler predicate, executes the exact two-instruction generated host
prefix, and preserves the closed active-and-suspended validation relation. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryIncrement_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check false continuation) targetStore targetLocals
      targetCode witness source target)
    (supported : OrdinaryIncrementEffectSupported context sourceRuntime
      sourceEnv (.inc objectId amount check false continuation) continuation
      nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.ordinaryIncrement supported)
    (by omega)
  exact related.advanceCode related.core.validation.incContinuation
    (pointwise.advance_ordinaryIncrement_of_step supported sourceStep)

/-- Ordinary recursive decrement preserves the same closed relation across its
exact two-instruction generated host prefix. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryDecrement_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (supported : OrdinaryDecrementEffectSupported context sourceRuntime
      sourceEnv (.dec objectId amount check false objectFields? continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.ordinaryDecrement supported)
    (by omega)
  exact related.advanceCode related.core.validation.decContinuation
    (pointwise.advance_ordinaryDecrement_of_step supported sourceStep)

section ClosedValidatorDerivedOrdinaryOwnership

variable
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}

/-- Closed ordinary increment with compiler admission reconstructed from the
retained production validator.  The only additional premise is the genuine
finite-wasm32 reference-count headroom condition. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_ordinaryIncrement_of_validated_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check false continuation) targetStore targetLocals
      targetCode witness source target)
    (fits : ∀ (sourceObject : Value) (location : Location) (cell : HeapCell),
      lookupValue sourceEnv objectId = .ok sourceObject →
        sourceObject = .object (.heap location) →
          findCell? sourceRuntime.heap location = some cell →
            cell.rc + amount < UInt32.size)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ nextRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  obtain ⟨objectKind, objectCompiled, objectRefines⟩ :=
    validated.incOrdinary_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.core.core.focus.incOrdinary_source_of_step sourceStep
  let supported : OrdinaryIncrementEffectSupported context sourceRuntime
      sourceEnv (.inc objectId amount check false continuation) continuation
      nextRuntime :=
    .inc sourceRuntime nextRuntime sourceEnv objectId amount check continuation
      objectKind sourceObject objectCompiled objectRefines objectLookup updated
      (fun location cell sourceObjectEq found =>
        fits sourceObject location cell objectLookup sourceObjectEq found)
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_ordinaryIncrement_of_step supported sourceStep
  exact ⟨nextRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

/-- Closed ordinary decrement with all current-node admission reconstructed
from production validation and the successful source step.  Unlike increment,
it needs no independent finite-width premise. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_ordinaryDecrement_of_validated_step
    {objectFields? : Option Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ nextRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  obtain ⟨objectKind, objectCompiled, objectRefines⟩ :=
    validated.decOrdinary_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.core.core.focus.decOrdinary_source_of_step sourceStep
  let supported : OrdinaryDecrementEffectSupported context sourceRuntime
      sourceEnv
      (.dec objectId amount check false objectFields? continuation)
      continuation nextRuntime :=
    .dec sourceRuntime nextRuntime sourceEnv objectId amount check objectFields?
      continuation objectKind sourceObject objectCompiled objectRefines
      objectLookup updated
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_ordinaryDecrement_of_step supported sourceStep
  exact ⟨nextRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

end ClosedValidatorDerivedOrdinaryOwnership

/-- Object-field writes retain the residual state after their executable kind
guards have succeeded. -/
theorem ConcreteStructuredValidationFocus.osetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {fieldIndex : Nat}
    {arg : Lean.Compiler.LCNF.Arg .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.oset objectId fieldIndex arg continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  have continuationSupported :
      Fir.Wasm.supportedCodeWithJoins program joins locals expectedResult facts
        sharing continuation = true := by
    cases continuationFound : Fir.Wasm.supportedCodeWithJoins program joins
        locals expectedResult facts sharing continuation with
    | false => split at supported <;> simp_all
    | true => rfl
  exact ⟨continuationSupported⟩

theorem ConcreteStructuredValidationState.osetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {fieldIndex : Nat}
    {arg : Lean.Compiler.LCNF.Arg .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.oset objectId fieldIndex arg continuation)) :
    ConcreteStructuredValidationState program functionResult continuation := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.osetContinuation⟩

/-- Object-field writes preserve compiler/validator local agreement. -/
theorem ConcreteStructuredAlignedValidationState.osetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {fieldIndex : Nat}
    {field : Lean.Compiler.LCNF.Arg .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.oset objectId fieldIndex field continuation)) :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.osetContinuation, agrees⟩

/-- `USize` field writes preserve the residual validator state. -/
theorem ConcreteStructuredValidationFocus.usetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {fieldIndex : Nat} {fieldId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.uset objectId fieldIndex fieldId continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  exact ⟨supported.2⟩

theorem ConcreteStructuredValidationState.usetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {fieldIndex : Nat} {fieldId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.uset objectId fieldIndex fieldId continuation)) :
    ConcreteStructuredValidationState program functionResult continuation := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.usetContinuation⟩

/-- `USize` field writes preserve compiler/validator local agreement. -/
theorem ConcreteStructuredAlignedValidationState.usetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {fieldIndex : Nat} {fieldId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.uset objectId fieldIndex fieldId continuation)) :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.usetContinuation, agrees⟩

/-- Packed scalar field writes preserve the residual validator state. -/
theorem ConcreteStructuredValidationFocus.ssetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {byteOffset fieldIndex : Nat}
    {fieldId : Lean.FVarId} {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.sset objectId byteOffset fieldIndex fieldId type continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  have continuationSupported :
      Fir.Wasm.supportedCodeWithJoins program joins locals expectedResult facts
        sharing continuation = true := by
    cases continuationFound : Fir.Wasm.supportedCodeWithJoins program joins
        locals expectedResult facts sharing continuation with
    | false => split at supported <;> simp_all
    | true => rfl
  exact ⟨continuationSupported⟩

theorem ConcreteStructuredValidationState.ssetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {byteOffset fieldIndex : Nat}
    {fieldId : Lean.FVarId} {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.sset objectId byteOffset fieldIndex fieldId type continuation)) :
    ConcreteStructuredValidationState program functionResult continuation := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.ssetContinuation⟩

/-- Packed-scalar field writes preserve compiler/validator local agreement. -/
theorem ConcreteStructuredAlignedValidationState.ssetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {byteOffset fieldIndex : Nat}
    {fieldId : Lean.FVarId} {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult
      (.sset objectId byteOffset fieldIndex fieldId type continuation)) :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.ssetContinuation, agrees⟩

/-- Validation of constructor-tag mutation exposes both parts of its static
admission boundary: the source `Nat` fits the wasm32 header and the mutated
local is compiled in the ordinary-object lane. -/
theorem ConcreteStructuredValidationFocus.setTag_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.setTag objectId tag continuation)) :
    tag < UInt32.size ∧
      Fir.Wasm.findLocalKind? locals objectId = some .object := by
  have supported := validated.supported
  simp [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  exact supported.1

/-- Residual-local agreement turns the validator's constructor-tag guard into
the exact production compiler equation while retaining the width fact. -/
theorem ConcreteStructuredValidationFocus.setTag_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.setTag objectId tag continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals) :
    tag < UInt32.size ∧
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, .object) := by
  obtain ⟨tagFits, objectFound⟩ := validated.setTag_eq
  exact ⟨tagFits, agrees objectFound⟩

/-- Local inversion for the semantic helper used by mutation admission. -/
private theorem getLiveCell_shape_for_admission
    {runtime : RuntimeState} {location : Location} {cell : HeapCell}
    (effect : getLiveCell runtime location = .ok cell) :
    findCell? runtime.heap location = some cell ∧ cell.live = true := by
  unfold getLiveCell at effect
  cases found : findCell? runtime.heap location with
  | none => simp [found] at effect
  | some actualCell =>
      cases live : actualCell.live with
      | false => simp [found, live] at effect
      | true =>
          have cellEq : actualCell = cell := by
            simpa [found, live] using effect
          subst cell
          exact ⟨rfl, live⟩

/-- Successful constructor decoding fixes the heap reference, live cell, and
constructor payload used by the mutation. -/
private theorem getConstructor_shape_for_admission
    {runtime : RuntimeState} {value : Value} {location : Location}
    {cell : HeapCell} {semantic : ConstructorObject}
    (effect : getConstructor runtime value = .ok (location, cell, semantic)) :
    value = .object (.heap location) ∧
      findCell? runtime.heap location = some cell ∧
      cell.live = true ∧ cell.object = .ctor semantic := by
  unfold getConstructor at effect
  cases value with
  | object reference =>
      cases reference with
      | tagged payload => simp at effect
      | heap actualLocation =>
          simp only [Bind.bind, Except.bind] at effect
          cases liveResult : getLiveCell runtime actualLocation with
          | error fault => simp [liveResult] at effect
          | ok actualCell =>
              simp only [liveResult] at effect
              cases objectEq : actualCell.object with
              | ctor actualSemantic =>
                  simp only [objectEq, Pure.pure, Except.pure] at effect
                  have tripleEq := Except.ok.inj effect
                  rcases tripleEq with ⟨rfl, rfl, rfl⟩
                  have liveShape :=
                    getLiveCell_shape_for_admission liveResult
                  exact ⟨rfl, liveShape.1, liveShape.2, objectEq⟩
              | closure function arity fixed => simp [objectEq] at effect
              | boxed type value => simp [objectEq] at effect
              | string value => simp [objectEq] at effect
              | natural value => simp [objectEq] at effect
              | integer value => simp [objectEq] at effect
              | byteArray value => simp [objectEq] at effect
              | array elements capacity => simp [objectEq] at effect
              | «opaque» typeName => simp [objectEq] at effect
  | usize value => simp at effect
  | scalar value => simp at effect
  | erased => simp at effect
  | reuseToken location? => simp at effect

/-- A successful source constructor-tag step exposes the live constructor that
the semantic update mutates. This is the dynamic half of admission and
inspects no target execution. -/
theorem ConcreteStructuredCodeFocus.setTag_source_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.setTag objectId tag continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ location cell semantic nextRuntime,
      lookupValue sourceEnv objectId = .ok (.object (.heap location)) ∧
        setTag sourceRuntime (.object (.heap location)) tag =
          .ok nextRuntime ∧
        findCell? sourceRuntime.heap location = some cell ∧
        cell.live = true ∧
        cell.object = .ctor semantic := by
  rcases source with
    ⟨sourceProgram, sourceControl, sourceStateEnv, sourceJoins, sourceFrames,
      sourceStateRuntime⟩
  have sourceControlEq := related.sourceControlEq
  change sourceControl = .code (.setTag objectId tag continuation)
    at sourceControlEq
  subst sourceControl
  have sourceEnvEq := related.sourceEnvEq
  change sourceStateEnv = sourceEnv at sourceEnvEq
  subst sourceStateEnv
  have sourceRuntimeEq := related.sourceRuntimeEq
  change sourceStateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceStateRuntime
  cases objectResult : lookupValue sourceEnv objectId with
  | error fault =>
      simp [executeStep, coreStep, objectResult, fail] at sourceStep
  | ok sourceObject =>
      cases updateResult : setTag sourceRuntime sourceObject tag with
      | error fault =>
          simp [executeStep, coreStep, objectResult, updateResult, fail]
            at sourceStep
      | ok nextRuntime =>
          have updated := updateResult
          unfold setTag modifyConstructor at updateResult
          generalize constructorEq :
            getConstructor sourceRuntime sourceObject = constructorResult
              at updateResult
          cases constructorResult with
          | error fault =>
              simp [Bind.bind, Except.bind] at updateResult
          | ok triple =>
              obtain ⟨location, cell, semantic⟩ := triple
              have shape := getConstructor_shape_for_admission constructorEq
              rw [shape.1] at objectResult updated
              exact ⟨location, cell, semantic, nextRuntime,
                congrArg Except.ok shape.1, updated, shape.2.1, shape.2.2.1,
                shape.2.2.2⟩

/-- Constructor-tag admission is derived entirely from the current validator,
compiler-local agreement, and one successful source step. -/
theorem ConcreteStructuredValidationFocus.admit_setTag_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : AbiKind}
    {validatorFacts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expectedResult) validatorFacts sharing
      (.setTag objectId tag continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.setTag objectId tag continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.setTag objectId tag continuation) := by
  obtain ⟨tagFits, objectCompiled⟩ := validated.setTag_compiler agrees
  obtain ⟨location, cell, semantic, nextRuntime, objectLookup, updated, found,
      live, objectEq⟩ := related.setTag_source_of_step sourceStep
  exact .constructorTag
    (.setTag sourceRuntime nextRuntime sourceEnv objectId tag continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq tagFits)

/-- The aligned residual package discharges constructor-tag admission from the
successful current source step alone. -/
theorem ConcreteStructuredAlignedValidationState.admit_setTag_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult (.setTag objectId tag continuation))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.setTag objectId tag continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.setTag objectId tag continuation) := by
  obtain ⟨joins, locals, validatorFacts, sharing, focus, agrees⟩ := validated
  exact focus.admit_setTag_of_step agrees related sourceStep

/-- Source-level descriptor typing for one object field.

This is the exact invariant absent from representation-only LCNF validation:
the object currently named by `objectId` has `kind` at `index` in every
concrete descriptor related to that source value. It mentions neither emitted
code nor a target execution and is therefore a typing premise, not a
translation certificate. -/
def ConcreteObjectFieldKindAligned
    (sourceEnv : Env) (objectId : Lean.FVarId) (index : Nat)
    (kind : AbiKind) : Prop :=
  ∀ {sourceObject : Value} {witness : RefinementWitness}
      {objectWord : Word32} {info : Lean.Compiler.LCNF.CtorInfo}
      {fieldKinds : Array AbiKind},
    lookupValue sourceEnv objectId = .ok sourceObject →
      ValueRel witness .tobject (.word32 objectWord) sourceObject →
        witness.descriptors.lookup? objectWord =
            some (.constructor info fieldKinds) →
          fieldKinds[index]? = some kind

/-- The current universally witness-quantified field-alignment boundary is not
derivable from a semantic environment and heap location alone.

An otherwise valid reference witness may attach a different proof-only field
descriptor to the same semantic location.  The eventual source typing theorem
must therefore retain constructor-schema provenance and relate that provenance
to the active refinement witness; it cannot manufacture this judgment from
`MachineState` value shapes alone. -/
theorem concreteObjectFieldKindAligned_not_of_sourceLocation_alone
    (objectId : Lean.FVarId) (location : Location)
    (info : Lean.Compiler.LCNF.CtorInfo) :
    ¬ ConcreteObjectFieldKindAligned
        (bind [] objectId (.object (.heap location))) objectId 0 .object := by
  intro aligned
  let address : Word32 := ⟨8, by decide⟩
  let witness : RefinementWitness :=
    (default : RefinementWitness).bindConstructor location address info
      #[.erased]
  have sourceLookup :
      lookupValue (bind [] objectId (.object (.heap location))) objectId =
        .ok (.object (.heap location)) := by
    simp [lookupValue]
  have valueRelated :
      ValueRel witness .tobject (.word32 address)
        (.object (.heap location)) :=
    .tobject (.heap (.mapped (by
      simp [witness, RefinementWitness.bindConstructor,
        LocationMap.lookup?])))
  have descriptorFound :
      witness.descriptors.lookup? address =
        some (.constructor info #[.erased]) := by
    simp [witness, RefinementWitness.bindConstructor, DescriptorMap.lookup?]
  have impossible := aligned sourceLookup valueRelated descriptorFound
  simp at impossible

/-- The FVar mutation specialization connects descriptor typing to the exact
payload kind selected by production lowering. -/
def ConcreteObjectFieldFVarTyped
    (context : Fir.Wasm.Context) (sourceEnv : Env)
    (objectId fieldId : Lean.FVarId) (index : Nat) : Prop :=
  ∀ {fieldKind : AbiKind},
    Fir.Wasm.getLocal context fieldId =
        .ok (.localGet fieldId, fieldKind) →
      ConcreteObjectFieldKindAligned sourceEnv objectId index fieldKind

/-- Source-schema form of FVar object-field typing. Production validation
selects the payload ABI; final-LCNF typing proves that the object slot at the
same use site has that ABI in the retained semantic schema. -/
def ConstructorSchema.ObjectFieldFVarTyped
    (schema : ConstructorSchema) (context : Fir.Wasm.Context)
    (sourceEnv : Env) (objectId fieldId : Lean.FVarId) (index : Nat) : Prop :=
  ∀ {fieldKind : AbiKind},
    Fir.Wasm.getLocal context fieldId =
        .ok (.localGet fieldId, fieldKind) →
      schema.ObjectFieldKindAt sourceEnv objectId index fieldKind

/-- Validation of an FVar object-field write fixes the object lane, payload
lane, and the payload's object-field classification. -/
theorem ConcreteStructuredValidationFocus.oset_fvar_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.oset objectId index (.fvar fieldId) continuation)) :
    ∃ fieldKind,
      Fir.Wasm.findLocalKind? locals objectId = some .object ∧
        Fir.Wasm.findLocalKind? locals fieldId = some fieldKind ∧
        fieldKind.isObjectField = true := by
  have supported := validated.supported
  simp [Fir.Wasm.supportedCodeWithJoins, Fir.Wasm.supportedArgKind?] at supported
  split at supported <;> simp_all

/-- Residual-local agreement turns the FVar object-field guards into the exact
production compiler equations. -/
theorem ConcreteStructuredValidationFocus.oset_fvar_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.oset objectId index (.fvar fieldId) continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals) :
    ∃ fieldKind,
      Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, .object) ∧
        Fir.Wasm.getLocal context fieldId =
          .ok (.localGet fieldId, fieldKind) ∧
        fieldKind.isObjectField = true := by
  obtain ⟨fieldKind, objectFound, fieldFound, fieldObjectKind⟩ :=
    validated.oset_fvar_eq
  exact ⟨fieldKind, agrees objectFound, agrees fieldFound, fieldObjectKind⟩

/-- Validation of an erased object-field write fixes the object lane; the
payload lane is definitionally the canonical erased lane. -/
theorem ConcreteStructuredValidationFocus.oset_erased_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.oset objectId index .erased continuation)) :
    Fir.Wasm.findLocalKind? locals objectId = some .object := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  cases objectFound : Fir.Wasm.findLocalKind? locals objectId with
  | none => simp [objectFound] at supported
  | some objectKind =>
      cases objectKind <;>
        simp [objectFound, Fir.Wasm.supportedArgKind?] at supported ⊢

/-- Residual-local agreement turns the erased object-field guard into the
exact production object-local equation. -/
theorem ConcreteStructuredValidationFocus.oset_erased_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.oset objectId index .erased continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals) :
    Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object) :=
  agrees validated.oset_erased_eq

/-- A successful semantic object-field update determines its heap constructor
and exact object-slot bound. -/
private theorem setObjectField_shape_for_admission
    {runtime nextRuntime : RuntimeState} {object field : Value} {index : Nat}
    (updated : setObjectField runtime object index field = .ok nextRuntime) :
    ∃ location cell semantic,
      object = .object (.heap location) ∧
        findCell? runtime.heap location = some cell ∧
        cell.live = true ∧
        cell.object = .ctor semantic ∧
        index < semantic.objectFields.size := by
  unfold setObjectField modifyConstructor at updated
  simp only [Bind.bind, Except.bind] at updated
  generalize constructorEq :
    getConstructor runtime object = constructorResult at updated
  cases constructorResult with
  | error fault => simp at updated
  | ok triple =>
      obtain ⟨location, cell, semantic⟩ := triple
      simp only at updated
      by_cases bounded : index < semantic.objectFields.size
      · rw [dif_pos bounded] at updated
        have shape := getConstructor_shape_for_admission constructorEq
        exact ⟨location, cell, semantic, shape.1, shape.2.1, shape.2.2.1,
          shape.2.2.2, bounded⟩
      · rw [dif_neg bounded] at updated
        simp at updated

/-- A successful FVar object-field source step exposes all dynamic mutation
facts without inspecting the target. -/
theorem ConcreteStructuredCodeFocus.oset_fvar_source_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ location cell semantic field nextRuntime,
      lookupValue sourceEnv objectId = .ok (.object (.heap location)) ∧
        lookupValue sourceEnv fieldId = .ok field ∧
        setObjectField sourceRuntime (.object (.heap location)) index field =
          .ok nextRuntime ∧
        findCell? sourceRuntime.heap location = some cell ∧
        cell.live = true ∧
        cell.object = .ctor semantic ∧
        index < semantic.objectFields.size := by
  rcases source with
    ⟨sourceProgram, sourceControl, sourceStateEnv, sourceJoins, sourceFrames,
      sourceStateRuntime⟩
  have sourceControlEq := related.sourceControlEq
  change sourceControl =
    .code (.oset objectId index (.fvar fieldId) continuation) at sourceControlEq
  subst sourceControl
  have sourceEnvEq := related.sourceEnvEq
  change sourceStateEnv = sourceEnv at sourceEnvEq
  subst sourceStateEnv
  have sourceRuntimeEq := related.sourceRuntimeEq
  change sourceStateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceStateRuntime
  cases objectResult : lookupValue sourceEnv objectId with
  | error fault =>
      simp [executeStep, coreStep, objectResult, fail] at sourceStep
  | ok sourceObject =>
      cases fieldResult : lookupValue sourceEnv fieldId with
      | error fault =>
          have evalField : evalArg sourceEnv (.fvar fieldId) = .error fault := by
            change lookupValue sourceEnv fieldId = .error fault
            exact fieldResult
          simp [executeStep, coreStep, objectResult, evalField, fail] at sourceStep
      | ok sourceField =>
          have evalField : evalArg sourceEnv (.fvar fieldId) = .ok sourceField := by
            change lookupValue sourceEnv fieldId = .ok sourceField
            exact fieldResult
          cases updateResult :
              setObjectField sourceRuntime sourceObject index sourceField with
          | error fault =>
              simp [executeStep, coreStep, objectResult, evalField, updateResult,
                fail] at sourceStep
          | ok nextRuntime =>
              have updated := updateResult
              obtain ⟨location, cell, semantic, objectEq, found, live,
                  semanticEq, bounded⟩ :=
                setObjectField_shape_for_admission updated
              rw [objectEq] at updated
              exact ⟨location, cell, semantic, sourceField, nextRuntime,
                congrArg Except.ok objectEq, rfl,
                updated, found, live,
                semanticEq, bounded⟩

/-- A successful erased object-field source step exposes the same dynamic
facts with its canonical erased payload. -/
theorem ConcreteStructuredCodeFocus.oset_erased_source_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.oset objectId index .erased continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ location cell semantic nextRuntime,
      lookupValue sourceEnv objectId = .ok (.object (.heap location)) ∧
        setObjectField sourceRuntime (.object (.heap location)) index .erased =
          .ok nextRuntime ∧
        findCell? sourceRuntime.heap location = some cell ∧
        cell.live = true ∧
        cell.object = .ctor semantic ∧
        index < semantic.objectFields.size := by
  rcases source with
    ⟨sourceProgram, sourceControl, sourceStateEnv, sourceJoins, sourceFrames,
      sourceStateRuntime⟩
  have sourceControlEq := related.sourceControlEq
  change sourceControl = .code (.oset objectId index .erased continuation)
    at sourceControlEq
  subst sourceControl
  have sourceEnvEq := related.sourceEnvEq
  change sourceStateEnv = sourceEnv at sourceEnvEq
  subst sourceStateEnv
  have sourceRuntimeEq := related.sourceRuntimeEq
  change sourceStateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceStateRuntime
  cases objectResult : lookupValue sourceEnv objectId with
  | error fault =>
      simp [executeStep, coreStep, evalArg, objectResult, fail] at sourceStep
  | ok sourceObject =>
      cases updateResult :
          setObjectField sourceRuntime sourceObject index .erased with
      | error fault =>
          simp [executeStep, coreStep, evalArg, objectResult, updateResult,
            fail] at sourceStep
      | ok nextRuntime =>
          have updated := updateResult
          obtain ⟨location, cell, semantic, objectEq, found, live, semanticEq,
              bounded⟩ := setObjectField_shape_for_admission updated
          rw [objectEq] at updated
          exact ⟨location, cell, semantic, nextRuntime,
            congrArg Except.ok objectEq, updated, found, live, semanticEq,
            bounded⟩

/-- FVar object-field mutation is a complete current-step admission case once
the explicit source descriptor-typing invariant is supplied. -/
theorem ConcreteStructuredValidationFocus.admit_oset_fvar_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : AbiKind}
    {validatorFacts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expectedResult) validatorFacts sharing
      (.oset objectId index (.fvar fieldId) continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (fieldTyped : ConcreteObjectFieldFVarTyped context sourceEnv objectId
      fieldId index) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.oset objectId index (.fvar fieldId) continuation) := by
  obtain ⟨fieldKind, objectCompiled, fieldCompiled, fieldObjectKind⟩ :=
    validated.oset_fvar_compiler agrees
  obtain ⟨location, cell, semantic, field, nextRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq, indexValid⟩ :=
    related.oset_fvar_source_of_step sourceStep
  exact .objectFieldFVar
    (.oset sourceRuntime nextRuntime sourceEnv objectId fieldId index
      continuation location cell semantic field fieldKind objectCompiled
      fieldCompiled fieldObjectKind objectLookup fieldLookup updated found live
      objectEq indexValid (fun objectRelated descriptorFound =>
        fieldTyped fieldCompiled objectLookup objectRelated descriptorFound))

/-- Erased object-field mutation uses the same source typing boundary at the
canonical erased descriptor kind. -/
theorem ConcreteStructuredValidationFocus.admit_oset_erased_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : AbiKind}
    {validatorFacts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expectedResult) validatorFacts sharing
      (.oset objectId index .erased continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.oset objectId index .erased continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (fieldTyped : ConcreteObjectFieldKindAligned sourceEnv objectId index
      .erased) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.oset objectId index .erased continuation) := by
  have objectCompiled := validated.oset_erased_compiler agrees
  obtain ⟨location, cell, semantic, nextRuntime, objectLookup, updated, found,
      live, objectEq, indexValid⟩ :=
    related.oset_erased_source_of_step sourceStep
  exact .objectFieldErased
    (.oset sourceRuntime nextRuntime sourceEnv objectId index continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq indexValid (fun objectRelated descriptorFound =>
        fieldTyped objectLookup objectRelated descriptorFound))

/-- The aligned residual package closes FVar object-field admission under the
same source descriptor-typing invariant. -/
theorem ConcreteStructuredAlignedValidationState.admit_oset_fvar_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult (.oset objectId index (.fvar fieldId) continuation))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (fieldTyped : ConcreteObjectFieldFVarTyped context sourceEnv objectId
      fieldId index) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.oset objectId index (.fvar fieldId) continuation) := by
  obtain ⟨joins, locals, validatorFacts, sharing, focus, agrees⟩ := validated
  exact focus.admit_oset_fvar_of_step agrees related sourceStep fieldTyped

/-- The aligned residual package closes erased object-field admission under
the canonical erased descriptor-typing invariant. -/
theorem ConcreteStructuredAlignedValidationState.admit_oset_erased_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult (.oset objectId index .erased continuation))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.oset objectId index .erased continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (fieldTyped : ConcreteObjectFieldKindAligned sourceEnv objectId index
      .erased) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.oset objectId index .erased continuation) := by
  obtain ⟨joins, locals, validatorFacts, sharing, focus, agrees⟩ := validated
  exact focus.admit_oset_erased_of_step agrees related sourceStep fieldTyped

/-- Validation of a `USize` field write fixes both compiler-local lanes. -/
theorem ConcreteStructuredValidationFocus.uset_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.uset objectId index fieldId continuation)) :
    Fir.Wasm.findLocalKind? locals objectId = some .object ∧
      Fir.Wasm.findLocalKind? locals fieldId = some .usize := by
  have supported := validated.supported
  simp [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  exact supported.1

/-- Residual-local agreement turns the two `USize` validator guards into the
exact production compiler equations. -/
theorem ConcreteStructuredValidationFocus.uset_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.uset objectId index fieldId continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals) :
    Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, .object) ∧
      Fir.Wasm.getLocal context fieldId =
        .ok (.localGet fieldId, .usize) := by
  obtain ⟨objectFound, fieldFound⟩ := validated.uset_eq
  exact ⟨agrees objectFound, agrees fieldFound⟩

/-- A successful semantic `USize` write determines its heap constructor,
payload lane, and exact absolute-slot bounds. -/
private theorem setUSizeSlot_shape_for_admission
    {runtime nextRuntime : RuntimeState} {object fieldValue : Value}
    {slot : Nat}
    (updated : setUSizeSlot runtime object slot fieldValue = .ok nextRuntime) :
    ∃ location cell semantic field,
      object = .object (.heap location) ∧
        fieldValue = .usize field ∧
        findCell? runtime.heap location = some cell ∧
        cell.live = true ∧
        cell.object = .ctor semantic ∧
        semantic.objectFields.size ≤ slot ∧
        slot < semantic.objectFields.size + semantic.usizeFields.size := by
  cases fieldValue with
  | object reference => simp [setUSizeSlot] at updated
  | usize field =>
      unfold setUSizeSlot modifyConstructor at updated
      simp only [Bind.bind, Except.bind] at updated
      generalize constructorEq :
        getConstructor runtime object = constructorResult at updated
      cases constructorResult with
      | error fault => simp at updated
      | ok triple =>
          obtain ⟨location, cell, semantic⟩ := triple
          simp only at updated
          by_cases slotStart : semantic.objectFields.size ≤ slot
          · rw [if_pos slotStart] at updated
            let localIndex := slot - semantic.objectFields.size
            by_cases bounded : localIndex < semantic.usizeFields.size
            · rw [dif_pos bounded] at updated
              have shape :=
                getConstructor_shape_for_admission constructorEq
              exact ⟨location, cell, semantic, field, shape.1, rfl,
                shape.2.1, shape.2.2.1, shape.2.2.2, slotStart, by omega⟩
            · rw [dif_neg bounded] at updated
              simp at updated
          · rw [if_neg slotStart] at updated
            simp at updated
  | scalar value => simp [setUSizeSlot] at updated
  | erased => simp [setUSizeSlot] at updated
  | reuseToken location? => simp [setUSizeSlot] at updated

/-- A successful source `USize` field step exposes all dynamic facts required
by the existing concrete mutation theorem, without inspecting the target. -/
theorem ConcreteStructuredCodeFocus.uset_source_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.uset objectId index fieldId continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ location cell semantic field nextRuntime,
      lookupValue sourceEnv objectId = .ok (.object (.heap location)) ∧
        lookupValue sourceEnv fieldId = .ok (.usize field) ∧
        setUSizeSlot sourceRuntime (.object (.heap location)) index
            (.usize field) = .ok nextRuntime ∧
        findCell? sourceRuntime.heap location = some cell ∧
        cell.live = true ∧
        cell.object = .ctor semantic ∧
        semantic.objectFields.size ≤ index ∧
        index < semantic.objectFields.size + semantic.usizeFields.size := by
  rcases source with
    ⟨sourceProgram, sourceControl, sourceStateEnv, sourceJoins, sourceFrames,
      sourceStateRuntime⟩
  have sourceControlEq := related.sourceControlEq
  change sourceControl = .code (.uset objectId index fieldId continuation)
    at sourceControlEq
  subst sourceControl
  have sourceEnvEq := related.sourceEnvEq
  change sourceStateEnv = sourceEnv at sourceEnvEq
  subst sourceStateEnv
  have sourceRuntimeEq := related.sourceRuntimeEq
  change sourceStateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceStateRuntime
  cases objectResult : lookupValue sourceEnv objectId with
  | error fault =>
      simp [executeStep, coreStep, objectResult, fail] at sourceStep
  | ok sourceObject =>
      cases fieldResult : lookupValue sourceEnv fieldId with
      | error fault =>
          simp [executeStep, coreStep, objectResult, fieldResult, fail]
            at sourceStep
      | ok sourceField =>
          cases updateResult :
              setUSizeSlot sourceRuntime sourceObject index sourceField with
          | error fault =>
              simp [executeStep, coreStep, objectResult, fieldResult,
                updateResult, fail] at sourceStep
          | ok nextRuntime =>
              have updated := updateResult
              obtain ⟨location, cell, semantic, field, objectEq, fieldEq,
                  found, live, semanticEq, slotStart, slotEnd⟩ :=
                setUSizeSlot_shape_for_admission updated
              rw [objectEq, fieldEq] at updated
              exact ⟨location, cell, semantic, field, nextRuntime,
                congrArg Except.ok objectEq, congrArg Except.ok fieldEq,
                updated, found, live, semanticEq, slotStart, slotEnd⟩

/-- `USize` field mutation is a complete validator-derived current-step
admission case. -/
theorem ConcreteStructuredValidationFocus.admit_uset_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : AbiKind}
    {validatorFacts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expectedResult) validatorFacts sharing
      (.uset objectId index fieldId continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.uset objectId index fieldId continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.uset objectId index fieldId continuation) := by
  obtain ⟨objectCompiled, fieldCompiled⟩ := validated.uset_compiler agrees
  obtain ⟨location, cell, semantic, field, nextRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq, slotStart, slotEnd⟩ :=
    related.uset_source_of_step sourceStep
  exact .usizeField
    (.uset sourceRuntime nextRuntime sourceEnv objectId fieldId index
      continuation location cell semantic field objectCompiled fieldCompiled
      objectLookup fieldLookup updated found live objectEq slotStart slotEnd)

/-- The aligned residual package discharges `USize` field admission from one
successful source step. -/
theorem ConcreteStructuredAlignedValidationState.admit_uset_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult (.uset objectId index fieldId continuation))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.uset objectId index fieldId continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.uset objectId index fieldId continuation) := by
  obtain ⟨joins, locals, validatorFacts, sharing, focus, agrees⟩ := validated
  exact focus.admit_uset_of_step agrees related sourceStep

/-- Source/runtime layout typing for one packed-scalar field mutation.

The predicate connects the semantic constructor currently named by
`objectId` to every concrete descriptor refining that value. It states exactly
the packed coordinate, extent, and non-overlap facts required by the existing
concrete scalar-mutation theorem. It mentions neither emitted code nor a
target execution and is therefore a source typing premise rather than a
translation certificate. -/
def ConcreteScalarFieldLayoutAligned
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (objectId : Lean.FVarId) (slotIndex byteOffset : Nat)
    (fieldKind : AbiKind) : Prop :=
  ∀ {location : Location} {cell : HeapCell} {semantic : ConstructorObject}
      {witness : RefinementWitness} {objectWord : Word32}
      {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind},
    lookupValue sourceEnv objectId = .ok (.object (.heap location)) →
      findCell? sourceRuntime.heap location = some cell →
        cell.live = true →
          cell.object = .ctor semantic →
            ValueRel witness .tobject (.word32 objectWord)
                (.object (.heap location)) →
              witness.descriptors.lookup? objectWord =
                  some (.constructor info fieldKinds) →
                ScalarFieldMutationSafe semantic slotIndex byteOffset
                  fieldKind info

/-- The scalar-field specialization connects source/runtime layout typing to
the exact payload kind selected by production lowering. -/
def ConcreteScalarFieldMutationTyped
    (context : Fir.Wasm.Context) (sourceRuntime : RuntimeState)
    (sourceEnv : Env) (objectId fieldId : Lean.FVarId)
    (slotIndex byteOffset : Nat) : Prop :=
  ∀ {fieldKind : AbiKind},
    Fir.Wasm.getLocal context fieldId =
        .ok (.localGet fieldId, fieldKind) →
      ConcreteScalarFieldLayoutAligned sourceRuntime sourceEnv objectId
        slotIndex byteOffset fieldKind

/-- Validation of a packed-scalar write fixes the object lane, payload lane,
source annotation, and the scalar ABI family accepted by production lowering.
The production validator deliberately supplies no layout-coordinate fact. -/
theorem ConcreteStructuredValidationFocus.sset_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.sset objectId slotIndex byteOffset fieldId type continuation)) :
    ∃ fieldKind,
      Fir.Wasm.findLocalKind? locals objectId = some .object ∧
        Fir.Wasm.findLocalKind? locals fieldId = some fieldKind ∧
        Fir.Wasm.abiValueKind? type = some fieldKind ∧
        Fir.Wasm.supportedScalarProjectionKind fieldKind = true := by
  have supported := validated.supported
  simp [Fir.Wasm.supportedCodeWithJoins] at supported
  split at supported <;> simp_all
  simpa [supported.1.1] using supported.1.2

/-- Residual-local agreement turns the scalar validator guards into the exact
production compiler equations. -/
theorem ConcreteStructuredValidationFocus.sset_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.sset objectId slotIndex byteOffset fieldId type continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals) :
    ∃ fieldKind,
      Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, .object) ∧
        Fir.Wasm.getLocal context fieldId =
          .ok (.localGet fieldId, fieldKind) ∧
        Fir.Wasm.abiValueKind? type = some fieldKind ∧
        Fir.Wasm.supportedScalarProjectionKind fieldKind = true := by
  obtain ⟨fieldKind, objectFound, fieldFound, annotationFound,
      scalarSupported⟩ := validated.sset_eq
  exact ⟨fieldKind, agrees objectFound, agrees fieldFound, annotationFound,
    scalarSupported⟩

/-- A successful semantic scalar write determines its heap constructor and
scalar payload. Source execution itself imposes no packed-layout bounds. -/
private theorem setScalarField_shape_for_admission
    {runtime nextRuntime : RuntimeState} {object fieldValue : Value}
    {slotIndex byteOffset : Nat}
    (updated : setScalarField runtime object slotIndex byteOffset fieldValue =
      .ok nextRuntime) :
    ∃ location cell semantic field,
      object = .object (.heap location) ∧
        fieldValue = .scalar field ∧
        findCell? runtime.heap location = some cell ∧
        cell.live = true ∧
        cell.object = .ctor semantic := by
  cases fieldValue with
  | object reference => simp [setScalarField] at updated
  | usize field => simp [setScalarField] at updated
  | scalar field =>
      unfold setScalarField modifyConstructor at updated
      simp only [Bind.bind, Except.bind] at updated
      generalize constructorEq :
        getConstructor runtime object = constructorResult at updated
      cases constructorResult with
      | error fault => simp at updated
      | ok triple =>
          obtain ⟨location, cell, semantic⟩ := triple
          simp only at updated
          have shape := getConstructor_shape_for_admission constructorEq
          exact ⟨location, cell, semantic, field, shape.1, rfl,
            shape.2.1, shape.2.2.1, shape.2.2.2⟩
  | erased => simp [setScalarField] at updated
  | reuseToken location? => simp [setScalarField] at updated

/-- A successful source scalar-field step exposes every dynamic mutation fact
without inspecting the target. -/
theorem ConcreteStructuredCodeFocus.sset_source_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ location cell semantic field nextRuntime,
      lookupValue sourceEnv objectId = .ok (.object (.heap location)) ∧
        lookupValue sourceEnv fieldId = .ok (.scalar field) ∧
        setScalarField sourceRuntime (.object (.heap location)) slotIndex
            byteOffset (.scalar field) = .ok nextRuntime ∧
        findCell? sourceRuntime.heap location = some cell ∧
        cell.live = true ∧
        cell.object = .ctor semantic := by
  rcases source with
    ⟨sourceProgram, sourceControl, sourceStateEnv, sourceJoins, sourceFrames,
      sourceStateRuntime⟩
  have sourceControlEq := related.sourceControlEq
  change sourceControl = .code
    (.sset objectId slotIndex byteOffset fieldId type continuation)
    at sourceControlEq
  subst sourceControl
  have sourceEnvEq := related.sourceEnvEq
  change sourceStateEnv = sourceEnv at sourceEnvEq
  subst sourceStateEnv
  have sourceRuntimeEq := related.sourceRuntimeEq
  change sourceStateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceStateRuntime
  cases objectResult : lookupValue sourceEnv objectId with
  | error fault =>
      simp [executeStep, coreStep, objectResult, fail] at sourceStep
  | ok sourceObject =>
      cases fieldResult : lookupValue sourceEnv fieldId with
      | error fault =>
          simp [executeStep, coreStep, objectResult, fieldResult, fail]
            at sourceStep
      | ok sourceField =>
          cases updateResult : setScalarField sourceRuntime sourceObject
              slotIndex byteOffset sourceField with
          | error fault =>
              simp [executeStep, coreStep, objectResult, fieldResult,
                updateResult, fail] at sourceStep
          | ok nextRuntime =>
              have updated := updateResult
              obtain ⟨location, cell, semantic, field, objectEq, fieldEq,
                  found, live, semanticEq⟩ :=
                setScalarField_shape_for_admission updated
              rw [objectEq, fieldEq] at updated
              exact ⟨location, cell, semantic, field, nextRuntime,
                congrArg Except.ok objectEq, congrArg Except.ok fieldEq,
                updated, found, live, semanticEq⟩

/-- Packed-integer scalar mutation is a complete current-step admission case
once the explicit source/runtime layout-typing invariant is supplied. -/
theorem ConcreteStructuredValidationFocus.admit_sset_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : AbiKind}
    {validatorFacts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expectedResult) validatorFacts sharing
      (.sset objectId slotIndex byteOffset fieldId type continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (fieldTyped : ConcreteScalarFieldMutationTyped context sourceRuntime
      sourceEnv objectId fieldId slotIndex byteOffset) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.sset objectId slotIndex byteOffset fieldId type continuation) := by
  obtain ⟨fieldKind, objectCompiled, fieldCompiled, annotationFound,
      scalarSupported⟩ := validated.sset_compiler agrees
  obtain ⟨location, cell, semantic, field, nextRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq⟩ :=
    related.sset_source_of_step sourceStep
  exact .scalarField
    (.sset sourceRuntime nextRuntime sourceEnv objectId fieldId slotIndex
      byteOffset type continuation location cell semantic field fieldKind
      objectCompiled fieldCompiled objectLookup fieldLookup updated found live
      objectEq (fun objectRelated descriptorFound =>
        fieldTyped fieldCompiled objectLookup found live objectEq objectRelated
          descriptorFound))

/-- The aligned residual package closes packed-integer scalar admission under
the same explicit source/runtime layout invariant. -/
theorem ConcreteStructuredAlignedValidationState.admit_sset_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult
      (.sset objectId slotIndex byteOffset fieldId type continuation))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      targetStore targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (fieldTyped : ConcreteScalarFieldMutationTyped context sourceRuntime
      sourceEnv objectId fieldId slotIndex byteOffset) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.sset objectId slotIndex byteOffset fieldId type continuation) := by
  obtain ⟨joins, locals, validatorFacts, sharing, focus, agrees⟩ := validated
  exact focus.admit_sset_of_step agrees related sourceStep fieldTyped

/-- Constructor-tag writes preserve the residual validator state. -/
theorem ConcreteStructuredValidationFocus.setTagContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.setTag objectId tag continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  exact ⟨supported.2⟩

theorem ConcreteStructuredValidationState.setTagContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.setTag objectId tag continuation)) :
    ConcreteStructuredValidationState program functionResult continuation := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.setTagContinuation⟩

/-- Constructor-tag writes preserve compiler/validator local agreement. -/
theorem ConcreteStructuredAlignedValidationState.setTagContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.setTag objectId tag continuation)) :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.setTagContinuation, agrees⟩

/-- Validation of explicit deletion selects the exact ordinary-object local
lane used by production lowering. -/
theorem ConcreteStructuredValidationFocus.del_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.del objectId continuation)) :
    Fir.Wasm.findLocalKind? locals objectId = some .object := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  simpa using supported.1

/-- Residual-local agreement turns the validator's delete guard into the
production compiler equation required by delete admission. -/
theorem ConcreteStructuredValidationFocus.del_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.del objectId continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals) :
    Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object) :=
  agrees validated.del_eq

/-- A successful source delete step exposes exactly the semantic lookup and
update stored by ordinary-delete admission. Target execution is not inspected.
-/
theorem ConcreteStructuredCodeFocus.del_source_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.del objectId continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ sourceObject nextRuntime,
      lookupValue sourceEnv objectId = .ok sourceObject ∧
        deleteValue sourceRuntime sourceObject = .ok nextRuntime := by
  rcases source with
    ⟨sourceProgram, sourceControl, sourceStateEnv, sourceJoins, sourceFrames,
      sourceStateRuntime⟩
  have sourceControlEq := related.sourceControlEq
  change sourceControl = .code (.del objectId continuation) at sourceControlEq
  subst sourceControl
  have sourceEnvEq := related.sourceEnvEq
  change sourceStateEnv = sourceEnv at sourceEnvEq
  subst sourceStateEnv
  have sourceRuntimeEq := related.sourceRuntimeEq
  change sourceStateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceStateRuntime
  cases objectResult : lookupValue sourceEnv objectId with
  | error fault =>
      simp [executeStep, coreStep, objectResult, fail] at sourceStep
  | ok sourceObject =>
      cases updateResult : deleteValue sourceRuntime sourceObject with
      | error fault =>
          simp [executeStep, coreStep, objectResult, updateResult, fail]
            at sourceStep
      | ok nextRuntime =>
          exact ⟨sourceObject, nextRuntime, rfl, updateResult⟩

/-- Validator-derived delete admission from the aligned current state and the
actual successful source step. No target path or continuation admission is
retained. -/
theorem ConcreteStructuredValidationFocus.admit_del_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : AbiKind}
    {validatorFacts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expectedResult) validatorFacts sharing
      (.del objectId continuation))
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.del objectId continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.del objectId continuation) := by
  have objectCompiled := validated.del_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.del_source_of_step sourceStep
  exact .ordinaryDelete
    (.del sourceRuntime nextRuntime sourceEnv objectId continuation .object
      sourceObject objectCompiled objectLookup updated)

/-- The aligned residual package discharges explicit-delete admission from
the successful current source step alone. -/
theorem ConcreteStructuredAlignedValidationState.admit_del_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult (.del objectId continuation))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.del objectId continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0
      (.del objectId continuation) := by
  obtain ⟨joins, locals, validatorFacts, sharing, focus, agrees⟩ := validated
  exact focus.admit_del_of_step agrees related sourceStep

/-- Explicit deletion preserves the residual validator state. -/
theorem ConcreteStructuredValidationFocus.delContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.del objectId continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  exact ⟨supported.2⟩

theorem ConcreteStructuredValidationState.delContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.del objectId continuation)) :
    ConcreteStructuredValidationState program functionResult continuation := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.delContinuation⟩

/-- Explicit deletion preserves the complete aligned residual state. -/
theorem ConcreteStructuredAlignedValidationState.delContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.del objectId continuation)) :
    ConcreteStructuredAlignedValidationState program context functionResult
      continuation := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  exact ⟨joins, locals, facts, sharing, focus.delContinuation, agrees⟩

/-- Explicit delete, including erased physical zero, preserves the closed
relation across the exact two-instruction generated host prefix. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryDelete_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.del objectId continuation) targetStore targetLocals targetCode witness
      source target)
    (supported : OrdinaryDeleteEffectSupported context sourceRuntime sourceEnv
      (.del objectId continuation) continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.ordinaryDelete supported)
    (by omega)
  exact related.advanceCode related.core.validation.delContinuation
    (pointwise.advance_ordinaryDelete_of_step supported sourceStep)

/-- Closed explicit deletion with its compiler local and semantic transition
reconstructed from retained validation and the successful source step. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_ordinaryDelete_of_validated_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.del objectId continuation) targetStore targetLocals targetCode witness
      source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ nextRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  have objectCompiled := validated.del_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.core.core.focus.del_source_of_step sourceStep
  let supported : OrdinaryDeleteEffectSupported context sourceRuntime sourceEnv
      (.del objectId continuation) continuation nextRuntime :=
    .del sourceRuntime nextRuntime sourceEnv objectId continuation .object
      sourceObject objectCompiled objectLookup updated
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_ordinaryDelete_of_step supported sourceStep
  exact ⟨nextRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

section ClosedMutation

variable
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}

/-- Constructor-tag mutation preserves the closed active-and-suspended
validation relation across its exact generated two-step prefix. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_constructorTag_of_step
    {objectId : Lean.FVarId} {tag : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.setTag objectId tag continuation) targetStore targetLocals targetCode
      witness source target)
    (supported : ConstructorTagEffectSupported context sourceRuntime sourceEnv
      (.setTag objectId tag continuation) continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.constructorTag supported) (by omega)
  exact related.advanceCode related.core.validation.setTagContinuation
    (pointwise.advance_constructorTag_of_step supported sourceStep)

/-- Closed constructor-tag mutation with static width/local facts recovered
from production validation and heap-shape facts recovered from the source
step. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_constructorTag_of_validated_step
    {objectId : Lean.FVarId} {tag : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.setTag objectId tag continuation) targetStore targetLocals targetCode
      witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  obtain ⟨tagFits, objectCompiled⟩ := validated.setTag_compiler agrees
  obtain ⟨location, cell, semantic, resultRuntime, objectLookup, updated,
      found, live, objectEq⟩ :=
    related.core.core.focus.setTag_source_of_step sourceStep
  let supported : ConstructorTagEffectSupported context sourceRuntime sourceEnv
      (.setTag objectId tag continuation) continuation resultRuntime :=
    .setTag sourceRuntime resultRuntime sourceEnv objectId tag continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq tagFits
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_constructorTag_of_step supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

/-- Object-reference field mutation preserves closed validation across its
exact generated three-step prefix. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_objectFieldFVar_of_step
    {objectId fieldId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) targetStore
      targetLocals targetCode witness source target)
    (supported : ObjectFieldFVarEffectSupported context sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) continuation
      nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.objectFieldFVar supported) (by omega)
  exact related.advanceCode related.core.validation.osetContinuation
    (pointwise.advance_objectFieldFVar_of_step supported sourceStep)

/-- Erased object-field mutation preserves closed validation while the target
writes the canonical erased physical zero. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_objectFieldErased_of_step
    {objectId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index .erased continuation) targetStore targetLocals
      targetCode witness source target)
    (supported : ObjectFieldErasedEffectSupported context sourceRuntime
      sourceEnv (.oset objectId index .erased continuation) continuation
      nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.objectFieldErased supported) (by omega)
  exact related.advanceCode related.core.validation.osetContinuation
    (pointwise.advance_objectFieldErased_of_step supported sourceStep)

theorem ConcreteStructuredValidatedCodeOutcome.advance_objectFieldFVarAt_of_step
    {objectId fieldId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) targetStore
      targetLocals targetCode witness source target)
    (supported : ObjectFieldFVarEffectSupportedAt context witness sourceRuntime
      sourceEnv (.oset objectId index (.fvar fieldId) continuation) continuation
      nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  exact related.advanceCode related.core.validation.osetContinuation
    (related.core.core.advance_objectFieldFVarAt_of_step spec supported
      sourceStep)

theorem ConcreteStructuredValidatedCodeOutcome.advance_objectFieldErasedAt_of_step
    {objectId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index .erased continuation) targetStore targetLocals
      targetCode witness source target)
    (supported : ObjectFieldErasedEffectSupportedAt context witness
      sourceRuntime sourceEnv (.oset objectId index .erased continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  exact related.advanceCode related.core.validation.osetContinuation
    (related.core.core.advance_objectFieldErasedAt_of_step spec supported
      sourceStep)

/-- `USize` slot mutation preserves the closed relation across its exact
generated three-step prefix. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_usizeField_of_step
    {objectId fieldId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) targetStore targetLocals
      targetCode witness source target)
    (supported : USizeFieldEffectSupported context sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.usizeField supported) (by omega)
  exact related.advanceCode related.core.validation.usetContinuation
    (pointwise.advance_usizeField_of_step supported sourceStep)

/-- Packed-integer scalar mutation preserves the closed relation across its
descriptor/layout-checked three-step prefix. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_scalarField_of_step
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation) targetStore
      targetLocals targetCode witness source target)
    (supported : ScalarFieldEffectSupported context sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.scalarField supported) (by omega)
  exact related.advanceCode related.core.validation.ssetContinuation
    (pointwise.advance_scalarField_of_step supported sourceStep)

/-- Closed object-reference field mutation.  Production validation supplies
the compiled operands, the successful source step supplies the live mutation,
and `fieldTyped` is the sole source descriptor-typing boundary. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_objectFieldFVar_of_validated_step
    {objectId fieldId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) targetStore
      targetLocals targetCode witness source target)
    (fieldTyped : ConcreteObjectFieldFVarTyped context sourceEnv objectId
      fieldId index)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  obtain ⟨fieldKind, objectCompiled, fieldCompiled, fieldObjectKind⟩ :=
    validated.oset_fvar_compiler agrees
  obtain ⟨location, cell, semantic, field, resultRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq, indexValid⟩ :=
    related.core.core.focus.oset_fvar_source_of_step sourceStep
  let supported : ObjectFieldFVarEffectSupported context sourceRuntime
      sourceEnv (.oset objectId index (.fvar fieldId) continuation)
      continuation resultRuntime :=
    .oset sourceRuntime resultRuntime sourceEnv objectId fieldId index
      continuation location cell semantic field fieldKind objectCompiled
      fieldCompiled fieldObjectKind objectLookup fieldLookup updated found live
      objectEq indexValid (fun objectRelated descriptorFound =>
        fieldTyped fieldCompiled objectLookup objectRelated descriptorFound)
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_objectFieldFVar_of_step supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

/-- Closed erased object-field mutation.  The only non-validator premise is
the source descriptor's erased-field alignment. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_objectFieldErased_of_validated_step
    {objectId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index .erased continuation) targetStore targetLocals
      targetCode witness source target)
    (fieldTyped : ConcreteObjectFieldKindAligned sourceEnv objectId index
      .erased)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  have objectCompiled := validated.oset_erased_compiler agrees
  obtain ⟨location, cell, semantic, resultRuntime, objectLookup, updated,
      found, live, objectEq, indexValid⟩ :=
    related.core.core.focus.oset_erased_source_of_step sourceStep
  let supported : ObjectFieldErasedEffectSupported context sourceRuntime
      sourceEnv (.oset objectId index .erased continuation) continuation
      resultRuntime :=
    .oset sourceRuntime resultRuntime sourceEnv objectId index continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq indexValid (fun objectRelated descriptorFound =>
        fieldTyped objectLookup objectRelated descriptorFound)
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_objectFieldErased_of_step supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

/-- Closed FVar object-field mutation from source schema typing and agreement
with the active simulation witness. No arbitrary-witness premise remains. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_objectFieldFVar_of_schema_step
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {schema : ConstructorSchema}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) targetStore
      targetLocals targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (fieldTyped : schema.ObjectFieldFVarTyped context sourceEnv objectId
      fieldId index)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  obtain ⟨fieldKind, objectCompiled, fieldCompiled, fieldObjectKind⟩ :=
    validated.oset_fvar_compiler agrees
  obtain ⟨location, cell, semantic, field, resultRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq, indexValid⟩ :=
    related.core.core.focus.oset_fvar_source_of_step sourceStep
  have activeAligned :
      ConcreteObjectFieldKindAlignedAt witness location index fieldKind :=
    ConcreteObjectFieldKindAlignedAt.of_schema schemaAgrees
      (fieldTyped fieldCompiled objectLookup)
  let supported : ObjectFieldFVarEffectSupportedAt context witness
      sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) continuation
      resultRuntime :=
    .oset sourceRuntime resultRuntime sourceEnv objectId fieldId index
      continuation location cell semantic field fieldKind objectCompiled
      fieldCompiled fieldObjectKind objectLookup fieldLookup updated found live
      objectEq indexValid activeAligned
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_objectFieldFVarAt_of_step supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

/-- Closed erased object-field mutation from the same active schema bridge. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_objectFieldErased_of_schema_step
    {objectId : Lean.FVarId} {index : Nat} {schema : ConstructorSchema}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index .erased continuation) targetStore targetLocals
      targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (fieldTyped : schema.ObjectFieldKindAt sourceEnv objectId index .erased)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  have objectCompiled := validated.oset_erased_compiler agrees
  obtain ⟨location, cell, semantic, resultRuntime, objectLookup, updated,
      found, live, objectEq, indexValid⟩ :=
    related.core.core.focus.oset_erased_source_of_step sourceStep
  have activeAligned :
      ConcreteObjectFieldKindAlignedAt witness location index .erased :=
    ConcreteObjectFieldKindAlignedAt.of_schema schemaAgrees
      (fieldTyped objectLookup)
  let supported : ObjectFieldErasedEffectSupportedAt context witness
      sourceRuntime sourceEnv (.oset objectId index .erased continuation)
      continuation resultRuntime :=
    .oset sourceRuntime resultRuntime sourceEnv objectId index continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq indexValid activeAligned
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_objectFieldErasedAt_of_step supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

/-- Closed `USize` field mutation is fully reconstructed from validation and
one successful source step; no additional source layout premise is needed. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_usizeField_of_validated_step
    {objectId fieldId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) targetStore targetLocals
      targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  obtain ⟨objectCompiled, fieldCompiled⟩ := validated.uset_compiler agrees
  obtain ⟨location, cell, semantic, field, resultRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq, slotStart, slotEnd⟩ :=
    related.core.core.focus.uset_source_of_step sourceStep
  let supported : USizeFieldEffectSupported context sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) continuation resultRuntime :=
    .uset sourceRuntime resultRuntime sourceEnv objectId fieldId index
      continuation location cell semantic field objectCompiled fieldCompiled
      objectLookup fieldLookup updated found live objectEq slotStart slotEnd
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_usizeField_of_step supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

/-- Closed packed-scalar field mutation.  All compiler and dynamic operation
facts are reconstructed; `fieldTyped` remains the explicit source/runtime
descriptor-layout invariant. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_scalarField_of_validated_step
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation) targetStore
      targetLocals targetCode witness source target)
    (fieldTyped : ConcreteScalarFieldMutationTyped context sourceRuntime
      sourceEnv objectId fieldId slotIndex byteOffset)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees⟩ :=
    related.core.validation
  obtain ⟨fieldKind, objectCompiled, fieldCompiled, _annotationFound,
      _scalarSupported⟩ := validated.sset_compiler agrees
  obtain ⟨location, cell, semantic, field, resultRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq⟩ :=
    related.core.core.focus.sset_source_of_step sourceStep
  let supported : ScalarFieldEffectSupported context sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      continuation resultRuntime :=
    .sset sourceRuntime resultRuntime sourceEnv objectId fieldId slotIndex
      byteOffset type continuation location cell semantic field fieldKind
      objectCompiled fieldCompiled objectLookup fieldLookup updated found live
      objectEq (fun objectRelated descriptorFound =>
        fieldTyped fieldCompiled objectLookup found live objectEq objectRelated
          descriptorFound)
  obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
    related.advance_scalarField_of_step supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath, next⟩

end ClosedMutation

/-- Return validation identifies the residual local kind and the exact
compiler-level compatibility check against the active result ABI. -/
theorem ConcreteStructuredValidationFocus.return_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expected : Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {result : Lean.FVarId}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expected) facts sharing (.return result)) :
    ∃ actual,
      Fir.Wasm.findLocalKind? locals result = some actual ∧
        actual.leanCompatible expected = true := by
  have supported := validated.supported
  cases actualFound : Fir.Wasm.findLocalKind? locals result with
  | none =>
      simp [Fir.Wasm.supportedCodeWithJoins, actualFound] at supported
  | some actual =>
      refine ⟨actual, rfl, ?_⟩
      simpa [Fir.Wasm.supportedCodeWithJoins, actualFound] using supported

/-- Residual production validation plus source value typing closes return
admission at exactly the compiler's object-family calling boundary.

The validator supplies `leanCompatible`; the semantic premise supplies the
strict value-shape information needed when that compatibility runs opposite
to `AbiKind.refines`.  Thus no arbitrary `.tobject` is reinterpreted as a
heap-only `.object` or immediate-only `.tagged` value. -/
theorem ConcreteStructuredAlignedValidationState.admit_return
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    (validated : ConcreteStructuredAlignedValidationState program context
      expectedResult (.return result))
    (resultSemantic :
      ∀ {sourceValue}, lookup sourceEnv result = some sourceValue →
        SemanticValueAtAbi expectedResult sourceValue) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv 0 (.return result) := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, focus, agrees⟩ :=
    validated
  obtain ⟨actualResult, resultFound, resultCompatible⟩ := focus.return_eq
  exact .ret (agrees resultFound) resultCompatible resultSemantic

/-- A validated jump retains the selected join declaration, result
compatibility, and the complete path-sensitive argument check. -/
theorem ConcreteStructuredValidationFocus.jump_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {fvarId : Lean.FVarId}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.jmp fvarId args)) :
    ∃ decl,
      Fir.Wasm.findJoinPoint? joins fvarId = some decl ∧
        Fir.Wasm.resultKindCompatible
            (Fir.Wasm.abiValueKind? decl.type) expectedResult = true ∧
        Fir.Wasm.supportedJumpArgs locals facts sharing decl args = true := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  cases found : Fir.Wasm.findJoinPoint? joins fvarId with
  | none =>
      simp [found] at supported
  | some decl =>
      refine ⟨decl, rfl, ?_⟩
      simpa [found, Bool.and_eq_true] using supported

/-- Introducing a join validates both its body under the extended join/local
state and its continuation under the extended join state. -/
theorem ConcreteStructuredValidationFocus.join_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {decl : Lean.Compiler.LCNF.FunDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.jp decl continuation)) :
    ∃ bodyLocals,
      decl.params.foldlM (init := locals) (fun locals param => do
          let kind ← Fir.Wasm.joinParamAbiKind? decl param
          some (Fir.Wasm.insertLocal locals param.fvarId kind)) =
          some bodyLocals ∧
        Fir.Wasm.abiTypeKnown decl.type = true ∧
        Fir.Wasm.resultKindCompatible (Fir.Wasm.abiValueKind? decl.type)
            expectedResult = true ∧
        ConcreteStructuredValidationFocus program
          ((decl.fvarId, decl) :: joins) bodyLocals
          (Fir.Wasm.abiValueKind? decl.type) [] [] decl.value ∧
        ConcreteStructuredValidationFocus program
          ((decl.fvarId, decl) :: joins) locals expectedResult facts sharing
          continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  cases bodyFound : decl.params.foldlM (init := locals)
      (fun locals param => do
        let kind ← Fir.Wasm.joinParamAbiKind? decl param
        some (Fir.Wasm.insertLocal locals param.fvarId kind)) with
  | none =>
      rw [bodyFound] at supported
      simp at supported
  | some bodyLocals =>
      rw [bodyFound] at supported
      simp only [Bool.and_eq_true] at supported
      exact ⟨bodyLocals, rfl,
        supported.1.1.1, supported.1.1.2,
        ⟨supported.1.2⟩, ⟨supported.2⟩⟩

/-- Case validation exposes the discriminator mode and the executable
all-alternatives judgment from which the selected branch is recovered. -/
theorem ConcreteStructuredValidationFocus.cases_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.cases cases)) :
    ∃ discrKind mode,
      Fir.Wasm.findLocalKind? locals cases.discr = some discrKind ∧
        Fir.Wasm.supportedCaseDiscriminatorMode? discrKind = some mode ∧
        Fir.Wasm.abiTypeKnown cases.resultType = true ∧
        Fir.Wasm.resultKindCompatible
            (Fir.Wasm.abiValueKind? cases.resultType) expectedResult = true ∧
        Fir.Wasm.supportedAltsWithJoins program joins locals expectedResult
          facts sharing mode cases.discr cases.alts.toList = true := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  simp only [Bool.and_eq_true] at supported
  cases discrFound : Fir.Wasm.findLocalKind? locals cases.discr with
  | none =>
      have impossible := supported.2
      simp [discrFound] at impossible
  | some discrKind =>
      cases modeFound :
          Fir.Wasm.supportedCaseDiscriminatorMode? discrKind with
      | none =>
          have impossible := supported.2
          simp [discrFound, modeFound] at impossible
      | some mode =>
          refine ⟨discrKind, mode, rfl, modeFound,
            supported.1.1, supported.1.2, ?_⟩
          simpa [discrFound, modeFound] using supported.2

/-- A validated constructor alternative selected from a validated case chain
inherits the inserted discriminator fact used by guarded joins. -/
theorem ConcreteStructuredValidationFocus.constructorAlt
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.cases cases))
    {info : Lean.Compiler.LCNF.CtorInfo}
    {selected : Lean.Compiler.LCNF.Code .impure}
    (member : Lean.Compiler.LCNF.Alt.ctorAlt info selected ∈ cases.alts) :
    ∃ mode,
      Fir.Wasm.caseConstructorTagFits mode info = true ∧
        ConcreteStructuredValidationFocus program joins locals expectedResult
          (Fir.Wasm.insertSupportedCaseFact facts cases.discr info.cidx) sharing
          selected := by
  obtain ⟨discrKind, mode, _discrFound, _modeFound, _resultKnown,
      _resultCompatible, alternatives⟩ := validated.cases_eq
  have selectedSupported := Fir.Wasm.supportedAltWithJoins_of_mem alternatives
    (by simpa using member)
  simp only [Fir.Wasm.supportedAltWithJoins] at selectedSupported
  simp only [Bool.and_eq_true] at selectedSupported
  exact ⟨mode, selectedSupported.1, ⟨selectedSupported.2⟩⟩

/-- A validated default alternative erases any stale discriminator fact. -/
theorem ConcreteStructuredValidationFocus.defaultAlt
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.cases cases))
    {selected : Lean.Compiler.LCNF.Code .impure}
    (member : Lean.Compiler.LCNF.Alt.default selected ∈ cases.alts) :
    ConcreteStructuredValidationFocus program joins locals expectedResult
      (Fir.Wasm.eraseSupportedCaseFact facts cases.discr) sharing selected := by
  obtain ⟨_discrKind, mode, _discrFound, _modeFound, _resultKnown,
      _resultCompatible, alternatives⟩ := validated.cases_eq
  have selectedSupported := Fir.Wasm.supportedAltWithJoins_of_mem alternatives
    (by simpa using member)
  simp only [Fir.Wasm.supportedAltWithJoins] at selectedSupported
  exact ⟨selectedSupported⟩

/-- A successful constructor lookup identifies the exact constructor
alternative in the source table. -/
private theorem exists_ctorAlt_mem_of_findCtorAlt
    {tag : Nat}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {selected : Lean.Compiler.LCNF.Code .impure}
    (found : findCtorAlt tag alts = some selected) :
    ∃ info, Lean.Compiler.LCNF.Alt.ctorAlt info selected ∈ alts := by
  induction alts with
  | nil => simp [findCtorAlt] at found
  | cons alt rest ih =>
      cases alt with
      | alt ctorName params code impossible => nomatch impossible
      | ctorAlt info code _ =>
          simp only [findCtorAlt] at found
          split at found
          · have codeEq : code = selected := Option.some.inj found
            subst selected
            exact ⟨info, List.mem_cons_self⟩
          · obtain ⟨selectedInfo, member⟩ := ih found
            exact ⟨selectedInfo, List.mem_cons_of_mem _ member⟩
      | default code =>
          simp only [findCtorAlt] at found
          obtain ⟨selectedInfo, member⟩ := ih found
          exact ⟨selectedInfo, List.mem_cons_of_mem _ member⟩

/-- A successful default lookup identifies the exact default alternative in
the source table. -/
private theorem default_mem_of_findDefaultAlt
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {selected : Lean.Compiler.LCNF.Code .impure}
    (found : findDefaultAlt alts = some selected) :
    Lean.Compiler.LCNF.Alt.default selected ∈ alts := by
  induction alts with
  | nil => simp [findDefaultAlt] at found
  | cons alt rest ih =>
      cases alt with
      | alt ctorName params code impossible => nomatch impossible
      | ctorAlt info code _ =>
          simp only [findDefaultAlt] at found
          exact List.mem_cons_of_mem _ (ih found)
      | default code =>
          simp only [findDefaultAlt, Option.some.injEq] at found
          subst selected
          exact List.mem_cons_self

/-- Every successful source case selection is either the exact constructor
arm or the exact default arm present in the source table. -/
private theorem selected_alt_mem_of_chooseAlt
    {tag : Nat}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {selected : Lean.Compiler.LCNF.Code .impure}
    (chosen : chooseAlt tag alts = some selected) :
    (∃ info, Lean.Compiler.LCNF.Alt.ctorAlt info selected ∈ alts) ∨
      Lean.Compiler.LCNF.Alt.default selected ∈ alts := by
  unfold chooseAlt at chosen
  cases found : findCtorAlt tag alts with
  | some code =>
      have codeEq : code = selected := by simpa [found] using chosen
      subst selected
      exact .inl (exists_ctorAlt_mem_of_findCtorAlt found)
  | none =>
      have defaultFound : findDefaultAlt alts = some selected := by
        simpa [found] using chosen
      exact .inr (default_mem_of_findDefaultAlt defaultFound)

/-- Executable validation follows the exact branch chosen by the source
interpreter. Constructor selection inserts the discriminator fact used by
guarded joins; default selection erases any stale fact. -/
theorem ConcreteStructuredValidationState.selectedCase
    {program : Fir.LeanIR.ImpureProgram}
    {functionResult : Fir.Wasm.AbiKind}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {selected : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationState program functionResult
      (.cases cases))
    (sourceResult : SourceCaseResult sourceRuntime sourceEnv cases selected) :
    ConcreteStructuredValidationState program functionResult selected := by
  obtain ⟨joins, locals, facts, sharing, focus⟩ := validated
  obtain ⟨_discrValue, tag, _found, _tagged, chosen⟩ := sourceResult
  rcases selected_alt_mem_of_chooseAlt chosen with constructor | default
  · obtain ⟨info, member⟩ := constructor
    obtain ⟨_mode, _fits, selectedFocus⟩ := focus.constructorAlt
      (by simpa using member)
    exact ⟨joins, locals,
      Fir.Wasm.insertSupportedCaseFact facts cases.discr info.cidx,
      sharing, selectedFocus⟩
  · exact ⟨joins, locals,
      Fir.Wasm.eraseSupportedCaseFact facts cases.discr,
      sharing, focus.defaultAlt (by simpa using default)⟩

/-- Aligned executable validation follows the selected source branch while
retaining the unchanged agreement between the validator's local row and the
compiler context.  Case selection changes only discriminator facts. -/
theorem ConcreteStructuredAlignedValidationState.selectedCase
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : Fir.Wasm.AbiKind}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {selected : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.cases cases))
    (sourceResult : SourceCaseResult sourceRuntime sourceEnv cases selected) :
    ConcreteStructuredAlignedValidationState program context functionResult
      selected := by
  obtain ⟨joins, locals, facts, sharing, focus, agrees⟩ := validated
  obtain ⟨_discrValue, tag, _found, _tagged, chosen⟩ := sourceResult
  rcases selected_alt_mem_of_chooseAlt chosen with constructor | default
  · obtain ⟨info, member⟩ := constructor
    obtain ⟨_mode, _fits, selectedFocus⟩ := focus.constructorAlt
      (by simpa using member)
    exact ⟨joins, locals,
      Fir.Wasm.insertSupportedCaseFact facts cases.discr info.cidx,
      sharing, selectedFocus, agrees⟩
  · exact ⟨joins, locals,
      Fir.Wasm.eraseSupportedCaseFact facts cases.discr,
      sharing, focus.defaultAlt (by simpa using default), agrees⟩

/-- Reassemble a closed active-code state when structured case testing has
pushed target-only label frames.  Source caller validation is unchanged;
production stack/resource agreement grows by the matching case protocol. -/
private theorem ConcreteStructuredValidatedCodeOutcome.withCaseSuccessor
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {selected : Lean.Compiler.LCNF.Code .impure}
    {targetLocals nextLocals : Wasm.Locals}
    {targetCode selectedTarget targetSuffix : Wasm.Program}
    {belowStack : List Wasm.Value}
    {testCount : Nat}
    {source sourceAfter : MachineState}
    {target targetAfter : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (nextCore : ConcreteStructuredCodeCoreRel program context sourceModule
      sourceFunction externals (List.replicate testCount none ++ labels)
      entryRuntime entryStore entryWitness
      functionResult callerExpectedResult facts remainingBytes sourceRuntime
      sourceEnv selected targetStore nextLocals selectedTarget witness
      sourceAfter targetAfter)
    (nextValidation : ConcreteStructuredAlignedValidationState program context
      functionResult selected)
    (sourceFramesEq : sourceAfter.frames = source.frames)
    (targetFramesEq : targetAfter.frames =
      structuredWasmCaseLabels belowStack targetSuffix testCount ++
        target.frames) :
    ConcreteStructuredValidatedCodeOutcome program context functionCode
      sourceModule sourceFunction targetModule hosts spec externals
      (List.replicate testCount none ++ labels)
      entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv selected targetStore nextLocals
      selectedTarget witness sourceAfter targetAfter := by
  let pushedSupported := ConcreteStructuredSupportedFrameStack.case
    (belowStack := belowStack) (targetRest := targetSuffix)
    (testCount := testCount) related.frames.supported
  let pushedResources := ConcreteStructuredSuspendedResourceStack.case
    (belowStack := belowStack) (targetRest := targetSuffix)
    (testCount := testCount) related.core.core.resources.suspended
  have pushedAgrees : pushedSupported.Agrees pushedResources :=
    .case related.frames.supported related.core.core.resources.suspended
      related.agrees
  obtain ⟨spine, aligned⟩ := related.validationAgrees
  have pushedValidationAgrees :
      ConcreteStructuredValidationAgrees pushedAgrees
        related.frames.validation :=
    ⟨spine, .case aligned⟩
  obtain ⟨nextSupported, nextAgrees⟩ := pushedAgrees.reindex
    sourceFramesEq targetFramesEq nextCore.resources.suspended
  have nextFrameValidation :
      ConcreteStructuredSuspendedValidation program functionResult
        callerExpectedResult sourceAfter.frames := by
    rw [sourceFramesEq]
    exact related.frames.validation
  have nextValidationAgrees :
      ConcreteStructuredValidationAgrees nextAgrees nextFrameValidation :=
    pushedValidationAgrees.reindex sourceFramesEq targetFramesEq nextAgrees
      nextFrameValidation
  exact ⟨related.contextCaches, ⟨nextCore, nextValidation⟩,
    ⟨nextSupported, nextFrameValidation⟩, nextAgrees,
    nextValidationAgrees⟩

/-- A compiler-erased default-only case is a closed zero-target-step
transition and strictly decreases the structured source rank. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_defaultOnlyCase_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {selected : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (supported : DefaultOnlyCaseSupported sourceRuntime sourceEnv cases selected)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 0 target
        target ∧
      ConcreteStructuredValidatedCodeOutcome program context functionCode
        sourceModule sourceFunction targetModule hosts spec externals labels
        entryRuntime entryStore entryWitness functionResult callerExpectedResult
        facts remainingBytes sourceRuntime sourceEnv selected targetStore
        targetLocals targetCode witness sourceAfter target ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source := by
  have sourceResult := related.core.core.focus.defaultOnlyCaseResult_of_step
    supported sourceStep
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.defaultOnlyCase supported) (by omega)
  obtain ⟨targetPath, sourceFramesEq, nextCore, rank⟩ :=
    pointwise.advance_defaultOnlyCase_of_step supported sourceStep
  have validatedCore : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv selected targetStore targetLocals targetCode
      witness sourceAfter target :=
    ⟨nextCore, related.core.validation.selectedCase sourceResult⟩
  exact ⟨targetPath,
    related.withSuccessor validatedCore sourceFramesEq rfl, rank⟩

section ClosedTestedCases

variable
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {admittedSelected : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}

/-- Normalized object cases preserve closed validation and push one matching
target-only case label per executed constructor test. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_objectCases_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (supported : ObjectConstructorCasesSupported context sourceRuntime
      sourceEnv cases admittedSelected)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ testCount targetAfter selected selectedTarget,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          (5 * testCount) target targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals
          (List.replicate testCount none ++ labels)
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          selected targetStore
          { targetLocals with values := targetLocals.values } selectedTarget
          witness sourceAfter targetAfter ∧
        (5 * testCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨chosen, sourceResult, sourceAfterEq⟩ :=
    related.core.core.focus.caseResult_of_step sourceStep
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.objectCases supported) (by omega)
  obtain ⟨testCount, targetAfter, selected, selectedTarget, targetSuffix,
      targetPath, sourceFramesEq, targetFramesEq, nextCore, zeroRank⟩ :=
    pointwise.advance_objectCases_of_step supported sourceStep
  have selectedEq : selected = chosen := by
    have controlEq := nextCore.focus.sourceControlEq
    rw [sourceAfterEq] at controlEq
    have chosenEq : chosen = selected := by
      simpa using Control.code.inj controlEq
    exact chosenEq.symm
  subst selected
  exact ⟨testCount, targetAfter, chosen, selectedTarget, targetPath,
    related.withCaseSuccessor nextCore
      (related.core.validation.selectedCase sourceResult)
      sourceFramesEq targetFramesEq,
    zeroRank⟩

/-- Normalized scalar `UInt8` cases have the same closed branch semantics;
their resident comparisons cost four target steps per test. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_scalarUInt8Cases_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (supported : ScalarUInt8CasesSupported context sourceRuntime sourceEnv cases
      admittedSelected)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ testCount targetAfter selected selectedTarget,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          (4 * testCount) target targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals
          (List.replicate testCount none ++ labels)
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          selected targetStore
          { targetLocals with values := targetLocals.values } selectedTarget
          witness sourceAfter targetAfter ∧
        (4 * testCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨chosen, sourceResult, sourceAfterEq⟩ :=
    related.core.core.focus.caseResult_of_step sourceStep
  have pointwise := related.toPointwise
    (ConcreteStructuredCodeStepAdmission.scalarUInt8Cases supported) (by omega)
  obtain ⟨testCount, targetAfter, selected, selectedTarget, targetSuffix,
      targetPath, sourceFramesEq, targetFramesEq, nextCore, zeroRank⟩ :=
    pointwise.advance_scalarUInt8Cases_of_step supported sourceStep
  have selectedEq : selected = chosen := by
    have controlEq := nextCore.focus.sourceControlEq
    rw [sourceAfterEq] at controlEq
    have chosenEq : chosen = selected := by
      simpa using Control.code.inj controlEq
    exact chosenEq.symm
  subst selected
  exact ⟨testCount, targetAfter, chosen, selectedTarget, targetPath,
    related.withCaseSuccessor nextCore
      (related.core.validation.selectedCase sourceResult)
      sourceFramesEq targetFramesEq,
    zeroRank⟩

end ClosedTestedCases

/-- Normalized final-LCNF case-table shape used by source interpretation and
production lowering: zero or more constructor arms followed by at most one
default arm.  Constructor tag bounds remain representation-specific and are
recovered from executable validation below. -/
inductive ConcreteStructuredCaseAltsNormalized :
    List (Lean.Compiler.LCNF.Alt .impure) → Prop where
  | nil : ConcreteStructuredCaseAltsNormalized []
  | default (code : Lean.Compiler.LCNF.Code .impure) :
      ConcreteStructuredCaseAltsNormalized [.default code]
  | ctor
      (rest : ConcreteStructuredCaseAltsNormalized alternatives) :
      ConcreteStructuredCaseAltsNormalized
        (.ctorAlt info code :: alternatives)

/-- Executable object-mode validation supplies every constructor-tag bound
needed by the existing normalized object-chain theorem. -/
theorem ConcreteStructuredCaseAltsNormalized.objectSupported_of_validation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {discr : Lean.FVarId}
    {alternatives : List (Lean.Compiler.LCNF.Alt .impure)}
    (normalized : ConcreteStructuredCaseAltsNormalized alternatives)
    (validated : Fir.Wasm.supportedAltsWithJoins program joins locals
      expectedResult facts sharing .objectTag discr alternatives = true) :
    ObjectConstructorCaseAltsSupported alternatives := by
  induction normalized with
  | nil => exact .nil
  | default code => exact .default code
  | ctor rest ih =>
      simp only [Fir.Wasm.supportedAltsWithJoins, Bool.and_eq_true] at validated
      exact .ctor validated.1.1 (ih validated.2)

/-- Executable scalar-mode validation supplies the corresponding `UInt8`
constructor-tag bounds. -/
theorem ConcreteStructuredCaseAltsNormalized.scalarSupported_of_validation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {discr : Lean.FVarId}
    {alternatives : List (Lean.Compiler.LCNF.Alt .impure)}
    (normalized : ConcreteStructuredCaseAltsNormalized alternatives)
    (validated : Fir.Wasm.supportedAltsWithJoins program joins locals
      expectedResult facts sharing .scalarUInt8 discr alternatives = true) :
    ScalarUInt8CaseAltsSupported alternatives := by
  induction normalized with
  | nil => exact .nil
  | default code => exact .default code
  | ctor rest ih =>
      simp only [Fir.Wasm.supportedAltsWithJoins, Bool.and_eq_true] at validated
      exact .ctor validated.1.1 (ih validated.2)

/-- A successful production local lookup exposes the exact compiler local
kind used by case-discriminator mode selection. -/
private theorem findLocalKind?_of_getLocal
    {context : Fir.Wasm.Context} {fvarId : Lean.FVarId} {kind : AbiKind}
    (compiled : Fir.Wasm.getLocal context fvarId =
      .ok (.localGet fvarId, kind)) :
    Fir.Wasm.findLocalKind? context.localKinds fvarId = some kind := by
  unfold Fir.Wasm.getLocal at compiled
  cases found : Fir.Wasm.findLocalKind? context.localKinds fvarId with
  | none => simp [found] at compiled
  | some actual =>
      have actualEq : actual = kind := by simpa [found] using compiled
      subst actual
      rfl

/-- Source-level safety boundary for a currently active case table.

This is an invariant on final-LCNF syntax, the source runtime, and the compiler
context, not a translation certificate: it contains no target module,
instruction path, numeric local, refinement witness, or future execution.
Executable residual validation supplies result compatibility and every static
constructor-tag bound.  The phase bridge supplies only normalized alternative
order, the two currently proved discriminator representations, and the
semantic range law for object tags.

The normalization field remains explicit until the final-LCNF phase interface
exports the missing theorem recorded by
`FIR-BUG-impure-case-table-selector-determinism`. -/
structure ConcreteStructuredCaseSafeAt
    (context : Fir.Wasm.Context)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (cases : Lean.Compiler.LCNF.Cases .impure) : Prop where
  normalized : ConcreteStructuredCaseAltsNormalized cases.alts.toList
  discriminator :
    Fir.Wasm.getLocal context cases.discr =
        .ok (.localGet cases.discr, .tobject) ∨
      Fir.Wasm.getLocal context cases.discr =
        .ok (.localGet cases.discr, .uint8)
  objectTagsFit :
    ∀ {sourceObject : Value} {actualTag : Nat},
      lookupValue sourceEnv cases.discr = .ok sourceObject →
      getTag sourceRuntime sourceObject = .ok actualTag →
      actualTag < UInt32.size

/-- Residual executable validation turns the minimal source case invariant
into the existing production case family.  In particular, compiler-local
agreement and discriminator mode are derived here rather than stored in a
per-step certificate. -/
theorem ConcreteStructuredValidatedCodeCoreRel.productionCasesSupported_of_caseSafe
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv (.cases cases) targetStore targetLocals targetCode
      witness source target)
    (sourceSafe : ConcreteStructuredCaseSafeAt context sourceRuntime sourceEnv
      cases) :
    ∀ {selected : Lean.Compiler.LCNF.Code .impure},
      ProductionCasesSupported context sourceRuntime sourceEnv cases selected := by
  intro selected
  obtain ⟨joins, locals, validatorFacts, sharing, validated, agrees⟩ :=
    related.validation
  obtain ⟨discrKind, mode, discrFound, modeFound, _resultKnown,
      _resultCompatible, alternatives⟩ := validated.cases_eq
  have discrCompiled := agrees discrFound
  unfold ProductionCasesSupported
  rcases sourceSafe.discriminator with objectCompiled | scalarCompiled
  · have discrKindEq : discrKind = .tobject := by
      have pairEq := Except.ok.inj (discrCompiled.symm.trans objectCompiled)
      exact congrArg Prod.snd pairEq
    subst discrKind
    have modeEq : mode = .objectTag := by
      simpa [Fir.Wasm.supportedCaseDiscriminatorMode?] using modeFound.symm
    subst mode
    have contextFound := findLocalKind?_of_getLocal objectCompiled
    have contextMode :
        Fir.Wasm.caseDiscriminatorMode context cases.discr = .objectTag := by
      simp [Fir.Wasm.caseDiscriminatorMode, contextFound]
    exact Or.inr (Or.inl ⟨
      sourceSafe.normalized.objectSupported_of_validation alternatives,
      contextMode, objectCompiled, sourceSafe.objectTagsFit⟩)
  · have discrKindEq : discrKind = .uint8 := by
      have pairEq := Except.ok.inj (discrCompiled.symm.trans scalarCompiled)
      exact congrArg Prod.snd pairEq
    subst discrKind
    have modeEq : mode = .scalarUInt8 := by
      simpa [Fir.Wasm.supportedCaseDiscriminatorMode?] using modeFound.symm
    subst mode
    have contextFound := findLocalKind?_of_getLocal scalarCompiled
    have contextMode :
        Fir.Wasm.caseDiscriminatorMode context cases.discr = .scalarUInt8 := by
      simp [Fir.Wasm.caseDiscriminatorMode, contextFound]
    exact Or.inr (Or.inr ⟨
      sourceSafe.normalized.scalarSupported_of_validation alternatives,
      contextMode, scalarCompiled⟩)

/-- Outcome-level spelling of the case admission bridge.  Suspended-frame
validation is irrelevant to classifying the current case node, so the proof
delegates to the residual validated code core. -/
theorem ConcreteStructuredValidatedCodeOutcome.productionCasesSupported_of_caseSafe
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (sourceSafe : ConcreteStructuredCaseSafeAt context sourceRuntime sourceEnv
      cases) :
    ∀ {selected : Lean.Compiler.LCNF.Code .impure},
      ProductionCasesSupported context sourceRuntime sourceEnv cases selected :=
  related.core.productionCasesSupported_of_caseSafe sourceSafe

/-- One source case step satisfying the source-level case invariant has a
finite concrete Wasm path and preserves the closed validated relation.

The existential presentation deliberately forgets whether the path used the
zero-step default protocol, five-step object tests, or four-step `UInt8`
tests.  The specialized theorems retain those exact costs; this theorem is the
uniform interface needed by the module-wide one-step dispatcher.  If the
target path is empty, the source control rank strictly decreases. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_cases_of_source_safe_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (sourceSafe : ConcreteStructuredCaseSafeAt context sourceRuntime sourceEnv
      cases)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetSteps targetAfter selected selectedTarget nextLabels,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetSteps target targetAfter ∧
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals
          nextLabels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          selected targetStore
          { targetLocals with values := targetLocals.values } selectedTarget
          witness sourceAfter targetAfter ∧
        (targetSteps = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨selected, _sourceResult, _sourceAfterEq⟩ :=
    related.core.core.focus.caseResult_of_step sourceStep
  rcases related.productionCasesSupported_of_caseSafe
      (selected := selected) sourceSafe with defaultOnly | tested
  · obtain ⟨targetPath, next, rank⟩ :=
      related.advance_defaultOnlyCase_of_step defaultOnly sourceStep
    refine ⟨0, target, selected, targetCode, labels, targetPath, ?_,
      fun _ => rank⟩
    simpa using next
  · rcases tested with objectCases | scalarCases
    · obtain ⟨testCount, targetAfter, selected, selectedTarget,
          targetPath, next, zeroRank⟩ :=
        related.advance_objectCases_of_step objectCases sourceStep
      exact ⟨5 * testCount, targetAfter, selected, selectedTarget,
        List.replicate testCount none ++ labels, targetPath, next, zeroRank⟩
    · obtain ⟨testCount, targetAfter, selected, selectedTarget,
          targetPath, next, zeroRank⟩ :=
        related.advance_scalarUInt8Cases_of_step scalarCases sourceStep
      exact ⟨4 * testCount, targetAfter, selected, selectedTarget,
        List.replicate testCount none ++ labels, targetPath, next, zeroRank⟩

/-- Finite-header safety needed only by a nonpersistent reference-count
increment.  This is a source runtime invariant; successful unbounded source
execution alone does not imply that the updated count fits the wasm32 header.
-/
def ConcreteStructuredIncrementHeadroomAt
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (objectId : Lean.FVarId) (amount : Nat) : Prop :=
  ∀ (sourceObject : Value) (location : Location) (cell : HeapCell),
    lookupValue sourceEnv objectId = .ok sourceObject →
      sourceObject = .object (.heap location) →
        findCell? sourceRuntime.heap location = some cell →
          cell.rc + amount < UInt32.size

/-- Source/compiler facts that make one residual validated code node
admissible.

This judgment is deliberately weaker than
`ConcreteStructuredCodeStepAdmission`: it stores no compiled-local equation,
semantic heap update, selected case arm, target path, refinement witness,
allocation budget, successor admission, or termination evidence.  Residual
production validation recovers compiler equations, and the successful source
step recovers dynamic effects.  The remaining fields are exactly the phase
typing and semantic operation-domain facts that those two inputs cannot
manufacture; finite concrete resources are stated separately. -/
inductive ConcreteStructuredSourceAdmissionSafeAt
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (externals : ExternalImpl)
    (expectedResult : AbiKind)
    (facts : ReuseCapacityFacts)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (source : MachineState) :
    Lean.Compiler.LCNF.Code .impure → Prop where
  | ret
      {result : Lean.FVarId}
      (safe : ConcreteStructuredReturnValueSafeAt expectedResult source) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source (.return result)
  | directLet
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (supported : ReuseBudgetedDirectSupported context facts decl) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.let decl continuation)
  | pureExternal
      {nextRuntime : RuntimeState}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {sourceValue : Value}
      {stepCost : Nat}
      (supported : PureExternalSupported context externals sourceRuntime
        sourceEnv decl continuation nextRuntime sourceValue stepCost) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.let decl continuation)
  | directCall
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (site : DirectInternalCallSite context decl sourceEnv) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.let decl continuation)
  | saturatedCall
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (site : SaturatedClosureCallSite context decl sourceEnv)
      (resolution : SaturatedClosureCallResolution context sourceRuntime site) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.let decl continuation)
  | lazy
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      {declaration : Lean.Name}
      {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
      {resultKind : AbiKind}
      (call : LazyCacheCallSupported context decl declaration
        sourceDeclaration resultKind)
      (generated : LazyCacheGeneratedEnvironment context sourceModule)
      (path : ConcreteStructuredLazyReadyAdmission context sourceModule call
        generated sourceRuntime) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.let decl continuation)
  | cases
      {cases : Lean.Compiler.LCNF.Cases .impure}
      (safe : ConcreteStructuredCaseSafeAt context sourceRuntime sourceEnv
        cases) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source (.cases cases)
  | incPersistent
      {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
      {continuation : Lean.Compiler.LCNF.Code .impure} :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.inc objectId amount check true continuation)
  | incOrdinary
      {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
      {continuation : Lean.Compiler.LCNF.Code .impure} :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.inc objectId amount check false continuation)
  | decPersistent
      {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
      {objectFields? : Option Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure} :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.dec objectId amount check true objectFields? continuation)
  | decOrdinary
      {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
      {objectFields? : Option Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure} :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.dec objectId amount check false objectFields? continuation)
  | del
      {objectId : Lean.FVarId}
      {continuation : Lean.Compiler.LCNF.Code .impure} :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.del objectId continuation)
  | setTag
      {objectId : Lean.FVarId} {tag : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure} :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.setTag objectId tag continuation)
  | objectFieldFVar
      {objectId fieldId : Lean.FVarId} {index : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (fieldTyped : ConcreteObjectFieldFVarTyped context sourceEnv objectId
        fieldId index) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.oset objectId index (.fvar fieldId) continuation)
  | objectFieldErased
      {objectId : Lean.FVarId} {index : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (fieldTyped : ConcreteObjectFieldKindAligned sourceEnv objectId index
        .erased) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.oset objectId index .erased continuation)
  | usizeField
      {objectId fieldId : Lean.FVarId} {index : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure} :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.uset objectId index fieldId continuation)
  | scalarField
      {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
      {type : Lean.Expr}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (fieldTyped : ConcreteScalarFieldMutationTyped context sourceRuntime
        sourceEnv objectId fieldId slotIndex byteOffset) :
      ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
        expectedResult facts sourceRuntime sourceEnv source
        (.sset objectId slotIndex byteOffset fieldId type continuation)

/-- The compatibility arm of schema admission excludes exactly the two object
field shapes whose legacy proofs quantify over arbitrary witnesses. -/
def ConcreteStructuredSchemaLegacyCode :
    Lean.Compiler.LCNF.Code .impure → Prop
  | .oset _ _ (.fvar _) _ => False
  | .oset _ _ .erased _ => False
  | _ => True

/-- Source-admission boundary used while constructor-schema provenance is
threaded into the global simulation.

All already-proved non-field source facts pass through `legacy`. The two
object-field cases instead retain final-LCNF schema typing and make no claim
about an arbitrary refinement witness. Keeping this as a thin migration layer
lets the global relation change independently of the concrete writer and the
other current-node admission proofs. -/
inductive ConcreteStructuredSchemaSourceAdmissionSafeAt
    (schema : ConstructorSchema)
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (externals : ExternalImpl)
    (expectedResult : AbiKind)
    (facts : ReuseCapacityFacts)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (source : MachineState) :
    Lean.Compiler.LCNF.Code .impure → Prop where
  | legacy
      {code : Lean.Compiler.LCNF.Code .impure}
      (safe : ConcreteStructuredSourceAdmissionSafeAt context sourceModule
        externals expectedResult facts sourceRuntime sourceEnv source code)
      (eligible : ConcreteStructuredSchemaLegacyCode code) :
      ConcreteStructuredSchemaSourceAdmissionSafeAt schema context sourceModule
        externals expectedResult facts sourceRuntime sourceEnv source code
  | objectFieldFVar
      {objectId fieldId : Lean.FVarId} {index : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (fieldTyped : schema.ObjectFieldFVarTyped context sourceEnv objectId
        fieldId index) :
      ConcreteStructuredSchemaSourceAdmissionSafeAt schema context sourceModule
        externals expectedResult facts sourceRuntime sourceEnv source
        (.oset objectId index (.fvar fieldId) continuation)
  | objectFieldErased
      {objectId : Lean.FVarId} {index : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (fieldTyped : schema.ObjectFieldKindAt sourceEnv objectId index .erased) :
      ConcreteStructuredSchemaSourceAdmissionSafeAt schema context sourceModule
        externals expectedResult facts sourceRuntime sourceEnv source
        (.oset objectId index .erased continuation)

/-- Current-node admission after source schema typing has been combined with
residual compiler validation.

`legacy` preserves every existing operation proof. The two schema cases have
zero allocation cost and postpone descriptor alignment until the active
simulation witness is available to the dispatcher. -/
inductive ConcreteStructuredSchemaCodeStepAdmission
    (schema : ConstructorSchema)
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (externals : ExternalImpl)
    (expectedResult : AbiKind) :
    ReuseCapacityFacts → RuntimeState → Env → Nat →
      Lean.Compiler.LCNF.Code .impure → Prop where
  | legacy
      {facts : ReuseCapacityFacts}
      {sourceRuntime : RuntimeState}
      {sourceEnv : Env}
      {requiredBytes : Nat}
      {code : Lean.Compiler.LCNF.Code .impure}
      (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
        externals expectedResult facts sourceRuntime sourceEnv requiredBytes
        code)
      (eligible : ConcreteStructuredSchemaLegacyCode code) :
      ConcreteStructuredSchemaCodeStepAdmission schema context sourceModule
        externals expectedResult facts sourceRuntime sourceEnv requiredBytes
        code
  | objectFieldFVar
      {facts : ReuseCapacityFacts}
      {sourceRuntime : RuntimeState}
      {sourceEnv : Env}
      {objectId fieldId : Lean.FVarId} {index : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (fieldTyped : schema.ObjectFieldFVarTyped context sourceEnv objectId
        fieldId index) :
      ConcreteStructuredSchemaCodeStepAdmission schema context sourceModule
        externals expectedResult facts sourceRuntime sourceEnv 0
        (.oset objectId index (.fvar fieldId) continuation)
  | objectFieldErased
      {facts : ReuseCapacityFacts}
      {sourceRuntime : RuntimeState}
      {sourceEnv : Env}
      {objectId : Lean.FVarId} {index : Nat}
      {continuation : Lean.Compiler.LCNF.Code .impure}
      (fieldTyped : schema.ObjectFieldKindAt sourceEnv objectId index .erased) :
      ConcreteStructuredSchemaCodeStepAdmission schema context sourceModule
        externals expectedResult facts sourceRuntime sourceEnv 0
        (.oset objectId index .erased continuation)

/-- Schema admission classifies the current code focus into the one family
that evolves constructor provenance or a proof that no direct schema shape is
present.  This is a source/compiler classification; it inspects no target
state or refinement witness. -/
theorem ConcreteStructuredSchemaCodeStepAdmission.sourceSchemaCases
    {schema : ConstructorSchema}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {requiredBytes : Nat}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    (admitted : ConcreteStructuredSchemaCodeStepAdmission schema context
      sourceModule externals expectedResult facts sourceRuntime sourceEnv
      requiredBytes sourceCode) :
    (∃ (decl : Lean.Compiler.LCNF.LetDecl .impure)
        (continuation : Lean.Compiler.LCNF.Code .impure),
      sourceCode = .let decl continuation ∧
        requiredBytes = directLetAllocationCost decl ∧
        SchemaChangingDirectSupported context facts decl) ∨
      ¬ ∃ nextSchema,
        ConstructorSchema.DirectLetCodeShape sourceRuntime sourceEnv sourceCode
          schema nextSchema := by
  cases admitted with
  | legacy admitted eligible =>
      cases admitted with
      | ret =>
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | directLet supported =>
          cases supported.schema_cases with
          | inl changing => exact .inl ⟨_, _, rfl, rfl, changing⟩
          | inr preserving =>
              exact .inr
                (ConstructorSchema.noDirectLetCodeShape_of_noDeclShape
                  (fun {_ _} => preserving.noDirectLetShape))
      | pureExternal supported =>
          apply Or.inr
          apply ConstructorSchema.noDirectLetCodeShape_of_noDeclShape
          intro otherContext nextSchema shape
          rcases supported with integer | natural | scalar
          · cases integer
            apply shape.not_of_fap
            assumption
          · cases natural
            apply shape.not_of_fap
            assumption
          · cases scalar
            apply shape.not_of_fap
            assumption
      | directCall site =>
          apply Or.inr
          apply ConstructorSchema.noDirectLetCodeShape_of_noDeclShape
          intro otherContext nextSchema shape
          exact shape.not_of_fap site.valueEq
      | saturatedCall site resolution sharedCapacity =>
          apply Or.inr
          apply ConstructorSchema.noDirectLetCodeShape_of_noDeclShape
          intro otherContext nextSchema shape
          exact shape.not_of_fvar site.valueEq
      | lazyHit call generated semanticFound =>
          apply Or.inr
          apply ConstructorSchema.noDirectLetCodeShape_of_noDeclShape
          intro otherContext nextSchema shape
          cases call
          apply shape.not_of_fap
          assumption
      | lazyMiss call generated resultClassified notObject notTObject
          semanticEmpty =>
          apply Or.inr
          apply ConstructorSchema.noDirectLetCodeShape_of_noDeclShape
          intro otherContext nextSchema shape
          cases call with
          | intro supported bodyEq =>
              cases supported
              apply shape.not_of_fap
              assumption
      | defaultOnlyCase supported =>
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | objectCases supported =>
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | scalarUInt8Cases supported =>
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | incPersistent =>
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | decPersistent =>
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | ordinaryIncrement supported =>
          cases supported
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | ordinaryDecrement supported =>
          cases supported
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | ordinaryDelete supported =>
          cases supported
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | constructorTag supported =>
          cases supported
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | objectFieldFVar supported =>
          cases supported
          exact .inr (by simp [ConcreteStructuredSchemaLegacyCode] at eligible)
      | objectFieldErased supported =>
          cases supported
          exact .inr (by simp [ConcreteStructuredSchemaLegacyCode] at eligible)
      | usizeField supported =>
          cases supported
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
      | scalarField supported =>
          cases supported
          exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
  | objectFieldFVar fieldTyped =>
      exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])
  | objectFieldErased fieldTyped =>
      exact .inr (by simp [ConstructorSchema.DirectLetCodeShape])

/-- Precise use-site typing of a current return binding directly supplies its
source-admission constructor. -/
theorem ConcreteStructuredSourceAdmissionSafeAt.ret_of_semanticBinding
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {source : MachineState}
    {result : Lean.FVarId}
    (control : source.control = .code (.return result))
    (typed : SemanticBindingAtAbi source.env result expectedResult) :
    ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv source (.return result) :=
  .ret (ConcreteStructuredReturnValueSafeAt.of_semanticBinding control typed)

/-- Reference-count increment is source-admissible independently of whether
the validator selected the persistent or ordinary lowering.  The ordinary
case's finite `UInt32` headroom is deliberately kept in
`ConcreteStructuredFiniteRuntimeSafeAt`, not this semantic judgment. -/
theorem ConcreteStructuredSourceAdmissionSafeAt.inc_of_any_persistence
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {source : MachineState}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check persistent : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure} :
    ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv source
      (.inc objectId amount check persistent continuation) := by
  cases persistent with
  | false => exact .incOrdinary
  | true => exact .incPersistent

/-- Reference-count decrement has no additional source semantic premise for
either persistence mode. -/
theorem ConcreteStructuredSourceAdmissionSafeAt.dec_of_any_persistence
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {source : MachineState}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check persistent : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure} :
    ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv source
      (.dec objectId amount check persistent objectFields? continuation) := by
  cases persistent with
  | false => exact .decOrdinary
  | true => exact .decPersistent

/-- Deletion, constructor-tag mutation, and unboxed `USize` field mutation
are the three persistence-independent mutation forms whose current source
admission follows from their syntax alone. -/
theorem ConcreteStructuredSourceAdmissionSafeAt.del_unconditional
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {source : MachineState}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure} :
    ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv source
      (.del objectId continuation) :=
  .del

theorem ConcreteStructuredSourceAdmissionSafeAt.setTag_unconditional
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {source : MachineState}
    {objectId : Lean.FVarId}
    {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure} :
    ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv source
      (.setTag objectId tag continuation) :=
  .setTag

theorem ConcreteStructuredSourceAdmissionSafeAt.usizeField_unconditional
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {source : MachineState}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure} :
    ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
      expectedResult facts sourceRuntime sourceEnv source
      (.uset objectId index fieldId continuation) :=
  .usizeField

/-- Finite concrete-runtime conditions for the current source syntax.

Saturated closure entry needs capacity for retaining the captures selected by
its semantic resolution, and ordinary increment needs a `UInt32` header
successor.  Every other currently admitted source shape is resource-neutral
at this boundary; allocation bytes are checked independently against the
frame's `remainingBytes`. -/
def ConcreteStructuredFiniteRuntimeSafeAt
    (context : Fir.Wasm.Context)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env) :
    Lean.Compiler.LCNF.Code .impure → Prop
  | .let decl _ =>
      ∀ (site : SaturatedClosureCallSite context decl sourceEnv)
        (resolution : SaturatedClosureCallResolution context sourceRuntime
          site)
        (parentRuntime : RuntimeState),
        setCell sourceRuntime resolution.location
            { resolution.cell with rc := resolution.cell.rc - 1 } =
              .ok parentRuntime →
          ClosureRetainCapacity parentRuntime resolution.captures.toList
  | .inc objectId amount _ false _ =>
      ConcreteStructuredIncrementHeadroomAt sourceRuntime sourceEnv objectId
        amount
  | _ => True

/-- Residual production validation plus source admission safety construct the
exact current-node admission and allocation cost.

This is the common primitive factoring: validator equations are proved once,
successful source effects are inverted once, and each operation contributes
only its genuinely independent source invariant. -/
theorem ConcreteStructuredValidatedCodeCoreRel.admit_of_source_safe_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv sourceCode targetStore targetLocals targetCode
      witness source target)
    (sourceSafe : ConcreteStructuredSourceAdmissionSafeAt context sourceModule
      externals functionResult facts sourceRuntime sourceEnv source sourceCode)
    (finiteRuntimeSafe : ConcreteStructuredFiniteRuntimeSafeAt context
      sourceRuntime sourceEnv sourceCode)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ requiredBytes,
      ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv requiredBytes sourceCode := by
  cases sourceSafe with
  | ret safe =>
      refine ⟨0, related.validation.admit_return ?_⟩
      intro sourceValue sourceLookup
      apply safe related.core.focus.sourceControlEq
      simpa only [related.core.focus.sourceEnvEq] using sourceLookup
  | directLet supported =>
      exact ⟨directLetAllocationCost _, .directLet supported⟩
  | pureExternal supported =>
      exact ⟨_, .pureExternal supported⟩
  | directCall site =>
      exact ⟨0, .directCall site⟩
  | saturatedCall site resolution =>
      exact ⟨0, .saturatedCall site resolution
        (finiteRuntimeSafe site resolution)⟩
  | lazy call generated path =>
      cases path with
      | hit sourceValue semanticFound =>
          exact ⟨0, .lazyHit call generated semanticFound⟩
      | miss calleeCode internal resultClassified notObject notTObject
          semanticEmpty =>
          exact ⟨0, .lazyMiss internal generated resultClassified notObject
            notTObject semanticEmpty⟩
  | cases safe =>
      obtain ⟨selected, _sourceResult, _sourceAfterEq⟩ :=
        related.core.focus.caseResult_of_step sourceStep
      rcases related.productionCasesSupported_of_caseSafe
          (selected := selected) safe with defaultOnly | tested
      · exact ⟨0, .defaultOnlyCase defaultOnly⟩
      · rcases tested with objectCases | scalarCases
        · exact ⟨0, .objectCases objectCases⟩
        · exact ⟨0, .scalarUInt8Cases scalarCases⟩
  | incPersistent =>
      exact ⟨0, related.validation.admit_incPersistent⟩
  | incOrdinary =>
      exact ⟨0, related.validation.admit_incOrdinary_of_step
        related.core.focus sourceStep finiteRuntimeSafe⟩
  | decPersistent =>
      exact ⟨0, related.validation.admit_decPersistent⟩
  | decOrdinary =>
      exact ⟨0, related.validation.admit_decOrdinary_of_step
        related.core.focus sourceStep⟩
  | del =>
      exact ⟨0, related.validation.admit_del_of_step related.core.focus
        sourceStep⟩
  | setTag =>
      exact ⟨0, related.validation.admit_setTag_of_step related.core.focus
        sourceStep⟩
  | objectFieldFVar fieldTyped =>
      exact ⟨0, related.validation.admit_oset_fvar_of_step
        related.core.focus sourceStep fieldTyped⟩
  | objectFieldErased fieldTyped =>
      exact ⟨0, related.validation.admit_oset_erased_of_step
        related.core.focus sourceStep fieldTyped⟩
  | usizeField =>
      exact ⟨0, related.validation.admit_uset_of_step related.core.focus
        sourceStep⟩
  | scalarField fieldTyped =>
      exact ⟨0, related.validation.admit_sset_of_step related.core.focus
        sourceStep fieldTyped⟩

/-- Schema-aware source safety constructs the migration admission without
reintroducing arbitrary-witness descriptor premises.

Existing operation cases reuse `admit_of_source_safe_step`. FVar and erased
object-field writes carry only source schema typing; their successful semantic
effect and active descriptor alignment are reconstructed by the schema
dispatcher below. -/
theorem ConcreteStructuredValidatedCodeCoreRel.admitSchema_of_source_safe_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (related : ConcreteStructuredValidatedCodeCoreRel program context
      sourceModule sourceFunction externals labels entryRuntime entryStore
      entryWitness functionResult callerExpectedResult facts remainingBytes
      sourceRuntime sourceEnv sourceCode targetStore targetLocals targetCode
      witness source target)
    (sourceSafe : ConcreteStructuredSchemaSourceAdmissionSafeAt schema context
      sourceModule externals functionResult facts sourceRuntime sourceEnv source
      sourceCode)
    (finiteRuntimeSafe : ConcreteStructuredFiniteRuntimeSafeAt context
      sourceRuntime sourceEnv sourceCode)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ requiredBytes,
      ConcreteStructuredSchemaCodeStepAdmission schema context sourceModule
        externals functionResult facts sourceRuntime sourceEnv requiredBytes
        sourceCode := by
  cases sourceSafe with
  | legacy safe eligible =>
      obtain ⟨requiredBytes, admitted⟩ :=
        related.admit_of_source_safe_step safe finiteRuntimeSafe sourceStep
      exact ⟨requiredBytes, .legacy admitted eligible⟩
  | objectFieldFVar fieldTyped =>
      exact ⟨0, .objectFieldFVar fieldTyped⟩
  | objectFieldErased fieldTyped =>
      exact ⟨0, .objectFieldErased fieldTyped⟩

/-- Constructor-complete successor theorem for the validated ordinary-code
relation.

The current admission is consumed exactly once.  Each branch delegates to its
operation-specific theorem, which advances the residual validator state and
the hereditary suspended-caller validation in lockstep with the source and
target machines.  Thus the conclusion stays in the validated global relation;
validation provenance is not reconstructed from an arbitrary admission-free
compiler core after the fact. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_of_admission
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {requiredBytes remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
      externals functionResult facts sourceRuntime sourceEnv requiredBytes
      sourceCode)
    (budget : requiredBytes ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  cases admitted with
  | ret resultCompiled resultCompatible resultSemantic =>
      obtain ⟨targetAfter, targetPath, next⟩ :=
        related.advance_return_of_step activeResult
          (.ret resultCompiled resultCompatible resultSemantic) sourceStep
      exact ⟨2, targetAfter, targetPath, next, by omega⟩
  | directLet supported =>
      obtain ⟨targetAfter, nextRuntime, sourceValue, nextStore,
          resumedLocals, nextWitness, nextFacts, nextTargetCode, targetCount,
          targetPath, targetPositive, next⟩ :=
        related.advance_directLet_of_step supported budget sourceStep
      exact ⟨targetCount, targetAfter, targetPath,
        .code activeResult next, by omega⟩
  | pureExternal supported =>
      obtain ⟨site, physicalArgs, operation, resolvedResultKind,
          targetImport, callIndex, resultIndex, targetArguments, targetRest,
          targetAfter, targetPath, next, rank⟩ :=
        related.advance_pureExternal_stage activeResult supported budget
          sourceStep
      exact ⟨targetArguments.length, targetAfter, targetPath,
        .externalReady next, fun zero => rank⟩
  | directCall site =>
      obtain ⟨calleeContext, calleeFunction, row, physicalArgs, resultIndex,
          targetArguments, targetRest, targetAfter, targetPath, next, rank⟩ :=
        related.advance_directCall_stage_of_step activeResult site sourceStep
      exact ⟨targetArguments.length, targetAfter, targetPath,
        .directReady next, fun zero => rank⟩
  | saturatedCall site resolution sharedCapacity =>
      obtain ⟨calleeContext, calleeFunction, row, targetValue, targetRest,
          resultIndex, targetPath, next, rank⟩ :=
        related.advance_saturatedCall_stage_of_step activeResult site resolution
          sharedCapacity sourceStep
      exact ⟨0, target, targetPath, .saturatedReady next, fun _ => rank⟩
  | lazyHit call generated semanticFound =>
      let path : ConcreteStructuredLazyReadyAdmission context sourceModule call
          generated sourceRuntime := .hit _ semanticFound
      obtain ⟨cacheIndex, declarationId, cacheSetId, resultIndex, targetRest,
          targetPath, next, rank⟩ :=
        related.advance_lazy_stage_of_step activeResult call generated path
          sourceStep
      exact ⟨0, target, targetPath, .lazyReady next, fun _ => rank⟩
  | lazyMiss call generated resultClassified notObject notTObject
      semanticEmpty =>
      let path : ConcreteStructuredLazyReadyAdmission context sourceModule
          call.callSupported generated sourceRuntime :=
        .miss _ call resultClassified notObject notTObject semanticEmpty
      obtain ⟨cacheIndex, declarationId, cacheSetId, resultIndex, targetRest,
          targetPath, next, rank⟩ :=
        related.advance_lazy_stage_of_step activeResult call.callSupported
          generated path sourceStep
      exact ⟨0, target, targetPath, .lazyReady next, fun _ => rank⟩
  | defaultOnlyCase supported =>
      obtain ⟨targetPath, next, rank⟩ :=
        related.advance_defaultOnlyCase_of_step supported sourceStep
      exact ⟨0, target, targetPath, .code activeResult next, fun _ => rank⟩
  | objectCases supported =>
      obtain ⟨testCount, targetAfter, selected, selectedTarget, targetPath,
          next, zeroRank⟩ :=
        related.advance_objectCases_of_step supported sourceStep
      exact ⟨5 * testCount, targetAfter, targetPath,
        .code activeResult next, zeroRank⟩
  | scalarUInt8Cases supported =>
      obtain ⟨testCount, targetAfter, selected, selectedTarget, targetPath,
          next, zeroRank⟩ :=
        related.advance_scalarUInt8Cases_of_step supported sourceStep
      exact ⟨4 * testCount, targetAfter, targetPath,
        .code activeResult next, zeroRank⟩
  | incPersistent =>
      obtain ⟨_admitted, targetPath, _framesEq, next, rank⟩ :=
        related.advance_incPersistent_of_step
          (module := targetModule.wasmModule) (hostEnv := hosts.env) sourceStep
      exact ⟨0, target, targetPath, .code activeResult next, fun _ => rank⟩
  | decPersistent =>
      obtain ⟨_admitted, targetPath, _framesEq, next, rank⟩ :=
        related.advance_decPersistent_of_step
          (module := targetModule.wasmModule) (hostEnv := hosts.env) sourceStep
      exact ⟨0, target, targetPath, .code activeResult next, fun _ => rank⟩
  | ordinaryIncrement supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId amount check,
          sourceCode = .inc objectId amount check false continuation := by
        cases supported
        exact ⟨_, _, _, rfl⟩
      obtain ⟨objectId, amount, check, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
        related.advance_ordinaryIncrement_of_step supported sourceStep
      exact ⟨2, targetAfter, targetPath, .code activeResult next, by omega⟩
  | ordinaryDecrement supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId amount check objectFields?,
          sourceCode =
            .dec objectId amount check false objectFields? continuation := by
        cases supported
        exact ⟨_, _, _, _, rfl⟩
      obtain ⟨objectId, amount, check, objectFields?, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
        related.advance_ordinaryDecrement_of_step supported sourceStep
      exact ⟨2, targetAfter, targetPath, .code activeResult next, by omega⟩
  | ordinaryDelete supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId,
          sourceCode = .del objectId continuation := by
        cases supported
        exact ⟨_, rfl⟩
      obtain ⟨objectId, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
        related.advance_ordinaryDelete_of_step supported sourceStep
      exact ⟨2, targetAfter, targetPath, .code activeResult next, by omega⟩
  | constructorTag supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId tag,
          sourceCode = .setTag objectId tag continuation := by
        cases supported
        exact ⟨_, _, rfl⟩
      obtain ⟨objectId, tag, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
        related.advance_constructorTag_of_step supported sourceStep
      exact ⟨2, targetAfter, targetPath, .code activeResult next, by omega⟩
  | objectFieldFVar supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId fieldId index,
          sourceCode =
            .oset objectId index (.fvar fieldId) continuation := by
        cases supported
        exact ⟨_, _, _, rfl⟩
      obtain ⟨objectId, fieldId, index, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
        related.advance_objectFieldFVar_of_step supported sourceStep
      exact ⟨3, targetAfter, targetPath, .code activeResult next, by omega⟩
  | objectFieldErased supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId index,
          sourceCode = .oset objectId index .erased continuation := by
        cases supported
        exact ⟨_, _, rfl⟩
      obtain ⟨objectId, index, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
        related.advance_objectFieldErased_of_step supported sourceStep
      exact ⟨3, targetAfter, targetPath, .code activeResult next, by omega⟩
  | usizeField supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId fieldId index,
          sourceCode = .uset objectId index fieldId continuation := by
        cases supported
        exact ⟨_, _, _, rfl⟩
      obtain ⟨objectId, fieldId, index, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
        related.advance_usizeField_of_step supported sourceStep
      exact ⟨3, targetAfter, targetPath, .code activeResult next, by omega⟩
  | scalarField supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId fieldId slotIndex byteOffset type,
          sourceCode = .sset objectId slotIndex byteOffset fieldId type
            continuation := by
        cases supported
        exact ⟨_, _, _, _, _, rfl⟩
      obtain ⟨objectId, fieldId, slotIndex, byteOffset, type, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
        related.advance_scalarField_of_step supported sourceStep
      exact ⟨3, targetAfter, targetPath, .code activeResult next, by omega⟩

/-- Constructor-complete ordinary-code dispatcher at the schema boundary.

All established admissions delegate to the existing dispatcher. The two
object-field alternatives instead combine source constructor typing with
agreement for the one active witness and invoke the schema-derived closed
successors. This theorem is the interface the evolving global relation will
use; it contains no universal-witness field premise. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_of_schema_admission
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {requiredBytes remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (admitted : ConcreteStructuredSchemaCodeStepAdmission schema context
      sourceModule externals functionResult facts sourceRuntime sourceEnv
      requiredBytes sourceCode)
    (budget : requiredBytes ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  cases admitted with
  | legacy admitted eligible =>
      exact related.advance_of_admission activeResult admitted budget sourceStep
  | objectFieldFVar fieldTyped =>
      obtain ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath,
          next⟩ :=
        related.advance_objectFieldFVar_of_schema_step schemaAgrees fieldTyped
          sourceStep
      exact ⟨3, targetAfter, targetPath, .code activeResult next, by omega⟩
  | objectFieldErased fieldTyped =>
      obtain ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath,
          next⟩ :=
        related.advance_objectFieldErased_of_schema_step schemaAgrees fieldTyped
          sourceStep
      exact ⟨3, targetAfter, targetPath, .code activeResult next, by omega⟩

/-- FVar object-field mutation preserves the schema-enriched global relation
because its concrete successor keeps the active witness unchanged. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_objectFieldFVarSchemaGlobal_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) targetStore
      targetLocals targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (fieldTyped : schema.ObjectFieldFVarTyped context sourceEnv objectId
      fieldId index)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
  obtain ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath,
      next⟩ :=
    related.advance_objectFieldFVar_of_schema_step schemaAgrees fieldTyped
      sourceStep
  refine ⟨targetAfter, targetPath, ?_⟩
  exact (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult next)
    |>.withSchema schemaAgrees

/-- Erased object-field mutation preserves the same schema-enriched global
relation and its active witness index. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_objectFieldErasedSchemaGlobal_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.oset objectId index .erased continuation) targetStore targetLocals
      targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (fieldTyped : schema.ObjectFieldKindAt sourceEnv objectId index .erased)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
  obtain ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath,
      next⟩ :=
    related.advance_objectFieldErased_of_schema_step schemaAgrees fieldTyped
      sourceStep
  refine ⟨targetAfter, targetPath, ?_⟩
  exact (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult next)
    |>.withSchema schemaAgrees

/-- Complete ordinary-code dispatcher for the schema-enriched global
relation.  The legacy compatibility arm is inspected only to select an
already-proved successor: direct operations use their complete schema-global
law, every same-witness branch transports the current agreement, and the two
object-field shapes are impossible in that arm.  The dedicated field arms use
the active-schema successors above. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_schemaStep_of_schema_admission_noShape
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {requiredBytes remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (admitted : ConcreteStructuredSchemaCodeStepAdmission schema context
      sourceModule externals functionResult facts sourceRuntime sourceEnv
      requiredBytes sourceCode)
    (budget : requiredBytes ≤ remainingBytes)
    (noShape : ¬ ∃ nextSchema,
      ConstructorSchema.DirectLetShapeAt source schema nextSchema)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
          targetModule hosts externals source sourceAfter schema targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  cases admitted with
  | legacy admitted eligible =>
      cases admitted with
      | ret resultCompiled resultCompatible resultSemantic =>
          obtain ⟨targetAfter, targetPath, next⟩ :=
            related.advance_returnAt_of_step activeResult
              (.ret resultCompiled resultCompatible resultSemantic) sourceStep
          exact ⟨2, targetAfter, targetPath,
            next.withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
      | directLet supported =>
          obtain ⟨targetAfter, targetCount, targetPath, targetPositive,
              next⟩ :=
            related.advance_directLetSchemaStep_of_step activeResult
              schemaAgrees supported budget sourceStep
          exact ⟨targetCount, targetAfter, targetPath, next, by omega⟩
      | pureExternal supported =>
          obtain ⟨site, physicalArgs, operation, resolvedResultKind,
              targetImport, callIndex, resultIndex, targetArguments,
              targetRest, targetAfter, targetPath, next, rank⟩ :=
            related.advance_pureExternal_stage activeResult supported budget
              sourceStep
          exact ⟨targetArguments.length, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.externalReady next)
              |>.withSchemaPreservedStep sourceStep noShape schemaAgrees,
            fun zero => rank⟩
      | directCall site =>
          obtain ⟨calleeContext, calleeFunction, row, physicalArgs,
              resultIndex, targetArguments, targetRest, targetAfter,
              targetPath, next, rank⟩ :=
            related.advance_directCall_stage_of_step activeResult site
              sourceStep
          exact ⟨targetArguments.length, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.directReady next)
              |>.withSchemaPreservedStep sourceStep noShape schemaAgrees,
            fun zero => rank⟩
      | saturatedCall site resolution sharedCapacity =>
          obtain ⟨calleeContext, calleeFunction, row, targetValue,
              targetRest, resultIndex, targetPath, next, rank⟩ :=
            related.advance_saturatedCall_stage_of_step activeResult site
              resolution sharedCapacity sourceStep
          exact ⟨0, target, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.saturatedReady next)
              |>.withSchemaPreservedStep sourceStep noShape schemaAgrees,
            fun _ => rank⟩
      | lazyHit call generated semanticFound =>
          let path : ConcreteStructuredLazyReadyAdmission context sourceModule
              call generated sourceRuntime := .hit _ semanticFound
          obtain ⟨cacheIndex, declarationId, cacheSetId, resultIndex,
              targetRest, targetPath, next, rank⟩ :=
            related.advance_lazy_stage_of_step activeResult call generated path
              sourceStep
          exact ⟨0, target, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.lazyReady next)
              |>.withSchemaPreservedStep sourceStep noShape schemaAgrees,
            fun _ => rank⟩
      | lazyMiss call generated resultClassified notObject notTObject
          semanticEmpty =>
          let path : ConcreteStructuredLazyReadyAdmission context sourceModule
              call.callSupported generated sourceRuntime :=
            .miss _ call resultClassified notObject notTObject semanticEmpty
          obtain ⟨cacheIndex, declarationId, cacheSetId, resultIndex,
              targetRest, targetPath, next, rank⟩ :=
            related.advance_lazy_stage_of_step activeResult call.callSupported
              generated path sourceStep
          exact ⟨0, target, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.lazyReady next)
              |>.withSchemaPreservedStep sourceStep noShape schemaAgrees,
            fun _ => rank⟩
      | defaultOnlyCase supported =>
          obtain ⟨targetPath, next, rank⟩ :=
            related.advance_defaultOnlyCase_of_step supported sourceStep
          exact ⟨0, target, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            fun _ => rank⟩
      | objectCases supported =>
          obtain ⟨testCount, targetAfter, selected, selectedTarget,
              targetPath, next, zeroRank⟩ :=
            related.advance_objectCases_of_step supported sourceStep
          exact ⟨5 * testCount, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            zeroRank⟩
      | scalarUInt8Cases supported =>
          obtain ⟨testCount, targetAfter, selected, selectedTarget,
              targetPath, next, zeroRank⟩ :=
            related.advance_scalarUInt8Cases_of_step supported sourceStep
          exact ⟨4 * testCount, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            zeroRank⟩
      | incPersistent =>
          obtain ⟨_admitted, targetPath, _framesEq, next, rank⟩ :=
            related.advance_incPersistent_of_step
              (module := targetModule.wasmModule) (hostEnv := hosts.env)
              sourceStep
          exact ⟨0, target, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            fun _ => rank⟩
      | decPersistent =>
          obtain ⟨_admitted, targetPath, _framesEq, next, rank⟩ :=
            related.advance_decPersistent_of_step
              (module := targetModule.wasmModule) (hostEnv := hosts.env)
              sourceStep
          exact ⟨0, target, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            fun _ => rank⟩
      | ordinaryIncrement supported =>
          rename_i nextRuntime continuation
          have shape : ∃ objectId amount check,
              sourceCode = .inc objectId amount check false continuation := by
            cases supported
            exact ⟨_, _, _, rfl⟩
          obtain ⟨objectId, amount, check, rfl⟩ := shape
          obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
            related.advance_ordinaryIncrement_of_step supported sourceStep
          exact ⟨2, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
      | ordinaryDecrement supported =>
          rename_i nextRuntime continuation
          have shape : ∃ objectId amount check objectFields?,
              sourceCode =
                .dec objectId amount check false objectFields? continuation := by
            cases supported
            exact ⟨_, _, _, _, rfl⟩
          obtain ⟨objectId, amount, check, objectFields?, rfl⟩ := shape
          obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
            related.advance_ordinaryDecrement_of_step supported sourceStep
          exact ⟨2, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
      | ordinaryDelete supported =>
          rename_i nextRuntime continuation
          have shape : ∃ objectId,
              sourceCode = .del objectId continuation := by
            cases supported
            exact ⟨_, rfl⟩
          obtain ⟨objectId, rfl⟩ := shape
          obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
            related.advance_ordinaryDelete_of_step supported sourceStep
          exact ⟨2, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
      | constructorTag supported =>
          rename_i nextRuntime continuation
          have shape : ∃ objectId tag,
              sourceCode = .setTag objectId tag continuation := by
            cases supported
            exact ⟨_, _, rfl⟩
          obtain ⟨objectId, tag, rfl⟩ := shape
          obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
            related.advance_constructorTag_of_step supported sourceStep
          exact ⟨2, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
      | objectFieldFVar supported =>
          rename_i nextRuntime continuation
          have shape : ∃ objectId fieldId index,
              sourceCode =
                .oset objectId index (.fvar fieldId) continuation := by
            cases supported
            exact ⟨_, _, _, rfl⟩
          obtain ⟨objectId, fieldId, index, rfl⟩ := shape
          simp [ConcreteStructuredSchemaLegacyCode] at eligible
      | objectFieldErased supported =>
          rename_i nextRuntime continuation
          have shape : ∃ objectId index,
              sourceCode = .oset objectId index .erased continuation := by
            cases supported
            exact ⟨_, _, rfl⟩
          obtain ⟨objectId, index, rfl⟩ := shape
          simp [ConcreteStructuredSchemaLegacyCode] at eligible
      | usizeField supported =>
          rename_i nextRuntime continuation
          have shape : ∃ objectId fieldId index,
              sourceCode = .uset objectId index fieldId continuation := by
            cases supported
            exact ⟨_, _, _, rfl⟩
          obtain ⟨objectId, fieldId, index, rfl⟩ := shape
          obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
            related.advance_usizeField_of_step supported sourceStep
          exact ⟨3, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
      | scalarField supported =>
          rename_i nextRuntime continuation
          have shape : ∃ objectId fieldId slotIndex byteOffset type,
              sourceCode = .sset objectId slotIndex byteOffset fieldId type
                continuation := by
            cases supported
            exact ⟨_, _, _, _, _, rfl⟩
          obtain ⟨objectId, fieldId, slotIndex, byteOffset, type, rfl⟩ :=
            shape
          obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next⟩ :=
            related.advance_scalarField_of_step supported sourceStep
          exact ⟨3, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult
              next).withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
  | objectFieldFVar fieldTyped =>
      obtain ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath,
          next⟩ :=
        related.advance_objectFieldFVar_of_schema_step schemaAgrees fieldTyped
          sourceStep
      exact ⟨3, targetAfter, targetPath,
        (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult next)
          |>.withSchemaPreservedStep sourceStep noShape schemaAgrees,
        by omega⟩
  | objectFieldErased fieldTyped =>
      obtain ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, targetPath,
          next⟩ :=
        related.advance_objectFieldErased_of_schema_step schemaAgrees fieldTyped
          sourceStep
      exact ⟨3, targetAfter, targetPath,
        (ConcreteStructuredValidatedCodeGlobalOutcomeAt.code activeResult next)
          |>.withSchemaPreservedStep sourceStep noShape schemaAgrees,
        by omega⟩

/-- Complete ordinary-code dispatcher retaining the exact source/compiler
schema transition.

Admission is classified once.  Constructor/reuse bindings take the dedicated
compiled-layout transition; every other admitted source node uses the shared
proof that no direct schema shape exists and therefore records identity
evolution. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_schemaStep_of_schema_admission
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {requiredBytes remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (admitted : ConcreteStructuredSchemaCodeStepAdmission schema context
      sourceModule externals functionResult facts sourceRuntime sourceEnv
      requiredBytes sourceCode)
    (budget : requiredBytes ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
          targetModule hosts externals source sourceAfter schema targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  cases admitted.sourceSchemaCases with
  | inl changing =>
      obtain ⟨decl, continuation, codeEq, requiredEq, supported⟩ := changing
      subst sourceCode
      rw [requiredEq] at budget
      obtain ⟨targetAfter, targetCount, targetPath, targetPositive, next⟩ :=
        related.advance_schemaChangingDirectLetSchemaStep_of_step activeResult
          schemaAgrees supported budget sourceStep
      exact ⟨targetCount, targetAfter, targetPath, next, by omega⟩
  | inr noCodeShape =>
      have noShape :=
        ConstructorSchema.noDirectLetShapeAt_of_noCodeShape
          related.core.core.focus.sourceControlEq
          related.core.core.focus.sourceRuntimeEq
          related.core.core.focus.sourceEnvEq noCodeShape
      exact related.advance_schemaStep_of_schema_admission_noShape activeResult
        schemaAgrees admitted budget noShape sourceStep

/-- Compatibility projection of the exact schema-step dispatcher. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_schemaGlobal_of_schema_admission
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {requiredBytes remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {schema : ConstructorSchema}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (admitted : ConcreteStructuredSchemaCodeStepAdmission schema context
      sourceModule externals functionResult facts sourceRuntime sourceEnv
      requiredBytes sourceCode)
    (budget : requiredBytes ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨targetCount, targetAfter, targetPath, next, rank⟩ :=
    related.advance_schemaStep_of_schema_admission activeResult schemaAgrees
      admitted budget sourceStep
  exact ⟨targetCount, targetAfter, targetPath, next.toSchemaGlobal, rank⟩

end FirTalos.Concrete
