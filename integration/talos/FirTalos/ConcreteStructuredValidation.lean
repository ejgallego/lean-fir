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
    {labels : List Lean.FVarId}
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
      ConcreteStructuredValidationState program callerResult continuation)
    (tail : ConcreteStructuredValidatedFrameStack program sourceModule
      targetModule hosts callerResult tailResult sourceFrames targetFrames) :
    ConcreteStructuredValidatedFrameStack program sourceModule targetModule
      hosts calleeResult (some kind)
      (.bind result continuation callerEnv callerJoins :: sourceFrames)
      (.call 1 callerRemainder callerLocals
          (.localSet resultIndex :: targetRest) :: targetFrames) :=
  ⟨.direct spec callerResultAt contextCaches continuationAdapted resultFound
      kindAt calleeCompatible tail.supported,
    .bind continuationValidation tail.validation⟩

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
    {labels : List Lean.FVarId}
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
      ConcreteStructuredValidationState program callerResult continuation)
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
    .bind continuationValidation tail.validation⟩

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
    {labels : List Lean.FVarId}
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
      ConcreteStructuredValidationState program callerResult continuation)
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
    .lazy continuationValidation tail.validation⟩

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
      {labels : List Lean.FVarId}
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
      (continuationValidation : ConcreteStructuredValidationState program
        callerResult continuation)
      (tailAligned : ConcreteStructuredValidatedStackAgreement spine tailAgrees
        tailValidation) :
      ConcreteStructuredValidatedStackAgreement
        ((callerResult, tailResult) :: spine)
        (.direct (callerJoins := callerJoins)
          (callerRemainder := callerRemainder) spec callerResultAt contextCaches
          callerScope programEq continuationAdapted resultFound kindAt
          calleeCompatible supportedTail resourceTail tailAgrees)
        (.bind continuationValidation tailValidation)
  | saturated
      {spine : List (AbiKind × Option AbiKind)}
      {activeEntryRuntime callerEntryRuntime : RuntimeState}
      {activeEntryStore callerEntryStore : Wasm.Store Host}
      {activeEntryWitness callerEntryWitness : RefinementWitness}
      {callerContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {callerFunction : Fir.Wasm.Function}
      {labels : List Lean.FVarId}
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
      (continuationValidation : ConcreteStructuredValidationState program
        callerResult continuation)
      (tailAligned : ConcreteStructuredValidatedStackAgreement spine tailAgrees
        tailValidation) :
      ConcreteStructuredValidatedStackAgreement
        ((callerResult, tailResult) :: spine)
        (.saturated (callerJoins := callerJoins)
          (matcherCount := matcherCount) spec callerResultAt contextCaches
          callerScope programEq continuationAdapted resultFound kindAt
          calleeCompatible supportedTail resourceTail tailAgrees)
        (.bind continuationValidation tailValidation)
  | lazy
      {spine : List (AbiKind × Option AbiKind)}
      {activeEntryRuntime callerEntryRuntime : RuntimeState}
      {activeEntryStore callerEntryStore : Wasm.Store Host}
      {activeEntryWitness callerEntryWitness : RefinementWitness}
      {callerContext : Fir.Wasm.Context}
      {callerCode : Lean.Compiler.LCNF.Code .impure}
      {callerFunction : Fir.Wasm.Function}
      {labels : List Lean.FVarId}
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
      (continuationValidation : ConcreteStructuredValidationState program
        callerResult continuation)
      (tailAligned : ConcreteStructuredValidatedStackAgreement spine tailAgrees
        tailValidation) :
      ConcreteStructuredValidatedStackAgreement
        ((callerResult, tailResult) :: spine)
        (.lazy (callerJoins := callerJoins) (cacheIndex := cacheIndex)
          (cacheSetId := cacheSetId) spec callerResultAt contextCaches callerScope
          programEq continuationAdapted resultFound kindAt initializerFound
          signature cacheSetCall notObject notTObject calleeCompatible
          supportedTail resourceTail tailAgrees)
        (.lazy continuationValidation tailValidation)

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
validation state of its current source node.  This companion relation is the
incremental bridge to universal compiler admission: it adds no source step,
target path, allocation budget, future admission, or termination evidence. -/
structure ConcreteStructuredValidatedCodeCoreRel
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (externals : ExternalImpl)
    (labels : List Lean.FVarId)
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
  validation : ConcreteStructuredValidationState program functionResult
    sourceCode

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
    (labels : List Lean.FVarId)
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
    (labels : List Lean.FVarId)
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
    ConcreteStructuredValidationState program functionResult continuation
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
    (labels : List Lean.FVarId)
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
    ConcreteStructuredValidationState program functionResult continuation
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
    (labels : List Lean.FVarId)
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
    ConcreteStructuredValidationState program functionResult continuation
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
    (labels : List Lean.FVarId)
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

The direct-ready constructor is the first administrative branch in this sum:
it carries the caller continuation validation between staging and entry.
Saturated, lazy, external, and yielded branches will join it as their matching
transport lemmas are completed. -/
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
      {labels : List Lean.FVarId}
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
      {labels : List Lean.FVarId}
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
      {labels : List Lean.FVarId}
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
  | externalBind
      {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts}
      {labels : List Lean.FVarId}
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
      {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    (nextValidation : ConcreteStructuredValidationState program functionResult
      nextCode)
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
    {labels : List Lean.FVarId}
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
    (nextValidation : ConcreteStructuredValidationState program functionResult
      nextCode) :
    ConcreteStructuredValidatedCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult nextFacts nextRemainingBytes
      nextRuntime nextEnv nextCode nextStore nextLocals nextTargetCode
      nextWitness nextSource nextTarget :=
  ⟨nextCore, nextValidation⟩

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
    {labels : List Lean.FVarId}
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
  ⟨core, spec.rootValidationState activeResult⟩

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
  .code rfl (spec.validatedCodeRoot contextCaches invariant)

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

/-- Any compiler/resource successor of a validated direct `let` continuation
inherits the exact residual validator state, even when the concrete operation
changes heap facts, remaining address-space budget, or refinement witness. -/
theorem ConcreteStructuredValidatedCodeCoreRel.letSuccessor
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : List Lean.FVarId}
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
  obtain ⟨_kind, _locals, _kindFound, nextValidation⟩ :=
    related.validation.letContinuation
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
    {labels : List Lean.FVarId}
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
  have validatedCore := related.core.letSuccessor nextCore
  exact ⟨targetAfter, nextRuntime, sourceValue, nextStore, resumedLocals,
    nextWitness, nextFacts, nextTargetCode, targetCount, targetPath,
    targetPositive,
    related.withSuccessor validatedCore sourceFramesEq targetFramesEq⟩

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
    {labels : List Lean.FVarId}
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
  obtain ⟨_kind, _locals, _kindFound, continuationValidation⟩ :=
    related.core.validation.letContinuation
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
    {labels : List Lean.FVarId}
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
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
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
        site.calleeResultKind (some site.resultKind) [] remainingBytes
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
      (callerRemainder := callerRemainder) spec related.activeResult
      related.contextCaches entry.continuationAdapted entry.resultFound
      entry.resultKindAt site.calleeResultRefines
      related.continuationValidation related.frames
  let pushedResources :=
    ConcreteStructuredSuspendedResourceStack.direct
      (callerEnv := callerEnv) (callerJoins := callerJoins)
      (callerLocals := storedCallerLocals)
      (callerRemainder := callerRemainder) callerScope
      spec.contextProgram.symm entry.continuationAdapted entry.resultFound
      entry.resultKindAt site.calleeResultRefines
      related.core.resources.suspended
  have pushedAgrees : pushedFrames.supported.Agrees pushedResources := by
    exact ConcreteStructuredSupportedFrameStack.Agrees.direct
      spec related.activeResult related.contextCaches callerScope
      spec.contextProgram.symm entry.continuationAdapted entry.resultFound
      entry.resultKindAt site.calleeResultRefines related.frames.supported
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
        site.calleeResultRefines related.continuationValidation
        callerValidationAgrees⟩
  obtain ⟨supportedAfter, agreesAfter⟩ := pushedAgrees.reindex
    entry.sourceFramesEq entry.targetFramesEq
    validatedCore.core.resources.suspended
  have validationAfter :
      ConcreteStructuredSuspendedValidation program site.calleeResultKind
        (some site.resultKind) sourceAfter.frames := by
    rw [entry.sourceFramesEq]
    exact pushedFrames.validation
  have nextFrames :
      ConcreteStructuredValidatedFrameStack program sourceModule targetModule
        hosts site.calleeResultKind (some site.resultKind) sourceAfter.frames
        targetAfter.frames :=
    ⟨supportedAfter, validationAfter⟩
  have nextValidationAgrees :
      ConcreteStructuredValidationAgrees agreesAfter validationAfter :=
    pushedValidationAgrees.reindex entry.sourceFramesEq entry.targetFramesEq
      agreesAfter validationAfter
  have nextOutcome :
      ConcreteStructuredValidatedCodeOutcome program calleeContext
        site.calleeCode sourceModule calleeFunction targetModule hosts
        calleeSpec externals [] sourceRuntime targetStore witness
        site.calleeResultKind (some site.resultKind) [] remainingBytes
        sourceRuntime site.calleeEnv site.calleeCode targetStore
        (row.targetFunction.toLocals physicalArgs) row.targetFunction.body
        witness sourceAfter targetAfter :=
    ⟨rowAtProgram.contextCaches, validatedCore, nextFrames, agreesAfter,
      nextValidationAgrees⟩
  exact ⟨targetAfter, targetPath,
    ConcreteStructuredValidatedCodeGlobalOutcome.code calleeResultAt
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
    {labels : List Lean.FVarId}
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
  obtain ⟨_kind, _locals, _kindFound, continuationValidation⟩ :=
    related.core.validation.letContinuation
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
    {labels : List Lean.FVarId}
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
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
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
    ConcreteStructuredValidatedCodeGlobalOutcome.code calleeResultAt
      nextOutcome⟩
  omega

/-- A validated return enters the closed yielded branch.  Current-node
admission supplies only the compiled result kind; the concrete theorem derives
the semantic/physical result and both machine paths, while suspended caller
validation is transported across the unchanged-frame equalities. -/
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
    {labels : List Lean.FVarId}
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
    ConcreteStructuredValidatedCodeGlobalOutcome.returned returned⟩

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
    {labels : List Lean.FVarId}
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
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
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
          ConcreteStructuredValidatedCodeGlobalOutcome.code callerResultAt
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
          ConcreteStructuredValidatedCodeGlobalOutcome.code callerResultAt
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
    {labels : List Lean.FVarId}
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
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
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
        ConcreteStructuredValidatedCodeGlobalOutcome.externalBind
          bindValidated⟩

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
    {labels : List Lean.FVarId}
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
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter := by
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
    ConcreteStructuredValidatedCodeGlobalOutcome.code related.activeResult
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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

/-- Uniform successor transport for ownership increments. -/
theorem ConcreteStructuredValidatedCodeCoreRel.incSuccessor
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult facts remainingBytes sourceRuntime
      sourceEnv selected targetStore nextLocals selectedTarget witness
      sourceAfter targetAfter)
    (nextValidation : ConcreteStructuredValidationState program functionResult
      selected)
    (sourceFramesEq : sourceAfter.frames = source.frames)
    (targetFramesEq : targetAfter.frames =
      structuredWasmCaseLabels belowStack targetSuffix testCount ++
        target.frames) :
    ConcreteStructuredValidatedCodeOutcome program context functionCode
      sourceModule sourceFunction targetModule hosts spec externals labels
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
    {labels : List Lean.FVarId}
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
    {labels : List Lean.FVarId}
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
          sourceModule sourceFunction targetModule hosts spec externals labels
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
          sourceModule sourceFunction targetModule hosts spec externals labels
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

end FirTalos.Concrete
