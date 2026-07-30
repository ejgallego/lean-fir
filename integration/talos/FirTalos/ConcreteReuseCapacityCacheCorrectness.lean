import FirTalos.ConcreteReuseCapacityCallCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/--
One lazy-cache result with all transports needed by the facts-indexed
resource frame.

The executable cache hit or miss is still represented by the existing
`LazyLetStepSimulates` theorem. This wrapper adds only the proof-side facts
that its continuation-polymorphic WP contract intentionally omits: the
checked destination write, witness/header and ordinary-token transport,
immutable-table preservation, and residual allocation budget.
-/
structure BudgetedCapacityPreservingLazyStep
    (path : LazyCachePath)
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (decl : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceValue : Value)
    (initial nextStore : Wasm.Store Host)
    (locals nextLocals : Wasm.Locals)
    (resultIndex : Nat)
    (initialWitness nextWitness : RefinementWitness)
    (physical : Wasm.Value)
    (stepCost : Nat) : Prop where
  simulates :
    LazyLetStepSimulates path context sourceFunction module hostEnv
      sourceExternals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue initial nextStore locals nextLocals resultIndex
      initialWitness nextWitness
  targetSet :
    locals.set? resultIndex physical = some nextLocals
  ordinaryTransport :
    OrdinaryPersistenceTransport sourceRuntime nextRuntime
  witnessTransport :
    WitnessTransport initialWitness nextWitness
  capacityTransport :
    HeaderCapacityTransport initial.host.runtime.heap
      nextStore.host.runtime.heap initialWitness
  externalsPreserved :
    nextStore.host.externals = initial.host.externals
  hostDescriptorsPreserved :
    nextStore.host.closureDescriptors =
      initial.host.closureDescriptors
  witnessDescriptorsPreserved :
    nextWitness.closureDescriptors =
      initialWitness.closureDescriptors
  residualBudget :
    ∀ remainingBytes,
      stepCost ≤ remainingBytes →
        initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
          nextStore.host.runtime.heap.AddressSpaceBudget
            (remainingBytes - stepCost)

/--
The generated cache-hit path is a zero-allocation budgeted lazy step.

The populated flag/value globals select and identify the cached physical
value. The only target mutation is the checked caller-local write; host state,
the heap, and the representation witness are unchanged.
-/
theorem BudgetedCapacityPreservingLazyStep.hit
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {missBody : Wasm.Program}
    {flagIndex valueIndex resultIndex : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {initialWitness : RefinementWitness}
    {physical : Wasm.Value}
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv
        decl continuation sourceRuntime sourceValue)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (flagPublished :
      initial.globals.globals[flagIndex]? = some (.i32 1))
    (valuePublished :
      initial.globals.globals[valueIndex]? = some physical)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (nextRelated :
      StateRelated sourceFunction sourceRuntime
        (bind sourceEnv decl.fvarId sourceValue) initial nextLocals
        initialWitness) :
    BudgetedCapacityPreservingLazyStep .hit context sourceFunction module
      hostEnv sourceExternals decl continuation
      [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
      sourceRuntime sourceRuntime sourceEnv sourceValue initial initial locals
      nextLocals resultIndex initialWitness initialWitness physical 0 := by
  refine {
    simulates := lazyLetStepSimulates_hit sourceStep initialRelated
      flagPublished valuePublished targetSet rfl nextRelated
    targetSet
    ordinaryTransport := OrdinaryPersistenceTransport.refl sourceRuntime
    witnessTransport := WitnessTransport.refl initialWitness
    capacityTransport :=
      HeaderCapacityTransport.refl initial.host.runtime.heap initialWitness
    externalsPreserved := rfl
    hostDescriptorsPreserved := rfl
    witnessDescriptorsPreserved := rfl
    residualBudget := ?_
  }
  intro remainingBytes _ budget
  simpa using budget

/--
Package a proved cache-miss execution with its proof-side resource
transports. The executable miss block remains supplied by the existing
compiler-anchored lazy-cache theorem; this constructor centralizes the
additional W6 frame obligations and path-dependent cost.
-/
theorem BudgetedCapacityPreservingLazyStep.miss
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial nextStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {resultIndex stepCost : Nat}
    {initialWitness nextWitness : RefinementWitness}
    {physical : Wasm.Value}
    (simulates :
      LazyLetStepSimulates .miss context sourceFunction module hostEnv
        sourceExternals decl continuation targetValue sourceRuntime nextRuntime
        sourceEnv sourceValue initial nextStore locals nextLocals resultIndex
        initialWitness nextWitness)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (ordinaryTransport :
      OrdinaryPersistenceTransport sourceRuntime nextRuntime)
    (witnessTransport :
      WitnessTransport initialWitness nextWitness)
    (capacityTransport :
      HeaderCapacityTransport initial.host.runtime.heap
        nextStore.host.runtime.heap initialWitness)
    (externalsPreserved :
      nextStore.host.externals = initial.host.externals)
    (hostDescriptorsPreserved :
      nextStore.host.closureDescriptors =
        initial.host.closureDescriptors)
    (witnessDescriptorsPreserved :
      nextWitness.closureDescriptors =
        initialWitness.closureDescriptors)
    (residualBudget :
      ∀ remainingBytes,
        stepCost ≤ remainingBytes →
          initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
            nextStore.host.runtime.heap.AddressSpaceBudget
              (remainingBytes - stepCost)) :
    BudgetedCapacityPreservingLazyStep .miss context sourceFunction module
      hostEnv sourceExternals decl continuation targetValue sourceRuntime
      nextRuntime sourceEnv sourceValue initial nextStore locals nextLocals
      resultIndex initialWitness nextWitness physical stepCost := {
  simulates
  targetSet
  ordinaryTransport
  witnessTransport
  capacityTransport
  externalsPreserved
  hostDescriptorsPreserved
  witnessDescriptorsPreserved
  residualBudget
}

/--
Close the exact compiler-generated lazy miss from a hereditary declaration
body, concrete `cacheSet`, and the two Wasm global publications, then attach
the W6 resource transports.

Unlike `BudgetedCapacityPreservingLazyStep.miss`, this theorem does not accept
an already assembled lazy simulation. It invokes the existing
compiler-anchored miss-body theorem and the surrounding flag conditional
directly.
-/
theorem BudgetedCapacityPreservingLazyStep.miss_of_bodyWP_cacheSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {kind : AbiKind}
    {declarationId cacheSetId : Nat}
    {imp : Wasm.ImportDecl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial afterCall afterCache valueStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {initialWitness nextWitness : RefinementWitness}
    {physical oldValue oldFlag : Wasm.Value}
    {flagIndex valueIndex resultIndex stepCost : Nat}
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (initialRelated :
      StateRelated callerFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (flagEmpty :
      initial.globals.globals[flagIndex]? = some (.i32 0))
    (body :
      CachedDeclarationBodyWP context sourceModule calleeFunction module
        hostEnv sourceRuntime sourceCode targetFunction initial afterCall
        initialWitness physical)
    (notImport :
      module.imports[declarationId]? = none)
    (functionFound :
      module.funcs[declarationId - module.imports.length]? =
        some targetFunction)
    (importFound :
      module.imports[cacheSetId]? = some imp)
    (hostSatisfies : hostEnv.Satisfies module spec)
    (importInBounds : cacheSetId < module.imports.length)
    (contractFound :
      spec.contracts[cacheSetId]? =
        some (cacheSetContract declaration kind))
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 1)
    (operation :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache)
    (valueGlobal :
      afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq :
      valueStore = writeWasmGlobal afterCache valueIndex physical)
    (flagGlobal :
      valueStore.globals.globals[flagIndex]? = some oldFlag)
    (distinct : valueIndex ≠ flagIndex)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (nextRelated :
      StateRelated callerFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue)
        (writeWasmGlobal valueStore flagIndex (.i32 1)) nextLocals
        nextWitness)
    (ordinaryTransport :
      OrdinaryPersistenceTransport sourceRuntime nextRuntime)
    (witnessTransport :
      WitnessTransport initialWitness nextWitness)
    (capacityTransport :
      HeaderCapacityTransport initial.host.runtime.heap
        (writeWasmGlobal valueStore flagIndex (.i32 1)).host.runtime.heap
        initialWitness)
    (externalsPreserved :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.externals =
        initial.host.externals)
    (hostDescriptorsPreserved :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.closureDescriptors =
        initial.host.closureDescriptors)
    (witnessDescriptorsPreserved :
      nextWitness.closureDescriptors =
        initialWitness.closureDescriptors)
    (residualBudget :
      ∀ remainingBytes,
        stepCost ≤ remainingBytes →
          initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
            ((writeWasmGlobal valueStore flagIndex
                (.i32 1)).host.runtime.heap).AddressSpaceBudget
              (remainingBytes - stepCost)) :
    BudgetedCapacityPreservingLazyStep .miss context callerFunction module
      hostEnv sourceExternals decl continuation
      [.globalGet flagIndex,
        .iff 0 0 [] [
          .call declarationId,
          .call cacheSetId,
          .globalSet valueIndex,
          .const 1,
          .globalSet flagIndex],
        .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue initial
      (writeWasmGlobal valueStore flagIndex (.i32 1)) locals nextLocals
      resultIndex initialWitness nextWitness physical stepCost := by
  have missBody :
      LazyMissBodySimulates module hostEnv
        [.call declarationId, .call cacheSetId, .globalSet valueIndex,
          .const 1, .globalSet flagIndex]
        valueIndex resultIndex initial
        (writeWasmGlobal valueStore flagIndex (.i32 1))
        locals nextLocals :=
    lazyMissBodySimulates_of_bodyWP_cacheSet body notImport functionFound
      importFound hostSatisfies importInBounds contractFound parameterCount
      resultCount operation valueGlobal valueStoreEq flagGlobal distinct
      targetSet
  have simulates :
      LazyLetStepSimulates .miss context callerFunction module hostEnv
        sourceExternals decl continuation
        [.globalGet flagIndex,
          .iff 0 0 [] [
            .call declarationId,
            .call cacheSetId,
            .globalSet valueIndex,
            .const 1,
            .globalSet flagIndex],
          .globalGet valueIndex]
        sourceRuntime nextRuntime sourceEnv sourceValue initial
        (writeWasmGlobal valueStore flagIndex (.i32 1)) locals nextLocals
        resultIndex initialWitness nextWitness :=
    lazyLetStepSimulates_miss sourceStep initialRelated flagEmpty missBody
      nextRelated
  exact .miss simulates targetSet ordinaryTransport witnessTransport
    capacityTransport externalsPreserved hostDescriptorsPreserved
    witnessDescriptorsPreserved residualBudget

/--
A budgeted hereditary nullary declaration plus a nonallocating cache
publication closes the complete lazy miss resource boundary.

The declaration consumes the path's allocation cost. `cacheSet` may update
persistence metadata and semantic globals but must preserve already mapped
header extents and the residual address-space budget; the two Wasm
`global.set`s are part of the same final store and require no additional
resource premise.
-/
theorem
    BudgetedCapacityPreservingLazyStep.miss_of_budgetedDeclaration_cacheSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {calleeCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {kind resultKind : AbiKind}
    {declarationId cacheSetId : Nat}
    {imp : Wasm.ImportDecl}
    {sourceRuntime callRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial afterCall afterCache valueStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {initialWitness callWitness : RefinementWitness}
    {physical oldValue oldFlag : Wasm.Value}
    {flagIndex valueIndex resultIndex stepCost : Nat}
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (initialRelated :
      StateRelated callerFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (flagEmpty :
      initial.globals.globals[flagIndex]? = some (.i32 0))
    (callee :
      BudgetedCapacityPreservingSuccessfulDeclaration context sourceModule
        calleeFunction module hostEnv sourceExternals sourceRuntime callRuntime
        [] calleeCode targetFunction declarationId initial afterCall
        initialWitness callWitness [] resultKind sourceValue physical stepCost)
    (importFound :
      module.imports[cacheSetId]? = some imp)
    (hostSatisfies : hostEnv.Satisfies module spec)
    (importInBounds : cacheSetId < module.imports.length)
    (contractFound :
      spec.contracts[cacheSetId]? =
        some (cacheSetContract declaration kind))
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 1)
    (operation :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache)
    (valueGlobal :
      afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq :
      valueStore = writeWasmGlobal afterCache valueIndex physical)
    (flagGlobal :
      valueStore.globals.globals[flagIndex]? = some oldFlag)
    (distinct : valueIndex ≠ flagIndex)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (nextRelated :
      StateRelated callerFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue)
        (writeWasmGlobal valueStore flagIndex (.i32 1)) nextLocals
        callWitness)
    (publicationOrdinary :
      OrdinaryPersistenceTransport callRuntime nextRuntime)
    (publicationCapacity :
      HeaderCapacityTransport afterCall.host.runtime.heap
        (writeWasmGlobal valueStore flagIndex (.i32 1)).host.runtime.heap
        callWitness)
    (publicationExternals :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.externals =
        afterCall.host.externals)
    (publicationDescriptors :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.closureDescriptors =
        afterCall.host.closureDescriptors)
    (publicationBudget :
      ∀ remainingBytes,
        afterCall.host.runtime.heap.AddressSpaceBudget remainingBytes →
          ((writeWasmGlobal valueStore flagIndex
              (.i32 1)).host.runtime.heap).AddressSpaceBudget
            remainingBytes) :
    BudgetedCapacityPreservingLazyStep .miss context callerFunction module
      hostEnv sourceExternals decl continuation
      [.globalGet flagIndex,
        .iff 0 0 [] [
          .call declarationId,
          .call cacheSetId,
          .globalSet valueIndex,
          .const 1,
          .globalSet flagIndex],
        .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue initial
      (writeWasmGlobal valueStore flagIndex (.i32 1)) locals nextLocals
      resultIndex initialWitness callWitness physical stepCost := by
  apply BudgetedCapacityPreservingLazyStep.miss_of_bodyWP_cacheSet sourceStep
    initialRelated flagEmpty
    callee.capacityPreserving.successful.cachedBody
    callee.capacityPreserving.successful.notImport
    callee.capacityPreserving.successful.functionFound
    importFound hostSatisfies importInBounds contractFound parameterCount
    resultCount operation valueGlobal valueStoreEq flagGlobal distinct
    targetSet nextRelated
  · exact callee.ordinaryTransport.trans publicationOrdinary
  · exact callee.capacityPreserving.witnessTransport
  · exact callee.capacityPreserving.capacityTransport.transAcross
      callee.capacityPreserving.witnessTransport publicationCapacity
  · exact publicationExternals.trans callee.externalsPreserved
  · exact publicationDescriptors.trans callee.hostDescriptorsPreserved
  · exact callee.witnessDescriptorsPreserved
  · intro remainingBytes stepFits budget
    exact publicationBudget _
      (callee.residualBudget stepFits budget)

/--
A budgeted lazy result re-establishes the canonical mixed facts-indexed
frame, erasing only the destination's stale reuse fact.

This is the common hit/miss resource proof. Path-specific implementation
theorems need only build `BudgetedCapacityPreservingLazyStep`; they do not
repeat fact-map, local-frame, handler-table, descriptor, or budget
reconstruction.
-/
theorem
    ConcreteReuseCapacityPureExternalOwnershipFrame.ofLazyCacheResult
    {path : LazyCachePath}
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial nextStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {resultIndex remainingBytes stepCost : Nat}
    {initialWitness nextWitness : RefinementWitness}
    {physical : Wasm.Value}
    (invariant :
      ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (stepFits : stepCost ≤ remainingBytes)
    (step :
      BudgetedCapacityPreservingLazyStep path context sourceFunction module
        hostEnv sourceExternals decl continuation targetValue sourceRuntime
        nextRuntime sourceEnv sourceValue initial nextStore locals nextLocals
        resultIndex initialWitness nextWitness physical stepCost)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId)) :
    ∃ resultStore resultLocals resultWitness nextFacts,
      LazyLetStepSimulates path context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue initial resultStore locals
          resultLocals resultIndex initialWitness resultWitness ∧
        resultStore.host.externals = initial.host.externals ∧
          resultStore.host.closureDescriptors =
              initial.host.closureDescriptors ∧
            resultWitness.closureDescriptors =
                initialWitness.closureDescriptors ∧
              reuseCapacityLetFacts? facts decl = some nextFacts ∧
                ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
                  sourceExternals nextFacts (remainingBytes - stepCost)
                  nextRuntime (bind sourceEnv decl.fvarId sourceValue)
                  resultStore resultLocals resultWitness := by
  rcases invariant with
    ⟨⟨⟨initialRelated, ordinaryTokens, frameAligned, budget⟩,
      integerImplementation, naturalImplementation, scalarImplementation⟩,
      descriptorAgreement⟩
  have nextRelated :
      ReuseCapacityStateRelated
        (eraseReuseCapacityFact facts decl.fvarId) sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness :=
    initialRelated.eraseResult step.simulates.2.2.1
      resultFound
      (localUpdate_of_set? step.targetSet) step.witnessTransport
      step.capacityTransport
  have nextOrdinary :
      ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts decl.fvarId)
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) := by
    simpa using ordinaryTokens.eraseBind step.ordinaryTransport
  have lengths := FirTalos.Correctness.locals_lengths_of_set? step.targetSet
  have nextFrameAligned :
      ConcreteLocalFrameAligned sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness :=
    ⟨lengths.1.trans frameAligned.1, lengths.2.trans frameAligned.2⟩
  have nextBudget :
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - stepCost) :=
    step.residualBudget remainingBytes stepFits budget
  have nextDescriptorAgreement :
      nextStore.host.closureDescriptors =
        nextWitness.closureDescriptors :=
    step.hostDescriptorsPreserved.trans
      (descriptorAgreement.trans step.witnessDescriptorsPreserved.symm)
  exact ⟨nextStore, nextLocals, nextWitness,
    eraseReuseCapacityFact facts decl.fvarId, step.simulates,
    step.externalsPreserved, step.hostDescriptorsPreserved,
    step.witnessDescriptorsPreserved, transfer,
    ⟨⟨⟨nextRelated, nextOrdinary, nextFrameAligned, nextBudget⟩,
      by rw [step.externalsPreserved]; exact integerImplementation,
      by rw [step.externalsPreserved]; exact naturalImplementation,
      by rw [step.externalsPreserved]; exact scalarImplementation⟩,
      nextDescriptorAgreement⟩⟩

/--
Uniform implementation condition for compiler-generated lazy declarations.

From the source path/admission and the actual compiler/adapter outputs, the
generated-program theorem selects one budgeted hit or miss result. This is a
declaration-environment property, not a caller-provided target execution
certificate.
-/
def LazyCacheImplementation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (LazySupported :
      LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop) : Prop :=
  ∀ {path : LazyCachePath}
      {facts : ReuseCapacityFacts}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {valueCode : List Fir.Wasm.Instruction}
      {targetValue : Wasm.Program}
      {initial : Wasm.Store Host}
      {locals : Wasm.Locals}
      {resultIndex stepCost : Nat}
      {initialWitness : RefinementWitness},
    LazySupported path sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost →
      SourceLazyLetResult path context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue →
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        initial locals initialWitness →
      Fir.Wasm.compileLetValue context decl = .ok valueCode →
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue →
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex →
      ∃ nextStore nextLocals nextWitness physical,
        BudgetedCapacityPreservingLazyStep path context sourceFunction module
            hostEnv sourceExternals decl continuation targetValue sourceRuntime
            nextRuntime sourceEnv sourceValue initial nextStore locals
            nextLocals resultIndex initialWitness nextWitness physical
            stepCost ∧
          reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId)

/-- A uniform lazy-declaration implementation instantiates the generic cache
law for the canonical mixed frame. -/
theorem LazyCacheImplementation.runtimeRefines
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {LazySupported :
      LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    (implementation :
      LazyCacheImplementation context sourceModule sourceFunction labels module
        hostEnv sourceExternals LazySupported) :
    ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels module hostEnv sourceExternals LazySupported
      (ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
        sourceExternals) := by
  intro path facts sourceRuntime nextRuntime sourceEnv decl continuation
    sourceValue valueCode targetValue initial locals resultIndex remainingBytes
    stepCost initialWitness supported stepFits invariant sourceStep
    valueCompiled valueAdapted resultFound
  obtain ⟨nextStore, nextLocals, nextWitness, physical, step, transfer⟩ :=
    implementation supported sourceStep invariant.1.1.1 valueCompiled
      valueAdapted resultFound
  exact invariant.ofLazyCacheResult stepFits step resultFound transfer

end FirTalos.Concrete
