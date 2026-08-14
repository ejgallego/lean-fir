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

/-- Module-wide closed relation for active generated code.  The constructor
hides the current generated function, entry anchor, resource budget, residual
validator state, and compiler focus while retaining the proof that the active
function's selected result ABI is the one validated at its root.

Ready-call and yielded branches will join this sum as their validation
transport lemmas are completed; the present relation is already stable across
all active-code successors whose conclusion remains active code. -/
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
  exact ⟨related.contextCaches, nextCore,
    ⟨nextSupported, nextValidation⟩, nextAgrees⟩

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
  exact ⟨contextCaches, validatedCore, frames, agrees⟩

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

end FirTalos.Concrete
