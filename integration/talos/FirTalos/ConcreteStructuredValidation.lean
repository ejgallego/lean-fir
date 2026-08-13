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
