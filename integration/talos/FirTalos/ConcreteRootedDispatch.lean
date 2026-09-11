import FirTalos.ConcreteRootResult
import FirTalos.ConcreteResumableWasm

/-!
# Rooted, precise one-step compiler dispatch

This additive proof companion retains the actual witness and each named
successor's checked caller spine. Only a returned focus identifies its represented
kind with the active function result. That active result can differ from the
original root inside a call; ready and bind temporaries retain their own ABIs.

The ordinary dispatcher consumes existing admission once and packages one
accepted rooted producer per branch. Seven-focus one-step closure then reuses
the independent compiler-admission and address-space laws for code only, and
the stored ready/bind/return evidence otherwise. Neither theorem derives those
laws, changes runtime state, or assembles schema, finite-prefix or terminal simulation.
-/

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Witness-indexed named outcomes with their own root evidence and precise returns. -/
inductive ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : ExternalImpl)
    (rootResult : AbiKind)
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
        sourceCode targetStore targetLocals targetCode witness source target)
      (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
        related.agrees related.frames.validation) :
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness source target
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
        targetRest targetFrames witness physicalArgs resultIndex source target)
      (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
        related.agrees related.frames.validation) :
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness source target
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
        witness resultIndex source target)
      (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
        related.agrees related.frames.validation) :
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness source target
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
        resultIndex source target)
      (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
        related.agrees related.frames.validation) :
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness source target
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
        physicalArgs callIndex resultIndex source target)
      (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
        related.agrees related.frames.validation) :
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness source target
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
        physical resultIndex source target)
      (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
        related.agrees related.frames.validation) :
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness source target
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
      {physical : Wasm.Value}
      {source : MachineState}
      {target : StructuredWasmState Host}
      (related : ConcreteStructuredValidatedReturnedOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec
        externals labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        sourceValue targetStore targetLocals witness functionResult physical source
        target)
      (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
        related.agrees related.frames.validation) :
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness source target

/-- Forget only the additive root/return precision metadata. -/
theorem ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.toValidatedGlobalAt
    {program sourceModule targetModule hosts externals rootResult witness source target}
    (related : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals rootResult witness source target) :
    ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals witness source target := by
  cases related with
  | code activeResult next _ => exact .code activeResult next
  | directReady next _ => exact .directReady next
  | saturatedReady next _ => exact .saturatedReady next
  | lazyReady next _ => exact .lazyReady next
  | externalReady next _ => exact .externalReady next
  | externalBind next _ => exact .externalBind next
  | returned next _ => exact .returned next

/-- Compose the accepted root-preserving producers for every ordinary admission.
The current witness may change; costs and the zero-step rank come from the same
producer as the named successor, without independently matching existentials. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_atRoot_of_admission
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
    {functionResult rootResult : AbiKind}
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
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
      externals functionResult facts sourceRuntime sourceEnv requiredBytes
      sourceCode)
    (budget : requiredBytes ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  cases admitted with
  | ret resultCompiled resultCompatible resultSemantic =>
      obtain ⟨targetAfter, sourceValue, physical, targetPath, next, nextRoot, _⟩ :=
        related.advance_returnPreciseAtRoot_of_step activeResult rooted
          (.ret resultCompiled resultCompatible resultSemantic) sourceStep
      exact ⟨2, targetAfter, witness, targetPath, .returned next nextRoot, by omega⟩
  | directLet supported =>
      obtain ⟨targetAfter, nextRuntime, sourceValue, nextStore,
          resumedLocals, nextWitness, nextFacts, nextTargetCode, targetCount,
          targetPath, targetPositive, next, nextRoot, _⟩ :=
        related.advance_directLetAtRoot_of_step rooted supported budget sourceStep
      exact ⟨targetCount, targetAfter, nextWitness, targetPath,
        .code activeResult next nextRoot, by omega⟩
  | pureExternal supported =>
      obtain ⟨site, physicalArgs, operation, resolvedResultKind,
          targetImport, callIndex, resultIndex, targetArguments, targetRest,
          targetAfter, targetPath, next, nextRoot, rank⟩ :=
        related.advance_pureExternal_stageAtRoot activeResult rooted supported budget
          sourceStep
      exact ⟨targetArguments.length, targetAfter, witness, targetPath,
        .externalReady next nextRoot, fun zero => rank⟩
  | directCall site =>
      obtain ⟨calleeContext, calleeFunction, row, physicalArgs, resultIndex,
          targetArguments, targetRest, targetAfter, targetPath, next, nextRoot, rank⟩ :=
        related.advance_directCall_stageAtRoot_of_step activeResult rooted site sourceStep
      exact ⟨targetArguments.length, targetAfter, witness, targetPath,
        .directReady next nextRoot, fun zero => rank⟩
  | saturatedCall site resolution sharedCapacity =>
      obtain ⟨calleeContext, calleeFunction, row, targetValue, targetRest,
          resultIndex, targetPath, next, nextRoot, rank⟩ :=
        related.advance_saturatedCall_stageAtRoot_of_step activeResult rooted site resolution
          sharedCapacity sourceStep
      exact ⟨0, target, witness, targetPath, .saturatedReady next nextRoot, fun _ => rank⟩
  | lazyHit call generated semanticFound =>
      let path : ConcreteStructuredLazyReadyAdmission context sourceModule call
          generated sourceRuntime := .hit _ semanticFound
      obtain ⟨cacheIndex, declarationId, cacheSetId, resultIndex, targetRest,
          targetPath, next, nextRoot, rank⟩ :=
        related.advance_lazy_stageAtRoot_of_step activeResult rooted call generated path
          sourceStep
      exact ⟨0, target, witness, targetPath, .lazyReady next nextRoot, fun _ => rank⟩
  | lazyMiss call generated resultClassified notObject notTObject
      semanticEmpty =>
      let path : ConcreteStructuredLazyReadyAdmission context sourceModule
          call.callSupported generated sourceRuntime :=
        .miss _ call resultClassified notObject notTObject semanticEmpty
      obtain ⟨cacheIndex, declarationId, cacheSetId, resultIndex, targetRest,
          targetPath, next, nextRoot, rank⟩ :=
        related.advance_lazy_stageAtRoot_of_step activeResult rooted call.callSupported
          generated path sourceStep
      exact ⟨0, target, witness, targetPath, .lazyReady next nextRoot, fun _ => rank⟩
  | defaultOnlyCase supported =>
      obtain ⟨targetPath, next, nextRoot, rank, _⟩ :=
        related.advance_defaultOnlyCaseAtRoot_of_step rooted supported sourceStep
      exact ⟨0, target, witness, targetPath, .code activeResult next nextRoot, fun _ => rank⟩
  | objectCases supported =>
      obtain ⟨testCount, targetAfter, selected, selectedTarget, targetSuffix, targetPath,
          next, nextRoot, _selected, _sourceFrames, _targetFrames, zeroRank⟩ :=
        related.advance_objectCasesAtRoot_of_step rooted supported sourceStep
      exact ⟨5 * testCount, targetAfter, witness, targetPath,
        .code activeResult next nextRoot, zeroRank⟩
  | scalarUInt8Cases supported =>
      obtain ⟨testCount, targetAfter, selected, selectedTarget, targetSuffix, targetPath,
          next, nextRoot, _selected, _sourceFrames, _targetFrames, zeroRank⟩ :=
        related.advance_scalarUInt8CasesAtRoot_of_step rooted supported sourceStep
      exact ⟨4 * testCount, targetAfter, witness, targetPath,
        .code activeResult next nextRoot, zeroRank⟩
  | incPersistent =>
      obtain ⟨_admitted, targetPath, _framesEq, next, nextRoot, rank⟩ :=
        related.advance_incPersistentAtRoot_of_step
          (module := targetModule.wasmModule) (hostEnv := hosts.env) rooted sourceStep
      exact ⟨0, target, witness, targetPath, .code activeResult next nextRoot, fun _ => rank⟩
  | decPersistent =>
      obtain ⟨_admitted, targetPath, _framesEq, next, nextRoot, rank⟩ :=
        related.advance_decPersistentAtRoot_of_step
          (module := targetModule.wasmModule) (hostEnv := hosts.env) rooted sourceStep
      exact ⟨0, target, witness, targetPath, .code activeResult next nextRoot, fun _ => rank⟩
  | ordinaryIncrement supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId amount check,
          sourceCode = .inc objectId amount check false continuation := by
        cases supported
        exact ⟨_, _, _, rfl⟩
      obtain ⟨objectId, amount, check, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next, nextRoot, _⟩ :=
        related.advance_ordinaryIncrementAtRoot_of_step rooted supported sourceStep
      exact ⟨2, targetAfter, witness, targetPath, .code activeResult next nextRoot, by omega⟩
  | ordinaryDecrement supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId amount check objectFields?,
          sourceCode =
            .dec objectId amount check false objectFields? continuation := by
        cases supported
        exact ⟨_, _, _, _, rfl⟩
      obtain ⟨objectId, amount, check, objectFields?, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next, nextRoot, _⟩ :=
        related.advance_ordinaryDecrementAtRoot_of_step rooted supported sourceStep
      exact ⟨2, targetAfter, witness, targetPath, .code activeResult next nextRoot, by omega⟩
  | ordinaryDelete supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId,
          sourceCode = .del objectId continuation := by
        cases supported
        exact ⟨_, rfl⟩
      obtain ⟨objectId, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next, nextRoot, _⟩ :=
        related.advance_ordinaryDeleteAtRoot_of_step rooted supported sourceStep
      exact ⟨2, targetAfter, witness, targetPath, .code activeResult next nextRoot, by omega⟩
  | constructorTag supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId tag,
          sourceCode = .setTag objectId tag continuation := by
        cases supported
        exact ⟨_, _, rfl⟩
      obtain ⟨objectId, tag, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next, nextRoot, _⟩ :=
        related.advance_constructorTagAtRoot_of_step rooted supported sourceStep
      exact ⟨2, targetAfter, witness, targetPath, .code activeResult next nextRoot, by omega⟩
  | objectFieldFVar supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId fieldId index,
          sourceCode =
            .oset objectId index (.fvar fieldId) continuation := by
        cases supported
        exact ⟨_, _, _, rfl⟩
      obtain ⟨objectId, fieldId, index, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next, nextRoot, _⟩ :=
        related.advance_objectFieldFVarAtRoot_of_step rooted supported.toActive sourceStep
      exact ⟨3, targetAfter, witness, targetPath, .code activeResult next nextRoot, by omega⟩
  | objectFieldErased supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId index,
          sourceCode = .oset objectId index .erased continuation := by
        cases supported
        exact ⟨_, _, rfl⟩
      obtain ⟨objectId, index, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next, nextRoot, _⟩ :=
        related.advance_objectFieldErasedAtRoot_of_step rooted supported.toActive sourceStep
      exact ⟨3, targetAfter, witness, targetPath, .code activeResult next nextRoot, by omega⟩
  | usizeField supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId fieldId index,
          sourceCode = .uset objectId index fieldId continuation := by
        cases supported
        exact ⟨_, _, _, rfl⟩
      obtain ⟨objectId, fieldId, index, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next, nextRoot, _⟩ :=
        related.advance_usizeFieldAtRoot_of_step rooted supported sourceStep
      exact ⟨3, targetAfter, witness, targetPath, .code activeResult next nextRoot, by omega⟩
  | scalarField supported =>
      rename_i nextRuntime continuation
      have shape : ∃ objectId fieldId slotIndex byteOffset type,
          sourceCode = .sset objectId slotIndex byteOffset fieldId type
            continuation := by
        cases supported
        exact ⟨_, _, _, _, _, rfl⟩
      obtain ⟨objectId, fieldId, slotIndex, byteOffset, type, rfl⟩ := shape
      obtain ⟨targetAfter, nextStore, nextTargetCode, targetPath, next, nextRoot, _⟩ :=
        related.advance_scalarFieldAtRoot_of_step rooted supported sourceStep
      exact ⟨3, targetAfter, witness, targetPath, .code activeResult next nextRoot, by omega⟩

/-- Regression: the actual ordinary dispatcher yields the original root ABI at an empty return. -/
example
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
    {functionResult rootResult : AbiKind}
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
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)

    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
      externals functionResult facts sourceRuntime sourceEnv 0 (.return result))
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetCount targetAfter nextWitness value context' sourceFunction'
        targetStore' targetLocals' physical,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetCount target targetAfter ∧
      ConcreteStructuredYieldFocus context' sourceFunction' sourceAfter.runtime
        sourceAfter.env value targetStore' targetLocals' nextWitness rootResult
        physical sourceAfter targetAfter ∧ sourceAfter.frames = [] := by
  obtain ⟨count, after, nextWitness, path, next, _rank⟩ :=
    related.advance_atRoot_of_admission activeResult rooted admitted (by omega) sourceStep
  have returnedSource : ∃ value, sourceAfter.control = .yielded value ∧
      sourceAfter.frames = [] := by
    have control := related.core.core.focus.sourceControlEq
    cases lookupResult : lookupValue source.env result with
    | error fault =>
        simp [executeStep, coreStep, control, lookupResult, fail] at sourceStep
    | ok value =>
        have afterEq : { source with control := .yielded value } = sourceAfter := by
          simpa [executeStep, coreStep, control, lookupResult] using sourceStep
        rw [← afterEq]
        exact ⟨value, rfl, empty⟩
  obtain ⟨value, control, emptyAfter⟩ := returnedSource
  cases next with
  | code _ next _ =>
      have impossible := next.core.core.focus.sourceControlEq
      rw [control] at impossible
      cases impossible
  | directReady next _ =>
      have impossible := next.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | saturatedReady next _ =>
      have impossible := next.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | lazyReady next _ =>
      have impossible := next.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | externalReady next _ =>
      have impossible := next.core.ready.sourceControlEq
      rw [control] at impossible
      cases impossible
  | externalBind next _ =>
      have impossible := next.core.bindFocus.sourceFramesEq
      rw [emptyAfter] at impossible
      cases impossible
  | returned next nextRoot =>
      have precise := next.yieldAtRoot_of_empty nextRoot emptyAfter
      have valueEq := Control.yielded.inj (control.symm.trans precise.sourceControlEq)
      rw [← precise.sourceRuntimeEq, ← precise.sourceEnvEq, ← valueEq] at precise
      exact ⟨count, after, nextWitness, value, _, _, _, _, _, path, precise, emptyAfter⟩


/- These checks specialize the actual dispatcher, not duplicate local wrappers.
The existential witness is deliberately free to evolve; the zero-count rank
implication is retained even on source-only staging and erased operations. -/
section DispatcherRegressions

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
    {functionResult rootResult : AbiKind}
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

/-- Allocating direct lets do not promise that the successor witness is the input witness. -/
example
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.let decl continuation)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ReuseBudgetedDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    (.directLet supported) budget sourceStep

/-- Persistent inc retains the dispatcher's strict rank condition for a zero-step match. -/
example
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.inc objectId amount check true continuation)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    .incPersistent (by omega) sourceStep

/-- Persistent dec retains the dispatcher's strict rank condition for a zero-step match. -/
example
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.dec objectId amount check true objectFields? continuation)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    .decPersistent (by omega) sourceStep

/-- Default-only case dispatch retains the same zero-step rank condition. -/
example
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {selected : Lean.Compiler.LCNF.Code .impure}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.cases cases)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : DefaultOnlyCaseSupported sourceRuntime sourceEnv cases selected)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    (.defaultOnlyCase supported) (by omega) sourceStep

/-- Legacy object write admission is accepted without any all-witness hypothesis. -/
example
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure} {nextRuntime : RuntimeState}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.oset objectId index (.fvar fieldId) continuation)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ObjectFieldFVarEffectSupported context sourceRuntime
      sourceEnv (.oset objectId index (.fvar fieldId) continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    (.objectFieldFVar supported) (by omega) sourceStep

/-- Legacy object write admission is accepted without any all-witness hypothesis. -/
example
    {objectId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure} {nextRuntime : RuntimeState}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.oset objectId index .erased continuation)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ObjectFieldErasedEffectSupported context sourceRuntime
      sourceEnv (.oset objectId index .erased continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    (.objectFieldErased supported) (by omega) sourceStep

/-- Zero-step lazy staging leaves the cached value kind distinct from caller/root ABIs. -/
example
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {declaration : Lean.Name} {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind} {cachedValue : Value}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.let decl continuation)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (call : LazyCacheCallSupported context decl declaration sourceDeclaration resultKind)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    (_different : resultKind ≠ functionResult)
    (semanticFound : findGlobal? sourceRuntime.globals declaration = some cachedValue)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    (.lazyHit call generated semanticFound) (by omega) sourceStep

/-- An active callee can differ from the original root. Erasure keeps the
same actual witness, target path and zero-step rank implication. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv sourceCode
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (different : functionResult ≠ rootResult)
    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule externals
      functionResult facts sourceRuntime sourceEnv requiredBytes sourceCode)
    (budget : requiredBytes ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ count after nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) count target after ∧
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule targetModule
        hosts externals nextWitness sourceAfter after ∧
      (count = 0 → compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source) ∧ functionResult ≠ rootResult := by
  obtain ⟨count, after, nextWitness, path, next, rank⟩ :=
    related.advance_atRoot_of_admission activeResult rooted admitted budget sourceStep
  exact ⟨count, after, nextWitness, path, next.toValidatedGlobalAt, rank, different⟩

/-- Saturated staging retains its zero-step rank without equating callee and root ABIs. -/
example
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.let decl continuation)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (site : SaturatedClosureCallSite context decl sourceEnv)
    (resolution : SaturatedClosureCallResolution context sourceRuntime site)
    (sharedCapacity : ∀ parentRuntime,
      setCell sourceRuntime resolution.location
          { resolution.cell with rc := resolution.cell.rc - 1 } = .ok parentRuntime →
        ClosureRetainCapacity parentRuntime resolution.captures.toList)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    (.saturatedCall site resolution sharedCapacity) (by omega) sourceStep

/-- Pure-external staging adds no host-result/root-result equality premise. -/
example
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {nextRuntime : RuntimeState} {sourceValue : Value} {stepCost : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.let decl continuation)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : PureExternalSupported context externals sourceRuntime sourceEnv
      decl continuation nextRuntime sourceValue stepCost)
    (budget : stepCost ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  exact related.advance_atRoot_of_admission activeResult rooted
    (.pureExternal supported) budget sourceStep

end DispatcherRegressions

/-- Negative sensitivity: forgetting the represented return kind cannot build
the companion, even when the old returned outcome and its root are available. -/
example
    {program sourceModule targetModule hosts externals rootResult witness}
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
      target)
    (_rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (different : kind ≠ functionResult) : kind ≠ functionResult := by
  fail_if_success
    have bad : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness source target :=
      .returned related _rooted
  exact different

/-- Positive sensitivity: bind temporaries (from cache or external execution)
need not have the active function's or original root's result ABI. -/
example
    {program sourceModule targetModule hosts externals rootResult witness}
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
      physical resultIndex source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (differentActive : kind ≠ functionResult) (differentRoot : kind ≠ rootResult) :
    ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals rootResult witness source target ∧
      kind ≠ functionResult ∧ kind ≠ rootResult :=
  ⟨.externalBind related rooted, differentActive, differentRoot⟩

/-- Repackage the accepted returned dispatch payload, retaining its actual
already-bound code or still-unbound published bind. No pop, publication or
subsequent source transition is executed by this metadata projection. -/
theorem ConcreteStructuredValidatedReturnedOutcome.SuccessorAtRoot.toRootedPreciseGlobal
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
    {functionResult actualKind rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceValue : Value}
    {targetLocals : Wasm.Locals}
    {physical : Wasm.Value}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}

    {related : ConcreteStructuredValidatedReturnedOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceValue targetStore targetLocals witness actualKind physical source
      target}
    {targetCount : Nat} {targetAfter : StructuredWasmState Host}
    (next : related.SuccessorAtRoot rootResult sourceAfter targetCount targetAfter) :
    ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals rootResult witness sourceAfter targetAfter := by
  rcases next with next | next
  · rcases next with ⟨
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      callerResultAt, nextActive, rooted, _⟩
    exact .code callerResultAt nextActive rooted
  · rcases next with ⟨
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, nextBind, rooted, _⟩
    exact .externalBind nextBind rooted

/-- One successful source step closes the accepted seven-focus rooted/precise
companion. Only ordinary code consumes compiler admission and the independent
address-space law; ready/bind/returned cases use their stored validated evidence.
This is one-step closure, not a prefix simulator or a proof of either law. -/
theorem ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.advance_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {externals : ExternalImpl}
    {rootResult : AbiKind} {witness : RefinementWitness}
    {source sourceAfter : MachineState} {target : StructuredWasmState Host}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    (related : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals rootResult witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetCount target targetAfter ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
      (targetCount = 0 → compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source) := by
  cases related with
  | code activeResult related rooted =>
      obtain ⟨requiredBytes, admitted⟩ := admission.code _ activeResult related sourceStep
      have budget := addressSpaceSafety.code related.core.core sourceStep admitted
      exact related.advance_atRoot_of_admission activeResult rooted admitted budget sourceStep
  | directReady related rooted =>
      obtain ⟨after, path, calleeSpec, activeResult, next, nextRoot, _⟩ :=
        related.advance_enterAtRoot_of_step rooted sourceStep
      exact ⟨1, after, witness, path, .code activeResult next nextRoot, by omega⟩
  | saturatedReady related rooted =>
      obtain ⟨after, nextStore, physicalArgs, matcherCount, argumentCount, callRuntime,
          path, positive, calleeSpec, activeResult, next, nextRoot, _⟩ :=
        related.advance_enterAtRoot_of_step rooted sourceStep
      exact ⟨3 * (matcherCount + 1) + argumentCount + 1, after, witness,
        path, .code activeResult next nextRoot, by omega⟩
  | lazyReady related rooted =>
      cases related.path with
      | hit sourceValue semanticFound =>
          obtain ⟨physical, after, path, next, nextRoot⟩ :=
            related.advance_hitAtRoot_of_step rooted semanticFound sourceStep
          exact ⟨4, after, witness, path, .externalBind next nextRoot, by omega⟩
      | miss calleeCode internal resultClassified notObject notTObject semanticEmpty =>
          obtain ⟨calleeContext, calleeFunction, row, after, path,
              calleeSpec, activeResult, next, nextRoot, _⟩ :=
            related.advance_missAtRoot_of_step rooted internal resultClassified
              notObject notTObject semanticEmpty sourceStep
          exact ⟨3, after, witness, path, .code activeResult next nextRoot, by omega⟩
  | externalReady related rooted =>
      obtain ⟨nextStore, nextWitness, physicalResult, after, path, _extends, next, nextRoot⟩ :=
        related.advance_bindAtRoot_of_step rooted sourceStep
      exact ⟨1, after, nextWitness, path, .externalBind next nextRoot, by omega⟩
  | externalBind related rooted =>
      obtain ⟨after, resumedLocals, path, next, nextRoot, _⟩ :=
        related.advance_codeAtRoot_of_step rooted sourceStep
      exact ⟨1, after, witness, path, .code related.activeResult next nextRoot, by omega⟩
  | returned related rooted =>
      obtain ⟨count, after, path, positive, next⟩ :=
        related.advance_atRoot_of_step rooted sourceStep
      exact ⟨count, after, witness, path, next.toRootedPreciseGlobal, by omega⟩

section SevenFocusRegressions

variable
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {externals : ExternalImpl}
    {rootResult : AbiKind} {witness : RefinementWitness}
    {source sourceAfter : MachineState} {target : StructuredWasmState Host}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)

/-- Actual-composition regression for all non-code inputs. Their source rank
is zero, so the new theorem's rank condition rules out a zero-step target match.
No instruction admission or operation-specific successor is supplied here. -/
example
    (related : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals rootResult witness source target)
    (notCode : ∀ code, source.control ≠ .code code)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ count after nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        count target after ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult nextWitness sourceAfter after ∧
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals nextWitness sourceAfter after ∧ 0 < count := by
  obtain ⟨count, after, nextWitness, path, next, rank⟩ :=
    related.advance_of_step admission addressSpaceSafety sourceStep
  have beforeRank : compilerStructuredControlRank source = 0 := by
    cases control : source.control <;>
      simp_all [compilerStructuredControlRank, compilerCodeSilenceRank]
  exact ⟨count, after, nextWitness, path, next, next.toValidatedGlobalAt, by
    have zeroImpossible : count ≠ 0 := by
      intro zero
      have decrease := rank zero
      omega
    omega⟩

/-- The actual host response may extend the witness. Both views below use that
successor witness, not a forced copy of the incoming witness. -/
example
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
      physicalArgs callIndex resultIndex source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ count after nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        count target after ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult nextWitness sourceAfter after ∧
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals nextWitness sourceAfter after ∧
      (count = 0 → compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source) := by
  have current : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals rootResult witness source target :=
    .externalReady related rooted
  obtain ⟨count, after, nextWitness, path, next, rank⟩ :=
    current.advance_of_step admission addressSpaceSafety sourceStep
  fail_if_success
    have reusedWitness : ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness sourceAfter after := next.toValidatedGlobalAt
  exact ⟨count, after, nextWitness, path, next, next.toValidatedGlobalAt, rank⟩

/-- Lazy hit/miss is read from ready.path by the actual composition; this
caller supplies neither a hit/miss classifier nor separate lookup evidence. -/
example
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
      resultIndex source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ count after nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        count target after ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult nextWitness sourceAfter after ∧
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals nextWitness sourceAfter after ∧
      (count = 0 → compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source) := by
  have current : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals rootResult witness source target :=
    .lazyReady related rooted
  obtain ⟨count, after, nextWitness, path, next, rank⟩ :=
    current.advance_of_step admission addressSpaceSafety sourceStep
  exact ⟨count, after, nextWitness, path, next, next.toValidatedGlobalAt, rank⟩

/-- Code's conditional strict rank survives the seven-focus assembly, rather
than being replaced by a positive-target-step requirement. -/
example
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
      sourceCode targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ count after nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        count target after ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult nextWitness sourceAfter after ∧
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals nextWitness sourceAfter after ∧
      (count = 0 → compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source) := by
  have current : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals rootResult witness source target :=
    .code activeResult related rooted
  obtain ⟨count, after, nextWitness, path, next, rank⟩ :=
    current.advance_of_step admission addressSpaceSafety sourceStep
  exact ⟨count, after, nextWitness, path, next, next.toValidatedGlobalAt, rank⟩

end SevenFocusRegressions

section ReturnedCompositionRegressions

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
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {sourceValue : Value}
    {targetLocals : Wasm.Locals}
    {physical : Wasm.Value}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}

variable
    {related : ConcreteStructuredValidatedReturnedOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceValue targetStore targetLocals witness functionResult physical source
      target}
    {targetCount : Nat} {targetAfter : StructuredWasmState Host}


/-- Actual returned composition retains the already-bound caller payload,
including its exact restored environment, indices and case-prefix cost. -/
example
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (head : ConcreteStructuredBindCallerAtHead source.frames) :
    ∃ count after,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) count target after ∧
      0 < count ∧
      related.BindSuccessorAtRoot rootResult sourceAfter count after ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness sourceAfter after := by
  obtain ⟨count, after, path, positive, next⟩ :=
    related.advance_atRoot_of_step rooted sourceStep
  exact ⟨count, after, path, positive, next.bind_of_head head,
    next.toRootedPreciseGlobal⟩

/-- Actual returned composition retains publication as a distinct unbound
ExternalBindOutcome, including the changed cache store and seven-step cost.
It neither executes destination binding nor requires compiler code admission. -/
example
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (head : ConcreteStructuredLazyCallerAtHead source.frames) :
    ∃ count after,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) count target after ∧
      0 < count ∧
      related.LazySuccessorAtRoot rootResult sourceAfter count after ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult witness sourceAfter after := by
  obtain ⟨count, after, path, positive, next⟩ :=
    related.advance_atRoot_of_step rooted sourceStep
  exact ⟨count, after, path, positive, next.lazy_of_head head,
    next.toRootedPreciseGlobal⟩

end ReturnedCompositionRegressions

end FirTalos.Concrete
