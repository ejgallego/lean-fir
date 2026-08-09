import FirTalos.ConcreteReuseCapacityCacheCorrectness

namespace FirTalos.Concrete.CompilerCorrectnessContract

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- The concrete generated-export boundary retains the phase invariant needed
to identify source declarations with their unique generated call targets. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName) :
    program.NamesUnique :=
  spec.programNamesUnique

/-- The validator's ABI subtyping decision is sufficient to reinterpret an
already-related concrete argument row at the generated callee's exact
parameter kinds; no target execution or translation certificate is needed. -/
example
    {witness : RefinementWitness}
    {actual expected : Array AbiKind}
    {physicals : List Wasm.Value} {semanticValues : List Value}
    (related :
      ConstructorArgumentsRelated witness actual.toList physicals
        semanticValues)
    (refines : Fir.Wasm.kindsRefine actual expected = true) :
    ConstructorArgumentsRelated witness expected.toList physicals
      semanticValues :=
  related.ofKindsRefine refines

/-- Every selected production-generated internal row carries the parameter
identifier uniqueness validated by `lowerSupported`, alongside its exact
lowerer parameter-local row. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (row :
      ConcreteGeneratedInternalDeclaration program declaration context
        sourceCode sourceModule sourceFunction target) :
    Fir.Wasm.declarationParameterIdsUnique declaration = true :=
  row.parameterIdsUnique

/-- Recursive clients retain the exact program and canonical cache-name table
used to construct every production-generated declaration context. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target) :
    context.program = program ∧
      context.cachedDeclarations =
        Fir.Wasm.cachedDeclarationNames program :=
  ⟨row.contextProgram, row.contextCaches⟩

/-- A generated internal declaration carries the compiler-proved identity
between its source name and exact unified Wasm call index. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target) :
    callIndex? sourceModule (.declaration declaration.name) =
      some row.targetFunctionIndex :=
  row.callIndexEq

/-- The real lowerer's front-insert/reverse implementation is exposed as the
source-order declaration parameter row at the proof boundary. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {parameterKinds : Array AbiKind}
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target)
    (known :
      Fir.Wasm.declarationParameterKinds? program declaration =
        some parameterKinds) :
    sourceFunction.params.toList =
      (declaration.params.toList.zip parameterKinds.toList).map
        (fun pair => (pair.fst.fvarId, pair.snd)) :=
  row.sourceParameterBindings known

/-- A caller-side related argument row and the admitted direct-call site are
sufficient to construct the generated callee's exact entry local relation. -/
example
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure} {callerEnv : Env}
    {sourceModule : Fir.Wasm.Module}
    {calleeFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {witness : RefinementWitness} {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList) :
    EnvLocalsRelated witness (functionBindings calleeFunction) site.calleeEnv
      (row.targetFunction.toLocals physicalArgs) :=
  row.entryEnvLocalsRelatedOfArguments site argumentsRelated

/-- A valid caller frame and a production-admitted direct call determine the
complete generated callee-entry frame. No separately supplied translation
certificate or callee invariant is required. -/
example
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {callerEnv : Env} {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule} {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals} {witness : RefinementWitness}
    (callerFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
        facts remainingBytes sourceRuntime callerEnv targetStore callerLocals
        witness)
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList) :
    ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals []
      remainingBytes sourceRuntime site.calleeEnv targetStore
      (row.targetFunction.toLocals physicalArgs) witness :=
  callerFrame.generatedDirectCalleeEntry site row argumentsRelated

/-- The structural call's existing budget-fit check is retained through the
implementation boundary and weakens the generated callee frame to the exact
source-selected body cost. -/
example
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {callerEnv : Env} {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule} {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes stepCost : Nat}
    {sourceRuntime : RuntimeState} {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals} {witness : RefinementWitness}
    (callerFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
        facts remainingBytes sourceRuntime callerEnv targetStore callerLocals
        witness)
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList)
    (stepFits : stepCost ≤ remainingBytes) :
    ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals []
      stepCost sourceRuntime site.calleeEnv targetStore
      (row.targetFunction.toLocals physicalArgs) witness :=
  callerFrame.generatedDirectCalleeEntryAtCost site row argumentsRelated
    stepFits

/--
The recursive finite-evaluation boundary is source-only: a direct-call node
contains its callee and continuation derivations, erases to the ordinary mixed
source judgment, fixes the exact terminal source state, and checks that its
terminal local's ABI refines the enclosing declaration result ABI. No target
program, store, witness, execution, or translation certificate is an input.
-/
example
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    {letCost : LCNF.LetDecl .impure → Nat}
    {context : Fir.Wasm.Context}
    {expectedResult : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value} {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        DirectSupported ExternalSupported LazySupported CaseSupported
        EffectSupported letCost context expectedResult facts sourceRuntime
        sourceEnv sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes) :
    SourceCodeResult context sourceExternals sourceRuntime sourceEnv sourceCode
      resultRuntime resultValue :=
  evaluation.sourceResult

/--
Compile-time harness for the public partial-correctness boundary.

This application intentionally has no `ConcreteCodeSimulation`,
`ReuseCapacityCodeSimulation`, or other translation-certificate premise. If
the public return theorem regresses to such an interface, this module stops
building under `make talos-check`.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {result : FVarId}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.return result) sourceModule
        sourceFunction target hosts exportName)
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    (sourceEvaluation :
      CodeEvaluates context sourceRuntime sourceEnv (.return result)
        resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv (.return result))
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind callerTail) :=
  spec.correctReturn sourceEvaluation stateRelated parameterCount

/--
The structural direct-value theorem accepts one uniform runtime-refinement law,
not a source/target translation derivation.  The complete target program,
every target split, and every numeric local are recovered from
`CodeAdapted`, which itself records the executable compiler/adaptor result.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {targetFunction : Wasm.Function}
    {parameters callerTail : List Wasm.Value}
    {Supported : LCNF.LetDecl .impure → Prop}
    {Invariant :
      RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (evaluation :
      DirectValueEvaluates context Supported sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels sourceCode target)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (invariant : Invariant sourceRuntime sourceEnv initial locals witness)
    (runtimeRefines :
      DirectLetRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv Supported Invariant)
    (parameterCount : parameters.length = targetFunction.numParams)
    (resultCount : targetFunction.results.length = 1) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction labels module hostEnv
          sourceRuntime sourceEnv sourceCode target initial locals witness []
          (ConcreteFunctionBodyPost targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost resultStore physical callerTail)) ∧
        ConcreteRuntimeRel resultStore.host.runtime resultWitness
          resultRuntime ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness resultKind physical resultValue :=
  codeWP_of_directValueEvaluates evaluation adapted localsAligned stateRelated
    invariant runtimeRefines parameterCount resultCount

/--
The first concrete structural instance checks a two-`let` local-alias spine.
Both target `local.get`/`local.set` pairs and all four numeric local indices
come from the production compiler and adapter.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime middleRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {first second : LCNF.LetDecl .impure}
    {result : FVarId}
    {firstValue secondValue resultValue : Value}
    {target : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {targetFunction : Wasm.Function}
    {parameters callerTail : List Wasm.Value}
    (firstSupported : LocalAliasSupported context first)
    (secondSupported : LocalAliasSupported context second)
    (firstStep :
      SourceLetResult context sourceRuntime sourceEnv first middleRuntime
        firstValue)
    (secondStep :
      SourceLetResult context middleRuntime
        (bind sourceEnv first.fvarId firstValue) second resultRuntime
        secondValue)
    (resultLookup :
      lookup
          (bind (bind sourceEnv first.fvarId firstValue)
            second.fvarId secondValue)
          result =
        some resultValue)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let first (.let second (.return result))) target)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals witness)
    (parameterCount : parameters.length = targetFunction.numParams)
    (resultCount : targetFunction.results.length = 1) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction labels module hostEnv
          sourceRuntime sourceEnv
          (.let first (.let second (.return result))) target initial locals
          witness []
          (ConcreteFunctionBodyPost targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost resultStore physical callerTail)) ∧
        ConcreteRuntimeRel resultStore.host.runtime resultWitness
          resultRuntime ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness resultKind physical resultValue := by
  apply codeWP_of_directValueEvaluates
    (.letValue firstSupported firstStep
      (.letValue secondSupported secondStep (.ret resultLookup)))
    adapted localsAligned stateRelated frameAligned
    (directLetRuntimeRefines_localAlias localsAligned)
    parameterCount resultCount

/--
The successful packed-scalar leaf is itself a uniform runtime law. Its only
additional admission fact is source scalar/ABI-kind agreement.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ScalarProjectionSupported context)
      (ConcreteLocalFrameAligned sourceFunction) :=
  spec.directLetRuntimeRefines_scalarProjection

/--
Integer-box admission is entirely source/compiler-facing. In particular it
does not contain a physical lane, allocation result, target index, or
execution witness.
-/
example
    {context : Fir.Wasm.Context} {decl : LCNF.LetDecl .impure}
    (scalarId : FVarId) (kind : BoxedScalarKind) (resultKind : AbiKind)
    (valueEq : decl.value = .box kind.semanticType scalarId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (resultKindEq :
      resultKind = Fir.Wasm.boxResultKind kind.semanticType .tobject)
    (scalarCompiled :
      Fir.Wasm.getLocal context scalarId =
        .ok (.localGet scalarId, kind.abiKind))
    (annotationKind :
      Fir.Wasm.checkedAbiKind kind.semanticType = .ok kind.abiKind)
    (resultCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind)) :
    BoxSupported context decl :=
  .intro scalarId kind resultKind valueEq valueKind resultKindEq
    scalarCompiled annotationKind resultCompiled

/--
The fixed one-slot reservation constructs any concrete boxing branch and
returns the uniformly indexed residual address-space budget.
-/
example
    {state : MemoryState} (valid : state.FrontierInvariant)
    (scalar : BoxedScalar) {remainingBytes : Nat}
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : boxScalarAllocationBytes ≤ remainingBytes) :
    ∃ result word,
      boxScalar state scalar = .ok (result, word) ∧
        result.AddressSpaceBudget
          (remainingBytes - boxScalarAllocationBytes) :=
  valid.boxScalar_eq_ok_of_budget scalar budget fits

/--
Successful integer boxing satisfies the indexed direct runtime law without a
concrete scalar, physical lane, allocation result, target index, or operation
witness.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BoxSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) :=
  spec.directLetRuntimeRefinesWithCost_box

/--
Reset admission is source/compiler-facing: it contains neither a selected
runtime branch nor a concrete heap/address/token witness.
-/
example
    {context : Fir.Wasm.Context} {decl : LCNF.LetDecl .impure}
    (count : Nat) (objectId : FVarId) (objectKind : AbiKind)
    (valueEq : decl.value = .reset count objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok .reuseToken)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (objectRefines : objectKind.refines .tobject = true)
    (resultCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .reuseToken)) :
    ResetSupported context decl :=
  .intro count objectId objectKind valueEq valueKind objectCompiled
    objectRefines resultCompiled

/--
The concrete reset boundary derives all representation branches from the
successful semantic step and preserves both the witness descriptor table and
the exact heap frontier.
-/
example
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime nextRuntime : RuntimeState} {sourceObject sourceToken : Value}
    {word : Word32} {count : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (objectRelated :
      ValueRel witness .tobject (.word32 word) sourceObject)
    (updated :
      reset runtime count sourceObject = .ok (nextRuntime, sourceToken)) :
    ∃ heap nextWitness token,
      resetStep count initial [.i32 (UInt32.ofNat word.value)] =
          .Return [.i32 (UInt32.ofNat token.value)]
            (replaceHeap initial heap) ∧
        WitnessTransport witness nextWitness ∧
        ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
          nextRuntime ∧
        ValueRel nextWitness .reuseToken (.word32 token) sourceToken ∧
        nextWitness.closureDescriptors = witness.closureDescriptors ∧
        MappedHeaderCapacityTransport initial.host.runtime.heap heap witness ∧
        heap.heapCursor = initial.host.runtime.heap.heapCursor :=
  resetStep_of_refines runtimeRelated descriptorsEq objectRelated updated

/--
Successful reset satisfies the cost-indexed direct runtime law under the
ownership frame, without a concrete branch or translation certificate.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    (externals : ExternalImpl)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ResetSupported context)
      directLetAllocationCost
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.directLetRuntimeRefinesWithCost_reset externals

/--
The typed-unbox compatibility boundary is source-only. Tagged operands are
polymorphic; heap operands expose the live semantic cell and stored scalar
kind, never a concrete address or descriptor lookup.
-/
example
    (runtime : RuntimeState) (kind : BoxedScalarKind) (payload : UInt64) :
    SourceUnboxKindCompatible runtime kind (.object (.tagged payload)) :=
  .tagged

example
    {runtime : RuntimeState} {kind : BoxedScalarKind}
    {location : Location} {cell : HeapCell}
    (storedType : Expr) (scalar : BoxedScalar)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .boxed storedType scalar.semanticValue)
    (kindEq : scalar.kind = kind) :
    SourceUnboxKindCompatible runtime kind (.object (.heap location)) :=
  .heap storedType scalar found live objectEq kindEq

/--
Successful compatible unboxing satisfies the indexed direct runtime law
without a concrete object word, descriptor lookup, checked memory read,
numeric target index, or operation witness.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (UnboxSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) :=
  spec.directLetRuntimeRefinesWithCost_unbox

/--
Successful `isShared` observations satisfy the indexed direct runtime law
without target indices, a concrete object word, or an operation witness.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (IsSharedSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) :=
  spec.directLetRuntimeRefinesWithCost_isShared

/--
All nonallocating integer and `USize` literals obtain their constant/write
runtime law from the same source classification.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ImmediateLiteralSupported context)
      (ConcreteLocalFrameAligned sourceFunction) :=
  spec.directLetRuntimeRefines_immediateLiteral

/--
A whole mixed read-only direct-value spine obtains its runtime law from the
concrete supported export. Local aliases, immediate literals, plus object,
`USize`, and successful packed-integer projections may be interleaved; the
client supplies neither target instructions/import indices nor concrete
heap-read witnesses.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {parameters callerTail : List Wasm.Value}
    (evaluation :
      DirectValueEvaluates context (ReadOnlyDirectSupported context)
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals witness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
          sourceRuntime sourceEnv sourceCode spec.targetFunction.body initial
          locals witness []
          (ConcreteFunctionBodyPost spec.targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost resultStore physical callerTail)) ∧
        ConcreteRuntimeRel resultStore.host.runtime resultWitness
          resultRuntime ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness resultKind physical resultValue :=
  codeWP_of_directValueEvaluates evaluation spec.bodyAdapted
    spec.localsAligned stateRelated frameAligned
    spec.directLetRuntimeRefines_readOnlyDirect parameterCount
    spec.singleResult

/--
The arbitrary-precision integer boundary is constructive from one exact
source-facing allocation budget; callers do not supply an allocation result,
limb-count encoding, or representation witness.
-/
example
    {state : MemoryState} {value : Int} {remainingBytes : Nat}
    (valid : state.FrontierInvariant)
    (budget : state.AddressSpaceBudget remainingBytes)
    (fits : integerAllocationBytes value ≤ remainingBytes) :
    ∃ result address,
      allocateInteger state value = .ok (result, address) ∧
        result.AddressSpaceBudget
          (remainingBytes - integerAllocationBytes value) :=
  valid.allocateInteger_eq_ok_of_budget value budget fits

/--
The pure integer-result external boundary is an operation-family law plus the
source result and its exact budget. Callers do not supply the concrete
allocation, result address, extended witness, or handler response.
-/
example
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {value : Int} {remainingBytes : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (implementationRelated :
      concreteImplementation.IntegerResultRefines semanticImplementation)
    (requestRelated :
      ConcreteExternalRequestRel beforeWitness concreteRequest semanticRequest)
    (resultKind : concreteRequest.resultKind = .tobject)
    (semanticCalled :
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticIntegerExternalResponse semanticBefore value))
    (budget :
      concreteBefore.heap.AddressSpaceBudget remainingBytes)
    (fits : integerAllocationBytes value ≤ remainingBytes) :
    ∃ result address,
      allocateInteger concreteBefore.heap value = .ok (result, address) ∧
        concreteImplementation.invoke concreteRequest concreteBefore =
          .ok (concreteBefore.applyExternalResponse concreteRequest
              (concreteIntegerExternalResponse concreteBefore result address),
            (concreteIntegerExternalResponse concreteBefore result address).value) ∧
        semanticImplementation.call semanticRequest semanticBefore =
          .ok (semanticIntegerExternalResponse semanticBefore value) ∧
        ConcretePureExternalPost concreteBefore beforeWitness
          (beforeWitness.bindInteger semanticBefore.nextLocation address value)
          semanticBefore concreteRequest semanticRequest
          (concreteIntegerExternalResponse concreteBefore result address)
          (semanticIntegerExternalResponse semanticBefore value) ∧
        result.AddressSpaceBudget
          (remainingBytes - integerAllocationBytes value) :=
  runtimeRelated.invoke_pure_integer_result_refines_of_budget
    implementationRelated requestRelated resultKind semanticCalled budget fits

/--
The compiler-level pure-Int law is discharged from the whole generated-export
package and the installed operation-family implementation law. Its interface
contains no target code, numeric indices, physical operands, concrete
response, allocation result, or per-program simulation certificate.
-/
example : PureIntegerExternalName ``Int.ofNat := .intOfNat
example : PureIntegerExternalName ``Int.neg := .intNeg
example : PureIntegerExternalName ``Int.add := .intAdd
example : PureIntegerExternalName ``Int.sub := .intSub

example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureIntegerExternalSupported context externals)
      (ConcreteBudgetedIntegerExternalFrame sourceFunction externals) :=
  spec.externalLetRuntimeRefinesWithCost_pureInteger externals

/--
`Int.natAbs`, `Nat.add`, and `Nat.sub` are admitted through the
representation-polymorphic natural-result family. The compiler law constructs
all adapted code, indices, allocation artifacts, and the post-witness
internally.
-/
example : PureNaturalExternalName ``Int.natAbs := .intNatAbs
example : PureNaturalExternalName ``Nat.add := .natAdd
example : PureNaturalExternalName ``Nat.sub := .natSub

example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureNaturalExternalSupported context externals)
      (ConcreteBudgetedNaturalExternalFrame sourceFunction externals) :=
  spec.externalLetRuntimeRefinesWithCost_pureNatural externals

/--
One source-facing natural result and exact budget construct the physical
representation, extended witness, exact event trace, and residual budget.
-/
example
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {beforeWitness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {value remainingBytes : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore beforeWitness semanticBefore)
    (implementationRelated :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        concreteImplementation semanticImplementation)
    (requestRelated :
      ConcreteExternalRequestRel beforeWitness concreteRequest semanticRequest)
    (resultKind : concreteRequest.resultKind = .tobject)
    (semanticCalled :
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticNaturalExternalResponse semanticBefore value))
    (budget :
      concreteBefore.heap.AddressSpaceBudget remainingBytes)
    (fits : naturalAllocationBytes value ≤ remainingBytes) :
    ∃ result word afterWitness,
      allocateNatural concreteBefore.heap value = .ok (result, word) ∧
        concreteImplementation.invoke concreteRequest concreteBefore =
          .ok (concreteBefore.applyExternalResponse concreteRequest
              (concreteNaturalExternalResponse concreteBefore result word),
            (concreteNaturalExternalResponse concreteBefore result word).value) ∧
        semanticImplementation.call semanticRequest semanticBefore =
          .ok (semanticNaturalExternalResponse semanticBefore value) ∧
        ConcretePureExternalPost concreteBefore beforeWitness afterWitness
          semanticBefore concreteRequest semanticRequest
          (concreteNaturalExternalResponse concreteBefore result word)
          (semanticNaturalExternalResponse semanticBefore value) ∧
        result.AddressSpaceBudget
          (remainingBytes - naturalAllocationBytes value) :=
  FirTalos.Concrete.ConcreteRuntimeRel.invoke_pure_natural_result_refines_of_budget
    runtimeRelated implementationRelated requestRelated resultKind
      semanticCalled budget fits

/--
The resident Int/Nat decisions are admitted only at their exact `UInt8`
result kind. The generic scalar runtime law preserves the heap and witness and
returns the canonical unboxed lane.
-/
example : PureScalarExternalName ``Int.decLt .uint8 := .intDecLt
example : PureScalarExternalName ``Nat.decEq .uint8 := .natDecEq
example : PureScalarExternalName ``Nat.decLt .uint8 := .natDecLt
example : PureScalarExternalName ``Nat.decLe .uint8 := .natDecLe

example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureScalarExternalSupported context externals)
      (ConcreteBudgetedScalarExternalFrame sourceFunction externals) :=
  spec.externalLetRuntimeRefinesWithCost_pureScalar externals

/--
The three pure-result families expose one compositional runtime law. Clients
may admit them through one source-facing disjunction while retaining every
installed implementation law in a shared frame.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureExternalSupported context externals)
      (ConcreteBudgetedPureExternalFrame sourceFunction externals) :=
  spec.externalLetRuntimeRefinesWithCost_pureExternal externals

example
    {concreteImplementation : ConcreteExternalImpl}
    {semanticImplementation : ExternalImpl}
    {concreteBefore : ConcreteRuntimeState}
    {witness : RefinementWitness}
    {semanticBefore : RuntimeState}
    {concreteRequest : ConcreteExternalRequest}
    {semanticRequest : ExternalRequest}
    {scalar : BoxedScalar}
    (runtimeRelated :
      ConcreteRuntimeRel concreteBefore witness semanticBefore)
    (implementationRelated :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        concreteImplementation semanticImplementation)
    (requestRelated :
      ConcreteExternalRequestRel witness concreteRequest semanticRequest)
    (resultKind : concreteRequest.resultKind = scalar.kind.abiKind)
    (semanticCalled :
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticScalarExternalResponse semanticBefore scalar)) :
    concreteImplementation.invoke concreteRequest concreteBefore =
        .ok (concreteBefore.applyExternalResponse concreteRequest
            (concreteScalarExternalResponse concreteBefore scalar),
          (concreteScalarExternalResponse concreteBefore scalar).value) ∧
      semanticImplementation.call semanticRequest semanticBefore =
        .ok (semanticScalarExternalResponse semanticBefore scalar) ∧
      ConcretePureExternalPost concreteBefore witness witness semanticBefore
        concreteRequest semanticRequest
        (concreteScalarExternalResponse concreteBefore scalar)
        (semanticScalarExternalResponse semanticBefore scalar) := by
  have concreteCalled :=
    implementationRelated runtimeRelated requestRelated semanticCalled
  exact
    FirTalos.Concrete.ConcreteExternalImpl.invoke_pure_scalar_result_refines
      runtimeRelated requestRelated resultKind concreteCalled semanticCalled

/--
An arbitrary finite natural-literal spine uses one source-computed budget
across immediate, promoted-tag, and heap-limb representations.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {parameters callerTail : List Wasm.Value}
    (evaluation :
      DirectValueEvaluates context (NaturalLiteralSupported context)
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals witness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget
        (DirectValuePathCost directLetAllocationCost sourceCode))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
          sourceRuntime sourceEnv sourceCode spec.targetFunction.body initial
          locals witness []
          (ConcreteFunctionBodyPost spec.targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost resultStore physical callerTail)) ∧
        ConcreteRuntimeRel resultStore.host.runtime resultWitness
          resultRuntime ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness resultKind physical resultValue :=
  codeWP_of_directValueEvaluates_withCost evaluation spec.bodyAdapted
    spec.localsAligned stateRelated ⟨frameAligned, budget⟩
    spec.directLetRuntimeRefines_naturalLiteral parameterCount
    spec.singleResult

/--
An arbitrary finite String-literal spine uses one source-computed wasm32
budget. Each generated allocation consumes its exact cost and the structural
induction passes the residual budget to the remaining source code.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {parameters callerTail : List Wasm.Value}
    (evaluation :
      DirectValueEvaluates context (StringLiteralSupported context)
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals witness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget
        (DirectValuePathCost directLetAllocationCost sourceCode))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
          sourceRuntime sourceEnv sourceCode spec.targetFunction.body initial
          locals witness []
          (ConcreteFunctionBodyPost spec.targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost resultStore physical callerTail)) ∧
        ConcreteRuntimeRel resultStore.host.runtime resultWitness
          resultRuntime ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness resultKind physical resultValue :=
  codeWP_of_directValueEvaluates_withCost evaluation spec.bodyAdapted
    spec.localsAligned stateRelated ⟨frameAligned, budget⟩
    spec.directLetRuntimeRefines_stringLiteral parameterCount spec.singleResult

/--
The same indexed structural theorem covers arbitrary finite nonempty
constructor spines. Source/compiler admission contains layout bounds only;
each mixed local/erased physical prefix and concrete allocation step is
derived at its source node.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {parameters callerTail : List Wasm.Value}
    (evaluation :
      DirectValueEvaluates context (NonemptyConstructorSupported context)
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals witness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget
        (DirectValuePathCost directLetAllocationCost sourceCode))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
          sourceRuntime sourceEnv sourceCode spec.targetFunction.body initial
          locals witness []
          (ConcreteFunctionBodyPost spec.targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost resultStore physical callerTail)) ∧
        ConcreteRuntimeRel resultStore.host.runtime resultWitness
          resultRuntime ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness resultKind physical resultValue :=
  codeWP_of_directValueEvaluates_withCost evaluation spec.bodyAdapted
    spec.localsAligned stateRelated ⟨frameAligned, budget⟩
    spec.directLetRuntimeRefines_nonemptyConstructor parameterCount
    spec.singleResult

/--
The mixed indexed fragment interleaves cost-zero aliases, immediate literals,
successful object/`USize`/packed-scalar projections, and sharing observations
with allocating Strings and nonempty constructors under one source path cost.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {parameters callerTail : List Wasm.Value}
    (evaluation :
      DirectValueEvaluates context (BudgetedDirectSupported context)
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals witness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget
        (DirectValuePathCost directLetAllocationCost sourceCode))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
          sourceRuntime sourceEnv sourceCode spec.targetFunction.body initial
          locals witness []
          (ConcreteFunctionBodyPost spec.targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost resultStore physical callerTail)) ∧
        ConcreteRuntimeRel resultStore.host.runtime resultWitness
          resultRuntime ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness resultKind physical resultValue :=
  codeWP_of_directValueEvaluates_withCost evaluation spec.bodyAdapted
    spec.localsAligned stateRelated ⟨frameAligned, budget⟩
    spec.directLetRuntimeRefines_budgetedDirect parameterCount
    spec.singleResult

/--
The public whole-export theorem exposes the same budgeted direct fragment
without a `CodeWP`, target program, translation certificate, concrete
operation witness, or per-node allocation premise.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    (evaluation :
      DirectValueEvaluates context (BudgetedDirectSupported context)
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget
        (DirectValuePathCost directLetAllocationCost sourceCode))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedDirect evaluation stateRelated frameAligned budget
    parameterCount

/--
The mixed direct/external endpoint is also certificate-free. External result
allocation is represented by the source evaluation's Nat cost index, while
the reusable external runtime law supplies the implementation proof for the
admitted operation family. The public application contains no target body,
numeric Wasm index, concrete response, or per-node simulation witness.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {directCost : LCNF.LetDecl .impure → Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals DirectSupported
        ExternalSupported directCost sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (directRuntimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env DirectSupported directCost
        (ConcreteBudgetedLocalFrame sourceFunction))
    (externalRuntimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals ExternalSupported
        (ConcreteBudgetedLocalFrame sourceFunction))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedSpine evaluation stateRelated frameAligned budget
    directRuntimeRefines externalRuntimeRefines parameterCount

/--
The concrete mixed endpoint needs no runtime-law arguments for the operation
families already proved by W6. Direct helpers preserve the installed external
implementation, so pure integer construction and arithmetic calls may occur
anywhere in the same budgeted source spine.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals
        (BudgetedDirectSupported context)
        (PureIntegerExternalSupported context externals)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (implementation :
      initial.host.externals.IntegerResultRefines externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedIntegerExternalSpine evaluation stateRelated frameAligned
    budget implementation parameterCount

/--
The natural-result whole-export endpoint likewise needs only source
evaluation, the initial state/frame relation, one path budget, and the
installed operation-family law.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals
        (BudgetedDirectSupported context)
        (PureNaturalExternalSupported context externals)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (implementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedNaturalExternalSpine evaluation stateRelated frameAligned
    budget implementation parameterCount

/--
The scalar-result whole-export endpoint needs no allocation or representation
witness from its caller.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals
        (BudgetedDirectSupported context)
        (PureScalarExternalSupported context externals)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (implementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedScalarExternalSpine evaluation stateRelated frameAligned
    budget implementation parameterCount

/--
One certificate-free whole-export theorem covers source spines that mix the
integer, natural, and scalar external families. The caller supplies the three
stable operation-family laws once, not a runtime-law or target witness at each
source node.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalSpine evaluation stateRelated frameAligned
    budget integerImplementation naturalImplementation scalarImplementation
    parameterCount

/--
Default-only case compilation supplies the generic case implementation law
without a target witness or per-program translation certificate.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} :
    CaseRuntimeRefines context sourceModule sourceFunction labels module hostEnv
      DefaultOnlyCaseSupported :=
  caseRuntimeRefines_defaultOnly

/-- Exact explicit returns satisfy the generated case-arm resumption law. -/
example
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {targetStore : Wasm.Store Host}
    {physical : Wasm.Value}
    {tail : List Wasm.Value} :
    CaseResumptionStable module hostEnv tail
      (ExactReturnControlPost targetStore physical) := by
  intro continuation returned
  subst continuation
  rfl

/-- Stable case posts remain stable through one nested generated arm. -/
example
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (stable : CaseResumptionStable module hostEnv tail Q) :
    CaseResumptionStable module hostEnv tail
      (CaseResumePost module hostEnv [] Q tail) :=
  stable.resume

/--
Successful production compilation of any case node exposes its actual
fallback and adapted constructor chain. Callers do not provide a parallel
target description.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {cases : LCNF.Cases .impure}
    {target : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels (.cases cases)
        target) :
    CasesAdapted context sourceModule sourceFunction labels cases target :=
  CodeAdapted.cases_eq adapted

/--
Every normalized object-constructor chain, of arbitrary arity and with an
optional trailing default, is implemented by the compiler-derived concrete
`getTag` dispatcher.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    CaseRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (ObjectConstructorCasesSupported context) :=
  spec.caseRuntimeRefines_objectConstructorCases

/--
Every normalized scalar `UInt8` constructor chain is implemented by direct
compiler-derived local comparisons; source admission contains no target
program, runtime import, or dynamic tag-range witness.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    CaseRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (ScalarUInt8CasesSupported context) :=
  spec.caseRuntimeRefines_scalarUInt8Cases

/--
Singleton object-constructor cases are implemented by the compiler-derived
concrete `getTag` dispatcher, with no target witness in source admission.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    CaseRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (SingleObjectConstructorCaseSupported context) :=
  spec.caseRuntimeRefines_singleObjectConstructor

/--
Two ordered object-constructor tests and their default are implemented by the
same compiler-derived concrete dispatcher law.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {labels : List FVarId} :
    CaseRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (TwoObjectConstructorDefaultCasesSupported context) :=
  spec.caseRuntimeRefines_twoObjectConstructorDefault

/--
Persistent increments and decrements satisfy the generic no-result effect
condition for every invariant. Their source and compiled target steps are
exact no-ops.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop} :
    EffectRuntimeRefines context sourceModule sourceFunction labels module
      hostEnv PersistentOwnershipEffectSupported Invariant :=
  effectRuntimeRefines_persistentOwnership

/--
Uniform operation-family laws compose through a source-facing disjoint union.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {left right : EffectSupportedPredicate}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (leftRefines :
      EffectRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv left Invariant)
    (rightRefines :
      EffectRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv right Invariant) :
    EffectRuntimeRefines context sourceModule sourceFunction labels module
      hostEnv (EffectSupportedOr left right) Invariant := by
  apply EffectRuntimeRefines.or
  · exact leftRefines
  · exact rightRefines

/--
Ordinary increments satisfy the generic effect condition for the complete
budgeted pure-external frame. Compiler and resolver indices remain internal to
the implementation law.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OrdinaryIncrementEffectSupported context)
      (ConcreteBudgetedPureExternalFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ordinaryIncrement

/--
Ordinary recursive decrements satisfy the generic effect condition when the
threaded frame carries immutable closure-descriptor agreement.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OrdinaryDecrementEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ordinaryDecrement

/--
Explicit deletion satisfies the generic effect condition for both ordinary
heap objects and the exact erased reset token.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OrdinaryDeleteEffectSupported context)
      (ConcreteBudgetedPureExternalFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ordinaryDelete

/--
Successful constructor-tag mutation satisfies the generic effect condition
without a caller-supplied target prefix, numeric index, or simulation witness.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ConstructorTagEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_constructorTag

/--
Successful FVar object-field mutation satisfies the generic effect condition.
The source typing premise supplies descriptor-slot kind agreement, while
production compilation and state refinement recover all concrete witnesses.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ObjectFieldFVarEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_objectFieldFVar

/--
Successful erased object-field mutation satisfies the generic effect
condition. Compiler inversion reconstructs the canonical zero prefix; source
admission carries only descriptor-slot kind agreement.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ObjectFieldErasedEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_objectFieldErased

/--
Both FVar and erased object-field writes satisfy one structural effect law.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ObjectFieldEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_objectField

/--
Successful `USize` field mutation satisfies the generic effect condition using
only source lookups, update/bounds facts, and source-local compiler equations.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (USizeFieldEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_usizeField

/--
Object and `USize` field writes satisfy one structural effect law.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (FieldMutationEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_fieldMutation

/--
Successful packed `UInt8`/`UInt16`/`UInt32`/`UInt64` field mutation satisfies
the generic effect condition using only source facts and the compiler-shaped
layout judgment.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ScalarFieldEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_scalarField

/--
Object, `USize`, and all four supported packed-integer field writes satisfy one
structural effect law.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (AllFieldMutationEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_allFieldMutation

/--
All currently proved ownership operations satisfy one uniform effect condition
and may therefore be interleaved in a single structural source evaluation.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OwnershipEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ownership

/--
The ownership family and constructor-tag mutation satisfy one uniform effect
condition and may be interleaved in a single structural source evaluation.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OwnershipAndTagEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ownershipAndTag

/--
Ownership, tag mutation, and FVar object-field mutation satisfy one uniform
effect condition and may be interleaved structurally.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (OwnershipTagAndObjectFVarEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ownershipTagAndObjectFVar

/--
Ownership, tag mutation, and both object-field argument forms satisfy one
uniform effect condition and may be interleaved structurally.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (OwnershipTagAndObjectEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ownershipTagAndObject

/--
Ownership, tag mutation, object mutation, and `USize` mutation satisfy one
uniform effect condition and may be interleaved structurally.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (OwnershipTagAndFieldMutationEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ownershipTagAndFieldMutation

/--
Ownership, tag mutation, and every supported successful constructor-field
mutation satisfy one uniform structural effect condition.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (OwnershipTagAndAllFieldMutationEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
  spec.effectRuntimeRefines_ownershipTagAndAllFieldMutation

/--
The mixed whole-export theorem admits arbitrary nesting of sole-default cases
around every currently proved direct and resident numeric operation.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported NoEffectsSupported directLetAllocationCost
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue
        requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalDefaultCases evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation parameterCount

/--
The whole-export theorem admits arbitrary interleaving of compiler-erased
persistent ownership effects with default cases, direct operations, and pure
externals, without charging heap budget for either ownership node.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported PersistentOwnershipEffectSupported
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalPersistentOwnership evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation parameterCount

/--
The whole-export theorem admits arbitrary interleaving of successful ordinary
increments with default cases, direct operations, and pure externals, while
preserving the allocation budget across every header-only update.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OrdinaryIncrementEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOrdinaryIncrements evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation parameterCount

/--
The ownership-aware whole-export theorem admits arbitrary successful recursive
decrements mixed with default cases, direct operations, and pure externals.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OrdinaryDecrementEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOrdinaryDecrements evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation descriptorAgreement parameterCount

/--
The whole-export theorem admits arbitrary successful explicit deletions mixed
with default cases, direct operations, and pure externals.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OrdinaryDeleteEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOrdinaryDeletes evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation parameterCount

/--
The mixed ownership endpoint admits persistent operations, ordinary increment,
recursive decrement, and explicit deletion in any order.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OwnershipEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOwnership evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation descriptorAgreement parameterCount

/--
The mixed ownership-and-tag endpoint admits successful constructor-tag
mutation together with every proved ownership effect, default cases, direct
operations, and pure externals.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OwnershipAndTagEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOwnershipAndTag evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation descriptorAgreement parameterCount

/--
The mixed ownership/tag/object endpoint admits successful FVar object-field
mutation together with all previously proved effects, default cases, direct
operations, and pure externals.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndObjectFVarEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOwnershipTagAndObjectFVar evaluation
    stateRelated frameAligned budget integerImplementation naturalImplementation
    scalarImplementation descriptorAgreement parameterCount

/--
The mixed whole-export theorem admits both FVar and erased object-field writes
alongside ownership, tag mutation, default cases, direct operations, and pure
externals.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndObjectEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOwnershipTagAndObject evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation descriptorAgreement parameterCount

/--
The mixed whole-export theorem admits object and `USize` field writes alongside
ownership, tag mutation, default cases, direct operations, and pure externals.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndFieldMutationEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOwnershipTagAndFieldMutation evaluation
    stateRelated frameAligned budget integerImplementation naturalImplementation
    scalarImplementation descriptorAgreement parameterCount

/--
The mixed whole-export theorem admits object, `USize`, and packed-integer field
writes alongside ownership, tag mutation, default cases, direct operations,
and pure externals.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOwnershipTagAndAllFieldMutation evaluation
    stateRelated frameAligned budget integerImplementation naturalImplementation
    scalarImplementation descriptorAgreement parameterCount

/--
The strongest ownership/field-mutation whole-export endpoint also admits
branch-independent successful reset as a direct declaration.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (OwnershipBudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalOwnershipTagAllFieldMutationAndReset
    evaluation stateRelated frameAligned budget integerImplementation
    naturalImplementation scalarImplementation descriptorAgreement
    parameterCount

/--
The mixed whole-export theorem admits arbitrary nesting of normalized
object-constructor chains around every currently proved direct and resident
numeric operation.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        (ObjectConstructorCasesSupported context)
        NoEffectsSupported directLetAllocationCost sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalObjectConstructorCases evaluation
    stateRelated frameAligned budget integerImplementation
    naturalImplementation scalarImplementation parameterCount

/--
The mixed whole-export theorem also admits arbitrary nesting of normalized
scalar `UInt8` constructor chains around every currently proved direct and
resident numeric operation.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        (ScalarUInt8CasesSupported context)
        NoEffectsSupported directLetAllocationCost sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalScalarUInt8Cases evaluation stateRelated
    frameAligned budget integerImplementation naturalImplementation
    scalarImplementation parameterCount

/--
The same whole-export theorem closes arbitrary nesting of admitted singleton
object-constructor dispatch around the current direct/resident family.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        (SingleObjectConstructorCaseSupported context)
        NoEffectsSupported directLetAllocationCost sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalSingleObjectConstructorCases evaluation
    stateRelated frameAligned budget integerImplementation
    naturalImplementation scalarImplementation parameterCount

/--
The whole-export theorem also admits arbitrary nesting of two-constructor
object chains with a default around the current direct/resident family.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        (TwoObjectConstructorDefaultCasesSupported context)
        NoEffectsSupported directLetAllocationCost sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) :=
  spec.correctBudgetedPureExternalTwoObjectConstructorDefaultCases evaluation
    stateRelated frameAligned budget integerImplementation
    naturalImplementation scalarImplementation parameterCount

/--
The recursive direct-`let` API is likewise certificate-free: its only
recursive premise is correctness of the compiler-selected continuation.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {value : Nat}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .lit (.nat value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .tobject))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    {heap : MemoryState}
    {word : Word32}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (allocated :
      allocateNatural initial.host.runtime.heap value = .ok (heap, word))
    (localSetReady :
      ∀ {resultIndex},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated)
    (continued :
      ∀ {targetRest resultIndex updated nextWitness},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated →
          witness.Extends nextWitness →
          ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
              (literal sourceRuntime (.nat value)).1 →
          PhysicalValueRel nextWitness .tobject
              (.i32 (UInt32.ofNat word.value))
              (literal sourceRuntime (.nat value)).2 →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env (literal sourceRuntime (.nat value)).1
            (bind sourceEnv decl.fvarId
              (literal sourceRuntime (.nat value)).2)
            continuation targetRest (replaceHeap initial heap) updated
            nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q :=
  spec.codeWP_naturalLiteralLet valueEq valueKind localCompiled stateRelated
    allocated localSetReady continued

/--
The UTF-8 String instance keeps the recursive certificate-free boundary,
derives concrete allocation from one source-path budget, and gives the exact
residual budget to the compiler-selected continuation.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {value : String}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .lit (.str value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .object)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    {remainingBytes : Nat}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (allocationFits :
      align8 (headerBytes + (stringUtf8Bytes value).length) ≤ remainingBytes)
    (localSetReady :
      ∀ {resultIndex} {word : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated)
    (continued :
      ∀ {heap : MemoryState} {word : Word32}
          {targetRest resultIndex updated nextWitness},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated →
          witness.Extends nextWitness →
          ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
              (literal sourceRuntime (.str value)).1 →
          PhysicalValueRel nextWitness .object
              (.i32 (UInt32.ofNat word.value))
              (literal sourceRuntime (.str value)).2 →
          heap.AddressSpaceBudget
              (remainingBytes -
                align8
                  (headerBytes + (stringUtf8Bytes value).length)) →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env (literal sourceRuntime (.str value)).1
            (bind sourceEnv decl.fvarId
              (literal sourceRuntime (.str value)).2)
            continuation targetRest (replaceHeap initial heap) updated
            nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q :=
  spec.codeWP_stringLiteralLet_of_budget valueEq valueKind localCompiled
    stateRelated budget allocationFits localSetReady continued

/--
The first compositional API check. A natural literal and its return require
only static pipeline facts plus concrete allocation/local capacity; no
syntax-directed simulation object is accepted from the caller.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {value : Nat}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context
        (.let decl (.return decl.fvarId)) sourceModule sourceFunction target
        hosts exportName)
    (valueEq : decl.value = .lit (.nat value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .tobject))
    {sourceExternals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {heap : MemoryState}
    {word : Word32}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (allocated :
      allocateNatural initial.host.runtime.heap value = .ok (heap, word))
    (localSetReady :
      ∀ {resultIndex},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            (spec.targetFunction.toLocals parameters.reverse).set? resultIndex
                (.i32 (UInt32.ofNat word.value)) =
              some updated) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.let decl (.return decl.fvarId)))
        (ReturnedObservation
          (literal sourceRuntime (.nat value)).1
          (literal sourceRuntime (.nat value)).2) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost
          (literal sourceRuntime (.nat value)).1
          (literal sourceRuntime (.nat value)).2 .tobject callerTail) :=
  spec.correctNaturalLiteralReturn valueEq valueKind localCompiled stateRelated
    parameterCount allocated localSetReady

/--
The finite UTF-8 String export theorem likewise accepts no caller-supplied
translation simulation or concrete-allocation success witness. The only heap
resource premise is explicit wasm32 address-space headroom.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {value : String}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context
        (.let decl (.return decl.fvarId)) sourceModule sourceFunction target
        hosts exportName)
    (valueEq : decl.value = .lit (.str value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .object)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object))
    {sourceExternals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (allocationCapacity :
      initial.host.runtime.heap.AllocationCapacity
        (align8 (headerBytes + (stringUtf8Bytes value).length)))
    (localSetReady :
      ∀ {resultIndex} {word : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            (spec.targetFunction.toLocals parameters.reverse).set? resultIndex
                (.i32 (UInt32.ofNat word.value)) =
              some updated) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.let decl (.return decl.fvarId)))
        (ReturnedObservation
          (literal sourceRuntime (.str value)).1
          (literal sourceRuntime (.str value)).2) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost
          (literal sourceRuntime (.str value)).1
          (literal sourceRuntime (.str value)).2 .object callerTail) :=
  spec.correctStringLiteralReturn valueEq valueKind localCompiled stateRelated
    parameterCount allocationCapacity localSetReady

/--
Object projection is compositional without a target-code certificate.  Static
slots and calls are derived; the caller exposes only the semantic read,
selected-field ABI-kind agreement, local capacity, and the continuation IH.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {index : Nat}
    {objectId : FVarId}
    {objectKind resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .oproj index objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (objectRefines : objectKind.refines .tobject = true)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {sourceObject value : Value}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getObjectField sourceRuntime sourceObject index = .ok value)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (fieldKindAligned :
      ∀ {objectWord : Word32} {info : LCNF.CtorInfo}
          {fieldKinds : Array AbiKind},
        ValueRel witness .tobject (.word32 objectWord) sourceObject →
          witness.descriptors.lookup? objectWord =
              some (.constructor info fieldKinds) →
            fieldKinds[index]? = some resultKind)
    (localSetReady :
      ∀ {resultIndex : Nat} {resultWord : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex
                (.i32 (UInt32.ofNat resultWord.value)) =
              some updated)
    (continued :
      ∀ {targetRest : Wasm.Program} {resultIndex : Nat}
          {resultWord : Word32} {updated : Wasm.Locals},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex
                (.i32 (UInt32.ofNat resultWord.value)) =
              some updated →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env sourceRuntime (bind sourceEnv decl.fvarId value)
            continuation targetRest (clearFailure initial) updated witness
            tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q :=
  spec.codeWP_objectProjectionLet valueEq valueKind objectCompiled
    objectRefines localCompiled sourceLookup projected stateRelated
    fieldKindAligned localSetReady continued

/-- `USize` projection has the same certificate-free recursive boundary. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {index : Nat}
    {objectId : FVarId}
    {objectKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .uproj index objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok .usize)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (objectRefines : objectKind.refines .tobject = true)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .usize))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {sourceObject : Value}
    {value : UInt64}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getUSizeSlot sourceRuntime sourceObject index = .ok (.usize value))
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (localSetReady :
      ∀ {resultIndex : Nat},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i64 value) = some updated)
    (continued :
      ∀ {targetRest : Wasm.Program} {resultIndex : Nat}
          {updated : Wasm.Locals},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex (.i64 value) = some updated →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env sourceRuntime
            (bind sourceEnv decl.fvarId (.usize value)) continuation targetRest
            (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q :=
  spec.codeWP_usizeProjectionLet valueEq valueKind objectCompiled
    objectRefines localCompiled sourceLookup projected stateRelated
    localSetReady continued

/--
Packed integer projection exposes only its operation-specific concrete read
refinement; all compiler, adapter, resolver, and local-layout evidence is
derived.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {width offset : Nat}
    {objectId : FVarId}
    {objectKind resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .sproj width offset objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (objectRefines : objectKind.refines .tobject = true)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {sourceObject sourceValue : Value}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getScalarField sourceRuntime sourceObject width offset =
        .ok sourceValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (concreteStep :
      ∀ {objectWord : Word32},
        ValueRel witness .tobject (.word32 objectWord) sourceObject →
          ∃ physical,
            scalarProjStep width offset resultKind initial
                [.i32 (UInt32.ofNat objectWord.value)] =
              .Return [physical] (clearFailure initial) ∧
            PhysicalValueRel witness resultKind physical sourceValue)
    (localSetReady :
      ∀ {resultIndex : Nat} {physical : Wasm.Value},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated, locals.set? resultIndex physical = some updated)
    (continued :
      ∀ {targetRest : Wasm.Program} {resultIndex : Nat}
          {physical : Wasm.Value} {updated : Wasm.Locals},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex physical = some updated →
          PhysicalValueRel witness resultKind physical sourceValue →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env sourceRuntime (bind sourceEnv decl.fvarId sourceValue)
            continuation targetRest (clearFailure initial) updated witness
            tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q :=
  spec.codeWP_scalarProjectionLet valueEq valueKind objectCompiled
    objectRefines localCompiled sourceLookup projected stateRelated concreteStep
    localSetReady continued

/--
Mixed local/erased nonempty constructor allocation exposes the recursive
certificate-free API. Static code, physical operands, field decoding, and the
concrete allocation/refinement step are derived internally. The caller
supplies explicit ABI/layout/resource conditions and the continuation
induction hypothesis.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (argumentCode, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (operationWellFormed :
      (RuntimeOp.allocCtor info fieldKinds resultKind).abiWellFormed = true)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {semanticArgs : Array Value}
    {sourceValue : Value}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (capacity :
      initial.host.runtime.heap.AllocationCapacity
        (ConstructorLayout.ofInfo info).allocationBytes)
    (localSetReady :
      ∀ {resultIndex : Nat} {word : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated)
    (continued :
      ∀ {targetRest : Wasm.Program} {resultIndex : Nat}
          {nextStore : Wasm.Store Host} {word : Word32}
          {nextWitness : RefinementWitness} {updated : Wasm.Locals},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
            some updated →
          witness.Extends nextWitness →
          ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime →
          nextStore.host.failure? = none →
          PhysicalValueRel nextWitness resultKind
              (.i32 (UInt32.ofNat word.value)) sourceValue →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env nextRuntime (bind sourceEnv decl.fvarId sourceValue)
            continuation targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q :=
  spec.codeWP_constructorNonemptyLet_of_capacity valueEq fits valueKind
    argumentsCompiled localCompiled operationWellFormed nonempty
    objectFieldsFit usizeFieldsFit scalarBytesFit evaluated semanticStep
    stateRelated capacity localSetReady continued

/--
The finite nonempty-constructor corollary has no caller-supplied concrete
operation step, `ConcreteCodeSimulation`, or translation certificate.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context
        (.let decl (.return decl.fvarId)) sourceModule sourceFunction target
        hosts exportName)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (argumentCode, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (operationWellFormed :
      (RuntimeOp.allocCtor info fieldKinds resultKind).abiWellFormed = true)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {parameters callerTail : List Wasm.Value}
    {semanticArgs : Array Value}
    {sourceValue : Value}
    {initialWitness : RefinementWitness}
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (capacity :
      initial.host.runtime.heap.AllocationCapacity
        (ConstructorLayout.ofInfo info).allocationBytes)
    (localSetReady :
      ∀ {resultIndex : Nat} {word : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            (spec.targetFunction.toLocals parameters.reverse).set? resultIndex
                (.i32 (UInt32.ofNat word.value)) =
              some updated) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.let decl (.return decl.fvarId)))
        (ReturnedObservation nextRuntime sourceValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost nextRuntime sourceValue resultKind callerTail) :=
  spec.correctConstructorNonemptyReturn_of_capacity valueEq fits valueKind
    argumentsCompiled localCompiled operationWellFormed nonempty
    objectFieldsFit usizeFieldsFit scalarBytesFit evaluated semanticStep
    stateRelated parameterCount capacity localSetReady

/--
The cache-hit source premise itself determines the unchanged runtime and
semantic global lookup. Callers do not supply a separate cache-presence fact.
-/
example
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {fvarId : FVarId}
    {type : Expr}
    {declaration : Name}
    {target : LCNF.Decl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (targetEq : context.program.findDecl? declaration = some target)
    (paramsEq : target.params.isEmpty = true)
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv {
          fvarId
          binderName := fvarId.name
          type
          value := .fap declaration #[] }
        continuation nextRuntime sourceValue) :
    nextRuntime = sourceRuntime ∧
      findGlobal? sourceRuntime.globals declaration = some sourceValue :=
  FirTalos.Concrete.SourceLazyLetResult.hit_cacheFacts targetEq paramsEq
    sourceStep

/--
The structured cache-miss source premise determines both initial absence and
the exact semantic publication. The callee runtime is existential because an
internal declaration may execute an arbitrary finite body before publishing.
-/
example
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {declaration : Name}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (valueEq : decl.value = .fap declaration #[])
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue) :
    ∃ callRuntime : RuntimeState,
      findGlobal? sourceRuntime.globals declaration = none ∧
        nextRuntime =
          callRuntime.setGlobal declaration sourceValue :=
  FirTalos.Concrete.SourceLazyLetResult.miss_cacheFacts_of_valueEq valueEq
    sourceStep

/--
The exact hereditary callee result identifies the miss's pre-publication
runtime. Static declaration lookup/body facts replace the former
caller-supplied runtime equation and permit unrelated nested-cache evolution.
-/
example
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {declaration : Name}
    {target : LCNF.Decl .impure}
    {calleeCode continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (valueEq : decl.value = .fap declaration #[])
    (declarationFound :
      context.program.findDecl? declaration = some target)
    (targetParams : target.params = #[])
    (targetBody : target.value = .code calleeCode)
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (calleeResult :
      SourceCodeResult context sourceExternals sourceRuntime [] calleeCode
        resultRuntime sourceValue) :
    findGlobal? sourceRuntime.globals declaration = none ∧
      nextRuntime =
        resultRuntime.setGlobal declaration sourceValue :=
  FirTalos.Concrete.SourceLazyLetResult.miss_cacheFacts_of_callee valueEq
    declarationFound targetParams targetBody sourceStep calleeResult

/--
The production supported-lowering/adaptation pipeline determines the
generated cache-name table and symbolic validation facts. The integration
validator owes one uniform soundness theorem; callers retain only the exact
result-kind condition isolated by the confirmed compiler bug.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    {target : FirTalos.AdaptedModule}
    (localKinds : Fir.Wasm.LocalKinds)
    (joins : Fir.Wasm.JoinPoints)
    (validatorSound : LazyCacheValidatorSound)
    (lowered : Fir.Wasm.lowerSupported program = .ok source)
    (adapted : FirTalos.adapt source = .ok target)
    (resultKinds :
      LazyCacheResultKindsAligned {
        program
        localKinds
        joins
        cachedDeclarations :=
          Fir.Wasm.cachedDeclarationNames program } source) :
    LazyCacheGeneratedEnvironment {
      program
      localKinds
      joins
      cachedDeclarations :=
        Fir.Wasm.cachedDeclarationNames program } source :=
  LazyCacheGeneratedEnvironment.ofCanonicalSupportedPipeline localKinds joins
    validatorSound lowered adapted resultKinds

/--
One generated environment replaces independent per-call initializer and
signature premises. The selected index is still the compiler's executable
`findIdx?` result.
-/
example
    {context : Fir.Wasm.Context}
    {source : Fir.Wasm.Module}
    (generated : LazyCacheGeneratedEnvironment context source)
    {type : Expr}
    {declaration : Name}
    {target : LCNF.Decl .impure}
    {kind : AbiKind}
    {index : Nat}
    (kindEq : Fir.Wasm.checkedAbiKind type = .ok kind)
    (targetEq : context.program.findDecl? declaration = some target)
    (paramsEq : target.params.isEmpty = true)
    (cacheEq :
      context.cachedDeclarations.findIdx? (· == declaration) = some index) :
    source.initializers[index]? = some declaration ∧
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind :=
  generated.select kindEq targetEq paramsEq cacheEq

/--
Reachability disjointness is one sufficient implementation of the minimal
facts-aware cache-publication boundary. The compiler theorem itself consumes
the transport, so an alias-invalidating fact analysis may discharge the same
boundary without proving a stronger all-location persistence property.
-/
example
    {facts : ReuseCapacityFacts}
    {resultId : FVarId}
    {runtime : RuntimeState}
    {sourceEnv : Env}
    {result : Value}
    (declaration : Name)
    (disjoint :
      ReuseTokenPublicationDisjoint facts runtime sourceEnv result) :
    ReuseTokenOrdinaryBindTransport facts resultId runtime
      (runtime.setGlobal declaration result) sourceEnv result :=
  ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint declaration disjoint

/--
The complete production direct family is available over the canonical
whole-cache frame with transports accumulated from a fixed declaration
entry. Direct readers, allocations, boxing, literals, constructors, and reuse
therefore compose inside hereditary cached bodies without a caller-supplied
target execution.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    (externals : ExternalImpl)
    {labels : List FVarId}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels target.wasmModule hosts.env
      (ReuseBudgetedDirectSupported context) directLetAllocationCost
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness) :=
  spec.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
    externals

/--
The production pure-external family is directly available over the canonical
whole-cache frame with transports accumulated from a fixed declaration
entry. This is the exact structural premise used by hereditary body proofs;
the caller supplies no target execution.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    (externals : ExternalImpl)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityExternalLetRuntimeRefinesWithCost context sourceModule
      sourceFunction [] target.wasmModule hosts.env externals
      (PureExternalSupported context externals)
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness) :=
  spec.reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
    externals

/--
The complete production no-result effect family is available over the same
entry-relative whole-cache frame. Ownership operations and every admitted
constructor mutation preserve cache globals and extend all hereditary entry
transports without a caller-supplied target execution.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    (externals : ExternalImpl)
    {labels : List FVarId}
    {facts : ReuseCapacityFacts}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (OwnershipTagAndAllFieldMutationEffectSupported context)
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts) :=
  spec.effectRuntimeRefines_reuseOwnershipTagAndAllFieldMutation_pureExternal_entryRelativeCache
    externals

/--
Recursive declarations may have different local layouts while still belonging
to one generated module. The public coherence boundary transports exact source
execution through their shared program without equating `localKinds` or
`joins`.
-/
example
    {callerContext calleeContext : Fir.Wasm.Context}
    (contexts :
      DeclarationContextsCoherent callerContext calleeContext)
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {sourceValue : Value}
    (result :
      SourceCodeResult calleeContext sourceExternals sourceRuntime sourceEnv
        sourceCode resultRuntime sourceValue) :
    SourceCodeResult callerContext sourceExternals sourceRuntime sourceEnv
      sourceCode resultRuntime sourceValue :=
  contexts.sourceCodeResult result

/--
The production declaration selector is driven by `lowerSupported` and
`adapt`, not by caller-supplied symbolic/target rows. The canonical binding row
constructed by `lowerDecl` supplies local-layout alignment internally; the
result carries the exact callee context and pointwise adapted function row.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {caller : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {resultKind : AbiKind}
    (callerProgram : caller.program = program)
    (callerCaches :
      caller.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target)
    (declarationFound :
      program.findDecl? declarationName = some declaration)
    (bodyEq : declaration.value = .code sourceCode)
    (resultClassified :
      Fir.Wasm.abiKind? declaration.type = .ok (some resultKind)) :
    ∃ calleeContext sourceFunction,
      DeclarationContextsCoherent caller calleeContext ∧
        Nonempty (ConcreteGeneratedDeclaration calleeContext sourceCode
          sourceModule sourceFunction target) :=
  ConcreteGeneratedDeclaration.exists_ofSupportedPipeline
    callerProgram callerCaches lowered adapted
    declarationFound bodyEq resultClassified

/--
The same two production equations assemble every internal value-returning
declaration into one module-wide family. Recursive callers may have different
local layouts; they supply only the shared program and cache-name equations.
Each selected row also retains the exact production parameter layout needed
to relate semantic arguments to the callee's initial Wasm locals.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target) :
    ConcreteGeneratedDeclarationFamily program sourceModule target :=
  ConcreteGeneratedDeclarationFamily.ofSupportedPipeline namesUnique lowered
    adapted

/--
An already exposed canonical `lowerDecl` row is selected verbatim by the
production pipeline. This is the static identity needed to apply a nested
hereditary induction hypothesis without transporting it to an arbitrary
callee context.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {caller : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    {resultKind : AbiKind}
    (callerProgram : caller.program = program)
    (callerCaches :
      caller.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target)
    (declarationFound :
      program.findDecl? declarationName = some declaration)
    (row :
      LoweredInternalDeclaration caller.program caller.cachedDeclarations
        declaration sourceCode sourceFunction)
    (resultClassified :
      Fir.Wasm.abiKind? declaration.type = .ok (some resultKind)) :
    Nonempty (ConcreteGeneratedInternalDeclaration program declaration
      row.context sourceCode sourceModule sourceFunction target) :=
  ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipelineAtLowered
    callerProgram callerCaches namesUnique lowered adapted declarationFound
      row resultClassified

/--
A cache-aware direct-declaration implementation supplies the interprocedural
call premise over the same fixed-entry cache frame. Its recursive callee
returns the evolved cache table; no unchanged-global adapter is involved.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {CallSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    (implementation :
      DirectDeclarationCallImplementationWithCache context sourceModule
        sourceFunction labels module hostEnv sourceExternals CallSupported)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityCallLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels module hostEnv sourceExternals CallSupported
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals)
        entryRuntime entryStore entryWitness) :=
  implementation.runtimeRefinesEntryRelative

/--
Production named-call selection constructs the cache-aware implementation from
source-only call sites and one module-wide hereditary declaration theorem.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedExport program context callerCode sourceModule
        callerFunction targetModule hosts exportName)
    (declarations :
      DirectInternalCallDeclarationInduction context sourceModule targetModule
        hosts sourceExternals) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      callerFunction labels targetModule.wasmModule hosts.env sourceExternals
      (DirectInternalCallSupported context) :=
  DirectDeclarationCallImplementationWithCache.ofInternalCompiler spec
    declarations

/--
The preferred production named-call boundary consumes correctness of nested
finite source derivations. The compiler reconstructs the exact callee row,
numeric call index, entry frame, and caller-facing result refinement; neither
an index equation nor a target execution is a call-site premise.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState →
          Value → Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    (spec :
      ConcreteSupportedExport program context callerCode sourceModule
        callerFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (declarations :
      DirectHereditaryGeneratedDeclarationInduction program sourceModule target
        hosts sourceExternals DirectSupported ExternalSupported LazySupported
        CaseSupported EffectSupported) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      callerFunction labels target.wasmModule hosts.env sourceExternals
      (ReuseCapacityDirectHereditaryCallSupported sourceExternals
        DirectSupported ExternalSupported LazySupported CaseSupported
        EffectSupported directLetAllocationCost context) :=
  DirectDeclarationCallImplementationWithCache.ofHereditaryInternalCompiler
    spec.contextProgram contextCaches spec.programNamesUnique spec.lowered
      spec.adapted spec.localsAligned declarations

/-- The generated declaration induction is itself derived from the finite
source evaluation and uniform production operation laws. Recursive clients do
not supply a target execution or a module-wide correctness certificate. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState →
          Value → Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target)
    (operationLaws :
      DirectHereditaryGeneratedOperationLaws program sourceModule target hosts
        sourceExternals DirectSupported ExternalSupported LazySupported
        CaseSupported EffectSupported) :
    DirectHereditaryGeneratedDeclarationInduction program sourceModule target
      hosts sourceExternals DirectSupported ExternalSupported LazySupported
      CaseSupported EffectSupported :=
  DirectHereditaryGeneratedDeclarationInduction.ofOperationLaws namesUnique
    lowered adapted operationLaws

/-- The first production recursive fragment constructs its complete generated
declaration induction from the root pipeline and individual operation
theorems. No operation bundle or callee correctness premise remains. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (sourceExternals : ExternalImpl) :
    DirectHereditaryGeneratedDeclarationInduction program sourceModule target
      hosts sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun _ => NoReuseCapacityExternalsSupported)
      (fun _ => NoReuseCapacityLazySupported)
      (fun _ => DefaultOnlyCaseSupported)
      (fun _ => NoEffectsSupported) :=
  spec.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_noCalls
    sourceExternals

/-- Consequently the root named-call law is also production-derived: callers
supply the canonical compiler context fact, not target behavior for callees. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (sourceExternals : ExternalImpl) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      sourceFunction labels target.wasmModule hosts.env sourceExternals
      (ReuseCapacityDirectHereditaryCallSupported sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun _ => NoReuseCapacityExternalsSupported)
        (fun _ => NoReuseCapacityLazySupported)
        (fun _ => DefaultOnlyCaseSupported)
        (fun _ => NoEffectsSupported)
        directLetAllocationCost context) :=
  spec.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_noCalls
    contextCaches sourceExternals

/--
The saturated closure path derives the adapted dispatch from the exact
compiler candidate enumeration returned by its module-wide selection
induction, then exposes the same cache-aware implementation boundary.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedExport program context callerCode sourceModule
        callerFunction targetModule hosts exportName)
    (selection :
      SaturatedClosureDispatchSelectionInduction context sourceModule
        callerFunction labels targetModule hosts sourceExternals) :
    SaturatedClosureCallImplementationWithCache context sourceModule
      callerFunction labels targetModule.wasmModule hosts.env hosts.spec
      sourceExternals (SaturatedClosureCallSupported context) :=
  SaturatedClosureCallImplementationWithCache.ofInternalCompiler spec
    selection

/--
The preferred saturated-dispatch constructor needs only implementations for
compiler candidates carrying the resolved source identity. Static enumeration,
concrete address recovery, and first-match selection are internal theorems.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedExport program context callerCode sourceModule
        callerFunction targetModule hosts exportName)
    (induction :
      SaturatedClosureCandidateResolutionInduction context sourceModule
        callerFunction labels targetModule hosts sourceExternals) :
    SaturatedClosureCallImplementationWithCache context sourceModule
      callerFunction labels targetModule.wasmModule hosts.env hosts.spec
      sourceExternals (SaturatedClosureCallSupported context) :=
  SaturatedClosureCallImplementationWithCache.ofInternalCompilerResolved spec
    induction

/--
The saturated closure address is recovered canonically from source resolution,
local-layout alignment, and the ordinary concrete state relation. Executable
candidate construction therefore starts only after the mapped address is
known.
-/
example
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureIndex : Nat}
    {closureKind : AbiKind}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (site : SaturatedClosureCallSite context decl sourceEnv)
    (resolution :
      SaturatedClosureCallResolution context sourceRuntime site)
    (closureFound :
      findFVar? (functionBindings sourceFunction) site.closureId =
        some closureIndex)
    (closureKindAt :
      (functionBindings sourceFunction)[closureIndex]?.map Prod.snd =
        some closureKind) :
    ∃ address : Word32,
      locals.get closureIndex =
          some (.i32 (UInt32.ofNat address.value)) ∧
        witness.locations.lookup? resolution.location = some address :=
  invariant.resolveClosureAddress site resolution closureFound closureKindAt

/--
The constructive saturated-dispatch boundary resolves the concrete closure
address and exact matcher result from the ordinary state relation plus both
immutable closure-table equations. No physical address or matcher execution
is supplied independently.
-/
example
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureId : FVarId}
    {closureIndex : Nat}
    {closureKind : AbiKind}
    {location : Location}
    {cell : HeapCell}
    {function expectedFunction : Name}
    {arity expectedArity expectedFixed : Nat}
    {captures : Array Value}
    (related :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        witness)
    (dispatchEq :
      witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (sourceLookup :
      lookup sourceEnv closureId = some (.object (.heap location)))
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex)
    (closureKindAt :
      (functionBindings sourceFunction)[closureIndex]?.map Prod.snd =
        some closureKind)
    (cellFound : findCell? sourceRuntime.heap location = some cell)
    (cellLive : cell.live = true)
    (cellObjectEq : cell.object = .closure function arity captures) :
    ∃ address : Word32,
      locals.get closureIndex =
          some (.i32 (UInt32.ofNat address.value)) ∧
        (∀ results next,
          closureMatchesStep expectedFunction expectedArity expectedFixed initial
              [.i32 (UInt32.ofNat address.value)] = .Return results next →
            results = [
              .i32 (if function == expectedFunction && arity == expectedArity &&
                captures.size == expectedFixed then 1 else 0)]) ∧
        closureData sourceRuntime (.object (.heap location)) =
          .ok (function, arity, captures) :=
  related.resolveClosureMatcher dispatchEq descriptorsEq sourceLookup
    closureFound closureKindAt cellFound cellLive cellObjectEq

/--
The canonical cache-aware frame now supplies both closure-table equations;
cached declaration bodies do not restate them at each saturated call site.
-/
example
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureId : FVarId}
    {closureIndex : Nat}
    {closureKind : AbiKind}
    {location : Location}
    {cell : HeapCell}
    {function expectedFunction : Name}
    {arity expectedArity expectedFixed : Nat}
    {captures : Array Value}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (sourceLookup :
      lookup sourceEnv closureId = some (.object (.heap location)))
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex)
    (closureKindAt :
      (functionBindings sourceFunction)[closureIndex]?.map Prod.snd =
        some closureKind)
    (cellFound : findCell? sourceRuntime.heap location = some cell)
    (cellLive : cell.live = true)
    (cellObjectEq : cell.object = .closure function arity captures) :
    ∃ address : Word32,
      locals.get closureIndex =
          some (.i32 (UInt32.ofNat address.value)) ∧
        (∀ results next,
          closureMatchesStep expectedFunction expectedArity expectedFixed initial
              [.i32 (UInt32.ofNat address.value)] = .Return results next →
            results = [
              .i32 (if function == expectedFunction && arity == expectedArity &&
                captures.size == expectedFixed then 1 else 0)]) ∧
        closureData sourceRuntime (.object (.heap location)) =
          .ok (function, arity, captures) :=
  invariant.resolveClosureMatcher sourceLookup closureFound closureKindAt
    cellFound cellLive cellObjectEq

/--
The same canonical frame derives the first executable matcher from semantic
candidate coverage, without accepting matcher bits or table agreement as
separate call-site premises.
-/
example
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureId : FVarId}
    {closureIndex : Nat}
    {address : Word32}
    {location : Location}
    {cell : HeapCell}
    {function : Name}
    {arity : Nat}
    {captures : Array Value}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (candidates : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (mapped : witness.locations.lookup? location = some address)
    (cellFound : findCell? sourceRuntime.heap location = some cell)
    (cellLive : cell.live = true)
    (cellObjectEq : cell.object = .closure function arity captures)
    (containsMatch :
      ∃ candidate ∈ candidates,
        (function == candidate.function && arity == candidate.arity &&
          captures.size == candidate.fixed) = true) :
    ∃ before selected suffix,
      candidates = before ++ selected :: suffix ∧
        (∀ candidate, candidate ∈ before →
          candidate.matched = (0 : UInt32)) ∧
          (selected.matched != 0) = true :=
  invariant.closureCandidates_exists_first_match candidates mapped cellFound
    cellLive cellObjectEq containsMatch

/--
First-match selection is a theorem over the executable matcher bits, not an
extra candidate-order certificate.
-/
example
    {α : Type} (matched : α → UInt32) (values : List α)
    (existsMatch :
      ∃ candidate ∈ values, (matched candidate != 0) = true) :
    ∃ before selected suffix,
      values = before ++ selected :: suffix ∧
        (∀ candidate, candidate ∈ before → matched candidate = 0) ∧
          (matched selected != 0) = true :=
  exists_first_nonzero matched values existsMatch

/--
The production compiler-generated non-heap lazy family is available over the
fixed-entry cache frame. Misses thread the recursively evolved table and use
heap-neutral publication to preserve the hereditary ordinaryness transport.
-/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedExport program context callerCode sourceModule
        sourceFunction targetModule hosts exportName)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (resultKinds : LazyCacheInternalResultKindsNonHeap context)
    (declarations :
      LazyCacheInternalHereditaryDeclarationInduction context sourceModule
        targetModule hosts sourceExternals)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels targetModule.wasmModule hosts.env sourceExternals
      (LazyCacheInternalSupported context)
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals)
        entryRuntime entryStore entryWitness) :=
  spec.internalNonHeapLazyRuntimeRefines_entryRelativeCache generated
    resultKinds declarations

/--
The hereditary theorem for a lazy initializer returns ordinary declaration
correctness and the exact evolved cache table together. This is the recursive
induction result consumed by nested miss publication, not a target execution
certificate supplied by the caller.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    {stepCost : Nat}
    (callee :
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction module hostEnv sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode targetFunction
        functionIndex initial afterCall initialWitness resultWitness parameters
        resultKind resultValue physical stepCost) :
    BudgetedCapacityPreservingSuccessfulDeclaration context sourceModule
          sourceFunction module hostEnv sourceExternals sourceRuntime
          resultRuntime sourceEnv sourceCode targetFunction functionIndex
          initial afterCall initialWitness resultWitness parameters resultKind
          resultValue physical stepCost ∧
      LazyCacheGlobalsRel resultWitness sourceModule resultRuntime afterCall :=
  ⟨callee.declaration, callee.cacheTable⟩

/--
The hereditary cache package can expose a caller-facing ABI superkind without
changing its execution, resource, or whole-cache postconditions.
-/
example
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {actualKind expectedKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    {stepCost : Nat}
    (callee :
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction module hostEnv sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode targetFunction
        functionIndex initial afterCall initialWitness resultWitness parameters
        actualKind resultValue physical stepCost)
    (refines : actualKind.refines expectedKind = true) :
    BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
      sourceModule sourceFunction module hostEnv sourceExternals sourceRuntime
      resultRuntime sourceEnv sourceCode targetFunction functionIndex initial
      afterCall initialWitness resultWitness parameters expectedKind resultValue
      physical stepCost :=
  callee.ofRefines refines

/--
Executable witness for
`FIR-BUG-wasm-none-lazy-cache-result-refinement`.

Source admission permits the precise `.object` target result at a `.tobject`
call site. Lowering then emits a `.tobject` cache operation for an `.object`
value global, and production adaptation rejects that generated module.
-/
private def lazyCacheRefinementResult : FVarId :=
  FVarId.mk `FirTalos.Concrete.CompilerCorrectnessContract.lazyCacheResult

private def lazyCacheRefinementTarget : LCNF.Decl .impure :=
  { name := `FirTalos.Concrete.CompilerCorrectnessContract.lazyCacheTarget
    levelParams := []
    type := LCNF.ImpureType.object
    params := #[]
    value := .code (.unreach LCNF.ImpureType.object)
    safe := true
    recursive := false
    inlineAttr? := none }

private def lazyCacheRefinementCaller : LCNF.Decl .impure :=
  { name := `FirTalos.Concrete.CompilerCorrectnessContract.lazyCacheCaller
    levelParams := []
    type := LCNF.ImpureType.tobject
    params := #[]
    value := .code <|
      .let
        { fvarId := lazyCacheRefinementResult
          binderName := lazyCacheRefinementResult.name
          type := LCNF.ImpureType.tobject
          value :=
            .fap
              `FirTalos.Concrete.CompilerCorrectnessContract.lazyCacheTarget #[] }
        (.return lazyCacheRefinementResult)
    safe := true
    recursive := false
    inlineAttr? := none }

private def lazyCacheRefinementProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[lazyCacheRefinementTarget, lazyCacheRefinementCaller] }

#guard Fir.Wasm.supportedProgram lazyCacheRefinementProgram

#guard
  match Fir.Wasm.lowerSupported lazyCacheRefinementProgram with
  | .error _ => false
  | .ok source =>
      source.initializers ==
          #[`FirTalos.Concrete.CompilerCorrectnessContract.lazyCacheTarget] &&
        match adapt source with
        | .error (.invalidModule (.invalidGlobalKind function index)) =>
            function ==
                `FirTalos.Concrete.CompilerCorrectnessContract.lazyCacheCaller &&
              index == 1
        | _ => false

/--
Every related generated cache slot retains two physically allocated lanes,
even while an unpublished value lane remains semantically unconstrained.
-/
example
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {runtime : RuntimeState}
    {store : Wasm.Store Host}
    {index : Nat}
    {declaration : Name}
    {kind : AbiKind}
    (related : LazyCacheGlobalsRel witness source runtime store)
    (initializerFound :
      source.initializers[index]? = some declaration)
    (signature :
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind) :
    ∃ oldFlag oldValue,
      store.globals.globals[2 * index]? = some oldFlag ∧
        store.globals.globals[2 * index + 1]? = some oldValue :=
  related.slotLanesPresent initializerFound signature

/--
Whole-table publication overwrites either an empty slot or a slot populated
by nested execution. It therefore needs no pre-publication semantic-absence
premise at the callee's final runtime.
-/
example
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {beforeRuntime nextRuntime : RuntimeState}
    {beforeStore valueStore : Wasm.Store Host}
    {index : Nat}
    {declaration : Name}
    {kind : AbiKind}
    {sourceValue : Value}
    {physical : Wasm.Value}
    (related :
      LazyCacheGlobalsRel witness source beforeRuntime beforeStore)
    (initializerFound :
      source.initializers[index]? = some declaration)
    (signature :
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind)
    (runtimeEq :
      nextRuntime = beforeRuntime.setGlobal declaration sourceValue)
    (valueRelated :
      PhysicalValueRel witness kind physical sourceValue)
    (valueStoreEq :
      valueStore =
        writeWasmGlobal beforeStore (2 * index + 1) physical) :
    LazyCacheGlobalsRel witness source nextRuntime
      (writeWasmGlobal valueStore (2 * index) (.i32 1)) :=
  related.publish initializerFound signature runtimeEq valueRelated
    valueStoreEq

/-!
The erased generic-parameter admission used by compiler-generated `_boxed`
facades is deliberately structural. This executable proof fixture mirrors the
relevant final-LCNF shape without relying on a declaration suffix: a raw
`tobject` parameter is accepted as `.erased` only because its sole use is an
exact forwarding call to a parameter whose final-LCNF type is erased.
-/

private def erasedFacadeAlpha : FVarId :=
  ⟨`FirTalos.Concrete.CompilerCorrectnessContract.erasedFacadeAlpha⟩

private def erasedFacadeCaptured : FVarId :=
  ⟨`FirTalos.Concrete.CompilerCorrectnessContract.erasedFacadeCaptured⟩

private def erasedFacadeValue : FVarId :=
  ⟨`FirTalos.Concrete.CompilerCorrectnessContract.erasedFacadeValue⟩

private def erasedFacadeResult : FVarId :=
  ⟨`FirTalos.Concrete.CompilerCorrectnessContract.erasedFacadeResult⟩

private def erasedFacadeClosure : FVarId :=
  ⟨`FirTalos.Concrete.CompilerCorrectnessContract.erasedFacadeClosure⟩

private def erasedFacadeParam (id : FVarId) (type : Expr) :
    LCNF.Param .impure :=
  { fvarId := id, binderName := id.name, type, borrow := false }

private def erasedFacadeTarget : LCNF.Decl .impure :=
  { name := `FirTalos.Concrete.CompilerCorrectnessContract.erasedFacadeTarget
    levelParams := []
    type := LCNF.ImpureType.tobject
    params := #[
      erasedFacadeParam erasedFacadeAlpha LCNF.ImpureType.erased,
      erasedFacadeParam erasedFacadeCaptured LCNF.ImpureType.tobject,
      erasedFacadeParam erasedFacadeValue LCNF.ImpureType.tobject]
    value := .code (.return erasedFacadeCaptured)
    safe := true
    recursive := false
    inlineAttr? := none }

private def erasedFacade : LCNF.Decl .impure :=
  { name := `FirTalos.Concrete.CompilerCorrectnessContract.erasedFacade
    levelParams := []
    type := LCNF.ImpureType.tobject
    params := #[
      erasedFacadeParam erasedFacadeAlpha LCNF.ImpureType.tobject,
      erasedFacadeParam erasedFacadeCaptured LCNF.ImpureType.tobject,
      erasedFacadeParam erasedFacadeValue LCNF.ImpureType.tobject]
    value := .code <| .let
      { fvarId := erasedFacadeResult
        binderName := erasedFacadeResult.name
        type := LCNF.ImpureType.tobject
        value := .fap erasedFacadeTarget.name #[
          .fvar erasedFacadeAlpha,
          .fvar erasedFacadeCaptured,
          .fvar erasedFacadeValue] }
      (.return erasedFacadeResult)
    safe := true
    recursive := false
    inlineAttr? := none }

private def erasedFacadeCaller : LCNF.Decl .impure :=
  { name := `FirTalos.Concrete.CompilerCorrectnessContract.erasedFacadeCaller
    levelParams := []
    type := LCNF.ImpureType.tobject
    params := #[]
    value := .code <| .let
      { fvarId := erasedFacadeClosure
        binderName := erasedFacadeClosure.name
        type := LCNF.ImpureType.tobject
        value := .pap erasedFacade.name #[.erased] }
      (.return erasedFacadeClosure)
    safe := true
    recursive := false
    inlineAttr? := none }

private def erasedFacadeProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[erasedFacadeTarget, erasedFacade, erasedFacadeCaller] }

#guard Fir.Wasm.erasedOnlyParameter erasedFacadeProgram erasedFacade
  erasedFacade.params[0]!

#guard Fir.Wasm.declarationParameterKinds? erasedFacadeProgram erasedFacade ==
  some #[.erased, .tobject, .tobject]

#guard
  match Fir.Wasm.lowerSupported erasedFacadeProgram with
  | .error _ => false
  | .ok module =>
      module.runtimeOperations.contains <|
        .partialApply erasedFacade.name 3 1 #[.erased] .tobject

/-- An exact generated internal row inherits the reusable static pipeline
contract without claiming that the recursive callee is itself exported. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext context : Fir.Wasm.Context}
    {rootCode sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {declaration : LCNF.Decl .impure}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target) :
    ConcreteSupportedFunction program context sourceCode sourceModule
      sourceFunction target hosts :=
  row.toSupportedFunction spec

end FirTalos.Concrete.CompilerCorrectnessContract
