import FirTalos.ConcreteCompilerCorrectness

namespace FirTalos.Concrete.CompilerCorrectnessContract

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

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
and successful object/`USize`/packed-scalar projections with allocating
Strings and nonempty constructors under one source path cost.
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
        DefaultOnlyCaseSupported directLetAllocationCost sourceRuntime
        sourceEnv sourceCode resultRuntime resultValue requiredBytes)
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

end FirTalos.Concrete.CompilerCorrectnessContract
