import FirTalos.ConcreteProgramCorrectness
import FirTalos.ConcreteResolver
import Fir.Wasm.WellFormed

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- Fuel-free concrete target correctness for a function selected by exported
name rather than by a separately supplied function index. -/
def ConcreteExportTerminatesWith
    (hostEnv : Wasm.HostEnv Host)
    (module : Wasm.Module)
    (exportName : String)
    (initial : Wasm.Store Host)
    (args : List Wasm.Value)
    (Post : Wasm.Store Host → List Wasm.Value → Prop) : Prop :=
  ∃ functionIndex,
    module.findExport exportName = some functionIndex ∧
      Wasm.TerminatesWith hostEnv module functionIndex initial args Post

/-- The lowering context and the selected symbolic function assign the same
ABI kind and numeric slot to every successfully compiled local read. This is
a static invariant of `lowerDecl`; keeping it explicit here prevents dynamic
simulation evidence from standing in for compiler layout correctness. -/
def LocalLayoutAligned
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) : Prop :=
  ∀ {fvarId : FVarId} {kind : AbiKind},
    Fir.Wasm.getLocal context fvarId = .ok (.localGet fvarId, kind) →
      ∃ index,
        findFVar? (functionBindings sourceFunction) fvarId = some index ∧
          (functionBindings sourceFunction)[index]?.map Prod.snd = some kind

/-- The concrete contract selected by the executable host resolver, when that
resolver supports the runtime operation. -/
def resolvedContract? (operation : RuntimeOp) :
    Option (Wasm.HostContract Host) :=
  (hostFn? operation).map fun function =>
    fun initial args result => result = function.invoke initial args

/--
Every symbolic runtime call used by the adapter occupies the same numeric
slot in the target import table and concrete host specification.

This is static resolver/adaptor alignment. It exposes no source behavior and
is intended to be discharged once from `adapt` and `resolveHosts`, not supplied
as a per-execution simulation certificate.
-/
def ConcreteRuntimeCallsAligned
    (sourceModule : Fir.Wasm.Module)
    (target : AdaptedModule)
    (hosts : ResolvedHosts) : Prop :=
  ∀ {operation : RuntimeOp} {id : Nat},
    callIndex? sourceModule (.runtime operation) = some id →
      ∃ imp,
        target.wasmModule.imports[id]? = some imp ∧
          id < target.wasmModule.imports.length ∧
          hosts.spec.contracts[id]? = resolvedContract? operation ∧
          imp.params.length = operation.signature.params.size ∧
          imp.results.length = operation.signature.results.size

/--
One executable external operation retains exactly the declaration metadata
used by the source interpreter and the ABI signature computed by lowering.
-/
structure ExternalOperationMatchesDeclaration
    (operation : ExternalOperation) (declaration : LCNF.Decl .impure) : Prop where
  name : operation.name = declaration.name
  paramTypes : operation.paramTypes = declaration.params.map (·.type)
  resultType : operation.resultType = declaration.type
  paramTypesSize :
    operation.paramTypes.size = operation.signature.params.size
  signature :
    ExternalTypes.signature {
      params := declaration.params.map (·.type)
      result := declaration.type } = .ok operation.signature

/--
Every named call to a source external declaration occupies the matching
adapted import slot and selects the concrete external host contract built from
that declaration's exact metadata and ABI signature.

This is static lowering/adapter/resolver alignment, analogous to
`ConcreteRuntimeCallsAligned`. It is discharged once for a generated module;
it contains no source execution, concrete response, allocation result, or
per-program target simulation.
-/
def ConcreteExternalCallsAligned
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (target : AdaptedModule)
    (hosts : ResolvedHosts) : Prop :=
  ∀ {name : Lean.Name} {declaration : LCNF.Decl .impure} {id : Nat},
    program.findDecl? name = some declaration →
      (∃ metadata, declaration.value = .extern metadata) →
      callIndex? sourceModule (.declaration name) = some id →
      ∃ operation resultKind imp,
        operation.name = name ∧
          ExternalOperationMatchesDeclaration operation declaration ∧
          operation.signature.results = #[resultKind] ∧
          target.wasmModule.imports[id]? = some imp ∧
          id < target.wasmModule.imports.length ∧
          hosts.spec.contracts[id]? =
            some (externalContract operation resultKind) ∧
          imp.params.length = operation.signature.params.size ∧
          imp.results.length = 1

/-- Static whole-pipeline evidence for one concrete generated function.

`bodyAdapted` is the crucial compiler-facing equation: it ties the selected
source code to the generated core through `compileCode` and the numeric Talos
adapter. `targetBodyEq` then records the physical validation marker separately.
Dynamic source behavior, target-state refinement, and export-table membership
are deliberately absent from this reusable package.
-/
structure ConcreteSupportedFunction
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (code : LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (target : AdaptedModule)
    (hosts : ResolvedHosts) where
  programSupported : Fir.Wasm.WasmSupported program
  programNamesUnique : program.NamesUnique
  contextProgram : context.program = program
  lowered : Fir.Wasm.lowerSupported program = .ok sourceModule
  sourceFunctionIndex : Nat
  sourceFunctionFound :
    sourceModule.functions[sourceFunctionIndex]? = some sourceFunction
  sourceResultKind : AbiKind
  sourceResultAt :
    sourceFunction.results[0]? = some sourceResultKind
  sourceDeclaration : LCNF.Decl .impure
  sourceDeclarationFound :
    program.findDecl? sourceDeclaration.name = some sourceDeclaration
  sourceDeclarationBody : sourceDeclaration.value = .code code
  sourceResultSelected :
    Fir.Wasm.effectiveDeclarationResultKind? sourceDeclaration =
      some sourceResultKind
  localsAligned : LocalLayoutAligned context sourceFunction
  adapted : adapt sourceModule = .ok target
  hostsResolved : resolveHosts sourceModule = .ok hosts
  hostsAligned :
    target.wasmModule.imports.length = hosts.hosts.length
  runtimeCallsAligned :
    ConcreteRuntimeCallsAligned sourceModule target hosts
  externalCallsAligned :
    ConcreteExternalCallsAligned program sourceModule target hosts
  targetFunctionIndex : Nat
  targetFunction : Wasm.Function
  notImport :
    target.wasmModule.imports[targetFunctionIndex]? = none
  targetFunctionFound :
    target.wasmModule.funcs[
        targetFunctionIndex - target.wasmModule.imports.length]? =
      some targetFunction
  targetBody : Wasm.Program
  targetBodyEq :
    targetFunction.body =
      targetBody ++ functionTerminal sourceModule sourceFunction
  bodyAdapted :
    CodeAdapted context sourceModule sourceFunction [] code targetBody
  singleResult : targetFunction.results.length = 1

/-- Recover the exact declaration-body validation performed by
`WasmSupported` for this compiler-selected function.

The local-kind row is existential because it is the validator's incremental
parameter row, not the lowerer's complete numeric-local row.  This theorem
contains no execution evidence and is the static starting point for deriving
current-node admission along the structured simulation relation. -/
theorem ConcreteSupportedFunction.validatedBody
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context code sourceModule
      sourceFunction target hosts) :
    ∃ parameterLocals,
      Fir.Wasm.addSupportedDeclarationParams? program spec.sourceDeclaration =
          some parameterLocals ∧
        Fir.Wasm.supportedCode program parameterLocals
            (some spec.sourceResultKind) code = true := by
  have declarationMember : spec.sourceDeclaration ∈ program.decls := by
    obtain ⟨_, index, inBounds, selected, _⟩ :=
      Array.find?_eq_some_iff_getElem.mp spec.sourceDeclarationFound
    rw [← selected]
    exact Array.getElem_mem inBounds
  have declarationsSupported :
      program.decls.all (Fir.Wasm.supportedDecl program) = true := by
    have supported := spec.programSupported
    unfold Fir.Wasm.WasmSupported Fir.Wasm.supportedProgram at supported
    simp only [Bool.and_eq_true] at supported
    exact supported.1.1
  have declarationSupported :
      Fir.Wasm.supportedDecl program spec.sourceDeclaration = true :=
    (Array.all_eq_true'.mp declarationsSupported) _ declarationMember
  unfold Fir.Wasm.supportedDecl at declarationSupported
  simp only [Bool.and_eq_true] at declarationSupported
  cases parametersFound :
      Fir.Wasm.addSupportedDeclarationParams? program spec.sourceDeclaration with
  | none =>
      simp [parametersFound, spec.sourceDeclarationBody] at declarationSupported
  | some parameterLocals =>
      refine ⟨parameterLocals, rfl, ?_⟩
      simpa [parametersFound, spec.sourceDeclarationBody,
        spec.sourceResultSelected] using
        declarationSupported.2

/-- Reindex declaration validation by the active result equality retained by
the structured global simulation relation. -/
theorem ConcreteSupportedFunction.validatedBodyAt
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context code sourceModule
      sourceFunction target hosts)
    {functionResult : AbiKind}
    (activeResult : spec.sourceResultKind = functionResult) :
    ∃ parameterLocals,
      Fir.Wasm.addSupportedDeclarationParams? program spec.sourceDeclaration =
          some parameterLocals ∧
        Fir.Wasm.supportedCode program parameterLocals
            (some functionResult) code = true := by
  simpa [activeResult] using spec.validatedBody

/-- A supported generated function together with the one extra static fact
needed by a named whole-export correctness theorem. Internal recursive
declarations use `ConcreteSupportedFunction` directly. -/
structure ConcreteSupportedExport
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (code : LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (target : AdaptedModule)
    (hosts : ResolvedHosts)
    (exportName : String)
    extends ConcreteSupportedFunction program context code sourceModule
      sourceFunction target hosts where
  exported :
    target.wasmModule.findExport exportName = some targetFunctionIndex

instance
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction target hosts exportName) :
    CoeDep
      (ConcreteSupportedExport program context code sourceModule
        sourceFunction target hosts exportName)
      spec
      (ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts) :=
  ⟨spec.toConcreteSupportedFunction⟩

/-- Successful concrete resolution provides the exact host contract installed
for the adapted module. -/
theorem ConcreteSupportedFunction.hostsSatisfy
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts) :
    hosts.env.Satisfies target.wasmModule hosts.spec :=
  hosts.satisfies target.wasmModule spec.hostsAligned

/-- Install an exact-return proof for the compiler core as the selected
physical target function, crossing its validation-only suffix once. -/
theorem ConcreteSupportedFunction.terminatesWithExactCore
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context} {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {initial afterCall : Wasm.Store Host}
    {parameters callerTail : List Wasm.Value}
    {witness : RefinementWitness} {physical : Wasm.Value}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (correct :
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
        sourceRuntime sourceEnv code spec.targetBody initial
        (spec.targetFunction.toLocals parameters.reverse) witness []
        (ExactReturnControlPost afterCall physical)) :
    Wasm.TerminatesWith hosts.env target.wasmModule spec.targetFunctionIndex
      initial (parameters ++ callerTail)
      (ExactReturnPost afterCall physical callerTail) :=
  correct.toConcreteTerminatesWith_of_exactReturnSuffix spec.notImport
    spec.targetFunctionFound spec.targetBodyEq parameterCount spec.singleResult

/-- Specialize whole-pipeline external alignment to one compiler-selected
named call. -/
theorem ConcreteSupportedFunction.externalCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {name : Lean.Name} {declaration : LCNF.Decl .impure} {id : Nat}
    (found : program.findDecl? name = some declaration)
    (external : ∃ metadata, declaration.value = .extern metadata)
    (callFound :
      callIndex? sourceModule (.declaration name) = some id) :
    ∃ operation resultKind imp,
      operation.name = name ∧
        ExternalOperationMatchesDeclaration operation declaration ∧
        operation.signature.results = #[resultKind] ∧
        target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (externalContract operation resultKind) ∧
        imp.params.length = operation.signature.params.size ∧
        imp.results.length = 1 :=
  spec.externalCallsAligned found external callFound

/--
Resolver/adaptor alignment specializes to the exact value-preserving cache
publication contract selected by the compiler-derived declaration and kind.

Successful host resolution rules out the two unrepresented floating-point
kinds hidden behind the resolver's private classification; callers therefore
need no separate `cacheSet` support certificate.
-/
theorem ConcreteSupportedFunction.cacheSetCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {declaration : Lean.Name} {kind : AbiKind} {id : Nat}
    (found :
      callIndex? sourceModule (.runtime (.cacheSet declaration kind)) =
        some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (cacheSetContract declaration kind) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  obtain ⟨_, actualContract, _, actualContractFound, _⟩ :=
    spec.hostsSatisfy id inBounds
  have resolvedSome :
      resolvedContract? (.cacheSet declaration kind) = some actualContract :=
    contracted.symm.trans actualContractFound
  simp only [resolvedContract?, hostFn?] at resolvedSome contracted
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = cacheSetStep declaration kind initial args)
    split at resolvedSome
    · rename_i supported
      simpa only [supported, if_true, Option.map_some, cacheSetFn]
        using contracted
    · simp at resolvedSome
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment specializes to the exact closure matcher
contract emitted by the compiler's candidate chain.  Unlike dynamic closure
selection, this theorem contains only static import and host-contract facts. -/
theorem ConcreteSupportedFunction.closureMatchesCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {function : Lean.Name} {arity fixed id : Nat}
    (found :
      callIndex? sourceModule
          (.runtime (.closureMatches function arity fixed)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (closureMatchesContract function arity fixed) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = closureMatchesStep function arity fixed initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some,
      closureMatchesFn] using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment specializes to the exact typed closure-capture
projection contract emitted by `compileFixedClosureFields`. Successful host
resolution constructively rules out the unrepresented floating kinds. -/
theorem ConcreteSupportedFunction.closureProjCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {function : Lean.Name} {arity fixed index : Nat} {kind : AbiKind}
    {id : Nat}
    (found :
      callIndex? sourceModule
          (.runtime (.closureProj function arity fixed index kind)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (closureProjContract function arity fixed index kind) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  obtain ⟨_, actualContract, _, actualContractFound, _⟩ :=
    spec.hostsSatisfy id inBounds
  have resolvedSome :
      resolvedContract? (.closureProj function arity fixed index kind) =
        some actualContract :=
    contracted.symm.trans actualContractFound
  simp only [resolvedContract?, hostFn?] at resolvedSome contracted
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = closureProjStep function arity fixed index kind initial args)
    split at resolvedSome
    · rename_i represented
      simpa only [represented, if_true, Option.map_some, closureProjFn]
        using contracted
    · simp at resolvedSome
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment specializes to the exact concrete natural
literal contract expected by the allocation refinement theorem. -/
theorem ConcreteSupportedFunction.naturalLiteralCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {value id : Nat}
    (found :
      callIndex? sourceModule
        (.runtime (.literal (.nat value) .tobject)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (naturalLiteralContract value) ∧
        imp.params.length = 0 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = naturalLiteralStep value initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, naturalLiteralFn]
      using contracted
  · change imp.params.length = 0 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment specializes to the exact concrete UTF-8 String
literal contract expected by the allocation refinement theorem. -/
theorem ConcreteSupportedFunction.stringLiteralCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {value : String}
    {id : Nat}
    (found :
      callIndex? sourceModule
        (.runtime (.literal (.str value) .object)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (stringLiteralContract value) ∧
        imp.params.length = 0 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = stringLiteralStep value initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, stringLiteralFn]
      using contracted
  · change imp.params.length = 0 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment specializes to the exact concrete constructor
allocation contract selected by its compiler-derived field and result kinds. -/
theorem ConcreteSupportedFunction.allocCtorCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {id : Nat}
    (found :
      callIndex? sourceModule
        (.runtime (.allocCtor info fieldKinds resultKind)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (allocCtorContract info fieldKinds resultKind) ∧
        imp.params.length = fieldKinds.size ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = allocCtorStep info fieldKinds resultKind initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, allocCtorFn]
      using contracted
  · change imp.params.length = fieldKinds.size at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment for a concrete object-field projection. -/
theorem ConcreteSupportedFunction.objectProjectionCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {index id : Nat}
    {resultKind : AbiKind}
    (found :
      callIndex? sourceModule
        (.runtime (.objectProj index resultKind)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (objectProjContract index) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = objectProjStep index initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, objectProjFn]
      using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment for a concrete `USize`-slot projection. -/
theorem ConcreteSupportedFunction.usizeProjectionCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {index id : Nat}
    (found :
      callIndex? sourceModule (.runtime (.usizeProj index)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (usizeProjContract index) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = usizeProjStep index initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, usizeProjFn]
      using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment for a concrete packed-scalar projection. -/
theorem ConcreteSupportedFunction.scalarProjectionCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {width offset id : Nat}
    {resultKind : AbiKind}
    (found :
      callIndex? sourceModule
        (.runtime (.scalarProj width offset resultKind)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (scalarProjContract width offset resultKind) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  obtain ⟨_, actualContract, _, actualContractFound, _⟩ :=
    spec.hostsSatisfy id inBounds
  have resolvedSome :
      resolvedContract? (.scalarProj width offset resultKind) =
        some actualContract :=
    contracted.symm.trans actualContractFound
  simp only [resolvedContract?, hostFn?] at resolvedSome contracted
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = scalarProjStep width offset resultKind initial args)
    split at resolvedSome
    · rename_i supported
      simpa only [supported, if_true, Option.map_some, scalarProjFn]
        using contracted
    · simp at resolvedSome
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment for one count-indexed concrete reset call. -/
theorem ConcreteSupportedFunction.resetCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {count id : Nat}
    (found :
      callIndex? sourceModule (.runtime (.reset count)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (resetContract count) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = resetStep count initial args)
    simpa only [resolvedContract?, hostFn?_reset, Option.map_some,
      resetFn] using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/--
Resolver/adaptor alignment specializes to the exact concrete reuse contract
selected by the replacement layout and compiler-derived field/result kinds.
-/
theorem ConcreteSupportedFunction.reuseCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {info : LCNF.CtorInfo}
    {updateHeader : Bool}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {id : Nat}
    (found :
      callIndex? sourceModule
        (.runtime (.reuse info updateHeader fieldKinds resultKind)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (reuseContract info updateHeader fieldKinds resultKind) ∧
        imp.params.length = fieldKinds.size + 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result =
            reuseStep info updateHeader fieldKinds resultKind initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, reuseFn]
      using contracted
  · simpa [RuntimeOp.signature, Nat.add_comm] using params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment for one concrete integer-boxing call. -/
theorem ConcreteSupportedFunction.boxCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {kind : BoxedScalarKind} {resultKind : AbiKind} {id : Nat}
    (found :
      callIndex? sourceModule
        (.runtime (.box kind.abiKind resultKind)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (boxContract kind resultKind) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = boxStep kind resultKind initial args)
    simpa only [resolvedContract?, hostFn?_box_abiKind, Option.map_some,
      boxFn] using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment for one concrete typed-unbox call. -/
theorem ConcreteSupportedFunction.unboxCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {kind : BoxedScalarKind} {id : Nat}
    (found :
      callIndex? sourceModule (.runtime (.unbox kind.abiKind)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (unboxContract kind) ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = unboxStep kind initial args)
    simpa only [resolvedContract?, hostFn?_unbox_abiKind, Option.map_some,
      unboxFn] using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- Resolver/adaptor alignment for the concrete sharing observation. -/
theorem ConcreteSupportedFunction.isSharedCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context code sourceModule
        sourceFunction target hosts)
    {id : Nat}
    (found :
      callIndex? sourceModule (.runtime .isShared) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some isSharedContract ∧
        imp.params.length = 1 ∧
        imp.results.length = 1 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = isSharedStep initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, isSharedFn]
      using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 1 at results
    exact results

/-- The syntax-directed proof for the statically selected generated function
constructs T1's exact successful-declaration certificate. -/
theorem ConcreteSupportedExport.toSuccessfulDeclaration
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
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction []
        target.wasmModule hosts.env sourceExternals sourceRuntime sourceEnv
        sourceCode spec.targetBody initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        resultRuntime resultValue resultKind resultStore resultWitness physical)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    SuccessfulDeclaration context sourceModule sourceFunction
      target.wasmModule hosts.env sourceExternals sourceRuntime resultRuntime
      sourceEnv sourceCode spec.targetFunction spec.targetFunctionIndex initial
      resultStore initialWitness resultWitness parameters resultKind resultValue
      physical :=
  simulation.toSuccessfulDeclaration spec.targetBodyEq parameterCount
    spec.singleResult
    spec.notImport spec.targetFunctionFound

/-- T3 whole-export success. The target function and index come from the
generated module's exported-name lookup, while T2 supplies exact source
execution and concrete body correctness for that selected function. -/
theorem ConcreteSupportedExport.correct
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
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction []
        target.wasmModule hosts.env sourceExternals sourceRuntime sourceEnv
        sourceCode spec.targetBody initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        resultRuntime resultValue resultKind resultStore resultWitness physical)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) := by
  have declaration :=
    spec.toSuccessfulDeclaration simulation parameterCount
  exact ⟨declaration.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    declaration.terminatesWith callerTail⟩

end FirTalos.Concrete
