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

/-- Static whole-pipeline evidence for one concrete generated export.

`bodyAdapted` is the crucial compiler-facing equation: it ties the selected
source code to the actual generated target body through `compileCode` and the
numeric Talos adapter. Dynamic source behavior and target-state refinement are
deliberately absent from this static package. -/
structure ConcreteSupportedExport
    (program : Fir.LeanIR.ImpureProgram)
    (context : Fir.Wasm.Context)
    (code : LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (target : AdaptedModule)
    (hosts : ResolvedHosts)
    (exportName : String) where
  programSupported : Fir.Wasm.WasmSupported program
  programNamesUnique : program.NamesUnique
  contextProgram : context.program = program
  lowered : Fir.Wasm.lowerSupported program = .ok sourceModule
  sourceFunctionIndex : Nat
  sourceFunctionFound :
    sourceModule.functions[sourceFunctionIndex]? = some sourceFunction
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
  exported :
    target.wasmModule.findExport exportName = some targetFunctionIndex
  notImport :
    target.wasmModule.imports[targetFunctionIndex]? = none
  targetFunctionFound :
    target.wasmModule.funcs[
        targetFunctionIndex - target.wasmModule.imports.length]? =
      some targetFunction
  bodyAdapted :
    CodeAdapted context sourceModule sourceFunction [] code targetFunction.body
  singleResult : targetFunction.results.length = 1

/-- Successful concrete resolution provides the exact host contract installed
for the adapted module. -/
theorem ConcreteSupportedExport.hostsSatisfy
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName) :
    hosts.env.Satisfies target.wasmModule hosts.spec :=
  hosts.satisfies target.wasmModule spec.hostsAligned

/-- Specialize whole-pipeline external alignment to one compiler-selected
named call. -/
theorem ConcreteSupportedExport.externalCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.cacheSetCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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

/-- Resolver/adaptor alignment specializes to the exact concrete natural
literal contract expected by the allocation refinement theorem. -/
theorem ConcreteSupportedExport.naturalLiteralCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.stringLiteralCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.allocCtorCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.objectProjectionCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.usizeProjectionCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.scalarProjectionCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.resetCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.reuseCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.boxCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.unboxCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
theorem ConcreteSupportedExport.isSharedCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
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
        sourceCode spec.targetFunction.body initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        resultRuntime resultValue resultKind resultStore resultWitness physical)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    SuccessfulDeclaration context sourceModule sourceFunction
      target.wasmModule hosts.env sourceExternals sourceRuntime resultRuntime
      sourceEnv sourceCode spec.targetFunction spec.targetFunctionIndex initial
      resultStore initialWitness resultWitness parameters resultKind resultValue
      physical :=
  simulation.toSuccessfulDeclaration parameterCount spec.singleResult
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
        sourceCode spec.targetFunction.body initial
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
