import FirTalos.ConcreteReuseCapacityCacheCorrectness
import FirTalos.ConcreteRuntimeAlignment

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open FirTalos.Correctness

/-- Independent successful adaptation and concrete resolution have the same
import count because both preserve the original positional table. -/
theorem resolveHosts_aligned_of_adapt
    {source : Fir.Wasm.Module} {target : AdaptedModule} {hosts : ResolvedHosts}
    (adapted : adapt source = .ok target)
    (resolved : resolveHosts source = .ok hosts) :
    target.wasmModule.imports.length = hosts.hosts.length :=
  (adapt_preserves_import_count adapted).trans
    (resolveHosts_preserves_import_count resolved).symm

/-- The executable host environment satisfies its exact invocation contracts
without a separately supplied table-length premise. This alone does not prove
the semantic runtime/external contract alignment required by compiler rules. -/
theorem resolveHosts_satisfy_of_adapt
    {source : Fir.Wasm.Module} {target : AdaptedModule} {hosts : ResolvedHosts}
    (adapted : adapt source = .ok target)
    (resolved : resolveHosts source = .ok hosts) :
    hosts.env.Satisfies target.wasmModule hosts.spec :=
  hosts.satisfies target.wasmModule (resolveHosts_aligned_of_adapt adapted resolved)

/-- Construct a supported export from the production-generated row, without
requiring an existing export witness.

The caller selects a source declaration, not a handwritten symbolic function,
numeric index, local layout, or adapted body. The selected declaration identity
is retained in the conclusion; its effective result ABI comes from lowering,
and need not equal the declaration's unrefined public ABI classification.

The supported-program/name checks, external contract alignment, and named
export lookup remain explicit static obligations. Import count and runtime
contract alignment are derived from successful adaptation and resolution.
This constructor adds no source execution,
target execution, current-step admission, address-space safety, or entry-frame
premise; those belong to the subsequent runtime correctness theorem. The input
is the actual `lowerSupported`/`adapt` pair: no capture, closed-closure pruning,
resident-linking or encoded-artifact correspondence is asserted. -/
theorem ConcreteSupportedExport.exists_ofSupportedPipeline
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {declaration : LCNF.Decl .impure}
    {code : LCNF.Code .impure}
    {resultKind : AbiKind}
    {exportName : String}
    (supported : Fir.Wasm.WasmSupported program)
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : adapt sourceModule = .ok target)
    (resolved : resolveHosts sourceModule = .ok hosts)
    (externalAligned :
      ConcreteExternalCallsAligned program sourceModule target hosts)
    (found : program.findDecl? declaration.name = some declaration)
    (body : declaration.value = .code code)
    (classified :
      Fir.Wasm.abiKind? declaration.type = .ok (some resultKind))
    (exported :
      target.wasmModule.findExport exportName =
        callIndex? sourceModule (.declaration declaration.name)) :
    ∃ context sourceFunction,
      ∃ spec : ConcreteSupportedExport program context code sourceModule
          sourceFunction target hosts exportName,
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program ∧
        spec.sourceDeclaration = declaration := by
  let caller : Fir.Wasm.Context := {
    program
    localKinds := []
    cachedDeclarations := Fir.Wasm.cachedDeclarationNames program }
  obtain ⟨context, sourceFunction, _, ⟨row⟩⟩ :=
    ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipeline
      (caller := caller) rfl rfl namesUnique lowered adapted found body classified
  let spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction target hosts exportName := {
    row with
    programSupported := supported
    programNamesUnique := namesUnique
    lowered
    sourceDeclaration := declaration
    sourceDeclarationFound := row.declarationFound
    sourceDeclarationBody := row.declarationBody
    adapted
    hostsResolved := resolved
    hostsAligned := resolveHosts_aligned_of_adapt adapted resolved
    runtimeCallsAligned := concreteRuntimeCallsAligned_ofPipeline adapted resolved
    externalCallsAligned := externalAligned
    exported := exported.trans row.callIndexEq }
  exact ⟨context, sourceFunction, spec, row.contextCaches, rfl⟩

/-- Regression for the selector's identity-carrying result: both the function
name and effective ABI belong to the requested declaration. An unrelated
declaration cannot be substituted without proving its equality to the retained
source declaration. In particular, no equality with the public classification
used to establish a single result is asserted. -/
theorem ConcreteSupportedExport.selectedDeclarationResult
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context} {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts} {exportName : String}
    {declaration : LCNF.Decl .impure}
    (spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction target hosts exportName)
    (selected : spec.sourceDeclaration = declaration) :
    sourceFunction.name = declaration.name ∧
      Fir.Wasm.effectiveDeclarationResultKind? declaration =
        some spec.sourceResultKind := by
  subst declaration
  exact ⟨spec.sourceFunctionName, spec.sourceResultSelected⟩

/-- Regression through the actual constructor: the selected declaration's
identity, cache row and effective result survive the whole static assembly.
Neither a handwritten function/index, import-count premise, nor runtime-contract
alignment premise is supplied. -/
example
    {program : Fir.LeanIR.ImpureProgram} {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    {declaration : LCNF.Decl .impure} {code : LCNF.Code .impure}
    {resultKind : AbiKind} {exportName : String}
    (supported : Fir.Wasm.WasmSupported program)
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : adapt sourceModule = .ok target)
    (resolved : resolveHosts sourceModule = .ok hosts)
    (externalAligned : ConcreteExternalCallsAligned program sourceModule target hosts)
    (found : program.findDecl? declaration.name = some declaration)
    (body : declaration.value = .code code)
    (classified : Fir.Wasm.abiKind? declaration.type = .ok (some resultKind))
    (exported : target.wasmModule.findExport exportName =
      callIndex? sourceModule (.declaration declaration.name)) :
    ∃ context sourceFunction,
      ∃ spec : ConcreteSupportedExport program context code sourceModule
          sourceFunction target hosts exportName,
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program ∧
        spec.sourceDeclaration = declaration ∧
        sourceFunction.name = declaration.name ∧
        Fir.Wasm.effectiveDeclarationResultKind? declaration =
          some spec.sourceResultKind := by
  obtain ⟨context, sourceFunction, spec, caches, selected⟩ :=
    ConcreteSupportedExport.exists_ofSupportedPipeline supported namesUnique
      lowered adapted resolved externalAligned found body
      classified exported
  exact ⟨context, sourceFunction, spec, caches, selected,
    spec.selectedDeclarationResult selected⟩

end FirTalos.Concrete
