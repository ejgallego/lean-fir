import FirTalos.ConcreteSupportedExportCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open FirTalos.Correctness

local instance : LawfulBEq LCNF.LitValue where
  rfl := by
    intro a
    cases a <;> simp [BEq.beq, LCNF.instBEqLitValue.beq]
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq, LCNF.instBEqLitValue.beq]

local instance : LawfulBEq LCNF.CtorInfo where
  rfl := by
    intro a
    change ((a.name == a.name) && ((a.cidx == a.cidx) &&
      ((a.size == a.size) && ((a.usize == a.usize) && (a.ssize == a.ssize))))) = true
    simp
  eq_of_beq := by
    intro a b h
    change ((a.name == b.name) && ((a.cidx == b.cidx) &&
      ((a.size == b.size) && ((a.usize == b.usize) && (a.ssize == b.ssize))))) = true at h
    cases a; cases b
    simpa [Bool.and_eq_true] using h

deriving instance ReflBEq, LawfulBEq for RuntimeOp

/-- A runtime call index selects the exact runtime identity in the symbolic
import table, not a function row or a presentation-name match. -/
theorem runtimeImport_at_of_callIndex
    {source : Fir.Wasm.Module} {operation : RuntimeOp} {index : Nat}
    (called : callIndex? source (.runtime operation) = some index) :
    ∃ imp, source.imports[index]? = some imp ∧ imp.key = .runtime operation := by
  obtain ⟨inBounds, matching, _⟩ :=
    Array.findIdx?_eq_some_iff_getElem.mp called
  let imp := source.imports[index]
  have operationEq : imp.operation? = some operation := beq_iff_eq.mp matching
  refine ⟨imp, Array.getElem?_eq_getElem inBounds, ?_⟩
  cases keyEq : imp.key with
  | runtime actual =>
      simp only [Import.operation?, keyEq, Option.some.injEq] at operationEq
      simp [operationEq]
  | external name =>
      simp [Import.operation?, keyEq] at operationEq

/-- Adaptation retains the source import at its exact numeric slot. -/
theorem adaptedImport_at
    {source : Fir.Wasm.Module} {target : AdaptedModule}
    (adapted : adapt source = .ok target)
    {index : Nat} {imp : Fir.Wasm.Import}
    (found : source.imports[index]? = some imp) :
    target.wasmModule.imports[index]? = some (importDecl imp) := by
  obtain ⟨_, _, layout⟩ := adapt_preserves_module_layout adapted
  simp [layout, List.getElem?_map, found]

/-- Successful production adaptation and concrete host resolution align every
runtime call with its exact positional contract and semantic signature. This
is a static compiler/resolver theorem: no client alignment assumption, source
or target execution, heap invariant, or resource premise is required. -/
theorem concreteRuntimeCallsAligned_ofPipeline
    {source : Fir.Wasm.Module} {target : AdaptedModule} {hosts : ResolvedHosts}
    (adapted : adapt source = .ok target)
    (resolved : resolveHosts source = .ok hosts) :
    ConcreteRuntimeCallsAligned source target hosts := by
  intro operation index called
  obtain ⟨imp, found, runtime⟩ := runtimeImport_at_of_callIndex called
  obtain ⟨host, hostFound, hostSelected, signature⟩ :=
    resolveHosts_runtime_at resolved found runtime
  have targetFound := adaptedImport_at adapted found
  refine ⟨importDecl imp, targetFound, ?_, ?_, ?_, ?_⟩
  · exact List.getElem?_eq_some_iff.mp targetFound |>.1
  · simp only [ResolvedHosts.spec, List.getElem?_map, hostFound,
      resolvedContract?, hostSelected, Option.map_some, Option.some.injEq]
    rfl
  · simp [importDecl, signature]
  · simp [importDecl, signature]

end FirTalos.Concrete
