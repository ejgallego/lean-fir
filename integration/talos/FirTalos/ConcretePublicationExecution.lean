import FirTalos.ConcretePublicationScope

/-! Executable cache publication from production import alignment and the
whole-table cache relation. Physical global existence is derived, not assumed
by theorem clients. This suffix stops before the source destination bind. -/

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Execute the generated seven-step publication suffix. Compiler alignment
supplies the host import contract; cache-table refinement supplies both global
lanes, including a valid flag after the value write. The result kind is not
restricted to non-heap values. -/
theorem LazyCacheGlobalsRel.publicationFinitePath_of_compiler
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    {witness : RefinementWitness} {runtime : RuntimeState}
    {store afterCache : Wasm.Store Host}
    {declaration : Name} {kind : AbiKind} {physical : Wasm.Value}
    {cacheIndex cacheSetId resultIndex : Nat}
    {callerLocals calleeLocals : Wasm.Locals}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    (related : LazyCacheGlobalsRel witness sourceModule runtime store)
    (spec : ConcreteSupportedFunction program context code sourceModule
      sourceFunction target hosts)
    (initializerFound : sourceModule.initializers[cacheIndex]? = some declaration)
    (signature : (sourceModule.callSignature? (.declaration declaration)).bind
      (·.results[0]?) = some kind)
    (cacheSetCall : callIndex? sourceModule (.runtime (.cacheSet declaration kind)) =
      some cacheSetId)
    (operation : cacheSetStep declaration kind store [physical] =
      .Return [physical] afterCache) :
    FinitePath (StructuredWasmStep target.wasmModule hosts.env) 7
      ⟨store, .returning (physical :: calleeLocals.values),
        .call 1 callerLocals.values callerLocals
          [.call cacheSetId, .globalSet (2 * cacheIndex + 1),
            .const 1, .globalSet (2 * cacheIndex)] ::
        .label 0 callerLocals.values
          ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) :: frames⟩
      ⟨writeWasmGlobal (writeWasmGlobal afterCache (2 * cacheIndex + 1) physical)
          (2 * cacheIndex) (.i32 1),
        .running { callerLocals with values := physical :: callerLocals.values }
          (.localSet resultIndex :: rest), frames⟩ := by
  obtain ⟨oldFlag, oldValue, flagBefore, valueBefore⟩ :=
    related.slotLanesPresent initializerFound signature
  have valueAfter : afterCache.globals.globals[2 * cacheIndex + 1]? = some oldValue := by
    rw [cacheSetStep_preserves_wasmGlobals operation]
    exact valueBefore
  have flagAfter :
      (writeWasmGlobal afterCache (2 * cacheIndex + 1) physical).globals.globals[2 * cacheIndex]?
        = some oldFlag := by
    rw [writeWasmGlobal_get_ne (by omega), cacheSetStep_preserves_wasmGlobals operation]
    exact flagBefore
  obtain ⟨imp, importFound, importInBounds, contractFound, parameterCount, resultCount⟩ :=
    spec.cacheSetCall cacheSetCall
  exact structuredWasmLazyMissPublicationFinitePath callerLocals.values importFound
    spec.hostsSatisfy importInBounds contractFound parameterCount resultCount operation
    valueAfter rfl flagAfter (by omega)

end FirTalos.Concrete
