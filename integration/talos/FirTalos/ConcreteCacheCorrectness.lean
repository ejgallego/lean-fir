import FirTalos.ConcreteRuntime

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- The lowerer and Talos adapter expose the exact lazy-cache program consumed
by the concrete hit/miss proofs below. This theorem keeps the proof boundary
anchored to `compileLetValue`, rather than to a hand-written Wasm fragment. -/
theorem compileCachedLetValue_adapted
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (fvarId : Lean.FVarId) (type : Lean.Expr) (name : Lean.Name)
    (target : Lean.Compiler.LCNF.Decl .impure)
    (resultKind : AbiKind) (cacheIndex declarationId cacheSetId : Nat)
    (kindEq : Fir.Wasm.checkedAbiKind type = .ok resultKind)
    (targetEq : context.program.findDecl? name = some target)
    (paramsEq : target.params.isEmpty = true)
    (cacheEq :
      context.cachedDeclarations.findIdx? (· == name) = some cacheIndex)
    (declarationFound :
      callIndex? sourceModule (.declaration name) = some declarationId)
    (cacheSetFound :
      callIndex? sourceModule (.runtime (.cacheSet name resultKind)) =
        some cacheSetId) :
    let decl : Lean.Compiler.LCNF.LetDecl .impure := {
      fvarId
      binderName := fvarId.name
      type
      value := .fap name #[] }
    Fir.Wasm.compileLetValue context decl = .ok [
        .globalGet (2 * cacheIndex) .uint32,
        .ifElse [] [
          .call (.declaration name),
          .call (.runtime (.cacheSet name resultKind)),
          .globalSet (2 * cacheIndex + 1) resultKind,
          .i32Const .uint32 1,
          .globalSet (2 * cacheIndex) .uint32],
        .globalGet (2 * cacheIndex + 1) resultKind] ∧
      instructions sourceModule sourceFunction labels [
        .globalGet (2 * cacheIndex) .uint32,
        .ifElse [] [
          .call (.declaration name),
          .call (.runtime (.cacheSet name resultKind)),
          .globalSet (2 * cacheIndex + 1) resultKind,
          .i32Const .uint32 1,
          .globalSet (2 * cacheIndex) .uint32],
        .globalGet (2 * cacheIndex + 1) resultKind] = .ok [
          .globalGet (2 * cacheIndex),
          .iff 0 0 [] [
            .call declarationId,
            .call cacheSetId,
            .globalSet (2 * cacheIndex + 1),
            .const 1,
            .globalSet (2 * cacheIndex)],
          .globalGet (2 * cacheIndex + 1)] := by
  dsimp
  constructor
  · exact Fir.Wasm.compileLetValue_fap_cached context fvarId type name target
      resultKind cacheIndex kindEq targetEq paramsEq cacheEq
  · simp [instructions, instruction, declarationFound, cacheSetFound]
    rfl

/-- The proof package required from one compiler-generated zero-argument
declaration before its result may be published through the lazy cache.

The declaration body itself starts with empty source locals and an empty
callee operand stack. `ConcreteFunctionBodyPost` reattaches each arbitrary
caller tail after the singleton cached result, exactly as Talos direct calls
do. Keeping the package tail-polymorphic makes it usable by every call site. -/
def CachedDeclarationBodyWP
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceRuntime : RuntimeState)
    (sourceCode : Lean.Compiler.LCNF.Code .impure)
    (targetFunction : Wasm.Function)
    (initial afterCall : Wasm.Store Host)
    (witness : RefinementWitness)
    (physical : Wasm.Value) : Prop :=
  targetFunction.numParams = 0 ∧
    targetFunction.results.length = 1 ∧
      ∀ tail,
        CodeWP context sourceModule sourceFunction [] module hostEnv
          sourceRuntime [] sourceCode targetFunction.body initial
          (targetFunction.toLocals [])
          witness []
          (ConcreteFunctionBodyPost targetFunction tail
            (fun final results =>
              final = afterCall ∧ results = physical :: tail))

/-- Weakening the continuation assertion preserves the concrete code
judgment. This local form mirrors the semantic-host helper but ranges over the
W6 concrete host and representation witness. -/
theorem concreteCodeWP_conseq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {target : Wasm.Program} {initial : Wasm.Store Host}
    {locals : Wasm.Locals} {witness : RefinementWitness}
    {tail : List Wasm.Value} {Q Q' : Wasm.Assertion Host}
    (post : ∀ continuation, Q continuation → Q' continuation)
    (correct : CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv sourceCode target initial locals witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv sourceCode target initial locals witness tail Q' :=
  ⟨correct.1, correct.2.1, Wasm.wp.conseq post correct.2.2⟩

/-- Concrete-host base rule for a generated source return installed as the
last two instructions of a singleton-result Wasm body. The related source
binding identifies the exact physical local returned to the caller. -/
theorem codeWP_return_to_bodyPost
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetFunction : Wasm.Function}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {result : Lean.FVarId} {sourceValue : Value} {kind : AbiKind}
    {resultIndex : Nat} {physical : Wasm.Value}
    (localCompiled :
      Fir.Wasm.getLocal context result = .ok (.localGet result, kind))
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (sourceLookup : lookup sourceEnv result = some sourceValue)
    (stateRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness)
    (targetLookup : targetLocals.get resultIndex = some physical)
    (resultEq : targetFunction.results.length = 1) :
    CodeWP context sourceModule sourceFunction [] module hostEnv sourceRuntime
      sourceEnv (.return result) [.localGet resultIndex, .ret]
      targetStore targetLocals witness []
      (ConcreteFunctionBodyPost targetFunction []
        (fun final results =>
          final = targetStore ∧ results = [physical])) := by
  obtain ⟨actual, actualLookup, _⟩ :=
    stateRelated.resolve sourceLookup resultFound kindAt
  rw [targetLookup] at actualLookup
  injection actualLookup with physicalEq
  subst actual
  refine ⟨codeAdapted_return localCompiled resultFound, stateRelated, ?_⟩
  rw [Wasm.wp_localGet_cons]
  have targetLookupWithStack :
      ({ targetLocals with values := [] } : Wasm.Locals).get resultIndex =
        some physical := by
    simpa [Wasm.Locals.get] using targetLookup
  simp only [targetLookupWithStack]
  rw [Wasm.wp_ret_cons]
  simp [ConcreteFunctionBodyPost, resultEq]

/-- For a zero-argument, singleton-result declaration it is enough to prove
the generated body once with an empty caller remainder. Wasm's function-body
postcondition restores every arbitrary caller tail structurally. -/
theorem CachedDeclarationBodyWP.of_emptyTail
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {initial afterCall : Wasm.Store Host}
    {witness : RefinementWitness} {physical : Wasm.Value}
    (paramsEq : targetFunction.numParams = 0)
    (resultEq : targetFunction.results.length = 1)
    (correct :
      CodeWP context sourceModule sourceFunction [] module hostEnv
        sourceRuntime [] sourceCode targetFunction.body initial
        (targetFunction.toLocals []) witness []
        (ConcreteFunctionBodyPost targetFunction []
          (fun final results =>
            final = afterCall ∧ results = [physical]))) :
    CachedDeclarationBodyWP context sourceModule sourceFunction module hostEnv
      sourceRuntime sourceCode targetFunction initial afterCall witness physical := by
  refine ⟨paramsEq, resultEq, fun tail => ?_⟩
  apply concreteCodeWP_conseq (correct := correct)
  intro continuation post
  cases continuation <;>
    simp_all [ConcreteFunctionBodyPost]

/-- First declaration-specific cache body family: a compiler-generated
zero-argument declaration that allocates one natural literal and returns it.
All heap growth and physical-value refinement come from the existing literal
rule; this theorem supplies the concrete return base case and packages the
complete generated body for lazy-cache callers. -/
theorem cachedDeclarationBodyWP_naturalLiteral
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host} {heap : MemoryState} {word : Word32}
    {targetFunction : Wasm.Function} {updated : Wasm.Locals}
    {resultIndex value : Nat} {witness : RefinementWitness}
    (valueEq : decl.value = .lit (.nat value))
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.call (.runtime (.literal (.nat value) .tobject))])
    (callFound : callIndex? sourceModule
      (.runtime (.literal (.nat value) .tobject)) = some id)
    (initialRelated : StateRelated sourceFunction sourceRuntime []
      initial (targetFunction.toLocals []) witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .tobject)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .tobject))
    (allocated : allocateNatural initial.host.runtime.heap value =
      .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (naturalLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (targetSet :
      (targetFunction.toLocals []).set? resultIndex
          (.i32 (UInt32.ofNat word.value)) =
        some updated)
    (paramsEq : targetFunction.numParams = 0)
    (resultEq : targetFunction.results.length = 1)
    (bodyEq : targetFunction.body = [
      .call id, .localSet resultIndex, .localGet resultIndex, .ret]) :
    CachedDeclarationBodyWP context sourceModule sourceFunction module hostEnv
      sourceRuntime (.let decl (.return decl.fvarId)) targetFunction initial
      (replaceHeap initial heap) witness (.i32 (UInt32.ofNat word.value)) := by
  apply CachedDeclarationBodyWP.of_emptyTail paramsEq resultEq
  rw [bodyEq]
  apply codeWP_naturalLiteral_let valueEq valueCompiled callFound
    initialRelated resultFound resultKindAt allocated hImp hSat hi hContract
    hParams hResults targetSet
  intro nextWitness extension nextRuntimeRelated valueRelated
  have failureClear :
      (replaceHeap initial heap).host.failure? = none := by
    simp [replaceHeap, clearFailure]
  have nextState := initialRelated.bindAfter extension nextRuntimeRelated
    failureClear resultFound resultKindAt valueRelated targetSet
  apply codeWP_return_to_bodyPost localCompiled resultFound resultKindAt
    (lookup_bind_self [] decl.fvarId
      (literal sourceRuntime (.nat value)).2)
    nextState (localUpdate_of_set? targetSet).1 resultEq

/-- A per-declaration body package supplies the store-specific, fuel-free
termination theorem expected by generated direct calls. -/
theorem CachedDeclarationBodyWP.terminatesWith
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {witness : RefinementWitness}
    {physical : Wasm.Value}
    (body :
      CachedDeclarationBodyWP context sourceModule sourceFunction module
        hostEnv sourceRuntime sourceCode targetFunction initial afterCall
        witness physical)
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? =
        some targetFunction)
    (tail : List Wasm.Value) :
    Wasm.TerminatesWith hostEnv module functionIndex initial tail
      (fun final results =>
        final = afterCall ∧ results = physical :: tail) := by
  apply CodeWP.toConcreteTerminatesWith notImport found
  simpa [body.1] using body.2.2 tail

/-- The exact two-global postcondition established by generated cache
publication. It is factored out of the miss proof so the next invocation can
consume the populated flag and cached value through the hit rule directly. -/
theorem cachePublication_globals
    {afterCache valueStore : Wasm.Store Host}
    {physical oldValue oldFlag : Wasm.Value}
    {valueIndex flagIndex : Nat}
    (hValue : afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq : valueStore =
      writeWasmGlobal afterCache valueIndex physical)
    (hFlag : valueStore.globals.globals[flagIndex]? = some oldFlag)
    (different : valueIndex ≠ flagIndex) :
    let publishedStore :=
      writeWasmGlobal valueStore flagIndex (.i32 1)
    publishedStore.globals.globals[flagIndex]? = some (.i32 1) ∧
      publishedStore.globals.globals[valueIndex]? = some physical := by
  constructor
  · exact writeWasmGlobal_get_self hFlag
  · rw [writeWasmGlobal_get_ne different.symm, valueStoreEq]
    exact writeWasmGlobal_get_self hValue

/-- A cache state produced by the miss publication sequence is immediately a
valid input to the generated hit path. The host runtime and both physical
globals are unchanged by the hit; only the caller's destination local is
updated with the cached physical value. -/
theorem lazyLetStepSimulates_hit_after_cachePublication
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {missBody : Wasm.Program} {flagIndex valueIndex resultIndex : Nat}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {afterCache valueStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {physical oldValue oldFlag : Wasm.Value}
    {witness nextWitness : RefinementWitness}
    (sourceStep : SourceLazyLetResult .hit context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue)
    (stateRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      (writeWasmGlobal valueStore flagIndex (.i32 1)) targetLocals witness)
    (hValue : afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq : valueStore =
      writeWasmGlobal afterCache valueIndex physical)
    (hFlag : valueStore.globals.globals[flagIndex]? = some oldFlag)
    (different : valueIndex ≠ flagIndex)
    (hSet : targetLocals.set? resultIndex physical = some nextLocals)
    (nextStateRelated : StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue)
      (writeWasmGlobal valueStore flagIndex (.i32 1)) nextLocals nextWitness) :
    LazyLetStepSimulates .hit context sourceFunction module hostEnv externals
      decl continuation
      [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue
      (writeWasmGlobal valueStore flagIndex (.i32 1))
      (writeWasmGlobal valueStore flagIndex (.i32 1))
      targetLocals nextLocals resultIndex witness nextWitness := by
  obtain ⟨flagPublished, valuePublished⟩ :=
    cachePublication_globals hValue valueStoreEq hFlag different
  exact lazyLetStepSimulates_hit sourceStep stateRelated flagPublished
    valuePublished hSet rfl nextStateRelated

/-- Close the complete generated lazy-miss block from one declaration's
`CodeWP` package. This removes the manually supplied `TerminatesWith` premise
from cache clients while reusing the existing concrete persistence, host-call,
two-global publication, reload, and destination-local proofs unchanged. -/
theorem lazyMissBodySimulates_of_bodyWP_cacheSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {declarationId cacheSetId : Nat} {imp : Wasm.ImportDecl}
    {declaration : Lean.Name} {kind : AbiKind}
    {targetStore afterCall afterCache valueStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {physical oldValue oldFlag : Wasm.Value}
    {valueIndex flagIndex resultIndex : Nat}
    (body :
      CachedDeclarationBodyWP context sourceModule sourceFunction module
        hostEnv sourceRuntime sourceCode targetFunction targetStore afterCall
        witness physical)
    (notImport : module.imports[declarationId]? = none)
    (functionFound :
      module.funcs[declarationId - module.imports.length]? =
        some targetFunction)
    (hImp : module.imports[cacheSetId]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : cacheSetId < module.imports.length)
    (hContract : spec.contracts[cacheSetId]? =
      some (cacheSetContract declaration kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : cacheSetStep declaration kind afterCall [physical] =
      .Return [physical] afterCache)
    (hValue : afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq : valueStore =
      writeWasmGlobal afterCache valueIndex physical)
    (hFlag : valueStore.globals.globals[flagIndex]? = some oldFlag)
    (different : valueIndex ≠ flagIndex)
    (hSet : targetLocals.set? resultIndex physical = some nextLocals) :
    LazyMissBodySimulates module hostEnv
      [.call declarationId, .call cacheSetId, .globalSet valueIndex,
        .const 1, .globalSet flagIndex]
      valueIndex resultIndex targetStore
      (writeWasmGlobal valueStore flagIndex (.i32 1))
      targetLocals nextLocals := by
  apply lazyMissBodySimulates_of_call_cacheSet
    (declarationCall := fun tail =>
      body.terminatesWith notImport functionFound tail)
    hImp hSat hi hContract hParams hResults operation hValue valueStoreEq
    hFlag different hSet

end FirTalos.Concrete
