import FirTalos.ConcreteRegionCode

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Immediate literal entry, preserving the exact runtime, store and witness.
The compiler and frame relation determine both local indices and execution. -/
theorem ConcreteStructuredRegionCodeCore.advance_immediateLiteral
    {context : Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hosts : Wasm.HostEnv Host} {externals : ExternalImpl} {labels : LabelContext}
    {runtime : RuntimeState} {env : Env} {decl : Compiler.LCNF.LetDecl .impure}
    {continuation : Compiler.LCNF.Code .impure} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {code : Wasm.Program} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host}
    {literal : Compiler.LCNF.LitValue} {kind : AbiKind}
    {entryRuntime : RuntimeState} {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} {facts : ReuseCapacityFacts} {bytes : Nat}
    (shape : ImmediateLiteralKind literal kind)
    (valueEq : decl.value = .lit literal)
    (valueKind : letValueKind decl = .ok kind)
    (resultCompiled : getLocal context decl.fvarId = .ok (.localGet decl.fvarId, kind))
    (aligned : LocalLayoutAligned context sourceFunction)
    (active : ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals
      labels entryRuntime entryStore entryWitness facts bytes runtime env
      (.let decl continuation) store locals code witness source target) :
    ∃ sourceAfter targetAfter resumedLocals rest,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hosts) 2 target targetAfter ∧
      ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals labels
        entryRuntime entryStore entryWitness (eraseReuseCapacityFact facts decl.fvarId) bytes
        runtime (bind env decl.fvarId shape.sourceValue) continuation
        store resumedLocals rest witness sourceAfter targetAfter ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  have related := active.focus
  obtain ⟨valueCode, targetValue, rest, resultIndex, compiled, adapted, resultFound,
      continuationAdapted, codeEq⟩ := CodeAdaptedWithSuffix.let_eq related.adapted
  rw [shape.compileLetValue_eq valueEq valueKind] at compiled
  cases Except.ok.inj compiled
  rw [shape.instructions_eq] at adapted
  cases Except.ok.inj adapted
  obtain ⟨index, found, kindAt⟩ := aligned resultCompiled
  rw [resultFound] at found
  cases Option.some.inj found
  obtain ⟨updated, set, nextAligned⟩ := related.frameAligned.set?
    (nextRuntime := runtime) (nextEnv := bind env decl.fvarId shape.sourceValue)
    (nextStore := store) (nextWitness := witness) (physical := shape.physical) resultFound
  have evaluated : SourceLetResult context runtime env decl runtime shape.sourceValue := by
    cases shape <;> simp [SourceLetResult, evalLetValue, valueEq,
      Fir.LeanIR.Impure.literal, ImmediateLiteralKind.sourceValue, Pure.pure, Except.pure]
  obtain ⟨sourceAfter, targetAfter, sourceStep, path, focus, joins, frames, targetFrames⟩ :=
    related.advance_flatLet codeEq continuationAdapted
      (shape.structuredFlatProgram module resultIndex)
      (letStepSimulates_immediateLiteral shape evaluated related.stateRelated
        resultFound kindAt set) nextAligned
  refine ⟨sourceAfter, targetAfter, _, rest, sourceStep, ?_,
    active.afterLocalBind focus resultFound set, joins, frames,
    targetFrames⟩
  simpa using path

/-- Small tagged natural literals do not allocate. This precise result rule
does not relabel heap naturals or arbitrary `tobject` values as tagged. -/
theorem ConcreteStructuredRegionCodeCore.advance_smallTaggedNatural
    {program : Fir.LeanIR.ImpureProgram} {context : Context}
    {rootCode : Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context rootCode sourceModule
      sourceFunction targetModule hosts)
    {externals : ExternalImpl} {labels : LabelContext}
    {runtime : RuntimeState} {env : Env} {decl : Compiler.LCNF.LetDecl .impure}
    {continuation : Compiler.LCNF.Code .impure} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {code : Wasm.Program} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host} {value : Nat}
    {entryRuntime : RuntimeState} {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} {facts : ReuseCapacityFacts} {bytes : Nat}
    (small : value ≤ maxImmediatePayload)
    (valueEq : decl.value = .lit (.nat value))
    (valueKind : letValueKind decl = .ok .tagged)
    (resultCompiled : getLocal context decl.fvarId = .ok (.localGet decl.fvarId, .tagged))
    (active : ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals
      labels entryRuntime entryStore entryWitness facts bytes runtime env
      (.let decl continuation) store locals code witness source target) :
    ∃ sourceAfter targetAfter resumedLocals rest,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2
        target targetAfter ∧
      ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals labels
        entryRuntime entryStore entryWitness (eraseReuseCapacityFact facts decl.fvarId) bytes
        runtime (bind env decl.fvarId (.object (.tagged (UInt64.ofNat value)))) continuation
        store resumedLocals rest witness sourceAfter targetAfter ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  have related := active.focus
  have sourceSmall : value ≤ maxTaggedPayload := by
    simp [maxImmediatePayload, maxTaggedPayload] at *; omega
  have fits64 : value < UInt64.size := by
    simp [maxImmediatePayload, UInt64.size] at *; omega
  have payloadEq : (UInt64.ofNat value).toNat = value := by simp [Nat.mod_eq_of_lt fits64]
  have payloadSmall : (UInt64.ofNat value).toNat ≤ maxImmediatePayload := by
    simpa [payloadEq] using small
  let word := Word32.encodeImmediate (UInt64.ofNat value).toNat payloadSmall
  let physical := Wasm.Value.i32 (UInt32.ofNat word.value)
  obtain ⟨valueCode, targetValue, rest, resultIndex, compiled, adapted, resultFound,
      continuationAdapted, codeEq⟩ := CodeAdaptedWithSuffix.let_eq related.adapted
  have compiledEq : compileLetValue context decl =
      .ok [.call (.runtime (.literal (.nat value) .tagged))] := by
    simp [compileLetValue, valueEq, valueKind, AbiKind.acceptsLiteral,
      compileLiteral, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [compiledEq] at compiled
  cases Except.ok.inj compiled
  cases foundCall : callIndex? sourceModule (.runtime (.literal (.nat value) .tagged)) with
  | none =>
      simp [instructions, instruction, foundCall, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at adapted
  | some id =>
    have adaptedEq : targetValue = [.call id] := by
      simpa [instructions, instruction, foundCall, Bind.bind, Except.bind,
        Pure.pure, Except.pure] using adapted.symm
    subst targetValue
    obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
      spec.runtimeCallsAligned foundCall
    have contract : hosts.spec.contracts[id]? = some (naturalLiteralContract value) := by
      change hosts.spec.contracts[id]? =
        some (fun initial args result => result = naturalLiteralStep value initial args)
      simpa only [resolvedContract?, hostFn?, Option.map_some, naturalLiteralFn,
        naturalLiteralContract]
        using contracted
    have parameterCount : imp.params.length = 0 := params
    have resultCount : imp.results.length = 1 := results
    obtain ⟨index, found, kindAt⟩ := spec.localsAligned resultCompiled
    rw [resultFound] at found
    cases Option.some.inj found
    obtain ⟨updated, set, nextAligned⟩ := related.frameAligned.set?
      (nextRuntime := runtime)
      (nextEnv := bind env decl.fvarId (.object (.tagged (UInt64.ofNat value))))
      (nextStore := store) (nextWitness := witness) (physical := physical) resultFound
    have valueRelated : PhysicalValueRel witness .tagged physical
        (.object (.tagged (UInt64.ofNat value))) :=
      .word32 (.tagged (.immediate _ payloadSmall))
    have nextState := related.stateRelated.bindPhysical resultFound kindAt valueRelated set
    rw [related.stateRelated.clearFailure] at nextState
    have allocated : allocateNatural store.host.runtime.heap value =
        .ok (store.host.runtime.heap, word) := by
      simp [allocateNatural, sourceSmall, encodeTagged_immediate _ _ payloadSmall, word]
    have operation : naturalLiteralStep value store [] = .Return [physical] store := by
      simp [naturalLiteralStep, related.stateRelated.clearFailure, allocated,
        replaceHeap, physical]
    have step : LetStepSimulates context sourceFunction targetModule.wasmModule
        hosts.env decl [.call id] runtime runtime env
        (.object (.tagged (UInt64.ofNat value))) store store locals updated
        resultIndex witness witness := by
      refine ⟨?_, related.stateRelated, nextState, ?_⟩
      · simp [SourceLetResult, evalLetValue, valueEq, Fir.LeanIR.Impure.literal,
          sourceSmall, Pure.pure, Except.pure]
      · intro rest Q tail continued
        exact wp_naturalLiteral_let tail imported spec.hostsSatisfy inBounds
          contract parameterCount resultCount operation set continued
    have flat : StructuredWasmFlatProgram targetModule.wasmModule
        ([.call id] ++ [.localSet resultIndex]) :=
      .cons (.importedCall imported) (.cons (.atomic (by trivial)) .nil)
    obtain ⟨sourceAfter, targetAfter, sourceStep, path, focus, joins, frames,
        targetFrames⟩ := related.advance_flatLet codeEq continuationAdapted flat step nextAligned
    exact ⟨sourceAfter, targetAfter, _, rest, sourceStep, path,
      active.afterLocalBind focus resultFound set, joins,
      frames, targetFrames⟩

end FirTalos.Concrete
