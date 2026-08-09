import FirTalos.Correctness.ResumableWasm

/-!
# Collapse laws for emitted structured Wasm frames

The FIR adapter emits only direct calls, zero-arity blocks/loops/conditionals,
branches, returns, and ordinary atomic instructions.  A future small-step
machine will expose the bodies and callees of those structured instructions.
This module proves the local equations needed to collapse each completed
reified frame back to one checked `ResumableWasmStep`.

These are semantic laws, not caller-supplied execution certificates: their
finite body/callee paths are produced by the target transition relation and
the conclusion reconstructs Talos's own outer instruction result.
-/

namespace FirTalos.Correctness

/-- A completed internal callee ending at the compiler-emitted `.ret`
reconstructs the caller's single Talos call transition exactly. -/
theorem ResumableWasmStep.internalCall_of_callee_ret
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {callerStore : Wasm.Store α} {callerLocals : Wasm.Locals}
    {callerRest calleeRest : Wasm.Program}
    {count : Nat} {calleeAfter : ResumableWasmState α}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (calleePath : FinitePath (ResumableWasmStep module env) count
      (ResumableWasmState.functionEntry function callerStore
        callerLocals.values)
      calleeAfter)
    (atReturn : calleeAfter.program = .ret :: calleeRest) :
    ResumableWasmStep module env
      ⟨callerStore, callerLocals, .call functionIndex :: callerRest⟩
      ⟨calleeAfter.store,
        { callerLocals with
          values :=
            calleeAfter.locals.values.take function.results.length ++
              callerLocals.values.drop function.numParams },
        callerRest⟩ := by
  obtain ⟨bound, calleeRuns⟩ :=
    ResumableWasmStep.finitePath_run_ret
      notImport found calleePath atReturn
  apply ResumableWasmStep.fallthrough (fuel := bound + 1)
  simp only [Wasm.execOne.eq_def]
  rw [calleeRuns bound (Nat.le_refl bound)]

/-- A reified block body that falls through reconstructs the outer block's
stack normalization and instruction-boundary transition. -/
theorem ResumableWasmStep.block_of_body_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat}
    {body rest : Wasm.Program} {store : Wasm.Store α}
    {locals : Wasm.Locals} {count : Nat}
    {bodyAfter : ResumableWasmState α}
    (bodyPath : FinitePath (ResumableWasmStep module env) count
      ⟨store, locals, body⟩ bodyAfter)
    (completed : bodyAfter.program = []) :
    ResumableWasmStep module env
      ⟨store, locals, .block paramArity resultArity body :: rest⟩
      ⟨bodyAfter.store,
        { bodyAfter.locals with
          values := bodyAfter.locals.values.take resultArity ++
            locals.values.drop paramArity },
        rest⟩ := by
  obtain ⟨bound, bodyRuns⟩ :=
    ResumableWasmStep.finitePath_exec_fallthrough bodyPath completed
  apply ResumableWasmStep.fallthrough (fuel := bound + 1)
  simp only [Wasm.execOne.eq_def]
  rw [bodyRuns bound (Nat.le_refl bound)]

/-- Branching to the current block label has the same normalized outer
fallthrough as reaching the end of the block body. -/
theorem ResumableWasmStep.block_of_body_br_zero
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat}
    {body rest branchRest : Wasm.Program} {store : Wasm.Store α}
    {locals : Wasm.Locals} {count : Nat}
    {bodyAfter : ResumableWasmState α}
    (bodyPath : FinitePath (ResumableWasmStep module env) count
      ⟨store, locals, body⟩ bodyAfter)
    (atBranch : bodyAfter.program = .br 0 :: branchRest) :
    ResumableWasmStep module env
      ⟨store, locals, .block paramArity resultArity body :: rest⟩
      ⟨bodyAfter.store,
        { bodyAfter.locals with
          values := bodyAfter.locals.values.take resultArity ++
            locals.values.drop paramArity },
        rest⟩ := by
  obtain ⟨bound, bodyRuns⟩ :=
    ResumableWasmStep.finitePath_exec_br bodyPath atBranch
  apply ResumableWasmStep.fallthrough (fuel := bound + 1)
  simp only [Wasm.execOne.eq_def]
  rw [bodyRuns bound (Nat.le_refl bound)]

/-- A reified loop body that falls through exits the loop with Talos's exact
result-stack normalization.  A `br 0` restart remains a separate frame step. -/
theorem ResumableWasmStep.loop_of_body_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat}
    {body rest : Wasm.Program} {store : Wasm.Store α}
    {locals : Wasm.Locals} {count : Nat}
    {bodyAfter : ResumableWasmState α}
    (bodyPath : FinitePath (ResumableWasmStep module env) count
      ⟨store, locals, body⟩ bodyAfter)
    (completed : bodyAfter.program = []) :
    ResumableWasmStep module env
      ⟨store, locals, .loop paramArity resultArity body :: rest⟩
      ⟨bodyAfter.store,
        { bodyAfter.locals with
          values := bodyAfter.locals.values.take resultArity ++
            locals.values.drop paramArity },
        rest⟩ := by
  obtain ⟨bound, bodyRuns⟩ :=
    ResumableWasmStep.finitePath_exec_fallthrough bodyPath completed
  apply ResumableWasmStep.fallthrough (fuel := bound + 1)
  rw [Wasm.execOne_loop_succ]
  simp only
  rw [bodyRuns bound (Nat.le_refl bound)]

/-- A nonzero condition selects and collapses a completed reified then-frame. -/
theorem ResumableWasmStep.iff_of_then_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat}
    {thenBody elseBody rest : Wasm.Program} {store : Wasm.Store α}
    {locals : Wasm.Locals} {condition : UInt32} {values : List Wasm.Value}
    {count : Nat} {bodyAfter : ResumableWasmState α}
    (conditionNonzero : condition ≠ 0)
    (bodyPath : FinitePath (ResumableWasmStep module env) count
      ⟨store, { locals with values := values }, thenBody⟩ bodyAfter)
    (completed : bodyAfter.program = []) :
    ResumableWasmStep module env
      ⟨store, { locals with values := .i32 condition :: values },
        .iff paramArity resultArity thenBody elseBody :: rest⟩
      ⟨bodyAfter.store,
        { bodyAfter.locals with
          values := bodyAfter.locals.values.take resultArity ++
            values.drop paramArity },
        rest⟩ := by
  obtain ⟨bound, bodyRuns⟩ :=
    ResumableWasmStep.finitePath_exec_fallthrough bodyPath completed
  apply ResumableWasmStep.fallthrough (fuel := bound + 1)
  simp only [Wasm.execOne.eq_def, if_pos conditionNonzero]
  rw [bodyRuns bound (Nat.le_refl bound)]

/-- A zero condition selects and collapses a completed reified else-frame. -/
theorem ResumableWasmStep.iff_of_else_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat}
    {thenBody elseBody rest : Wasm.Program} {store : Wasm.Store α}
    {locals : Wasm.Locals} {values : List Wasm.Value}
    {count : Nat} {bodyAfter : ResumableWasmState α}
    (bodyPath : FinitePath (ResumableWasmStep module env) count
      ⟨store, { locals with values := values }, elseBody⟩ bodyAfter)
    (completed : bodyAfter.program = []) :
    ResumableWasmStep module env
      ⟨store, { locals with values := .i32 0 :: values },
        .iff paramArity resultArity thenBody elseBody :: rest⟩
      ⟨bodyAfter.store,
        { bodyAfter.locals with
          values := bodyAfter.locals.values.take resultArity ++
            values.drop paramArity },
        rest⟩ := by
  obtain ⟨bound, bodyRuns⟩ :=
    ResumableWasmStep.finitePath_exec_fallthrough bodyPath completed
  apply ResumableWasmStep.fallthrough (fuel := bound + 1)
  simp only [Wasm.execOne.eq_def, ne_eq, not_true_eq_false, if_false]
  rw [bodyRuns bound (Nat.le_refl bound)]

end FirTalos.Correctness
