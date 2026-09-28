import FirTalos.ConcreteLazyBodyEntry
import FirTalos.ConcreteRegionCode

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Cache-miss entry installs the actual caller continuations and starts a
construction region at the unchanged runtime. No nonheap-result restriction,
chosen return root or post-entry separation premise is needed. The exact frame
equations retain the saved caller; nested lazy-stack admission remains separate. -/
theorem ConcreteStructuredLazyCallReadyFocus.enterRegion
    {program : Fir.LeanIR.ImpureProgram} {context calleeContext : Context}
    {sourceModule : Fir.Wasm.Module} {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts} {externals : ExternalImpl}
    {labels : LabelContext} {decl : Compiler.LCNF.LetDecl .impure}
    {declaration : Name} {sourceDeclaration : Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    {call : LazyCacheCallSupported context decl declaration sourceDeclaration resultKind}
    {generated : LazyCacheGeneratedEnvironment context sourceModule}
    {entryRuntime runtime : RuntimeState} {entryStore store : Wasm.Store Host}
    {entryWitness witness : RefinementWitness} {facts : ReuseCapacityFacts} {bytes : Nat}
    {callerEnv : Env} {continuation calleeCode : Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv} {sourceFrames : List Frame} {callerLocals : Wasm.Locals}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    {cacheIndex declarationId cacheSetId resultIndex : Nat}
    {source : MachineState} {target : StructuredWasmState Host}
    (ready : ConcreteStructuredLazyCallReadyFocus context sourceModule callerFunction labels
      call generated runtime callerEnv continuation callerJoins sourceFrames store
      callerLocals rest frames witness cacheIndex declarationId cacheSetId resultIndex source target)
    (scope : ConcreteStructuredResourceScope context sourceModule callerFunction externals
      entryRuntime entryStore entryWitness facts bytes runtime callerEnv store callerLocals witness)
    (contextProgram : context.program = program)
    (row : ConcreteGeneratedInternalDeclaration program sourceDeclaration calleeContext
      calleeCode sourceModule calleeFunction targetModule)
    (empty : findGlobal? runtime.globals declaration = none) :
    ∃ sourceAfter targetAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target targetAfter ∧
      ConcreteStructuredRegionCodeCore calleeContext sourceModule calleeFunction externals
        [] runtime store witness [] bytes runtime [] calleeCode store
        (row.targetFunction.toLocals []) row.targetFunction.body witness sourceAfter targetAfter ∧
      sourceAfter.joins = [] ∧
      sourceAfter.frames = .cache declaration ::
        .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames ∧
      targetAfter.frames =
        .call 1 callerLocals.values callerLocals
          [.call cacheSetId, .globalSet (2 * cacheIndex + 1), .const 1,
            .globalSet (2 * cacheIndex)] ::
        .label 0 callerLocals.values
          ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) :: frames := by
  obtain ⟨sourceAfter, targetAfter, step, path, focus, frame, joins, sourceFrames, targetFrames⟩ :=
    ready.enterBody scope contextProgram row empty
  exact ⟨sourceAfter, targetAfter, step, path, .atEntry focus frame,
    joins, sourceFrames, targetFrames⟩

end FirTalos.Concrete
