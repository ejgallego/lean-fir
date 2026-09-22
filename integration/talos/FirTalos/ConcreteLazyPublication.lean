import FirTalos.ConcreteReuseCapacityCacheCorrectness

/-!
Facts-aware source transport for a complete internal lazy-cache miss.

Publication deliberately makes the returned ownership graph persistent. It
need not preserve ordinaryness at every heap location; it must preserve the
retained reuse-token facts of the caller. These lemmas compose the existing
callee and publication proofs at that narrower boundary. They do not change
the structured simulator's stronger declaration-entry transport invariant.
-/

namespace FirTalos.Concrete

open Lean Lean.Compiler Fir.Wasm Fir.LeanIR.Impure Fir.Wasm.Concrete
open FirTalos.Correctness

/-- An ordinary callee prefix followed by facts-aware publication preserves
exactly the caller's retained facts after binding, without requiring the
published graph itself to remain ordinary. -/
theorem ReuseTokenOrdinaryBindTransport.precompose
    {facts : ReuseCapacityFacts} {resultId : FVarId}
    {before middle after : RuntimeState} {sourceEnv : Env} {result : Value}
    (beforePublication : OrdinaryPersistenceTransport before middle)
    (publication : ReuseTokenOrdinaryBindTransport facts resultId middle after
      sourceEnv result) :
    ReuseTokenOrdinaryBindTransport facts resultId before after sourceEnv
      result := by
  intro ordinary
  exact publication (ordinary.transport beforePublication)

section InternalMiss

variable
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {sourceDeclaration : LCNF.Decl .impure}
    {resultKind : AbiKind}
    {calleeCode : LCNF.Code .impure}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {stepCost : Nat}

/-- The complete compiler-selected internal miss transports retained token
ordinaryness from caller entry through initializer execution, recursive
publication, and destination binding. Unlike the all-location transport,
this theorem admits heap-valued initializer results.

The actual lowering/adapter equations select the recursive callee. Its
existing miss induction supplies the exact publication transport, rather
than a new caller-selected target path or a non-heap result restriction. -/
theorem SourceLazyLetResult.miss_ordinaryBindTransport_of_internalCompiler
    (supported : LazyCacheInternalMissSupported context decl declaration
      sourceDeclaration resultKind calleeCode)
    (sourceStep : SourceLazyLetResult .miss context sourceExternals
      sourceRuntime sourceEnv decl continuation nextRuntime sourceValue)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted : instructions sourceModule callerFunction labels valueCode =
      .ok targetValue)
    (induction : LazyCacheInternalMissInduction context sourceModule module
      hostEnv sourceExternals facts sourceRuntime sourceEnv decl.fvarId
      declaration calleeCode resultKind initial initialWitness sourceValue
      stepCost) :
    ReuseTokenOrdinaryBindTransport facts decl.fvarId sourceRuntime nextRuntime
      sourceEnv sourceValue := by
  rcases supported with
    ⟨⟨valueEq, kindEq, targetEq, _targetResultEq, _resultCompatible, paramsEq,
      _resultCompiled⟩, bodyEq⟩
  obtain ⟨_targetResultKind, _cacheIndex, declarationId, _cacheSetId,
      _recoveredTargetResultEq, _cacheEq, declarationCall, _cacheSetCall,
      _valueCodeEq, _targetValueEq⟩ :=
    compileCachedLetValue_adapted_inv context sourceModule callerFunction
      labels decl declaration sourceDeclaration _ valueCode targetValue
      valueEq kindEq targetEq paramsEq valueCompiled valueAdapted
  obtain ⟨calleeContext, calleeFunction, targetFunction, callRuntime,
      afterCall, callWitness, physical, contexts, callee, publication⟩ :=
    induction declarationCall
  have publicationRuntimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue :=
    (SourceLazyLetResult.miss_cacheFacts_of_callee valueEq targetEq
      (Array.isEmpty_iff.mp paramsEq) bodyEq sourceStep
      (contexts.sourceCodeResult
        callee.declaration.capacityPreserving.successful.sourceResult)).2
  rw [publicationRuntimeEq]
  exact publication.precompose callee.declaration.ordinaryTransport

/-- The preferred semantic postcondition, disjointness from the returned
ownership graph, supplies the complete miss transport. No ABI result kind is
excluded. Proving this disjointness for arbitrary admitted callers remains a
separate ownership obligation; this theorem does not assume it from typing. -/
theorem SourceLazyLetResult.miss_ordinaryBindTransport_of_publicationInduction
    (supported : LazyCacheInternalMissSupported context decl declaration
      sourceDeclaration resultKind calleeCode)
    (sourceStep : SourceLazyLetResult .miss context sourceExternals
      sourceRuntime sourceEnv decl continuation nextRuntime sourceValue)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted : instructions sourceModule callerFunction labels valueCode =
      .ok targetValue)
    (induction : LazyCacheInternalPublicationInduction context sourceModule
      module hostEnv sourceExternals facts sourceRuntime sourceEnv declaration
      calleeCode resultKind initial initialWitness sourceValue stepCost) :
    ReuseTokenOrdinaryBindTransport facts decl.fvarId sourceRuntime nextRuntime
      sourceEnv sourceValue :=
  SourceLazyLetResult.miss_ordinaryBindTransport_of_internalCompiler supported
    sourceStep valueCompiled valueAdapted induction.toMissInduction

end InternalMiss

end FirTalos.Concrete
