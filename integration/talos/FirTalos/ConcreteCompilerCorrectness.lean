import FirTalos.ConcreteSupportedExportCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/--
Inversion of the real two-stage compiler for a source return.

This theorem extracts the local kind and numeric slot from successful
`compileCode` plus Talos adaptation. It is compiler verification, not an
independently supplied translation certificate.
-/
theorem CodeAdapted.return_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {result : FVarId}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels (.return result)
        target) :
    ∃ kind resultIndex,
      Fir.Wasm.getLocal context result =
          .ok (.localGet result, kind) ∧
        findFVar? (functionBindings sourceFunction) result =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some kind ∧
        target = [.localGet resultIndex, .ret] := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases kindFound :
      Fir.Wasm.findLocalKind? context.localKinds result with
  | none =>
      have localError :
          Fir.Wasm.getLocal context result =
            .error (.unknownVariable result) := by
        simp [Fir.Wasm.getLocal, kindFound]
      rw [localError] at core
      change some (Except.error (CompileError.unknownVariable result)) =
        some (Except.ok symbolic) at core
      have impossible :
          Except.error (CompileError.unknownVariable result) =
            Except.ok symbolic :=
        Option.some.inj core
      contradiction
  | some kind =>
      have localCompiled :
          Fir.Wasm.getLocal context result =
            .ok (.localGet result, kind) := by
        simp [Fir.Wasm.getLocal, kindFound]
      rw [localCompiled] at core
      change some (Except.ok [.localGet result, .ret]) =
        some (Except.ok symbolic) at core
      injection core with symbolicEq
      injection symbolicEq with symbolicEq
      subst symbolic
      obtain ⟨alignedIndex, alignedFound, kindAt⟩ :=
        localsAligned localCompiled
      simp only [instructions, instruction] at targetCompiled
      change
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            result =
          some alignedIndex at alignedFound
      rw [alignedFound] at targetCompiled
      simp at targetCompiled
      have targetEq : [.localGet alignedIndex, .ret] = target :=
        Except.ok.inj targetCompiled
      subst target
      exact ⟨kind, alignedIndex, localCompiled, alignedFound, kindAt, rfl⟩

/--
Inversion of the real two-stage compiler at an arbitrary direct `let`.

Successful whole-body compilation determines separately compiled and adapted
value and continuation fragments, together with the adapter-selected numeric
destination local. This is the inverse of `codeAdapted_let`; it exposes facts
computed by the executable compiler and adapter rather than asking clients for
a syntax-directed translation certificate.
-/
theorem CodeAdapted.let_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ valueCode restCode targetValue targetRest resultIndex,
      Fir.Wasm.compileLetValue context decl = .ok valueCode ∧
        Fir.Wasm.compileCode context continuation = .ok restCode ∧
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue ∧
        instructions sourceModule sourceFunction labels restCode =
          .ok targetRest ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        target = targetValue ++ .localSet resultIndex :: targetRest := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases valueResult : Fir.Wasm.compileLetValue context decl with
  | error error =>
      rw [valueResult] at core
      change some (Except.error error) = some (Except.ok symbolic) at core
      have impossible :
          Except.error error = Except.ok symbolic :=
        Option.some.inj core
      cases impossible
  | ok valueCode =>
      rw [valueResult] at core
      cases restResult :
          Fir.Wasm.compileCodeCore context continuation with
      | none =>
          rw [restResult] at core
          change none = some (Except.ok symbolic) at core
          cases core
      | some result =>
          cases result with
          | error error =>
              rw [restResult] at core
              change
                some (Except.error error) = some (Except.ok symbolic) at core
              have impossible :
                  Except.error error = Except.ok symbolic :=
                Option.some.inj core
              cases impossible
          | ok restCode =>
              rw [restResult] at core
              change
                some (Except.ok
                  (valueCode ++ [.localSet decl.fvarId] ++ restCode)) =
                    some (Except.ok symbolic) at core
              injection core with symbolicEq
              injection symbolicEq with symbolicEq
              subst symbolic
              have restCompiled :
                  Fir.Wasm.compileCode context continuation =
                    .ok restCode :=
                Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
              simp only [List.append_assoc] at targetCompiled
              cases valueAdapted :
                  instructions sourceModule sourceFunction labels valueCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append,
                    valueAdapted] at targetCompiled
                  change Except.error error = Except.ok target at targetCompiled
                  cases targetCompiled
              | ok targetValue =>
                  rw [FirTalos.Correctness.instructions_append,
                    valueAdapted] at targetCompiled
                  cases resultFound :
                      findFVar? (functionBindings sourceFunction) decl.fvarId with
                  | none =>
                      change
                        findFVar?
                            (sourceFunction.params.toList ++
                              sourceFunction.locals.toList)
                            decl.fvarId = none at resultFound
                      simp [instructions, instruction, resultFound]
                        at targetCompiled
                      change
                        Except.error (AdapterError.unknownLocal decl.fvarId) =
                          Except.ok target at targetCompiled
                      cases targetCompiled
                  | some resultIndex =>
                      change
                        findFVar?
                            (sourceFunction.params.toList ++
                              sourceFunction.locals.toList)
                            decl.fvarId = some resultIndex at resultFound
                      cases restAdapted :
                          instructions sourceModule sourceFunction labels
                            restCode with
                      | error error =>
                          simp [instructions, instruction, resultFound,
                            restAdapted] at targetCompiled
                          change
                            Except.error error = Except.ok target
                              at targetCompiled
                          cases targetCompiled
                      | ok targetRest =>
                          have targetEq :
                              targetValue ++ .localSet resultIndex :: targetRest =
                                target := by
                            simp [instructions, instruction, resultFound,
                              restAdapted] at targetCompiled
                            change
                              Except.ok
                                  (targetValue ++
                                    .localSet resultIndex :: targetRest) =
                                Except.ok target at targetCompiled
                            exact Except.ok.inj targetCompiled
                          exact ⟨valueCode, restCode, targetValue, targetRest,
                            resultIndex, rfl, restCompiled, valueAdapted,
                            restAdapted, rfl, targetEq.symm⟩

/-- Invert one successful adapter sequence step. -/
theorem instructions_cons_eq_ok
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {head : Fir.Wasm.Instruction}
    {rest : List Fir.Wasm.Instruction} {target : Wasm.Program}
    (adapted :
      instructions sourceModule sourceFunction labels (head :: rest) =
        .ok target) :
    ∃ targetHead targetRest,
      instruction sourceModule sourceFunction labels head = .ok targetHead ∧
        instructions sourceModule sourceFunction labels rest =
          .ok targetRest ∧
        target = targetHead :: targetRest := by
  cases headAdapted :
      instruction sourceModule sourceFunction labels head with
  | error error =>
      have impossible :
          Except.error error = Except.ok target := by
        simpa [instructions, headAdapted, pure, Except.pure, Bind.bind,
          Except.bind] using adapted
      cases impossible
  | ok targetHead =>
      cases restAdapted :
          instructions sourceModule sourceFunction labels rest with
      | error error =>
          have impossible :
              Except.error error = Except.ok target := by
            simpa [instructions, headAdapted, restAdapted, pure, Except.pure,
              Bind.bind, Except.bind] using adapted
          cases impossible
      | ok targetRest =>
          have targetEq : targetHead :: targetRest = target := by
            simpa [instructions, headAdapted, restAdapted, pure, Except.pure,
              Bind.bind, Except.bind] using adapted
          exact ⟨targetHead, targetRest, rfl, rfl, targetEq.symm⟩

/--
Syntax-directed characterization of the argument code and ABI kinds emitted
by `compileArg`.  The relation is deliberately independent of target
numbering: numeric locals are fixed later by successful Talos adaptation.
-/
inductive ConstructorArgsCompiled (context : Fir.Wasm.Context) :
    List (LCNF.Arg .impure) → List Fir.Wasm.Instruction →
      List AbiKind → Prop where
  | nil : ConstructorArgsCompiled context [] [] []
  | erased
      (rest : ConstructorArgsCompiled context args argumentCode fieldKinds) :
      ConstructorArgsCompiled context (.erased :: args)
        (.i32Const .erased 0 :: argumentCode) (.erased :: fieldKinds)
  | fvar
      (kindFound :
        Fir.Wasm.findLocalKind? context.localKinds fvarId = some kind)
      (rest : ConstructorArgsCompiled context args argumentCode fieldKinds) :
      ConstructorArgsCompiled context (.fvar fvarId :: args)
        (.localGet fvarId :: argumentCode) (kind :: fieldKinds)

theorem ConstructorArgsCompiled.append
    {context : Fir.Wasm.Context}
    {leftArgs rightArgs : List (LCNF.Arg .impure)}
    {leftCode rightCode : List Fir.Wasm.Instruction}
    {leftKinds rightKinds : List AbiKind}
    (left :
      ConstructorArgsCompiled context leftArgs leftCode leftKinds)
    (right :
      ConstructorArgsCompiled context rightArgs rightCode rightKinds) :
    ConstructorArgsCompiled context (leftArgs ++ rightArgs)
      (leftCode ++ rightCode) (leftKinds ++ rightKinds) := by
  induction left with
  | nil =>
      simpa using right
  | erased rest ih =>
      simpa [List.append_assoc] using
        ConstructorArgsCompiled.erased ih
  | fvar kindFound rest ih =>
      simpa [List.append_assoc] using
        ConstructorArgsCompiled.fvar kindFound ih

private theorem constructorArgsCompiled_of_foldlM
    {context : Fir.Wasm.Context}
    {prefixArgs remaining : List (LCNF.Arg .impure)}
    {prefixCode argumentCode : List Fir.Wasm.Instruction}
    {prefixKinds fieldKinds : Array AbiKind}
    (prefixReady :
      ConstructorArgsCompiled context prefixArgs prefixCode
        prefixKinds.toList)
    (compiled :
      remaining.foldlM (init := (prefixCode, prefixKinds))
          (fun (instructions, kinds) arg => do
            let (argument, kind) ← Fir.Wasm.compileArg context arg
            return (instructions ++ argument, kinds.push kind)) =
        .ok (argumentCode, fieldKinds)) :
    ConstructorArgsCompiled context (prefixArgs ++ remaining) argumentCode
      fieldKinds.toList := by
  induction remaining generalizing prefixArgs prefixCode prefixKinds with
  | nil =>
      simp only [List.foldlM_nil] at compiled
      change
        Except.ok (prefixCode, prefixKinds) =
          Except.ok (argumentCode, fieldKinds) at compiled
      have pairEq :
          (prefixCode, prefixKinds) = (argumentCode, fieldKinds) :=
        Except.ok.inj compiled
      injection pairEq with codeEq kindsEq
      subst argumentCode
      subst fieldKinds
      simpa using prefixReady
  | cons arg remaining ih =>
      cases arg with
      | erased =>
          have singleton :
              ConstructorArgsCompiled context [.erased]
                [.i32Const .erased 0] [.erased] :=
            .erased .nil
          have nextPrefix :
              ConstructorArgsCompiled context
                (prefixArgs ++ [.erased])
                (prefixCode ++ [.i32Const .erased 0])
                (prefixKinds.push .erased).toList := by
            simpa using prefixReady.append singleton
          have remainingCompiled :
              remaining.foldlM
                  (init :=
                    (prefixCode ++ [.i32Const .erased 0],
                      prefixKinds.push .erased))
                  (fun (instructions, kinds) arg => do
                    let (argument, kind) ← Fir.Wasm.compileArg context arg
                    return (instructions ++ argument, kinds.push kind)) =
                .ok (argumentCode, fieldKinds) := by
            simpa [Fir.Wasm.compileArg, Functor.map, Except.map, Bind.bind,
              Except.bind, pure, Except.pure] using compiled
          simpa [List.append_assoc] using ih nextPrefix remainingCompiled
      | fvar fvarId =>
          cases kindFound :
              Fir.Wasm.findLocalKind? context.localKinds fvarId with
          | none =>
              simp [Fir.Wasm.compileArg, kindFound, Functor.map, Except.map,
                Bind.bind, Except.bind, pure, Except.pure] at compiled
          | some kind =>
              have singleton :
                  ConstructorArgsCompiled context [.fvar fvarId]
                    [.localGet fvarId] [kind] :=
                .fvar kindFound .nil
              have nextPrefix :
                  ConstructorArgsCompiled context
                    (prefixArgs ++ [.fvar fvarId])
                    (prefixCode ++ [.localGet fvarId])
                    (prefixKinds.push kind).toList := by
                simpa using prefixReady.append singleton
              have remainingCompiled :
                  remaining.foldlM
                      (init :=
                        (prefixCode ++ [.localGet fvarId],
                          prefixKinds.push kind))
                      (fun (instructions, kinds) arg => do
                        let (argument, kind) ← Fir.Wasm.compileArg context arg
                        return (instructions ++ argument, kinds.push kind)) =
                    .ok (argumentCode, fieldKinds) := by
                simpa [Fir.Wasm.compileArg, kindFound, Functor.map, Except.map,
                  Bind.bind, Except.bind, pure, Except.pure] using compiled
              simpa [List.append_assoc] using ih nextPrefix remainingCompiled
      | type expr impossible =>
          exact nomatch impossible

/--
Successful production `compileArgs` is characterized by
`ConstructorArgsCompiled`; no parallel argument compiler is trusted.
-/
theorem ConstructorArgsCompiled.ofCompileArgs
    {context : Fir.Wasm.Context}
    {args : Array (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind}
    (compiled :
      Fir.Wasm.compileArgs context args = .ok (argumentCode, fieldKinds)) :
    ConstructorArgsCompiled context args.toList argumentCode
      fieldKinds.toList := by
  apply constructorArgsCompiled_of_foldlM
    (prefixArgs := []) (prefixCode := []) (prefixKinds := #[]) .nil
  unfold Fir.Wasm.compileArgs at compiled
  rw [← Array.foldlM_toList] at compiled
  exact compiled

/--
Compiler-characterized source arguments, successful source evaluation, the
real adapter, and the concrete state relation determine an executable mixed
constructor prefix.  In particular, an erased source field contributes the
canonical physical zero without requiring a source local.
-/
theorem ConstructorArgsCompiled.ready
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {args : List (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : List AbiKind}
    {targetArguments : Wasm.Program}
    {semanticArgs : List Value}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    (compiled :
      ConstructorArgsCompiled context args argumentCode fieldKinds)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (adapted :
      instructions sourceModule sourceFunction labels argumentCode =
        .ok targetArguments)
    (evaluated : args.mapM (evalArg sourceEnv) = .ok semanticArgs)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        witness) :
    ∃ physicalArgs,
      ConstructorArgsReady locals targetArguments physicalArgs ∧
        physicalArgs.length = fieldKinds.length := by
  induction compiled generalizing targetArguments semanticArgs with
  | nil =>
      have targetEq : targetArguments = [] := by
        simpa [instructions, pure, Except.pure] using adapted.symm
      subst targetArguments
      exact ⟨[], .nil, rfl⟩
  | @erased args argumentCode fieldKinds rest ih =>
      obtain ⟨targetHead, targetRest, headAdapted, restAdapted, targetEq⟩ :=
        instructions_cons_eq_ok adapted
      have targetHeadEq : targetHead = .const 0 := by
        simpa [instruction, pure, Except.pure] using headAdapted.symm
      cases restEvaluated :
          _root_.List.mapM (evalArg sourceEnv) args with
      | error fault =>
          rw [List.mapM_cons] at evaluated
          simp only [evalArg, restEvaluated, Functor.map, Except.map,
            Bind.bind, Except.bind] at evaluated
          contradiction
      | ok restValues =>
          obtain ⟨physicalArgs, ready, lengthEq⟩ :=
            ih restAdapted restEvaluated
          subst targetHead
          subst targetArguments
          exact ⟨.i32 0 :: physicalArgs, .erased ready, by
            simp [lengthEq]⟩
  | @fvar fvarId kind args argumentCode fieldKinds kindFound rest ih =>
      obtain ⟨targetHead, targetRest, headAdapted, restAdapted, targetEq⟩ :=
        instructions_cons_eq_ok adapted
      cases sourceLookup : lookup sourceEnv fvarId with
      | none =>
          rw [List.mapM_cons] at evaluated
          simp only [evalArg, sourceLookup, Functor.map, Except.map,
            Bind.bind, Except.bind] at evaluated
          contradiction
      | some sourceValue =>
          cases restEvaluated :
              _root_.List.mapM (evalArg sourceEnv) args with
          | error fault =>
              rw [List.mapM_cons] at evaluated
              simp only [evalArg, sourceLookup, restEvaluated, Functor.map,
                Except.map, Bind.bind, Except.bind] at evaluated
              contradiction
          | ok restValues =>
              have localCompiled :
                  Fir.Wasm.getLocal context fvarId =
                    .ok (.localGet fvarId, kind) := by
                simp [Fir.Wasm.getLocal, kindFound]
              obtain ⟨index, localFound, kindAt⟩ :=
                localsAligned localCompiled
              have localFound' :
                  findFVar?
                      (sourceFunction.params.toList ++
                        sourceFunction.locals.toList)
                      fvarId = some index := by
                simpa [functionBindings] using localFound
              have targetHeadEq : targetHead = .localGet index := by
                have adaptedEq :
                    (Except.ok (.localGet index) :
                      Except AdapterError Wasm.Instruction) =
                      Except.ok targetHead := by
                  simpa [instruction, localFound', pure, Except.pure] using
                    headAdapted
                exact (Except.ok.inj adaptedEq).symm
              obtain ⟨physical, physicalFound, _⟩ :=
                stateRelated.resolve sourceLookup localFound kindAt
              obtain ⟨physicalArgs, ready, lengthEq⟩ :=
                ih restAdapted restEvaluated
              subst targetHead
              subst targetArguments
              exact ⟨physical :: physicalArgs,
                .localGet physicalFound ready, by simp [lengthEq]⟩

/--
Public array-facing corollary: the actual `compileArgs`, adapter, evaluator,
and state relation produce the exact mixed local/erased target prefix and its
physical arity.
-/
theorem constructorArgsReady_of_compileArgs
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {args : Array (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind}
    {targetArguments : Wasm.Program}
    {semanticArgs : Array Value}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (compiled :
      Fir.Wasm.compileArgs context args =
        .ok (argumentCode, fieldKinds))
    (adapted :
      instructions sourceModule sourceFunction labels argumentCode =
        .ok targetArguments)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        witness) :
    ∃ physicalArgs,
      ConstructorArgsReady locals targetArguments physicalArgs ∧
        physicalArgs.length = fieldKinds.size := by
  have characterized := ConstructorArgsCompiled.ofCompileArgs compiled
  unfold evalArgs at evaluated
  rw [Array.mapM_eq_mapM_toList] at evaluated
  cases listEvaluated :
      args.toList.mapM (evalArg sourceEnv) with
  | error fault =>
      rw [listEvaluated] at evaluated
      contradiction
  | ok semanticValues =>
      obtain ⟨physicalArgs, ready, lengthEq⟩ :=
        characterized.ready localsAligned adapted listEvaluated stateRelated
      exact ⟨physicalArgs, ready, by simpa using lengthEq⟩

/--
Invert adaptation of an arbitrary successfully compiled argument prefix
followed by one runtime call.
-/
theorem instructions_append_call_eq
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {argumentCode : List Fir.Wasm.Instruction}
    {operation : RuntimeOp} {target : Wasm.Program}
    (adapted :
      instructions sourceModule sourceFunction labels
          (argumentCode ++ [.call (.runtime operation)]) = .ok target) :
    ∃ targetArguments callIndex,
      instructions sourceModule sourceFunction labels argumentCode =
          .ok targetArguments ∧
        callIndex? sourceModule (.runtime operation) = some callIndex ∧
        target = targetArguments ++ [.call callIndex] := by
  cases argumentsAdapted :
      instructions sourceModule sourceFunction labels argumentCode with
  | error fault =>
      rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
        at adapted
      contradiction
  | ok targetArguments =>
      rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
        at adapted
      cases callFound :
          callIndex? sourceModule (.runtime operation) with
      | none =>
          have impossible :
              Except.error AdapterError.unknownCallTarget =
                Except.ok target := by
            simpa [instructions, instruction, callFound, Functor.map,
              Except.map, Bind.bind, Except.bind, pure, Except.pure] using
              adapted
          contradiction
      | some callIndex =>
          have adaptedEq :
              (Except.ok (targetArguments ++ [.call callIndex]) :
                Except AdapterError Wasm.Program) =
                Except.ok target := by
            simpa [instructions, instruction, callFound, Functor.map,
              Except.map, Bind.bind, Except.bind, pure, Except.pure] using
              adapted
          exact ⟨targetArguments, callIndex, rfl, rfl,
            (Except.ok.inj adaptedEq).symm⟩

/--
Invert adaptation of a symbolic local-get prefix followed by one runtime call.

This is the static converse of `instructions_localGets` needed by compiler
correctness: successful adaptation determines the numeric source-local slots
and runtime import slot used by the emitted target prefix.
-/
theorem instructions_localGets_call_eq
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {fvarIds : List FVarId}
    {operation : RuntimeOp} {target : Wasm.Program}
    (adapted :
      instructions sourceModule sourceFunction labels
          (fvarIds.map Fir.Wasm.Instruction.localGet ++
            [.call (.runtime operation)]) = .ok target) :
    ∃ indices callIndex,
      List.Forall₂
          (fun fvarId index =>
            findFVar? (functionBindings sourceFunction) fvarId = some index)
          fvarIds indices ∧
        callIndex? sourceModule (.runtime operation) = some callIndex ∧
        target =
          indices.map Wasm.Instruction.localGet ++ [.call callIndex] := by
  induction fvarIds generalizing target with
  | nil =>
      obtain ⟨targetHead, targetRest, headAdapted, restAdapted, targetEq⟩ :=
        instructions_cons_eq_ok adapted
      have targetRestEq : targetRest = [] := by
        simpa [instructions, pure, Except.pure, Bind.bind, Except.bind] using
          restAdapted.symm
      cases callFound : callIndex? sourceModule (.runtime operation) with
      | none =>
          have impossible :
              Except.error AdapterError.unknownCallTarget =
                Except.ok targetHead := by
            simpa [instruction, callFound, pure, Except.pure, Bind.bind,
              Except.bind] using headAdapted
          cases impossible
      | some callIndex =>
          have targetHeadEq : targetHead = .call callIndex := by
            simpa [instruction, callFound, pure, Except.pure, Bind.bind,
              Except.bind] using headAdapted.symm
          exact ⟨[], callIndex, .nil, rfl, by
            simp [targetEq, targetHeadEq, targetRestEq]⟩
  | cons fvarId rest ih =>
      obtain ⟨targetHead, targetRest, headAdapted, restAdapted, targetEq⟩ :=
        instructions_cons_eq_ok adapted
      cases localFound :
          findFVar? (functionBindings sourceFunction) fvarId with
      | none =>
          have localFound' :
              findFVar?
                  (sourceFunction.params.toList ++
                    sourceFunction.locals.toList)
                  fvarId = none := by
            simpa [functionBindings] using localFound
          have impossible :
              Except.error (AdapterError.unknownLocal fvarId) =
                Except.ok targetHead := by
            simpa [instruction, localFound', pure,
              Except.pure, Bind.bind, Except.bind] using headAdapted
          cases impossible
      | some index =>
          have localFound' :
              findFVar?
                  (sourceFunction.params.toList ++
                    sourceFunction.locals.toList)
                  fvarId = some index := by
            simpa [functionBindings] using localFound
          have targetHeadEq : targetHead = .localGet index := by
            simpa [instruction, localFound', pure,
              Except.pure, Bind.bind, Except.bind] using headAdapted.symm
          obtain ⟨indices, callIndex, found, callFound, restEq⟩ :=
            ih restAdapted
          exact ⟨index :: indices, callIndex, .cons localFound found,
            callFound, by simp [targetEq, targetHeadEq, restEq]⟩

/--
Natural-literal specialization of `CodeAdapted.let_eq` with an arbitrary
continuation.

Besides splitting the continuation out of the real compiler output, this
specialization resolves the literal host call and proves that the adapter's
numeric destination has the expected `tobject` kind.
-/
theorem CodeAdapted.naturalLiteralLet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {value : Nat}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .lit (.nat value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .tobject))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ callIndex resultIndex targetRest,
      Fir.Wasm.compileLetValue context decl =
          .ok [.call (.runtime (.literal (.nat value) .tobject))] ∧
        callIndex? sourceModule
            (.runtime (.literal (.nat value) .tobject)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some .tobject ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target = .call callIndex :: .localSet resultIndex :: targetRest := by
  have literalCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.call (.runtime (.literal (.nat value) .tobject))] :=
    compileLetValue_naturalLiteral valueEq valueKind
  obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
      valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
      targetEq⟩ :=
    CodeAdapted.let_eq adapted
  rw [literalCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨alignedIndex, alignedFound, resultKindAt⟩ :=
    localsAligned localCompiled
  rw [resultFound] at alignedFound
  injection alignedFound with indexEq
  subst alignedIndex
  cases callFound :
      callIndex? sourceModule
        (.runtime (.literal (.nat value) .tobject)) with
  | none =>
      simp [instructions, instruction, callFound] at valueAdapted
      change
        Except.error AdapterError.unknownCallTarget =
          Except.ok targetValue at valueAdapted
      cases valueAdapted
  | some callIndex =>
      have targetValueEq : [.call callIndex] = targetValue := by
        simp [instructions, instruction, callFound] at valueAdapted
        exact Except.ok.inj valueAdapted
      subst targetValue
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      exact ⟨callIndex, resultIndex, targetRest, literalCompiled, rfl,
        resultFound, resultKindAt, continuationAdapted, by
          simpa using targetEq⟩

/--
UTF-8 String-literal specialization of `CodeAdapted.let_eq` with an arbitrary
continuation.

The executable compiler fixes the `.object` result lane and symbolic String
host call; successful adaptation fixes the numeric import and destination
local while retaining the independently compiled continuation.
-/
theorem CodeAdapted.stringLiteralLet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {value : String}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .lit (.str value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .object)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ callIndex resultIndex targetRest,
      Fir.Wasm.compileLetValue context decl =
          .ok [.call (.runtime (.literal (.str value) .object))] ∧
        callIndex? sourceModule
            (.runtime (.literal (.str value) .object)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some .object ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target = .call callIndex :: .localSet resultIndex :: targetRest := by
  have literalCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.call (.runtime (.literal (.str value) .object))] :=
    compileLetValue_stringLiteral valueEq valueKind
  obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
      valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
      targetEq⟩ :=
    CodeAdapted.let_eq adapted
  rw [literalCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨alignedIndex, alignedFound, resultKindAt⟩ :=
    localsAligned localCompiled
  rw [resultFound] at alignedFound
  injection alignedFound with indexEq
  subst alignedIndex
  cases callFound :
      callIndex? sourceModule
        (.runtime (.literal (.str value) .object)) with
  | none =>
      simp [instructions, instruction, callFound] at valueAdapted
      change
        Except.error AdapterError.unknownCallTarget =
          Except.ok targetValue at valueAdapted
      cases valueAdapted
  | some callIndex =>
      have targetValueEq : [.call callIndex] = targetValue := by
        simp [instructions, instruction, callFound] at valueAdapted
        exact Except.ok.inj valueAdapted
      subst targetValue
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      exact ⟨callIndex, resultIndex, targetRest, literalCompiled, rfl,
        resultFound, resultKindAt, continuationAdapted, by
          simpa using targetEq⟩

/--
Constructor-allocation inversion for the complete `compileArgs` language.
The argument prefix may freely mix compiler-resolved locals and erased
constants; successful whole-body adaptation determines its exact target
instructions, constructor import, destination local, and continuation.
-/
theorem CodeAdapted.constructorLet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (argumentCode, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ targetArguments callIndex resultIndex targetRest,
      Fir.Wasm.compileLetValue context decl =
          .ok (argumentCode ++ [.call (.runtime
            (.allocCtor info fieldKinds resultKind))]) ∧
        instructions sourceModule sourceFunction labels argumentCode =
          .ok targetArguments ∧
        callIndex? sourceModule
            (.runtime (.allocCtor info fieldKinds resultKind)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some resultKind ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          targetArguments ++
            .call callIndex :: .localSet resultIndex :: targetRest := by
  have constructorCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (argumentCode ++ [.call (.runtime
          (.allocCtor info fieldKinds resultKind))]) :=
    compileLetValue_constructor valueEq fits valueKind argumentsCompiled
  obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
      valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
      targetEq⟩ :=
    CodeAdapted.let_eq adapted
  rw [constructorCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨alignedIndex, alignedFound, resultKindAt⟩ :=
    localsAligned localCompiled
  rw [resultFound] at alignedFound
  injection alignedFound with indexEq
  subst alignedIndex
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_call_eq valueAdapted
  subst targetValue
  have continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest :=
    ⟨restCode, restCompiled, restAdapted⟩
  exact ⟨targetArguments, callIndex, resultIndex, targetRest,
    constructorCompiled, argumentsAdapted, callFound, resultFound,
    resultKindAt, continuationAdapted, by
      simpa [List.append_assoc] using targetEq⟩

/--
Constructor-allocation specialization for the current all-`fvar` field
boundary and an arbitrary continuation.

The `compileArgs` premise is a compiler equation, not a target certificate.
Together with successful whole-body adaptation it determines every numeric
argument slot, the constructor import, the destination local, and the
independently compiled continuation.
-/
theorem CodeAdapted.constructorFVarLet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {fvarIds : List FVarId}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (fvarIds.map Fir.Wasm.Instruction.localGet, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ indices callIndex resultIndex targetRest,
      Fir.Wasm.compileLetValue context decl =
          .ok (fvarIds.map Fir.Wasm.Instruction.localGet ++
            [.call (.runtime
              (.allocCtor info fieldKinds resultKind))]) ∧
        List.Forall₂
            (fun fvarId index =>
              findFVar? (functionBindings sourceFunction) fvarId =
                some index)
            fvarIds indices ∧
        callIndex? sourceModule
            (.runtime (.allocCtor info fieldKinds resultKind)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some resultKind ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          indices.map Wasm.Instruction.localGet ++
            .call callIndex :: .localSet resultIndex :: targetRest := by
  have constructorCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (fvarIds.map Fir.Wasm.Instruction.localGet ++
          [.call (.runtime (.allocCtor info fieldKinds resultKind))]) :=
    compileLetValue_constructor valueEq fits valueKind argumentsCompiled
  obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
      valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
      targetEq⟩ :=
    CodeAdapted.let_eq adapted
  rw [constructorCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨alignedIndex, alignedFound, resultKindAt⟩ :=
    localsAligned localCompiled
  rw [resultFound] at alignedFound
  injection alignedFound with indexEq
  subst alignedIndex
  obtain ⟨indices, callIndex, argumentsFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq valueAdapted
  subst targetValue
  have continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest :=
    ⟨restCode, restCompiled, restAdapted⟩
  exact ⟨indices, callIndex, resultIndex, targetRest, constructorCompiled,
    argumentsFound, callFound, resultFound, resultKindAt,
    continuationAdapted, by simpa [List.append_assoc] using targetEq⟩

/--
Inversion of the real compiler and adapter for a natural-literal binding that
is returned immediately.

The source annotation and local-kind premises describe the supported
`tobject` lane. The numeric import/local indices and the complete target body
are consequences of the executable compiler pipeline.
-/
theorem CodeAdapted.naturalLiteralReturn_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {value : Nat}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .lit (.nat value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .tobject))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl (.return decl.fvarId)) target) :
    ∃ callIndex resultIndex,
      Fir.Wasm.compileLetValue context decl =
          .ok [.call (.runtime (.literal (.nat value) .tobject))] ∧
        callIndex? sourceModule
            (.runtime (.literal (.nat value) .tobject)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some .tobject ∧
        target = [
          .call callIndex,
          .localSet resultIndex,
          .localGet resultIndex,
          .ret] := by
  obtain ⟨callIndex, resultIndex, targetRest, valueCompiled, callFound,
      resultFound, resultKindAt, continuationAdapted, targetEq⟩ :=
    CodeAdapted.naturalLiteralLet_eq localsAligned valueEq valueKind
      localCompiled adapted
  obtain ⟨returnKind, returnIndex, returnCompiled, returnFound, _,
      returnEq⟩ :=
    CodeAdapted.return_eq localsAligned continuationAdapted
  rw [localCompiled] at returnCompiled
  injection returnCompiled with kindEq
  injection kindEq with kindEq
  subst returnKind
  rw [resultFound] at returnFound
  injection returnFound with indexEq
  subst returnIndex
  rw [returnEq] at targetEq
  exact ⟨callIndex, resultIndex, valueCompiled, callFound, resultFound,
    resultKindAt, by simpa using targetEq⟩

/--
Immediate-return corollary of the general UTF-8 String direct-`let`
inversion.
-/
theorem CodeAdapted.stringLiteralReturn_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {value : String}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .lit (.str value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .object)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl (.return decl.fvarId)) target) :
    ∃ callIndex resultIndex,
      Fir.Wasm.compileLetValue context decl =
          .ok [.call (.runtime (.literal (.str value) .object))] ∧
        callIndex? sourceModule
            (.runtime (.literal (.str value) .object)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some .object ∧
        target = [
          .call callIndex,
          .localSet resultIndex,
          .localGet resultIndex,
          .ret] := by
  obtain ⟨callIndex, resultIndex, targetRest, valueCompiled, callFound,
      resultFound, resultKindAt, continuationAdapted, targetEq⟩ :=
    CodeAdapted.stringLiteralLet_eq localsAligned valueEq valueKind
      localCompiled adapted
  obtain ⟨returnKind, returnIndex, returnCompiled, returnFound, _,
      returnEq⟩ :=
    CodeAdapted.return_eq localsAligned continuationAdapted
  rw [localCompiled] at returnCompiled
  injection returnCompiled with kindEq
  injection kindEq with kindEq
  subst returnKind
  rw [resultFound] at returnFound
  injection returnFound with indexEq
  subst returnIndex
  rw [returnEq] at targetEq
  exact ⟨callIndex, resultIndex, valueCompiled, callFound, resultFound,
    resultKindAt, by simpa using targetEq⟩

/-- Immediate-return corollary of the mixed constructor inversion. -/
theorem CodeAdapted.constructorReturn_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (argumentCode, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl (.return decl.fvarId)) target) :
    ∃ targetArguments callIndex resultIndex,
      Fir.Wasm.compileLetValue context decl =
          .ok (argumentCode ++ [.call (.runtime
            (.allocCtor info fieldKinds resultKind))]) ∧
        instructions sourceModule sourceFunction labels argumentCode =
          .ok targetArguments ∧
        callIndex? sourceModule
            (.runtime (.allocCtor info fieldKinds resultKind)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some resultKind ∧
        target =
          targetArguments ++ [
            .call callIndex,
            .localSet resultIndex,
            .localGet resultIndex,
            .ret] := by
  obtain ⟨targetArguments, callIndex, resultIndex, targetRest, valueCompiled,
      argumentsAdapted, callFound, resultFound, resultKindAt,
      continuationAdapted, targetEq⟩ :=
    CodeAdapted.constructorLet_eq localsAligned valueEq fits valueKind
      argumentsCompiled localCompiled adapted
  obtain ⟨returnKind, returnIndex, returnCompiled, returnFound, _, returnEq⟩ :=
    CodeAdapted.return_eq localsAligned continuationAdapted
  rw [localCompiled] at returnCompiled
  injection returnCompiled with kindEq
  injection kindEq with kindEq
  subst returnKind
  rw [resultFound] at returnFound
  injection returnFound with indexEq
  subst returnIndex
  rw [returnEq] at targetEq
  exact ⟨targetArguments, callIndex, resultIndex, valueCompiled,
    argumentsAdapted, callFound, resultFound, resultKindAt, by
      simpa [List.append_assoc] using targetEq⟩

/-- Immediate-return corollary of the all-`fvar` constructor inversion. -/
theorem CodeAdapted.constructorFVarReturn_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {fvarIds : List FVarId}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (fvarIds.map Fir.Wasm.Instruction.localGet, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl (.return decl.fvarId)) target) :
    ∃ indices callIndex resultIndex,
      Fir.Wasm.compileLetValue context decl =
          .ok (fvarIds.map Fir.Wasm.Instruction.localGet ++
            [.call (.runtime
              (.allocCtor info fieldKinds resultKind))]) ∧
        List.Forall₂
            (fun fvarId index =>
              findFVar? (functionBindings sourceFunction) fvarId =
                some index)
            fvarIds indices ∧
        callIndex? sourceModule
            (.runtime (.allocCtor info fieldKinds resultKind)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some resultKind ∧
        target =
          indices.map Wasm.Instruction.localGet ++ [
            .call callIndex,
            .localSet resultIndex,
            .localGet resultIndex,
            .ret] := by
  obtain ⟨indices, callIndex, resultIndex, targetRest, valueCompiled,
      argumentsFound, callFound, resultFound, resultKindAt,
      continuationAdapted, targetEq⟩ :=
    CodeAdapted.constructorFVarLet_eq localsAligned valueEq fits valueKind
      argumentsCompiled localCompiled adapted
  obtain ⟨returnKind, returnIndex, returnCompiled, returnFound, _, returnEq⟩ :=
    CodeAdapted.return_eq localsAligned continuationAdapted
  rw [localCompiled] at returnCompiled
  injection returnCompiled with kindEq
  injection kindEq with kindEq
  subst returnKind
  rw [resultFound] at returnFound
  injection returnFound with indexEq
  subst returnIndex
  rw [returnEq] at targetEq
  exact ⟨indices, callIndex, resultIndex, valueCompiled, argumentsFound,
    callFound, resultFound, resultKindAt, by
      simpa [List.append_assoc] using targetEq⟩

/--
Certificate-free recursive correctness rule for a natural-literal `let` with
an arbitrary continuation.

The `continued` premise is the semantic induction hypothesis for the
continuation selected by the executable compiler/adaptor equation. It is not a
translation witness: this theorem derives the literal instruction, import
index, destination local, target split, and concrete host contract from
`ConcreteSupportedExport`.
-/
theorem ConcreteSupportedExport.codeWP_naturalLiteralLet
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {value : Nat}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .lit (.nat value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .tobject))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    {heap : MemoryState}
    {word : Word32}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (allocated :
      allocateNatural initial.host.runtime.heap value = .ok (heap, word))
    (localSetReady :
      ∀ {resultIndex},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated)
    (continued :
      ∀ {targetRest resultIndex updated nextWitness},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated →
          witness.Extends nextWitness →
          ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
              (literal sourceRuntime (.nat value)).1 →
          PhysicalValueRel nextWitness .tobject
              (.i32 (UInt32.ofNat word.value))
              (literal sourceRuntime (.nat value)).2 →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env (literal sourceRuntime (.nat value)).1
            (bind sourceEnv decl.fvarId
              (literal sourceRuntime (.nat value)).2)
            continuation targetRest (replaceHeap initial heap) updated
            nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q := by
  obtain ⟨callIndex, resultIndex, targetRest, valueCompiled, callFound,
      resultFound, resultKindAt, continuationAdapted, bodyEq⟩ :=
    CodeAdapted.naturalLiteralLet_eq spec.localsAligned valueEq valueKind
      localCompiled spec.bodyAdapted
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.naturalLiteralCall callFound
  rw [bodyEq]
  apply codeWP_naturalLiteral_let valueEq valueCompiled callFound stateRelated
    resultFound resultKindAt allocated imported spec.hostsSatisfy inBounds
    contracted params results targetSet
  intro nextWitness extension nextRuntimeRelated valueRelated
  exact continued continuationAdapted resultFound targetSet extension
    nextRuntimeRelated valueRelated

/--
Certificate-free recursive correctness rule for a UTF-8 String-literal `let`
with an arbitrary compiler-selected continuation.

As in the natural-literal rule, the recursive premise is continuation
correctness. Compiler output, target splitting, import/local numbering, and
the concrete host contract are all derived from `ConcreteSupportedExport`.
-/
theorem ConcreteSupportedExport.codeWP_stringLiteralLet
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {value : String}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .lit (.str value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .object)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    {heap : MemoryState}
    {word : Word32}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (allocated :
      allocateString initial.host.runtime.heap value = .ok (heap, word))
    (localSetReady :
      ∀ {resultIndex},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated)
    (continued :
      ∀ {targetRest resultIndex updated nextWitness},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated →
          witness.Extends nextWitness →
          ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
              (literal sourceRuntime (.str value)).1 →
          PhysicalValueRel nextWitness .object
              (.i32 (UInt32.ofNat word.value))
              (literal sourceRuntime (.str value)).2 →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env (literal sourceRuntime (.str value)).1
            (bind sourceEnv decl.fvarId
              (literal sourceRuntime (.str value)).2)
            continuation targetRest (replaceHeap initial heap) updated
            nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q := by
  obtain ⟨callIndex, resultIndex, targetRest, valueCompiled, callFound,
      resultFound, resultKindAt, continuationAdapted, bodyEq⟩ :=
    CodeAdapted.stringLiteralLet_eq spec.localsAligned valueEq valueKind
      localCompiled spec.bodyAdapted
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.stringLiteralCall callFound
  rw [bodyEq]
  apply codeWP_stringLiteral_let valueEq valueCompiled callFound stateRelated
    resultFound resultKindAt allocated imported spec.hostsSatisfy inBounds
    contracted params results targetSet
  intro nextWitness extension nextRuntimeRelated valueRelated
  exact continued continuationAdapted resultFound targetSet extension
    nextRuntimeRelated valueRelated

/--
Certificate-free recursive correctness for the complete constructor argument
language.  The compiler, adapter, source evaluator, and state relation derive
the physical local/erased prefix.  The caller supplies only the
operation-specific concrete allocation refinement for whichever physical
operands that derivation produces.
-/
theorem ConcreteSupportedExport.codeWP_constructorLet
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (argumentCode, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {semanticArgs : Array Value}
    {sourceValue : Value}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (concreteStep :
      ∀ {physicalArgs},
        physicalArgs.length = fieldKinds.size →
          ∃ (nextStore : Wasm.Store Host) (word : Word32)
              (nextWitness : RefinementWitness),
            allocCtorStep info fieldKinds resultKind initial physicalArgs =
                .Return [.i32 (UInt32.ofNat word.value)] nextStore ∧
              witness.Extends nextWitness ∧
              ConcreteRuntimeRel nextStore.host.runtime nextWitness
                nextRuntime ∧
              nextStore.host.failure? = none ∧
              PhysicalValueRel nextWitness resultKind
                (.i32 (UInt32.ofNat word.value)) sourceValue)
    (localSetReady :
      ∀ {resultIndex : Nat} {word : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated)
    (continued :
      ∀ {targetRest : Wasm.Program} {resultIndex : Nat}
          {nextStore : Wasm.Store Host} {word : Word32}
          {nextWitness : RefinementWitness} {updated : Wasm.Locals},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
            some updated →
          witness.Extends nextWitness →
          ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime →
          nextStore.host.failure? = none →
          PhysicalValueRel nextWitness resultKind
              (.i32 (UInt32.ofNat word.value)) sourceValue →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env nextRuntime (bind sourceEnv decl.fvarId sourceValue)
            continuation targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q := by
  obtain ⟨targetArguments, callIndex, resultIndex, targetRest, valueCompiled,
      argumentsAdapted, callFound, resultFound, resultKindAt,
      continuationAdapted, bodyEq⟩ :=
    CodeAdapted.constructorLet_eq spec.localsAligned valueEq fits valueKind
      argumentsCompiled localCompiled spec.bodyAdapted
  obtain ⟨physicalArgs, argumentsReady, physicalArity⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      argumentsAdapted evaluated stateRelated
  obtain ⟨nextStore, word, nextWitness, operation, extension,
      nextRuntimeRelated, failureClear, valueRelated⟩ :=
    concreteStep physicalArity
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.allocCtorCall callFound
  have physicalParams : imp.params.length = physicalArgs.length :=
    params.trans physicalArity.symm
  rw [bodyEq]
  apply codeWP_constructorArgs_let valueEq valueCompiled argumentsAdapted
    callFound evaluated semanticStep stateRelated resultFound resultKindAt
    argumentsReady imported spec.hostsSatisfy inBounds contracted
    physicalParams results operation extension nextRuntimeRelated failureClear
    valueRelated targetSet
  exact continued continuationAdapted resultFound targetSet extension
    nextRuntimeRelated failureClear valueRelated

/--
Certificate-free recursive correctness for an all-`fvar` constructor
allocation followed by an arbitrary compiler-selected continuation.

Compiler and adapter inversion derive the argument/import/local indices and
target split. The remaining premises are execution facts: source argument and
allocation success, the matching concrete allocation/refinement, physical
argument/local readiness, destination capacity, and correctness of the
continuation under the extended witness.
-/
theorem ConcreteSupportedExport.codeWP_constructorFVarLet
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {fvarIds : List FVarId}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (fvarIds.map Fir.Wasm.Instruction.localGet, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host}
    {locals : Wasm.Locals}
    {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value}
    {sourceValue : Value}
    {word : Word32}
    {witness nextWitness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (argumentsReady :
      ∀ {indices},
        List.Forall₂
            (fun fvarId index =>
              findFVar? (functionBindings sourceFunction) fvarId =
                some index)
            fvarIds indices →
          List.Forall₂
            (fun index physical => locals.get index = some physical)
            indices physicalArgs)
    (physicalArity : physicalArgs.length = fieldKinds.size)
    (operation :
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (valueRelated :
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat word.value)) sourceValue)
    (localSetReady :
      ∀ {resultIndex},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated)
    (continued :
      ∀ {targetRest resultIndex updated},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
            some updated →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env nextRuntime (bind sourceEnv decl.fvarId sourceValue)
            continuation targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q := by
  obtain ⟨indices, callIndex, resultIndex, targetRest, valueCompiled,
      argumentsFound, callFound, resultFound, resultKindAt,
      continuationAdapted, bodyEq⟩ :=
    CodeAdapted.constructorFVarLet_eq spec.localsAligned valueEq fits
      valueKind argumentsCompiled localCompiled spec.bodyAdapted
  have hGets := argumentsReady argumentsFound
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.allocCtorCall callFound
  have physicalParams : imp.params.length = physicalArgs.length :=
    params.trans physicalArity.symm
  rw [bodyEq]
  apply codeWP_constructor_let valueEq valueCompiled argumentsFound callFound
    evaluated semanticStep stateRelated resultFound resultKindAt hGets imported
    spec.hostsSatisfy inBounds contracted physicalParams results operation
    extension nextRuntimeRelated failureClear valueRelated targetSet
  exact continued continuationAdapted resultFound targetSet

/--
Certificate-free partial compiler correctness for the base return case.

The only dynamic premise is a source evaluation. The target proof is derived
from the actual compiler/adaptor equation retained by
`ConcreteSupportedExport`, plus the initial source/concrete state relation.
No `ConcreteCodeSimulation` or `ReuseCapacityCodeSimulation` premise appears.
-/
theorem ConcreteSupportedExport.correctReturn
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {result : FVarId}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.return result) sourceModule
        sourceFunction target hosts exportName)
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    (sourceEvaluation :
      CodeEvaluates context sourceRuntime sourceEnv (.return result)
        resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv (.return result))
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind callerTail) := by
  cases sourceEvaluation with
  | ret sourceLookup =>
      obtain ⟨kind, resultIndex, localCompiled, resultFound, kindAt, bodyEq⟩ :=
        CodeAdapted.return_eq spec.localsAligned spec.bodyAdapted
      obtain ⟨physical, targetLookup, valueRelated⟩ :=
        stateRelated.resolve sourceLookup resultFound kindAt
      have body :
          DeclarationBodyWP context sourceModule sourceFunction
            target.wasmModule hosts.env sourceRuntime sourceEnv
            (.return result) spec.targetFunction initial initial
            initialWitness parameters physical := by
        refine ⟨parameterCount, spec.singleResult, fun tail => ?_⟩
        rw [bodyEq]
        exact codeWP_return_to_exactBodyPost
          (callerTail := tail) localCompiled resultFound kindAt sourceLookup
          stateRelated targetLookup parameterCount spec.singleResult
      have declaration :
          SuccessfulDeclaration context sourceModule sourceFunction
            target.wasmModule hosts.env sourceExternals sourceRuntime
            sourceRuntime sourceEnv (.return result) spec.targetFunction
            spec.targetFunctionIndex initial initial initialWitness
            initialWitness parameters kind resultValue physical := {
        sourceEvaluates :=
          (CodeEvaluates.ret sourceLookup).execEvaluates sourceExternals
        notImport := spec.notImport
        functionFound := spec.targetFunctionFound
        body
        runtimeRelated := stateRelated.1
        failureClear := stateRelated.2.1
        valueRelated }
      exact ⟨declaration.sourceEvaluates, kind, spec.targetFunctionIndex,
        spec.exported, declaration.terminatesWith callerTail⟩
  | effect sourceStep _ =>
      unfold SourceEffectResult at sourceStep
      have impossible := sourceStep sourceExternals
      cases sourceLookup : lookup sourceEnv result with
      | none =>
          simp [executeStep, coreStep, lookupValue, sourceLookup, fail, observe]
            at impossible
      | some value =>
          simp [executeStep, coreStep, lookupValue, sourceLookup] at impossible

/--
Certificate-free partial compiler correctness for one allocating natural
literal followed by its return.

Unlike the return base case, this theorem composes a real source/target step:
the concrete host allocates the literal, the generated `local.set` records its
physical word, and the compiled return reads that word back. Allocation and
checked-local-write success remain explicit runtime preconditions. All
instruction selection, call numbering, local numbering, host-contract
selection, and continuation composition are derived from the static pipeline
package and the operation-level refinement theorems.
-/
theorem ConcreteSupportedExport.correctNaturalLiteralReturn
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {value : Nat}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context
        (.let decl (.return decl.fvarId)) sourceModule sourceFunction target
        hosts exportName)
    (valueEq : decl.value = .lit (.nat value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .tobject))
    {sourceExternals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {heap : MemoryState}
    {word : Word32}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (allocated :
      allocateNatural initial.host.runtime.heap value = .ok (heap, word))
    (localSetReady :
      ∀ {resultIndex},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            (spec.targetFunction.toLocals parameters.reverse).set? resultIndex
                (.i32 (UInt32.ofNat word.value)) =
              some updated) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.let decl (.return decl.fvarId)))
        (ReturnedObservation
          (literal sourceRuntime (.nat value)).1
          (literal sourceRuntime (.nat value)).2) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost
          (literal sourceRuntime (.nat value)).1
          (literal sourceRuntime (.nat value)).2 .tobject callerTail) := by
  obtain ⟨callIndex, resultIndex, valueCompiled, callFound, resultFound,
      resultKindAt, bodyEq⟩ :=
    CodeAdapted.naturalLiteralReturn_eq spec.localsAligned valueEq valueKind
      localCompiled spec.bodyAdapted
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.naturalLiteralCall callFound
  obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated, step⟩ :=
    letStepSimulates_naturalLiteral (context := context) valueEq stateRelated
      resultFound resultKindAt allocated imported spec.hostsSatisfy inBounds
      contracted params results targetSet
  have sourceEvaluation :
      CodeEvaluates context sourceRuntime sourceEnv
        (.let decl (.return decl.fvarId))
        (literal sourceRuntime (.nat value)).1
        (literal sourceRuntime (.nat value)).2 :=
    .letValue step.1
      (.ret (lookup_bind_self sourceEnv decl.fvarId
        (literal sourceRuntime (.nat value)).2))
  have valueAdapted :
      instructions sourceModule sourceFunction []
          [.call (.runtime (.literal (.nat value) .tobject))] =
        .ok [.call callIndex] := by
    simp [instructions, instruction, callFound]
    rfl
  have resultLookup :
      updated.get resultIndex =
        some (.i32 (UInt32.ofNat word.value)) :=
    (localUpdate_of_set? targetSet).1
  have body :
      DeclarationBodyWP context sourceModule sourceFunction target.wasmModule
        hosts.env sourceRuntime sourceEnv
        (.let decl (.return decl.fvarId)) spec.targetFunction initial
        (replaceHeap initial heap) initialWitness parameters
        (.i32 (UInt32.ofNat word.value)) := by
    refine ⟨parameterCount, spec.singleResult, fun tail => ?_⟩
    rw [bodyEq]
    have continued :=
      codeWP_return_to_exactBodyPost
        (context := context) (sourceModule := sourceModule)
        (sourceFunction := sourceFunction) (labels := [])
        (module := target.wasmModule) (hostEnv := hosts.env)
        (targetFunction := spec.targetFunction)
        (parameters := parameters) (callerTail := tail)
        localCompiled resultFound resultKindAt
        (lookup_bind_self sourceEnv decl.fvarId
          (literal sourceRuntime (.nat value)).2)
        step.2.2.1 resultLookup parameterCount spec.singleResult
    simpa using
      codeWP_letValue valueCompiled valueAdapted resultFound step continued
  have failureClear :
      (replaceHeap initial heap).host.failure? = none := by
    simp [replaceHeap, clearFailure]
  have declaration :
      SuccessfulDeclaration context sourceModule sourceFunction
        target.wasmModule hosts.env sourceExternals sourceRuntime
        (literal sourceRuntime (.nat value)).1 sourceEnv
        (.let decl (.return decl.fvarId)) spec.targetFunction
        spec.targetFunctionIndex initial (replaceHeap initial heap)
        initialWitness nextWitness parameters .tobject
        (literal sourceRuntime (.nat value)).2
        (.i32 (UInt32.ofNat word.value)) := {
    sourceEvaluates := sourceEvaluation.execEvaluates sourceExternals
    notImport := spec.notImport
    functionFound := spec.targetFunctionFound
    body
    runtimeRelated := nextRuntimeRelated
    failureClear
    valueRelated }
  exact ⟨declaration.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    declaration.terminatesWith callerTail⟩

/--
Certificate-free partial compiler correctness for one allocating UTF-8 String
literal followed by its return.

The theorem derives the compiler-selected String call, destination local,
concrete resolver contract, and return suffix from the static pipeline. Its
only dynamic resource premises are successful String allocation and capacity
for the checked local write.
-/
theorem ConcreteSupportedExport.correctStringLiteralReturn
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {value : String}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context
        (.let decl (.return decl.fvarId)) sourceModule sourceFunction target
        hosts exportName)
    (valueEq : decl.value = .lit (.str value))
    (valueKind : Fir.Wasm.letValueKind decl = .ok .object)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object))
    {sourceExternals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {heap : MemoryState}
    {word : Word32}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (allocated :
      allocateString initial.host.runtime.heap value = .ok (heap, word))
    (localSetReady :
      ∀ {resultIndex},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            (spec.targetFunction.toLocals parameters.reverse).set? resultIndex
                (.i32 (UInt32.ofNat word.value)) =
              some updated) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.let decl (.return decl.fvarId)))
        (ReturnedObservation
          (literal sourceRuntime (.str value)).1
          (literal sourceRuntime (.str value)).2) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost
          (literal sourceRuntime (.str value)).1
          (literal sourceRuntime (.str value)).2 .object callerTail) := by
  obtain ⟨callIndex, resultIndex, valueCompiled, callFound, resultFound,
      resultKindAt, bodyEq⟩ :=
    CodeAdapted.stringLiteralReturn_eq spec.localsAligned valueEq valueKind
      localCompiled spec.bodyAdapted
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.stringLiteralCall callFound
  obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated, step⟩ :=
    letStepSimulates_stringLiteral (context := context) valueEq stateRelated
      resultFound resultKindAt allocated imported spec.hostsSatisfy inBounds
      contracted params results targetSet
  have sourceEvaluation :
      CodeEvaluates context sourceRuntime sourceEnv
        (.let decl (.return decl.fvarId))
        (literal sourceRuntime (.str value)).1
        (literal sourceRuntime (.str value)).2 :=
    .letValue step.1
      (.ret (lookup_bind_self sourceEnv decl.fvarId
        (literal sourceRuntime (.str value)).2))
  have valueAdapted :
      instructions sourceModule sourceFunction []
          [.call (.runtime (.literal (.str value) .object))] =
        .ok [.call callIndex] := by
    simp [instructions, instruction, callFound]
    rfl
  have resultLookup :
      updated.get resultIndex =
        some (.i32 (UInt32.ofNat word.value)) :=
    (localUpdate_of_set? targetSet).1
  have body :
      DeclarationBodyWP context sourceModule sourceFunction target.wasmModule
        hosts.env sourceRuntime sourceEnv
        (.let decl (.return decl.fvarId)) spec.targetFunction initial
        (replaceHeap initial heap) initialWitness parameters
        (.i32 (UInt32.ofNat word.value)) := by
    refine ⟨parameterCount, spec.singleResult, fun tail => ?_⟩
    rw [bodyEq]
    have continued :=
      codeWP_return_to_exactBodyPost
        (context := context) (sourceModule := sourceModule)
        (sourceFunction := sourceFunction) (labels := [])
        (module := target.wasmModule) (hostEnv := hosts.env)
        (targetFunction := spec.targetFunction)
        (parameters := parameters) (callerTail := tail)
        localCompiled resultFound resultKindAt
        (lookup_bind_self sourceEnv decl.fvarId
          (literal sourceRuntime (.str value)).2)
        step.2.2.1 resultLookup parameterCount spec.singleResult
    simpa using
      codeWP_letValue valueCompiled valueAdapted resultFound step continued
  have failureClear :
      (replaceHeap initial heap).host.failure? = none := by
    simp [replaceHeap, clearFailure]
  have declaration :
      SuccessfulDeclaration context sourceModule sourceFunction
        target.wasmModule hosts.env sourceExternals sourceRuntime
        (literal sourceRuntime (.str value)).1 sourceEnv
        (.let decl (.return decl.fvarId)) spec.targetFunction
        spec.targetFunctionIndex initial (replaceHeap initial heap)
        initialWitness nextWitness parameters .object
        (literal sourceRuntime (.str value)).2
        (.i32 (UInt32.ofNat word.value)) := {
    sourceEvaluates := sourceEvaluation.execEvaluates sourceExternals
    notImport := spec.notImport
    functionFound := spec.targetFunctionFound
    body
    runtimeRelated := nextRuntimeRelated
    failureClear
    valueRelated }
  exact ⟨declaration.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    declaration.terminatesWith callerTail⟩

/--
Certificate-free finite compiler correctness for a constructor allocation
returned immediately, with arbitrary mixtures of local and erased arguments.

All target instructions and physical operands are derived from the production
compiler, adapter, evaluator, and initial state relation.  The remaining
`concreteStep` premise is the operation-specific allocation refinement at the
derived operands.
-/
theorem ConcreteSupportedExport.correctConstructorReturn
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context
        (.let decl (.return decl.fvarId)) sourceModule sourceFunction target
        hosts exportName)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (argumentCode, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {parameters callerTail : List Wasm.Value}
    {semanticArgs : Array Value}
    {sourceValue : Value}
    {initialWitness : RefinementWitness}
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (concreteStep :
      ∀ {physicalArgs},
        physicalArgs.length = fieldKinds.size →
          ∃ (nextStore : Wasm.Store Host) (word : Word32)
              (nextWitness : RefinementWitness),
            allocCtorStep info fieldKinds resultKind initial physicalArgs =
                .Return [.i32 (UInt32.ofNat word.value)] nextStore ∧
              initialWitness.Extends nextWitness ∧
              ConcreteRuntimeRel nextStore.host.runtime nextWitness
                nextRuntime ∧
              nextStore.host.failure? = none ∧
              PhysicalValueRel nextWitness resultKind
                (.i32 (UInt32.ofNat word.value)) sourceValue)
    (localSetReady :
      ∀ {resultIndex : Nat} {word : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            (spec.targetFunction.toLocals parameters.reverse).set? resultIndex
                (.i32 (UInt32.ofNat word.value)) =
              some updated) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.let decl (.return decl.fvarId)))
        (ReturnedObservation nextRuntime sourceValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost nextRuntime sourceValue resultKind callerTail) := by
  obtain ⟨targetArguments, callIndex, resultIndex, valueCompiled,
      argumentsAdapted, callFound, resultFound, resultKindAt, bodyEq⟩ :=
    CodeAdapted.constructorReturn_eq spec.localsAligned valueEq fits valueKind
      argumentsCompiled localCompiled spec.bodyAdapted
  obtain ⟨physicalArgs, argumentsReady, physicalArity⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      argumentsAdapted evaluated stateRelated
  obtain ⟨nextStore, word, nextWitness, operation, extension,
      nextRuntimeRelated, failureClear, valueRelated⟩ :=
    concreteStep physicalArity
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.allocCtorCall callFound
  have physicalParams : imp.params.length = physicalArgs.length :=
    params.trans physicalArity.symm
  have step := letStepSimulates_constructorArgs (context := context) valueEq
    evaluated semanticStep stateRelated resultFound resultKindAt
    argumentsReady imported spec.hostsSatisfy inBounds contracted
    physicalParams results operation extension nextRuntimeRelated failureClear
    valueRelated targetSet
  have sourceEvaluation :
      CodeEvaluates context sourceRuntime sourceEnv
        (.let decl (.return decl.fvarId)) nextRuntime sourceValue :=
    .letValue step.1
      (.ret (lookup_bind_self sourceEnv decl.fvarId sourceValue))
  have resultLookup :
      updated.get resultIndex =
        some (.i32 (UInt32.ofNat word.value)) :=
    (localUpdate_of_set? targetSet).1
  have body :
      DeclarationBodyWP context sourceModule sourceFunction target.wasmModule
        hosts.env sourceRuntime sourceEnv
        (.let decl (.return decl.fvarId)) spec.targetFunction initial nextStore
        initialWitness parameters (.i32 (UInt32.ofNat word.value)) := by
    refine ⟨parameterCount, spec.singleResult, fun tail => ?_⟩
    rw [bodyEq]
    have continued :=
      codeWP_return_to_exactBodyPost
        (context := context) (sourceModule := sourceModule)
        (sourceFunction := sourceFunction) (labels := [])
        (module := target.wasmModule) (hostEnv := hosts.env)
        (targetFunction := spec.targetFunction)
        (parameters := parameters) (callerTail := tail)
        localCompiled resultFound resultKindAt
        (lookup_bind_self sourceEnv decl.fvarId sourceValue)
        step.2.2.1 resultLookup parameterCount spec.singleResult
    simpa [List.append_assoc] using
      codeWP_constructorArgs_let valueEq valueCompiled argumentsAdapted
        callFound evaluated semanticStep stateRelated resultFound resultKindAt
        argumentsReady imported spec.hostsSatisfy inBounds contracted
        physicalParams results operation extension nextRuntimeRelated
        failureClear valueRelated targetSet continued
  have declaration :
      SuccessfulDeclaration context sourceModule sourceFunction
        target.wasmModule hosts.env sourceExternals sourceRuntime nextRuntime
        sourceEnv (.let decl (.return decl.fvarId)) spec.targetFunction
        spec.targetFunctionIndex initial nextStore initialWitness nextWitness
        parameters resultKind sourceValue
        (.i32 (UInt32.ofNat word.value)) := {
    sourceEvaluates := sourceEvaluation.execEvaluates sourceExternals
    notImport := spec.notImport
    functionFound := spec.targetFunctionFound
    body
    runtimeRelated := nextRuntimeRelated
    failureClear
    valueRelated }
  exact ⟨declaration.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    declaration.terminatesWith callerTail⟩

/--
Certificate-free finite compiler correctness for an all-`fvar` constructor
allocation returned immediately.

The static target body, local/import numbering, and concrete resolver contract
are recovered from the actual compiler pipeline. Dynamic premises describe
only the successful source and concrete allocation/refinement plus ordinary
Wasm-local capacity.
-/
theorem ConcreteSupportedExport.correctConstructorFVarReturn
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    {fvarIds : List FVarId}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context
        (.let decl (.return decl.fvarId)) sourceModule sourceFunction target
        hosts exportName)
    (valueEq : decl.value = .ctor info args)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (fvarIds.map Fir.Wasm.Instruction.localGet, fieldKinds))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host}
    {parameters callerTail : List Wasm.Value}
    {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value}
    {sourceValue : Value}
    {word : Word32}
    {initialWitness nextWitness : RefinementWitness}
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (argumentsReady :
      ∀ {indices},
        List.Forall₂
            (fun fvarId index =>
              findFVar? (functionBindings sourceFunction) fvarId =
                some index)
            fvarIds indices →
          List.Forall₂
            (fun index physical =>
              (spec.targetFunction.toLocals parameters.reverse).get index =
                some physical)
            indices physicalArgs)
    (physicalArity : physicalArgs.length = fieldKinds.size)
    (operation :
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : initialWitness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (valueRelated :
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat word.value)) sourceValue)
    (localSetReady :
      ∀ {resultIndex},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            (spec.targetFunction.toLocals parameters.reverse).set? resultIndex
                (.i32 (UInt32.ofNat word.value)) =
              some updated) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.let decl (.return decl.fvarId)))
        (ReturnedObservation nextRuntime sourceValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost nextRuntime sourceValue resultKind callerTail) := by
  obtain ⟨indices, callIndex, resultIndex, valueCompiled, argumentsFound,
      callFound, resultFound, resultKindAt, bodyEq⟩ :=
    CodeAdapted.constructorFVarReturn_eq spec.localsAligned valueEq fits
      valueKind argumentsCompiled localCompiled spec.bodyAdapted
  have hGets := argumentsReady argumentsFound
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.allocCtorCall callFound
  have physicalParams : imp.params.length = physicalArgs.length :=
    params.trans physicalArity.symm
  have step := letStepSimulates_constructor (context := context) valueEq
    evaluated semanticStep stateRelated resultFound resultKindAt hGets imported
    spec.hostsSatisfy inBounds contracted physicalParams results operation
    extension nextRuntimeRelated failureClear valueRelated targetSet
  have sourceEvaluation :
      CodeEvaluates context sourceRuntime sourceEnv
        (.let decl (.return decl.fvarId)) nextRuntime sourceValue :=
    .letValue step.1
      (.ret (lookup_bind_self sourceEnv decl.fvarId sourceValue))
  have resultLookup :
      updated.get resultIndex =
        some (.i32 (UInt32.ofNat word.value)) :=
    (localUpdate_of_set? targetSet).1
  have body :
      DeclarationBodyWP context sourceModule sourceFunction target.wasmModule
        hosts.env sourceRuntime sourceEnv
        (.let decl (.return decl.fvarId)) spec.targetFunction initial nextStore
        initialWitness parameters (.i32 (UInt32.ofNat word.value)) := by
    refine ⟨parameterCount, spec.singleResult, fun tail => ?_⟩
    rw [bodyEq]
    have continued :=
      codeWP_return_to_exactBodyPost
        (context := context) (sourceModule := sourceModule)
        (sourceFunction := sourceFunction) (labels := [])
        (module := target.wasmModule) (hostEnv := hosts.env)
        (targetFunction := spec.targetFunction)
        (parameters := parameters) (callerTail := tail)
        localCompiled resultFound resultKindAt
        (lookup_bind_self sourceEnv decl.fvarId sourceValue)
        step.2.2.1 resultLookup parameterCount spec.singleResult
    simpa [List.append_assoc] using
      codeWP_constructor_let valueEq valueCompiled argumentsFound callFound
        evaluated semanticStep stateRelated resultFound resultKindAt hGets
        imported spec.hostsSatisfy inBounds contracted physicalParams results
        operation extension nextRuntimeRelated failureClear valueRelated
        targetSet continued
  have declaration :
      SuccessfulDeclaration context sourceModule sourceFunction
        target.wasmModule hosts.env sourceExternals sourceRuntime nextRuntime
        sourceEnv (.let decl (.return decl.fvarId)) spec.targetFunction
        spec.targetFunctionIndex initial nextStore initialWitness nextWitness
        parameters resultKind sourceValue
        (.i32 (UInt32.ofNat word.value)) := {
    sourceEvaluates := sourceEvaluation.execEvaluates sourceExternals
    notImport := spec.notImport
    functionFound := spec.targetFunctionFound
    body
    runtimeRelated := nextRuntimeRelated
    failureClear
    valueRelated }
  exact ⟨declaration.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    declaration.terminatesWith callerTail⟩

end FirTalos.Concrete
