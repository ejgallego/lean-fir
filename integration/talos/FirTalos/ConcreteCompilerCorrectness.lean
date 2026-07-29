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
Generic compiler/adaptor inversion for a direct `let` whose value code reads
one source local and invokes one runtime operation.

This is the shared static shape behind object, `USize`, and packed-scalar
projections.  It recovers both numeric local slots, the numeric import slot,
and the independently compiled continuation from the production compiler and
adapter.
-/
theorem CodeAdapted.localRuntimeCallLet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceId : FVarId}
    {operation : RuntimeOp}
    {resultKind : AbiKind}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet sourceId, .call (.runtime operation)])
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ sourceIndex callIndex resultIndex targetRest,
      Fir.Wasm.compileLetValue context decl =
          .ok [.localGet sourceId, .call (.runtime operation)] ∧
        findFVar? (functionBindings sourceFunction) sourceId =
          some sourceIndex ∧
        callIndex? sourceModule (.runtime operation) = some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some resultKind ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          .localGet sourceIndex :: .call callIndex ::
            .localSet resultIndex :: targetRest := by
  obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
      actualValueCompiled, restCompiled, valueAdapted, restAdapted,
      resultFound, targetEq⟩ :=
    CodeAdapted.let_eq adapted
  rw [valueCompiled] at actualValueCompiled
  injection actualValueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨alignedIndex, alignedFound, resultKindAt⟩ :=
    localsAligned localCompiled
  rw [resultFound] at alignedFound
  injection alignedFound with indexEq
  subst alignedIndex
  obtain ⟨indices, callIndex, sourceFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq
      (fvarIds := [sourceId]) (operation := operation) valueAdapted
  cases sourceFound with
  | cons sourceFound noMore =>
      cases noMore
      subst targetValue
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      exact ⟨_, callIndex, resultIndex, targetRest, valueCompiled,
        sourceFound, callFound, resultFound, resultKindAt,
        continuationAdapted, by simpa using targetEq⟩

/-- Production compiler/adaptor inversion for an object projection `let`. -/
theorem CodeAdapted.objectProjectionLet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {index : Nat}
    {objectId : FVarId}
    {objectKind resultKind : AbiKind}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .oproj index objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ objectIndex callIndex resultIndex targetRest,
      Fir.Wasm.compileLetValue context decl =
          .ok [.localGet objectId,
            .call (.runtime (.objectProj index resultKind))] ∧
        findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        callIndex? sourceModule
            (.runtime (.objectProj index resultKind)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some resultKind ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          .localGet objectIndex :: .call callIndex ::
            .localSet resultIndex :: targetRest := by
  apply CodeAdapted.localRuntimeCallLet_eq localsAligned
    (compileLetValue_objectProjection valueEq valueKind objectCompiled)
    localCompiled adapted

/-- Production compiler/adaptor inversion for a `USize` projection `let`. -/
theorem CodeAdapted.usizeProjectionLet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {index : Nat}
    {objectId : FVarId}
    {objectKind : AbiKind}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .uproj index objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok .usize)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .usize))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ objectIndex callIndex resultIndex targetRest,
      Fir.Wasm.compileLetValue context decl =
          .ok [.localGet objectId,
            .call (.runtime (.usizeProj index))] ∧
        findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        callIndex? sourceModule (.runtime (.usizeProj index)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some .usize ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          .localGet objectIndex :: .call callIndex ::
            .localSet resultIndex :: targetRest := by
  apply CodeAdapted.localRuntimeCallLet_eq localsAligned
    (compileLetValue_usizeProjection valueEq valueKind objectCompiled)
    localCompiled adapted

/-- Production compiler/adaptor inversion for a packed-scalar projection. -/
theorem CodeAdapted.scalarProjectionLet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {width offset : Nat}
    {objectId : FVarId}
    {objectKind resultKind : AbiKind}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (valueEq : decl.value = .sproj width offset objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation) target) :
    ∃ objectIndex callIndex resultIndex targetRest,
      Fir.Wasm.compileLetValue context decl =
          .ok [.localGet objectId,
            .call (.runtime (.scalarProj width offset resultKind))] ∧
        findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        callIndex? sourceModule
            (.runtime (.scalarProj width offset resultKind)) =
          some callIndex ∧
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex ∧
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some resultKind ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          .localGet objectIndex :: .call callIndex ::
            .localSet resultIndex :: targetRest := by
  apply CodeAdapted.localRuntimeCallLet_eq localsAligned
    (compileLetValue_scalarProjection valueEq valueKind objectCompiled)
    localCompiled adapted

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
Concrete allocation success is derived from explicit wasm32 headroom.
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
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (allocationCapacity :
      initial.host.runtime.heap.AllocationCapacity
        (align8 (headerBytes + (stringUtf8Bytes value).length)))
    (localSetReady :
      ∀ {resultIndex} {word : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
              some updated)
    (continued :
      ∀ {heap : MemoryState} {word : Word32}
          {targetRest resultIndex updated nextWitness},
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
  obtain ⟨heap, word, allocated⟩ :=
    stateRelated.1.heap.frontier.allocateString_eq_ok_of_capacity value
      allocationCapacity
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
Certificate-free recursive correctness for an object-projection `let`.

The production compiler and adapter determine both local slots, the concrete
projection import, and the continuation split.  The source/state relation
determines the physical object operand. Descriptor existence follows from the
successful source constructor read and `ConcreteRuntimeRel`; only ABI-kind
agreement for the selected object field remains explicit.
-/
theorem ConcreteSupportedExport.codeWP_objectProjectionLet
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {index : Nat}
    {objectId : FVarId}
    {objectKind resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .oproj index objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (objectRefines : objectKind.refines .tobject = true)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {sourceObject value : Value}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getObjectField sourceRuntime sourceObject index = .ok value)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (fieldKindAligned :
      ∀ {objectWord : Word32} {info : LCNF.CtorInfo}
          {fieldKinds : Array AbiKind},
        ValueRel witness .tobject (.word32 objectWord) sourceObject →
          witness.descriptors.lookup? objectWord =
              some (.constructor info fieldKinds) →
            fieldKinds[index]? = some resultKind)
    (localSetReady :
      ∀ {resultIndex : Nat} {resultWord : Word32},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex
                (.i32 (UInt32.ofNat resultWord.value)) =
              some updated)
    (continued :
      ∀ {targetRest : Wasm.Program} {resultIndex : Nat}
          {resultWord : Word32} {updated : Wasm.Locals},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex
                (.i32 (UInt32.ofNat resultWord.value)) =
              some updated →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env sourceRuntime (bind sourceEnv decl.fvarId value)
            continuation targetRest (clearFailure initial) updated witness
            tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q := by
  obtain ⟨objectIndex, callIndex, resultIndex, targetRest, valueCompiled,
      objectFound, callFound, resultFound, resultKindAt,
      continuationAdapted, bodyEq⟩ :=
    CodeAdapted.objectProjectionLet_eq spec.localsAligned valueEq valueKind
      objectCompiled localCompiled spec.bodyAdapted
  obtain ⟨alignedObjectIndex, alignedObjectFound, objectKindAt⟩ :=
    spec.localsAligned objectCompiled
  rw [objectFound] at alignedObjectFound
  injection alignedObjectFound with objectIndexEq
  subst alignedObjectIndex
  obtain ⟨objectPhysical, hObject, physicalRelated⟩ :=
    stateRelated.resolve sourceLookup objectFound objectKindAt
  have tobjectRelated := physicalRelated.toTObject objectRefines
  cases tobjectRelated with
  | word32 objectRelated =>
      obtain ⟨info, fieldKinds, descriptor⟩ :=
        FirTalos.Concrete.ConcreteRuntimeRel.constructorDescriptor_of_getObjectField
          stateRelated.1 objectRelated projected
      have fieldKind := fieldKindAligned objectRelated descriptor
      obtain ⟨resultWord, concreteRead, _, _⟩ :=
        objectProjStep_of_refines stateRelated.1 objectRelated descriptor
          fieldKind projected
      obtain ⟨updated, targetSet⟩ := localSetReady resultFound
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        spec.objectProjectionCall callFound
      rw [bodyEq]
      apply codeWP_objectProjection_let valueEq valueCompiled objectFound
        callFound sourceLookup projected stateRelated resultFound resultKindAt
        hObject objectRelated descriptor fieldKind concreteRead imported
        spec.hostsSatisfy inBounds contracted params results targetSet
      exact continued continuationAdapted resultFound targetSet
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

/--
Certificate-free recursive correctness for a `USize` projection `let`.
The source object lane is recovered from the compiler-assigned local; the
successful source read and whole-heap relation recover its constructor
descriptor automatically.
-/
theorem ConcreteSupportedExport.codeWP_usizeProjectionLet
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {index : Nat}
    {objectId : FVarId}
    {objectKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .uproj index objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok .usize)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (objectRefines : objectKind.refines .tobject = true)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .usize))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {sourceObject : Value}
    {value : UInt64}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getUSizeSlot sourceRuntime sourceObject index = .ok (.usize value))
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (localSetReady :
      ∀ {resultIndex : Nat},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated,
            locals.set? resultIndex (.i64 value) = some updated)
    (continued :
      ∀ {targetRest : Wasm.Program} {resultIndex : Nat}
          {updated : Wasm.Locals},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex (.i64 value) = some updated →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env sourceRuntime
            (bind sourceEnv decl.fvarId (.usize value)) continuation targetRest
            (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q := by
  obtain ⟨objectIndex, callIndex, resultIndex, targetRest, valueCompiled,
      objectFound, callFound, resultFound, resultKindAt,
      continuationAdapted, bodyEq⟩ :=
    CodeAdapted.usizeProjectionLet_eq spec.localsAligned valueEq valueKind
      objectCompiled localCompiled spec.bodyAdapted
  obtain ⟨alignedObjectIndex, alignedObjectFound, objectKindAt⟩ :=
    spec.localsAligned objectCompiled
  rw [objectFound] at alignedObjectFound
  injection alignedObjectFound with objectIndexEq
  subst alignedObjectIndex
  obtain ⟨objectPhysical, hObject, physicalRelated⟩ :=
    stateRelated.resolve sourceLookup objectFound objectKindAt
  have tobjectRelated := physicalRelated.toTObject objectRefines
  cases tobjectRelated with
  | word32 objectRelated =>
      obtain ⟨info, fieldKinds, descriptor⟩ :=
        FirTalos.Concrete.ConcreteRuntimeRel.constructorDescriptor_of_getUSizeSlot
          stateRelated.1 objectRelated projected
      obtain ⟨updated, targetSet⟩ := localSetReady resultFound
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        spec.usizeProjectionCall callFound
      rw [bodyEq]
      apply codeWP_usizeProjection_let valueEq valueCompiled objectFound
        callFound sourceLookup projected stateRelated resultFound resultKindAt
        hObject objectRelated descriptor imported spec.hostsSatisfy inBounds
        contracted params results targetSet
      exact continued continuationAdapted resultFound targetSet
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

/--
Certificate-free recursive correctness for a packed integer-scalar projection.

The generic compiler/adaptor inversion and source-local relation determine the
target prefix and object operand.  `concreteStep` is precisely the
operation-specific refinement boundary: for that derived object word, the
concrete reader returns one physical lane related to the successful source
projection.
-/
theorem ConcreteSupportedExport.codeWP_scalarProjectionLet
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {width offset : Nat}
    {objectId : FVarId}
    {objectKind resultKind : AbiKind}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context (.let decl continuation)
        sourceModule sourceFunction target hosts exportName)
    (valueEq : decl.value = .sproj width offset objectId)
    (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (objectRefines : objectKind.refines .tobject = true)
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, resultKind))
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {sourceObject sourceValue : Value}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getScalarField sourceRuntime sourceObject width offset =
        .ok sourceValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (concreteStep :
      ∀ {objectWord : Word32},
        ValueRel witness .tobject (.word32 objectWord) sourceObject →
          ∃ physical,
            scalarProjStep width offset resultKind initial
                [.i32 (UInt32.ofNat objectWord.value)] =
              .Return [physical] (clearFailure initial) ∧
            PhysicalValueRel witness resultKind physical sourceValue)
    (localSetReady :
      ∀ {resultIndex : Nat} {physical : Wasm.Value},
        findFVar? (functionBindings sourceFunction) decl.fvarId =
            some resultIndex →
          ∃ updated, locals.set? resultIndex physical = some updated)
    (continued :
      ∀ {targetRest : Wasm.Program} {resultIndex : Nat}
          {physical : Wasm.Value} {updated : Wasm.Locals},
        CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest →
          findFVar? (functionBindings sourceFunction) decl.fvarId =
              some resultIndex →
          locals.set? resultIndex physical = some updated →
          PhysicalValueRel witness resultKind physical sourceValue →
          CodeWP context sourceModule sourceFunction [] target.wasmModule
            hosts.env sourceRuntime (bind sourceEnv decl.fvarId sourceValue)
            continuation targetRest (clearFailure initial) updated witness
            tail Q) :
    CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
      sourceRuntime sourceEnv (.let decl continuation)
      spec.targetFunction.body initial locals witness tail Q := by
  obtain ⟨objectIndex, callIndex, resultIndex, targetRest, valueCompiled,
      objectFound, callFound, resultFound, resultKindAt,
      continuationAdapted, bodyEq⟩ :=
    CodeAdapted.scalarProjectionLet_eq spec.localsAligned valueEq valueKind
      objectCompiled localCompiled spec.bodyAdapted
  obtain ⟨alignedObjectIndex, alignedObjectFound, objectKindAt⟩ :=
    spec.localsAligned objectCompiled
  rw [objectFound] at alignedObjectFound
  injection alignedObjectFound with objectIndexEq
  subst alignedObjectIndex
  obtain ⟨objectPhysical, hObject, physicalObjectRelated⟩ :=
    stateRelated.resolve sourceLookup objectFound objectKindAt
  have tobjectRelated := physicalObjectRelated.toTObject objectRefines
  cases tobjectRelated with
  | word32 objectRelated =>
      obtain ⟨physical, operation, physicalRelated⟩ :=
        concreteStep objectRelated
      obtain ⟨updated, targetSet⟩ := localSetReady resultFound
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        spec.scalarProjectionCall callFound
      rw [bodyEq]
      apply codeWP_scalarProjection_let valueEq valueCompiled objectFound
        callFound sourceLookup projected stateRelated resultFound resultKindAt
        hObject physicalRelated imported spec.hostsSatisfy inBounds contracted
        params results operation targetSet
      exact continued continuationAdapted resultFound targetSet
        physicalRelated
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

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
Successful source evaluation for the first structural compiler fragment:
returns and direct-value `let` nodes.

This is a source semantic relation, not a translation certificate.  It is the
direct-value subrelation of `CodeEvaluates`; target code remains absent and is
recovered exclusively from the executable compiler and Talos adapter.
-/
inductive DirectValueEvaluates (context : Fir.Wasm.Context)
    (Supported : LCNF.LetDecl .impure → Prop) :
    RuntimeState → Env → LCNF.Code .impure → RuntimeState → Value → Prop where
  | ret
      (sourceLookup : lookup sourceEnv result = some sourceValue) :
      DirectValueEvaluates context Supported sourceRuntime sourceEnv
        (.return result)
        sourceRuntime sourceValue
  | letValue
      (supported : Supported decl)
      (sourceStep :
        SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
          sourceValue)
      (continued :
        DirectValueEvaluates context Supported nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation
          resultRuntime resultValue) :
      DirectValueEvaluates context Supported sourceRuntime sourceEnv
        (.let decl continuation) resultRuntime resultValue

/-- The direct-value evaluation view is a sound restriction of the existing
proof-facing source semantics. -/
theorem DirectValueEvaluates.toCodeEvaluates
    {context : Fir.Wasm.Context}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value}
    {Supported : LCNF.LetDecl .impure → Prop}
    (evaluation :
      DirectValueEvaluates context Supported sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue) :
    CodeEvaluates context sourceRuntime sourceEnv sourceCode resultRuntime
      resultValue := by
  induction evaluation with
  | ret sourceLookup =>
      exact .ret sourceLookup
  | letValue _ sourceStep _ ih =>
      exact .letValue sourceStep ih

/-- Direct-value evaluation also denotes an actual finite run of the
repository's executable source interpreter. -/
theorem DirectValueEvaluates.execEvaluates
    {context : Fir.Wasm.Context}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value}
    {Supported : LCNF.LetDecl .impure → Prop}
    (evaluation :
      DirectValueEvaluates context Supported sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue)
    (externals : ExternalImpl) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (ReturnedObservation resultRuntime resultValue) :=
  evaluation.toCodeEvaluates.execEvaluates externals

/--
Static admission for a direct local alias.

The declaration copies an existing local without applying it, and source and
destination have the same compiler ABI kind.  These are source/compiler facts,
not a target-code witness; the target prefix is still recovered from
`compileLetValue` and the Talos adapter.
-/
inductive LocalAliasSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (sourceId : FVarId) (kind : AbiKind)
      (valueEq : decl.value = .fvar sourceId #[])
      (resultKind : Fir.Wasm.letValueKind decl = .ok kind)
      (sourceCompiled :
        Fir.Wasm.getLocal context sourceId =
          .ok (.localGet sourceId, kind))
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind)) :
      LocalAliasSupported context decl

/--
The nonallocating literal forms and their exact compiler ABI kind.

The relation is source-facing. Its derived symbolic instruction, Talos
instruction, physical value, and semantic value are functions of this
classification rather than caller-provided translation evidence.
-/
inductive ImmediateLiteralKind : LCNF.LitValue → AbiKind → Type where
  | uint8 (value : UInt8) : ImmediateLiteralKind (.uint8 value) .uint8
  | uint16 (value : UInt16) : ImmediateLiteralKind (.uint16 value) .uint16
  | uint32 (value : UInt32) : ImmediateLiteralKind (.uint32 value) .uint32
  | uint64 (value : UInt64) : ImmediateLiteralKind (.uint64 value) .uint64
  | usize (value : UInt64) : ImmediateLiteralKind (.usize value) .usize

namespace ImmediateLiteralKind

def sourceValue {literal : LCNF.LitValue} {kind : AbiKind} :
    ImmediateLiteralKind literal kind → Value
  | .uint8 value => .scalar (.uint8 value)
  | .uint16 value => .scalar (.uint16 value)
  | .uint32 value => .scalar (.uint32 value)
  | .uint64 value => .scalar (.uint64 value)
  | .usize value => .usize value

def symbolicInstruction {literal : LCNF.LitValue} {kind : AbiKind} :
    ImmediateLiteralKind literal kind → Fir.Wasm.Instruction
  | .uint8 value => .i32Const .uint8 (UInt32.ofNat value.toNat)
  | .uint16 value => .i32Const .uint16 (UInt32.ofNat value.toNat)
  | .uint32 value => .i32Const .uint32 value
  | .uint64 value => .i64Const .uint64 value
  | .usize value => .i64Const .usize value

def targetInstruction {literal : LCNF.LitValue} {kind : AbiKind} :
    ImmediateLiteralKind literal kind → Wasm.Instruction
  | .uint8 value => .const (UInt32.ofNat value.toNat)
  | .uint16 value => .const (UInt32.ofNat value.toNat)
  | .uint32 value => .const value
  | .uint64 value => .constI64 value
  | .usize value => .constI64 value

def physical {literal : LCNF.LitValue} {kind : AbiKind} :
    ImmediateLiteralKind literal kind → Wasm.Value
  | .uint8 value => .i32 (UInt32.ofNat value.toNat)
  | .uint16 value => .i32 (UInt32.ofNat value.toNat)
  | .uint32 value => .i32 value
  | .uint64 value => .i64 value
  | .usize value => .i64 value

@[simp] theorem sourceLiteral
    {literal : LCNF.LitValue} {kind : AbiKind}
    (shape : ImmediateLiteralKind literal kind) (runtime : RuntimeState) :
    Fir.LeanIR.Impure.literal runtime literal =
      (runtime, shape.sourceValue) := by
  cases shape <;> simp [sourceValue, Fir.LeanIR.Impure.literal]

theorem physicalRelated
    {literal : LCNF.LitValue} {kind : AbiKind}
    (shape : ImmediateLiteralKind literal kind)
    (witness : RefinementWitness) :
    PhysicalValueRel witness kind shape.physical shape.sourceValue := by
  cases shape with
  | uint8 value =>
      simpa [physical, sourceValue] using
        (PhysicalValueRel.word32
          (ValueRel.uint8
            (witness := witness) (word := Word32.ofUInt8 value) rfl))
  | uint16 value =>
      simpa [physical, sourceValue] using
        (PhysicalValueRel.word32
          (ValueRel.uint16
            (witness := witness) (word := Word32.ofUInt16 value) rfl))
  | uint32 value =>
      simpa [physical, sourceValue] using
        (PhysicalValueRel.word32
          (ValueRel.uint32
            (witness := witness) (word := Word32.ofUInt32 value) rfl))
  | uint64 value =>
      simpa [physical, sourceValue] using
        (PhysicalValueRel.word64
          (ValueRel.uint64 (witness := witness) (value := value)))
  | usize value =>
      simpa [physical, sourceValue] using
        (PhysicalValueRel.word64
          (ValueRel.usize (witness := witness) (value := value)))

theorem compileLetValue_eq
    {context : Fir.Wasm.Context} {decl : LCNF.LetDecl .impure}
    {literal : LCNF.LitValue} {kind : AbiKind}
    (shape : ImmediateLiteralKind literal kind)
    (valueEq : decl.value = .lit literal)
    (valueKind : Fir.Wasm.letValueKind decl = .ok kind) :
    Fir.Wasm.compileLetValue context decl =
      .ok [shape.symbolicInstruction] := by
  cases shape <;>
    simp [Fir.Wasm.compileLetValue, valueEq, valueKind,
      AbiKind.acceptsLiteral, Fir.Wasm.literalKind, Fir.Wasm.compileLiteral,
      symbolicInstruction, Bind.bind, Except.bind, pure, Except.pure]

theorem instructions_eq
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {literal : LCNF.LitValue} {kind : AbiKind}
    (shape : ImmediateLiteralKind literal kind) :
    instructions sourceModule sourceFunction labels
        [shape.symbolicInstruction] =
      .ok [shape.targetInstruction] := by
  cases shape <;>
    simp [instructions, instruction, symbolicInstruction, targetInstruction,
      Bind.bind, Except.bind, pure, Except.pure]

theorem wp_let
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {store : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {tail : List Wasm.Value}
    {literal : LCNF.LitValue} {kind : AbiKind}
    (shape : ImmediateLiteralKind literal kind)
    (targetSet :
      locals.set? resultIndex shape.physical = some updated)
    (continued :
      Wasm.wp module rest Q store { updated with values := tail } hostEnv) :
    Wasm.wp module
      (shape.targetInstruction :: .localSet resultIndex :: rest)
      Q store { locals with values := tail } hostEnv := by
  cases shape with
  | uint8 value =>
      simpa [physical, targetInstruction] using
        wp_i32Const_let (UInt32.ofNat value.toNat) tail targetSet continued
  | uint16 value =>
      simpa [physical, targetInstruction] using
        wp_i32Const_let (UInt32.ofNat value.toNat) tail targetSet continued
  | uint32 value =>
      simpa [physical, targetInstruction] using
        wp_i32Const_let value tail targetSet continued
  | uint64 value =>
      simpa [physical, targetInstruction] using
        wp_i64Const_let value tail targetSet continued
  | usize value =>
      simpa [physical, targetInstruction] using
        wp_i64Const_let value tail targetSet continued

end ImmediateLiteralKind

/--
Static admission for a nonallocating integer or `USize` literal.

Only the source literal classification and compiler-selected destination are
recorded. The emitted instruction, physical constant, and semantic result are
derived from `ImmediateLiteralKind`.
-/
inductive ImmediateLiteralSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (literal : LCNF.LitValue) (resultKind : AbiKind)
      (valueEq : decl.value = .lit literal)
      (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, resultKind))
      (shape : ImmediateLiteralKind literal resultKind) :
      ImmediateLiteralSupported context decl

/--
Static admission for a direct `USize` projection.

The predicate contains only source/compiler typing facts: the object and
destination symbolic locals, the target-independent ABI refinement, and the
selected source slot.  Numeric locals, imports, concrete words, and heap
descriptors remain outputs of compilation and state refinement.
-/
inductive USizeProjectionSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (index : Nat) (objectId : FVarId) (objectKind : AbiKind)
      (valueEq : decl.value = .uproj index objectId)
      (resultKind : Fir.Wasm.letValueKind decl = .ok .usize)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectRefines : objectKind.refines .tobject = true)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, .usize)) :
      USizeProjectionSupported context decl

/--
Static admission for a direct object projection.

The selected field's ABI kind is the one additional typing fact that cannot
be recovered from `ConcreteRuntimeRel`: the heap relation proves descriptor
existence and contents, while this source-level condition connects the
compiler-selected result kind to that descriptor. It quantifies over related
source values but contains no target program, numeric slot, import, concrete
read, or chosen descriptor witness.
-/
inductive ObjectProjectionSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (index : Nat) (objectId : FVarId)
      (objectKind resultKind : AbiKind)
      (valueEq : decl.value = .oproj index objectId)
      (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectRefines : objectKind.refines .tobject = true)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, resultKind))
      (fieldKindAligned :
        ∀ {sourceEnv : Env} {sourceObject : Value}
            {witness : RefinementWitness} {objectWord : Word32}
            {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind},
          lookup sourceEnv objectId = some sourceObject →
            ValueRel witness .tobject (.word32 objectWord) sourceObject →
            witness.descriptors.lookup? objectWord =
                some (.constructor info fieldKinds) →
              fieldKinds[index]? = some resultKind) :
      ObjectProjectionSupported context decl

/--
Static admission for a direct packed-integer scalar projection.

The final premise is exactly the missing source typing judgment: whenever the
successful semantic read produces a scalar, its constructor agrees with the
compiler-selected result ABI kind. It contains no concrete object word,
numeric local/import, heap read, or target-step witness.
-/
inductive ScalarProjectionSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (width offset : Nat) (objectId : FVarId)
      (objectKind resultKind : AbiKind)
      (valueEq : decl.value = .sproj width offset objectId)
      (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectRefines : objectKind.refines .tobject = true)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, resultKind))
      (valueKindAligned :
        ∀ {sourceRuntime : RuntimeState} {sourceEnv : Env}
            {sourceObject : Value} {scalar : ScalarValue},
          lookup sourceEnv objectId = some sourceObject →
            getScalarField sourceRuntime sourceObject width offset =
              .ok (.scalar scalar) →
              ScalarValueKind scalar resultKind) :
      ScalarProjectionSupported context decl

/-- Every successful absolute-slot `USize` read produces an unboxed word. -/
theorem getUSizeSlot_ok_eq_usize
    {runtime : RuntimeState} {object result : Value} {slot : Nat}
    (read : getUSizeSlot runtime object slot = .ok result) :
    ∃ word, result = .usize word := by
  unfold getUSizeSlot at read
  generalize constructorEq :
    getConstructor runtime object = constructorResult at read
  cases constructorResult with
  | error fault =>
      simp [Bind.bind, Except.bind] at read
  | ok constructor =>
      obtain ⟨location, cell, value⟩ := constructor
      simp only [Bind.bind, Except.bind] at read
      by_cases bounded : value.objectFields.size ≤ slot
      · rw [if_pos bounded] at read
        generalize fieldEq :
          value.usizeFields[slot - value.objectFields.size]? = fieldResult
            at read
        cases fieldResult with
        | none =>
            simp at read
        | some word =>
            simp [Pure.pure, Except.pure] at read
            cases read
            exact ⟨word, rfl⟩
      · rw [if_neg bounded] at read
        contradiction

/--
Invert a successful source `USize` projection without introducing a separate
evaluation certificate.
-/
theorem sourceLetResult_usizeProjection_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {index : Nat} {objectId : FVarId}
    (valueEq : decl.value = .uproj index objectId)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ sourceObject value,
      nextRuntime = sourceRuntime ∧
        sourceValue = .usize value ∧
        lookup sourceEnv objectId = some sourceObject ∧
        getUSizeSlot sourceRuntime sourceObject index = .ok (.usize value) := by
  unfold SourceLetResult at sourceStep
  simp only [evalLetValue, valueEq] at sourceStep
  cases sourceLookup : lookup sourceEnv objectId with
  | none =>
      have lookupFailed :
          lookupValue sourceEnv objectId = .error (.unknownVar objectId) := by
        simp [lookupValue, sourceLookup]
      rw [lookupFailed] at sourceStep
      contradiction
  | some sourceObject =>
      have lookupSucceeded :
          lookupValue sourceEnv objectId = .ok sourceObject := by
        simp [lookupValue, sourceLookup]
      rw [lookupSucceeded] at sourceStep
      simp only [Bind.bind, Except.bind] at sourceStep
      cases projected : getUSizeSlot sourceRuntime sourceObject index with
      | error fault =>
          rw [projected] at sourceStep
          contradiction
      | ok projectedValue =>
          rw [projected] at sourceStep
          have pairEq :
              (sourceRuntime, LetAction.value projectedValue) =
                (nextRuntime, LetAction.value sourceValue) := by
            exact Except.ok.inj sourceStep
          have runtimeEq : sourceRuntime = nextRuntime :=
            congrArg Prod.fst pairEq
          have valueEq' : projectedValue = sourceValue := by
            exact LetAction.value.inj (congrArg Prod.snd pairEq)
          subst sourceValue
          obtain ⟨value, resultEq⟩ := getUSizeSlot_ok_eq_usize projected
          subst projectedValue
          exact ⟨sourceObject, value, runtimeEq.symm, rfl, rfl, projected⟩

/--
Invert a successful source object projection to its environment lookup and
semantic field read.
-/
theorem sourceLetResult_objectProjection_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {index : Nat} {objectId : FVarId}
    (valueEq : decl.value = .oproj index objectId)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ sourceObject,
      nextRuntime = sourceRuntime ∧
        lookup sourceEnv objectId = some sourceObject ∧
        getObjectField sourceRuntime sourceObject index = .ok sourceValue := by
  unfold SourceLetResult at sourceStep
  simp only [evalLetValue, valueEq] at sourceStep
  cases sourceLookup : lookup sourceEnv objectId with
  | none =>
      have lookupFailed :
          lookupValue sourceEnv objectId = .error (.unknownVar objectId) := by
        simp [lookupValue, sourceLookup]
      rw [lookupFailed] at sourceStep
      contradiction
  | some sourceObject =>
      have lookupSucceeded :
          lookupValue sourceEnv objectId = .ok sourceObject := by
        simp [lookupValue, sourceLookup]
      rw [lookupSucceeded] at sourceStep
      simp only [Bind.bind, Except.bind] at sourceStep
      cases projected : getObjectField sourceRuntime sourceObject index with
      | error fault =>
          rw [projected] at sourceStep
          contradiction
      | ok projectedValue =>
          rw [projected] at sourceStep
          have pairEq :
              (sourceRuntime, LetAction.value projectedValue) =
                (nextRuntime, LetAction.value sourceValue) :=
            Except.ok.inj sourceStep
          have runtimeEq : sourceRuntime = nextRuntime :=
            congrArg Prod.fst pairEq
          have valueEq' : projectedValue = sourceValue :=
            LetAction.value.inj (congrArg Prod.snd pairEq)
          subst projectedValue
          exact ⟨sourceObject, runtimeEq.symm, rfl, projected⟩

/-- Every successful packed-scalar read returns an unboxed scalar value. -/
theorem getScalarField_ok_eq_scalar
    {runtime : RuntimeState} {object result : Value}
    {width offset : Nat}
    (read : getScalarField runtime object width offset = .ok result) :
    ∃ scalar, result = .scalar scalar := by
  unfold getScalarField at read
  generalize constructorEq :
    getConstructor runtime object = constructorResult at read
  cases constructorResult with
  | error fault =>
      simp [Bind.bind, Except.bind] at read
  | ok constructor =>
      obtain ⟨location, cell, value⟩ := constructor
      simp only [Bind.bind, Except.bind] at read
      generalize fieldEq :
        value.scalarFields.find? (fun field =>
          field.width == width && field.offset == offset) = fieldResult
          at read
      cases fieldResult with
      | none =>
          simp at read
      | some field =>
          simp [Pure.pure, Except.pure] at read
          cases read
          exact ⟨field.value, rfl⟩

/--
Invert a successful source scalar projection to its object lookup, scalar
constructor, and exact semantic field read.
-/
theorem sourceLetResult_scalarProjection_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {width offset : Nat} {objectId : FVarId}
    (valueEq : decl.value = .sproj width offset objectId)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ sourceObject scalar,
      nextRuntime = sourceRuntime ∧
        sourceValue = .scalar scalar ∧
        lookup sourceEnv objectId = some sourceObject ∧
        getScalarField sourceRuntime sourceObject width offset =
          .ok (.scalar scalar) := by
  unfold SourceLetResult at sourceStep
  simp only [evalLetValue, valueEq] at sourceStep
  cases sourceLookup : lookup sourceEnv objectId with
  | none =>
      have lookupFailed :
          lookupValue sourceEnv objectId = .error (.unknownVar objectId) := by
        simp [lookupValue, sourceLookup]
      rw [lookupFailed] at sourceStep
      contradiction
  | some sourceObject =>
      have lookupSucceeded :
          lookupValue sourceEnv objectId = .ok sourceObject := by
        simp [lookupValue, sourceLookup]
      rw [lookupSucceeded] at sourceStep
      simp only [Bind.bind, Except.bind] at sourceStep
      cases projected : getScalarField sourceRuntime sourceObject width offset with
      | error fault =>
          rw [projected] at sourceStep
          contradiction
      | ok projectedValue =>
          rw [projected] at sourceStep
          have pairEq :
              (sourceRuntime, LetAction.value projectedValue) =
                (nextRuntime, LetAction.value sourceValue) :=
            Except.ok.inj sourceStep
          have runtimeEq : sourceRuntime = nextRuntime :=
            congrArg Prod.fst pairEq
          have valueEq' : projectedValue = sourceValue :=
            LetAction.value.inj (congrArg Prod.snd pairEq)
          subst sourceValue
          obtain ⟨scalar, resultEq⟩ :=
            getScalarField_ok_eq_scalar projected
          subst projectedValue
          exact ⟨sourceObject, scalar, runtimeEq.symm, rfl, rfl, projected⟩

/--
Invert a successful nonallocating literal source step. The literal
classification fixes both its unchanged runtime and exact semantic value.
-/
theorem sourceLetResult_immediateLiteral_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {literal : LCNF.LitValue} {kind : AbiKind}
    (shape : ImmediateLiteralKind literal kind)
    (valueEq : decl.value = .lit literal)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    nextRuntime = sourceRuntime ∧ sourceValue = shape.sourceValue := by
  unfold SourceLetResult at sourceStep
  simp only [evalLetValue, valueEq] at sourceStep
  rw [shape.sourceLiteral] at sourceStep
  change
    Except.ok (sourceRuntime, LetAction.value shape.sourceValue) =
      Except.ok (nextRuntime, LetAction.value sourceValue)
    at sourceStep
  have pairEq :
      (sourceRuntime, LetAction.value shape.sourceValue) =
        (nextRuntime, LetAction.value sourceValue) :=
    Except.ok.inj sourceStep
  exact ⟨(congrArg Prod.fst pairEq).symm,
    LetAction.value.inj (congrArg Prod.snd pairEq).symm⟩

/--
The concrete frame has exactly the parameter and local capacity allocated for
the selected symbolic function.  Runtime and witness components are ignored:
this is a threaded resource invariant, separate from semantic state
refinement.
-/
def ConcreteLocalFrameAligned
    (sourceFunction : Fir.Wasm.Function)
    (_sourceRuntime : RuntimeState) (_sourceEnv : Env)
    (_targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (_witness : RefinementWitness) : Prop :=
  targetLocals.params.length = sourceFunction.params.size ∧
    targetLocals.locals.length = sourceFunction.locals.size

theorem ConcreteLocalFrameAligned.validIndex
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {fvar : FVarId} {index : Nat}
    (aligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (found :
      findFVar? (functionBindings sourceFunction) fvar = some index) :
    targetLocals.validIndex index := by
  have bounded := FirTalos.Correctness.findFVar?_lt_length found
  simp only [functionBindings, List.length_append, Array.length_toList] at bounded
  simpa [ConcreteLocalFrameAligned, Wasm.Locals.validIndex, aligned.1,
    aligned.2] using bounded

/-- A checked destination write preserves the exact concrete frame shape. -/
theorem ConcreteLocalFrameAligned.set?
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv nextEnv : Env}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness nextWitness : RefinementWitness} {fvar : FVarId} {index : Nat}
    {physical : Wasm.Value}
    (aligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (found :
      findFVar? (functionBindings sourceFunction) fvar = some index) :
    ∃ updated,
      targetLocals.set? index physical = some updated ∧
        ConcreteLocalFrameAligned sourceFunction nextRuntime nextEnv nextStore
          updated nextWitness := by
  obtain ⟨updated, targetSet⟩ :=
    FirTalos.Correctness.locals_set?_exists (aligned.validIndex found)
  have lengths := FirTalos.Correctness.locals_lengths_of_set? targetSet
  exact ⟨updated, targetSet,
    ⟨lengths.1.trans aligned.1, lengths.2.trans aligned.2⟩⟩

/--
The uniform runtime condition needed by the structural direct-`let` proof.

For every successful direct source value accepted by the production compiler
and adapter, the concrete runtime must implement the same step and establish
the related continuation state.  This property contains no target program or
per-source translation derivation: `valueCode`, `targetValue`, and
`resultIndex` are universally quantified outputs of the executable pipeline.
The operation-specific W6 refinement theorems discharge its cases.
-/
def DirectLetRuntimeRefines
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (Supported : LCNF.LetDecl .impure → Prop)
    (Invariant :
      RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop) : Prop :=
  ∀ {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {sourceValue : Value}
      {valueCode : List Fir.Wasm.Instruction}
      {targetValue : Wasm.Program}
      {targetStore : Wasm.Store Host}
      {targetLocals : Wasm.Locals}
      {resultIndex : Nat}
      {witness : RefinementWitness},
    Supported decl →
      Invariant sourceRuntime sourceEnv targetStore targetLocals witness →
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue →
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness →
      Fir.Wasm.compileLetValue context decl = .ok valueCode →
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue →
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex →
      ∃ nextStore nextLocals nextWitness,
        LetStepSimulates context sourceFunction module hostEnv decl targetValue
          sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
          targetLocals nextLocals resultIndex witness nextWitness ∧
        Invariant nextRuntime (bind sourceEnv decl.fvarId sourceValue)
          nextStore nextLocals nextWitness

/-- Uniform runtime laws with the same resource invariant compose by source
admission disjunction. This is the structural bridge for mixed direct-value
spines; it combines verified operation families without constructing a
source/target certificate. -/
theorem DirectLetRuntimeRefines.or
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {Left Right : LCNF.LetDecl .impure → Prop}
    {Invariant :
      RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (left :
      DirectLetRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv Left Invariant)
    (right :
      DirectLetRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv Right Invariant) :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels module
      hostEnv (fun decl => Left decl ∨ Right decl) Invariant := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex witness supported
    invariant sourceStep stateRelated valueCompiled valueAdapted resultFound
  cases supported with
  | inl leftSupported =>
      exact left leftSupported invariant sourceStep stateRelated valueCompiled
        valueAdapted resultFound
  | inr rightSupported =>
      exact right rightSupported invariant sourceStep stateRelated valueCompiled
        valueAdapted resultFound

/--
One compiler-produced immediate literal is simulated by its generated
constant and destination write. No host call, heap transition, or witness
extension is involved.
-/
theorem letStepSimulates_immediateLiteral
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {sourceEnv : Env}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {witness : RefinementWitness}
    {literal : LCNF.LitValue} {kind : AbiKind}
    (shape : ImmediateLiteralKind literal kind)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl sourceRuntime
        shape.sourceValue)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some kind)
    (targetSet :
      locals.set? resultIndex shape.physical = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [shape.targetInstruction]
      sourceRuntime sourceRuntime sourceEnv shape.sourceValue initial initial
      locals updated resultIndex witness witness := by
  have nextRelated :
      StateRelated sourceFunction sourceRuntime
        (bind sourceEnv decl.fvarId shape.sourceValue) initial updated witness := by
    have bound :=
      initialRelated.bindPhysical resultFound resultKindAt
        (shape.physicalRelated witness) targetSet
    simpa [initialRelated.clearFailure] using bound
  refine ⟨sourceStep, initialRelated, nextRelated, ?_⟩
  intro rest Q tail continued
  exact shape.wp_let targetSet continued

/--
One zero-argument local alias is simulated by the generated `local.get` /
`local.set` pair.  No host operation or heap transition is involved.
-/
theorem letStepSimulates_localAlias
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {sourceEnv : Env}
    {sourceId : FVarId} {kind : AbiKind}
    {sourceRuntime : RuntimeState} {sourceValue : Value}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {sourceIndex resultIndex : Nat} {physical : Wasm.Value}
    {witness : RefinementWitness}
    (valueEq : decl.value = .fvar sourceId #[])
    (sourceLookup : lookup sourceEnv sourceId = some sourceValue)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (sourcePhysical : locals.get sourceIndex = some physical)
    (physicalRelated :
      PhysicalValueRel witness kind physical sourceValue)
    (targetSet : locals.set? resultIndex physical = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet sourceIndex]
      sourceRuntime sourceRuntime sourceEnv sourceValue initial initial locals
      updated resultIndex witness witness := by
  have nextRelated :
      StateRelated sourceFunction sourceRuntime
        (bind sourceEnv decl.fvarId sourceValue) initial updated witness := by
    have bound := initialRelated.bindPhysical resultFound resultKindAt
      physicalRelated targetSet
    simpa [initialRelated.clearFailure] using bound
  refine ⟨?_, initialRelated, nextRelated, ?_⟩
  · unfold SourceLetResult
    have sourceLookupValue :
        lookupValue sourceEnv sourceId = .ok sourceValue := by
      simp [lookupValue, sourceLookup]
    have emptyArgs : evalArgs sourceEnv #[] = .ok #[] := by
      unfold evalArgs
      simp
      rfl
    simp only [evalLetValue, valueEq]
    rw [sourceLookupValue, emptyArgs]
    change
      Except.ok (sourceRuntime, LetAction.value sourceValue) =
        Except.ok (sourceRuntime, LetAction.value sourceValue)
    rfl
  · intro rest Q tail continued
    simp only [List.singleton_append, Wasm.wp_localGet_cons]
    have sourcePhysicalWithTail :
        ({ locals with values := tail } : Wasm.Locals).get sourceIndex =
          some physical := by
      simpa [Wasm.Locals.get] using sourcePhysical
    rw [sourcePhysicalWithTail]
    exact FirTalos.Concrete.wp_localSet_of_set targetSet continued

/--
Uniform runtime-law instance for every admitted local alias in an arbitrary
direct-value spine.

The proof derives both symbolic and numeric instructions from the executable
compiler/adapter, resolves the copied lane from `StateRelated`, and uses the
threaded frame-shape invariant to justify the destination write.
-/
theorem directLetRuntimeRefines_localAlias
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    (localsAligned : LocalLayoutAligned context sourceFunction) :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels module
      hostEnv (LocalAliasSupported context)
      (ConcreteLocalFrameAligned sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex witness supported
    frameAligned sourceStep stateRelated valueCompiled valueAdapted resultFound
  rcases supported with
    ⟨sourceId, kind, valueEq, resultKind, sourceCompiled, resultCompiled⟩
  have sourceFacts :
      nextRuntime = sourceRuntime ∧
        lookup sourceEnv sourceId = some sourceValue := by
    unfold SourceLetResult at sourceStep
    simp only [evalLetValue, valueEq] at sourceStep
    have emptyArgs : evalArgs sourceEnv #[] = .ok #[] := by
      unfold evalArgs
      simp
      rfl
    cases sourceLookupEq : lookup sourceEnv sourceId with
    | none =>
        have lookupFailed :
            lookupValue sourceEnv sourceId =
              .error (.unknownVar sourceId) := by
          simp [lookupValue, sourceLookupEq]
        rw [lookupFailed] at sourceStep
        contradiction
    | some actual =>
        have lookupSucceeded :
            lookupValue sourceEnv sourceId = .ok actual := by
          simp [lookupValue, sourceLookupEq]
        rw [lookupSucceeded, emptyArgs] at sourceStep
        have pairEq :
            (sourceRuntime, LetAction.value actual) =
              (nextRuntime, LetAction.value sourceValue) := by
          change
            Except.ok (sourceRuntime, LetAction.value actual) =
              Except.ok (nextRuntime, LetAction.value sourceValue)
            at sourceStep
          exact Except.ok.inj sourceStep
        have runtimeEq : sourceRuntime = nextRuntime :=
          congrArg Prod.fst pairEq
        have actionEq :
            LetAction.value actual = LetAction.value sourceValue :=
          congrArg Prod.snd pairEq
        have actualEq : actual = sourceValue :=
          LetAction.value.inj actionEq
        exact ⟨runtimeEq.symm, congrArg some actualEq⟩
  rcases sourceFacts with ⟨rfl, sourceLookup⟩
  obtain ⟨sourceIndex, sourceFound, sourceKindAt⟩ :=
    localsAligned sourceCompiled
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    localsAligned resultCompiled
  rw [resultFound] at alignedResultFound
  injection alignedResultFound with resultIndexEq
  subst alignedResultIndex
  obtain ⟨physical, sourcePhysical, physicalRelated⟩ :=
    stateRelated.resolve sourceLookup sourceFound sourceKindAt
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet sourceId] := by
    have emptyCompiled :
        Fir.Wasm.compileArgs context #[] = .ok ([], #[]) := by
      rfl
    simp [Fir.Wasm.compileLetValue, valueEq, resultKind, sourceCompiled,
      emptyCompiled]
    rfl
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  have expectedAdapted :
      instructions sourceModule sourceFunction labels [.localGet sourceId] =
        .ok [.localGet sourceIndex] := by
    have sourceFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            sourceId =
          some sourceIndex := by
      simpa [functionBindings] using sourceFound
    simp [instructions, instruction, sourceFound']
    rfl
  rw [expectedAdapted] at valueAdapted
  injection valueAdapted with targetValueEq
  subst targetValue
  obtain ⟨updated, targetSet, nextFrameAligned⟩ :=
    frameAligned.set? (nextRuntime := nextRuntime)
      (nextEnv := bind sourceEnv decl.fvarId sourceValue)
      (nextStore := targetStore) (nextWitness := witness)
      (physical := physical) resultFound
  exact ⟨targetStore, updated, witness,
    letStepSimulates_localAlias valueEq sourceLookup stateRelated resultFound
      resultKindAt sourcePhysical physicalRelated targetSet,
    nextFrameAligned⟩

/--
Uniform runtime-law instance for every nonallocating integer or `USize`
literal.

The source classification derives the semantic value, compiler instruction,
adapted Talos constant, and related physical lane. Exact frame capacity is the
only runtime resource premise.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_immediateLiteral
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
    {labels : List FVarId} :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ImmediateLiteralSupported context)
      (ConcreteLocalFrameAligned sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex witness supported
    frameAligned sourceStep stateRelated valueCompiled valueAdapted resultFound
  rcases supported with
    ⟨literal, resultKind, valueEq, valueKind, resultCompiled, shape⟩
  obtain ⟨rfl, rfl⟩ :=
    sourceLetResult_immediateLiteral_eq shape valueEq sourceStep
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [shape.symbolicInstruction] :=
    shape.compileLetValue_eq valueEq valueKind
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  have expectedAdapted :
      instructions sourceModule sourceFunction labels
          [shape.symbolicInstruction] =
        .ok [shape.targetInstruction] :=
    shape.instructions_eq
  rw [expectedAdapted] at valueAdapted
  injection valueAdapted with targetValueEq
  subst targetValue
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    spec.localsAligned resultCompiled
  rw [resultFound] at alignedResultFound
  injection alignedResultFound with resultIndexEq
  subst alignedResultIndex
  obtain ⟨updated, targetSet, nextFrameAligned⟩ :=
    frameAligned.set?
      (nextRuntime := nextRuntime)
      (nextEnv := bind sourceEnv decl.fvarId shape.sourceValue)
      (nextStore := targetStore)
      (nextWitness := witness)
      (physical := shape.physical) resultFound
  exact ⟨targetStore, updated, witness,
    letStepSimulates_immediateLiteral shape sourceStep stateRelated resultFound
      resultKindAt targetSet,
    nextFrameAligned⟩

/--
Uniform runtime-law instance for direct `USize` projections in any concrete
supported export.

The source evaluation supplies the object and successful semantic read; the
compiler and adapter supply the numeric object/import slots; `StateRelated`
supplies the physical object word; and `ConcreteRuntimeRel` recovers the
constructor descriptor.  Exact frame capacity alone justifies the generated
i64 destination write.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_usizeProjection
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
    {labels : List FVarId} :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (USizeProjectionSupported context)
      (ConcreteLocalFrameAligned sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex witness supported
    frameAligned sourceStep stateRelated valueCompiled valueAdapted resultFound
  rcases supported with
    ⟨index, objectId, objectKind, valueEq, resultKind, objectCompiled,
      objectRefines, resultCompiled⟩
  obtain ⟨sourceObject, value, rfl, rfl, sourceLookup, projected⟩ :=
    sourceLetResult_usizeProjection_eq valueEq sourceStep
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.usizeProj index))] :=
    compileLetValue_usizeProjection valueEq resultKind objectCompiled
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨indices, callIndex, objectFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq
      (fvarIds := [objectId]) (operation := .usizeProj index) valueAdapted
  cases objectFound with
  | cons objectFound noMore =>
      cases noMore
      subst targetValue
      obtain ⟨alignedObjectIndex, alignedObjectFound, objectKindAt⟩ :=
        spec.localsAligned objectCompiled
      rw [objectFound] at alignedObjectFound
      injection alignedObjectFound with objectIndexEq
      subst alignedObjectIndex
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        spec.localsAligned resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      obtain ⟨objectPhysical, hObject, physicalRelated⟩ :=
        stateRelated.resolve sourceLookup objectFound objectKindAt
      have tobjectRelated := physicalRelated.toTObject objectRefines
      cases tobjectRelated with
      | word32 objectRelated =>
          obtain ⟨info, fieldKinds, descriptor⟩ :=
            FirTalos.Concrete.ConcreteRuntimeRel.constructorDescriptor_of_getUSizeSlot
              stateRelated.1 objectRelated projected
          obtain ⟨updated, targetSet, nextFrameAligned⟩ :=
            frameAligned.set?
              (nextRuntime := nextRuntime)
              (nextEnv := bind sourceEnv decl.fvarId (.usize value))
              (nextStore := clearFailure targetStore)
              (nextWitness := witness)
              (physical := .i64 value) resultFound
          obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
            spec.usizeProjectionCall callFound
          exact ⟨clearFailure targetStore, updated, witness,
            letStepSimulates_usizeProjection valueEq sourceLookup projected
              stateRelated resultFound resultKindAt hObject objectRelated
              descriptor imported spec.hostsSatisfy inBounds contracted params
              results targetSet,
            nextFrameAligned⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Uniform runtime-law instance for direct object projections.

As for `USize`, every target-level choice is derived from the executable
pipeline and related state. The sole extra source obligation is
`ObjectProjectionSupported.fieldKindAligned`, which identifies the selected
descriptor field with the compiler's destination ABI kind.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_objectProjection
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
    {labels : List FVarId} :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ObjectProjectionSupported context)
      (ConcreteLocalFrameAligned sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex witness supported
    frameAligned sourceStep stateRelated valueCompiled valueAdapted resultFound
  rcases supported with
    ⟨index, objectId, objectKind, resultKind, valueEq, valueKind,
      objectCompiled, objectRefines, resultCompiled, fieldKindAligned⟩
  obtain ⟨sourceObject, rfl, sourceLookup, projected⟩ :=
    sourceLetResult_objectProjection_eq valueEq sourceStep
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.objectProj index resultKind))] :=
    compileLetValue_objectProjection valueEq valueKind objectCompiled
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨indices, callIndex, objectFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq
      (fvarIds := [objectId])
      (operation := .objectProj index resultKind) valueAdapted
  cases objectFound with
  | cons objectFound noMore =>
      cases noMore
      subst targetValue
      obtain ⟨alignedObjectIndex, alignedObjectFound, objectKindAt⟩ :=
        spec.localsAligned objectCompiled
      rw [objectFound] at alignedObjectFound
      injection alignedObjectFound with objectIndexEq
      subst alignedObjectIndex
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        spec.localsAligned resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      obtain ⟨objectPhysical, hObject, physicalRelated⟩ :=
        stateRelated.resolve sourceLookup objectFound objectKindAt
      have tobjectRelated := physicalRelated.toTObject objectRefines
      cases tobjectRelated with
      | word32 objectRelated =>
          obtain ⟨info, fieldKinds, descriptor⟩ :=
            FirTalos.Concrete.ConcreteRuntimeRel.constructorDescriptor_of_getObjectField
              stateRelated.1 objectRelated projected
          have fieldKind :=
            fieldKindAligned sourceLookup objectRelated descriptor
          obtain ⟨resultWord, concreteRead, valueRelated⟩ :=
            FirTalos.Concrete.ConcreteRuntimeRel.readObjectField_refines
              stateRelated.1 objectRelated descriptor fieldKind projected
          obtain ⟨updated, targetSet, nextFrameAligned⟩ :=
            frameAligned.set?
              (nextRuntime := nextRuntime)
              (nextEnv := bind sourceEnv decl.fvarId sourceValue)
              (nextStore := clearFailure targetStore)
              (nextWitness := witness)
              (physical := .i32 (UInt32.ofNat resultWord.value)) resultFound
          obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
            spec.objectProjectionCall callFound
          exact ⟨clearFailure targetStore, updated, witness,
            letStepSimulates_objectProjection valueEq sourceLookup projected
              stateRelated resultFound resultKindAt hObject objectRelated
              descriptor fieldKind concreteRead imported spec.hostsSatisfy
              inBounds contracted params results targetSet,
            nextFrameAligned⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Uniform runtime-law instance for successful packed-integer scalar
projections.

The source step determines the exact initialized scalar field. Source typing
connects its scalar constructor to the compiler-selected ABI kind; the generic
concrete runtime theorem then derives both the concrete read and physical
result. This theorem intentionally says nothing about a failing source read
from an uninitialized coordinate, whose zero-filled-heap discrepancy remains
recorded separately.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_scalarProjection
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
    {labels : List FVarId} :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ScalarProjectionSupported context)
      (ConcreteLocalFrameAligned sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex witness supported
    frameAligned sourceStep stateRelated valueCompiled valueAdapted resultFound
  rcases supported with
    ⟨width, offset, objectId, objectKind, resultKind, valueEq, valueKind,
      objectCompiled, objectRefines, resultCompiled, valueKindAligned⟩
  obtain ⟨sourceObject, scalar, rfl, rfl, sourceLookup, projected⟩ :=
    sourceLetResult_scalarProjection_eq valueEq sourceStep
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.scalarProj width offset resultKind))] :=
    compileLetValue_scalarProjection valueEq valueKind objectCompiled
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨indices, callIndex, objectFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq
      (fvarIds := [objectId])
      (operation := .scalarProj width offset resultKind) valueAdapted
  cases objectFound with
  | cons objectFound noMore =>
      cases noMore
      subst targetValue
      obtain ⟨alignedObjectIndex, alignedObjectFound, objectKindAt⟩ :=
        spec.localsAligned objectCompiled
      rw [objectFound] at alignedObjectFound
      injection alignedObjectFound with objectIndexEq
      subst alignedObjectIndex
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        spec.localsAligned resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      obtain ⟨objectPhysical, hObject, physicalRelated⟩ :=
        stateRelated.resolve sourceLookup objectFound objectKindAt
      have tobjectRelated := physicalRelated.toTObject objectRefines
      cases tobjectRelated with
      | word32 objectRelated =>
          have kindAligned := valueKindAligned sourceLookup projected
          obtain ⟨physical, operation, resultRelated⟩ :=
            scalarProjStep_of_refines stateRelated.1 objectRelated projected
              kindAligned
          obtain ⟨updated, targetSet, nextFrameAligned⟩ :=
            frameAligned.set?
              (nextRuntime := nextRuntime)
              (nextEnv := bind sourceEnv decl.fvarId (.scalar scalar))
              (nextStore := clearFailure targetStore)
              (nextWitness := witness)
              (physical := physical) resultFound
          obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
            spec.scalarProjectionCall callFound
          exact ⟨clearFailure targetStore, updated, witness,
            letStepSimulates_scalarProjection valueEq sourceLookup projected
              stateRelated resultFound resultKindAt hObject resultRelated
              imported spec.hostsSatisfy inBounds contracted params results
              operation targetSet,
            nextFrameAligned⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/-- Current constructive read-only direct-value admission. The disjunction is
deliberately source-facing and can grow operation by operation without
changing the structural theorem. -/
def ReadOnlyDirectSupported (context : Fir.Wasm.Context)
    (decl : LCNF.LetDecl .impure) : Prop :=
  LocalAliasSupported context decl ∨
    ImmediateLiteralSupported context decl ∨
      USizeProjectionSupported context decl ∨
        ObjectProjectionSupported context decl ∨
          ScalarProjectionSupported context decl

/--
Mixed local aliases, immediate literals, object, `USize`, and successful
packed-integer projection spines share one uniform runtime law and the same
exact-frame invariant.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_readOnlyDirect
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
    {labels : List FVarId} :
    DirectLetRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ReadOnlyDirectSupported context)
      (ConcreteLocalFrameAligned sourceFunction) := by
  change
    DirectLetRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (fun decl =>
          LocalAliasSupported context decl ∨
            (ImmediateLiteralSupported context decl ∨
              (USizeProjectionSupported context decl ∨
                (ObjectProjectionSupported context decl ∨
                  ScalarProjectionSupported context decl))))
        (ConcreteLocalFrameAligned sourceFunction)
  apply DirectLetRuntimeRefines.or
  · exact directLetRuntimeRefines_localAlias spec.localsAligned
  · apply DirectLetRuntimeRefines.or
    · exact spec.directLetRuntimeRefines_immediateLiteral
    · apply DirectLetRuntimeRefines.or
      · exact spec.directLetRuntimeRefines_usizeProjection
      · apply DirectLetRuntimeRefines.or
        · exact spec.directLetRuntimeRefines_objectProjection
        · exact spec.directLetRuntimeRefines_scalarProjection

/--
Structural, certificate-free partial correctness for the direct-value code
spine.

The proof inducts over source syntax and successful source evaluation.  At
each `let`, `CodeAdapted.let_eq` recovers the exact value prefix, destination
local, and recursively compiled continuation from the production pipeline;
`DirectLetRuntimeRefines` supplies only the uniform runtime refinement law.
The return leaf derives the final ABI lane and physical value from
`StateRelated`.
-/
theorem codeWP_of_directValueEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {targetFunction : Wasm.Function}
    {parameters callerTail : List Wasm.Value}
    {Supported : LCNF.LetDecl .impure → Prop}
    {Invariant :
      RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (evaluation :
      DirectValueEvaluates context Supported sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels sourceCode target)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (invariant : Invariant sourceRuntime sourceEnv initial locals witness)
    (runtimeRefines :
      DirectLetRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv Supported Invariant)
    (parameterCount : parameters.length = targetFunction.numParams)
    (resultCount : targetFunction.results.length = 1) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction labels module hostEnv
          sourceRuntime sourceEnv sourceCode target initial locals witness []
          (ConcreteFunctionBodyPost targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost resultStore physical callerTail)) ∧
        ConcreteRuntimeRel resultStore.host.runtime resultWitness
          resultRuntime ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness resultKind physical resultValue := by
  induction evaluation generalizing target initial locals witness with
  | ret sourceLookup =>
      obtain ⟨kind, resultIndex, localCompiled, resultFound, kindAt,
          targetEq⟩ :=
        CodeAdapted.return_eq localsAligned adapted
      obtain ⟨physical, targetLookup, valueRelated⟩ :=
        stateRelated.resolve sourceLookup resultFound kindAt
      subst target
      exact ⟨initial, witness, kind, physical,
        codeWP_return_to_exactBodyPost
          (callerTail := callerTail) localCompiled resultFound kindAt
          sourceLookup stateRelated targetLookup parameterCount resultCount,
        stateRelated.1, stateRelated.2.1, valueRelated⟩
  | letValue supported sourceStep continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels
            _ targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      obtain ⟨nextStore, nextLocals, nextWitness, step, nextInvariant⟩ :=
        runtimeRefines supported invariant sourceStep stateRelated valueCompiled
          valueAdapted resultFound
      obtain ⟨resultStore, resultWitness, resultKind, physical,
          continuationWP, resultRuntimeRelated, failureClear,
          valueRelated⟩ :=
        ih continuationAdapted step.2.2.1 nextInvariant
      subst target
      exact ⟨resultStore, resultWitness, resultKind, physical,
        codeWP_letValue valueCompiled valueAdapted resultFound step
          continuationWP,
        resultRuntimeRelated, failureClear, valueRelated⟩

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
only dynamic resource premises are wasm32 address-space headroom for the
concrete UTF-8 allocation and capacity for the checked local write. Allocation
success itself is derived from the related heap frontier.
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
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (allocationCapacity :
      initial.host.runtime.heap.AllocationCapacity
        (align8 (headerBytes + (stringUtf8Bytes value).length)))
    (localSetReady :
      ∀ {resultIndex} {word : Word32},
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
  obtain ⟨heap, word, allocated⟩ :=
    stateRelated.1.heap.frontier.allocateString_eq_ok_of_capacity value
      allocationCapacity
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
