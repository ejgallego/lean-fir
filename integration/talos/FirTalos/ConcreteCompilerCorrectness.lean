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

end FirTalos.Concrete
