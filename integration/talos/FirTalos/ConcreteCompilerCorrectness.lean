import FirTalos.ConcreteSupportedExportCorrectness
import FirTalos.ConcreteReuseCapacityCorrectness

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
Inversion of the real compiler at a persistent increment.

Persistent ownership operations are erased by lowering, so successful
compilation and adaptation of the whole node is exactly successful compilation
and adaptation of its continuation.
-/
theorem CodeAdapted.incPersistent_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId : FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.inc objectId amount check true continuation) target) :
    CodeAdapted context sourceModule sourceFunction labels continuation
      target := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp at core
  exact ⟨symbolic, Fir.Wasm.finishCompileResult_eq_ok_iff.mpr core,
    targetCompiled⟩

/--
Inversion of the real compiler at a persistent decrement.

As for persistent increments, the compiler emits no target instruction, so the
same symbolic and adapted programs compile the continuation.
-/
theorem CodeAdapted.decPersistent_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId : FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.dec objectId amount check true objectFields? continuation) target) :
    CodeAdapted context sourceModule sourceFunction labels continuation
      target := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp at core
  exact ⟨symbolic, Fir.Wasm.finishCompileResult_eq_ok_iff.mpr core,
    targetCompiled⟩

/--
A case node containing only its default alternative compiles and adapts to
exactly that selected branch. This is an inverse compiler fact: no
target-level branch witness is supplied by the caller.
-/
theorem CodeAdapted.defaultOnlyCases_selected
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {cases : LCNF.Cases .impure}
    {selected : LCNF.Code .impure}
    {target : Wasm.Program}
    (onlyDefault : cases.alts.toList = [.default selected])
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels (.cases cases)
        target) :
    CodeAdapted context sourceModule sourceFunction labels selected target := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  refine ⟨symbolic, ?_, targetCompiled⟩
  apply Fir.Wasm.finishCompileResult_eq_ok_iff.mpr
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  rw [onlyDefault] at core
  simpa [Fir.Wasm.compileCaseFallbackWithM,
    Fir.Wasm.compileCaseChainWithM, Fir.Wasm.isDefaultAlt] using core

/--
Recover the public fallback compiler result from a successful recursive-core
result. This is the reverse direction of the lowering bridge needed for
certificate-free case inversion.
-/
theorem compileCaseFallback_eq_ok_of_core
    {context : Fir.Wasm.Context}
    {alts : List (LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    (core :
      Fir.Wasm.compileCaseFallbackWithM
          (Fir.Wasm.compileCodeCore context) alts =
        some (.ok fallback)) :
    Fir.Wasm.compileCaseFallback context alts = .ok fallback := by
  unfold Fir.Wasm.compileCaseFallback
  unfold Fir.Wasm.compileCaseFallbackWithM at core ⊢
  generalize foundEq :
      alts.find? Fir.Wasm.isDefaultAlt = found at core ⊢
  cases found with
  | none =>
      change some (Except.ok [.unreachable]) =
        some (Except.ok fallback) at core
      simp only [Option.some.injEq, Except.ok.injEq] at core
      subst fallback
      rfl
  | some alt =>
      cases alt with
      | alt _ _ _ impossible => nomatch impossible
      | ctorAlt info code =>
          change some (Except.ok [.unreachable]) =
            some (Except.ok fallback) at core
          simp only [Option.some.injEq, Except.ok.injEq] at core
          subst fallback
          rfl
      | default code =>
          exact Fir.Wasm.finishCompileResult_eq_ok_iff.mpr core

/--
Recover the public constructor-chain compiler result from its successful
recursive-core execution. The proof follows the executable alternatives list
and introduces no independent target description.
-/
theorem compileCaseChain_eq_ok_of_core
    {context : Fir.Wasm.Context}
    {discr : FVarId}
    {alts : List (LCNF.Alt .impure)}
    {fallback result : List Fir.Wasm.Instruction}
    (core :
      Fir.Wasm.compileCaseChainWithM
          (Fir.Wasm.compileCodeCore context)
          (Fir.Wasm.caseDiscriminatorMode context discr)
          discr alts fallback =
        some (.ok result)) :
    Fir.Wasm.compileCaseChain context discr alts fallback = .ok result := by
  induction alts generalizing result with
  | nil =>
      rw [Fir.Wasm.compileCaseChainWithM.eq_def] at core
      change some (Except.ok fallback) = some (Except.ok result) at core
      simp only [Option.some.injEq, Except.ok.injEq] at core
      subst result
      change
        Fir.Wasm.compileCaseChainWithM
            (Fir.Wasm.compileCode context)
            (Fir.Wasm.caseDiscriminatorMode context discr)
            discr [] fallback =
          .ok fallback
      rw [Fir.Wasm.compileCaseChainWithM.eq_def]
      rfl
  | cons alt alts ih =>
      cases alt with
      | alt _ _ _ impossible => nomatch impossible
      | default code =>
          rw [Fir.Wasm.compileCaseChainWithM.eq_def] at core
          change
            Fir.Wasm.compileCaseChainWithM
                (Fir.Wasm.compileCode context)
                (Fir.Wasm.caseDiscriminatorMode context discr)
                discr (.default code :: alts) fallback =
              .ok result
          rw [Fir.Wasm.compileCaseChainWithM.eq_def]
          exact ih core
      | ctorAlt info code =>
          rw [Fir.Wasm.compileCaseChainWithM.eq_def] at core
          cases fitsEq :
              Fir.Wasm.caseConstructorTagFits
                (Fir.Wasm.caseDiscriminatorMode context discr) info with
          | false =>
              simp only [fitsEq, Bool.false_eq_true, ↓reduceIte] at core
              change
                some (Except.error (Fir.Wasm.CompileError.malformed
                  s!"constructor tag {info.cidx} does not fit the case discriminator ABI")) =
                    some (Except.ok result) at core
              cases core
          | true =>
              simp only [fitsEq, ↓reduceIte] at core
              cases thenCore :
                  Fir.Wasm.compileCodeCore context code with
              | none =>
                  rw [thenCore] at core
                  cases core
              | some thenResult =>
                  cases thenResult with
                  | error error =>
                      rw [thenCore] at core
                      cases core
                  | ok thenBody =>
                      cases elseCore :
                          Fir.Wasm.compileCaseChainWithM
                            (Fir.Wasm.compileCodeCore context)
                            (Fir.Wasm.caseDiscriminatorMode context discr)
                            discr alts fallback with
                      | none =>
                          rw [thenCore, elseCore] at core
                          cases core
                      | some elseResult =>
                          cases elseResult with
                          | error error =>
                              rw [thenCore, elseCore] at core
                              cases core
                          | ok elseBody =>
                              rw [thenCore, elseCore] at core
                              injection core with resultEq
                              injection resultEq with resultEq
                              subst result
                              have thenCompiled :
                                  Fir.Wasm.compileCode context code =
                                    .ok thenBody :=
                                Fir.Wasm.finishCompileResult_eq_ok_iff.mpr
                                  thenCore
                              have elseCompiled :
                                  Fir.Wasm.compileCaseChain context discr alts
                                      fallback =
                                    .ok elseBody :=
                                ih elseCore
                              have elseCompiled' :
                                  Fir.Wasm.compileCaseChainWithM
                                      (Fir.Wasm.compileCode context)
                                      (Fir.Wasm.caseDiscriminatorMode context
                                        discr)
                                      discr alts fallback =
                                    .ok elseBody :=
                                elseCompiled
                              change
                                Fir.Wasm.compileCaseChainWithM
                                    (Fir.Wasm.compileCode context)
                                    (Fir.Wasm.caseDiscriminatorMode context
                                      discr)
                                    discr (.ctorAlt info code :: alts)
                                    fallback =
                                  .ok
                                    (Fir.Wasm.caseTagTest
                                        (Fir.Wasm.caseDiscriminatorMode context
                                          discr)
                                        discr info ++
                                      [.i32Eq,
                                        .ifElse thenBody elseBody])
                              rw [Fir.Wasm.compileCaseChainWithM.eq_def]
                              simp only [fitsEq, ↓reduceIte]
                              rw [thenCompiled, elseCompiled']
                              rfl

/--
Generic inverse for production case compilation and Talos adaptation.
Successful `CodeAdapted (.cases cases)` yields the actual compiled fallback and
constructor-chain relation; clients do not supply either witness.
-/
theorem CodeAdapted.cases_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {cases : LCNF.Cases .impure}
    {target : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels (.cases cases)
        target) :
    CasesAdapted context sourceModule sourceFunction labels cases target := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases fallbackCore :
      Fir.Wasm.compileCaseFallbackWithM
        (Fir.Wasm.compileCodeCore context) cases.alts.toList with
  | none =>
      rw [fallbackCore] at core
      cases core
  | some fallbackResult =>
      cases fallbackResult with
      | error error =>
          rw [fallbackCore] at core
          cases core
      | ok fallback =>
          rw [fallbackCore] at core
          change
            Fir.Wasm.compileCaseChainWithM
                (Fir.Wasm.compileCodeCore context)
                (Fir.Wasm.caseDiscriminatorMode context cases.discr)
                cases.discr cases.alts.toList fallback =
              some (.ok symbolic) at core
          exact
            ⟨fallback,
              compileCaseFallback_eq_ok_of_core fallbackCore,
              symbolic,
              compileCaseChain_eq_ok_of_core core,
              targetCompiled⟩

/-- Invert the empty adapted case chain to its adapted fallback. -/
theorem CaseChainAdapted.nil_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {discr : FVarId}
    {fallback : List Fir.Wasm.Instruction}
    {target : Wasm.Program}
    (adapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr []
        fallback target) :
    instructions sourceModule sourceFunction labels fallback = .ok target := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  change
    Fir.Wasm.compileCaseChainWithM (Fir.Wasm.compileCode context)
        (Fir.Wasm.caseDiscriminatorMode context discr)
        discr [] fallback =
      .ok symbolic at compiled
  rw [Fir.Wasm.compileCaseChainWithM.eq_def] at compiled
  injection compiled with symbolicEq
  subst symbolic
  exact targetCompiled

/-- Defaults do not contribute a test to an adapted constructor chain. -/
theorem CaseChainAdapted.default_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {discr : FVarId}
    {code : LCNF.Code .impure}
    {alts : List (LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {target : Wasm.Program}
    (adapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr
        (.default code :: alts) fallback target) :
    CaseChainAdapted context sourceModule sourceFunction labels discr alts
      fallback target := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  refine ⟨symbolic, ?_, targetCompiled⟩
  change
    Fir.Wasm.compileCaseChainWithM (Fir.Wasm.compileCode context)
        (Fir.Wasm.caseDiscriminatorMode context discr)
        discr (.default code :: alts) fallback =
      .ok symbolic at compiled
  rw [Fir.Wasm.compileCaseChainWithM.eq_def] at compiled
  exact compiled

/--
Invert one adapted object-constructor test.

The executable chain compiler supplies the branch bodies and suffix; the
numeric adapter supplies the shared discriminator/import indices and exact
Talos `if`. No target component is an input to the theorem.
-/
theorem CaseChainAdapted.objectConstructor_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {discr : FVarId}
    {info : LCNF.CtorInfo}
    {code : LCNF.Code .impure}
    {alts : List (LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {target : Wasm.Program}
    (modeEq :
      Fir.Wasm.caseDiscriminatorMode context discr = .objectTag)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (adapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr
        (.ctorAlt info code :: alts) fallback target) :
    ∃ thenTarget elseTarget discrIndex getTagIndex,
      CodeAdapted context sourceModule sourceFunction labels code thenTarget ∧
      CaseChainAdapted context sourceModule sourceFunction labels discr alts
          fallback elseTarget ∧
      findFVar? (functionBindings sourceFunction) discr = some discrIndex ∧
      callIndex? sourceModule (.runtime .getTag) = some getTagIndex ∧
      target =
        [.localGet discrIndex, .call getTagIndex,
          .const (UInt32.ofNat info.cidx), .eq,
          .iff 0 0 thenTarget elseTarget] := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  change
    Fir.Wasm.compileCaseChainWithM (Fir.Wasm.compileCode context)
        (Fir.Wasm.caseDiscriminatorMode context discr)
        discr (.ctorAlt info code :: alts) fallback =
      .ok symbolic at compiled
  rw [Fir.Wasm.compileCaseChainWithM.eq_def] at compiled
  simp only [Fir.Wasm.caseConstructorTagFits, modeEq, fits, ↓reduceIte]
    at compiled
  cases thenCompiled : Fir.Wasm.compileCode context code with
  | error error =>
      rw [thenCompiled] at compiled
      cases compiled
  | ok thenBody =>
      cases elseCompiled :
          Fir.Wasm.compileCaseChain context discr alts fallback with
      | error error =>
          change
            Fir.Wasm.compileCaseChainWithM (Fir.Wasm.compileCode context)
                (Fir.Wasm.caseDiscriminatorMode context discr)
                discr alts fallback =
              .error error at elseCompiled
          have elseCompiled' :
              Fir.Wasm.compileCaseChainWithM
                  (Fir.Wasm.compileCode context) .objectTag
                  discr alts fallback =
                .error error := by
            simpa only [modeEq] using elseCompiled
          rw [thenCompiled, elseCompiled'] at compiled
          cases compiled
      | ok elseBody =>
          change
            Fir.Wasm.compileCaseChainWithM (Fir.Wasm.compileCode context)
                (Fir.Wasm.caseDiscriminatorMode context discr)
                discr alts fallback =
              .ok elseBody at elseCompiled
          have elseCompiled' :
              Fir.Wasm.compileCaseChainWithM
                  (Fir.Wasm.compileCode context) .objectTag
                  discr alts fallback =
                .ok elseBody := by
            simpa only [modeEq] using elseCompiled
          rw [thenCompiled, elseCompiled'] at compiled
          injection compiled with symbolicEq
          subst symbolic
          cases discrFound :
              findFVar? (functionBindings sourceFunction) discr with
          | none =>
              change findFVar?
                (sourceFunction.params.toList ++ sourceFunction.locals.toList)
                discr = none at discrFound
              simp [Fir.Wasm.caseTagTest, instructions, instruction, discrFound,
                Bind.bind, Except.bind, Pure.pure, Except.pure]
                at targetCompiled
          | some discrIndex =>
              change findFVar?
                (sourceFunction.params.toList ++ sourceFunction.locals.toList)
                discr = some discrIndex at discrFound
              cases getTagFound :
                  callIndex? sourceModule (.runtime .getTag) with
              | none =>
                  simp [Fir.Wasm.caseTagTest, instructions, instruction,
                    discrFound, getTagFound, Bind.bind, Except.bind,
                    Pure.pure, Except.pure] at targetCompiled
              | some getTagIndex =>
                  cases thenAdapted :
                      instructions sourceModule sourceFunction labels
                        thenBody with
                  | error error =>
                      simp [Fir.Wasm.caseTagTest, instructions, instruction,
                        discrFound, getTagFound, thenAdapted, Bind.bind,
                        Except.bind, Pure.pure, Except.pure] at targetCompiled
                  | ok thenTarget =>
                      cases elseAdapted :
                          instructions sourceModule sourceFunction labels
                            elseBody with
                      | error error =>
                          simp [Fir.Wasm.caseTagTest, instructions, instruction,
                            discrFound, getTagFound, thenAdapted, elseAdapted,
                            Bind.bind, Except.bind, Pure.pure, Except.pure]
                            at targetCompiled
                      | ok elseTarget =>
                          simp [Fir.Wasm.caseTagTest, instructions, instruction,
                            discrFound, getTagFound, thenAdapted, elseAdapted,
                            Bind.bind, Except.bind, Pure.pure, Except.pure]
                            at targetCompiled
                          exact
                            ⟨thenTarget, elseTarget, discrIndex, getTagIndex,
                              ⟨thenBody, thenCompiled, thenAdapted⟩,
                              ⟨elseBody, elseCompiled, elseAdapted⟩,
                              rfl, rfl, targetCompiled.symm⟩

/--
Invert one adapted scalar `UInt8` constructor test.

Production compilation supplies the branch bodies and suffix. Numeric
adaptation supplies the discriminator local and exact direct compare/`if`;
there is no runtime `getTag` import in this discriminator mode.
-/
theorem CaseChainAdapted.scalarUInt8Constructor_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {discr : FVarId}
    {info : LCNF.CtorInfo}
    {code : LCNF.Code .impure}
    {alts : List (LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {target : Wasm.Program}
    (modeEq :
      Fir.Wasm.caseDiscriminatorMode context discr = .scalarUInt8)
    (fits : Fir.Wasm.constructorTagFitsUInt8 info = true)
    (adapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr
        (.ctorAlt info code :: alts) fallback target) :
    ∃ thenTarget elseTarget discrIndex,
      CodeAdapted context sourceModule sourceFunction labels code thenTarget ∧
      CaseChainAdapted context sourceModule sourceFunction labels discr alts
          fallback elseTarget ∧
      findFVar? (functionBindings sourceFunction) discr = some discrIndex ∧
      target =
        [.localGet discrIndex, .const (UInt32.ofNat info.cidx), .eq,
          .iff 0 0 thenTarget elseTarget] := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  change
    Fir.Wasm.compileCaseChainWithM (Fir.Wasm.compileCode context)
        (Fir.Wasm.caseDiscriminatorMode context discr)
        discr (.ctorAlt info code :: alts) fallback =
      .ok symbolic at compiled
  rw [Fir.Wasm.compileCaseChainWithM.eq_def] at compiled
  simp only [Fir.Wasm.caseConstructorTagFits, modeEq, fits, ↓reduceIte]
    at compiled
  cases thenCompiled : Fir.Wasm.compileCode context code with
  | error error =>
      rw [thenCompiled] at compiled
      cases compiled
  | ok thenBody =>
      cases elseCompiled :
          Fir.Wasm.compileCaseChain context discr alts fallback with
      | error error =>
          change
            Fir.Wasm.compileCaseChainWithM (Fir.Wasm.compileCode context)
                (Fir.Wasm.caseDiscriminatorMode context discr)
                discr alts fallback =
              .error error at elseCompiled
          have elseCompiled' :
              Fir.Wasm.compileCaseChainWithM
                  (Fir.Wasm.compileCode context) .scalarUInt8
                  discr alts fallback =
                .error error := by
            simpa only [modeEq] using elseCompiled
          rw [thenCompiled, elseCompiled'] at compiled
          cases compiled
      | ok elseBody =>
          change
            Fir.Wasm.compileCaseChainWithM (Fir.Wasm.compileCode context)
                (Fir.Wasm.caseDiscriminatorMode context discr)
                discr alts fallback =
              .ok elseBody at elseCompiled
          have elseCompiled' :
              Fir.Wasm.compileCaseChainWithM
                  (Fir.Wasm.compileCode context) .scalarUInt8
                  discr alts fallback =
                .ok elseBody := by
            simpa only [modeEq] using elseCompiled
          rw [thenCompiled, elseCompiled'] at compiled
          injection compiled with symbolicEq
          subst symbolic
          cases discrFound :
              findFVar? (functionBindings sourceFunction) discr with
          | none =>
              change findFVar?
                (sourceFunction.params.toList ++ sourceFunction.locals.toList)
                discr = none at discrFound
              simp [Fir.Wasm.caseTagTest, instructions, instruction, discrFound,
                Bind.bind, Except.bind, Pure.pure, Except.pure]
                at targetCompiled
          | some discrIndex =>
              change findFVar?
                (sourceFunction.params.toList ++ sourceFunction.locals.toList)
                discr = some discrIndex at discrFound
              cases thenAdapted :
                  instructions sourceModule sourceFunction labels thenBody with
              | error error =>
                  simp [Fir.Wasm.caseTagTest, instructions, instruction,
                    discrFound, thenAdapted, Bind.bind, Except.bind,
                    Pure.pure, Except.pure] at targetCompiled
              | ok thenTarget =>
                  cases elseAdapted :
                      instructions sourceModule sourceFunction labels
                        elseBody with
                  | error error =>
                      simp [Fir.Wasm.caseTagTest, instructions, instruction,
                        discrFound, thenAdapted, elseAdapted, Bind.bind,
                        Except.bind, Pure.pure, Except.pure] at targetCompiled
                  | ok elseTarget =>
                      simp [Fir.Wasm.caseTagTest, instructions, instruction,
                        discrFound, thenAdapted, elseAdapted, Bind.bind,
                        Except.bind, Pure.pure, Except.pure] at targetCompiled
                      exact
                        ⟨thenTarget, elseTarget, discrIndex,
                          ⟨thenBody, thenCompiled, thenAdapted⟩,
                          ⟨elseBody, elseCompiled, elseAdapted⟩,
                          rfl, targetCompiled.symm⟩

/--
Invert production compilation and adaptation of a singleton constructor case.
The selected arm, discriminator local, concrete `getTag` import, and exact
generated test are recovered from the compiler result; none is supplied by a
source evaluation or a translation certificate.
-/
theorem CodeAdapted.singleObjectConstructorCases_eq
    {context : Fir.Wasm.Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {labels : List FVarId}
    {cases : LCNF.Cases .impure} {info : LCNF.CtorInfo}
    {selected : LCNF.Code .impure} {target : Wasm.Program}
    (altsEq : cases.alts.toList = [.ctorAlt info selected])
    (modeEq : Fir.Wasm.caseDiscriminatorMode context cases.discr = .objectTag)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (adapted : CodeAdapted context sourceModule sourceFunction labels
      (.cases cases) target) :
    ∃ selectedTarget discrIndex getTagIndex,
      CodeAdapted context sourceModule sourceFunction labels selected
          selectedTarget ∧
      findFVar? (functionBindings sourceFunction) cases.discr =
        some discrIndex ∧
      callIndex? sourceModule (.runtime .getTag) = some getTagIndex ∧
      target = [.localGet discrIndex, .call getTagIndex,
        .const (UInt32.ofNat info.cidx), .eq,
        .iff 0 0 selectedTarget [.unreachable]] := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  rw [altsEq] at core
  simp only [Fir.Wasm.compileCaseFallbackWithM,
    Fir.Wasm.compileCaseChainWithM, Fir.Wasm.isDefaultAlt,
    Fir.Wasm.caseConstructorTagFits, modeEq, fits, ↓reduceIte] at core
  cases selectedCore : Fir.Wasm.compileCodeCore context selected with
  | none =>
      rw [selectedCore] at core
      change none = some (Except.ok symbolic) at core
      cases core
  | some selectedResult =>
      cases selectedResult with
      | error error =>
          rw [selectedCore] at core
          change some (Except.error error) = some (Except.ok symbolic) at core
          cases core
      | ok selectedCode =>
          rw [selectedCore] at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have selectedCompiled :
              Fir.Wasm.compileCode context selected = .ok selectedCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr selectedCore
          cases discrFound :
              findFVar? (functionBindings sourceFunction) cases.discr with
          | none =>
              change findFVar?
                (sourceFunction.params.toList ++ sourceFunction.locals.toList)
                cases.discr = none at discrFound
              simp [Fir.Wasm.caseTagTest, instructions, instruction, discrFound,
                Bind.bind, Except.bind, Pure.pure, Except.pure]
                at targetCompiled
          | some discrIndex =>
              change findFVar?
                (sourceFunction.params.toList ++ sourceFunction.locals.toList)
                cases.discr = some discrIndex at discrFound
              cases getTagFound :
                  callIndex? sourceModule (.runtime .getTag) with
              | none =>
                  simp [Fir.Wasm.caseTagTest, instructions, instruction,
                    discrFound, getTagFound, Bind.bind, Except.bind,
                    Pure.pure, Except.pure] at targetCompiled
              | some getTagIndex =>
                  cases selectedAdapted :
                      instructions sourceModule sourceFunction labels
                        selectedCode with
                  | error error =>
                      simp [Fir.Wasm.caseTagTest, instructions, instruction,
                        discrFound, getTagFound, selectedAdapted,
                        Bind.bind, Except.bind, Pure.pure, Except.pure]
                        at targetCompiled
                  | ok selectedTarget =>
                      simp [Fir.Wasm.caseTagTest, instructions, instruction,
                        discrFound, getTagFound, selectedAdapted,
                        Bind.bind, Except.bind, Pure.pure, Except.pure]
                        at targetCompiled
                      exact ⟨selectedTarget, discrIndex, getTagIndex,
                        ⟨selectedCode, selectedCompiled, selectedAdapted⟩,
                        rfl, rfl, targetCompiled.symm⟩

/--
Invert production compilation and adaptation of two ordered object-constructor
arms followed by a default. All three adapted branch targets and the complete
nested test are recovered from the executable compiler and adapter.
-/
theorem CodeAdapted.twoObjectConstructorDefaultCases_eq
    {context : Fir.Wasm.Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {labels : List FVarId}
    {cases : LCNF.Cases .impure}
    {firstInfo secondInfo : LCNF.CtorInfo}
    {firstBranch secondBranch defaultBranch : LCNF.Code .impure}
    {target : Wasm.Program}
    (altsEq : cases.alts.toList =
      [.ctorAlt firstInfo firstBranch, .ctorAlt secondInfo secondBranch,
        .default defaultBranch])
    (modeEq : Fir.Wasm.caseDiscriminatorMode context cases.discr = .objectTag)
    (firstFits : Fir.Wasm.constructorTagFitsI32 firstInfo = true)
    (secondFits : Fir.Wasm.constructorTagFitsI32 secondInfo = true)
    (adapted : CodeAdapted context sourceModule sourceFunction labels
      (.cases cases) target) :
    ∃ firstTarget secondTarget defaultTarget discrIndex getTagIndex,
      CodeAdapted context sourceModule sourceFunction labels firstBranch
          firstTarget ∧
      CodeAdapted context sourceModule sourceFunction labels secondBranch
          secondTarget ∧
      CodeAdapted context sourceModule sourceFunction labels defaultBranch
          defaultTarget ∧
      findFVar? (functionBindings sourceFunction) cases.discr =
        some discrIndex ∧
      callIndex? sourceModule (.runtime .getTag) = some getTagIndex ∧
      target =
        [.localGet discrIndex, .call getTagIndex,
          .const (UInt32.ofNat firstInfo.cidx), .eq,
          .iff 0 0 firstTarget
            [.localGet discrIndex, .call getTagIndex,
              .const (UInt32.ofNat secondInfo.cidx), .eq,
              .iff 0 0 secondTarget defaultTarget]] := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  rw [altsEq] at core
  simp only [Fir.Wasm.compileCaseFallbackWithM,
    Fir.Wasm.compileCaseChainWithM, Fir.Wasm.isDefaultAlt,
    List.find?,
    Fir.Wasm.caseConstructorTagFits, modeEq, firstFits, secondFits,
    ↓reduceIte] at core
  cases defaultCore : Fir.Wasm.compileCodeCore context defaultBranch with
  | none =>
      rw [defaultCore] at core
      cases core
  | some defaultResult =>
      cases defaultResult with
      | error error =>
          rw [defaultCore] at core
          cases core
      | ok defaultCode =>
          cases firstCore :
              Fir.Wasm.compileCodeCore context firstBranch with
          | none =>
              rw [defaultCore, firstCore] at core
              cases core
          | some firstResult =>
              cases firstResult with
              | error error =>
                  rw [defaultCore, firstCore] at core
                  cases core
              | ok firstCode =>
                  cases secondCore :
                      Fir.Wasm.compileCodeCore context secondBranch with
                  | none =>
                      rw [defaultCore, firstCore, secondCore] at core
                      cases core
                  | some secondResult =>
                      cases secondResult with
                      | error error =>
                          rw [defaultCore, firstCore, secondCore] at core
                          cases core
                      | ok secondCode =>
                          rw [defaultCore, firstCore, secondCore] at core
                          injection core with symbolicEq
                          injection symbolicEq with symbolicEq
                          subst symbolic
                          have firstCompiled :
                              Fir.Wasm.compileCode context firstBranch =
                                .ok firstCode :=
                            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr firstCore
                          have secondCompiled :
                              Fir.Wasm.compileCode context secondBranch =
                                .ok secondCode :=
                            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr secondCore
                          have defaultCompiled :
                              Fir.Wasm.compileCode context defaultBranch =
                                .ok defaultCode :=
                            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr
                              defaultCore
                          cases discrFound :
                              findFVar?
                                (functionBindings sourceFunction)
                                cases.discr with
                          | none =>
                              change findFVar?
                                (sourceFunction.params.toList ++
                                  sourceFunction.locals.toList)
                                cases.discr = none at discrFound
                              simp [Fir.Wasm.caseTagTest, instructions,
                                instruction, discrFound, Bind.bind,
                                Except.bind, Pure.pure, Except.pure]
                                at targetCompiled
                          | some discrIndex =>
                              change findFVar?
                                (sourceFunction.params.toList ++
                                  sourceFunction.locals.toList)
                                cases.discr = some discrIndex at discrFound
                              cases getTagFound :
                                  callIndex? sourceModule
                                    (.runtime .getTag) with
                              | none =>
                                  simp [Fir.Wasm.caseTagTest, instructions,
                                    instruction, discrFound, getTagFound,
                                    Bind.bind, Except.bind, Pure.pure,
                                    Except.pure] at targetCompiled
                              | some getTagIndex =>
                                  cases firstAdapted :
                                      instructions sourceModule sourceFunction
                                        labels firstCode with
                                  | error error =>
                                      simp [Fir.Wasm.caseTagTest,
                                        instructions, instruction, discrFound,
                                        getTagFound, firstAdapted, Bind.bind,
                                        Except.bind, Pure.pure, Except.pure]
                                        at targetCompiled
                                  | ok firstTarget =>
                                      cases secondAdapted :
                                          instructions sourceModule
                                            sourceFunction labels secondCode with
                                      | error error =>
                                          simp [Fir.Wasm.caseTagTest,
                                            instructions, instruction,
                                            discrFound, getTagFound,
                                            firstAdapted, secondAdapted,
                                            Bind.bind, Except.bind, Pure.pure,
                                            Except.pure] at targetCompiled
                                      | ok secondTarget =>
                                          cases defaultAdapted :
                                              instructions sourceModule
                                                sourceFunction labels
                                                defaultCode with
                                          | error error =>
                                              simp [Fir.Wasm.caseTagTest,
                                                instructions, instruction,
                                                discrFound, getTagFound,
                                                firstAdapted, secondAdapted,
                                                defaultAdapted, Bind.bind,
                                                Except.bind, Pure.pure,
                                                Except.pure] at targetCompiled
                                          | ok defaultTarget =>
                                              simp [Fir.Wasm.caseTagTest,
                                                instructions, instruction,
                                                discrFound, getTagFound,
                                                firstAdapted, secondAdapted,
                                                defaultAdapted, Bind.bind,
                                                Except.bind, Pure.pure,
                                                Except.pure] at targetCompiled
                                              exact
                                                ⟨firstTarget, secondTarget,
                                                  defaultTarget, discrIndex,
                                                  getTagIndex,
                                                  ⟨firstCode, firstCompiled,
                                                    firstAdapted⟩,
                                                  ⟨secondCode, secondCompiled,
                                                    secondAdapted⟩,
                                                  ⟨defaultCode,
                                                    defaultCompiled,
                                                    defaultAdapted⟩,
                                                  rfl, rfl,
                                                  targetCompiled.symm⟩

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

/--
The source-order physical constructor operands produced by compiled arguments
refine the corresponding evaluated source values at their compiler-selected
ABI kinds. This relation is target-numbering independent and contains no
allocation or execution witness.
-/
inductive ConstructorArgumentsRelated (witness : RefinementWitness) :
    List AbiKind → List Wasm.Value → List Value → Prop where
  | nil : ConstructorArgumentsRelated witness [] [] []
  | cons
      (head : PhysicalValueRel witness kind physical semantic)
      (rest :
        ConstructorArgumentsRelated witness kinds physicals semanticValues) :
      ConstructorArgumentsRelated witness (kind :: kinds)
        (physical :: physicals) (semantic :: semanticValues)

/-- Compiled argument refinement preserves source/ABI arity. -/
theorem ConstructorArgumentsRelated.semanticLength
    {witness : RefinementWitness} {kinds : List AbiKind}
    {physicals : List Wasm.Value} {semanticValues : List Value}
    (related :
      ConstructorArgumentsRelated witness kinds physicals semanticValues) :
    semanticValues.length = kinds.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/--
An object-field ABI kind rules out every non-i32 physical lane. The remaining
word is exactly the one related to the source field.
-/
theorem PhysicalValueRel.objectFieldWord
    {witness : RefinementWitness} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : PhysicalValueRel witness kind physical semantic)
    (objectField : kind.isObjectField = true) :
    ∃ word,
      physical = .i32 (UInt32.ofNat word.value) ∧
        ValueRel witness kind (.word32 word) semantic := by
  cases related with
  | word32 valueRelated =>
      exact ⟨_, rfl, valueRelated⟩
  | word64 valueRelated =>
      cases valueRelated <;> simp [AbiKind.isObjectField] at objectField
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

/--
The compiled/evaluated argument relation constructively decodes every
object-field operand and preserves its pointwise source-value refinement.
-/
theorem ConstructorArgumentsRelated.decodeObjectWords
    {witness : RefinementWitness} {fieldKinds : List AbiKind}
    {physicalArgs : List Wasm.Value} {semanticArgs : List Value}
    (related :
      ConstructorArgumentsRelated witness fieldKinds physicalArgs semanticArgs)
    (valid : fieldKinds.all AbiKind.isObjectField = true)
    (start : Nat) :
    ∃ fields,
      decodeConstructorWords start physicalArgs = .ok fields ∧
        fields.length = fieldKinds.length ∧
        ∀ (index : Nat) (kind : AbiKind) (value : Value),
          fieldKinds[index]? = some kind →
          semanticArgs[index]? = some value →
          ∃ word, fields[index]? = some word ∧
            ValueRel witness kind (.word32 word) value := by
  induction related generalizing start with
  | nil =>
      exact ⟨[], by simp [decodeConstructorWords], rfl, by
        intro index kind value kindAt
        simp at kindAt⟩
  | @cons kind physical semantic kinds physicals semanticValues head rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at valid
      obtain ⟨word, physicalEq, headRelated⟩ :=
        head.objectFieldWord valid.1
      obtain ⟨fields, decoded, lengthEq, fieldsRelated⟩ :=
        ih valid.2 (start + 1)
      subst physical
      refine ⟨word :: fields, ?_, by simp [lengthEq], ?_⟩
      · simp [decodeConstructorWords, decoded]
      · intro index actualKind value kindAt valueAt
        cases index with
        | zero =>
            simp at kindAt valueAt
            subst actualKind
            subst value
            exact ⟨word, by simp, headRelated⟩
        | succ index =>
            simp at kindAt valueAt
            obtain ⟨field, fieldAt, fieldRelated⟩ :=
              fieldsRelated index actualKind value kindAt valueAt
            exact ⟨field, by simpa, fieldRelated⟩

/--
The ABI-indexed relation produced by `compileArgs` constructively decodes the
entire Talos operand prefix into W6 lanes. This is the general external-call
counterpart of `decodeObjectWords`: all supported ABI kinds are retained, and
the decoded list remains pointwise related to the evaluated source arguments.
-/
theorem ConstructorArgumentsRelated.decodePhysicalLanes
    {witness : RefinementWitness} {kinds : List AbiKind}
    {physicalArgs : List Wasm.Value} {semanticArgs : List Value}
    (related :
      ConstructorArgumentsRelated witness kinds physicalArgs semanticArgs)
    (start : Nat) :
    ∃ lanes,
      FirTalos.Concrete.decodePhysicalLanes start kinds physicalArgs =
          .ok lanes ∧
        lanes.length = kinds.length ∧
        semanticArgs.length = kinds.length ∧
        ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue) (value : Value),
          kinds[index]? = some kind →
          lanes[index]? = some lane →
          semanticArgs[index]? = some value →
          ValueRel witness kind lane value := by
  induction related generalizing start with
  | nil =>
      exact ⟨[], by simp [FirTalos.Concrete.decodePhysicalLanes], rfl, rfl, by
        intro index kind lane value kindAt
        simp at kindAt⟩
  | @cons kind physical semantic kinds physicals semanticValues head rest ih =>
      obtain ⟨headLane, headDecoded, headRelated⟩ :=
        FirTalos.Concrete.decodePhysicalLane_of_related head
      obtain ⟨lanes, tailDecoded, lanesLength, semanticLength, lanesRelated⟩ :=
        ih (start + 1)
      refine ⟨headLane :: lanes, ?_, by simp [lanesLength],
        by simp [semanticLength], ?_⟩
      · simp [FirTalos.Concrete.decodePhysicalLanes, headDecoded, tailDecoded,
          Bind.bind, Except.bind, pure, Except.pure]
      · intro index actualKind lane value kindAt laneAt valueAt
        cases index with
        | zero =>
            simp at kindAt laneAt valueAt
            subst actualKind
            subst lane
            subst value
            exact headRelated
        | succ index =>
            simp at kindAt laneAt valueAt
            exact lanesRelated index actualKind lane value
              kindAt laneAt valueAt

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
        physicalArgs.length = fieldKinds.length ∧
        ConstructorArgumentsRelated witness fieldKinds physicalArgs
          semanticArgs := by
  induction compiled generalizing targetArguments semanticArgs with
  | nil =>
      have targetEq : targetArguments = [] := by
        simpa [instructions, pure, Except.pure] using adapted.symm
      have semanticEq : semanticArgs = [] := by
        change (Except.ok [] : Except RuntimeFault (List Value)) =
          Except.ok semanticArgs at evaluated
        exact (Except.ok.inj evaluated).symm
      subst targetArguments
      subst semanticArgs
      exact ⟨[], .nil, rfl, .nil⟩
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
          have semanticEq : semanticArgs = .erased :: restValues := by
            rw [List.mapM_cons] at evaluated
            simpa [evalArg, restEvaluated, Functor.map, Except.map, Bind.bind,
              Except.bind, pure, Except.pure] using evaluated.symm
          obtain ⟨physicalArgs, ready, lengthEq, argumentsRelated⟩ :=
            ih restAdapted restEvaluated
          subst targetHead
          subst targetArguments
          subst semanticArgs
          exact ⟨.i32 0 :: physicalArgs, .erased ready, by
            simp [lengthEq], .cons (.word32 .erased) argumentsRelated⟩
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
              obtain ⟨physical, physicalFound, physicalRelated⟩ :=
                stateRelated.resolve sourceLookup localFound kindAt
              have semanticEq : semanticArgs = sourceValue :: restValues := by
                rw [List.mapM_cons] at evaluated
                simpa [evalArg, sourceLookup, restEvaluated, Functor.map,
                  Except.map, Bind.bind, Except.bind, pure, Except.pure] using
                    evaluated.symm
              obtain ⟨physicalArgs, ready, lengthEq, argumentsRelated⟩ :=
                ih restAdapted restEvaluated
              subst targetHead
              subst targetArguments
              subst semanticArgs
              exact ⟨physical :: physicalArgs,
                .localGet physicalFound ready, by simp [lengthEq],
                .cons physicalRelated argumentsRelated⟩

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
        physicalArgs.length = fieldKinds.size ∧
        ConstructorArgumentsRelated witness fieldKinds.toList physicalArgs
          semanticArgs.toList := by
  have characterized := ConstructorArgsCompiled.ofCompileArgs compiled
  unfold evalArgs at evaluated
  rw [Array.mapM_eq_mapM_toList] at evaluated
  cases listEvaluated :
      args.toList.mapM (evalArg sourceEnv) with
  | error fault =>
      rw [listEvaluated] at evaluated
      contradiction
  | ok semanticValues =>
      have semanticEq : semanticArgs = semanticValues.toArray := by
        simpa [listEvaluated] using evaluated.symm
      obtain ⟨physicalArgs, ready, lengthEq, argumentsRelated⟩ :=
        characterized.ready localsAligned adapted listEvaluated stateRelated
      subst semanticArgs
      exact ⟨physicalArgs, ready, by simpa using lengthEq, by simpa using
        argumentsRelated⟩

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
Invert adaptation of a successfully compiled argument prefix followed by one
named declaration call. Unlike the runtime-call corollary above, the recovered
numeric target may denote either an imported external or an internal function;
the resolver/compiler theorem using this lemma determines which case applies.
-/
theorem instructions_append_declaration_call_eq
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {argumentCode : List Fir.Wasm.Instruction}
    {name : Lean.Name} {target : Wasm.Program}
    (adapted :
      instructions sourceModule sourceFunction labels
          (argumentCode ++ [.call (.declaration name)]) = .ok target) :
    ∃ targetArguments callIndex,
      instructions sourceModule sourceFunction labels argumentCode =
          .ok targetArguments ∧
        callIndex? sourceModule (.declaration name) = some callIndex ∧
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
          callIndex? sourceModule (.declaration name) with
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
Production compiler/adaptor inversion for an ordinary reference-count
increment.

Given the source-local compiler equation, successful whole-node adaptation
determines the numeric object slot, runtime-import slot, exact generated unary
call prefix, and independently adapted continuation.
-/
theorem CodeAdapted.inc_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId : FVarId}
    {amount : Nat}
    {check : Bool}
    {objectKind : AbiKind}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.inc objectId amount check false continuation) target) :
    ∃ objectIndex callIndex targetRest,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
          some objectKind ∧
        callIndex? sourceModule (.runtime (.inc amount check)) =
          some callIndex ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          [.localGet objectIndex, .call callIndex] ++ targetRest := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
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
          rw [restResult, objectCompiled] at core
          change
            some (Except.ok
              ([.localGet objectId,
                .call (.runtime (.inc amount check))] ++ restCode)) =
              some (Except.ok symbolic) at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have restCompiled :
              Fir.Wasm.compileCode context continuation = .ok restCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
          cases prefixAdapted :
              instructions sourceModule sourceFunction labels
                [.localGet objectId,
                  .call (.runtime (.inc amount check))] with
          | error error =>
              rw [FirTalos.Correctness.instructions_append, prefixAdapted]
                at targetCompiled
              contradiction
          | ok targetPrefix =>
              cases restAdapted :
                  instructions sourceModule sourceFunction labels restCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append, prefixAdapted,
                    restAdapted] at targetCompiled
                  contradiction
              | ok targetRest =>
                  have targetEq : targetPrefix ++ targetRest = target := by
                    rw [FirTalos.Correctness.instructions_append,
                      prefixAdapted, restAdapted] at targetCompiled
                    exact Except.ok.inj targetCompiled
                  obtain ⟨indices, callIndex, found, callFound, prefixEq⟩ :=
                    instructions_localGets_call_eq
                      (fvarIds := [objectId])
                      (operation := .inc amount check) prefixAdapted
                  cases found with
                  | cons objectFound noMore =>
                      cases noMore
                      obtain ⟨alignedIndex, alignedFound, kindAt⟩ :=
                        localsAligned objectCompiled
                      rw [objectFound] at alignedFound
                      injection alignedFound with indexEq
                      subst alignedIndex
                      refine ⟨_, callIndex, targetRest, objectFound, kindAt,
                        callFound, ⟨restCode, restCompiled, restAdapted⟩, ?_⟩
                      rw [prefixEq] at targetEq
                      exact targetEq.symm

/--
Production compiler/adaptor inversion for an ordinary recursive decrement.

As for increments, the only input compiler fact is the source local's ABI
kind. Successful whole-node adaptation determines both numeric indices, the
exact generated unary decrement call, and the independently adapted
continuation.
-/
theorem CodeAdapted.dec_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId : FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {objectKind : AbiKind}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.dec objectId amount check false objectFields? continuation) target) :
    ∃ objectIndex callIndex targetRest,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
          some objectKind ∧
        callIndex? sourceModule
            (.runtime (.dec amount check objectFields?)) =
          some callIndex ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          [.localGet objectIndex, .call callIndex] ++ targetRest := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
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
          rw [restResult, objectCompiled] at core
          change
            some (Except.ok
              ([.localGet objectId,
                .call (.runtime
                  (.dec amount check objectFields?))] ++ restCode)) =
              some (Except.ok symbolic) at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have restCompiled :
              Fir.Wasm.compileCode context continuation = .ok restCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
          cases prefixAdapted :
              instructions sourceModule sourceFunction labels
                [.localGet objectId,
                  .call (.runtime (.dec amount check objectFields?))] with
          | error error =>
              rw [FirTalos.Correctness.instructions_append, prefixAdapted]
                at targetCompiled
              contradiction
          | ok targetPrefix =>
              cases restAdapted :
                  instructions sourceModule sourceFunction labels restCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append, prefixAdapted,
                    restAdapted] at targetCompiled
                  contradiction
              | ok targetRest =>
                  have targetEq : targetPrefix ++ targetRest = target := by
                    rw [FirTalos.Correctness.instructions_append,
                      prefixAdapted, restAdapted] at targetCompiled
                    exact Except.ok.inj targetCompiled
                  obtain ⟨indices, callIndex, found, callFound, prefixEq⟩ :=
                    instructions_localGets_call_eq
                      (fvarIds := [objectId])
                      (operation := .dec amount check objectFields?)
                      prefixAdapted
                  cases found with
                  | cons objectFound noMore =>
                      cases noMore
                      obtain ⟨alignedIndex, alignedFound, kindAt⟩ :=
                        localsAligned objectCompiled
                      rw [objectFound] at alignedFound
                      injection alignedFound with indexEq
                      subst alignedIndex
                      refine ⟨_, callIndex, targetRest, objectFound, kindAt,
                        callFound, ⟨restCode, restCompiled, restAdapted⟩, ?_⟩
                      rw [prefixEq] at targetEq
                      exact targetEq.symm

/--
Production compiler/adaptor inversion for explicit deletion.

The source-local compiler equation and successful whole-node adaptation
determine the numeric object/import slots, the exact generated unary delete
prefix, and the independently adapted continuation.
-/
theorem CodeAdapted.del_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId : FVarId}
    {objectKind : AbiKind}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, objectKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.del objectId continuation) target) :
    ∃ objectIndex callIndex targetRest,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
          some objectKind ∧
        callIndex? sourceModule (.runtime .delete) = some callIndex ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          [.localGet objectIndex, .call callIndex] ++ targetRest := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases restResult :
      Fir.Wasm.compileCodeCore context continuation with
  | none =>
      rw [objectCompiled, restResult] at core
      change none = some (Except.ok symbolic) at core
      cases core
  | some result =>
      cases result with
      | error error =>
          rw [objectCompiled, restResult] at core
          change
            some (Except.error error) = some (Except.ok symbolic) at core
          have impossible :
              Except.error error = Except.ok symbolic :=
            Option.some.inj core
          cases impossible
      | ok restCode =>
          rw [restResult, objectCompiled] at core
          change
            some (Except.ok
              ([.localGet objectId,
                .call (.runtime .delete)] ++ restCode)) =
              some (Except.ok symbolic) at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have restCompiled :
              Fir.Wasm.compileCode context continuation = .ok restCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
          cases prefixAdapted :
              instructions sourceModule sourceFunction labels
                [.localGet objectId, .call (.runtime .delete)] with
          | error error =>
              rw [FirTalos.Correctness.instructions_append, prefixAdapted]
                at targetCompiled
              contradiction
          | ok targetPrefix =>
              cases restAdapted :
                  instructions sourceModule sourceFunction labels restCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append, prefixAdapted,
                    restAdapted] at targetCompiled
                  contradiction
              | ok targetRest =>
                  have targetEq : targetPrefix ++ targetRest = target := by
                    rw [FirTalos.Correctness.instructions_append,
                      prefixAdapted, restAdapted] at targetCompiled
                    exact Except.ok.inj targetCompiled
                  obtain ⟨indices, callIndex, found, callFound, prefixEq⟩ :=
                    instructions_localGets_call_eq
                      (fvarIds := [objectId])
                      (operation := .delete) prefixAdapted
                  cases found with
                  | cons objectFound noMore =>
                      cases noMore
                      obtain ⟨alignedIndex, alignedFound, kindAt⟩ :=
                        localsAligned objectCompiled
                      rw [objectFound] at alignedFound
                      injection alignedFound with indexEq
                      subst alignedIndex
                      refine ⟨_, callIndex, targetRest, objectFound, kindAt,
                        callFound, ⟨restCode, restCompiled, restAdapted⟩, ?_⟩
                      rw [prefixEq] at targetEq
                      exact targetEq.symm

/--
Production compiler/adaptor inversion for constructor-tag mutation.

The source compiler accepts only an object local for this operation. Successful
whole-node adaptation determines the numeric object/import slots, the exact
generated unary tag-setter prefix, and the independently adapted continuation.
-/
theorem CodeAdapted.setTag_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId : FVarId}
    {tag : Nat}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, .object))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.setTag objectId tag continuation) target) :
    ∃ objectIndex callIndex targetRest,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
          some .object ∧
        callIndex? sourceModule (.runtime (.setTag tag)) = some callIndex ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          [.localGet objectIndex, .call callIndex] ++ targetRest := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases restResult :
      Fir.Wasm.compileCodeCore context continuation with
  | none =>
      rw [objectCompiled, restResult] at core
      change none = some (Except.ok symbolic) at core
      cases core
  | some result =>
      cases result with
      | error error =>
          rw [objectCompiled, restResult] at core
          change
            some (Except.error error) = some (Except.ok symbolic) at core
          have impossible :
              Except.error error = Except.ok symbolic :=
            Option.some.inj core
          cases impossible
      | ok restCode =>
          rw [restResult, objectCompiled] at core
          change
            some (Except.ok
              ([.localGet objectId,
                .call (.runtime (.setTag tag))] ++ restCode)) =
              some (Except.ok symbolic) at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have restCompiled :
              Fir.Wasm.compileCode context continuation = .ok restCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
          cases prefixAdapted :
              instructions sourceModule sourceFunction labels
                [.localGet objectId, .call (.runtime (.setTag tag))] with
          | error error =>
              rw [FirTalos.Correctness.instructions_append, prefixAdapted]
                at targetCompiled
              contradiction
          | ok targetPrefix =>
              cases restAdapted :
                  instructions sourceModule sourceFunction labels restCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append, prefixAdapted,
                    restAdapted] at targetCompiled
                  contradiction
              | ok targetRest =>
                  have targetEq : targetPrefix ++ targetRest = target := by
                    rw [FirTalos.Correctness.instructions_append,
                      prefixAdapted, restAdapted] at targetCompiled
                    exact Except.ok.inj targetCompiled
                  obtain ⟨indices, callIndex, found, callFound, prefixEq⟩ :=
                    instructions_localGets_call_eq
                      (fvarIds := [objectId])
                      (operation := .setTag tag) prefixAdapted
                  cases found with
                  | cons objectFound noMore =>
                      cases noMore
                      obtain ⟨alignedIndex, alignedFound, kindAt⟩ :=
                        localsAligned objectCompiled
                      rw [objectFound] at alignedFound
                      injection alignedFound with indexEq
                      subst alignedIndex
                      refine ⟨_, callIndex, targetRest, objectFound, kindAt,
                        callFound, ⟨restCode, restCompiled, restAdapted⟩, ?_⟩
                      rw [prefixEq] at targetEq
                      exact targetEq.symm

/-- A successful object-local compiler equation also supplies the canonical
single-instruction compilation of that local as an LCNF argument. -/
theorem compileArg_fvar_of_getLocal
    {context : Fir.Wasm.Context} {fieldId : FVarId} {fieldKind : AbiKind}
    (compiled :
      Fir.Wasm.getLocal context fieldId =
        .ok (.localGet fieldId, fieldKind)) :
    Fir.Wasm.compileArg context (.fvar fieldId) =
      .ok ([.localGet fieldId], fieldKind) := by
  cases found : Fir.Wasm.findLocalKind? context.localKinds fieldId with
  | none =>
      simp [Fir.Wasm.getLocal, found] at compiled
  | some kind =>
      simp [Fir.Wasm.getLocal, found] at compiled
      subst kind
      simp [Fir.Wasm.compileArg, found]

/--
Production compiler/adaptor inversion for FVar object-field mutation.

The two source-local compiler equations and successful whole-node adaptation
determine both numeric local slots, the object-set import, the exact generated
binary prefix, and the independently adapted continuation.
-/
theorem CodeAdapted.objectSetFVar_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId fieldId : FVarId}
    {index : Nat}
    {fieldKind : AbiKind}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, .object))
    (fieldCompiled :
      Fir.Wasm.getLocal context fieldId =
        .ok (.localGet fieldId, fieldKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.oset objectId index (.fvar fieldId) continuation) target) :
    ∃ objectIndex fieldIndex callIndex targetRest,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
          some .object ∧
        findFVar? (functionBindings sourceFunction) fieldId =
          some fieldIndex ∧
        (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd =
          some fieldKind ∧
        callIndex? sourceModule (.runtime (.objectSet index fieldKind)) =
          some callIndex ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          [.localGet objectIndex, .localGet fieldIndex, .call callIndex] ++
            targetRest := by
  have fieldArgCompiled :=
    compileArg_fvar_of_getLocal fieldCompiled
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases restResult :
      Fir.Wasm.compileCodeCore context continuation with
  | none =>
      rw [objectCompiled, fieldArgCompiled, restResult] at core
      change none = some (Except.ok symbolic) at core
      cases core
  | some result =>
      cases result with
      | error error =>
          rw [objectCompiled, fieldArgCompiled, restResult] at core
          change
            some (Except.error error) = some (Except.ok symbolic) at core
          have impossible :
              Except.error error = Except.ok symbolic :=
            Option.some.inj core
          cases impossible
      | ok restCode =>
          rw [objectCompiled, fieldArgCompiled, restResult] at core
          change
            some (Except.ok
              ([.localGet objectId, .localGet fieldId,
                .call (.runtime (.objectSet index fieldKind))] ++ restCode)) =
              some (Except.ok symbolic) at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have restCompiled :
              Fir.Wasm.compileCode context continuation = .ok restCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
          cases prefixAdapted :
              instructions sourceModule sourceFunction labels
                [.localGet objectId, .localGet fieldId,
                  .call (.runtime (.objectSet index fieldKind))] with
          | error error =>
              rw [FirTalos.Correctness.instructions_append, prefixAdapted]
                at targetCompiled
              contradiction
          | ok targetPrefix =>
              cases restAdapted :
                  instructions sourceModule sourceFunction labels restCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append, prefixAdapted,
                    restAdapted] at targetCompiled
                  contradiction
              | ok targetRest =>
                  have targetEq : targetPrefix ++ targetRest = target := by
                    rw [FirTalos.Correctness.instructions_append,
                      prefixAdapted, restAdapted] at targetCompiled
                    exact Except.ok.inj targetCompiled
                  obtain ⟨indices, callIndex, found, callFound, prefixEq⟩ :=
                    instructions_localGets_call_eq
                      (fvarIds := [objectId, fieldId])
                      (operation := .objectSet index fieldKind) prefixAdapted
                  cases found with
                  | cons objectFound found =>
                      cases found with
                      | cons fieldFound noMore =>
                          cases noMore
                          obtain ⟨alignedObjectIndex, alignedObjectFound,
                              objectKindAt⟩ :=
                            localsAligned objectCompiled
                          rw [objectFound] at alignedObjectFound
                          injection alignedObjectFound with objectIndexEq
                          subst alignedObjectIndex
                          obtain ⟨alignedFieldIndex, alignedFieldFound,
                              fieldKindAt⟩ :=
                            localsAligned fieldCompiled
                          rw [fieldFound] at alignedFieldFound
                          injection alignedFieldFound with fieldIndexEq
                          subst alignedFieldIndex
                          refine ⟨_, _, callIndex, targetRest, objectFound,
                            objectKindAt, fieldFound, fieldKindAt, callFound,
                            ⟨restCode, restCompiled, restAdapted⟩, ?_⟩
                          rw [prefixEq] at targetEq
                          exact targetEq.symm

/--
Invert the exact adapter prefix emitted for an erased object-field write.

The erased argument has no source local: compilation emits the canonical
wasm32 zero between the object local and the runtime call. Successful
adaptation therefore determines only the object-local and import indices.
-/
theorem instructions_localGet_erased_call_eq
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId : FVarId}
    {operation : RuntimeOp}
    {target : Wasm.Program}
    (adapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .i32Const .erased 0,
            .call (.runtime operation)] = .ok target) :
    ∃ objectIndex callIndex,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        callIndex? sourceModule (.runtime operation) = some callIndex ∧
        target =
          [.localGet objectIndex, .const 0, .call callIndex] := by
  obtain ⟨targetObject, afterObject, objectAdapted, afterObjectAdapted,
      targetEq⟩ :=
    instructions_cons_eq_ok adapted
  cases objectFound :
      findFVar? (functionBindings sourceFunction) objectId with
  | none =>
      have objectFound' :
          findFVar?
              (sourceFunction.params.toList ++
                sourceFunction.locals.toList)
              objectId = none := by
        simpa [functionBindings] using objectFound
      have impossible :
          Except.error (AdapterError.unknownLocal objectId) =
            Except.ok targetObject := by
        simpa [instruction, objectFound', pure, Except.pure,
          Bind.bind, Except.bind] using objectAdapted
      cases impossible
  | some objectIndex =>
      have objectFound' :
          findFVar?
              (sourceFunction.params.toList ++
                sourceFunction.locals.toList)
              objectId = some objectIndex := by
        simpa [functionBindings] using objectFound
      have objectTargetEq : targetObject = .localGet objectIndex := by
        simpa [instruction, objectFound', pure, Except.pure,
          Bind.bind, Except.bind] using objectAdapted.symm
      obtain ⟨targetZero, afterZero, zeroAdapted, afterZeroAdapted,
          afterObjectEq⟩ :=
        instructions_cons_eq_ok afterObjectAdapted
      have zeroTargetEq : targetZero = .const 0 := by
        simpa [instruction, pure, Except.pure, Bind.bind, Except.bind] using
          zeroAdapted.symm
      obtain ⟨targetCall, afterCall, callAdapted, afterCallAdapted,
          afterZeroEq⟩ :=
        instructions_cons_eq_ok afterZeroAdapted
      have afterCallEq : afterCall = [] := by
        simpa [instructions, pure, Except.pure, Bind.bind, Except.bind] using
          afterCallAdapted.symm
      cases callFound :
          callIndex? sourceModule (.runtime operation) with
      | none =>
          have impossible :
              Except.error AdapterError.unknownCallTarget =
                Except.ok targetCall := by
            simpa [instruction, callFound, pure, Except.pure, Bind.bind,
              Except.bind] using callAdapted
          cases impossible
      | some callIndex =>
          have callTargetEq : targetCall = .call callIndex := by
            simpa [instruction, callFound, pure, Except.pure, Bind.bind,
              Except.bind] using callAdapted.symm
          exact ⟨objectIndex, callIndex, rfl, rfl, by
            simp [targetEq, afterObjectEq, afterZeroEq, afterCallEq,
              objectTargetEq, zeroTargetEq, callTargetEq]⟩

/--
Production compiler/adaptor inversion for erased object-field mutation.

Successful whole-node adaptation recovers the object-local slot, the erased
object-set import, the canonical zero prefix, and the independently adapted
continuation.
-/
theorem CodeAdapted.objectSetErased_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId : FVarId}
    {index : Nat}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, .object))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.oset objectId index .erased continuation) target) :
    ∃ objectIndex callIndex targetRest,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
          some .object ∧
        callIndex? sourceModule (.runtime (.objectSet index .erased)) =
          some callIndex ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          [.localGet objectIndex, .const 0, .call callIndex] ++ targetRest := by
  have fieldArgCompiled :
      Fir.Wasm.compileArg context (.erased : LCNF.Arg .impure) =
        .ok ([.i32Const .erased 0], .erased) := by
    rfl
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases restResult :
      Fir.Wasm.compileCodeCore context continuation with
  | none =>
      rw [objectCompiled, fieldArgCompiled, restResult] at core
      change none = some (Except.ok symbolic) at core
      cases core
  | some result =>
      cases result with
      | error error =>
          rw [objectCompiled, fieldArgCompiled, restResult] at core
          change
            some (Except.error error) = some (Except.ok symbolic) at core
          have impossible :
              Except.error error = Except.ok symbolic :=
            Option.some.inj core
          cases impossible
      | ok restCode =>
          rw [objectCompiled, fieldArgCompiled, restResult] at core
          change
            some (Except.ok
              ([.localGet objectId, .i32Const .erased 0,
                .call (.runtime (.objectSet index .erased))] ++ restCode)) =
              some (Except.ok symbolic) at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have restCompiled :
              Fir.Wasm.compileCode context continuation = .ok restCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
          cases prefixAdapted :
              instructions sourceModule sourceFunction labels
                [.localGet objectId, .i32Const .erased 0,
                  .call (.runtime (.objectSet index .erased))] with
          | error error =>
              rw [FirTalos.Correctness.instructions_append, prefixAdapted]
                at targetCompiled
              contradiction
          | ok targetPrefix =>
              cases restAdapted :
                  instructions sourceModule sourceFunction labels restCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append, prefixAdapted,
                    restAdapted] at targetCompiled
                  contradiction
              | ok targetRest =>
                  have targetEq : targetPrefix ++ targetRest = target := by
                    rw [FirTalos.Correctness.instructions_append,
                      prefixAdapted, restAdapted] at targetCompiled
                    exact Except.ok.inj targetCompiled
                  obtain ⟨objectIndex, callIndex, objectFound, callFound,
                      prefixEq⟩ :=
                    instructions_localGet_erased_call_eq prefixAdapted
                  obtain ⟨alignedObjectIndex, alignedObjectFound,
                      objectKindAt⟩ :=
                    localsAligned objectCompiled
                  rw [objectFound] at alignedObjectFound
                  injection alignedObjectFound with objectIndexEq
                  subst alignedObjectIndex
                  refine ⟨objectIndex, callIndex, targetRest, objectFound,
                    objectKindAt, callFound,
                    ⟨restCode, restCompiled, restAdapted⟩, ?_⟩
                  rw [prefixEq] at targetEq
                  exact targetEq.symm

/--
Production compiler/adaptor inversion for `USize` field mutation.

The two source-local compiler equations and successful whole-node adaptation
determine both numeric local slots, the `USize`-set import, the exact generated
binary prefix, and the independently adapted continuation.
-/
theorem CodeAdapted.usizeSet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId fieldId : FVarId}
    {index : Nat}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, .object))
    (fieldCompiled :
      Fir.Wasm.getLocal context fieldId =
        .ok (.localGet fieldId, .usize))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.uset objectId index fieldId continuation) target) :
    ∃ objectIndex fieldIndex callIndex targetRest,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
          some .object ∧
        findFVar? (functionBindings sourceFunction) fieldId =
          some fieldIndex ∧
        (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd =
          some .usize ∧
        callIndex? sourceModule (.runtime (.usizeSet index)) =
          some callIndex ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          [.localGet objectIndex, .localGet fieldIndex, .call callIndex] ++
            targetRest := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases restResult :
      Fir.Wasm.compileCodeCore context continuation with
  | none =>
      rw [objectCompiled, fieldCompiled, restResult] at core
      change none = some (Except.ok symbolic) at core
      cases core
  | some result =>
      cases result with
      | error error =>
          rw [objectCompiled, fieldCompiled, restResult] at core
          change
            some (Except.error error) = some (Except.ok symbolic) at core
          have impossible :
              Except.error error = Except.ok symbolic :=
            Option.some.inj core
          cases impossible
      | ok restCode =>
          rw [objectCompiled, fieldCompiled, restResult] at core
          change
            some (Except.ok
              ([.localGet objectId, .localGet fieldId,
                .call (.runtime (.usizeSet index))] ++ restCode)) =
              some (Except.ok symbolic) at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have restCompiled :
              Fir.Wasm.compileCode context continuation = .ok restCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
          cases prefixAdapted :
              instructions sourceModule sourceFunction labels
                [.localGet objectId, .localGet fieldId,
                  .call (.runtime (.usizeSet index))] with
          | error error =>
              rw [FirTalos.Correctness.instructions_append, prefixAdapted]
                at targetCompiled
              contradiction
          | ok targetPrefix =>
              cases restAdapted :
                  instructions sourceModule sourceFunction labels restCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append, prefixAdapted,
                    restAdapted] at targetCompiled
                  contradiction
              | ok targetRest =>
                  have targetEq : targetPrefix ++ targetRest = target := by
                    rw [FirTalos.Correctness.instructions_append,
                      prefixAdapted, restAdapted] at targetCompiled
                    exact Except.ok.inj targetCompiled
                  obtain ⟨indices, callIndex, found, callFound, prefixEq⟩ :=
                    instructions_localGets_call_eq
                      (fvarIds := [objectId, fieldId])
                      (operation := .usizeSet index) prefixAdapted
                  cases found with
                  | cons objectFound found =>
                      cases found with
                      | cons fieldFound noMore =>
                          cases noMore
                          obtain ⟨alignedObjectIndex, alignedObjectFound,
                              objectKindAt⟩ :=
                            localsAligned objectCompiled
                          rw [objectFound] at alignedObjectFound
                          injection alignedObjectFound with objectIndexEq
                          subst alignedObjectIndex
                          obtain ⟨alignedFieldIndex, alignedFieldFound,
                              fieldKindAt⟩ :=
                            localsAligned fieldCompiled
                          rw [fieldFound] at alignedFieldFound
                          injection alignedFieldFound with fieldIndexEq
                          subst alignedFieldIndex
                          refine ⟨_, _, callIndex, targetRest, objectFound,
                            objectKindAt, fieldFound, fieldKindAt, callFound,
                            ⟨restCode, restCompiled, restAdapted⟩, ?_⟩
                          rw [prefixEq] at targetEq
                          exact targetEq.symm

/--
Production compiler/adaptor inversion for packed-scalar field mutation.

The two source-local compiler equations and successful whole-node adaptation
determine both numeric local slots, the kind-indexed scalar-set import, the
exact generated binary prefix, and the independently adapted continuation.
-/
theorem CodeAdapted.scalarSet_eq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {objectId fieldId : FVarId}
    {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {fieldKind : AbiKind}
    {continuation : LCNF.Code .impure}
    {target : Wasm.Program}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (objectCompiled :
      Fir.Wasm.getLocal context objectId =
        .ok (.localGet objectId, .object))
    (fieldCompiled :
      Fir.Wasm.getLocal context fieldId =
        .ok (.localGet fieldId, fieldKind))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.sset objectId slotIndex byteOffset fieldId type continuation) target) :
    ∃ objectIndex fieldIndex callIndex targetRest,
      findFVar? (functionBindings sourceFunction) objectId =
          some objectIndex ∧
        (functionBindings sourceFunction)[objectIndex]?.map Prod.snd =
          some .object ∧
        findFVar? (functionBindings sourceFunction) fieldId =
          some fieldIndex ∧
        (functionBindings sourceFunction)[fieldIndex]?.map Prod.snd =
          some fieldKind ∧
        callIndex? sourceModule
            (.runtime (.scalarSet slotIndex byteOffset fieldKind)) =
          some callIndex ∧
        CodeAdapted context sourceModule sourceFunction labels continuation
          targetRest ∧
        target =
          [.localGet objectIndex, .localGet fieldIndex, .call callIndex] ++
            targetRest := by
  rcases adapted with ⟨symbolic, compiled, targetCompiled⟩
  have core := Fir.Wasm.finishCompileResult_eq_ok_iff.mp compiled
  rw [Fir.Wasm.compileCodeCore.eq_def] at core
  simp only at core
  cases restResult :
      Fir.Wasm.compileCodeCore context continuation with
  | none =>
      rw [objectCompiled, fieldCompiled, restResult] at core
      change none = some (Except.ok symbolic) at core
      cases core
  | some result =>
      cases result with
      | error error =>
          rw [objectCompiled, fieldCompiled, restResult] at core
          change
            some (Except.error error) = some (Except.ok symbolic) at core
          have impossible :
              Except.error error = Except.ok symbolic :=
            Option.some.inj core
          cases impossible
      | ok restCode =>
          rw [objectCompiled, fieldCompiled, restResult] at core
          change
            some (Except.ok
              ([.localGet objectId, .localGet fieldId,
                .call (.runtime
                  (.scalarSet slotIndex byteOffset fieldKind))] ++ restCode)) =
              some (Except.ok symbolic) at core
          injection core with symbolicEq
          injection symbolicEq with symbolicEq
          subst symbolic
          have restCompiled :
              Fir.Wasm.compileCode context continuation = .ok restCode :=
            Fir.Wasm.finishCompileResult_eq_ok_iff.mpr restResult
          cases prefixAdapted :
              instructions sourceModule sourceFunction labels
                [.localGet objectId, .localGet fieldId,
                  .call (.runtime
                    (.scalarSet slotIndex byteOffset fieldKind))] with
          | error error =>
              rw [FirTalos.Correctness.instructions_append, prefixAdapted]
                at targetCompiled
              contradiction
          | ok targetPrefix =>
              cases restAdapted :
                  instructions sourceModule sourceFunction labels restCode with
              | error error =>
                  rw [FirTalos.Correctness.instructions_append, prefixAdapted,
                    restAdapted] at targetCompiled
                  contradiction
              | ok targetRest =>
                  have targetEq : targetPrefix ++ targetRest = target := by
                    rw [FirTalos.Correctness.instructions_append,
                      prefixAdapted, restAdapted] at targetCompiled
                    exact Except.ok.inj targetCompiled
                  obtain ⟨indices, callIndex, found, callFound, prefixEq⟩ :=
                    instructions_localGets_call_eq
                      (fvarIds := [objectId, fieldId])
                      (operation := .scalarSet slotIndex byteOffset fieldKind)
                      prefixAdapted
                  cases found with
                  | cons objectFound found =>
                      cases found with
                      | cons fieldFound noMore =>
                          cases noMore
                          obtain ⟨alignedObjectIndex, alignedObjectFound,
                              objectKindAt⟩ :=
                            localsAligned objectCompiled
                          rw [objectFound] at alignedObjectFound
                          injection alignedObjectFound with objectIndexEq
                          subst alignedObjectIndex
                          obtain ⟨alignedFieldIndex, alignedFieldFound,
                              fieldKindAt⟩ :=
                            localsAligned fieldCompiled
                          rw [fieldFound] at alignedFieldFound
                          injection alignedFieldFound with fieldIndexEq
                          subst alignedFieldIndex
                          refine ⟨_, _, callIndex, targetRest, objectFound,
                            objectKindAt, fieldFound, fieldKindAt, callFound,
                            ⟨restCode, restCompiled, restAdapted⟩, ?_⟩
                          rw [prefixEq] at targetEq
                          exact targetEq.symm

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
Budget-threaded recursive correctness for a UTF-8 String-literal `let`.

Unlike the single-step capacity rule, the continuation receives the exact
residual wasm32 path budget after the concrete String extent has been
allocated.  This is the first allocating recursive compiler rule that can be
composed sequentially without supplying a fresh capacity premise at every
source node.
-/
theorem ConcreteSupportedExport.codeWP_stringLiteralLet_of_budget
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
    {remainingBytes : Nat}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (allocationFits :
      align8 (headerBytes + (stringUtf8Bytes value).length) ≤ remainingBytes)
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
          heap.AddressSpaceBudget
              (remainingBytes -
                align8
                  (headerBytes + (stringUtf8Bytes value).length)) →
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
  obtain ⟨heap, word, allocated, remainingBudget⟩ :=
    stateRelated.1.heap.frontier.allocateString_eq_ok_of_budget value budget
      allocationFits
  obtain ⟨updated, targetSet⟩ := localSetReady resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.stringLiteralCall callFound
  rw [bodyEq]
  apply codeWP_stringLiteral_let valueEq valueCompiled callFound stateRelated
    resultFound resultKindAt allocated imported spec.hostsSatisfy inBounds
    contracted params results targetSet
  intro nextWitness extension nextRuntimeRelated valueRelated
  exact continued continuationAdapted resultFound targetSet extension
    nextRuntimeRelated valueRelated remainingBudget

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
The constructor-argument relation and explicit wasm32 resource conditions
construct the complete nonempty concrete host step. The only dynamic source
premise is the actual `allocCtor` step being simulated.
-/
theorem constructorNonemptyStep_of_capacity
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {sourceRuntime nextRuntime : RuntimeState}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {resultKind : AbiKind} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value} {sourceValue : Value}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness sourceRuntime)
    (argsLength : physicalArgs.length = fieldKinds.size)
    (argumentsRelated :
      ConstructorArgumentsRelated witness fieldKinds.toList physicalArgs
        semanticArgs.toList)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (semanticArity : semanticArgs.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (capacity :
      initial.host.runtime.heap.AllocationCapacity
        (ConstructorLayout.ofInfo info).allocationBytes) :
    ∃ (nextStore : Wasm.Store Host) (word : Word32)
        (nextWitness : RefinementWitness),
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
          .Return [.i32 (UInt32.ofNat word.value)] nextStore ∧
        witness.Extends nextWitness ∧
        ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime ∧
        nextStore.host.failure? = none ∧
        PhysicalValueRel nextWitness resultKind
          (.i32 (UInt32.ofNat word.value)) sourceValue := by
  obtain ⟨fields, decoded, fieldsLength, fieldsRelated⟩ :=
    argumentsRelated.decodeObjectWords (by simpa using fieldKindsValid) 0
  have arity : fields.toArray.size = info.size := by
    simpa [fieldsLength] using fieldKindsSize
  have fieldsRelatedArray :
      ∀ (index : Nat) (kind : AbiKind) (value : Value),
        fieldKinds[index]? = some kind →
        semanticArgs[index]? = some value →
        ∃ word, fields.toArray[index]? = some word ∧
          ValueRel witness kind (.word32 word) value := by
    intro index kind value kindAt valueAt
    obtain ⟨word, wordAt, valueRelated⟩ :=
      fieldsRelated index kind value (by simpa using kindAt)
        (by simpa using valueAt)
    exact ⟨word, by simpa using wordAt, valueRelated⟩
  obtain ⟨heap, address, extension, operation, nextRuntimeRelated,
      physicalRelated, expectedSourceStep⟩ :=
    allocCtorNonemptyStep_of_refines_of_capacity runtimeRelated argsLength
      decoded arity semanticArity fieldKindsSize fieldKindsValid
      fieldsRelatedArray nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit resultRefines capacity
  have resultEq :
      (semanticConstructorResult sourceRuntime info semanticArgs,
        .object (.heap sourceRuntime.nextLocation)) =
        (nextRuntime, sourceValue) :=
    Except.ok.inj (expectedSourceStep.symm.trans semanticStep)
  injection resultEq with runtimeEq valueEq
  subst nextRuntime
  subst sourceValue
  let nextWitness :=
    witness.bindConstructor sourceRuntime.nextLocation address info fieldKinds
  refine ⟨replaceHeap initial heap, address, nextWitness, operation, extension,
    nextRuntimeRelated, ?_, physicalRelated⟩
  simp [replaceHeap, clearFailure]

/--
Budget-threaded compiler-facing constructor step. It derives the same generated
host/source simulation as `constructorNonemptyStep_of_capacity` and additionally
exports the exact residual source-path budget on the returned store.
-/
theorem constructorNonemptyStep_of_budget
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {sourceRuntime nextRuntime : RuntimeState}
    {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {resultKind : AbiKind} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value} {sourceValue : Value}
    {remainingBytes : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness sourceRuntime)
    (argsLength : physicalArgs.length = fieldKinds.size)
    (argumentsRelated :
      ConstructorArgumentsRelated witness fieldKinds.toList physicalArgs
        semanticArgs.toList)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (semanticArity : semanticArgs.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (allocationFits :
      (ConstructorLayout.ofInfo info).allocationBytes ≤ remainingBytes) :
    ∃ (nextStore : Wasm.Store Host) (word : Word32)
        (nextWitness : RefinementWitness),
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
          .Return [.i32 (UInt32.ofNat word.value)] nextStore ∧
        nextStore.host.externals = initial.host.externals ∧
          nextStore.host.closureDescriptors =
              initial.host.closureDescriptors ∧
            nextWitness.closureDescriptors = witness.closureDescriptors ∧
              witness.Extends nextWitness ∧
              ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime ∧
              nextStore.host.failure? = none ∧
              PhysicalValueRel nextWitness resultKind
                  (.i32 (UInt32.ofNat word.value)) sourceValue ∧
              nextStore.host.runtime.heap.AddressSpaceBudget
                (remainingBytes -
                  (ConstructorLayout.ofInfo info).allocationBytes) := by
  obtain ⟨fields, decoded, fieldsLength, fieldsRelated⟩ :=
    argumentsRelated.decodeObjectWords (by simpa using fieldKindsValid) 0
  have arity : fields.toArray.size = info.size := by
    simpa [fieldsLength] using fieldKindsSize
  have fieldsRelatedArray :
      ∀ (index : Nat) (kind : AbiKind) (value : Value),
        fieldKinds[index]? = some kind →
        semanticArgs[index]? = some value →
        ∃ word, fields.toArray[index]? = some word ∧
          ValueRel witness kind (.word32 word) value := by
    intro index kind value kindAt valueAt
    obtain ⟨word, wordAt, valueRelated⟩ :=
      fieldsRelated index kind value (by simpa using kindAt)
        (by simpa using valueAt)
    exact ⟨word, by simpa using wordAt, valueRelated⟩
  obtain ⟨heap, address, remainingBudget, extension, operation,
      nextRuntimeRelated, physicalRelated, expectedSourceStep⟩ :=
    allocCtorNonemptyStep_of_refines_of_budget runtimeRelated argsLength
      decoded arity semanticArity fieldKindsSize fieldKindsValid
      fieldsRelatedArray nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit resultRefines budget allocationFits
  have resultEq :
      (semanticConstructorResult sourceRuntime info semanticArgs,
        .object (.heap sourceRuntime.nextLocation)) =
        (nextRuntime, sourceValue) :=
    Except.ok.inj (expectedSourceStep.symm.trans semanticStep)
  injection resultEq with runtimeEq valueEq
  subst nextRuntime
  subst sourceValue
  let nextWitness :=
    witness.bindConstructor sourceRuntime.nextLocation address info fieldKinds
  refine ⟨replaceHeap initial heap, address, nextWitness, operation, ?_, ?_,
    extension.closureDescriptors, extension, nextRuntimeRelated, ?_,
    physicalRelated, ?_⟩
  · simp [replaceHeap, clearFailure]
  · simp [replaceHeap, clearFailure]
  · simp [replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using remainingBudget

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
          ConstructorArgumentsRelated witness fieldKinds.toList physicalArgs
            semanticArgs.toList →
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
  obtain ⟨physicalArgs, argumentsReady, physicalArity, argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      argumentsAdapted evaluated stateRelated
  obtain ⟨nextStore, word, nextWitness, operation, extension,
      nextRuntimeRelated, failureClear, valueRelated⟩ :=
    concreteStep physicalArity argumentsRelated
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
Constructive recursive correctness for a nonempty constructor allocation.
Production compilation and adaptation derive the target prefix; source
evaluation and `StateRelated` derive its exact physical fields. The remaining
conditions are the generated operation's ABI well-formedness, representable
header counts, and explicit wasm32 address-space capacity.
-/
theorem ConcreteSupportedExport.codeWP_constructorNonemptyLet_of_capacity
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
    (operationWellFormed :
      (RuntimeOp.allocCtor info fieldKinds resultKind).abiWellFormed = true)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
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
    (capacity :
      initial.host.runtime.heap.AllocationCapacity
        (ConstructorLayout.ofInfo info).allocationBytes)
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
  have operationFacts :
      (info.size = fieldKinds.size ∧
        fieldKinds.all AbiKind.isObjectField = true) ∧
        (constructorKind info).refines resultKind = true := by
    simpa [RuntimeOp.abiWellFormed] using operationWellFormed
  have semanticArity : semanticArgs.size = info.size := by
    by_contra mismatch
    simp [allocCtor, mismatch, Bind.bind, Except.bind] at semanticStep
  have tagFits : info.cidx < UInt32.size := by
    simpa [Fir.Wasm.constructorTagFitsI32] using fits
  apply spec.codeWP_constructorLet valueEq fits valueKind argumentsCompiled
    localCompiled evaluated semanticStep stateRelated
  · intro physicalArgs physicalArity argumentsRelated
    exact constructorNonemptyStep_of_capacity stateRelated.1 physicalArity
      argumentsRelated semanticStep semanticArity operationFacts.1.1.symm
      operationFacts.1.2 nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit operationFacts.2 capacity
  · exact localSetReady
  · exact continued

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

/--
Total source-path allocation cost for the direct-value fragment.

The operation-specific `letCost` is source-facing. This fold follows only the
direct `let` spine; other code forms have cost zero because they cannot occur
in a `DirectValueEvaluates` derivation. No target program or translation
evidence contributes to the result.
-/
def DirectValuePathCost
    (letCost : LCNF.LetDecl .impure → Nat) :
    LCNF.Code .impure → Nat
  | .let decl continuation =>
      letCost decl + DirectValuePathCost letCost continuation
  | _ => 0

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
Successful source evaluation for a mixed direct/external `let` spine,
indexed by the wasm32 allocation budget required along that execution.

Direct declarations retain their syntax-computed cost. An external
declaration carries a source-facing dynamic cost because the size of a pure
`Nat`, `Int`, or `String` result need not be determined by the declaration
alone. `ExternalSupported` may inspect the exact source step and result, but
neither it nor this relation contains target code, numeric Wasm indices, or a
translation witness.
-/
inductive BudgetedSpineEvaluates (context : Fir.Wasm.Context)
    (externals : ExternalImpl)
    (DirectSupported : LCNF.LetDecl .impure → Prop)
    (ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop)
    (directCost : LCNF.LetDecl .impure → Nat) :
    RuntimeState → Env → LCNF.Code .impure → RuntimeState → Value → Nat → Prop where
  | ret
      (sourceLookup : lookup sourceEnv result = some sourceValue) :
      BudgetedSpineEvaluates context externals DirectSupported
        ExternalSupported directCost sourceRuntime sourceEnv (.return result)
        sourceRuntime sourceValue 0
  | letValue
      (supported : DirectSupported decl)
      (sourceStep :
        SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
          sourceValue)
      (continued :
        BudgetedSpineEvaluates context externals DirectSupported
          ExternalSupported directCost nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation
          resultRuntime resultValue continuationCost) :
      BudgetedSpineEvaluates context externals DirectSupported
        ExternalSupported directCost sourceRuntime sourceEnv
        (.let decl continuation) resultRuntime resultValue
        (directCost decl + continuationCost)
  | externalLet
      (supported :
        ExternalSupported sourceRuntime sourceEnv decl continuation nextRuntime
          sourceValue stepCost)
      (sourceStep :
        SourceExternalLetResult context externals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue)
      (continued :
        BudgetedSpineEvaluates context externals DirectSupported
          ExternalSupported directCost nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation
          resultRuntime resultValue continuationCost) :
      BudgetedSpineEvaluates context externals DirectSupported
        ExternalSupported directCost sourceRuntime sourceEnv
        (.let decl continuation) resultRuntime resultValue
        (stepCost + continuationCost)

/-- The indexed mixed-spine evaluation is an actual finite execution of the
repository source interpreter, including each complete three-step external
protocol and its exact trace insertion. -/
theorem BudgetedSpineEvaluates.execEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {directCost : LCNF.LetDecl .impure → Nat}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals DirectSupported
        ExternalSupported directCost sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue requiredBytes) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (ReturnedObservation resultRuntime resultValue) := by
  induction evaluation with
  | ret sourceLookup =>
      exact (CodeEvaluates.ret sourceLookup).execEvaluates externals
  | letValue _ sourceStep _ ih =>
      exact sourceLetResult_thenExecEvaluates sourceStep ih
  | externalLet _ sourceStep _ ih =>
      exact sourceExternalLetResult_thenExecEvaluates sourceStep ih

/-- The previous direct-only source relation embeds into the mixed indexed
relation with the exact existing `DirectValuePathCost`. -/
theorem DirectValueEvaluates.toBudgetedSpineEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {directCost : LCNF.LetDecl .impure → Nat}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value}
    (evaluation :
      DirectValueEvaluates context DirectSupported sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue) :
    BudgetedSpineEvaluates context externals DirectSupported ExternalSupported
      directCost sourceRuntime sourceEnv sourceCode resultRuntime resultValue
      (DirectValuePathCost directCost sourceCode) := by
  induction evaluation with
  | ret sourceLookup =>
      simpa [DirectValuePathCost] using
        (BudgetedSpineEvaluates.ret (externals := externals)
          (ExternalSupported := ExternalSupported)
          (directCost := directCost) sourceLookup)
  | letValue supported sourceStep _ ih =>
      simpa [DirectValuePathCost] using
        (BudgetedSpineEvaluates.letValue supported sourceStep ih)

/-- Source-facing admission shape for one successful no-result effect node. -/
abbrev EffectSupportedPredicate :=
  RuntimeState → Env → LCNF.Code .impure → LCNF.Code .impure →
    RuntimeState → Prop

/-- Empty effect family used by code fragments that admit no effect nodes. -/
def NoEffectsSupported : EffectSupportedPredicate :=
  fun _ _ _ _ _ => False

/--
Source-facing admission for compiler-erased persistent ownership operations.

Both operations resume in the same runtime and environment. The admission
contains no target program, numeric index, or translation witness.
-/
inductive PersistentOwnershipEffectSupported : EffectSupportedPredicate where
  | inc
      (sourceRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId : FVarId)
      (amount : Nat)
      (check : Bool)
      (continuation : LCNF.Code .impure) :
      PersistentOwnershipEffectSupported sourceRuntime sourceEnv
        (.inc objectId amount check true continuation) continuation
        sourceRuntime
  | dec
      (sourceRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId : FVarId)
      (amount : Nat)
      (check : Bool)
      (objectFields? : Option Nat)
      (continuation : LCNF.Code .impure) :
      PersistentOwnershipEffectSupported sourceRuntime sourceEnv
        (.dec objectId amount check true objectFields? continuation)
        continuation sourceRuntime

/--
Source/compiler-facing admission for one successful ordinary reference-count
increment.

The constructor records the semantic lookup/update and the exact wasm32 count
headroom needed by the concrete header write. The only compiler fact is the
source local's ABI kind; no target program, numeric local/import index,
concrete address, or simulation derivation is admitted.
-/
inductive OrdinaryIncrementEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate where
  | inc
      (sourceRuntime nextRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId : FVarId)
      (amount : Nat)
      (check : Bool)
      (continuation : LCNF.Code .impure)
      (objectKind : AbiKind)
      (sourceObject : Value)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectRefines : objectKind.refines .tobject = true)
      (objectLookup :
        lookupValue sourceEnv objectId = .ok sourceObject)
      (updated :
        incValue sourceRuntime sourceObject amount check = .ok nextRuntime)
      (fits : ∀ (location : Location) (cell : HeapCell),
        sourceObject = .object (.heap location) →
        findCell? sourceRuntime.heap location = some cell →
        cell.rc + amount < UInt32.size) :
      OrdinaryIncrementEffectSupported context sourceRuntime sourceEnv
        (.inc objectId amount check false continuation) continuation
        nextRuntime

/--
Source/compiler-facing admission for one successful ordinary decrement.

The semantic lookup and successful update determine whether the operation is a
header decrement or a recursive ownership release. Descriptor-table agreement
is deliberately absent: it belongs to the threaded concrete invariant, while
the admission contains only source facts and the source local's ABI kind.
-/
inductive OrdinaryDecrementEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate where
  | dec
      (sourceRuntime nextRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId : FVarId)
      (amount : Nat)
      (check : Bool)
      (objectFields? : Option Nat)
      (continuation : LCNF.Code .impure)
      (objectKind : AbiKind)
      (sourceObject : Value)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectRefines : objectKind.refines .tobject = true)
      (objectLookup :
        lookupValue sourceEnv objectId = .ok sourceObject)
      (updated :
        decValue sourceRuntime sourceObject amount check = .ok nextRuntime) :
      OrdinaryDecrementEffectSupported context sourceRuntime sourceEnv
        (.dec objectId amount check false objectFields? continuation)
        continuation nextRuntime

/--
Source/compiler-facing admission for one successful explicit deletion.

Deletion accepts either an ordinary heap object or the exact erased reset
token. The semantic lookup/update decides that distinction. The admission
therefore needs only the source local's ABI kind and contains no target
program, numeric index, concrete word, or translation witness.
-/
inductive OrdinaryDeleteEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate where
  | del
      (sourceRuntime nextRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId : FVarId)
      (continuation : LCNF.Code .impure)
      (objectKind : AbiKind)
      (sourceObject : Value)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectLookup :
        lookupValue sourceEnv objectId = .ok sourceObject)
      (updated :
        deleteValue sourceRuntime sourceObject = .ok nextRuntime) :
      OrdinaryDeleteEffectSupported context sourceRuntime sourceEnv
        (.del objectId continuation) continuation nextRuntime

/--
Source/compiler-facing admission for one successful constructor-tag mutation.

The admission records exactly the semantic live-constructor facts required by
the concrete header refinement and the compiler's object-local equation. It
contains no target program, numeric local/import index, concrete address, or
simulation derivation.
-/
inductive ConstructorTagEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate where
  | setTag
      (sourceRuntime nextRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId : FVarId)
      (tag : Nat)
      (continuation : LCNF.Code .impure)
      (location : Location)
      (cell : HeapCell)
      (semantic : ConstructorObject)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, .object))
      (objectLookup :
        lookupValue sourceEnv objectId =
          .ok (.object (.heap location)))
      (updated :
        setTag sourceRuntime (.object (.heap location)) tag =
          .ok nextRuntime)
      (found : findCell? sourceRuntime.heap location = some cell)
      (live : cell.live = true)
      (objectEq : cell.object = .ctor semantic)
      (tagFits : tag < UInt32.size) :
      ConstructorTagEffectSupported context sourceRuntime sourceEnv
        (.setTag objectId tag continuation) continuation nextRuntime

/--
Source/compiler-facing admission for successful FVar object-field mutation.

The final universally quantified premise is the missing source typing
judgment: whenever the current object is represented by a constructor
descriptor, the selected slot has the compiler-selected field kind. No chosen
witness, concrete word, numeric local/import index, target program, or
simulation derivation is admitted.
-/
inductive ObjectFieldFVarEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate where
  | oset
      (sourceRuntime nextRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId fieldId : FVarId)
      (index : Nat)
      (continuation : LCNF.Code .impure)
      (location : Location)
      (cell : HeapCell)
      (semantic : ConstructorObject)
      (field : Value)
      (fieldKind : AbiKind)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, .object))
      (fieldCompiled :
        Fir.Wasm.getLocal context fieldId =
          .ok (.localGet fieldId, fieldKind))
      (fieldObjectKind : fieldKind.isObjectField = true)
      (objectLookup :
        lookupValue sourceEnv objectId =
          .ok (.object (.heap location)))
      (fieldLookup : lookupValue sourceEnv fieldId = .ok field)
      (updated :
        setObjectField sourceRuntime (.object (.heap location)) index field =
          .ok nextRuntime)
      (found : findCell? sourceRuntime.heap location = some cell)
      (live : cell.live = true)
      (objectEq : cell.object = .ctor semantic)
      (indexValid : index < semantic.objectFields.size)
      (fieldKindAligned :
        ∀ {witness : RefinementWitness} {objectWord : Word32}
            {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind},
          ValueRel witness .tobject (.word32 objectWord)
              (.object (.heap location)) →
            witness.descriptors.lookup? objectWord =
                some (.constructor info fieldKinds) →
              fieldKinds[index]? = some fieldKind) :
      ObjectFieldFVarEffectSupported context sourceRuntime sourceEnv
        (.oset objectId index (.fvar fieldId) continuation) continuation
        nextRuntime

/--
Source/compiler-facing admission for successful erased object-field mutation.

The compiler-selected payload kind and value are fixed by `.erased`; the only
source typing obligation says that the selected constructor descriptor slot is
also erased. Numeric target indices, the canonical zero instruction, and all
concrete heap witnesses are reconstructed by compiler inversion and state
refinement.
-/
inductive ObjectFieldErasedEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate where
  | oset
      (sourceRuntime nextRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId : FVarId)
      (index : Nat)
      (continuation : LCNF.Code .impure)
      (location : Location)
      (cell : HeapCell)
      (semantic : ConstructorObject)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, .object))
      (objectLookup :
        lookupValue sourceEnv objectId =
          .ok (.object (.heap location)))
      (updated :
        setObjectField sourceRuntime (.object (.heap location)) index .erased =
          .ok nextRuntime)
      (found : findCell? sourceRuntime.heap location = some cell)
      (live : cell.live = true)
      (objectEq : cell.object = .ctor semantic)
      (indexValid : index < semantic.objectFields.size)
      (fieldKindAligned :
        ∀ {witness : RefinementWitness} {objectWord : Word32}
            {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind},
          ValueRel witness .tobject (.word32 objectWord)
              (.object (.heap location)) →
            witness.descriptors.lookup? objectWord =
                some (.constructor info fieldKinds) →
              fieldKinds[index]? = some .erased) :
      ObjectFieldErasedEffectSupported context sourceRuntime sourceEnv
        (.oset objectId index .erased continuation) continuation nextRuntime

/--
Source/compiler-facing admission for successful `USize` field mutation.

The predicate contains only source lookups and update facts, live-constructor
bounds, and the two source-local compiler equations. Numeric target indices,
the runtime import, target syntax, physical words, and the concrete simulation
are reconstructed by production inversion and `StateRelated`.
-/
inductive USizeFieldEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate where
  | uset
      (sourceRuntime nextRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId fieldId : FVarId)
      (index : Nat)
      (continuation : LCNF.Code .impure)
      (location : Location)
      (cell : HeapCell)
      (semantic : ConstructorObject)
      (field : UInt64)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, .object))
      (fieldCompiled :
        Fir.Wasm.getLocal context fieldId =
          .ok (.localGet fieldId, .usize))
      (objectLookup :
        lookupValue sourceEnv objectId =
          .ok (.object (.heap location)))
      (fieldLookup : lookupValue sourceEnv fieldId = .ok (.usize field))
      (updated :
        setUSizeSlot sourceRuntime (.object (.heap location)) index
            (.usize field) =
          .ok nextRuntime)
      (found : findCell? sourceRuntime.heap location = some cell)
      (live : cell.live = true)
      (objectEq : cell.object = .ctor semantic)
      (slotStart : semantic.objectFields.size ≤ index)
      (slotEnd :
        index < semantic.objectFields.size + semantic.usizeFields.size) :
      USizeFieldEffectSupported context sourceRuntime sourceEnv
        (.uset objectId index fieldId continuation) continuation nextRuntime

/-- The four packed-integer ABI kinds implemented by the concrete scalar
setter. Float and non-scalar kinds remain outside this fragment. -/
def PackedIntegerAbiKind : AbiKind → Prop
  | .uint8 | .uint16 | .uint32 | .uint64 => True
  | _ => False

/--
The source typing/layout condition needed by one packed-integer field write.

The width-indexed separation premise preserves every retained scalar field;
the descriptor coordinates identify the packed region and prove the selected
write fits. Unsupported ABI kinds reduce the final conjunct to `False`.
-/
def ScalarFieldMutationSafe
    (semantic : ConstructorObject) (slotIndex byteOffset : Nat)
    (fieldKind : AbiKind) (info : LCNF.CtorInfo) : Prop :=
  (match fieldKind with
    | .uint8 => ∀ old ∈ semantic.scalarFields,
        old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
        old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
          byteOffset + 1 ≤ old.offset
    | .uint16 => ∀ old ∈ semantic.scalarFields,
        old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
        old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
          byteOffset + 2 ≤ old.offset
    | .uint32 => ∀ old ∈ semantic.scalarFields,
        old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
        old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
          byteOffset + 4 ≤ old.offset
    | .uint64 => ∀ old ∈ semantic.scalarFields,
        old.width ≠ slotIndex ∨ old.offset ≠ byteOffset →
        old.offset + scalarValueByteSize old.value ≤ byteOffset ∨
          byteOffset + 8 ≤ old.offset
    | _ => semantic.scalarFields.filter (fun old =>
        old.width != slotIndex || old.offset != byteOffset) = []) ∧
  slotIndex = info.size + info.usize ∧
  match fieldKind with
    | .uint8 => byteOffset + 1 ≤ info.ssize
    | .uint16 => byteOffset + 2 ≤ info.ssize
    | .uint32 => byteOffset + 4 ≤ info.ssize
    | .uint64 => byteOffset + 8 ≤ info.ssize
    | _ => False

/--
Source/compiler-facing admission for successful packed-integer field mutation.

The universally quantified layout premise is the source typing judgment
connecting any refined constructor descriptor to the supported packed
coordinate. It chooses no witness, physical word, descriptor, numeric target
index, target syntax, or execution proof.
-/
inductive ScalarFieldEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate where
  | sset
      (sourceRuntime nextRuntime : RuntimeState)
      (sourceEnv : Env)
      (objectId fieldId : FVarId)
      (slotIndex byteOffset : Nat)
      (type : Lean.Expr)
      (continuation : LCNF.Code .impure)
      (location : Location)
      (cell : HeapCell)
      (semantic : ConstructorObject)
      (field : ScalarValue)
      (fieldKind : AbiKind)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, .object))
      (fieldCompiled :
        Fir.Wasm.getLocal context fieldId =
          .ok (.localGet fieldId, fieldKind))
      (objectLookup :
        lookupValue sourceEnv objectId =
          .ok (.object (.heap location)))
      (fieldLookup : lookupValue sourceEnv fieldId = .ok (.scalar field))
      (updated :
        setScalarField sourceRuntime (.object (.heap location)) slotIndex
            byteOffset (.scalar field) =
          .ok nextRuntime)
      (found : findCell? sourceRuntime.heap location = some cell)
      (live : cell.live = true)
      (objectEq : cell.object = .ctor semantic)
      (layoutSafe :
        ∀ {witness : RefinementWitness} {objectWord : Word32}
            {info : LCNF.CtorInfo} {fieldKinds : Array AbiKind},
          ValueRel witness .tobject (.word32 objectWord)
              (.object (.heap location)) →
            witness.descriptors.lookup? objectWord =
                some (.constructor info fieldKinds) →
              ScalarFieldMutationSafe semantic slotIndex byteOffset fieldKind
                info) :
      ScalarFieldEffectSupported context sourceRuntime sourceEnv
        (.sset objectId slotIndex byteOffset fieldId type continuation)
        continuation nextRuntime

/--
Disjoint union of two source-facing effect families.

The wrapper contains only the selected source admission. It is the generic
composition device for proving one structural compiler theorem from reusable
operation-family laws.
-/
inductive EffectSupportedOr
    (left right : EffectSupportedPredicate) : EffectSupportedPredicate where
  | left
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {code continuation : LCNF.Code .impure}
      (supported :
        left sourceRuntime sourceEnv code continuation nextRuntime) :
      EffectSupportedOr left right sourceRuntime sourceEnv code continuation
        nextRuntime
  | right
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {code continuation : LCNF.Code .impure}
      (supported :
        right sourceRuntime sourceEnv code continuation nextRuntime) :
      EffectSupportedOr left right sourceRuntime sourceEnv code continuation
        nextRuntime

/--
All currently proved successful ownership effects in one source-facing
admission family. The nesting is an implementation detail of the reusable
binary union and exposes no target syntax or proof certificate.
-/
abbrev OwnershipEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr PersistentOwnershipEffectSupported
    (EffectSupportedOr (OrdinaryIncrementEffectSupported context)
      (EffectSupportedOr (OrdinaryDecrementEffectSupported context)
        (OrdinaryDeleteEffectSupported context)))

/--
The complete ownership family extended with successful constructor-tag
mutation. This source-facing union is intentionally assembled from reusable
operation families and carries no generated-target evidence.
-/
abbrev OwnershipAndTagEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr (OwnershipEffectSupported context)
    (ConstructorTagEffectSupported context)

/--
The mixed ownership/tag family extended with successful FVar object-slot
mutation. The explicit FVar qualifier keeps erased-slot admission separate
until its production constant-prefix inversion is added.
-/
abbrev OwnershipTagAndObjectFVarEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr (OwnershipAndTagEffectSupported context)
    (ObjectFieldFVarEffectSupported context)

/--
Both source argument forms of successful object-slot mutation.
-/
abbrev ObjectFieldEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr (ObjectFieldFVarEffectSupported context)
    (ObjectFieldErasedEffectSupported context)

/--
The ownership/tag family extended with both FVar and compiler-erased
object-slot mutation.
-/
abbrev OwnershipTagAndObjectEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr (OwnershipAndTagEffectSupported context)
    (ObjectFieldEffectSupported context)

/--
All currently structural successful constructor-field mutations: object slots
for both argument forms and `USize` slots.
-/
abbrev FieldMutationEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr (ObjectFieldEffectSupported context)
    (USizeFieldEffectSupported context)

/--
The ownership/tag family extended with all currently structural successful
field mutations.
-/
abbrev OwnershipTagAndFieldMutationEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr (OwnershipAndTagEffectSupported context)
    (FieldMutationEffectSupported context)

/--
Object, `USize`, and supported packed-integer field mutations.
-/
abbrev AllFieldMutationEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr (FieldMutationEffectSupported context)
    (ScalarFieldEffectSupported context)

/--
The ownership/tag family extended with object, `USize`, and supported
packed-integer field mutations.
-/
abbrev OwnershipTagAndAllFieldMutationEffectSupported
    (context : Fir.Wasm.Context) : EffectSupportedPredicate :=
  EffectSupportedOr (OwnershipAndTagEffectSupported context)
    (AllFieldMutationEffectSupported context)

/--
Budgeted successful source evaluation for mixed direct/external code with
selected case branches and admitted no-result effects.

Cases and effects carry only source-facing admission facts plus the executable
interpreter step. Neither generated target structure nor an operation proof is
stored in the relation. Both node families consume zero heap-allocation budget;
their reusable runtime laws are supplied once to the structural theorem.
-/
inductive BudgetedCodeEvaluates (context : Fir.Wasm.Context)
    (externals : ExternalImpl)
    (DirectSupported : LCNF.LetDecl .impure → Prop)
    (ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop)
    (CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop)
    (EffectSupported : EffectSupportedPredicate)
    (directCost : LCNF.LetDecl .impure → Nat) :
    RuntimeState → Env → LCNF.Code .impure → RuntimeState → Value → Nat → Prop where
  | ret
      (sourceLookup : lookup sourceEnv result = some sourceValue) :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv (.return result) sourceRuntime sourceValue 0
  | letValue
      (supported : DirectSupported decl)
      (sourceStep :
        SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
          sourceValue)
      (continued :
        BudgetedCodeEvaluates context externals DirectSupported
          ExternalSupported CaseSupported EffectSupported directCost nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultRuntime
          resultValue continuationCost) :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv (.let decl continuation) resultRuntime resultValue
        (directCost decl + continuationCost)
  | externalLet
      (supported :
        ExternalSupported sourceRuntime sourceEnv decl continuation nextRuntime
          sourceValue stepCost)
      (sourceStep :
        SourceExternalLetResult context externals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue)
      (continued :
        BudgetedCodeEvaluates context externals DirectSupported
          ExternalSupported CaseSupported EffectSupported directCost nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultRuntime
          resultValue continuationCost) :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv (.let decl continuation) resultRuntime resultValue
        (stepCost + continuationCost)
  | caseOf
      (supported : CaseSupported sourceRuntime sourceEnv cases selected)
      (sourceStep :
        SourceCaseResult sourceRuntime sourceEnv cases selected)
      (continued :
        BudgetedCodeEvaluates context externals DirectSupported
          ExternalSupported CaseSupported EffectSupported directCost
          sourceRuntime sourceEnv selected resultRuntime resultValue
          requiredBytes) :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv (.cases cases) resultRuntime resultValue
        requiredBytes
  | effect
      (supported :
        EffectSupported sourceRuntime sourceEnv code continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        BudgetedCodeEvaluates context externals DirectSupported
          ExternalSupported CaseSupported EffectSupported directCost nextRuntime
          sourceEnv continuation resultRuntime resultValue requiredBytes) :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv code resultRuntime resultValue requiredBytes

/-- The mixed code relation denotes an exact finite interpreter run. -/
theorem BudgetedCodeEvaluates.execEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop}
    {EffectSupported : EffectSupportedPredicate}
    {directCost : LCNF.LetDecl .impure → Nat}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue
        requiredBytes) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (ReturnedObservation resultRuntime resultValue) := by
  induction evaluation with
  | ret sourceLookup =>
      exact (CodeEvaluates.ret sourceLookup).execEvaluates externals
  | letValue _ sourceStep _ ih =>
      exact sourceLetResult_thenExecEvaluates sourceStep ih
  | externalLet _ sourceStep _ ih =>
      exact sourceExternalLetResult_thenExecEvaluates sourceStep ih
  | caseOf _ sourceStep _ ih =>
      exact sourceCaseResult_thenExecEvaluates sourceStep ih
  | effect _ sourceStep _ ih =>
      exact sourceEffectResult_thenExecEvaluates sourceStep ih

/--
Every budgeted direct/external spine is mixed code with no case or effect
nodes.
-/
theorem BudgetedSpineEvaluates.toBudgetedCodeEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop}
    {directCost : LCNF.LetDecl .impure → Nat}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals DirectSupported
        ExternalSupported directCost sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue requiredBytes) :
    BudgetedCodeEvaluates context externals DirectSupported ExternalSupported
      CaseSupported NoEffectsSupported directCost sourceRuntime sourceEnv
      sourceCode resultRuntime resultValue requiredBytes := by
  induction evaluation with
  | ret sourceLookup =>
      exact .ret sourceLookup
  | letValue supported sourceStep _ ih =>
      exact .letValue supported sourceStep ih
  | externalLet supported sourceStep _ ih =>
      exact .externalLet supported sourceStep ih

/-- First case admission: a case node whose only alternative is its default. -/
def DefaultOnlyCaseSupported
    (_sourceRuntime : RuntimeState) (_sourceEnv : Env)
    (cases : LCNF.Cases .impure) (selected : LCNF.Code .impure) : Prop :=
  cases.alts.toList = [.default selected]

/--
Source-facing admission for the first real generated case family.

The case has one object-constructor arm and no default. Static fields record
only compiler facts. The dynamic range law is stated over source lookup and
`getTag`; it ensures that the concrete i32 comparison does not wrap, without
mentioning a target local, import index, physical word, or Wasm instruction.
-/
def SingleObjectConstructorCaseSupported
    (context : Fir.Wasm.Context)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (cases : LCNF.Cases .impure) (selected : LCNF.Code .impure) : Prop :=
  ∃ info : LCNF.CtorInfo,
    cases.alts.toList = [.ctorAlt info selected] ∧
    Fir.Wasm.caseDiscriminatorMode context cases.discr = .objectTag ∧
    Fir.Wasm.constructorTagFitsI32 info = true ∧
    Fir.Wasm.getLocal context cases.discr =
      .ok (.localGet cases.discr, .tobject) ∧
    ∀ {sourceObject : Value} {actualTag : Nat},
      lookupValue sourceEnv cases.discr = .ok sourceObject →
      getTag sourceRuntime sourceObject = .ok actualTag →
      actualTag < UInt32.size

/--
Source-facing admission for the first ordered multi-arm object case.

Two constructor tests precede one default. The source interpreter still
chooses the branch; the admission records only source/compiler shape and the
semantic tag-range law needed by both generated i32 comparisons.
-/
def TwoObjectConstructorDefaultCasesSupported
    (context : Fir.Wasm.Context)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (cases : LCNF.Cases .impure) (_selected : LCNF.Code .impure) : Prop :=
  ∃ firstInfo secondInfo : LCNF.CtorInfo,
    ∃ firstBranch secondBranch defaultBranch : LCNF.Code .impure,
      cases.alts.toList =
          [.ctorAlt firstInfo firstBranch,
            .ctorAlt secondInfo secondBranch,
            .default defaultBranch] ∧
        Fir.Wasm.caseDiscriminatorMode context cases.discr = .objectTag ∧
        Fir.Wasm.constructorTagFitsI32 firstInfo = true ∧
        Fir.Wasm.constructorTagFitsI32 secondInfo = true ∧
        Fir.Wasm.getLocal context cases.discr =
          .ok (.localGet cases.discr, .tobject) ∧
        ∀ {sourceObject : Value} {actualTag : Nat},
          lookupValue sourceEnv cases.discr = .ok sourceObject →
          getTag sourceRuntime sourceObject = .ok actualTag →
          actualTag < UInt32.size

/--
Compiler-facing shape for an arbitrary ordered object-constructor chain.

The chain is either constructor-only or ends in exactly one default. This is
the normalized order shared by `chooseAlt` and the executable case compiler;
every constructor tag is statically representable in the generated i32 test.
-/
inductive ObjectConstructorCaseAltsSupported :
    List (LCNF.Alt .impure) → Prop where
  | nil :
      ObjectConstructorCaseAltsSupported []
  | default (code : LCNF.Code .impure) :
      ObjectConstructorCaseAltsSupported [.default code]
  | ctor
      (fits : Fir.Wasm.constructorTagFitsI32 info = true)
      (rest : ObjectConstructorCaseAltsSupported alts) :
      ObjectConstructorCaseAltsSupported (.ctorAlt info code :: alts)

/--
Source/runtime admission for arbitrary normalized object-constructor cases.

The selected branch remains determined by `SourceCaseResult`. Admission
contains only the normalized source table, compiler discriminator facts, and
the semantic tag bound needed by every concrete i32 comparison.
-/
def ObjectConstructorCasesSupported
    (context : Fir.Wasm.Context)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (cases : LCNF.Cases .impure) (_selected : LCNF.Code .impure) : Prop :=
  ObjectConstructorCaseAltsSupported cases.alts.toList ∧
    Fir.Wasm.caseDiscriminatorMode context cases.discr = .objectTag ∧
    Fir.Wasm.getLocal context cases.discr =
      .ok (.localGet cases.discr, .tobject) ∧
    ∀ {sourceObject : Value} {actualTag : Nat},
      lookupValue sourceEnv cases.discr = .ok sourceObject →
      getTag sourceRuntime sourceObject = .ok actualTag →
      actualTag < UInt32.size

/--
Compiler-facing shape for an arbitrary ordered scalar `UInt8` case chain.

As for object cases, the normalized table is constructor-only or ends in one
default. Here every expected constructor tag must fit the direct `UInt8`
comparison lane.
-/
inductive ScalarUInt8CaseAltsSupported :
    List (LCNF.Alt .impure) → Prop where
  | nil :
      ScalarUInt8CaseAltsSupported []
  | default (code : LCNF.Code .impure) :
      ScalarUInt8CaseAltsSupported [.default code]
  | ctor
      (fits : Fir.Wasm.constructorTagFitsUInt8 info = true)
      (rest : ScalarUInt8CaseAltsSupported alts) :
      ScalarUInt8CaseAltsSupported (.ctorAlt info code :: alts)

/--
Source/compiler admission for arbitrary normalized scalar `UInt8` cases.

The exact runtime tag range is derived from `StateRelated` and the `.uint8`
value relation, so admission needs no dynamic bound and contains no physical
local or target-program evidence.
-/
def ScalarUInt8CasesSupported
    (context : Fir.Wasm.Context)
    (_sourceRuntime : RuntimeState) (_sourceEnv : Env)
    (cases : LCNF.Cases .impure) (_selected : LCNF.Code .impure) : Prop :=
  ScalarUInt8CaseAltsSupported cases.alts.toList ∧
    Fir.Wasm.caseDiscriminatorMode context cases.discr = .scalarUInt8 ∧
    Fir.Wasm.getLocal context cases.discr =
      .ok (.localGet cases.discr, .uint8)

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
Source-level wasm32 allocation reservation for the currently admitted
direct-value operations. Constructors and zero-token reuse use their
representation-sensitive fresh-allocation extent; retained in-place reuse
conservatively returns that reservation unused. Literals use their exact
selected extents. Integer boxing reserves one header-plus-slot upper bound:
promoted tags and heap boxes consume it physically, while immediate results
weaken the unused logical budget. All other forms are nonallocating.
-/
def directLetAllocationCost (decl : LCNF.LetDecl .impure) : Nat :=
  match decl.value with
  | .ctor info _ => (ConstructorLayout.ofInfo info).allocationBytes
  | .reuse _ info _ _ => constructorAllocationBytes info
  | .lit (.nat value) => naturalAllocationBytes value
  | .lit (.str value) =>
      align8 (headerBytes + (stringUtf8Bytes value).length)
  | .box _ _ => boxScalarAllocationBytes
  | _ => 0

/--
Static source/compiler admission for a representation-polymorphic natural
literal. Its immediate, promoted-tag, or limb-object representation is chosen
constructively from the source value and available address-space budget.
-/
inductive NaturalLiteralSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (value : Nat)
      (valueEq : decl.value = .lit (.nat value))
      (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, .tobject)) :
      NaturalLiteralSupported context decl

/--
Static source/compiler admission for an allocating UTF-8 String literal.
The concrete address, target import index, and target local index are not part
of the relation.
-/
inductive StringLiteralSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (value : String)
      (valueEq : decl.value = .lit (.str value))
      (valueKind : Fir.Wasm.letValueKind decl = .ok .object)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, .object)) :
      StringLiteralSupported context decl

/-- Exact source request metadata generated when invoking one external
declaration with an already evaluated argument array. -/
def declarationExternalRequest (declaration : LCNF.Decl .impure)
    (args : Array Value) : ExternalRequest := {
  name := declaration.name
  paramTypes := declaration.params.map (·.type)
  resultType := declaration.type
  args }

/--
Source-facing names whose successful pure response is an arbitrary-precision
integer. Keeping this admission family explicit separates the evolving set of
supported Lean externals from the name-agnostic compiler/adapter/refinement
proof.
-/
inductive PureIntegerExternalName : Lean.Name → Prop where
  | intOfNat : PureIntegerExternalName ``Int.ofNat
  | intNeg : PureIntegerExternalName ``Int.neg
  | intAdd : PureIntegerExternalName ``Int.add
  | intSub : PureIntegerExternalName ``Int.sub

/--
Source/compiler admission for the pure arbitrary-precision integer
result family.

The relation admits the names in `PureIntegerExternalName`, records their real
`compileArgs`/`evalArgs` results and source external response, and indexes the
step by the semantic result's exact heap cost. It contains no adapted program,
numeric Wasm index, concrete response, allocation result, or refinement
witness. The operation-family witness is intentionally unused by the generic
lowering proof; it is the source-facing gate that can grow independently.
-/
inductive PureIntegerExternalSupported
    (context : Fir.Wasm.Context) (externals : ExternalImpl) :
    RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
      RuntimeState → Value → Nat → Prop where
  | intro
      (name : Lean.Name) (args : Array (LCNF.Arg .impure))
      (argumentCode : List Fir.Wasm.Instruction)
      (argumentKinds : Array AbiKind) (semanticArgs : Array Value)
      (target : LCNF.Decl .impure) (value : Int)
      (valueEq : decl.value = .fap name args)
      (operation : PureIntegerExternalName name)
      (nonempty : args.isEmpty = false)
      (targetFound : context.program.findDecl? name = some target)
      (targetExternal : ∃ metadata, target.value = .extern metadata)
      (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
      (argumentsCompiled :
        Fir.Wasm.compileArgs context args =
          .ok (argumentCode, argumentKinds))
      (argumentsEvaluated :
        evalArgs sourceEnv args = .ok semanticArgs)
      (signature :
        ExternalTypes.signature {
          params := target.params.map (·.type)
          result := target.type } =
            .ok { params := argumentKinds, results := #[.tobject] })
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, .tobject))
      (semanticCalled :
        externals.call (declarationExternalRequest target semanticArgs)
            sourceRuntime =
          .ok (semanticIntegerExternalResponse sourceRuntime value))
      (nextRuntimeEq :
        nextRuntime =
          semanticExternalRuntimeAfter
            (declarationExternalRequest target semanticArgs) sourceRuntime
            (semanticIntegerExternalResponse sourceRuntime value))
      (sourceValueEq :
        sourceValue =
          (semanticIntegerExternalResponse sourceRuntime value).value)
      (stepCostEq : stepCost = integerAllocationBytes value) :
      PureIntegerExternalSupported context externals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue stepCost

/--
Source-facing pure externals whose result is a Lean `Nat`. This family is
separate from scalar-returning externals: `Nat` uses the compiler's `.tobject`
ABI and may choose any of the immediate, promoted-tag, or limb-object
representations.
-/
inductive PureNaturalExternalName : Lean.Name → Prop where
  | intNatAbs : PureNaturalExternalName ``Int.natAbs
  | natAdd : PureNaturalExternalName ``Nat.add
  | natSub : PureNaturalExternalName ``Nat.sub

/--
Source/compiler admission for pure natural-result externals.

As with the integer family, the relation records only source evaluation and
production compiler facts. It contains no adapted code, Wasm index, physical
word, allocation result, or post-witness.
-/
inductive PureNaturalExternalSupported
    (context : Fir.Wasm.Context) (externals : ExternalImpl) :
    RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
      RuntimeState → Value → Nat → Prop where
  | intro
      (name : Lean.Name) (args : Array (LCNF.Arg .impure))
      (argumentCode : List Fir.Wasm.Instruction)
      (argumentKinds : Array AbiKind) (semanticArgs : Array Value)
      (target : LCNF.Decl .impure) (value : Nat)
      (valueEq : decl.value = .fap name args)
      (operation : PureNaturalExternalName name)
      (nonempty : args.isEmpty = false)
      (targetFound : context.program.findDecl? name = some target)
      (targetExternal : ∃ metadata, target.value = .extern metadata)
      (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
      (argumentsCompiled :
        Fir.Wasm.compileArgs context args =
          .ok (argumentCode, argumentKinds))
      (argumentsEvaluated :
        evalArgs sourceEnv args = .ok semanticArgs)
      (signature :
        ExternalTypes.signature {
          params := target.params.map (·.type)
          result := target.type } =
            .ok { params := argumentKinds, results := #[.tobject] })
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, .tobject))
      (semanticCalled :
        externals.call (declarationExternalRequest target semanticArgs)
            sourceRuntime =
          .ok (semanticNaturalExternalResponse sourceRuntime value))
      (nextRuntimeEq :
        nextRuntime =
          semanticExternalRuntimeAfter
            (declarationExternalRequest target semanticArgs) sourceRuntime
            (semanticNaturalExternalResponse sourceRuntime value))
      (sourceValueEq :
        sourceValue =
          (semanticNaturalExternalResponse sourceRuntime value).value)
      (stepCostEq : stepCost = naturalAllocationBytes value) :
      PureNaturalExternalSupported context externals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue stepCost

/--
Source-facing pure externals returning an unboxed scalar lane. The result kind
is indexed explicitly so admitting a name cannot silently reinterpret an
`i32` as a different scalar width.
-/
inductive PureScalarExternalName :
    Lean.Name → BoxedScalarKind → Prop where
  | intDecLt : PureScalarExternalName ``Int.decLt .uint8
  | natDecEq : PureScalarExternalName ``Nat.decEq .uint8
  | natDecLt : PureScalarExternalName ``Nat.decLt .uint8
  | natDecLe : PureScalarExternalName ``Nat.decLe .uint8

/--
Source/compiler admission for pure nonallocating scalar-result externals.

The semantic scalar determines the exact ABI lane. The zero cost is recorded
as the execution index; all target code, indices, physical operands, and
response witnesses are reconstructed by the compiler theorem.
-/
inductive PureScalarExternalSupported
    (context : Fir.Wasm.Context) (externals : ExternalImpl) :
    RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
      RuntimeState → Value → Nat → Prop where
  | intro
      (name : Lean.Name) (args : Array (LCNF.Arg .impure))
      (argumentCode : List Fir.Wasm.Instruction)
      (argumentKinds : Array AbiKind) (semanticArgs : Array Value)
      (target : LCNF.Decl .impure) (scalar : BoxedScalar)
      (valueEq : decl.value = .fap name args)
      (operation : PureScalarExternalName name scalar.kind)
      (nonempty : args.isEmpty = false)
      (targetFound : context.program.findDecl? name = some target)
      (targetExternal : ∃ metadata, target.value = .extern metadata)
      (valueKind :
        Fir.Wasm.letValueKind decl = .ok scalar.kind.abiKind)
      (argumentsCompiled :
        Fir.Wasm.compileArgs context args =
          .ok (argumentCode, argumentKinds))
      (argumentsEvaluated :
        evalArgs sourceEnv args = .ok semanticArgs)
      (signature :
        ExternalTypes.signature {
          params := target.params.map (·.type)
          result := target.type } =
            .ok {
              params := argumentKinds
              results := #[scalar.kind.abiKind] })
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, scalar.kind.abiKind))
      (semanticCalled :
        externals.call (declarationExternalRequest target semanticArgs)
            sourceRuntime =
          .ok (semanticScalarExternalResponse sourceRuntime scalar))
      (nextRuntimeEq :
        nextRuntime =
          semanticExternalRuntimeAfter
            (declarationExternalRequest target semanticArgs) sourceRuntime
            (semanticScalarExternalResponse sourceRuntime scalar))
      (sourceValueEq :
        sourceValue =
          (semanticScalarExternalResponse sourceRuntime scalar).value)
      (stepCostEq : stepCost = 0) :
      PureScalarExternalSupported context externals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue stepCost

/-- Current source-facing union of all proved pure external result families. -/
def PureExternalSupported
    (context : Fir.Wasm.Context) (externals : ExternalImpl)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (decl : LCNF.LetDecl .impure) (continuation : LCNF.Code .impure)
    (nextRuntime : RuntimeState) (sourceValue : Value) (stepCost : Nat) : Prop :=
  PureIntegerExternalSupported context externals sourceRuntime sourceEnv decl
      continuation nextRuntime sourceValue stepCost ∨
    PureNaturalExternalSupported context externals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue stepCost ∨
      PureScalarExternalSupported context externals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue stepCost

/--
Static source/compiler admission for a nonempty constructor allocation.
The relation records only source layout bounds and successful symbolic
compilation. Physical arguments, numeric target indices, the concrete address,
and the host step are derived later.
-/
inductive NonemptyConstructorSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (info : LCNF.CtorInfo)
      (args : Array (LCNF.Arg .impure))
      (argumentCode : List Fir.Wasm.Instruction)
      (fieldKinds : Array AbiKind)
      (resultKind : AbiKind)
      (valueEq : decl.value = .ctor info args)
      (tagFits : Fir.Wasm.constructorTagFitsI32 info = true)
      (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
      (argumentsCompiled :
        Fir.Wasm.compileArgs context args =
          .ok (argumentCode, fieldKinds))
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, resultKind))
      (operationWellFormed :
        (RuntimeOp.allocCtor info fieldKinds resultKind).abiWellFormed = true)
      (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
      (objectFieldsFit : info.size < UInt32.size)
      (usizeFieldsFit : info.usize < UInt32.size)
      (scalarBytesFit : info.ssize < UInt32.size) :
      NonemptyConstructorSupported context decl

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

/--
Static admission for integer boxing.

The source annotation, operand local, destination local, and compiler result
kind all agree with one supported `BoxedScalarKind`. Runtime scalar values and
physical lanes are reconstructed from `StateRelated`; no translated program,
numeric index, allocation result, or execution witness is admitted here.
-/
inductive BoxSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (scalarId : FVarId) (kind : BoxedScalarKind)
      (valueEq : decl.value = .box kind.semanticType scalarId)
      (valueKind : Fir.Wasm.letValueKind decl = .ok .tobject)
      (scalarCompiled :
        Fir.Wasm.getLocal context scalarId =
          .ok (.localGet scalarId, kind.abiKind))
      (annotationKind :
        Fir.Wasm.checkedAbiKind kind.semanticType = .ok kind.abiKind)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, .tobject)) :
      BoxSupported context decl

/--
An exact physical scalar relation at a supported boxing kind determines the
canonical concrete scalar payload and lane.
-/
theorem PhysicalValueRel.boxedScalar_of_kind
    {witness : RefinementWitness} {kind : BoxedScalarKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : PhysicalValueRel witness kind.abiKind physical semantic) :
    ∃ scalar : BoxedScalar,
      scalar.kind = kind ∧
        semantic = scalar.semanticValue ∧
          physical = physicalOfLane scalar.lane := by
  cases kind with
  | uint8 =>
      cases related with
      | word32 valueRelated =>
          cases valueRelated with
          | uint8 encoded =>
              refine ⟨.uint8 _, rfl, rfl, ?_⟩
              simp [physicalOfLane, BoxedScalar.lane, Word32.ofUInt8, encoded]
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated
  | uint16 =>
      cases related with
      | word32 valueRelated =>
          cases valueRelated with
          | uint16 encoded =>
              refine ⟨.uint16 _, rfl, rfl, ?_⟩
              simp [physicalOfLane, BoxedScalar.lane, Word32.ofUInt16, encoded]
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated
  | uint32 =>
      cases related with
      | word32 valueRelated =>
          cases valueRelated with
          | uint32 encoded =>
              refine ⟨.uint32 _, rfl, rfl, ?_⟩
              simp [physicalOfLane, BoxedScalar.lane, Word32.ofUInt32, encoded]
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated
  | uint64 =>
      cases related with
      | word32 valueRelated => cases valueRelated
      | word64 valueRelated =>
          cases valueRelated with
          | uint64 =>
              exact ⟨.uint64 _, rfl, rfl, rfl⟩
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated
  | usize =>
      cases related with
      | word32 valueRelated => cases valueRelated
      | word64 valueRelated =>
          cases valueRelated with
          | usize =>
              exact ⟨.usize _, rfl, rfl, rfl⟩
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Source-state compatibility for typed unboxing.

Tagged objects are representation-polymorphic. A heap object is compatible
when its live semantic box contains a scalar whose constructor agrees with
the requested result kind. This judgment intentionally mentions no concrete
word, descriptor map, memory read, or target execution witness.
-/
inductive SourceUnboxKindCompatible (runtime : RuntimeState)
    (kind : BoxedScalarKind) : Value → Prop where
  | tagged :
      SourceUnboxKindCompatible runtime kind (.object (.tagged payload))
  | heap
      (storedType : Expr) (scalar : BoxedScalar)
      (found : findCell? runtime.heap location = some cell)
      (live : cell.live = true)
      (objectEq :
        cell.object = .boxed storedType scalar.semanticValue)
      (kindEq : scalar.kind = kind) :
      SourceUnboxKindCompatible runtime kind (.object (.heap location))

/--
Static admission for one successful typed unbox.

The final premise is the source typing boundary omitted by FIR's deliberately
type-erased heap-unbox semantics: a successful source operand must be tagged
or contain a live boxed scalar of the compiler-selected result kind.
-/
inductive UnboxSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (objectId : FVarId) (objectKind : AbiKind)
      (kind : BoxedScalarKind)
      (valueEq : decl.value = .unbox objectId)
      (resultTypeEq : decl.type = kind.semanticType)
      (valueKind : Fir.Wasm.letValueKind decl = .ok kind.abiKind)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectRefines : objectKind.refines .tobject = true)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, kind.abiKind))
      (kindCompatible :
        ∀ {sourceRuntime : RuntimeState} {sourceEnv : Env}
            {sourceObject sourceValue : Value},
          lookup sourceEnv objectId = some sourceObject →
            unbox sourceRuntime kind.semanticType sourceObject =
              .ok sourceValue →
            SourceUnboxKindCompatible sourceRuntime kind sourceObject) :
      UnboxSupported context decl

/--
Static admission for a successful `isShared` observation.

The predicate contains only the source declaration and compiler-local typing
facts. Numeric locals/imports, the concrete object word, and target execution
are reconstructed from production output and `StateRelated`.
-/
inductive IsSharedSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (objectId : FVarId) (objectKind : AbiKind)
      (valueEq : decl.value = .isShared objectId)
      (valueKind : Fir.Wasm.letValueKind decl = .ok .uint8)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectRefines : objectKind.refines .tobject = true)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, .uint8)) :
      IsSharedSupported context decl

/--
Static admission for a successful ownership reset.

The predicate records only the source declaration and compiler-local typing
facts. The tagged, persistent/nonunique, and unique-constructor runtime
branches are reconstructed from `StateRelated` and the successful source
step; no concrete word, heap cell, reset token, or target execution witness
appears in this boundary.
-/
inductive ResetSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Prop where
  | intro
      (count : Nat) (objectId : FVarId) (objectKind : AbiKind)
      (valueEq : decl.value = .reset count objectId)
      (valueKind : Fir.Wasm.letValueKind decl = .ok .reuseToken)
      (objectCompiled :
        Fir.Wasm.getLocal context objectId =
          .ok (.localGet objectId, objectKind))
      (objectRefines : objectKind.refines .tobject = true)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, .reuseToken)) :
      ResetSupported context decl

/--
Static source/compiler admission for one capacity-validated reuse declaration.

The relation records the authoritative fitting fact, production compiler
equations, representation-width checks, and the provenance-sensitive result
kind condition. It contains no runtime token branch, concrete word/address,
numeric local/import index, allocation result, or execution witness.
-/
inductive ReuseSupported (context : Fir.Wasm.Context)
    (facts : ReuseCapacityFacts) : LCNF.LetDecl .impure → Prop where
  | intro
      (tokenId : FVarId) (info : LCNF.CtorInfo) (updateHeader : Bool)
      (args : Array (LCNF.Arg .impure))
      (argumentCode : List Fir.Wasm.Instruction)
      (fieldKinds : Array AbiKind) (resultKind : AbiKind)
      (evidence : ReuseCapacityEvidence)
      (valueEq : decl.value = .reuse tokenId info updateHeader args)
      (tagFits : Fir.Wasm.constructorTagFitsI32 info = true)
      (valueKind : Fir.Wasm.letValueKind decl = .ok resultKind)
      (tokenCompiled :
        Fir.Wasm.getLocal context tokenId =
          .ok (.localGet tokenId, .reuseToken))
      (argumentsCompiled :
        Fir.Wasm.compileArgs context args =
          .ok (argumentCode, fieldKinds))
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, resultKind))
      (operationWellFormed :
        (RuntimeOp.reuse info updateHeader fieldKinds resultKind).abiWellFormed =
          true)
      (capacityFitting :
        findFittingReuseCapacityEvidence? facts tokenId info = some evidence)
      (resultCompatible :
        evidence = .emptyToken ∨ resultKind = .tobject)
      (objectFieldsFit : info.size < UInt32.size)
      (usizeFieldsFit : info.usize < UInt32.size)
      (scalarBytesFit : info.ssize < UInt32.size) :
      ReuseSupported context facts decl

/--
Source compatibility and the ordinary runtime relation reconstruct every
representation-specific premise of checked concrete unboxing.

For a tagged object, the concrete read is representation-polymorphic. For a
heap object, the source scalar constructor identifies the same boxed kind as
the live-cell relation, which recovers the frozen descriptor and checked
linear-memory read.
-/
theorem ConcreteRuntimeRel.unboxFacts_of_sourceCompatible
    {concrete : ConcreteRuntimeState}
    {witness : RefinementWitness} {runtime : RuntimeState}
    {word : Word32} {kind : BoxedScalarKind}
    {sourceObject sourceValue : Value}
    (runtimeRelated : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 word) sourceObject)
    (compatible :
      SourceUnboxKindCompatible runtime kind sourceObject)
    (unboxed :
      unbox runtime kind.semanticType sourceObject = .ok sourceValue) :
    ∃ scalar,
      UnboxObjectRel witness word kind sourceObject ∧
        readBoxedScalar concrete.heap kind word = .ok scalar ∧
        sourceValue = scalar.semanticValue := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | tagged taggedRelated =>
          cases compatible
          obtain ⟨concreteRead, semanticRead, _⟩ :=
            runtimeRelated.heap.readBoxedScalar_tagged_refines
              taggedRelated kind
          exact ⟨BoxedScalar.ofPayload kind _, .tagged taggedRelated,
            concreteRead, Except.ok.inj (unboxed.symm.trans semanticRead)⟩
      | heap heapRelated =>
          cases compatible with
          | heap storedType scalar found live compatibleObjectEq
              compatibleKindEq =>
              cases heapRelated with
              | mapped mapped =>
                  obtain ⟨actualCell, actualFound, cellRelated⟩ :=
                    runtimeRelated.heap.concreteToSemantic _ _ mapped
                  rw [found] at actualFound
                  injection actualFound with cellEq
                  subst actualCell
                  cases cellRelated with
                  | dead semanticCount semanticDead descriptor deadRelated =>
                      simp_all
                  | live liveRelated =>
                      cases liveRelated with
                      | constructor descriptor objectEq objectRelated
                          headerRead headerKind refCount persistent cellLive =>
                          rw [compatibleObjectEq] at objectEq
                          contradiction
                      | @boxed actualKind actualScalar header cell descriptor
                          objectEq boxedRelated refCount persistent cellLive =>
                          have boxedEq :
                              HeapObject.boxed actualKind.semanticType
                                  actualScalar.semanticValue =
                                HeapObject.boxed storedType
                                  scalar.semanticValue :=
                            objectEq.symm.trans compatibleObjectEq
                          have scalarValueEq :
                              actualScalar.semanticValue =
                                scalar.semanticValue :=
                            (HeapObject.boxed.inj boxedEq).2
                          have actualKindEq :
                              actualScalar.kind = scalar.kind := by
                            cases actualScalar <;> cases scalar <;>
                              simp_all [BoxedScalar.semanticValue,
                                BoxedScalar.kind]
                          have descriptorKindEq :
                              actualKind = kind := by
                            exact boxedRelated.scalarKind.symm.trans
                              (actualKindEq.trans compatibleKindEq)
                          subst actualKind
                          obtain ⟨decoded, concreteRead, valueEq, _⟩ :=
                            runtimeRelated.heap.readBoxedScalar_heap_refines
                              mapped descriptor unboxed
                          exact ⟨decoded, .heap (.mapped mapped) descriptor,
                            concreteRead, valueEq⟩
                      | natural descriptor objectEq headerRead headerKind
                          marker extent limbsFit decoded refCount persistent
                          cellLive =>
                          rw [compatibleObjectEq] at objectEq
                          contradiction
                      | integer descriptor objectEq objectRelated refCount
                          persistent cellLive =>
                          rw [compatibleObjectEq] at objectEq
                          contradiction
                      | string descriptor objectEq objectRelated refCount
                          persistent cellLive =>
                          rw [compatibleObjectEq] at objectEq
                          contradiction
                      | closure closureRelated =>
                          obtain ⟨function, arity, captures, objectEq⟩ :=
                            closureRelated.objectEq
                          rw [compatibleObjectEq] at objectEq
                          contradiction

/-- Direct source `let` evaluation is deterministic at fixed source state,
environment, and declaration. -/
theorem SourceLetResult.deterministic
    {context : Fir.Wasm.Context}
    {sourceRuntime leftRuntime rightRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {leftValue rightValue : Value}
    (left :
      SourceLetResult context sourceRuntime sourceEnv decl leftRuntime
        leftValue)
    (right :
      SourceLetResult context sourceRuntime sourceEnv decl rightRuntime
        rightValue) :
    leftRuntime = rightRuntime ∧ leftValue = rightValue := by
  simp only [SourceLetResult] at left right
  rw [left] at right
  have pairEq :
      (leftRuntime, LetAction.value leftValue) =
        (rightRuntime, LetAction.value rightValue) :=
    Except.ok.inj right
  exact ⟨congrArg Prod.fst pairEq,
    LetAction.value.inj (congrArg Prod.snd pairEq)⟩

/-- Invert a successful source constructor `let` into the exact evaluated
semantic argument array and source allocation step. -/
theorem sourceLetResult_constructor_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {info : LCNF.CtorInfo}
    {args : Array (LCNF.Arg .impure)}
    (valueEq : decl.value = .ctor info args)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ semanticArgs,
      evalArgs sourceEnv args = .ok semanticArgs ∧
        allocCtor sourceRuntime info semanticArgs =
          .ok (nextRuntime, sourceValue) := by
  simp only [SourceLetResult, evalLetValue, valueEq] at sourceStep
  cases evaluated : evalArgs sourceEnv args with
  | error fault =>
      rw [evaluated] at sourceStep
      contradiction
  | ok semanticArgs =>
      rw [evaluated] at sourceStep
      simp only [Bind.bind, Except.bind] at sourceStep
      cases allocated : allocCtor sourceRuntime info semanticArgs with
      | error fault =>
          rw [allocated] at sourceStep
          contradiction
      | ok result =>
          rw [allocated] at sourceStep
          rcases result with ⟨actualRuntime, actualValue⟩
          change
            Except.ok (actualRuntime, LetAction.value actualValue) =
              Except.ok (nextRuntime, LetAction.value sourceValue)
            at sourceStep
          have pairEq :
              (actualRuntime, LetAction.value actualValue) =
                (nextRuntime, LetAction.value sourceValue) :=
            Except.ok.inj sourceStep
          have runtimeEq : actualRuntime = nextRuntime :=
            congrArg Prod.fst pairEq
          have valueEq' : actualValue = sourceValue :=
            LetAction.value.inj (congrArg Prod.snd pairEq)
          subst actualRuntime
          subst actualValue
          exact ⟨semanticArgs, rfl, allocated⟩

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
Invert a successful typed-unbox declaration to its source object lookup and
canonical scalar-kind operation. No concrete representation evidence is
introduced.
-/
theorem sourceLetResult_unbox_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {objectId : FVarId} {kind : BoxedScalarKind}
    (valueEq : decl.value = .unbox objectId)
    (resultTypeEq : decl.type = kind.semanticType)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ sourceObject,
      nextRuntime = sourceRuntime ∧
        lookup sourceEnv objectId = some sourceObject ∧
        unbox sourceRuntime kind.semanticType sourceObject =
          .ok sourceValue := by
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
      rw [lookupSucceeded, resultTypeEq] at sourceStep
      simp only [Bind.bind, Except.bind] at sourceStep
      cases evaluated :
          unbox sourceRuntime kind.semanticType sourceObject with
      | error fault =>
          rw [evaluated] at sourceStep
          contradiction
      | ok actualValue =>
          rw [evaluated] at sourceStep
          have pairEq :
              (sourceRuntime, LetAction.value actualValue) =
                (nextRuntime, LetAction.value sourceValue) :=
            Except.ok.inj sourceStep
          have runtimeEq : sourceRuntime = nextRuntime :=
            congrArg Prod.fst pairEq
          have valueEq' : actualValue = sourceValue :=
            LetAction.value.inj (congrArg Prod.snd pairEq)
          subst actualValue
          exact ⟨sourceObject, runtimeEq.symm, rfl, evaluated⟩

/--
Invert a successful boxing declaration to the source scalar lookup and
semantic boxing step. This is source evaluation inversion only.
-/
theorem sourceLetResult_box_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {scalarId : FVarId} {kind : BoxedScalarKind}
    (valueEq : decl.value = .box kind.semanticType scalarId)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ sourceScalar,
      lookup sourceEnv scalarId = some sourceScalar ∧
        box sourceRuntime kind.semanticType sourceScalar =
          .ok (nextRuntime, sourceValue) := by
  unfold SourceLetResult at sourceStep
  simp only [evalLetValue, valueEq] at sourceStep
  cases sourceLookup : lookup sourceEnv scalarId with
  | none =>
      have lookupFailed :
          lookupValue sourceEnv scalarId = .error (.unknownVar scalarId) := by
        simp [lookupValue, sourceLookup]
      rw [lookupFailed] at sourceStep
      contradiction
  | some sourceScalar =>
      have lookupSucceeded :
          lookupValue sourceEnv scalarId = .ok sourceScalar := by
        simp [lookupValue, sourceLookup]
      rw [lookupSucceeded] at sourceStep
      simp only [Bind.bind, Except.bind] at sourceStep
      cases evaluated :
          box sourceRuntime kind.semanticType sourceScalar with
      | error fault =>
          rw [evaluated] at sourceStep
          contradiction
      | ok result =>
          rw [evaluated] at sourceStep
          have pairEq :
              (result.1, LetAction.value result.2) =
                (nextRuntime, LetAction.value sourceValue) :=
            Except.ok.inj sourceStep
          have runtimeEq : result.1 = nextRuntime :=
            congrArg Prod.fst pairEq
          have valueEq' : result.2 = sourceValue :=
            LetAction.value.inj (congrArg Prod.snd pairEq)
          subst nextRuntime
          subst sourceValue
          exact ⟨sourceScalar, rfl, evaluated⟩

/--
Invert a successful reset declaration to the source object lookup and
semantic reset step. This is source evaluation inversion only; in particular,
it does not classify the object representation or reset branch.
-/
theorem sourceLetResult_reset_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {count : Nat} {objectId : FVarId}
    (valueEq : decl.value = .reset count objectId)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ sourceObject,
      lookup sourceEnv objectId = some sourceObject ∧
        reset sourceRuntime count sourceObject =
          .ok (nextRuntime, sourceValue) := by
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
      cases evaluated : reset sourceRuntime count sourceObject with
      | error fault =>
          rw [evaluated] at sourceStep
          contradiction
      | ok result =>
          rw [evaluated] at sourceStep
          have pairEq :
              (result.1, LetAction.value result.2) =
                (nextRuntime, LetAction.value sourceValue) :=
            Except.ok.inj sourceStep
          have runtimeEq : result.1 = nextRuntime :=
            congrArg Prod.fst pairEq
          have valueEq' : result.2 = sourceValue :=
            LetAction.value.inj (congrArg Prod.snd pairEq)
          subst nextRuntime
          subst sourceValue
          exact ⟨sourceObject, rfl, evaluated⟩

/--
Invert a successful reuse declaration to the exact source token, evaluated
field array, and semantic reuse step. No concrete representation or token
branch is selected by this source-evaluation fact.
-/
theorem sourceLetResult_reuse_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {tokenId : FVarId} {info : LCNF.CtorInfo}
    {updateHeader : Bool} {args : Array (LCNF.Arg .impure)}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ sourceToken semanticFields,
      lookup sourceEnv tokenId = some sourceToken ∧
        evalArgs sourceEnv args = .ok semanticFields ∧
        reuse sourceRuntime sourceToken info updateHeader semanticFields =
          .ok (nextRuntime, sourceValue) := by
  simp only [SourceLetResult, evalLetValue, valueEq] at sourceStep
  cases tokenLookup : lookup sourceEnv tokenId with
  | none =>
      have lookupFailed :
          lookupValue sourceEnv tokenId = .error (.unknownVar tokenId) := by
        simp [lookupValue, tokenLookup]
      rw [lookupFailed] at sourceStep
      contradiction
  | some sourceToken =>
      have lookupSucceeded :
          lookupValue sourceEnv tokenId = .ok sourceToken := by
        simp [lookupValue, tokenLookup]
      rw [lookupSucceeded] at sourceStep
      simp only [Bind.bind, Except.bind] at sourceStep
      cases evaluated : evalArgs sourceEnv args with
      | error fault =>
          rw [evaluated] at sourceStep
          contradiction
      | ok semanticFields =>
          rw [evaluated] at sourceStep
          simp only [Bind.bind, Except.bind] at sourceStep
          cases reused :
              reuse sourceRuntime sourceToken info updateHeader semanticFields
          with
          | error fault =>
              rw [reused] at sourceStep
              contradiction
          | ok result =>
              rw [reused] at sourceStep
              rcases result with ⟨actualRuntime, actualValue⟩
              change
                Except.ok (actualRuntime, LetAction.value actualValue) =
                  Except.ok (nextRuntime, LetAction.value sourceValue)
                at sourceStep
              have pairEq :
                  (actualRuntime, LetAction.value actualValue) =
                    (nextRuntime, LetAction.value sourceValue) :=
                Except.ok.inj sourceStep
              have runtimeEq : actualRuntime = nextRuntime :=
                congrArg Prod.fst pairEq
              have valueEq' : actualValue = sourceValue :=
                LetAction.value.inj (congrArg Prod.snd pairEq)
              subst actualRuntime
              subst actualValue
              exact ⟨sourceToken, semanticFields, rfl, rfl, reused⟩

/-- Every successful sharing observation returns the direct `UInt8` lane. -/
theorem isShared_ok_eq_uint8
    {runtime : RuntimeState} {object result : Value}
    (evaluated : isShared runtime object = .ok result) :
    ∃ shared, result = .scalar (.uint8 shared) := by
  cases object with
  | object reference =>
      cases reference with
      | tagged payload =>
          simp [isShared] at evaluated
          exact ⟨1, evaluated.symm⟩
      | heap location =>
          simp only [isShared, Bind.bind, Except.bind] at evaluated
          cases liveResult : getLiveCell runtime location with
          | error fault =>
              rw [liveResult] at evaluated
              contradiction
          | ok cell =>
              rw [liveResult] at evaluated
              injection evaluated with resultEq
              exact ⟨if cell.persistent || cell.rc != 1 then 1 else 0,
                resultEq.symm⟩
  | _ =>
      simp [isShared] at evaluated

/--
Invert a successful source `isShared` declaration without introducing an
operation certificate.
-/
theorem sourceLetResult_isShared_eq
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {sourceValue : Value}
    {objectId : FVarId}
    (valueEq : decl.value = .isShared objectId)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue) :
    ∃ sourceObject shared,
      nextRuntime = sourceRuntime ∧
        sourceValue = .scalar (.uint8 shared) ∧
        lookup sourceEnv objectId = some sourceObject ∧
        isShared sourceRuntime sourceObject =
          .ok (.scalar (.uint8 shared)) := by
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
      cases evaluated : isShared sourceRuntime sourceObject with
      | error fault =>
          rw [evaluated] at sourceStep
          contradiction
      | ok actualValue =>
          rw [evaluated] at sourceStep
          have pairEq :
              (sourceRuntime, LetAction.value actualValue) =
                (nextRuntime, LetAction.value sourceValue) :=
            Except.ok.inj sourceStep
          have runtimeEq : sourceRuntime = nextRuntime :=
            congrArg Prod.fst pairEq
          have valueEq' : actualValue = sourceValue :=
            LetAction.value.inj (congrArg Prod.snd pairEq)
          subst sourceValue
          obtain ⟨shared, resultEq⟩ :=
            isShared_ok_eq_uint8 evaluated
          subst actualValue
          exact ⟨sourceObject, shared, runtimeEq.symm, rfl, rfl, evaluated⟩

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

/--
The structural allocating invariant: exact compiler-local frame shape paired
with the remaining source-path wasm32 address-space budget.
-/
def ConcreteBudgetedLocalFrame
    (sourceFunction : Fir.Wasm.Function)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness ∧
    targetStore.host.runtime.heap.AddressSpaceBudget remainingBytes

/--
Budgeted local-frame invariant for pure integer external spines. In addition
to the ordinary frame and heap budget, the currently installed concrete
external implementation satisfies the reusable integer-result family law.
`replaceRuntime` preserves that implementation field.
-/
def ConcreteBudgetedIntegerExternalFrame
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteBudgetedLocalFrame sourceFunction remainingBytes sourceRuntime
      sourceEnv targetStore targetLocals witness ∧
    targetStore.host.externals.IntegerResultRefines externals

/--
Budgeted local-frame invariant for pure natural-result external spines. The
natural implementation law is representation-polymorphic, so the threaded
witness may remain unchanged, gain a promoted descriptor, or bind a fresh
heap location after each call.
-/
def ConcreteBudgetedNaturalExternalFrame
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteBudgetedLocalFrame sourceFunction remainingBytes sourceRuntime
      sourceEnv targetStore targetLocals witness ∧
    FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
      targetStore.host.externals externals

/--
Budgeted local-frame invariant for nonallocating scalar-result external
spines. The heap budget is unchanged by each scalar call, while the installed
implementation law is threaded across surrounding direct operations.
-/
def ConcreteBudgetedScalarExternalFrame
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteBudgetedLocalFrame sourceFunction remainingBytes sourceRuntime
      sourceEnv targetStore targetLocals witness ∧
    FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
      targetStore.host.externals externals

/--
One structural invariant for spines that mix every currently proved pure
external result family. The heap budget and local frame are shared; each
installed-handler law is retained independently.
-/
def ConcreteBudgetedPureExternalFrame
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteBudgetedLocalFrame sourceFunction remainingBytes sourceRuntime
      sourceEnv targetStore targetLocals witness ∧
    targetStore.host.externals.IntegerResultRefines externals ∧
    FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
      targetStore.host.externals externals ∧
    FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
      targetStore.host.externals externals

/--
The pure-external budgeted frame extended with the immutable descriptor-table
agreement required by recursive ownership operations. The agreement is
proof-side state, not a source admission fact: direct and external steps
preserve both tables and re-establish it compositionally.
-/
def ConcreteBudgetedPureExternalOwnershipFrame
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteBudgetedPureExternalFrame sourceFunction externals remainingBytes
      sourceRuntime sourceEnv targetStore targetLocals witness ∧
    targetStore.host.closureDescriptors = witness.closureDescriptors

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

/--
Resource-indexed direct-`let` runtime law.

`letCost` assigns a source-level reservation to each admitted declaration.
`Invariant remainingBytes ...` describes the concrete resources available
before a step. The runtime implementation consumes at most the declaration's
reservation, advances the logical index by that reservation, preserves the
installed external implementation and the two immutable closure-descriptor
tables, and establishes the invariant at the residual index. Exact-cost
families consume the same physical extent; a conservative family may return
unused physical headroom by budget weakening. These preservation facts are
properties of the generated direct helper, not source/target certificates;
they let later external calls and recursive ownership effects rely on stable
concrete metadata.
-/
def DirectLetRuntimeRefinesWithCost
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (Supported : LCNF.LetDecl .impure → Prop)
    (letCost : LCNF.LetDecl .impure → Nat)
    (Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop) : Prop :=
  ∀ {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {sourceValue : Value}
      {valueCode : List Fir.Wasm.Instruction}
      {targetValue : Wasm.Program}
      {targetStore : Wasm.Store Host}
      {targetLocals : Wasm.Locals}
      {resultIndex remainingBytes : Nat}
      {witness : RefinementWitness},
    Supported decl →
      letCost decl ≤ remainingBytes →
      Invariant remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness →
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
        nextStore.host.externals = targetStore.host.externals ∧
          nextStore.host.closureDescriptors =
              targetStore.host.closureDescriptors ∧
            nextWitness.closureDescriptors = witness.closureDescriptors ∧
              Invariant (remainingBytes - letCost decl) nextRuntime
                (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
                nextWitness

/--
Resource-indexed external-`let` runtime law.

Unlike a direct declaration, a pure external may allocate a result whose size
depends on the actual source response. `ExternalSupported` therefore carries
the step cost as an execution index. The law still inverts and executes the
production compiler/adapter prefix; it does not accept target instructions,
numeric indices, or a per-program simulation certificate.
-/
def ExternalLetRuntimeRefinesWithCost
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (externals : ExternalImpl)
    (ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop)
    (Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop) : Prop :=
  ∀ {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {valueCode : List Fir.Wasm.Instruction}
      {targetValue : Wasm.Program}
      {targetStore : Wasm.Store Host}
      {targetLocals : Wasm.Locals}
      {resultIndex remainingBytes stepCost : Nat}
      {witness : RefinementWitness},
    ExternalSupported sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost →
      stepCost ≤ remainingBytes →
      Invariant remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness →
      SourceExternalLetResult context externals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue →
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness →
      Fir.Wasm.compileLetValue context decl = .ok valueCode →
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue →
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex →
      ∃ nextStore nextLocals nextWitness,
        ExternalLetStepSimulates context sourceFunction module hostEnv externals
          decl continuation targetValue sourceRuntime nextRuntime sourceEnv
          sourceValue targetStore nextStore targetLocals nextLocals resultIndex
          witness nextWitness ∧
        nextStore.host.externals = targetStore.host.externals ∧
          nextStore.host.closureDescriptors =
              targetStore.host.closureDescriptors ∧
            nextWitness.closureDescriptors = witness.closureDescriptors ∧
              Invariant (remainingBytes - stepCost) nextRuntime
                (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
                nextWitness

/--
Uniform runtime condition for one successful no-result effect node.

The source admission and executable source step contain no target evidence.
For every successful production compiler/adapter output, the implementation
law recovers the adapted continuation, executes the generated effect prefix,
and re-establishes the resource invariant at unchanged allocation budget.
This is an operation-family theorem condition, not a per-program certificate.
-/
def EffectRuntimeRefines
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (EffectSupported : EffectSupportedPredicate)
    (Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop) : Prop :=
  ∀ {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {code continuation : LCNF.Code .impure}
      {target : Wasm.Program}
      {targetStore : Wasm.Store Host}
      {targetLocals : Wasm.Locals}
      {remainingBytes : Nat}
      {witness : RefinementWitness},
    EffectSupported sourceRuntime sourceEnv code continuation nextRuntime →
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation →
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness →
      Invariant remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness →
      CodeAdapted context sourceModule sourceFunction labels code target →
      ∃ targetRest nextStore nextWitness,
        CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest ∧
          EffectStepSimulates context sourceModule sourceFunction labels module
            hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
            targetRest targetStore nextStore targetLocals witness nextWitness ∧
          Invariant remainingBytes nextRuntime sourceEnv nextStore targetLocals
            nextWitness

/-- The empty effect family satisfies every invariant vacuously. -/
theorem effectRuntimeRefines_noEffects
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop} :
    EffectRuntimeRefines context sourceModule sourceFunction labels module
      hostEnv NoEffectsSupported Invariant := by
  intro sourceRuntime nextRuntime sourceEnv code continuation target targetStore
    targetLocals remainingBytes witness supported
  exact False.elim supported

/--
Uniform effect refinement is closed under disjoint union of source admission
families.

This is the general composition theorem: operation proofs are established
once for a shared invariant, and arbitrary structural source evaluations may
then interleave either family without adding per-node target evidence.
-/
theorem EffectRuntimeRefines.or
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {left right : EffectSupportedPredicate}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (leftRefines :
      EffectRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv left Invariant)
    (rightRefines :
      EffectRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv right Invariant) :
    EffectRuntimeRefines context sourceModule sourceFunction labels module
      hostEnv (EffectSupportedOr left right) Invariant := by
  intro sourceRuntime nextRuntime sourceEnv code continuation target targetStore
    targetLocals remainingBytes witness supported sourceStep stateRelated
    invariant adapted
  cases supported with
  | left supported =>
      exact leftRefines supported sourceStep stateRelated invariant adapted
  | right supported =>
      exact rightRefines supported sourceStep stateRelated invariant adapted

/--
Resolver/adaptor alignment specialized to the concrete reference-count
increment host selected by a compiler-derived runtime-call slot.
-/
theorem ConcreteSupportedExport.incrementCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
    {amount : Nat}
    {check : Bool}
    {id : Nat}
    (found :
      callIndex? sourceModule (.runtime (.inc amount check)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (incrementContract amount check) ∧
        imp.params.length = 1 ∧
        imp.results.length = 0 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    supportedExport.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = incrementStep amount check initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, incrementFn]
      using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 0 at results
    exact results

/--
Resolver/adaptor alignment specialized to the concrete recursive decrement
host selected by a compiler-derived runtime-call slot.
-/
theorem ConcreteSupportedExport.decrementCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {id : Nat}
    (found :
      callIndex? sourceModule
          (.runtime (.dec amount check objectFields?)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (decrementContract amount check objectFields?) ∧
        imp.params.length = 1 ∧
        imp.results.length = 0 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    supportedExport.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = decrementStep amount check objectFields? initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, decrementFn]
      using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 0 at results
    exact results

/--
Resolver/adaptor alignment specialized to the concrete explicit-delete host
selected by the compiler-derived runtime-call slot.
-/
theorem ConcreteSupportedExport.deleteCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
    {id : Nat}
    (found :
      callIndex? sourceModule (.runtime .delete) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some deleteContract ∧
        imp.params.length = 1 ∧
        imp.results.length = 0 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    supportedExport.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = deleteStep initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, deleteFn]
      using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 0 at results
    exact results

/--
Resolver/adaptor alignment specialized to the concrete constructor-tag host
selected by the compiler-derived runtime-call slot.
-/
theorem ConcreteSupportedExport.setTagCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
    {tag id : Nat}
    (found :
      callIndex? sourceModule (.runtime (.setTag tag)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (setTagContract tag) ∧
        imp.params.length = 1 ∧
        imp.results.length = 0 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    supportedExport.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = setTagStep tag initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, setTagFn]
      using contracted
  · change imp.params.length = 1 at params
    exact params
  · change imp.results.length = 0 at results
    exact results

/--
Resolver/adaptor alignment specialized to the concrete object-field setter
selected by the compiler-derived runtime-call slot.
-/
theorem ConcreteSupportedExport.objectSetCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
    {index : Nat}
    {fieldKind : AbiKind}
    {id : Nat}
    (found :
      callIndex? sourceModule (.runtime (.objectSet index fieldKind)) =
        some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (objectSetContract index fieldKind) ∧
        imp.params.length = 2 ∧
        imp.results.length = 0 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    supportedExport.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = objectSetStep index fieldKind initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, objectSetFn]
      using contracted
  · change imp.params.length = 2 at params
    exact params
  · change imp.results.length = 0 at results
    exact results

/--
Resolver/adaptor alignment specialized to the concrete `USize` field setter
selected by the compiler-derived runtime-call slot.
-/
theorem ConcreteSupportedExport.usizeSetCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
    {index id : Nat}
    (found :
      callIndex? sourceModule (.runtime (.usizeSet index)) = some id) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? = some (usizeSetContract index) ∧
        imp.params.length = 2 ∧
        imp.results.length = 0 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    supportedExport.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result = usizeSetStep index initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, usizeSetFn]
      using contracted
  · change imp.params.length = 2 at params
    exact params
  · change imp.results.length = 0 at results
    exact results

/--
Resolver/adaptor alignment specialized to the kind-indexed concrete packed
scalar setter selected by the compiler-derived runtime-call slot.
-/
theorem ConcreteSupportedExport.scalarSetCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {code : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context code sourceModule sourceFunction
        target hosts exportName)
    {slotIndex byteOffset id : Nat}
    {fieldKind : AbiKind}
    (found :
      callIndex? sourceModule
          (.runtime (.scalarSet slotIndex byteOffset fieldKind)) =
        some id)
    (supportedKind : PackedIntegerAbiKind fieldKind) :
    ∃ imp,
      target.wasmModule.imports[id]? = some imp ∧
        id < target.wasmModule.imports.length ∧
        hosts.spec.contracts[id]? =
          some (scalarSetContract slotIndex byteOffset fieldKind) ∧
        imp.params.length = 2 ∧
        imp.results.length = 0 := by
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    supportedExport.runtimeCallsAligned found
  refine ⟨imp, imported, inBounds, ?_, ?_, ?_⟩
  · change
      hosts.spec.contracts[id]? =
        some (fun initial args result =>
          result =
            scalarSetStep slotIndex byteOffset fieldKind initial args)
    have supported :
        fieldKind = .uint8 ∨ fieldKind = .uint16 ∨
          fieldKind = .uint32 ∨ fieldKind = .uint64 := by
      cases fieldKind <;> simp [PackedIntegerAbiKind] at supportedKind ⊢
    have resolved :=
      hostFn?_scalarSet_of_packedInteger
        (slotIndex := slotIndex) (byteOffset := byteOffset) supported
    simpa only [resolvedContract?, resolved, Option.map_some, scalarSetFn]
      using contracted
  · change imp.params.length = 2 at params
    exact params
  · change imp.results.length = 0 at results
    exact results

/--
The compiler-erased persistent ownership family implements the generic effect
condition for every invariant.

The production compiler inversion recovers the continuation target. Source and
concrete execution then both take a no-op step, preserving runtime, store,
locals, witness, externals, trace, and the unchanged allocation budget.
-/
theorem effectRuntimeRefines_persistentOwnership
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop} :
    EffectRuntimeRefines context sourceModule sourceFunction labels module
      hostEnv PersistentOwnershipEffectSupported Invariant := by
  intro sourceRuntime nextRuntime sourceEnv code continuation target targetStore
    targetLocals remainingBytes witness supported _sourceStep stateRelated
    invariant adapted
  cases supported with
  | inc =>
      have continuationAdapted := CodeAdapted.incPersistent_eq adapted
      exact ⟨target, targetStore, witness, continuationAdapted,
        effectStepSimulates_inc_persistent stateRelated continuationAdapted,
        invariant⟩
  | dec =>
      have continuationAdapted := CodeAdapted.decPersistent_eq adapted
      exact ⟨target, targetStore, witness, continuationAdapted,
        effectStepSimulates_dec_persistent stateRelated continuationAdapted,
        invariant⟩

/--
Ordinary reference-count increment implements the generic effect condition
for the complete budgeted pure-external frame.

Compiler inversion and resolver alignment recover the generated local/import
indices and concrete increment contract. The successful header update
preserves the heap frontier, so it consumes no allocation budget while
retaining local-frame shape, witness, and all installed external family laws.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ordinaryIncrement
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OrdinaryIncrementEffectSupported context)
      (ConcreteBudgetedPureExternalFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | inc sourceRuntime nextRuntime sourceEnv objectId amount check continuation
      objectKind sourceObject objectCompiled objectRefines objectLookup updated
      fits =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetEq⟩ :=
        CodeAdapted.inc_eq supportedExport.localsAligned objectCompiled adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        supportedExport.incrementCall callFound
      obtain ⟨heap, step, cursor, _capacity⟩ :=
        effectStepSimulates_inc_with_capacity objectLookup updated stateRelated
          objectCompiled objectFound kindAt objectRefines callFound
          continuationAdapted imported supportedExport.hostsSatisfy inBounds
          contracted params results fits
      rcases invariant with
        ⟨⟨frameAligned, budget⟩, integerImplementation,
          naturalImplementation, scalarImplementation⟩
      have nextBudget : heap.AddressSpaceBudget remainingBytes := by
        constructor
        · simpa [cursor] using budget.cursorPositive
        · simpa [cursor] using budget.endWithinAddressSpace
      have nextInvariant :
          ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        have externalsEq :
            (replaceHeap targetStore heap).host.externals =
              targetStore.host.externals := by
          simp [replaceHeap, clearFailure]
        refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
        · rw [externalsEq]
          exact integerImplementation
        · rw [externalsEq]
          exact naturalImplementation
        · rw [externalsEq]
          exact scalarImplementation
      exact ⟨targetRest, replaceHeap targetStore heap, witness,
        continuationAdapted, step, nextInvariant⟩

/--
Ordinary recursive decrement implements the generic effect condition for the
ownership-aware pure-external frame.

The compiler and resolver recover the exact unary call from source facts.
Descriptor agreement comes only from the threaded invariant, discharging
recursive closure-capture release. The executable decrement preserves the
frontier and therefore consumes no allocation budget.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ordinaryDecrement
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OrdinaryDecrementEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | dec sourceRuntime nextRuntime sourceEnv objectId amount check objectFields?
      continuation objectKind sourceObject objectCompiled objectRefines
      objectLookup updated =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetEq⟩ :=
        CodeAdapted.dec_eq supportedExport.localsAligned objectCompiled adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        supportedExport.decrementCall callFound
      obtain ⟨heap, step, cursor, _capacity⟩ :=
        effectStepSimulates_dec_with_capacity objectLookup updated stateRelated
          objectCompiled objectFound kindAt objectRefines invariant.2 callFound
          continuationAdapted imported supportedExport.hostsSatisfy inBounds
          contracted params results
      rcases invariant.1 with
        ⟨⟨frameAligned, budget⟩, integerImplementation,
          naturalImplementation, scalarImplementation⟩
      have nextBudget : heap.AddressSpaceBudget remainingBytes := by
        constructor
        · simpa [cursor] using budget.cursorPositive
        · simpa [cursor] using budget.endWithinAddressSpace
      have nextBaseInvariant :
          ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        have externalsEq :
            (replaceHeap targetStore heap).host.externals =
              targetStore.host.externals := by
          simp [replaceHeap, clearFailure]
        refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
        · rw [externalsEq]
          exact integerImplementation
        · rw [externalsEq]
          exact naturalImplementation
        · rw [externalsEq]
          exact scalarImplementation
      have nextInvariant :
          ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        exact ⟨nextBaseInvariant, by
          simpa [replaceHeap, clearFailure] using invariant.2⟩
      exact ⟨targetRest, replaceHeap targetStore heap, witness,
        continuationAdapted, step, nextInvariant⟩

/--
Successful explicit deletion implements the generic effect condition for the
complete budgeted pure-external frame.

Production inversion and resolver alignment recover the generated unary
delete call. Both an ordinary header release and the erased/zero no-op preserve
the heap frontier exactly, so deletion consumes no allocation budget and
retains all installed pure-external laws.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ordinaryDelete
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OrdinaryDeleteEffectSupported context)
      (ConcreteBudgetedPureExternalFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | del sourceRuntime nextRuntime sourceEnv objectId continuation objectKind
      sourceObject objectCompiled objectLookup updated =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetEq⟩ :=
        CodeAdapted.del_eq supportedExport.localsAligned objectCompiled adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        supportedExport.deleteCall callFound
      obtain ⟨heap, step, _capacity, cursor⟩ :=
        effectStepSimulates_delete_with_capacity objectLookup updated
          stateRelated objectCompiled objectFound kindAt callFound
          continuationAdapted imported supportedExport.hostsSatisfy inBounds
          contracted params results
      rcases invariant with
        ⟨⟨frameAligned, budget⟩, integerImplementation,
          naturalImplementation, scalarImplementation⟩
      have nextBudget : heap.AddressSpaceBudget remainingBytes := by
        constructor
        · simpa [cursor] using budget.cursorPositive
        · simpa [cursor] using budget.endWithinAddressSpace
      have nextInvariant :
          ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        have externalsEq :
            (replaceHeap targetStore heap).host.externals =
              targetStore.host.externals := by
          simp [replaceHeap, clearFailure]
        refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
        · rw [externalsEq]
          exact integerImplementation
        · rw [externalsEq]
          exact naturalImplementation
        · rw [externalsEq]
          exact scalarImplementation
      exact ⟨targetRest, replaceHeap targetStore heap, witness,
        continuationAdapted, step, nextInvariant⟩

/--
Ordinary increment also preserves the ownership-aware frame.

This specialization reuses the same executable increment boundary while
threading immutable host/witness closure-descriptor agreement for composition
with recursive decrement nodes.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ordinaryIncrement_ownership
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OrdinaryIncrementEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | inc sourceRuntime nextRuntime sourceEnv objectId amount check continuation
      objectKind sourceObject objectCompiled objectRefines objectLookup updated
      fits =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetEq⟩ :=
        CodeAdapted.inc_eq supportedExport.localsAligned objectCompiled adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        supportedExport.incrementCall callFound
      obtain ⟨heap, step, cursor, _capacity⟩ :=
        effectStepSimulates_inc_with_capacity objectLookup updated stateRelated
          objectCompiled objectFound kindAt objectRefines callFound
          continuationAdapted imported supportedExport.hostsSatisfy inBounds
          contracted params results fits
      rcases invariant.1 with
        ⟨⟨frameAligned, budget⟩, integerImplementation,
          naturalImplementation, scalarImplementation⟩
      have nextBudget : heap.AddressSpaceBudget remainingBytes := by
        constructor
        · simpa [cursor] using budget.cursorPositive
        · simpa [cursor] using budget.endWithinAddressSpace
      have nextBaseInvariant :
          ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        have externalsEq :
            (replaceHeap targetStore heap).host.externals =
              targetStore.host.externals := by
          simp [replaceHeap, clearFailure]
        refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
        · rw [externalsEq]
          exact integerImplementation
        · rw [externalsEq]
          exact naturalImplementation
        · rw [externalsEq]
          exact scalarImplementation
      have nextInvariant :
          ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        exact ⟨nextBaseInvariant, by
          simpa [replaceHeap, clearFailure] using invariant.2⟩
      exact ⟨targetRest, replaceHeap targetStore heap, witness,
        continuationAdapted, step, nextInvariant⟩

/--
Explicit deletion preserves the ownership-aware frame.

The concrete operation changes only heap memory (or is the erased-zero no-op),
so host/witness closure-descriptor agreement remains available to subsequent
recursive decrement nodes.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ordinaryDelete_ownership
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OrdinaryDeleteEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | del sourceRuntime nextRuntime sourceEnv objectId continuation objectKind
      sourceObject objectCompiled objectLookup updated =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetEq⟩ :=
        CodeAdapted.del_eq supportedExport.localsAligned objectCompiled adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        supportedExport.deleteCall callFound
      obtain ⟨heap, step, _capacity, cursor⟩ :=
        effectStepSimulates_delete_with_capacity objectLookup updated
          stateRelated objectCompiled objectFound kindAt callFound
          continuationAdapted imported supportedExport.hostsSatisfy inBounds
          contracted params results
      rcases invariant.1 with
        ⟨⟨frameAligned, budget⟩, integerImplementation,
          naturalImplementation, scalarImplementation⟩
      have nextBudget : heap.AddressSpaceBudget remainingBytes := by
        constructor
        · simpa [cursor] using budget.cursorPositive
        · simpa [cursor] using budget.endWithinAddressSpace
      have nextBaseInvariant :
          ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        have externalsEq :
            (replaceHeap targetStore heap).host.externals =
              targetStore.host.externals := by
          simp [replaceHeap, clearFailure]
        refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
        · rw [externalsEq]
          exact integerImplementation
        · rw [externalsEq]
          exact naturalImplementation
        · rw [externalsEq]
          exact scalarImplementation
      have nextInvariant :
          ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        exact ⟨nextBaseInvariant, by
          simpa [replaceHeap, clearFailure] using invariant.2⟩
      exact ⟨targetRest, replaceHeap targetStore heap, witness,
        continuationAdapted, step, nextInvariant⟩

/--
Successful constructor-tag mutation implements the generic effect condition
for the ownership-aware pure-external frame.

Production inversion recovers the generated unary call from the source node,
and resolver alignment supplies its concrete host contract. The checked header
write preserves the exact heap frontier, all installed pure-external laws, and
the immutable closure-descriptor agreement used by recursive ownership steps.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_constructorTag
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ConstructorTagEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | setTag sourceRuntime nextRuntime sourceEnv objectId tag continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq tagFits =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetEq⟩ :=
        CodeAdapted.setTag_eq supportedExport.localsAligned objectCompiled
          adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        supportedExport.setTagCall callFound
      obtain ⟨heap, step, _capacity, cursor⟩ :=
        effectStepSimulates_setTag_with_capacity objectLookup updated
          stateRelated objectCompiled objectFound kindAt callFound
          continuationAdapted imported supportedExport.hostsSatisfy inBounds
          contracted params results found live objectEq tagFits
      rcases invariant.1 with
        ⟨⟨frameAligned, budget⟩, integerImplementation,
          naturalImplementation, scalarImplementation⟩
      have nextBudget : heap.AddressSpaceBudget remainingBytes := by
        constructor
        · simpa [cursor] using budget.cursorPositive
        · simpa [cursor] using budget.endWithinAddressSpace
      have nextBaseInvariant :
          ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        have externalsEq :
            (replaceHeap targetStore heap).host.externals =
              targetStore.host.externals := by
          simp [replaceHeap, clearFailure]
        refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
        · rw [externalsEq]
          exact integerImplementation
        · rw [externalsEq]
          exact naturalImplementation
        · rw [externalsEq]
          exact scalarImplementation
      have nextInvariant :
          ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv (replaceHeap targetStore heap)
            targetLocals witness := by
        exact ⟨nextBaseInvariant, by
          simpa [replaceHeap, clearFailure] using invariant.2⟩
      exact ⟨targetRest, replaceHeap targetStore heap, witness,
        continuationAdapted, step, nextInvariant⟩

/--
Successful FVar object-field mutation implements the generic effect condition
for the ownership-aware pure-external frame.

Production inversion determines both local slots and the binary object-set
call. The successful semantic constructor decode and `StateRelated` recover
the concrete object word and descriptor; the source typing premise supplies
only the selected descriptor-slot kind. The checked payload write preserves
the exact heap frontier and all nonheap invariants.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_objectFieldFVar
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ObjectFieldFVarEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | oset sourceRuntime nextRuntime sourceEnv objectId fieldId index continuation
      location cell semantic field fieldKind objectCompiled fieldCompiled
      fieldObjectKind objectLookup fieldLookup updated found live objectEq
      indexValid fieldKindAligned =>
      obtain ⟨objectIndex, fieldIndex, callIndex, targetRest, objectFound,
          objectKindAt, fieldFound, fieldKindAt, callFound,
          continuationAdapted, targetEq⟩ :=
        CodeAdapted.objectSetFVar_eq supportedExport.localsAligned objectCompiled
          fieldCompiled adapted
      subst targetCode
      have objectSourceLookup :
          lookup sourceEnv objectId = some (.object (.heap location)) := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value foundLookup
          injection objectLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      obtain ⟨physicalObject, hObject, physicalObjectRelated⟩ :=
        stateRelated.resolve objectSourceLookup objectFound objectKindAt
      cases physicalObjectRelated with
      | word32 objectRelated =>
          have decoded :
              getConstructor sourceRuntime (.object (.heap location)) =
                .ok (location, cell, semantic) := by
            unfold getConstructor
            simp only [getLiveCell, found, live, if_true, Bind.bind,
              Except.bind]
            rw [objectEq]
            rfl
          have tobjectRelated := objectRelated.object_to_tobject
          obtain ⟨info, fieldKinds, descriptorFound⟩ :=
            ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
              stateRelated.1 tobjectRelated decoded
          have fieldDescriptorKindAt :=
            fieldKindAligned tobjectRelated descriptorFound
          obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
            supportedExport.objectSetCall callFound
          have fieldArgCompiled :=
            compileArg_fvar_of_getLocal fieldCompiled
          obtain ⟨heap, step, _capacity, cursor⟩ :=
            effectStepSimulates_objectSet_with_capacity objectLookup fieldLookup
              updated stateRelated hObject objectRelated objectCompiled
              fieldArgCompiled objectFound fieldFound fieldKindAt fieldObjectKind
              callFound continuationAdapted imported
              supportedExport.hostsSatisfy inBounds contracted params results
              found live objectEq descriptorFound indexValid
              fieldDescriptorKindAt
          rcases invariant.1 with
            ⟨⟨frameAligned, budget⟩, integerImplementation,
              naturalImplementation, scalarImplementation⟩
          have nextBudget : heap.AddressSpaceBudget remainingBytes := by
            constructor
            · simpa [cursor] using budget.cursorPositive
            · simpa [cursor] using budget.endWithinAddressSpace
          have nextBaseInvariant :
              ConcreteBudgetedPureExternalFrame sourceFunction externals
                remainingBytes nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness := by
            have externalsEq :
                (replaceHeap targetStore heap).host.externals =
                  targetStore.host.externals := by
              simp [replaceHeap, clearFailure]
            refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
            · rw [externalsEq]
              exact integerImplementation
            · rw [externalsEq]
              exact naturalImplementation
            · rw [externalsEq]
              exact scalarImplementation
          have nextInvariant :
              ConcreteBudgetedPureExternalOwnershipFrame sourceFunction
                externals remainingBytes nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness := by
            exact ⟨nextBaseInvariant, by
              simpa [replaceHeap, clearFailure] using invariant.2⟩
          exact ⟨targetRest, replaceHeap targetStore heap, witness,
            continuationAdapted, step, nextInvariant⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Successful erased object-field mutation implements the generic effect
condition for the ownership-aware pure-external frame.

Production inversion recovers the object local, canonical zero, and binary
object-set call. State refinement recovers the physical object and descriptor;
the source typing premise identifies the selected slot as erased. The concrete
write preserves the exact heap frontier and every nonheap invariant.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_objectFieldErased
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ObjectFieldErasedEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | oset sourceRuntime nextRuntime sourceEnv objectId index continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq indexValid fieldKindAligned =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, objectKindAt,
          callFound, continuationAdapted, targetEq⟩ :=
        CodeAdapted.objectSetErased_eq supportedExport.localsAligned
          objectCompiled adapted
      subst targetCode
      have objectSourceLookup :
          lookup sourceEnv objectId = some (.object (.heap location)) := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value foundLookup
          injection objectLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      obtain ⟨physicalObject, hObject, physicalObjectRelated⟩ :=
        stateRelated.resolve objectSourceLookup objectFound objectKindAt
      cases physicalObjectRelated with
      | word32 objectRelated =>
          have decoded :
              getConstructor sourceRuntime (.object (.heap location)) =
                .ok (location, cell, semantic) := by
            unfold getConstructor
            simp only [getLiveCell, found, live, if_true, Bind.bind,
              Except.bind]
            rw [objectEq]
            rfl
          have tobjectRelated := objectRelated.object_to_tobject
          obtain ⟨info, fieldKinds, descriptorFound⟩ :=
            ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
              stateRelated.1 tobjectRelated decoded
          have fieldDescriptorKindAt :=
            fieldKindAligned tobjectRelated descriptorFound
          obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
            supportedExport.objectSetCall callFound
          obtain ⟨heap, step, _capacity, cursor⟩ :=
            effectStepSimulates_objectSet_erased_with_capacity objectLookup
              updated stateRelated hObject objectRelated objectCompiled
              objectFound callFound continuationAdapted imported
              supportedExport.hostsSatisfy inBounds contracted params results
              found live objectEq descriptorFound indexValid
              fieldDescriptorKindAt
          rcases invariant.1 with
            ⟨⟨frameAligned, budget⟩, integerImplementation,
              naturalImplementation, scalarImplementation⟩
          have nextBudget : heap.AddressSpaceBudget remainingBytes := by
            constructor
            · simpa [cursor] using budget.cursorPositive
            · simpa [cursor] using budget.endWithinAddressSpace
          have nextBaseInvariant :
              ConcreteBudgetedPureExternalFrame sourceFunction externals
                remainingBytes nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness := by
            have externalsEq :
                (replaceHeap targetStore heap).host.externals =
                  targetStore.host.externals := by
              simp [replaceHeap, clearFailure]
            refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
            · rw [externalsEq]
              exact integerImplementation
            · rw [externalsEq]
              exact naturalImplementation
            · rw [externalsEq]
              exact scalarImplementation
          have nextInvariant :
              ConcreteBudgetedPureExternalOwnershipFrame sourceFunction
                externals remainingBytes nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness := by
            exact ⟨nextBaseInvariant, by
              simpa [replaceHeap, clearFailure] using invariant.2⟩
          exact ⟨targetRest, replaceHeap targetStore heap, witness,
            continuationAdapted, step, nextInvariant⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Successful `USize` field mutation implements the generic effect condition for
the ownership-aware pure-external frame.

Production inversion recovers both numeric locals and the runtime call.
`StateRelated` inside the reusable concrete theorem recovers their physical
values. The checked payload write preserves the exact heap frontier and every
nonheap invariant.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_usizeField
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (USizeFieldEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | uset sourceRuntime nextRuntime sourceEnv objectId fieldId index continuation
      location cell semantic field objectCompiled fieldCompiled objectLookup
      fieldLookup updated found live objectEq slotStart slotEnd =>
      obtain ⟨objectIndex, fieldIndex, callIndex, targetRest, objectFound,
          objectKindAt, fieldFound, fieldKindAt, callFound,
          continuationAdapted, targetEq⟩ :=
        CodeAdapted.usizeSet_eq supportedExport.localsAligned objectCompiled
          fieldCompiled adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        supportedExport.usizeSetCall callFound
      obtain ⟨heap, step, _capacity, cursor⟩ :=
        effectStepSimulates_usizeSet_with_capacity objectLookup fieldLookup
          updated stateRelated objectCompiled fieldCompiled objectFound
          fieldFound objectKindAt fieldKindAt callFound continuationAdapted
          imported supportedExport.hostsSatisfy inBounds contracted params
          results found live objectEq slotStart slotEnd
      rcases invariant.1 with
        ⟨⟨frameAligned, budget⟩, integerImplementation,
          naturalImplementation, scalarImplementation⟩
      have nextBudget : heap.AddressSpaceBudget remainingBytes := by
        constructor
        · simpa [cursor] using budget.cursorPositive
        · simpa [cursor] using budget.endWithinAddressSpace
      have nextBaseInvariant :
          ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv
            (replaceHeap targetStore heap) targetLocals witness := by
        have externalsEq :
            (replaceHeap targetStore heap).host.externals =
              targetStore.host.externals := by
          simp [replaceHeap, clearFailure]
        refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
        · rw [externalsEq]
          exact integerImplementation
        · rw [externalsEq]
          exact naturalImplementation
        · rw [externalsEq]
          exact scalarImplementation
      have nextInvariant :
          ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals
            remainingBytes nextRuntime sourceEnv
            (replaceHeap targetStore heap) targetLocals witness := by
        exact ⟨nextBaseInvariant, by
          simpa [replaceHeap, clearFailure] using invariant.2⟩
      exact ⟨targetRest, replaceHeap targetStore heap, witness,
        continuationAdapted, step, nextInvariant⟩

/--
Successful packed-integer field mutation implements the generic effect
condition for the ownership-aware pure-external frame.

Production inversion recovers both numeric locals and the kind-indexed runtime
call. State refinement recovers the physical object and constructor
descriptor; the universal source layout premise supplies width separation and
descriptor coordinates. The checked payload write preserves the exact heap
frontier and every nonheap invariant.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_scalarField
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ScalarFieldEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation targetCode
    targetStore targetLocals remainingBytes witness supported _sourceStep
    stateRelated invariant adapted
  cases supported with
  | sset sourceRuntime nextRuntime sourceEnv objectId fieldId slotIndex
      byteOffset type continuation location cell semantic field fieldKind
      objectCompiled fieldCompiled objectLookup fieldLookup updated found live
      objectEq layoutSafe =>
      obtain ⟨objectIndex, fieldIndex, callIndex, targetRest, objectFound,
          objectKindAt, fieldFound, fieldKindAt, callFound,
          continuationAdapted, targetEq⟩ :=
        CodeAdapted.scalarSet_eq supportedExport.localsAligned objectCompiled
          fieldCompiled adapted
      subst targetCode
      have objectSourceLookup :
          lookup sourceEnv objectId = some (.object (.heap location)) := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value foundLookup
          injection objectLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      obtain ⟨physicalObject, hObject, physicalObjectRelated⟩ :=
        stateRelated.resolve objectSourceLookup objectFound objectKindAt
      cases physicalObjectRelated with
      | word32 objectRelated =>
          have decoded :
              getConstructor sourceRuntime (.object (.heap location)) =
                .ok (location, cell, semantic) := by
            unfold getConstructor
            simp only [getLiveCell, found, live, if_true, Bind.bind,
              Except.bind]
            rw [objectEq]
            rfl
          have tobjectRelated := objectRelated.object_to_tobject
          obtain ⟨info, fieldKinds, descriptorFound⟩ :=
            ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
              stateRelated.1 tobjectRelated decoded
          obtain ⟨historySafe, slotIndexEq, fieldFits⟩ :=
            layoutSafe tobjectRelated descriptorFound
          have fieldSupported : PackedIntegerAbiKind fieldKind := by
            cases fieldKind <;>
              simp [PackedIntegerAbiKind] at fieldFits ⊢
          cases fieldKind <;>
            simp [PackedIntegerAbiKind] at fieldSupported
          all_goals
            obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
              supportedExport.scalarSetCall callFound (by trivial)
            obtain ⟨heap, step, _capacity, cursor⟩ :=
              effectStepSimulates_scalarSet_with_capacity objectLookup
                fieldLookup updated stateRelated hObject objectRelated
                objectCompiled fieldCompiled objectFound fieldFound fieldKindAt
                callFound continuationAdapted imported
                supportedExport.hostsSatisfy inBounds contracted params results
                found live objectEq descriptorFound historySafe slotIndexEq
                fieldFits
            rcases invariant.1 with
              ⟨⟨frameAligned, budget⟩, integerImplementation,
                naturalImplementation, scalarImplementation⟩
            have nextBudget : heap.AddressSpaceBudget remainingBytes := by
              constructor
              · simpa [cursor] using budget.cursorPositive
              · simpa [cursor] using budget.endWithinAddressSpace
            have nextBaseInvariant :
                ConcreteBudgetedPureExternalFrame sourceFunction externals
                  remainingBytes nextRuntime sourceEnv
                  (replaceHeap targetStore heap) targetLocals witness := by
              have externalsEq :
                  (replaceHeap targetStore heap).host.externals =
                    targetStore.host.externals := by
                simp [replaceHeap, clearFailure]
              refine ⟨⟨frameAligned, nextBudget⟩, ?_, ?_, ?_⟩
              · rw [externalsEq]
                exact integerImplementation
              · rw [externalsEq]
                exact naturalImplementation
              · rw [externalsEq]
                exact scalarImplementation
            have nextInvariant :
                ConcreteBudgetedPureExternalOwnershipFrame sourceFunction
                  externals remainingBytes nextRuntime sourceEnv
                  (replaceHeap targetStore heap) targetLocals witness := by
              exact ⟨nextBaseInvariant, by
                simpa [replaceHeap, clearFailure] using invariant.2⟩
            exact ⟨targetRest, replaceHeap targetStore heap, witness,
              continuationAdapted, step, nextInvariant⟩
      | word64 objectRelated => cases objectRelated
      | float32Bits objectRelated => cases objectRelated
      | float64Bits objectRelated => cases objectRelated

/--
One uniform runtime law for every currently proved successful ownership effect.

The theorem is assembled solely with `EffectRuntimeRefines.or`: persistent
operations, ordinary increment, recursive decrement, and explicit deletion
retain the same ownership-aware invariant and may therefore occur in any
order in the structural source evaluation.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ownership
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OwnershipEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  have decrementDelete :
      EffectRuntimeRefines context sourceModule sourceFunction labels
        target.wasmModule hosts.env
        (EffectSupportedOr (OrdinaryDecrementEffectSupported context)
          (OrdinaryDeleteEffectSupported context))
        (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
    by
      apply EffectRuntimeRefines.or
      · exact supportedExport.effectRuntimeRefines_ordinaryDecrement
          (externals := externals)
      · exact supportedExport.effectRuntimeRefines_ordinaryDelete_ownership
          (externals := externals)
  have incrementRest :
      EffectRuntimeRefines context sourceModule sourceFunction labels
        target.wasmModule hosts.env
        (EffectSupportedOr (OrdinaryIncrementEffectSupported context)
          (EffectSupportedOr (OrdinaryDecrementEffectSupported context)
            (OrdinaryDeleteEffectSupported context)))
        (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) :=
    by
      apply EffectRuntimeRefines.or
      · exact supportedExport.effectRuntimeRefines_ordinaryIncrement_ownership
          (externals := externals)
      · exact decrementDelete
  apply EffectRuntimeRefines.or
  · exact effectRuntimeRefines_persistentOwnership
  · exact incrementRest

/--
One uniform runtime law for the ownership family plus constructor-tag
mutation. The generic union theorem is the only composition step, so
structural source evaluations may interleave the operation families without
storing operation-specific target witnesses.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ownershipAndTag
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OwnershipAndTagEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  apply EffectRuntimeRefines.or
  · exact supportedExport.effectRuntimeRefines_ownership
      (externals := externals)
  · exact supportedExport.effectRuntimeRefines_constructorTag
      (externals := externals)

/--
One uniform runtime law for ownership, tag mutation, and successful FVar
object-field mutation.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ownershipTagAndObjectFVar
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (OwnershipTagAndObjectFVarEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  apply EffectRuntimeRefines.or
  · exact supportedExport.effectRuntimeRefines_ownershipAndTag
      (externals := externals)
  · exact supportedExport.effectRuntimeRefines_objectFieldFVar
      (externals := externals)

/--
One uniform runtime law for both compiler argument forms accepted by
object-field mutation.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_objectField
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ObjectFieldEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  apply EffectRuntimeRefines.or
  · exact supportedExport.effectRuntimeRefines_objectFieldFVar
      (externals := externals)
  · exact supportedExport.effectRuntimeRefines_objectFieldErased
      (externals := externals)

/--
One uniform runtime law for ownership, tag mutation, and both FVar and erased
object-field mutation.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ownershipTagAndObject
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (OwnershipTagAndObjectEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  apply EffectRuntimeRefines.or
  · exact supportedExport.effectRuntimeRefines_ownershipAndTag
      (externals := externals)
  · exact supportedExport.effectRuntimeRefines_objectField
      (externals := externals)

/--
One uniform runtime law for every currently structural successful field
mutation: both object-slot argument forms and `USize` slots.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_fieldMutation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (FieldMutationEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  apply EffectRuntimeRefines.or
  · exact supportedExport.effectRuntimeRefines_objectField
      (externals := externals)
  · exact supportedExport.effectRuntimeRefines_usizeField
      (externals := externals)

/--
One uniform runtime law for ownership, tag mutation, and all currently
structural successful field mutations.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ownershipTagAndFieldMutation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (OwnershipTagAndFieldMutationEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  apply EffectRuntimeRefines.or
  · exact supportedExport.effectRuntimeRefines_ownershipAndTag
      (externals := externals)
  · exact supportedExport.effectRuntimeRefines_fieldMutation
      (externals := externals)

/--
One uniform runtime law for object, `USize`, and supported packed-integer field
mutations.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_allFieldMutation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env (AllFieldMutationEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  apply EffectRuntimeRefines.or
  · exact supportedExport.effectRuntimeRefines_fieldMutation
      (externals := externals)
  · exact supportedExport.effectRuntimeRefines_scalarField
      (externals := externals)

/--
One uniform runtime law for ownership, tag mutation, and object, `USize`, and
supported packed-integer field mutations.
-/
theorem
    ConcreteSupportedExport.effectRuntimeRefines_ownershipTagAndAllFieldMutation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (supportedExport :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {externals : ExternalImpl}
    {labels : List FVarId} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (OwnershipTagAndAllFieldMutationEffectSupported context)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  apply EffectRuntimeRefines.or
  · exact supportedExport.effectRuntimeRefines_ownershipAndTag
      (externals := externals)
  · exact supportedExport.effectRuntimeRefines_allFieldMutation
      (externals := externals)

/--
A postcondition is stable for a generated case arm when any selected-arm
result satisfying it also satisfies the case resumption wrapper. Explicit
returns, traps, and nonzero breaks are stable; unrestricted fallthrough is not.
-/
def CaseResumptionStable (module : Wasm.Module) (hostEnv : Wasm.HostEnv Host)
    (tail : List Wasm.Value) (Q : Wasm.Assertion Host) : Prop :=
  Q ⇛ CaseResumePost module hostEnv [] Q tail

/-- A stable post remains stable after one generated case-arm wrapper. -/
theorem CaseResumptionStable.resume
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (stable : CaseResumptionStable module hostEnv tail Q) :
    CaseResumptionStable module hostEnv tail
      (CaseResumePost module hostEnv [] Q tail) := by
  intro continuation resumed
  cases continuation with
  | Break level nextStore nextLocals =>
      cases level with
      | zero =>
          simpa [CaseResumePost, Wasm.wp_nil] using resumed
      | succ level =>
          exact stable (.Break level nextStore nextLocals) resumed
  | _ =>
      simpa [CaseResumePost, Wasm.wp_nil] using resumed

/--
The concrete `getTag` host implements every normalized object-constructor
suffix produced by the executable case compiler.

The theorem follows the source alternative list. A matching constructor
returns its compiled arm; a miss recursively proves the compiled suffix under
one more case-resumption boundary. The result is therefore path-sensitive:
only the branch selected by `chooseAlt` needs a semantic `CodeWP`, while all
unselected arms are recovered structurally from production compilation and
adaptation.
-/
theorem ConcreteSupportedExport.objectConstructorCaseChainRefines
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
    {labels : List FVarId}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {discr : FVarId}
    {alts : List (LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {chainTarget : Wasm.Program}
    {selected : LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {sourceObject : Value}
    {actualTag : Nat}
    (supported : ObjectConstructorCaseAltsSupported alts)
    (modeEq :
      Fir.Wasm.caseDiscriminatorMode context discr = .objectTag)
    (discrCompiled :
      Fir.Wasm.getLocal context discr =
        .ok (.localGet discr, .tobject))
    (selection : chooseAlt actualTag alts = some selected)
    (sourceLookup : lookup sourceEnv discr = some sourceObject)
    (tagged : getTag sourceRuntime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness)
    (fallbackCompiled :
      Fir.Wasm.compileCaseFallback context alts = .ok fallback)
    (chainAdapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr alts
        fallback chainTarget) :
    ∃ selectedTarget,
      CodeAdapted context sourceModule sourceFunction labels selected
          selectedTarget ∧
        ∀ (tail : List Wasm.Value) (Q : Wasm.Assertion Host),
          CaseResumptionStable target.wasmModule hosts.env tail Q →
          CodeWP context sourceModule sourceFunction labels target.wasmModule
              hosts.env sourceRuntime sourceEnv selected selectedTarget
              targetStore targetLocals witness tail Q →
            CaseChainWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv discr alts
              fallback chainTarget targetStore targetLocals witness tail Q := by
  induction supported generalizing chainTarget selected with
  | nil =>
      simp [chooseAlt, findCtorAlt, findDefaultAlt] at selection
  | default code =>
      have selectedEq : selected = code := by
        simpa [chooseAlt, findCtorAlt, findDefaultAlt] using selection.symm
      subst selected
      have branchCompiled :
          Fir.Wasm.compileCode context code = .ok fallback := by
        simpa [Fir.Wasm.compileCaseFallback,
          Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt]
          using fallbackCompiled
      have branchAdapted :
          CodeAdapted context sourceModule sourceFunction labels code
            chainTarget :=
        ⟨fallback, branchCompiled,
          CaseChainAdapted.nil_eq
            (CaseChainAdapted.default_eq chainAdapted)⟩
      refine ⟨chainTarget, branchAdapted, ?_⟩
      intro tail Q _stable continued
      exact ⟨chainAdapted, stateRelated, continued.2.2⟩
  | @ctor info alts code fits rest ih =>
      have fallbackCompiledRest :
          Fir.Wasm.compileCaseFallback context alts = .ok fallback := by
        simpa [Fir.Wasm.compileCaseFallback,
          Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt]
          using fallbackCompiled
      obtain ⟨thenTarget, elseTarget, discrIndex, getTagIndex, thenAdapted,
          elseAdapted, discrFound, getTagFound, targetEq⟩ :=
        CaseChainAdapted.objectConstructor_eq modeEq fits chainAdapted
      obtain ⟨alignedIndex, alignedFound, discrKind⟩ :=
        spec.localsAligned discrCompiled
      rw [discrFound] at alignedFound
      injection alignedFound with indexEq
      subst alignedIndex
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        spec.runtimeCallsAligned getTagFound
      have getTagContracted :
          hosts.spec.contracts[getTagIndex]? = some getTagContract := by
        change hosts.spec.contracts[getTagIndex]? =
          some (fun initial args result => result = getTagStep initial args)
        simpa only [resolvedContract?, hostFn?, Option.map_some, getTagFn]
          using contracted
      have parameterCount : imp.params.length = 1 := by
        change imp.params.length = 1 at params
        exact params
      have resultCount : imp.results.length = 1 := by
        change imp.results.length = 1 at results
        exact results
      have expectedFits : info.cidx < UInt32.size := by
        simpa [Fir.Wasm.constructorTagFitsI32] using fits
      by_cases hit : actualTag = info.cidx
      · have selectedEq : selected = code := by
          have branchEq : code = selected := by
            simpa [chooseAlt, findCtorAlt, findDefaultAlt, hit] using selection
          exact branchEq.symm
        subst selected
        refine ⟨thenTarget, thenAdapted, ?_⟩
        intro tail Q stable continued
        have continuedOnce :
            CodeWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv code
              thenTarget targetStore targetLocals witness tail
              (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
          continued.conseq stable
        have branchWP :
            Wasm.wp target.wasmModule
              (if actualTag = info.cidx then thenTarget else elseTarget)
              (CaseResumePost target.wasmModule hosts.env [] Q tail)
              targetStore { targetLocals with values := tail } hosts.env := by
          simpa [hit] using continuedOnce.2.2
        have chain :
            CaseChainWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv discr
              (.ctorAlt info code :: alts) fallback
              [.localGet discrIndex, .call getTagIndex,
                .const (UInt32.ofNat info.cidx), .eq,
                .iff 0 0 thenTarget elseTarget]
              targetStore targetLocals witness tail Q := by
          apply caseChainWP_constructor
            (spec := hosts.spec) (imp := imp) (sourceObject := sourceObject)
            (actualTag := actualTag)
          · exact modeEq
          · exact fits
          · exact thenAdapted
          · exact elseAdapted
          · exact discrFound
          · exact discrKind
          · exact getTagFound
          · exact stateRelated
          · exact sourceLookup
          · exact imported
          · exact spec.hostsSatisfy
          · exact inBounds
          · exact getTagContracted
          · exact parameterCount
          · exact resultCount
          · exact tagged
          · exact actualFits
          · exact expectedFits
          · exact branchWP
        simpa only [targetEq] using chain
      · have reverseMiss : info.cidx ≠ actualTag :=
          fun equal => hit equal.symm
        have selectionRest : chooseAlt actualTag alts = some selected := by
          simpa [chooseAlt, findCtorAlt, findDefaultAlt, hit, reverseMiss]
            using selection
        obtain ⟨selectedTarget, selectedAdapted, liftRest⟩ :=
          ih selectionRest fallbackCompiledRest elseAdapted
        refine ⟨selectedTarget, selectedAdapted, ?_⟩
        intro tail Q stable continued
        have continuedOnce :
            CodeWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv selected
              selectedTarget targetStore targetLocals witness tail
              (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
          continued.conseq stable
        have restChain :
            CaseChainWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv discr alts
              fallback elseTarget targetStore targetLocals witness tail
              (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
          liftRest tail (CaseResumePost target.wasmModule hosts.env [] Q tail)
            stable.resume continuedOnce
        have branchWP :
            Wasm.wp target.wasmModule
              (if actualTag = info.cidx then thenTarget else elseTarget)
              (CaseResumePost target.wasmModule hosts.env [] Q tail)
              targetStore { targetLocals with values := tail } hosts.env := by
          simpa [hit] using restChain.2.2
        have chain :
            CaseChainWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv discr
              (.ctorAlt info code :: alts) fallback
              [.localGet discrIndex, .call getTagIndex,
                .const (UInt32.ofNat info.cidx), .eq,
                .iff 0 0 thenTarget elseTarget]
              targetStore targetLocals witness tail Q := by
          apply caseChainWP_constructor
            (spec := hosts.spec) (imp := imp) (sourceObject := sourceObject)
            (actualTag := actualTag)
          · exact modeEq
          · exact fits
          · exact thenAdapted
          · exact restChain.1
          · exact discrFound
          · exact discrKind
          · exact getTagFound
          · exact stateRelated
          · exact sourceLookup
          · exact imported
          · exact spec.hostsSatisfy
          · exact inBounds
          · exact getTagContracted
          · exact parameterCount
          · exact resultCount
          · exact tagged
          · exact actualFits
          · exact expectedFits
          · exact branchWP
        simpa only [targetEq] using chain

/--
Direct scalar `UInt8` comparison implements every normalized constructor
suffix produced by the executable case compiler.

The proof follows the source alternatives list exactly as in the object-tag
case, but each constructor test is an in-Wasm local/constant comparison.
`StateRelated` supplies the concrete `UInt8` lane and hence the dynamic tag
bound; no runtime import or per-program translation certificate is needed.
-/
theorem ConcreteSupportedExport.scalarUInt8CaseChainRefines
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
    {labels : List FVarId}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {discr : FVarId}
    {alts : List (LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {chainTarget : Wasm.Program}
    {selected : LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {sourceValue : Value}
    {actualTag : Nat}
    (supported : ScalarUInt8CaseAltsSupported alts)
    (modeEq :
      Fir.Wasm.caseDiscriminatorMode context discr = .scalarUInt8)
    (discrCompiled :
      Fir.Wasm.getLocal context discr =
        .ok (.localGet discr, .uint8))
    (selection : chooseAlt actualTag alts = some selected)
    (sourceLookup : lookup sourceEnv discr = some sourceValue)
    (tagged : getTag sourceRuntime sourceValue = .ok actualTag)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness)
    (fallbackCompiled :
      Fir.Wasm.compileCaseFallback context alts = .ok fallback)
    (chainAdapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr alts
        fallback chainTarget) :
    ∃ selectedTarget,
      CodeAdapted context sourceModule sourceFunction labels selected
          selectedTarget ∧
        ∀ (tail : List Wasm.Value) (Q : Wasm.Assertion Host),
          CaseResumptionStable target.wasmModule hosts.env tail Q →
          CodeWP context sourceModule sourceFunction labels target.wasmModule
              hosts.env sourceRuntime sourceEnv selected selectedTarget
              targetStore targetLocals witness tail Q →
            CaseChainWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv discr alts
              fallback chainTarget targetStore targetLocals witness tail Q := by
  induction supported generalizing chainTarget selected with
  | nil =>
      simp [chooseAlt, findCtorAlt, findDefaultAlt] at selection
  | default code =>
      have selectedEq : selected = code := by
        simpa [chooseAlt, findCtorAlt, findDefaultAlt] using selection.symm
      subst selected
      have branchCompiled :
          Fir.Wasm.compileCode context code = .ok fallback := by
        simpa [Fir.Wasm.compileCaseFallback,
          Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt]
          using fallbackCompiled
      have branchAdapted :
          CodeAdapted context sourceModule sourceFunction labels code
            chainTarget :=
        ⟨fallback, branchCompiled,
          CaseChainAdapted.nil_eq
            (CaseChainAdapted.default_eq chainAdapted)⟩
      refine ⟨chainTarget, branchAdapted, ?_⟩
      intro tail Q _stable continued
      exact ⟨chainAdapted, stateRelated, continued.2.2⟩
  | @ctor info alts code fits rest ih =>
      have fallbackCompiledRest :
          Fir.Wasm.compileCaseFallback context alts = .ok fallback := by
        simpa [Fir.Wasm.compileCaseFallback,
          Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt]
          using fallbackCompiled
      obtain ⟨thenTarget, elseTarget, discrIndex, thenAdapted, elseAdapted,
          discrFound, targetEq⟩ :=
        CaseChainAdapted.scalarUInt8Constructor_eq modeEq fits chainAdapted
      obtain ⟨alignedIndex, alignedFound, discrKind⟩ :=
        spec.localsAligned discrCompiled
      rw [discrFound] at alignedFound
      injection alignedFound with indexEq
      subst alignedIndex
      have expectedFits : info.cidx < UInt8.size := by
        simpa [Fir.Wasm.constructorTagFitsUInt8] using fits
      by_cases hit : actualTag = info.cidx
      · have selectedEq : selected = code := by
          have branchEq : code = selected := by
            simpa [chooseAlt, findCtorAlt, findDefaultAlt, hit] using selection
          exact branchEq.symm
        subst selected
        refine ⟨thenTarget, thenAdapted, ?_⟩
        intro tail Q stable continued
        have continuedOnce :
            CodeWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv code
              thenTarget targetStore targetLocals witness tail
              (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
          continued.conseq stable
        have branchWP :
            Wasm.wp target.wasmModule
              (if actualTag = info.cidx then thenTarget else elseTarget)
              (CaseResumePost target.wasmModule hosts.env [] Q tail)
              targetStore { targetLocals with values := tail } hosts.env := by
          simpa [hit] using continuedOnce.2.2
        have chain :
            CaseChainWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv discr
              (.ctorAlt info code :: alts) fallback
              [.localGet discrIndex, .const (UInt32.ofNat info.cidx), .eq,
                .iff 0 0 thenTarget elseTarget]
              targetStore targetLocals witness tail Q := by
          apply caseChainWP_scalarUInt8_constructor
            (sourceValue := sourceValue) (actualTag := actualTag)
          · exact modeEq
          · exact fits
          · exact thenAdapted
          · exact elseAdapted
          · exact discrFound
          · exact discrKind
          · exact stateRelated
          · exact sourceLookup
          · exact tagged
          · exact expectedFits
          · exact branchWP
        simpa only [targetEq] using chain
      · have reverseMiss : info.cidx ≠ actualTag :=
          fun equal => hit equal.symm
        have selectionRest : chooseAlt actualTag alts = some selected := by
          simpa [chooseAlt, findCtorAlt, findDefaultAlt, hit, reverseMiss]
            using selection
        obtain ⟨selectedTarget, selectedAdapted, liftRest⟩ :=
          ih selectionRest fallbackCompiledRest elseAdapted
        refine ⟨selectedTarget, selectedAdapted, ?_⟩
        intro tail Q stable continued
        have continuedOnce :
            CodeWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv selected
              selectedTarget targetStore targetLocals witness tail
              (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
          continued.conseq stable
        have restChain :
            CaseChainWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv discr alts
              fallback elseTarget targetStore targetLocals witness tail
              (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
          liftRest tail (CaseResumePost target.wasmModule hosts.env [] Q tail)
            stable.resume continuedOnce
        have branchWP :
            Wasm.wp target.wasmModule
              (if actualTag = info.cidx then thenTarget else elseTarget)
              (CaseResumePost target.wasmModule hosts.env [] Q tail)
              targetStore { targetLocals with values := tail } hosts.env := by
          simpa [hit] using restChain.2.2
        have chain :
            CaseChainWP context sourceModule sourceFunction labels
              target.wasmModule hosts.env sourceRuntime sourceEnv discr
              (.ctorAlt info code :: alts) fallback
              [.localGet discrIndex, .const (UInt32.ofNat info.cidx), .eq,
                .iff 0 0 thenTarget elseTarget]
              targetStore targetLocals witness tail Q := by
          apply caseChainWP_scalarUInt8_constructor
            (sourceValue := sourceValue) (actualTag := actualTag)
          · exact modeEq
          · exact fits
          · exact thenAdapted
          · exact restChain.1
          · exact discrFound
          · exact discrKind
          · exact stateRelated
          · exact sourceLookup
          · exact tagged
          · exact expectedFits
          · exact branchWP
        simpa only [targetEq] using chain

/--
Uniform runtime condition for a selected source case branch.

The full and selected target programs are universally quantified outputs of
the production compiler and adapter. An operation-family instance recovers
the selected target and turns correctness of that branch into correctness of
the complete generated case chain whenever the enclosing postcondition is
stable under the generated arm's resumption boundary. This control condition
is semantic and reusable; no target program or per-program translation
certificate occurs in source admission.
-/
def CaseRuntimeRefines
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop) :
    Prop :=
  ∀ {sourceRuntime : RuntimeState}
      {sourceEnv : Env}
      {cases : LCNF.Cases .impure}
      {selected : LCNF.Code .impure}
      {target : Wasm.Program}
      {targetStore : Wasm.Store Host}
      {targetLocals : Wasm.Locals}
      {witness : RefinementWitness},
    CaseSupported sourceRuntime sourceEnv cases selected →
      SourceCaseResult sourceRuntime sourceEnv cases selected →
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness →
      CodeAdapted context sourceModule sourceFunction labels (.cases cases)
        target →
      ∃ selectedTarget,
        CodeAdapted context sourceModule sourceFunction labels selected
            selectedTarget ∧
          SourceCaseResult sourceRuntime sourceEnv cases selected ∧
          ∀ (tail : List Wasm.Value) (Q : Wasm.Assertion Host),
            CaseResumptionStable module hostEnv tail Q →
            CodeWP context sourceModule sourceFunction labels module hostEnv
                sourceRuntime sourceEnv selected selectedTarget targetStore
                targetLocals witness tail Q →
              CodeWP context sourceModule sourceFunction labels module hostEnv
                sourceRuntime sourceEnv (.cases cases) target targetStore
                targetLocals witness tail Q

/--
Default-only cases satisfy the generic case runtime condition without a host
step: executable compilation erases the wrapper to its selected branch.
-/
theorem caseRuntimeRefines_defaultOnly
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} :
    CaseRuntimeRefines context sourceModule sourceFunction labels module hostEnv
      DefaultOnlyCaseSupported := by
  intro sourceRuntime sourceEnv cases selected target targetStore targetLocals
    witness supported sourceStep stateRelated adapted
  have selectedAdapted :=
    CodeAdapted.defaultOnlyCases_selected supported adapted
  refine ⟨target, selectedAdapted, sourceStep, ?_⟩
  intro tail Q _stable continued
  exact ⟨adapted, stateRelated, continued.2.2⟩

/--
Arbitrary normalized object-constructor cases satisfy the uniform runtime
condition.

The interpreter supplies the selected source branch and semantic tag. Generic
compiler inversion recovers the fallback and constructor chain, and
`objectConstructorCaseChainRefines` follows exactly that selected path through
the concrete `getTag` calls.
-/
theorem ConcreteSupportedExport.caseRuntimeRefines_objectConstructorCases
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
    CaseRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (ObjectConstructorCasesSupported context) := by
  intro sourceRuntime sourceEnv cases selected fullTarget targetStore
    targetLocals witness supported sourceStep stateRelated adapted
  rcases supported with
    ⟨altsSupported, modeEq, discrCompiled, actualTagFits⟩
  rcases sourceStep with
    ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩
  have sourceLookup :
      lookup sourceEnv cases.discr = some sourceObject := by
    cases lookupEq : lookup sourceEnv cases.discr with
    | none =>
        simp [lookupValue, lookupEq] at lookupFound
    | some value =>
        have valueEq : value = sourceObject := by
          simpa [lookupValue, lookupEq] using lookupFound
        subst value
        rfl
  have actualFits : actualTag < UInt32.size :=
    actualTagFits lookupFound tagged
  rcases CodeAdapted.cases_eq adapted with
    ⟨fallback, fallbackCompiled, chainAdapted⟩
  obtain ⟨selectedTarget, selectedAdapted, liftChain⟩ :=
    spec.objectConstructorCaseChainRefines altsSupported modeEq discrCompiled
      chosen sourceLookup tagged actualFits stateRelated fallbackCompiled
      chainAdapted
  refine ⟨selectedTarget, selectedAdapted,
    ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩, ?_⟩
  intro tail Q stable continued
  apply codeWP_cases fallbackCompiled
  exact liftChain tail Q stable continued

/--
Arbitrary normalized scalar `UInt8` constructor cases satisfy the uniform
runtime condition.

The interpreter supplies the selected branch and semantic tag. Production
compiler inversion recovers the direct local comparisons, while the related
`.uint8` discriminator proves that every executed comparison observes the
same tag without consulting the concrete host.
-/
theorem ConcreteSupportedExport.caseRuntimeRefines_scalarUInt8Cases
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
    CaseRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (ScalarUInt8CasesSupported context) := by
  intro sourceRuntime sourceEnv cases selected fullTarget targetStore
    targetLocals witness supported sourceStep stateRelated adapted
  rcases supported with
    ⟨altsSupported, modeEq, discrCompiled⟩
  rcases sourceStep with
    ⟨sourceValue, actualTag, lookupFound, tagged, chosen⟩
  have sourceLookup :
      lookup sourceEnv cases.discr = some sourceValue := by
    cases lookupEq : lookup sourceEnv cases.discr with
    | none =>
        simp [lookupValue, lookupEq] at lookupFound
    | some value =>
        have valueEq : value = sourceValue := by
          simpa [lookupValue, lookupEq] using lookupFound
        subst value
        rfl
  rcases CodeAdapted.cases_eq adapted with
    ⟨fallback, fallbackCompiled, chainAdapted⟩
  obtain ⟨selectedTarget, selectedAdapted, liftChain⟩ :=
    spec.scalarUInt8CaseChainRefines altsSupported modeEq discrCompiled
      chosen sourceLookup tagged stateRelated fallbackCompiled chainAdapted
  refine ⟨selectedTarget, selectedAdapted,
    ⟨sourceValue, actualTag, lookupFound, tagged, chosen⟩, ?_⟩
  intro tail Q stable continued
  apply codeWP_cases fallbackCompiled
  exact liftChain tail Q stable continued

/--
The concrete `getTag` host implements singleton object-constructor dispatch.

All target structure is recovered from the production compiler and adapter.
The source admission contributes only the singleton shape, compiler ABI facts,
and the dynamic guarantee that the semantic tag fits the generated i32 lane.
-/
theorem ConcreteSupportedExport.caseRuntimeRefines_singleObjectConstructor
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
    CaseRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (SingleObjectConstructorCaseSupported context) := by
  intro sourceRuntime sourceEnv cases selected fullTarget targetStore
    targetLocals witness supported sourceStep stateRelated adapted
  rcases supported with
    ⟨info, altsEq, modeEq, expectedTagFits, discrCompiled, actualTagFits⟩
  rcases sourceStep with
    ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩
  have sourceLookup :
      lookup sourceEnv cases.discr = some sourceObject := by
    cases lookupEq : lookup sourceEnv cases.discr with
    | none =>
        simp [lookupValue, lookupEq] at lookupFound
    | some value =>
        have valueEq : value = sourceObject := by
          simpa [lookupValue, lookupEq] using lookupFound
        subst value
        rfl
  have tagEq : actualTag = info.cidx := by
    rw [altsEq] at chosen
    simp [chooseAlt, findCtorAlt, findDefaultAlt] at chosen
    omega
  have actualFits : actualTag < UInt32.size :=
    actualTagFits lookupFound tagged
  have expectedFits : info.cidx < UInt32.size := by
    simpa [Fir.Wasm.constructorTagFitsI32] using expectedTagFits
  obtain ⟨selectedTarget, discrIndex, getTagIndex, selectedAdapted,
      discrFound, getTagFound, targetEq⟩ :=
    CodeAdapted.singleObjectConstructorCases_eq altsEq modeEq expectedTagFits
      adapted
  obtain ⟨alignedIndex, alignedFound, discrKind⟩ :=
    spec.localsAligned discrCompiled
  rw [discrFound] at alignedFound
  injection alignedFound with indexEq
  subst alignedIndex
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned getTagFound
  have getTagContracted :
      hosts.spec.contracts[getTagIndex]? = some getTagContract := by
    change hosts.spec.contracts[getTagIndex]? =
      some (fun initial args result => result = getTagStep initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, getTagFn]
      using contracted
  have parameterCount : imp.params.length = 1 := by
    change imp.params.length = 1 at params
    exact params
  have resultCount : imp.results.length = 1 := by
    change imp.results.length = 1 at results
    exact results
  have fallbackCompiled :
      Fir.Wasm.compileCaseFallback context cases.alts.toList =
        .ok [.unreachable] := by
    rw [altsEq]
    rfl
  have fallbackAdapted :
      instructions sourceModule sourceFunction labels [.unreachable] =
        .ok [.unreachable] := by
    simp [instructions, instruction, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have emptyChain :
      CaseChainAdapted context sourceModule sourceFunction labels cases.discr
        [] [.unreachable] [.unreachable] :=
    caseChainAdapted_nil fallbackAdapted
  refine ⟨selectedTarget, selectedAdapted,
    ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩, ?_⟩
  intro tail Q stable continued
  have selectedResumed :
      CodeWP context sourceModule sourceFunction labels target.wasmModule
        hosts.env sourceRuntime sourceEnv selected selectedTarget targetStore
        targetLocals witness tail
        (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
    continued.conseq stable
  have branchWP :
      Wasm.wp target.wasmModule
        (if actualTag = info.cidx then selectedTarget else [.unreachable])
        (CaseResumePost target.wasmModule hosts.env [] Q tail) targetStore
        { targetLocals with values := tail } hosts.env := by
    rw [tagEq]
    simpa using selectedResumed.2.2
  have chain :
      CaseChainWP context sourceModule sourceFunction labels target.wasmModule
        hosts.env sourceRuntime sourceEnv cases.discr
        [.ctorAlt info selected] [.unreachable]
        [.localGet discrIndex, .call getTagIndex,
          .const (UInt32.ofNat info.cidx), .eq,
          .iff 0 0 selectedTarget [.unreachable]]
        targetStore targetLocals witness tail Q := by
    apply caseChainWP_constructor
      (spec := hosts.spec) (imp := imp) (sourceObject := sourceObject)
      (actualTag := actualTag)
    · exact modeEq
    · exact expectedTagFits
    · exact selectedAdapted
    · exact emptyChain
    · exact discrFound
    · exact discrKind
    · exact getTagFound
    · exact stateRelated
    · exact sourceLookup
    · exact imported
    · exact spec.hostsSatisfy
    · exact inBounds
    · exact getTagContracted
    · exact parameterCount
    · exact resultCount
    · exact tagged
    · exact actualFits
    · exact expectedFits
    · exact branchWP
  rw [targetEq]
  apply codeWP_cases fallbackCompiled
  simpa only [altsEq] using chain

/--
The concrete `getTag` host implements an ordered two-constructor chain with a
default fallback.

The proof executes the first hit, second hit after one miss, and default after
two misses. Nested generated resumption wrappers are discharged from the
single semantic stability condition carried by `CaseRuntimeRefines`.
-/
theorem ConcreteSupportedExport.caseRuntimeRefines_twoObjectConstructorDefault
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
    CaseRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (TwoObjectConstructorDefaultCasesSupported context) := by
  intro sourceRuntime sourceEnv cases selected fullTarget targetStore
    targetLocals witness supported sourceStep stateRelated adapted
  rcases supported with
    ⟨firstInfo, secondInfo, firstBranch, secondBranch, defaultBranch,
      altsEq, modeEq, firstTagFits, secondTagFits, discrCompiled,
      actualTagFits⟩
  rcases sourceStep with
    ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩
  have sourceLookup :
      lookup sourceEnv cases.discr = some sourceObject := by
    cases lookupEq : lookup sourceEnv cases.discr with
    | none =>
        simp [lookupValue, lookupEq] at lookupFound
    | some value =>
        have valueEq : value = sourceObject := by
          simpa [lookupValue, lookupEq] using lookupFound
        subst value
        rfl
  have actualFits : actualTag < UInt32.size :=
    actualTagFits lookupFound tagged
  have firstExpectedFits : firstInfo.cidx < UInt32.size := by
    simpa [Fir.Wasm.constructorTagFitsI32] using firstTagFits
  have secondExpectedFits : secondInfo.cidx < UInt32.size := by
    simpa [Fir.Wasm.constructorTagFitsI32] using secondTagFits
  obtain ⟨firstTarget, secondTarget, defaultTarget, discrIndex, getTagIndex,
      firstAdapted, secondAdapted, defaultAdapted, discrFound, getTagFound,
      targetEq⟩ :=
    CodeAdapted.twoObjectConstructorDefaultCases_eq altsEq modeEq firstTagFits
      secondTagFits adapted
  obtain ⟨alignedIndex, alignedFound, discrKind⟩ :=
    spec.localsAligned discrCompiled
  rw [discrFound] at alignedFound
  injection alignedFound with indexEq
  subst alignedIndex
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.runtimeCallsAligned getTagFound
  have getTagContracted :
      hosts.spec.contracts[getTagIndex]? = some getTagContract := by
    change hosts.spec.contracts[getTagIndex]? =
      some (fun initial args result => result = getTagStep initial args)
    simpa only [resolvedContract?, hostFn?, Option.map_some, getTagFn]
      using contracted
  have parameterCount : imp.params.length = 1 := by
    change imp.params.length = 1 at params
    exact params
  have resultCount : imp.results.length = 1 := by
    change imp.results.length = 1 at results
    exact results
  rcases defaultAdapted with
    ⟨defaultSymbolic, defaultCompiled, defaultTargetCompiled⟩
  have defaultAdapted' :
      CodeAdapted context sourceModule sourceFunction labels defaultBranch
        defaultTarget :=
    ⟨defaultSymbolic, defaultCompiled, defaultTargetCompiled⟩
  have fallbackCompiled :
      Fir.Wasm.compileCaseFallback context cases.alts.toList =
        .ok defaultSymbolic := by
    rw [altsEq]
    change
      Fir.Wasm.compileCaseFallbackWithM (Fir.Wasm.compileCode context)
          [.ctorAlt firstInfo firstBranch,
            .ctorAlt secondInfo secondBranch,
            .default defaultBranch] =
        .ok defaultSymbolic
    simp [Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt,
      defaultCompiled]
  have defaultChainAdapted :
      CaseChainAdapted context sourceModule sourceFunction labels cases.discr
        [.default defaultBranch] defaultSymbolic defaultTarget :=
    caseChainAdapted_default
      (caseChainAdapted_nil defaultTargetCompiled)
  have secondChainAdapted :
      CaseChainAdapted context sourceModule sourceFunction labels cases.discr
        [.ctorAlt secondInfo secondBranch, .default defaultBranch]
        defaultSymbolic
        [.localGet discrIndex, .call getTagIndex,
          .const (UInt32.ofNat secondInfo.cidx), .eq,
          .iff 0 0 secondTarget defaultTarget] :=
    caseChainAdapted_constructor modeEq secondTagFits secondAdapted
      defaultChainAdapted discrFound getTagFound
  by_cases firstHit : actualTag = firstInfo.cidx
  · have selectedEq : selected = firstBranch := by
      have branchEq : firstBranch = selected := by
        rw [altsEq] at chosen
        simpa [chooseAlt, findCtorAlt, findDefaultAlt, firstHit] using chosen
      exact branchEq.symm
    subst selected
    refine ⟨firstTarget, firstAdapted,
      ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩, ?_⟩
    intro tail Q stable continued
    have continuedOnce :
        CodeWP context sourceModule sourceFunction labels target.wasmModule
          hosts.env sourceRuntime sourceEnv firstBranch firstTarget targetStore
          targetLocals witness tail
          (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
      continued.conseq stable
    have branchWP :
        Wasm.wp target.wasmModule
          (if actualTag = firstInfo.cidx then firstTarget else
            [.localGet discrIndex, .call getTagIndex,
              .const (UInt32.ofNat secondInfo.cidx), .eq,
              .iff 0 0 secondTarget defaultTarget])
          (CaseResumePost target.wasmModule hosts.env [] Q tail) targetStore
          { targetLocals with values := tail } hosts.env := by
      simpa [firstHit] using continuedOnce.2.2
    have chain :
        CaseChainWP context sourceModule sourceFunction labels
          target.wasmModule hosts.env sourceRuntime sourceEnv cases.discr
          [.ctorAlt firstInfo firstBranch,
            .ctorAlt secondInfo secondBranch,
            .default defaultBranch]
          defaultSymbolic
          [.localGet discrIndex, .call getTagIndex,
            .const (UInt32.ofNat firstInfo.cidx), .eq,
            .iff 0 0 firstTarget
              [.localGet discrIndex, .call getTagIndex,
                .const (UInt32.ofNat secondInfo.cidx), .eq,
                .iff 0 0 secondTarget defaultTarget]]
          targetStore targetLocals witness tail Q := by
      apply caseChainWP_constructor
        (spec := hosts.spec) (imp := imp) (sourceObject := sourceObject)
        (actualTag := actualTag)
      · exact modeEq
      · exact firstTagFits
      · exact firstAdapted
      · exact secondChainAdapted
      · exact discrFound
      · exact discrKind
      · exact getTagFound
      · exact stateRelated
      · exact sourceLookup
      · exact imported
      · exact spec.hostsSatisfy
      · exact inBounds
      · exact getTagContracted
      · exact parameterCount
      · exact resultCount
      · exact tagged
      · exact actualFits
      · exact firstExpectedFits
      · exact branchWP
    rw [targetEq]
    apply codeWP_cases fallbackCompiled
    simpa only [altsEq] using chain
  · by_cases secondHit : actualTag = secondInfo.cidx
    · have selectedEq : selected = secondBranch := by
        have firstMiss' : firstInfo.cidx ≠ actualTag :=
          fun equal => firstHit equal.symm
        have different : firstInfo.cidx ≠ secondInfo.cidx :=
          fun equal => firstHit (secondHit.trans equal.symm)
        have branchEq : secondBranch = selected := by
          rw [altsEq] at chosen
          simpa [chooseAlt, findCtorAlt, findDefaultAlt, firstHit, firstMiss',
            secondHit, different] using chosen
        exact branchEq.symm
      subst selected
      refine ⟨secondTarget, secondAdapted,
        ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩, ?_⟩
      intro tail Q stable continued
      have continuedOnce :
          CodeWP context sourceModule sourceFunction labels target.wasmModule
            hosts.env sourceRuntime sourceEnv secondBranch secondTarget
            targetStore targetLocals witness tail
            (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
        continued.conseq stable
      have continuedTwice :
          CodeWP context sourceModule sourceFunction labels target.wasmModule
            hosts.env sourceRuntime sourceEnv secondBranch secondTarget
            targetStore targetLocals witness tail
            (CaseResumePost target.wasmModule hosts.env []
              (CaseResumePost target.wasmModule hosts.env [] Q tail) tail) :=
        continuedOnce.conseq stable.resume
      have innerBranchWP :
          Wasm.wp target.wasmModule
            (if actualTag = secondInfo.cidx then secondTarget else
              defaultTarget)
            (CaseResumePost target.wasmModule hosts.env []
              (CaseResumePost target.wasmModule hosts.env [] Q tail) tail)
            targetStore { targetLocals with values := tail } hosts.env := by
        simpa [secondHit] using continuedTwice.2.2
      have innerChain :
          CaseChainWP context sourceModule sourceFunction labels
            target.wasmModule hosts.env sourceRuntime sourceEnv cases.discr
            [.ctorAlt secondInfo secondBranch, .default defaultBranch]
            defaultSymbolic
            [.localGet discrIndex, .call getTagIndex,
              .const (UInt32.ofNat secondInfo.cidx), .eq,
              .iff 0 0 secondTarget defaultTarget]
            targetStore targetLocals witness tail
            (CaseResumePost target.wasmModule hosts.env [] Q tail) := by
        apply caseChainWP_constructor
          (spec := hosts.spec) (imp := imp) (sourceObject := sourceObject)
          (actualTag := actualTag)
        · exact modeEq
        · exact secondTagFits
        · exact secondAdapted
        · exact defaultChainAdapted
        · exact discrFound
        · exact discrKind
        · exact getTagFound
        · exact stateRelated
        · exact sourceLookup
        · exact imported
        · exact spec.hostsSatisfy
        · exact inBounds
        · exact getTagContracted
        · exact parameterCount
        · exact resultCount
        · exact tagged
        · exact actualFits
        · exact secondExpectedFits
        · exact innerBranchWP
      have outerBranchWP :
          Wasm.wp target.wasmModule
            (if actualTag = firstInfo.cidx then firstTarget else
              [.localGet discrIndex, .call getTagIndex,
                .const (UInt32.ofNat secondInfo.cidx), .eq,
                .iff 0 0 secondTarget defaultTarget])
            (CaseResumePost target.wasmModule hosts.env [] Q tail) targetStore
            { targetLocals with values := tail } hosts.env := by
        simpa [firstHit] using innerChain.2.2
      have chain :
          CaseChainWP context sourceModule sourceFunction labels
            target.wasmModule hosts.env sourceRuntime sourceEnv cases.discr
            [.ctorAlt firstInfo firstBranch,
              .ctorAlt secondInfo secondBranch,
              .default defaultBranch]
            defaultSymbolic
            [.localGet discrIndex, .call getTagIndex,
              .const (UInt32.ofNat firstInfo.cidx), .eq,
              .iff 0 0 firstTarget
                [.localGet discrIndex, .call getTagIndex,
                  .const (UInt32.ofNat secondInfo.cidx), .eq,
                  .iff 0 0 secondTarget defaultTarget]]
            targetStore targetLocals witness tail Q := by
        apply caseChainWP_constructor
          (spec := hosts.spec) (imp := imp) (sourceObject := sourceObject)
          (actualTag := actualTag)
        · exact modeEq
        · exact firstTagFits
        · exact firstAdapted
        · exact innerChain.1
        · exact discrFound
        · exact discrKind
        · exact getTagFound
        · exact stateRelated
        · exact sourceLookup
        · exact imported
        · exact spec.hostsSatisfy
        · exact inBounds
        · exact getTagContracted
        · exact parameterCount
        · exact resultCount
        · exact tagged
        · exact actualFits
        · exact firstExpectedFits
        · exact outerBranchWP
      rw [targetEq]
      apply codeWP_cases fallbackCompiled
      simpa only [altsEq] using chain
    · have selectedEq : selected = defaultBranch := by
        have firstMiss' : firstInfo.cidx ≠ actualTag :=
          fun equal => firstHit equal.symm
        have secondMiss' : secondInfo.cidx ≠ actualTag :=
          fun equal => secondHit equal.symm
        have branchEq : defaultBranch = selected := by
          rw [altsEq] at chosen
          simpa [chooseAlt, findCtorAlt, findDefaultAlt, firstHit, firstMiss',
            secondHit, secondMiss'] using chosen
        exact branchEq.symm
      subst selected
      refine ⟨defaultTarget, defaultAdapted',
        ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩, ?_⟩
      intro tail Q stable continued
      have continuedOnce :
          CodeWP context sourceModule sourceFunction labels target.wasmModule
            hosts.env sourceRuntime sourceEnv defaultBranch defaultTarget
            targetStore targetLocals witness tail
            (CaseResumePost target.wasmModule hosts.env [] Q tail) :=
        continued.conseq stable
      have continuedTwice :
          CodeWP context sourceModule sourceFunction labels target.wasmModule
            hosts.env sourceRuntime sourceEnv defaultBranch defaultTarget
            targetStore targetLocals witness tail
            (CaseResumePost target.wasmModule hosts.env []
              (CaseResumePost target.wasmModule hosts.env [] Q tail) tail) :=
        continuedOnce.conseq stable.resume
      have innerBranchWP :
          Wasm.wp target.wasmModule
            (if actualTag = secondInfo.cidx then secondTarget else
              defaultTarget)
            (CaseResumePost target.wasmModule hosts.env []
              (CaseResumePost target.wasmModule hosts.env [] Q tail) tail)
            targetStore { targetLocals with values := tail } hosts.env := by
        simpa [secondHit] using continuedTwice.2.2
      have innerChain :
          CaseChainWP context sourceModule sourceFunction labels
            target.wasmModule hosts.env sourceRuntime sourceEnv cases.discr
            [.ctorAlt secondInfo secondBranch, .default defaultBranch]
            defaultSymbolic
            [.localGet discrIndex, .call getTagIndex,
              .const (UInt32.ofNat secondInfo.cidx), .eq,
              .iff 0 0 secondTarget defaultTarget]
            targetStore targetLocals witness tail
            (CaseResumePost target.wasmModule hosts.env [] Q tail) := by
        apply caseChainWP_constructor
          (spec := hosts.spec) (imp := imp) (sourceObject := sourceObject)
          (actualTag := actualTag)
        · exact modeEq
        · exact secondTagFits
        · exact secondAdapted
        · exact defaultChainAdapted
        · exact discrFound
        · exact discrKind
        · exact getTagFound
        · exact stateRelated
        · exact sourceLookup
        · exact imported
        · exact spec.hostsSatisfy
        · exact inBounds
        · exact getTagContracted
        · exact parameterCount
        · exact resultCount
        · exact tagged
        · exact actualFits
        · exact secondExpectedFits
        · exact innerBranchWP
      have outerBranchWP :
          Wasm.wp target.wasmModule
            (if actualTag = firstInfo.cidx then firstTarget else
              [.localGet discrIndex, .call getTagIndex,
                .const (UInt32.ofNat secondInfo.cidx), .eq,
                .iff 0 0 secondTarget defaultTarget])
            (CaseResumePost target.wasmModule hosts.env [] Q tail) targetStore
            { targetLocals with values := tail } hosts.env := by
        simpa [firstHit] using innerChain.2.2
      have chain :
          CaseChainWP context sourceModule sourceFunction labels
            target.wasmModule hosts.env sourceRuntime sourceEnv cases.discr
            [.ctorAlt firstInfo firstBranch,
              .ctorAlt secondInfo secondBranch,
              .default defaultBranch]
            defaultSymbolic
            [.localGet discrIndex, .call getTagIndex,
              .const (UInt32.ofNat firstInfo.cidx), .eq,
              .iff 0 0 firstTarget
                [.localGet discrIndex, .call getTagIndex,
                  .const (UInt32.ofNat secondInfo.cidx), .eq,
                  .iff 0 0 secondTarget defaultTarget]]
            targetStore targetLocals witness tail Q := by
        apply caseChainWP_constructor
          (spec := hosts.spec) (imp := imp) (sourceObject := sourceObject)
          (actualTag := actualTag)
        · exact modeEq
        · exact firstTagFits
        · exact firstAdapted
        · exact innerChain.1
        · exact discrFound
        · exact discrKind
        · exact getTagFound
        · exact stateRelated
        · exact sourceLookup
        · exact imported
        · exact spec.hostsSatisfy
        · exact inBounds
        · exact getTagContracted
        · exact parameterCount
        · exact resultCount
        · exact tagged
        · exact actualFits
        · exact firstExpectedFits
        · exact outerBranchWP
      rw [targetEq]
      apply codeWP_cases fallbackCompiled
      simpa only [altsEq] using chain

/--
The production compiler, adapter, concrete resolver, and reusable external
implementation law jointly discharge every name in
`PureIntegerExternalName` for the budgeted structural theorem.

All physical arguments, decoded lanes, the import/local indices, allocation
address, response, and extended witness are constructed inside the proof.
-/
theorem ConcreteSupportedExport.externalLetRuntimeRefinesWithCost_pureInteger
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
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureIntegerExternalSupported context externals)
      (ConcreteBudgetedIntegerExternalFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue targetStore targetLocals resultIndex remainingBytes
    stepCost witness supported stepFits invariant sourceStep stateRelated
    valueCompiled valueAdapted resultFound
  rcases supported with
    ⟨name, args, argumentCode, argumentKinds, semanticArgs, declaration, value,
      valueEq, _family, nonempty, targetFound, targetExternal, valueKind,
      argumentsCompiled, argumentsEvaluated, signature, resultCompiled,
      semanticCalled, nextRuntimeEq, sourceValueEq, stepCostEq⟩
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (argumentCode ++ [.call (.declaration name)]) := by
    simp [Fir.Wasm.compileLetValue, valueEq, valueKind, argumentsCompiled,
      targetFound, nonempty, Bind.bind, Except.bind, pure, Except.pure]
  have valueCodeEq :
      valueCode = argumentCode ++ [.call (.declaration name)] := by
    rw [expectedCompiled] at valueCompiled
    exact (Except.ok.inj valueCompiled).symm
  subst valueCode
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_declaration_call_eq valueAdapted
  subst targetValue
  obtain ⟨physicalArgs, argumentsReady, physicalLength, argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      argumentsAdapted argumentsEvaluated stateRelated
  obtain ⟨concreteArgs, decoded, concreteLength, semanticLength,
      concreteRelated⟩ :=
    argumentsRelated.decodePhysicalLanes 0
  have programTargetFound :
      program.findDecl? name = some declaration := by
    rw [← spec.contextProgram]
    exact targetFound
  obtain ⟨externalOperation, resultKind, imp, operationName,
      operationMatches, resultSignature, imported, inBounds, contracted,
      parameterCount, resultCount⟩ :=
    spec.externalCall programTargetFound targetExternal callFound
  have operationSignature :
      externalOperation.signature =
        { params := argumentKinds, results := #[.tobject] } := by
    have signatureMatch := operationMatches.signature
    rw [signature] at signatureMatch
    exact (Except.ok.inj signatureMatch).symm
  have resultKindEq : resultKind = .tobject := by
    have resultAt :=
      congrArg (fun results : Array AbiKind => results[0]?) resultSignature
    symm
    simpa [operationSignature] using resultAt
  have declarationName : name = declaration.name :=
    operationName.symm.trans operationMatches.name
  have requestEq :
      externalOperation.request semanticArgs =
        declarationExternalRequest declaration semanticArgs := by
    simp [ExternalOperation.request, declarationExternalRequest,
      operationName, declarationName, operationMatches.paramTypes,
      operationMatches.resultType]
  have requestRelated :
      ConcreteExternalRequestRel witness
        (concreteExternalRequest externalOperation resultKind
          concreteArgs.toArray)
        (externalOperation.request semanticArgs) := by
    refine {
      name := rfl
      paramTypes := rfl
      resultType := rfl
      paramTypesSize := operationMatches.paramTypesSize
      paramKindsSize := ?_
      argsSize := ?_
      arguments := ?_ }
    · change externalOperation.signature.params.size = semanticArgs.size
      rw [operationSignature]
      simpa using semanticLength.symm
    · change concreteArgs.toArray.size = semanticArgs.size
      simpa using concreteLength.trans semanticLength.symm
    · intro index kind lane semantic kindAt laneAt semanticAt
      change externalOperation.signature.params[index]? = some kind at kindAt
      change concreteArgs.toArray[index]? = some lane at laneAt
      change semanticArgs[index]? = some semantic at semanticAt
      exact concreteRelated index kind lane semantic
        (by rw [operationSignature] at kindAt; simpa using kindAt)
        (by simpa using laneAt) (by simpa using semanticAt)
  have semanticCalled' :
      externals.call (externalOperation.request semanticArgs) sourceRuntime =
        .ok (semanticIntegerExternalResponse sourceRuntime value) := by
    rw [requestEq]
    exact semanticCalled
  have fits : integerAllocationBytes value ≤ remainingBytes := by
    simpa [stepCostEq] using stepFits
  have decoded' :
      decodePhysicalLanes 0 externalOperation.signature.params.toList
        physicalArgs = .ok concreteArgs := by
    simpa [operationSignature] using decoded
  obtain ⟨allocatedHeap, address, allocated, operationStep, _,
      witnessExtension, nextRuntimeRelated, resultRelated, remainingBudget⟩ :=
    integerExternalStep_of_budget externalOperation resultKind targetStore
      physicalArgs concreteArgs semanticArgs witness sourceRuntime externals
      value remainingBytes decoded' stateRelated.1 requestRelated invariant.2
      resultKindEq semanticCalled' invariant.1.2 fits
  have resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some (.tobject) := by
    obtain ⟨actualIndex, actualFound, actualKindAt⟩ :=
      spec.localsAligned resultCompiled
    rw [resultFound] at actualFound
    injection actualFound with indexEq
    subst actualIndex
    exact actualKindAt
  let response :=
    concreteIntegerExternalResponse targetStore.host.runtime allocatedHeap
      address
  let nextStore :=
    replaceRuntime targetStore
      (targetStore.host.runtime.applyExternalResponse
        (concreteExternalRequest externalOperation resultKind
          concreteArgs.toArray)
        response)
  let nextWitness :=
    witness.bindInteger sourceRuntime.nextLocation address value
  obtain ⟨updated, targetSet, updatedFrame⟩ :=
    invariant.1.1.set?
      (nextRuntime := semanticExternalRuntimeAfter
        (externalOperation.request semanticArgs) sourceRuntime
        (semanticIntegerExternalResponse sourceRuntime value))
      (nextEnv := bind sourceEnv decl.fvarId
        (semanticIntegerExternalResponse sourceRuntime value).value)
      (nextStore := nextStore) (nextWitness := nextWitness)
      (physical := physicalOfLane response.value) resultFound
  have failureClear : nextStore.host.failure? = none := by
    simp [nextStore, replaceRuntime, clearFailure]
  have nextRuntimeRelated' :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticIntegerExternalResponse sourceRuntime value)) := by
    simpa [nextStore, nextWitness, response, replaceRuntime, clearFailure] using
      nextRuntimeRelated
  have nextStateRelated :
      StateRelated sourceFunction
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticIntegerExternalResponse sourceRuntime value))
        (bind sourceEnv decl.fvarId
          (semanticIntegerExternalResponse sourceRuntime value).value)
        nextStore updated nextWitness :=
    stateRelated.bindAfter witnessExtension nextRuntimeRelated' failureClear
      resultFound resultKindAt
      (by simpa [resultKindEq, response, nextWitness] using resultRelated)
      targetSet
  have parameterCount' : imp.params.length = physicalArgs.length := by
    calc
      imp.params.length = externalOperation.signature.params.size :=
        parameterCount
      _ = argumentKinds.size := by simp [operationSignature]
      _ = physicalArgs.length := physicalLength.symm
  have step :
      ExternalLetStepSimulates context sourceFunction target.wasmModule
        hosts.env externals decl continuation
        (targetArguments ++ [.call callIndex]) sourceRuntime
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticIntegerExternalResponse sourceRuntime value))
        sourceEnv (semanticIntegerExternalResponse sourceRuntime value).value
        targetStore nextStore targetLocals updated resultIndex witness
        nextWitness := by
    refine ⟨?_, stateRelated, nextStateRelated, ?_⟩
    · simpa [nextRuntimeEq, sourceValueEq, requestEq] using sourceStep
    · intro rest Q tail continued
      simpa [List.append_assoc] using
        wp_external_ready_let externalOperation resultKind tail
          argumentsReady imported spec.hostsSatisfy inBounds contracted
          parameterCount' resultCount operationStep targetSet continued
  have nextBudget :
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - integerAllocationBytes value) := by
    simpa [nextStore, response, replaceRuntime, clearFailure,
      concreteIntegerExternalResponse,
      ConcreteRuntimeState.applyExternalResponse] using remainingBudget
  have nextImplementation :
      nextStore.host.externals.IntegerResultRefines externals := by
    change targetStore.host.externals.IntegerResultRefines externals
    exact invariant.2
  subst nextRuntime
  subst sourceValue
  subst stepCost
  exact ⟨nextStore, updated, nextWitness, by simpa [requestEq] using step,
    by simp [nextStore, replaceRuntime, clearFailure],
    by simp [nextStore, replaceRuntime, clearFailure],
    witnessExtension.closureDescriptors,
    ⟨⟨by simpa [requestEq] using updatedFrame, nextBudget⟩,
      nextImplementation⟩⟩

/--
The production compiler, adapter, concrete resolver, and reusable
natural-result implementation law jointly discharge `Int.natAbs`.

The proof constructs the physical arguments, target indices, concrete natural
representation, and post-witness from the generated export and source result;
none of those target artifacts appear in the source admission relation.
-/
theorem ConcreteSupportedExport.externalLetRuntimeRefinesWithCost_pureNatural
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
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureNaturalExternalSupported context externals)
      (ConcreteBudgetedNaturalExternalFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue targetStore targetLocals resultIndex remainingBytes
    stepCost witness supported stepFits invariant sourceStep stateRelated
    valueCompiled valueAdapted resultFound
  rcases supported with
    ⟨name, args, argumentCode, argumentKinds, semanticArgs, declaration, value,
      valueEq, _family, nonempty, targetFound, targetExternal, valueKind,
      argumentsCompiled, argumentsEvaluated, signature, resultCompiled,
      semanticCalled, nextRuntimeEq, sourceValueEq, stepCostEq⟩
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (argumentCode ++ [.call (.declaration name)]) := by
    simp [Fir.Wasm.compileLetValue, valueEq, valueKind, argumentsCompiled,
      targetFound, nonempty, Bind.bind, Except.bind, pure, Except.pure]
  have valueCodeEq :
      valueCode = argumentCode ++ [.call (.declaration name)] := by
    rw [expectedCompiled] at valueCompiled
    exact (Except.ok.inj valueCompiled).symm
  subst valueCode
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_declaration_call_eq valueAdapted
  subst targetValue
  obtain ⟨physicalArgs, argumentsReady, physicalLength, argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      argumentsAdapted argumentsEvaluated stateRelated
  obtain ⟨concreteArgs, decoded, concreteLength, semanticLength,
      concreteRelated⟩ :=
    argumentsRelated.decodePhysicalLanes 0
  have programTargetFound :
      program.findDecl? name = some declaration := by
    rw [← spec.contextProgram]
    exact targetFound
  obtain ⟨externalOperation, resultKind, imp, operationName,
      operationMatches, resultSignature, imported, inBounds, contracted,
      parameterCount, resultCount⟩ :=
    spec.externalCall programTargetFound targetExternal callFound
  have operationSignature :
      externalOperation.signature =
        { params := argumentKinds, results := #[.tobject] } := by
    have signatureMatch := operationMatches.signature
    rw [signature] at signatureMatch
    exact (Except.ok.inj signatureMatch).symm
  have resultKindEq : resultKind = .tobject := by
    have resultAt :=
      congrArg (fun results : Array AbiKind => results[0]?) resultSignature
    symm
    simpa [operationSignature] using resultAt
  have declarationName : name = declaration.name :=
    operationName.symm.trans operationMatches.name
  have requestEq :
      externalOperation.request semanticArgs =
        declarationExternalRequest declaration semanticArgs := by
    simp [ExternalOperation.request, declarationExternalRequest,
      operationName, declarationName, operationMatches.paramTypes,
      operationMatches.resultType]
  have requestRelated :
      ConcreteExternalRequestRel witness
        (concreteExternalRequest externalOperation resultKind
          concreteArgs.toArray)
        (externalOperation.request semanticArgs) := by
    refine {
      name := rfl
      paramTypes := rfl
      resultType := rfl
      paramTypesSize := operationMatches.paramTypesSize
      paramKindsSize := ?_
      argsSize := ?_
      arguments := ?_ }
    · change externalOperation.signature.params.size = semanticArgs.size
      rw [operationSignature]
      simpa using semanticLength.symm
    · change concreteArgs.toArray.size = semanticArgs.size
      simpa using concreteLength.trans semanticLength.symm
    · intro index kind lane semantic kindAt laneAt semanticAt
      change externalOperation.signature.params[index]? = some kind at kindAt
      change concreteArgs.toArray[index]? = some lane at laneAt
      change semanticArgs[index]? = some semantic at semanticAt
      exact concreteRelated index kind lane semantic
        (by rw [operationSignature] at kindAt; simpa using kindAt)
        (by simpa using laneAt) (by simpa using semanticAt)
  have semanticCalled' :
      externals.call (externalOperation.request semanticArgs) sourceRuntime =
        .ok (semanticNaturalExternalResponse sourceRuntime value) := by
    rw [requestEq]
    exact semanticCalled
  have fits : naturalAllocationBytes value ≤ remainingBytes := by
    simpa [stepCostEq] using stepFits
  have decoded' :
      decodePhysicalLanes 0 externalOperation.signature.params.toList
        physicalArgs = .ok concreteArgs := by
    simpa [operationSignature] using decoded
  obtain ⟨allocatedHeap, word, nextWitness, allocated, operationStep, _,
      witnessExtension, nextRuntimeRelated, resultRelated, remainingBudget⟩ :=
    naturalExternalStep_of_budget externalOperation resultKind targetStore
      physicalArgs concreteArgs semanticArgs witness sourceRuntime externals
      value remainingBytes decoded' stateRelated.1 requestRelated invariant.2
      resultKindEq semanticCalled' invariant.1.2 fits
  have resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some (.tobject) := by
    obtain ⟨actualIndex, actualFound, actualKindAt⟩ :=
      spec.localsAligned resultCompiled
    rw [resultFound] at actualFound
    injection actualFound with indexEq
    subst actualIndex
    exact actualKindAt
  let response :=
    concreteNaturalExternalResponse targetStore.host.runtime allocatedHeap word
  let nextStore :=
    replaceRuntime targetStore
      (targetStore.host.runtime.applyExternalResponse
        (concreteExternalRequest externalOperation resultKind
          concreteArgs.toArray)
        response)
  obtain ⟨updated, targetSet, updatedFrame⟩ :=
    invariant.1.1.set?
      (nextRuntime := semanticExternalRuntimeAfter
        (externalOperation.request semanticArgs) sourceRuntime
        (semanticNaturalExternalResponse sourceRuntime value))
      (nextEnv := bind sourceEnv decl.fvarId
        (semanticNaturalExternalResponse sourceRuntime value).value)
      (nextStore := nextStore) (nextWitness := nextWitness)
      (physical := physicalOfLane response.value) resultFound
  have failureClear : nextStore.host.failure? = none := by
    simp [nextStore, replaceRuntime, clearFailure]
  have nextRuntimeRelated' :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticNaturalExternalResponse sourceRuntime value)) := by
    simpa [nextStore, response, replaceRuntime, clearFailure] using
      nextRuntimeRelated
  have nextStateRelated :
      StateRelated sourceFunction
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticNaturalExternalResponse sourceRuntime value))
        (bind sourceEnv decl.fvarId
          (semanticNaturalExternalResponse sourceRuntime value).value)
        nextStore updated nextWitness :=
    stateRelated.bindAfter witnessExtension nextRuntimeRelated' failureClear
      resultFound resultKindAt
      (by simpa [resultKindEq, response] using resultRelated)
      targetSet
  have parameterCount' : imp.params.length = physicalArgs.length := by
    calc
      imp.params.length = externalOperation.signature.params.size :=
        parameterCount
      _ = argumentKinds.size := by simp [operationSignature]
      _ = physicalArgs.length := physicalLength.symm
  have step :
      ExternalLetStepSimulates context sourceFunction target.wasmModule
        hosts.env externals decl continuation
        (targetArguments ++ [.call callIndex]) sourceRuntime
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticNaturalExternalResponse sourceRuntime value))
        sourceEnv (semanticNaturalExternalResponse sourceRuntime value).value
        targetStore nextStore targetLocals updated resultIndex witness
        nextWitness := by
    refine ⟨?_, stateRelated, nextStateRelated, ?_⟩
    · simpa [nextRuntimeEq, sourceValueEq, requestEq] using sourceStep
    · intro rest Q tail continued
      simpa [List.append_assoc] using
        wp_external_ready_let externalOperation resultKind tail
          argumentsReady imported spec.hostsSatisfy inBounds contracted
          parameterCount' resultCount operationStep targetSet continued
  have nextBudget :
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - naturalAllocationBytes value) := by
    simpa [nextStore, response, replaceRuntime, clearFailure,
      concreteNaturalExternalResponse,
      ConcreteRuntimeState.applyExternalResponse] using remainingBudget
  have nextImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        nextStore.host.externals externals := by
    change
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        targetStore.host.externals externals
    exact invariant.2
  subst nextRuntime
  subst sourceValue
  subst stepCost
  exact ⟨nextStore, updated, nextWitness, by simpa [requestEq] using step,
    by simp [nextStore, replaceRuntime, clearFailure],
    by simp [nextStore, replaceRuntime, clearFailure],
    witnessExtension.closureDescriptors,
    ⟨⟨by simpa [requestEq] using updatedFrame, nextBudget⟩,
      nextImplementation⟩⟩

/--
Compiler-shaped correctness for the admitted pure scalar-result family,
initially `Int.decLt`.

The semantic scalar determines the result ABI and exact lane. Production
compilation, adaptation, static resolution, operand decoding, and destination
binding are all reconstructed internally, while the heap budget and witness
remain unchanged.
-/
theorem ConcreteSupportedExport.externalLetRuntimeRefinesWithCost_pureScalar
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
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureScalarExternalSupported context externals)
      (ConcreteBudgetedScalarExternalFrame sourceFunction externals) := by
  intro sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue targetStore targetLocals resultIndex remainingBytes
    stepCost witness supported _stepFits invariant sourceStep stateRelated
    valueCompiled valueAdapted resultFound
  rcases supported with
    ⟨name, args, argumentCode, argumentKinds, semanticArgs, declaration, scalar,
      valueEq, _family, nonempty, targetFound, targetExternal, valueKind,
      argumentsCompiled, argumentsEvaluated, signature, resultCompiled,
      semanticCalled, nextRuntimeEq, sourceValueEq, stepCostEq⟩
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (argumentCode ++ [.call (.declaration name)]) := by
    simp [Fir.Wasm.compileLetValue, valueEq, valueKind, argumentsCompiled,
      targetFound, nonempty, Bind.bind, Except.bind, pure, Except.pure]
  have valueCodeEq :
      valueCode = argumentCode ++ [.call (.declaration name)] := by
    rw [expectedCompiled] at valueCompiled
    exact (Except.ok.inj valueCompiled).symm
  subst valueCode
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_declaration_call_eq valueAdapted
  subst targetValue
  obtain ⟨physicalArgs, argumentsReady, physicalLength, argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      argumentsAdapted argumentsEvaluated stateRelated
  obtain ⟨concreteArgs, decoded, concreteLength, semanticLength,
      concreteRelated⟩ :=
    argumentsRelated.decodePhysicalLanes 0
  have programTargetFound :
      program.findDecl? name = some declaration := by
    rw [← spec.contextProgram]
    exact targetFound
  obtain ⟨externalOperation, resultKind, imp, operationName,
      operationMatches, resultSignature, imported, inBounds, contracted,
      parameterCount, resultCount⟩ :=
    spec.externalCall programTargetFound targetExternal callFound
  have operationSignature :
      externalOperation.signature = {
        params := argumentKinds
        results := #[scalar.kind.abiKind] } := by
    have signatureMatch := operationMatches.signature
    rw [signature] at signatureMatch
    exact (Except.ok.inj signatureMatch).symm
  have resultKindEq : resultKind = scalar.kind.abiKind := by
    have resultAt :=
      congrArg (fun results : Array AbiKind => results[0]?) resultSignature
    symm
    simpa [operationSignature] using resultAt
  have declarationName : name = declaration.name :=
    operationName.symm.trans operationMatches.name
  have requestEq :
      externalOperation.request semanticArgs =
        declarationExternalRequest declaration semanticArgs := by
    simp [ExternalOperation.request, declarationExternalRequest,
      operationName, declarationName, operationMatches.paramTypes,
      operationMatches.resultType]
  have requestRelated :
      ConcreteExternalRequestRel witness
        (concreteExternalRequest externalOperation resultKind
          concreteArgs.toArray)
        (externalOperation.request semanticArgs) := by
    refine {
      name := rfl
      paramTypes := rfl
      resultType := rfl
      paramTypesSize := operationMatches.paramTypesSize
      paramKindsSize := ?_
      argsSize := ?_
      arguments := ?_ }
    · change externalOperation.signature.params.size = semanticArgs.size
      rw [operationSignature]
      simpa using semanticLength.symm
    · change concreteArgs.toArray.size = semanticArgs.size
      simpa using concreteLength.trans semanticLength.symm
    · intro index kind lane semantic kindAt laneAt semanticAt
      change externalOperation.signature.params[index]? = some kind at kindAt
      change concreteArgs.toArray[index]? = some lane at laneAt
      change semanticArgs[index]? = some semantic at semanticAt
      exact concreteRelated index kind lane semantic
        (by rw [operationSignature] at kindAt; simpa using kindAt)
        (by simpa using laneAt) (by simpa using semanticAt)
  have semanticCalled' :
      externals.call (externalOperation.request semanticArgs) sourceRuntime =
        .ok (semanticScalarExternalResponse sourceRuntime scalar) := by
    rw [requestEq]
    exact semanticCalled
  have decoded' :
      decodePhysicalLanes 0 externalOperation.signature.params.toList
        physicalArgs = .ok concreteArgs := by
    simpa [operationSignature] using decoded
  obtain ⟨operationStep, _, nextRuntimeRelated, resultRelated⟩ :=
    scalarExternalStep externalOperation resultKind targetStore physicalArgs
      concreteArgs semanticArgs witness sourceRuntime externals scalar decoded'
      stateRelated.1 requestRelated invariant.2 resultKindEq semanticCalled'
  have resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some scalar.kind.abiKind := by
    obtain ⟨actualIndex, actualFound, actualKindAt⟩ :=
      spec.localsAligned resultCompiled
    rw [resultFound] at actualFound
    injection actualFound with indexEq
    subst actualIndex
    exact actualKindAt
  let response :=
    concreteScalarExternalResponse targetStore.host.runtime scalar
  let nextStore :=
    replaceRuntime targetStore
      (targetStore.host.runtime.applyExternalResponse
        (concreteExternalRequest externalOperation resultKind
          concreteArgs.toArray)
        response)
  obtain ⟨updated, targetSet, updatedFrame⟩ :=
    invariant.1.1.set?
      (nextRuntime := semanticExternalRuntimeAfter
        (externalOperation.request semanticArgs) sourceRuntime
        (semanticScalarExternalResponse sourceRuntime scalar))
      (nextEnv := bind sourceEnv decl.fvarId
        (semanticScalarExternalResponse sourceRuntime scalar).value)
      (nextStore := nextStore) (nextWitness := witness)
      (physical := physicalOfLane response.value) resultFound
  have failureClear : nextStore.host.failure? = none := by
    simp [nextStore, replaceRuntime, clearFailure]
  have nextRuntimeRelated' :
      ConcreteRuntimeRel nextStore.host.runtime witness
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticScalarExternalResponse sourceRuntime scalar)) := by
    simpa [nextStore, response, replaceRuntime, clearFailure] using
      nextRuntimeRelated
  have nextStateRelated :
      StateRelated sourceFunction
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticScalarExternalResponse sourceRuntime scalar))
        (bind sourceEnv decl.fvarId
          (semanticScalarExternalResponse sourceRuntime scalar).value)
        nextStore updated witness :=
    stateRelated.bindAfter (.refl witness) nextRuntimeRelated' failureClear
      resultFound resultKindAt
      (by simpa [resultKindEq, response] using resultRelated)
      targetSet
  have parameterCount' : imp.params.length = physicalArgs.length := by
    calc
      imp.params.length = externalOperation.signature.params.size :=
        parameterCount
      _ = argumentKinds.size := by simp [operationSignature]
      _ = physicalArgs.length := physicalLength.symm
  have step :
      ExternalLetStepSimulates context sourceFunction target.wasmModule
        hosts.env externals decl continuation
        (targetArguments ++ [.call callIndex]) sourceRuntime
        (semanticExternalRuntimeAfter
          (externalOperation.request semanticArgs) sourceRuntime
          (semanticScalarExternalResponse sourceRuntime scalar))
        sourceEnv (semanticScalarExternalResponse sourceRuntime scalar).value
        targetStore nextStore targetLocals updated resultIndex witness
        witness := by
    refine ⟨?_, stateRelated, nextStateRelated, ?_⟩
    · simpa [nextRuntimeEq, sourceValueEq, requestEq] using sourceStep
    · intro rest Q tail continued
      simpa [List.append_assoc] using
        wp_external_ready_let externalOperation resultKind tail
          argumentsReady imported spec.hostsSatisfy inBounds contracted
          parameterCount' resultCount operationStep targetSet continued
  have nextBudget :
      nextStore.host.runtime.heap.AddressSpaceBudget remainingBytes := by
    simpa [nextStore, response, replaceRuntime, clearFailure,
      concreteScalarExternalResponse,
      ConcreteRuntimeState.applyExternalResponse] using invariant.1.2
  have nextImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        nextStore.host.externals externals := by
    change
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        targetStore.host.externals externals
    exact invariant.2
  subst nextRuntime
  subst sourceValue
  subst stepCost
  exact ⟨nextStore, updated, witness, by simpa [requestEq] using step,
    by simp [nextStore, replaceRuntime, clearFailure],
    by simp [nextStore, replaceRuntime, clearFailure], rfl,
    ⟨⟨by simpa [requestEq] using updatedFrame, nextBudget⟩,
      nextImplementation⟩⟩

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

/-- Cost-indexed runtime laws compose when they use the same source cost
function and indexed invariant. -/
theorem DirectLetRuntimeRefinesWithCost.or
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {Left Right : LCNF.LetDecl .impure → Prop}
    {letCost : LCNF.LetDecl .impure → Nat}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (left :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
        module hostEnv Left letCost Invariant)
    (right :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
        module hostEnv Right letCost Invariant) :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      module hostEnv (fun decl => Left decl ∨ Right decl) letCost Invariant := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported stepFits invariant sourceStep stateRelated valueCompiled
    valueAdapted resultFound
  cases supported with
  | inl leftSupported =>
      exact left leftSupported stepFits invariant sourceStep stateRelated
        valueCompiled valueAdapted resultFound
  | inr rightSupported =>
      exact right rightSupported stepFits invariant sourceStep stateRelated
        valueCompiled valueAdapted resultFound

/--
A costed direct runtime law lifts through any invariant of the installed
concrete external implementation. The strengthened direct-step boundary
supplies the only needed fact: direct generated helpers leave
`Host.externals` unchanged.
-/
theorem DirectLetRuntimeRefinesWithCost.preservingExternalInvariant
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {Supported : LCNF.LetDecl .impure → Prop}
    {letCost : LCNF.LetDecl .impure → Nat}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    {ExternalInvariant : ConcreteExternalImpl → Prop}
    (runtimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
        module hostEnv Supported letCost Invariant) :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      module hostEnv Supported letCost
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        Invariant remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness ∧
          ExternalInvariant targetStore.host.externals) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported stepFits invariant sourceStep stateRelated valueCompiled
    valueAdapted resultFound
  obtain ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
      hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant⟩ :=
    runtimeRefines supported stepFits invariant.1 sourceStep stateRelated
      valueCompiled valueAdapted resultFound
  exact ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant,
    by simpa [externalsPreserved] using invariant.2⟩

/--
A costed direct runtime law lifts through concrete/witness closure-descriptor
agreement. Direct helpers preserve both immutable tables independently, so
agreement at the entry state is sufficient to re-establish it for the
continuation.
-/
theorem DirectLetRuntimeRefinesWithCost.preservingClosureDescriptorAgreement
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {Supported : LCNF.LetDecl .impure → Prop}
    {letCost : LCNF.LetDecl .impure → Nat}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (runtimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
        module hostEnv Supported letCost Invariant) :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      module hostEnv Supported letCost
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        Invariant remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness ∧
          targetStore.host.closureDescriptors = witness.closureDescriptors) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported stepFits invariant sourceStep stateRelated valueCompiled
    valueAdapted resultFound
  obtain ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
      hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant⟩ :=
    runtimeRefines supported stepFits invariant.1 sourceStep stateRelated
      valueCompiled valueAdapted resultFound
  exact ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant,
    hostDescriptorsPreserved.trans
      (invariant.2.trans witnessDescriptorsPreserved.symm)⟩

/-- Cost-indexed external runtime laws compose by source admission
disjunction when they share the same threaded invariant. -/
theorem ExternalLetRuntimeRefinesWithCost.or
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {Left Right :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (left :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction
        labels module hostEnv externals Left Invariant)
    (right :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction
        labels module hostEnv externals Right Invariant) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      module hostEnv externals
      (fun sourceRuntime sourceEnv decl continuation nextRuntime sourceValue
          stepCost =>
        Left sourceRuntime sourceEnv decl continuation nextRuntime sourceValue
            stepCost ∨
          Right sourceRuntime sourceEnv decl continuation nextRuntime sourceValue
            stepCost)
      Invariant := by
  intro sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue targetStore targetLocals resultIndex remainingBytes
    stepCost witness supported stepFits invariant sourceStep stateRelated
    valueCompiled valueAdapted resultFound
  cases supported with
  | inl leftSupported =>
      exact left leftSupported stepFits invariant sourceStep stateRelated
        valueCompiled valueAdapted resultFound
  | inr rightSupported =>
      exact right rightSupported stepFits invariant sourceStep stateRelated
        valueCompiled valueAdapted resultFound

/-- External runtime laws lift through an additional installed-handler
property because successful external responses preserve the handler table. -/
theorem ExternalLetRuntimeRefinesWithCost.preservingExternalInvariant
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {Supported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    {ExternalInvariant : ConcreteExternalImpl → Prop}
    (runtimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction
        labels module hostEnv externals Supported Invariant) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      module hostEnv externals Supported
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        Invariant remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness ∧
          ExternalInvariant targetStore.host.externals) := by
  intro sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue targetStore targetLocals resultIndex remainingBytes
    stepCost witness supported stepFits invariant sourceStep stateRelated
    valueCompiled valueAdapted resultFound
  obtain ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
      hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant⟩ :=
    runtimeRefines supported stepFits invariant.1 sourceStep stateRelated
      valueCompiled valueAdapted resultFound
  exact ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant,
    by simpa [externalsPreserved] using invariant.2⟩

/--
An external runtime law also lifts through closure-descriptor agreement.
Successful pure external calls may extend the heap witness, but they preserve
its immutable closure table and leave the concrete host table unchanged.
-/
theorem ExternalLetRuntimeRefinesWithCost.preservingClosureDescriptorAgreement
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {Supported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (runtimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction
        labels module hostEnv externals Supported Invariant) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      module hostEnv externals Supported
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        Invariant remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness ∧
          targetStore.host.closureDescriptors = witness.closureDescriptors) := by
  intro sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue targetStore targetLocals resultIndex remainingBytes
    stepCost witness supported stepFits invariant sourceStep stateRelated
    valueCompiled valueAdapted resultFound
  obtain ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
      hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant⟩ :=
    runtimeRefines supported stepFits invariant.1 sourceStep stateRelated
      valueCompiled valueAdapted resultFound
  exact ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant,
    hostDescriptorsPreserved.trans
      (invariant.2.trans witnessDescriptorsPreserved.symm)⟩

/-- Transport an external runtime law across a pointwise equivalent threaded
invariant. -/
theorem ExternalLetRuntimeRefinesWithCost.mapInvariant
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {Supported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {Old New :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (runtimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction
        labels module hostEnv externals Supported Old)
    (toOld : ∀ remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness,
      New remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness →
        Old remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness)
    (toNew : ∀ remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness,
      Old remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness →
        New remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      module hostEnv externals Supported New := by
  intro sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue targetStore targetLocals resultIndex remainingBytes
    stepCost witness supported stepFits invariant sourceStep stateRelated
    valueCompiled valueAdapted resultFound
  obtain ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
      hostDescriptorsPreserved, witnessDescriptorsPreserved, nextInvariant⟩ :=
    runtimeRefines supported stepFits
      (toOld remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness invariant)
      sourceStep stateRelated valueCompiled valueAdapted resultFound
  exact ⟨nextStore, nextLocals, nextWitness, step, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved,
    toNew (remainingBytes - stepCost) nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness
      nextInvariant⟩

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

/-- Cost-zero indexed instance for local aliases. The generated local copy
leaves the concrete heap and therefore the complete address-space budget
unchanged. -/
theorem directLetRuntimeRefinesWithCost_localAlias
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    (localsAligned : LocalLayoutAligned context sourceFunction) :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      module hostEnv (LocalAliasSupported context) directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported _ budgeted sourceStep stateRelated valueCompiled valueAdapted
    resultFound
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
    budgeted.1.set? (nextRuntime := nextRuntime)
      (nextEnv := bind sourceEnv decl.fvarId sourceValue)
      (nextStore := targetStore) (nextWitness := witness)
      (physical := physical) resultFound
  have costZero : directLetAllocationCost decl = 0 := by
    simp [directLetAllocationCost, valueEq]
  exact ⟨targetStore, updated, witness,
    letStepSimulates_localAlias valueEq sourceLookup stateRelated resultFound
      resultKindAt sourcePhysical physicalRelated targetSet,
    rfl, rfl, rfl, nextFrameAligned, by simpa [costZero] using budgeted.2⟩

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

/-- Cost-zero indexed instance for immediate integer and `USize` literals.
The generated constant/local write preserves the entire heap budget. -/
theorem ConcreteSupportedExport.directLetRuntimeRefinesWithCost_immediateLiteral
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ImmediateLiteralSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported _ budgeted sourceStep stateRelated valueCompiled valueAdapted
    resultFound
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
    budgeted.1.set?
      (nextRuntime := nextRuntime)
      (nextEnv := bind sourceEnv decl.fvarId shape.sourceValue)
      (nextStore := targetStore)
      (nextWitness := witness)
      (physical := shape.physical) resultFound
  have costZero : directLetAllocationCost decl = 0 := by
    cases shape <;> simp [directLetAllocationCost, valueEq]
  exact ⟨targetStore, updated, witness,
    letStepSimulates_immediateLiteral shape sourceStep stateRelated resultFound
      resultKindAt targetSet,
    rfl, rfl, rfl, nextFrameAligned, by simpa [costZero] using budgeted.2⟩

/--
Cost-indexed runtime-law instance for representation-polymorphic natural
literals.

`naturalAllocationBytes` selects zero cost, a promoted-tag extent, or a
variable limb-object extent from the source value. The constructive allocator
returns both the exact concrete representation and its residual budget; the
ordinary generated literal-call theorem then establishes the related
continuation state.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_naturalLiteral
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (NaturalLiteralSupported context)
      directLetAllocationCost (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported allocationFits budgeted sourceStep stateRelated valueCompiled
    valueAdapted resultFound
  rcases supported with
    ⟨value, valueEq, valueKind, resultCompiled⟩
  have naturalFits :
      naturalAllocationBytes value ≤ remainingBytes := by
    simpa [directLetAllocationCost, valueEq] using allocationFits
  obtain ⟨heap, word, allocated, remainingBudget⟩ :=
    stateRelated.1.heap.frontier.allocateNatural_eq_ok_of_budget value
      budgeted.2 naturalFits
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.call (.runtime (.literal (.nat value) .tobject))] :=
    compileLetValue_naturalLiteral valueEq valueKind
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
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
      have expectedAdapted :
          instructions sourceModule sourceFunction labels
              [.call (.runtime (.literal (.nat value) .tobject))] =
            .ok [.call callIndex] := by
        simp [instructions, instruction, callFound]
        rfl
      rw [expectedAdapted] at valueAdapted
      injection valueAdapted with targetValueEq
      subst targetValue
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        spec.localsAligned resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      obtain ⟨updated, targetSet⟩ :=
        FirTalos.Correctness.locals_set?_exists
          (budgeted.1.validIndex resultFound)
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        spec.naturalLiteralCall callFound
      obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated, step⟩ :=
        letStepSimulates_naturalLiteral (context := context) valueEq stateRelated
          resultFound resultKindAt allocated imported spec.hostsSatisfy
          inBounds contracted params results targetSet
      obtain ⟨runtimeEq, sourceValueEq⟩ :=
        SourceLetResult.deterministic sourceStep step.1
      subst nextRuntime
      subst sourceValue
      have lengths := FirTalos.Correctness.locals_lengths_of_set? targetSet
      have nextFrame :
          ConcreteLocalFrameAligned sourceFunction
            (literal sourceRuntime (.nat value)).1
            (bind sourceEnv decl.fvarId
              (literal sourceRuntime (.nat value)).2)
            (replaceHeap targetStore heap) updated nextWitness :=
        ⟨lengths.1.trans budgeted.1.1, lengths.2.trans budgeted.1.2⟩
      have nextBudget :
          (replaceHeap targetStore heap).host.runtime.heap.AddressSpaceBudget
            (remainingBytes - naturalAllocationBytes value) := by
        simpa [replaceHeap, clearFailure] using remainingBudget
      exact ⟨replaceHeap targetStore heap, updated, nextWitness, step,
        by simp [replaceHeap, clearFailure],
        by simp [replaceHeap, clearFailure], extension.closureDescriptors,
        nextFrame, by
          simpa [directLetAllocationCost, valueEq] using nextBudget⟩

/--
Cost-indexed runtime-law instance for allocating UTF-8 String literals.

The source declaration determines its exact aligned allocation cost.
`ConcreteBudgetedLocalFrame` supplies that headroom and the local-frame shape;
the concrete allocator returns the residual budget that is paired with the
generated call/local-write simulation for the continuation.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_stringLiteral
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (StringLiteralSupported context)
      directLetAllocationCost (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported allocationFits budgeted sourceStep stateRelated valueCompiled
    valueAdapted resultFound
  rcases supported with
    ⟨value, valueEq, valueKind, resultCompiled⟩
  have stringFits :
      align8 (headerBytes + (stringUtf8Bytes value).length) ≤
        remainingBytes := by
    simpa [directLetAllocationCost, valueEq] using allocationFits
  obtain ⟨heap, word, allocated, remainingBudget⟩ :=
    stateRelated.1.heap.frontier.allocateString_eq_ok_of_budget value
      budgeted.2 stringFits
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.call (.runtime (.literal (.str value) .object))] :=
    compileLetValue_stringLiteral valueEq valueKind
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
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
      have expectedAdapted :
          instructions sourceModule sourceFunction labels
              [.call (.runtime (.literal (.str value) .object))] =
            .ok [.call callIndex] := by
        simp [instructions, instruction, callFound]
        rfl
      rw [expectedAdapted] at valueAdapted
      injection valueAdapted with targetValueEq
      subst targetValue
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        spec.localsAligned resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      obtain ⟨updated, targetSet⟩ :=
        FirTalos.Correctness.locals_set?_exists
          (budgeted.1.validIndex resultFound)
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        spec.stringLiteralCall callFound
      obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated, step⟩ :=
        letStepSimulates_stringLiteral (context := context) valueEq stateRelated
          resultFound resultKindAt allocated imported spec.hostsSatisfy
          inBounds contracted params results targetSet
      obtain ⟨runtimeEq, sourceValueEq⟩ :=
        SourceLetResult.deterministic sourceStep step.1
      subst nextRuntime
      subst sourceValue
      have lengths := FirTalos.Correctness.locals_lengths_of_set? targetSet
      have nextFrame :
          ConcreteLocalFrameAligned sourceFunction
            (literal sourceRuntime (.str value)).1
            (bind sourceEnv decl.fvarId
              (literal sourceRuntime (.str value)).2)
            (replaceHeap targetStore heap) updated nextWitness :=
        ⟨lengths.1.trans budgeted.1.1, lengths.2.trans budgeted.1.2⟩
      have nextBudget :
          (replaceHeap targetStore heap).host.runtime.heap.AddressSpaceBudget
            (remainingBytes -
              align8
                (headerBytes + (stringUtf8Bytes value).length)) := by
        simpa [replaceHeap, clearFailure] using remainingBudget
      exact ⟨replaceHeap targetStore heap, updated, nextWitness, step,
        by simp [replaceHeap, clearFailure],
        by simp [replaceHeap, clearFailure], extension.closureDescriptors,
        nextFrame, by
          simpa [directLetAllocationCost, valueEq] using nextBudget⟩

/--
Cost-indexed runtime-law instance for nonempty constructor allocations.

Source evaluation supplies the semantic arguments and allocation result.
Production compilation/adaptation and `StateRelated` derive the mixed
local/erased physical prefix. The constructive concrete constructor theorem
then returns the generated step together with the exact residual layout
budget.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_nonemptyConstructor
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (NonemptyConstructorSupported context)
      directLetAllocationCost (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported allocationFits budgeted sourceStep stateRelated valueCompiled
    valueAdapted resultFound
  rcases supported with
    ⟨info, args, argumentCode, fieldKinds, resultKind, valueEq, tagFits,
      valueKind, argumentsCompiled, resultCompiled, operationWellFormed,
      nonempty, objectFieldsFit, usizeFieldsFit, scalarBytesFit⟩
  obtain ⟨semanticArgs, evaluated, semanticStep⟩ :=
    sourceLetResult_constructor_eq valueEq sourceStep
  have operationFacts :
      (info.size = fieldKinds.size ∧
        fieldKinds.all AbiKind.isObjectField = true) ∧
        (constructorKind info).refines resultKind = true := by
    simpa [RuntimeOp.abiWellFormed] using operationWellFormed
  have semanticArity : semanticArgs.size = info.size := by
    by_contra mismatch
    simp [allocCtor, mismatch, Bind.bind, Except.bind] at semanticStep
  have tagFits' : info.cidx < UInt32.size := by
    simpa [Fir.Wasm.constructorTagFitsI32] using tagFits
  have constructorFits :
      (ConstructorLayout.ofInfo info).allocationBytes ≤ remainingBytes := by
    simpa [directLetAllocationCost, valueEq] using allocationFits
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (argumentCode ++
          [.call (.runtime (.allocCtor info fieldKinds resultKind))]) :=
    compileLetValue_constructor valueEq tagFits valueKind argumentsCompiled
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_call_eq valueAdapted
  subst targetValue
  obtain ⟨physicalArgs, argumentsReady, physicalArity, argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      argumentsAdapted evaluated stateRelated
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    spec.localsAligned resultCompiled
  rw [resultFound] at alignedResultFound
  injection alignedResultFound with resultIndexEq
  subst alignedResultIndex
  obtain ⟨nextStore, word, nextWitness, operation, externalsPreserved,
      hostDescriptorsPreserved, witnessDescriptorsPreserved, extension,
      nextRuntimeRelated, failureClear, valueRelated, remainingBudget⟩ :=
    constructorNonemptyStep_of_budget stateRelated.1 physicalArity
      argumentsRelated semanticStep semanticArity operationFacts.1.1.symm
      operationFacts.1.2 nonempty tagFits' objectFieldsFit usizeFieldsFit
      scalarBytesFit operationFacts.2 budgeted.2 constructorFits
  obtain ⟨updated, targetSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (budgeted.1.validIndex resultFound)
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.allocCtorCall callFound
  have physicalParams : imp.params.length = physicalArgs.length :=
    params.trans physicalArity.symm
  have step :=
    letStepSimulates_constructorArgs (context := context) valueEq evaluated
      semanticStep stateRelated resultFound resultKindAt argumentsReady imported
      spec.hostsSatisfy inBounds contracted physicalParams results operation
      extension nextRuntimeRelated failureClear valueRelated targetSet
  have lengths := FirTalos.Correctness.locals_lengths_of_set? targetSet
  have nextFrame :
      ConcreteLocalFrameAligned sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore updated
        nextWitness :=
    ⟨lengths.1.trans budgeted.1.1, lengths.2.trans budgeted.1.2⟩
  exact ⟨nextStore, updated, nextWitness, step, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved, nextFrame, by
      simpa [directLetAllocationCost, valueEq] using remainingBudget⟩

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
Cost-indexed runtime-law instance for direct `USize` projections.

The generated reader only clears the host failure slot and leaves the concrete
heap unchanged, so the declaration has zero allocation cost and preserves the
complete residual address-space budget.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefinesWithCost_usizeProjection
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (USizeProjectionSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported _ budgeted sourceStep stateRelated valueCompiled valueAdapted
    resultFound
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
            budgeted.1.set?
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
            by simp [clearFailure], by simp [clearFailure], rfl,
            nextFrameAligned, by
              simpa [directLetAllocationCost, valueEq, clearFailure] using
                budgeted.2⟩
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
Cost-indexed runtime-law instance for direct object projections.

Successful field reads preserve the concrete heap exactly.  Consequently the
projection threads the same address-space budget through the compiler-emitted
host call and destination-local write.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefinesWithCost_objectProjection
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ObjectProjectionSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported _ budgeted sourceStep stateRelated valueCompiled valueAdapted
    resultFound
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
            budgeted.1.set?
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
            by simp [clearFailure], by simp [clearFailure], rfl,
            nextFrameAligned, by
              simpa [directLetAllocationCost, valueEq, clearFailure] using
                budgeted.2⟩
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

/--
Cost-indexed runtime-law instance for successful packed-integer scalar
projections.

As with the other projection families, the concrete reader changes only the
failure slot.  The source-facing allocation cost is zero and the exact heap
budget is therefore available unchanged to the continuation.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefinesWithCost_scalarProjection
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ScalarProjectionSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported _ budgeted sourceStep stateRelated valueCompiled valueAdapted
    resultFound
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
            budgeted.1.set?
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
            by simp [clearFailure], by simp [clearFailure], rfl,
            nextFrameAligned, by
              simpa [directLetAllocationCost, valueEq, clearFailure] using
                budgeted.2⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Cost-indexed runtime-law instance for integer boxing.

Production compilation and adaptation recover the scalar local and concrete
boxing import. `StateRelated` reconstructs the canonical `BoxedScalar` from
the source binding and its ABI lane. A fixed one-slot reservation then makes
all three representations constructive: immediate, promoted tag, or ordinary
heap box. The resulting source step is identified with the given interpreter
step by determinism, not by a supplied translation certificate.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefinesWithCost_box
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BoxSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported allocationFits budgeted sourceStep stateRelated valueCompiled
    valueAdapted resultFound
  rcases supported with
    ⟨scalarId, kind, valueEq, valueKind, scalarCompiled, annotationKind,
      resultCompiled⟩
  obtain ⟨sourceScalar, sourceLookup, _⟩ :=
    sourceLetResult_box_eq valueEq sourceStep
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet scalarId,
          .call (.runtime (.box kind.abiKind .tobject))] :=
    compileLetValue_box valueEq valueKind scalarCompiled annotationKind
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨indices, callIndex, scalarFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq
      (fvarIds := [scalarId])
      (operation := .box kind.abiKind .tobject) valueAdapted
  cases scalarFound with
  | cons scalarFound noMore =>
      cases noMore
      subst targetValue
      obtain ⟨alignedScalarIndex, alignedScalarFound, scalarKindAt⟩ :=
        spec.localsAligned scalarCompiled
      rw [scalarFound] at alignedScalarFound
      injection alignedScalarFound with scalarIndexEq
      subst alignedScalarIndex
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        spec.localsAligned resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      obtain ⟨physical, hScalar, physicalRelated⟩ :=
        stateRelated.resolve sourceLookup scalarFound scalarKindAt
      obtain ⟨scalar, kindEq, sourceScalarEq, physicalEq⟩ :=
        physicalRelated.boxedScalar_of_kind
      subst sourceScalar
      subst physical
      have boxFits :
          boxScalarAllocationBytes ≤ remainingBytes := by
        simpa [directLetAllocationCost, valueEq] using allocationFits
      obtain ⟨heap, word, boxed, remainingBudget⟩ :=
        stateRelated.1.heap.frontier.boxScalar_eq_ok_of_budget scalar
          budgeted.2 boxFits
      obtain ⟨updated, targetSet⟩ :=
        FirTalos.Correctness.locals_set?_exists
          (budgeted.1.validIndex resultFound)
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        spec.boxCall callFound
      obtain ⟨actualRuntime, actualValue, nextWitness, extension,
          nextRuntimeRelated, valueRelated, step⟩ :=
        letStepSimulates_box (context := context) kindEq valueEq sourceLookup
          stateRelated resultFound resultKindAt hScalar boxed imported
          spec.hostsSatisfy inBounds contracted params results targetSet
      obtain ⟨runtimeEq, sourceValueEq⟩ :=
        SourceLetResult.deterministic sourceStep step.1
      subst actualRuntime
      subst actualValue
      have lengths := FirTalos.Correctness.locals_lengths_of_set? targetSet
      have nextFrame :
          ConcreteLocalFrameAligned sourceFunction nextRuntime
            (bind sourceEnv decl.fvarId sourceValue)
            (replaceHeap targetStore heap) updated nextWitness :=
        ⟨lengths.1.trans budgeted.1.1, lengths.2.trans budgeted.1.2⟩
      have nextBudget :
          (replaceHeap targetStore heap).host.runtime.heap.AddressSpaceBudget
            (remainingBytes - boxScalarAllocationBytes) := by
        simpa [replaceHeap, clearFailure] using remainingBudget
      exact ⟨replaceHeap targetStore heap, updated, nextWitness, step,
        by simp [replaceHeap, clearFailure],
        by simp [replaceHeap, clearFailure], extension.closureDescriptors,
        nextFrame, by
          simpa [directLetAllocationCost, valueEq] using nextBudget⟩

/--
Cost-indexed runtime-law instance for successful typed unboxing.

The source step and source-only kind-compatibility premise determine the
semantic scalar. Production lowering and adaptation determine the object
local and typed runtime call. `StateRelated` then reconstructs the concrete
word, frozen heap descriptor (when needed), checked read, and exact physical
result lane. The operation preserves the full heap budget.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefinesWithCost_unbox
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (UnboxSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported _ budgeted sourceStep stateRelated valueCompiled valueAdapted
    resultFound
  rcases supported with
    ⟨objectId, objectKind, kind, valueEq, resultTypeEq, valueKind,
      objectCompiled, objectRefines, resultCompiled, kindCompatible⟩
  obtain ⟨sourceObject, rfl, sourceLookup, unboxed⟩ :=
    sourceLetResult_unbox_eq valueEq resultTypeEq sourceStep
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.unbox kind.abiKind))] :=
    compileLetValue_unbox valueEq valueKind objectCompiled
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨indices, callIndex, objectFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq
      (fvarIds := [objectId])
      (operation := .unbox kind.abiKind) valueAdapted
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
          have compatible := kindCompatible sourceLookup unboxed
          obtain ⟨scalar, unboxObjectRelated, concreteRead, sourceValueEq⟩ :=
            FirTalos.Concrete.ConcreteRuntimeRel.unboxFacts_of_sourceCompatible
              stateRelated.1 objectRelated compatible unboxed
          subst sourceValue
          obtain ⟨updated, targetSet, nextFrameAligned⟩ :=
            budgeted.1.set?
              (nextRuntime := nextRuntime)
              (nextEnv := bind sourceEnv decl.fvarId scalar.semanticValue)
              (nextStore := clearFailure targetStore)
              (nextWitness := witness)
              (physical := physicalOfLane scalar.lane) resultFound
          obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
            spec.unboxCall callFound
          exact ⟨clearFailure targetStore, updated, witness,
            letStepSimulates_unbox valueEq resultTypeEq sourceLookup unboxed
              stateRelated resultFound resultKindAt hObject
              unboxObjectRelated concreteRead imported spec.hostsSatisfy
              inBounds contracted params results targetSet,
            by simp [clearFailure], by simp [clearFailure], rfl,
            nextFrameAligned, by
              simpa [directLetAllocationCost, valueEq, clearFailure] using
                budgeted.2⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Cost-indexed runtime-law instance for successful sharing observations.

Production lowering and adaptation determine the object local and concrete
host call. `StateRelated` supplies the physical object representation, while
the source result fixes the direct `UInt8` destination. The read-only helper
preserves the heap frontier, installed external implementation, and closure
descriptor tables.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefinesWithCost_isShared
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (IsSharedSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported _ budgeted sourceStep stateRelated valueCompiled valueAdapted
    resultFound
  rcases supported with
    ⟨objectId, objectKind, valueEq, valueKind, objectCompiled, objectRefines,
      resultCompiled⟩
  obtain ⟨sourceObject, shared, rfl, rfl, sourceLookup, evaluated⟩ :=
    sourceLetResult_isShared_eq valueEq sourceStep
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime .isShared)] :=
    compileLetValue_isShared valueEq valueKind objectCompiled
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨indices, callIndex, objectFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq
      (fvarIds := [objectId]) (operation := .isShared) valueAdapted
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
          obtain ⟨updated, targetSet, nextFrameAligned⟩ :=
            budgeted.1.set?
              (nextRuntime := nextRuntime)
              (nextEnv :=
                bind sourceEnv decl.fvarId (.scalar (.uint8 shared)))
              (nextStore := clearFailure targetStore)
              (nextWitness := witness)
              (physical := .i32 (UInt32.ofNat shared.toNat)) resultFound
          obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
            spec.isSharedCall callFound
          exact ⟨clearFailure targetStore, updated, witness,
            letStepSimulates_isShared valueEq sourceLookup evaluated
              stateRelated resultFound resultKindAt hObject objectRelated
              imported spec.hostsSatisfy inBounds contracted params results
              targetSet,
            by simp [clearFailure], by simp [clearFailure], rfl,
            nextFrameAligned, by
              simpa [directLetAllocationCost, valueEq, clearFailure] using
                budgeted.2⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Cost-indexed runtime-law instance for successful ownership reset.

Production lowering and adaptation determine the object local and
count-indexed reset call. The successful source step and `StateRelated`
determine the concrete object representation; `resetStep_of_refines` then
derives the tagged, persistent/nonunique, or unique-constructor branch
internally. Reset preserves the heap frontier exactly, so its source cost is
zero even when recursively releasing captured fields.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefinesWithCost_reset
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
    (externals : ExternalImpl)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (ResetSupported context)
      directLetAllocationCost
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction
        externals) := by
  intro sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported _ budgeted sourceStep stateRelated valueCompiled valueAdapted
    resultFound
  rcases supported with
    ⟨count, objectId, objectKind, valueEq, valueKind, objectCompiled,
      objectRefines, resultCompiled⟩
  obtain ⟨sourceObject, sourceLookup, semanticReset⟩ :=
    sourceLetResult_reset_eq valueEq sourceStep
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.reset count))] :=
    compileLetValue_reset valueEq valueKind objectCompiled
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨indices, callIndex, objectFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq
      (fvarIds := [objectId]) (operation := .reset count) valueAdapted
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
          obtain ⟨heap, nextWitness, token, operation, transport, nextRelated,
              tokenRelated, witnessDescriptorsPreserved, capacity, cursor⟩ :=
            resetStep_of_refines stateRelated.1 budgeted.2.symm objectRelated
              semanticReset
          obtain ⟨updatedLocals, targetSet, nextFrameAligned⟩ :=
            budgeted.1.1.1.set?
              (nextRuntime := nextRuntime)
              (nextEnv := bind sourceEnv decl.fvarId sourceValue)
              (nextStore := replaceHeap targetStore heap)
              (nextWitness := nextWitness)
              (physical := .i32 (UInt32.ofNat token.value)) resultFound
          obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
            spec.resetCall callFound
          have nextBudget : heap.AddressSpaceBudget remainingBytes := by
            exact {
              cursorPositive := by
                simpa [cursor] using budgeted.1.1.2.cursorPositive
              endWithinAddressSpace := by
                simpa [cursor] using
                  budgeted.1.1.2.endWithinAddressSpace }
          refine ⟨replaceHeap targetStore heap, updatedLocals, nextWitness,
            letStepSimulates_reset valueEq sourceLookup semanticReset
              stateRelated transport nextRelated
              (by simp [replaceHeap, clearFailure])
              resultFound resultKindAt hObject tokenRelated imported
              spec.hostsSatisfy inBounds contracted params results operation
              targetSet,
            ?_, ?_, witnessDescriptorsPreserved, ?_⟩
          · simp [replaceHeap, clearFailure]
          · simp [replaceHeap, clearFailure]
          · refine ⟨?_, ?_⟩
            · refine ⟨⟨nextFrameAligned, ?_⟩, ?_, ?_, ?_⟩
              · change heap.AddressSpaceBudget
                  (remainingBytes - directLetAllocationCost decl)
                simpa [directLetAllocationCost, valueEq] using nextBudget
              · change
                  targetStore.host.externals.IntegerResultRefines externals
                exact budgeted.1.2.1
              · change
                  FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
                    targetStore.host.externals externals
                exact budgeted.1.2.2.1
              · change
                  FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
                    targetStore.host.externals externals
                exact budgeted.1.2.2.2
            · simpa [replaceHeap, clearFailure,
                witnessDescriptorsPreserved] using budgeted.2
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/--
Certificate-free compiler composition for one successful capacity-validated
reuse declaration.

Production compilation/adaptation derives the token local, mixed
local/erased field prefix, runtime import, and result local. Static capacity
evidence plus its dynamic state relation derives zero versus retained
execution; a representation-sensitive source budget constructs the fresh
branch. `ReuseTokenOrdinaryRel` is consumed as threaded source state and
re-established after the successful reuse; the shared validator gap tracked
by `FIR-BUG-wasm-none-reuse-retained-token-ordinary` is now confined to
intervening operations that may make a retained-token alias persistent.
-/
theorem ConcreteSupportedExport.reuseLetStep_of_capacity
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
    {facts : ReuseCapacityFacts}
    {labels : List FVarId}
    {decl : LCNF.LetDecl .impure}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {resultIndex remainingBytes : Nat}
    {witness : RefinementWitness}
    (supported : ReuseSupported context facts decl)
    (allocationFits :
      directLetAllocationCost decl ≤ remainingBytes)
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (ordinaryTokens :
      ReuseTokenOrdinaryRel facts sourceRuntime sourceEnv)
    (budget :
      targetStore.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (localFrame :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex) :
    ∃ nextStore nextLocals nextWitness nextFacts,
      LetStepSimulates context sourceFunction target.wasmModule hosts.env decl
        targetValue sourceRuntime nextRuntime sourceEnv sourceValue targetStore
        nextStore targetLocals nextLocals resultIndex witness nextWitness ∧
      nextStore.host.externals = targetStore.host.externals ∧
      nextStore.host.closureDescriptors =
        targetStore.host.closureDescriptors ∧
      nextWitness.closureDescriptors = witness.closureDescriptors ∧
      reuseCapacityLetFacts? facts decl = some nextFacts ∧
      ReuseCapacityStateRelated nextFacts sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness ∧
      ReuseTokenOrdinaryRel nextFacts nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) ∧
      ConcreteLocalFrameAligned sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness ∧
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - directLetAllocationCost decl) := by
  rcases supported with
    ⟨tokenId, info, updateHeader, args, argumentCode, fieldKinds, resultKind,
      evidence, valueEq, tagFits, valueKind, tokenCompiled, argumentsCompiled,
      resultCompiled, operationWellFormed, capacityFitting, resultCompatible,
      objectFieldsFit, usizeFieldsFit, scalarBytesFit⟩
  obtain ⟨sourceToken, semanticFields, tokenLookup, argumentsEvaluated,
      semanticReuse⟩ :=
    sourceLetResult_reuse_eq valueEq sourceStep
  have operationFacts :
      (info.size = fieldKinds.size ∧
        fieldKinds.all AbiKind.isObjectField = true) ∧
        (constructorKind info).refines resultKind = true := by
    simpa [RuntimeOp.abiWellFormed] using operationWellFormed
  have tagFits' : info.cidx < UInt32.size := by
    simpa [Fir.Wasm.constructorTagFitsI32] using tagFits
  have freshCostFits :
      constructorAllocationBytes info ≤ remainingBytes := by
    simpa [directLetAllocationCost, valueEq] using allocationFits
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (.localGet tokenId :: argumentCode ++
          [.call
            (.runtime
              (.reuse info updateHeader fieldKinds resultKind))]) :=
    compileLetValue_reuse valueEq valueKind tokenCompiled argumentsCompiled
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_call_eq valueAdapted
  subst targetValue
  obtain ⟨targetToken, targetFields, tokenAdapted, fieldsAdapted,
      targetArgumentsEq⟩ :=
    instructions_cons_eq_ok argumentsAdapted
  obtain ⟨tokenIndex, tokenFound, tokenKindAt⟩ :=
    spec.localsAligned tokenCompiled
  have targetTokenEq : targetToken = .localGet tokenIndex := by
    have tokenFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            tokenId =
          some tokenIndex := by
      simpa [functionBindings] using tokenFound
    have adaptedEq :
        (Except.ok (.localGet tokenIndex) :
          Except AdapterError Wasm.Instruction) =
            Except.ok targetToken := by
      simpa [instruction, tokenFound', pure, Except.pure]
        using tokenAdapted
    exact (Except.ok.inj adaptedEq).symm
  obtain ⟨physicalFields, fieldsReady, physicalArity, argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      fieldsAdapted argumentsEvaluated related.stateRelated
  obtain ⟨tokenLane, tokenPhysicalFound, tokenCapacity⟩ :=
    related.resolveFittingToken capacityFitting tokenLookup tokenFound
      tokenKindAt
  obtain ⟨tokenWord, tokenLaneEq⟩ := tokenCapacity.reuseTokenWord
  subst tokenLane
  obtain ⟨fields, fieldsDecoded, fieldsLength, fieldsRelated⟩ :=
    argumentsRelated.decodeObjectWords
      (by simpa using operationFacts.1.2) 1
  have fieldsArity : fields.toArray.size = info.size := by
    have fieldKindLength : fieldKinds.toList.length = info.size := by
      simpa using operationFacts.1.1.symm
    simpa using fieldsLength.trans fieldKindLength
  have semanticArity : semanticFields.size = info.size := by
    have fieldKindLength : fieldKinds.toList.length = info.size := by
      simpa using operationFacts.1.1.symm
    simpa using argumentsRelated.semanticLength.trans fieldKindLength
  have fieldRelated :
      ∀ (index : Nat) (kind : AbiKind) (value : Value),
        fieldKinds[index]? = some kind →
        semanticFields[index]? = some value →
        ∃ field, fields.toArray[index]? = some field ∧
          ValueRel witness kind (.word32 field) value := by
    intro index kind value kindAt valueAt
    obtain ⟨field, fieldAt, relatedField⟩ :=
      fieldsRelated index kind value (by simpa using kindAt)
        (by simpa using valueAt)
    exact ⟨field, by simpa using fieldAt, relatedField⟩
  have argsLength :
      (.i32 (UInt32.ofNat tokenWord.value) :: physicalFields).length =
        fieldKinds.size + 1 := by
    simp [physicalArity]
  have decoded :
      decodeReuseWords
          (.i32 (UInt32.ofNat tokenWord.value) :: physicalFields) =
        .ok (tokenWord, fields) := by
    simp [decodeReuseWords, fieldsDecoded,
      Word32.ofUInt32_ofNat_value]
  have fullReady :
      ConstructorArgsReady targetLocals
        (.localGet tokenIndex :: targetFields)
        (.i32 (UInt32.ofNat tokenWord.value) :: physicalFields) := by
    apply ConstructorArgsReady.localGet
    · simpa [physicalOfLane] using tokenPhysicalFound
    · exact fieldsReady
  have freshAllocated :
      sourceToken = .reuseToken none →
        ∃ heap word,
          reuseObject targetStore.host.runtime.heap Word32.zero info
              updateHeader fields.toArray =
            .ok (heap, word) ∧
          heap.AddressSpaceBudget
            (remainingBytes - constructorAllocationBytes info) := by
    intro _
    obtain ⟨heap, word, allocated, remainingBudget⟩ :=
      FirTalos.Concrete.MemoryState.FrontierInvariant.reuseObject_zero_eq_ok_of_budget
        related.stateRelated.1.heap.frontier info updateHeader fields.toArray
        fieldsArity tagFits' objectFieldsFit usizeFieldsFit scalarBytesFit
        budget freshCostFits
    exact ⟨heap, word, allocated, remainingBudget⟩
  have tokenOrdinary :
      ∀ (location : Location) (cell : HeapCell),
        sourceToken = .reuseToken (some location) →
        findCell? sourceRuntime.heap location = some cell →
        cell.persistent = false := by
    intro location cell tokenEq found
    cases evidence with
    | emptyToken =>
        have tokenNone := tokenCapacity.emptyToken_eq
        rw [tokenEq] at tokenNone
        cases tokenNone.2
    | retainedAtLeast available =>
        have tracked :=
          (findFittingReuseCapacityEvidence?_eq_some facts tokenId info
            (.retainedAtLeast available) capacityFitting).1
        have tokenLookup' :
            lookup sourceEnv tokenId =
              some (.reuseToken (some location)) := by
          simpa [tokenEq] using tokenLookup
        exact ordinaryTokens tokenId available location cell tracked
          tokenLookup' found
  obtain ⟨heap, word, nextWitness, operation, transport, nextRuntimeRelated,
      valueRelated, capacityValue, witnessDescriptorsPreserved,
      capacityTransport, remainingBudget⟩ :=
    reuseStep_of_capacityEvidence related.stateRelated.1 argsLength decoded
      tokenCapacity capacityFitting fieldsArity semanticArity
      operationFacts.1.1.symm operationFacts.1.2 fieldRelated tagFits'
      objectFieldsFit usizeFieldsFit scalarBytesFit operationFacts.2
      resultCompatible budget freshAllocated tokenOrdinary semanticReuse
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    spec.localsAligned resultCompiled
  rw [resultFound] at alignedResultFound
  injection alignedResultFound with resultIndexEq
  subst alignedResultIndex
  obtain ⟨updated, targetSet, nextFrameAligned⟩ :=
    localFrame.set?
      (nextRuntime := nextRuntime)
      (nextEnv := bind sourceEnv decl.fvarId sourceValue)
      (nextStore := replaceHeap targetStore heap)
      (nextWitness := nextWitness)
      (physical := .i32 (UInt32.ofNat word.value)) resultFound
  obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
    spec.reuseCall callFound
  have physicalParams :
      imp.params.length =
        (.i32 (UInt32.ofNat tokenWord.value) :: physicalFields).length :=
    params.trans argsLength.symm
  subst targetToken
  subst targetArguments
  have step :=
    letStepSimulates_reuseArgs (context := context) valueEq tokenLookup
      argumentsEvaluated semanticReuse related.stateRelated transport
      nextRuntimeRelated (by simp [replaceHeap, clearFailure]) resultFound
      resultKindAt fullReady valueRelated imported spec.hostsSatisfy inBounds
      contracted physicalParams results operation targetSet
  let nextFacts :=
    insertReuseCapacityFact facts decl.fvarId (evidence.afterReuse info)
  have transfer : reuseCapacityLetFacts? facts decl = some nextFacts := by
    simp [reuseCapacityLetFacts?, valueEq, capacityFitting, nextFacts]
  have nextCapacity :
      ReuseCapacityStateRelated nextFacts sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue)
        (replaceHeap targetStore heap) updated nextWitness := by
    exact related.ofReuseLetStep step resultFound resultKindAt targetSet
      transport capacityTransport capacityValue
  have nextOrdinary :
      ReuseTokenOrdinaryRel nextFacts nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) := by
    simpa [nextFacts] using
      ordinaryTokens.bindReuse
        (nextEvidence := evidence.afterReuse info) semanticReuse
  exact ⟨replaceHeap targetStore heap, updated, nextWitness, nextFacts, step,
    by simp [replaceHeap, clearFailure],
    by simp [replaceHeap, clearFailure], witnessDescriptorsPreserved,
    transfer, nextCapacity, nextOrdinary, nextFrameAligned, by
      change heap.AddressSpaceBudget
        (remainingBytes - directLetAllocationCost decl)
      simpa [directLetAllocationCost, valueEq] using remainingBudget⟩

/--
Current mixed allocating structural fragment: local aliases, immediate
integer/`USize` literals, representation-polymorphic natural literals,
successful object/`USize`/packed-scalar projections, integer boxing, typed
unboxing and sharing observations, UTF-8 String literals, and nonempty
constructors.
-/
def BudgetedDirectSupported (context : Fir.Wasm.Context)
    (decl : LCNF.LetDecl .impure) : Prop :=
  LocalAliasSupported context decl ∨
    ImmediateLiteralSupported context decl ∨
      NaturalLiteralSupported context decl ∨
        USizeProjectionSupported context decl ∨
          ObjectProjectionSupported context decl ∨
            ScalarProjectionSupported context decl ∨
              BoxSupported context decl ∨
                UnboxSupported context decl ∨
                  IsSharedSupported context decl ∨
                    StringLiteralSupported context decl ∨
                      NonemptyConstructorSupported context decl

/--
The complete direct family available under the ownership descriptor
agreement: the ordinary budgeted structural fragment plus successful reset.

Reset is separated from `BudgetedDirectSupported` because recursively
releasing closure captures requires the descriptor agreement carried by the
ownership frame. This distinction is an invariant requirement, not a
per-program certificate.
-/
def OwnershipBudgetedDirectSupported (context : Fir.Wasm.Context)
    (decl : LCNF.LetDecl .impure) : Prop :=
  BudgetedDirectSupported context decl ∨ ResetSupported context decl

/--
The cost-indexed runtime law composes natural/String/constructor allocation
with cost-zero aliases, fixed-width immediates, and successful projections.
One source-path budget is preserved across nonallocating nodes and consumed
exactly at allocating nodes.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_budgetedDirect
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
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (ConcreteBudgetedLocalFrame sourceFunction) := by
  change
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env
        (fun decl =>
          LocalAliasSupported context decl ∨
            (ImmediateLiteralSupported context decl ∨
              (NaturalLiteralSupported context decl ∨
                (USizeProjectionSupported context decl ∨
                  (ObjectProjectionSupported context decl ∨
                    (ScalarProjectionSupported context decl ∨
                      (BoxSupported context decl ∨
                        (UnboxSupported context decl ∨
                          (IsSharedSupported context decl ∨
                            (StringLiteralSupported context decl ∨
                              NonemptyConstructorSupported context decl))))))))))
      directLetAllocationCost (ConcreteBudgetedLocalFrame sourceFunction)
  apply DirectLetRuntimeRefinesWithCost.or
  · exact directLetRuntimeRefinesWithCost_localAlias spec.localsAligned
  · apply DirectLetRuntimeRefinesWithCost.or
    · exact spec.directLetRuntimeRefinesWithCost_immediateLiteral
    · apply DirectLetRuntimeRefinesWithCost.or
      · exact spec.directLetRuntimeRefines_naturalLiteral
      · apply DirectLetRuntimeRefinesWithCost.or
        · exact spec.directLetRuntimeRefinesWithCost_usizeProjection
        · apply DirectLetRuntimeRefinesWithCost.or
          · exact spec.directLetRuntimeRefinesWithCost_objectProjection
          · apply DirectLetRuntimeRefinesWithCost.or
            · exact spec.directLetRuntimeRefinesWithCost_scalarProjection
            · apply DirectLetRuntimeRefinesWithCost.or
              · exact spec.directLetRuntimeRefinesWithCost_box
              · apply DirectLetRuntimeRefinesWithCost.or
                · exact spec.directLetRuntimeRefinesWithCost_unbox
                · apply DirectLetRuntimeRefinesWithCost.or
                  · exact spec.directLetRuntimeRefinesWithCost_isShared
                  · apply DirectLetRuntimeRefinesWithCost.or
                    · exact spec.directLetRuntimeRefines_stringLiteral
                    · exact spec.directLetRuntimeRefines_nonemptyConstructor

/--
The complete current direct family preserves the frame used by pure integer
external calls. Thus aliases, literals, projections, constructors, and
integer construction/arithmetic calls may share one budgeted structural
induction.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_budgetedDirect_integerExternal
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
    (externals : ExternalImpl)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (ConcreteBudgetedIntegerExternalFrame sourceFunction externals) := by
  change
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        ConcreteBudgetedLocalFrame sourceFunction remainingBytes sourceRuntime
            sourceEnv targetStore targetLocals witness ∧
          targetStore.host.externals.IntegerResultRefines externals)
  exact
    DirectLetRuntimeRefinesWithCost.preservingExternalInvariant
      (ExternalInvariant :=
        fun concrete => concrete.IntegerResultRefines externals)
      spec.directLetRuntimeRefines_budgetedDirect

/--
The complete direct family preserves the frame and installed implementation
law used by pure natural-result external calls.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_budgetedDirect_naturalExternal
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
    (externals : ExternalImpl)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (ConcreteBudgetedNaturalExternalFrame sourceFunction externals) := by
  change
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        ConcreteBudgetedLocalFrame sourceFunction remainingBytes sourceRuntime
            sourceEnv targetStore targetLocals witness ∧
          FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
            targetStore.host.externals externals)
  exact
    DirectLetRuntimeRefinesWithCost.preservingExternalInvariant
      (ExternalInvariant :=
        fun concrete =>
          FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
            concrete externals)
      spec.directLetRuntimeRefines_budgetedDirect

/--
The complete direct family preserves the installed nonallocating scalar-result
implementation law.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_budgetedDirect_scalarExternal
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
    (externals : ExternalImpl)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (ConcreteBudgetedScalarExternalFrame sourceFunction externals) := by
  change
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        ConcreteBudgetedLocalFrame sourceFunction remainingBytes sourceRuntime
            sourceEnv targetStore targetLocals witness ∧
          FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
            targetStore.host.externals externals)
  exact
    DirectLetRuntimeRefinesWithCost.preservingExternalInvariant
      (ExternalInvariant :=
        fun concrete =>
          FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
            concrete externals)
      spec.directLetRuntimeRefines_budgetedDirect

/--
All current direct helpers preserve the three installed pure-external family
laws simultaneously.
-/
theorem ConcreteSupportedExport.directLetRuntimeRefines_budgetedDirect_pureExternal
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
    (externals : ExternalImpl)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (ConcreteBudgetedPureExternalFrame sourceFunction externals) := by
  change
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        ConcreteBudgetedLocalFrame sourceFunction remainingBytes sourceRuntime
            sourceEnv targetStore targetLocals witness ∧
          (targetStore.host.externals.IntegerResultRefines externals ∧
            FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
              targetStore.host.externals externals ∧
            FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
              targetStore.host.externals externals))
  exact
    DirectLetRuntimeRefinesWithCost.preservingExternalInvariant
      (ExternalInvariant := fun concrete =>
        concrete.IntegerResultRefines externals ∧
          FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
            concrete externals ∧
          FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
            concrete externals)
      spec.directLetRuntimeRefines_budgetedDirect

/--
Integer-, natural-, and scalar-result external calls share one invariant and
compose by source admission disjunction.
-/
theorem ConcreteSupportedExport.externalLetRuntimeRefinesWithCost_pureExternal
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
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureExternalSupported context externals)
      (ConcreteBudgetedPureExternalFrame sourceFunction externals) := by
  have integerLaw :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals
        (PureIntegerExternalSupported context externals)
        (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness =>
          ConcreteBudgetedIntegerExternalFrame sourceFunction externals
              remainingBytes sourceRuntime sourceEnv targetStore targetLocals
              witness ∧
            (FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
                targetStore.host.externals externals ∧
              FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
                targetStore.host.externals externals)) :=
    ExternalLetRuntimeRefinesWithCost.preservingExternalInvariant
      (ExternalInvariant := fun concrete =>
        FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
            concrete externals ∧
          FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
            concrete externals)
      (spec.externalLetRuntimeRefinesWithCost_pureInteger externals)
  have naturalLaw :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals
        (PureNaturalExternalSupported context externals)
        (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness =>
          ConcreteBudgetedNaturalExternalFrame sourceFunction externals
              remainingBytes sourceRuntime sourceEnv targetStore targetLocals
              witness ∧
            (targetStore.host.externals.IntegerResultRefines externals ∧
              FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
                targetStore.host.externals externals)) :=
    ExternalLetRuntimeRefinesWithCost.preservingExternalInvariant
      (ExternalInvariant := fun concrete =>
        concrete.IntegerResultRefines externals ∧
          FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
            concrete externals)
      (spec.externalLetRuntimeRefinesWithCost_pureNatural externals)
  have scalarLaw :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals
        (PureScalarExternalSupported context externals)
        (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness =>
          ConcreteBudgetedScalarExternalFrame sourceFunction externals
              remainingBytes sourceRuntime sourceEnv targetStore targetLocals
              witness ∧
            (targetStore.host.externals.IntegerResultRefines externals ∧
              FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
                targetStore.host.externals externals)) :=
    ExternalLetRuntimeRefinesWithCost.preservingExternalInvariant
      (ExternalInvariant := fun concrete =>
        concrete.IntegerResultRefines externals ∧
          FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
            concrete externals)
      (spec.externalLetRuntimeRefinesWithCost_pureScalar externals)
  have integerLaw' :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals
        (PureIntegerExternalSupported context externals)
        (ConcreteBudgetedPureExternalFrame sourceFunction externals) := by
    apply ExternalLetRuntimeRefinesWithCost.mapInvariant integerLaw
    · intro _ _ _ _ _ _ invariant
      exact ⟨⟨invariant.1, invariant.2.1⟩,
        invariant.2.2.1, invariant.2.2.2⟩
    · intro _ _ _ _ _ _ invariant
      exact ⟨invariant.1.1, invariant.1.2,
        invariant.2.1, invariant.2.2⟩
  have naturalLaw' :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals
        (PureNaturalExternalSupported context externals)
        (ConcreteBudgetedPureExternalFrame sourceFunction externals) := by
    apply ExternalLetRuntimeRefinesWithCost.mapInvariant naturalLaw
    · intro _ _ _ _ _ _ invariant
      exact ⟨⟨invariant.1, invariant.2.2.1⟩,
        invariant.2.1, invariant.2.2.2⟩
    · intro _ _ _ _ _ _ invariant
      exact ⟨invariant.1.1, invariant.2.1,
        invariant.1.2, invariant.2.2⟩
  have scalarLaw' :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals
        (PureScalarExternalSupported context externals)
        (ConcreteBudgetedPureExternalFrame sourceFunction externals) := by
    apply ExternalLetRuntimeRefinesWithCost.mapInvariant scalarLaw
    · intro _ _ _ _ _ _ invariant
      exact ⟨⟨invariant.1, invariant.2.2.2⟩,
        invariant.2.1, invariant.2.2.1⟩
    · intro _ _ _ _ _ _ invariant
      exact ⟨invariant.1.1, invariant.2.1,
        invariant.2.2, invariant.1.2⟩
  have naturalScalarLaw :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals
        (fun sourceRuntime sourceEnv decl continuation nextRuntime sourceValue
            stepCost =>
          PureNaturalExternalSupported context externals sourceRuntime sourceEnv
              decl continuation nextRuntime sourceValue stepCost ∨
            PureScalarExternalSupported context externals sourceRuntime sourceEnv
              decl continuation nextRuntime sourceValue stepCost)
        (ConcreteBudgetedPureExternalFrame sourceFunction externals) :=
    ExternalLetRuntimeRefinesWithCost.or naturalLaw' scalarLaw'
  have combinedLaw :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals
        (fun sourceRuntime sourceEnv decl continuation nextRuntime sourceValue
            stepCost =>
          PureIntegerExternalSupported context externals sourceRuntime sourceEnv
              decl continuation nextRuntime sourceValue stepCost ∨
            (PureNaturalExternalSupported context externals sourceRuntime
                sourceEnv decl continuation nextRuntime sourceValue stepCost ∨
              PureScalarExternalSupported context externals sourceRuntime
                sourceEnv decl continuation nextRuntime sourceValue stepCost))
        (ConcreteBudgetedPureExternalFrame sourceFunction externals) :=
    ExternalLetRuntimeRefinesWithCost.or
      (Left := PureIntegerExternalSupported context externals)
      (Right := fun sourceRuntime sourceEnv decl continuation nextRuntime
          sourceValue stepCost =>
        PureNaturalExternalSupported context externals sourceRuntime sourceEnv
            decl continuation nextRuntime sourceValue stepCost ∨
          PureScalarExternalSupported context externals sourceRuntime sourceEnv
            decl continuation nextRuntime sourceValue stepCost)
      integerLaw' naturalScalarLaw
  change
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (fun sourceRuntime sourceEnv decl continuation nextRuntime sourceValue
          stepCost =>
        PureIntegerExternalSupported context externals sourceRuntime sourceEnv
            decl continuation nextRuntime sourceValue stepCost ∨
          (PureNaturalExternalSupported context externals sourceRuntime
              sourceEnv decl continuation nextRuntime sourceValue stepCost ∨
            PureScalarExternalSupported context externals sourceRuntime
              sourceEnv decl continuation nextRuntime sourceValue stepCost))
      (ConcreteBudgetedPureExternalFrame sourceFunction externals)
  exact combinedLaw

/--
All current direct helpers preserve the ownership descriptor agreement in
addition to the complete pure-external frame.
-/
theorem
    ConcreteSupportedExport.directLetRuntimeRefines_budgetedDirect_ownership
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
    (externals : ExternalImpl)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  change
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (BudgetedDirectSupported context)
      directLetAllocationCost
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness ∧
          targetStore.host.closureDescriptors = witness.closureDescriptors)
  exact
    DirectLetRuntimeRefinesWithCost.preservingClosureDescriptorAgreement
      (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)

/--
The ownership-strengthened direct family composes the ordinary structural
fragment with branch-independent reset correctness.
-/
theorem
    ConcreteSupportedExport.directLetRuntimeRefines_ownershipBudgetedDirect
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
    (externals : ExternalImpl)
    {labels : List FVarId} :
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env (OwnershipBudgetedDirectSupported context)
      directLetAllocationCost
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  change
    DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (fun decl =>
        BudgetedDirectSupported context decl ∨ ResetSupported context decl)
      directLetAllocationCost
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals)
  exact DirectLetRuntimeRefinesWithCost.or
    (spec.directLetRuntimeRefines_budgetedDirect_ownership externals)
    (spec.directLetRuntimeRefinesWithCost_reset externals)

/--
Pure integer, natural, and scalar external calls likewise preserve the
ownership descriptor agreement while extending their ordinary heap witness.
-/
theorem
    ConcreteSupportedExport.externalLetRuntimeRefinesWithCost_ownership
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
    (externals : ExternalImpl) :
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureExternalSupported context externals)
      (ConcreteBudgetedPureExternalOwnershipFrame sourceFunction externals) := by
  change
    ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
      target.wasmModule hosts.env externals
      (PureExternalSupported context externals)
      (fun remainingBytes sourceRuntime sourceEnv targetStore targetLocals
          witness =>
        ConcreteBudgetedPureExternalFrame sourceFunction externals
            remainingBytes sourceRuntime sourceEnv targetStore targetLocals
            witness ∧
          targetStore.host.closureDescriptors = witness.closureDescriptors)
  exact
    ExternalLetRuntimeRefinesWithCost.preservingClosureDescriptorAgreement
      (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)

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
Cost-indexed structural partial correctness for the direct-value code spine.

The initial invariant is required at the source-computed
`DirectValuePathCost`. At every `let`, the runtime law consumes the head
declaration's cost and the induction hypothesis receives exactly the
continuation cost. This supports finite wasm32 allocation without adding a
translation certificate or a target-derived resource witness.
-/
theorem codeWP_of_directValueEvaluates_withCost
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
    {letCost : LCNF.LetDecl .impure → Nat}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (evaluation :
      DirectValueEvaluates context Supported sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels sourceCode target)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (invariant :
      Invariant (DirectValuePathCost letCost sourceCode) sourceRuntime sourceEnv
        initial locals witness)
    (runtimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
        module hostEnv Supported letCost Invariant)
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
  | @letValue decl letSourceRuntime letSourceEnv letNextRuntime letSourceValue
      continuation _ _ supported sourceStep continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels
            _ targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          letCost decl ≤
            DirectValuePathCost letCost (.let decl continuation) := by
        simp [DirectValuePathCost]
      obtain ⟨nextStore, nextLocals, nextWitness, step, _externalsPreserved,
          _hostDescriptorsPreserved, _witnessDescriptorsPreserved,
          nextInvariant⟩ :=
        runtimeRefines supported stepFits invariant sourceStep stateRelated
          valueCompiled valueAdapted resultFound
      have continuationInvariant :
          Invariant (DirectValuePathCost letCost continuation)
            letNextRuntime (bind letSourceEnv decl.fvarId letSourceValue)
            nextStore nextLocals nextWitness := by
        simpa [DirectValuePathCost] using nextInvariant
      obtain ⟨resultStore, resultWitness, resultKind, physical,
          continuationWP, resultRuntimeRelated, failureClear,
          valueRelated⟩ :=
        ih continuationAdapted step.2.2.1 continuationInvariant
      subst target
      exact ⟨resultStore, resultWitness, resultKind, physical,
        codeWP_letValue valueCompiled valueAdapted resultFound step
          continuationWP,
        resultRuntimeRelated, failureClear, valueRelated⟩

/--
Cost-indexed structural partial correctness for mixed direct and external
`let` spines.

The source evaluation supplies the exact external-call protocol and a
source-facing allocation-cost index for each foreign result. The two uniform
runtime laws discharge whole operation families. Compiler code, adapted
instructions, local/import indices, concrete responses, and continuation
splits are all reconstructed inside this induction.
-/
theorem codeWP_of_budgetedSpineEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {requiredBytes : Nat}
    {targetFunction : Wasm.Function}
    {parameters callerTail : List Wasm.Value}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {directCost : LCNF.LetDecl .impure → Nat}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (evaluation :
      BudgetedSpineEvaluates context externals DirectSupported
        ExternalSupported directCost sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue requiredBytes)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels sourceCode target)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (invariant :
      Invariant requiredBytes sourceRuntime sourceEnv initial locals witness)
    (directRuntimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
        module hostEnv DirectSupported directCost Invariant)
    (externalRuntimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction
        labels module hostEnv externals ExternalSupported Invariant)
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
  | @letValue decl letSourceRuntime letSourceEnv letNextRuntime letSourceValue
      continuation _ _ continuationCost supported sourceStep continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels
            _ targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          directCost decl ≤ directCost decl + continuationCost :=
        Nat.le_add_right _ _
      obtain ⟨nextStore, nextLocals, nextWitness, step, _externalsPreserved,
          _hostDescriptorsPreserved, _witnessDescriptorsPreserved,
          nextInvariant⟩ :=
        directRuntimeRefines supported stepFits invariant sourceStep stateRelated
          valueCompiled valueAdapted resultFound
      have continuationInvariant :
          Invariant continuationCost letNextRuntime
            (bind letSourceEnv decl.fvarId letSourceValue)
            nextStore nextLocals nextWitness := by
        simpa using nextInvariant
      obtain ⟨resultStore, resultWitness, resultKind, physical,
          continuationWP, resultRuntimeRelated, failureClear,
          valueRelated⟩ :=
        ih continuationAdapted step.2.2.1 continuationInvariant
      subst target
      exact ⟨resultStore, resultWitness, resultKind, physical,
        codeWP_letValue valueCompiled valueAdapted resultFound step
          continuationWP,
        resultRuntimeRelated, failureClear, valueRelated⟩
  | @externalLet externalSourceRuntime externalSourceEnv decl continuation
      externalNextRuntime externalSourceValue stepCost _ _ continuationCost
      supported sourceStep continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels
            _ targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits : stepCost ≤ stepCost + continuationCost :=
        Nat.le_add_right _ _
      obtain ⟨nextStore, nextLocals, nextWitness, step, _externalsPreserved,
          _hostDescriptorsPreserved, _witnessDescriptorsPreserved,
          nextInvariant⟩ :=
        externalRuntimeRefines supported stepFits invariant sourceStep
          stateRelated valueCompiled valueAdapted resultFound
      have continuationInvariant :
          Invariant continuationCost externalNextRuntime
            (bind externalSourceEnv decl.fvarId externalSourceValue)
            nextStore nextLocals nextWitness := by
        simpa using nextInvariant
      obtain ⟨resultStore, resultWitness, resultKind, physical,
          continuationWP, resultRuntimeRelated, failureClear,
          valueRelated⟩ :=
        ih continuationAdapted step.2.2.1 continuationInvariant
      subst target
      exact ⟨resultStore, resultWitness, resultKind, physical,
        codeWP_externalLet valueCompiled valueAdapted resultFound step
          continuationWP,
        resultRuntimeRelated, failureClear, valueRelated⟩

/--
Cost-indexed structural partial correctness for mixed direct/external code
with selected case branches and no-result effects, retaining the exact
explicit Wasm return.

The return-only postcondition is the natural compositional boundary for
generated case arms: it is unchanged by the arm-resumption wrapper. The public
body theorem below weakens this exact control result to
`ConcreteFunctionBodyPost` only after the syntax induction is complete.
-/
theorem codeWP_of_budgetedCodeEvaluates_exactReturn
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {requiredBytes : Nat}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop}
    {EffectSupported : EffectSupportedPredicate}
    {directCost : LCNF.LetDecl .impure → Nat}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (evaluation :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue
        requiredBytes)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels sourceCode target)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (invariant :
      Invariant requiredBytes sourceRuntime sourceEnv initial locals witness)
    (directRuntimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
        module hostEnv DirectSupported directCost Invariant)
    (externalRuntimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction
        labels module hostEnv externals ExternalSupported Invariant)
    (caseRuntimeRefines :
      CaseRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv CaseSupported)
    (effectRuntimeRefines :
      EffectRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv EffectSupported Invariant) :
    ∃ resultStore resultWitness resultKind physical,
      CodeWP context sourceModule sourceFunction labels module hostEnv
          sourceRuntime sourceEnv sourceCode target initial locals witness []
          (ExactReturnControlPost resultStore physical) ∧
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
        codeWP_return_to_exactControlPost localCompiled resultFound kindAt
          sourceLookup stateRelated targetLookup,
        stateRelated.1, stateRelated.2.1, valueRelated⟩
  | @letValue decl letSourceRuntime letSourceEnv letNextRuntime letSourceValue
      continuation _ _ continuationCost supported sourceStep continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels
            _ targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          directCost decl ≤ directCost decl + continuationCost :=
        Nat.le_add_right _ _
      obtain ⟨nextStore, nextLocals, nextWitness, step, _externalsPreserved,
          _hostDescriptorsPreserved, _witnessDescriptorsPreserved,
          nextInvariant⟩ :=
        directRuntimeRefines supported stepFits invariant sourceStep stateRelated
          valueCompiled valueAdapted resultFound
      have continuationInvariant :
          Invariant continuationCost letNextRuntime
            (bind letSourceEnv decl.fvarId letSourceValue)
            nextStore nextLocals nextWitness := by
        simpa using nextInvariant
      obtain ⟨resultStore, resultWitness, resultKind, physical,
          continuationWP, resultRuntimeRelated, failureClear,
          valueRelated⟩ :=
        ih continuationAdapted step.2.2.1 continuationInvariant
      subst target
      exact ⟨resultStore, resultWitness, resultKind, physical,
        codeWP_letValue valueCompiled valueAdapted resultFound step
          continuationWP,
        resultRuntimeRelated, failureClear, valueRelated⟩
  | @externalLet externalSourceRuntime externalSourceEnv decl continuation
      externalNextRuntime externalSourceValue stepCost _ _ continuationCost
      supported sourceStep continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels
            _ targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits : stepCost ≤ stepCost + continuationCost :=
        Nat.le_add_right _ _
      obtain ⟨nextStore, nextLocals, nextWitness, step, _externalsPreserved,
          _hostDescriptorsPreserved, _witnessDescriptorsPreserved,
          nextInvariant⟩ :=
        externalRuntimeRefines supported stepFits invariant sourceStep
          stateRelated valueCompiled valueAdapted resultFound
      have continuationInvariant :
          Invariant continuationCost externalNextRuntime
            (bind externalSourceEnv decl.fvarId externalSourceValue)
            nextStore nextLocals nextWitness := by
        simpa using nextInvariant
      obtain ⟨resultStore, resultWitness, resultKind, physical,
          continuationWP, resultRuntimeRelated, failureClear,
          valueRelated⟩ :=
        ih continuationAdapted step.2.2.1 continuationInvariant
      subst target
      exact ⟨resultStore, resultWitness, resultKind, physical,
        codeWP_externalLet valueCompiled valueAdapted resultFound step
          continuationWP,
        resultRuntimeRelated, failureClear, valueRelated⟩
  | caseOf supported sourceStep continued ih =>
      obtain ⟨selectedTarget, selectedAdapted, _selected, lift⟩ :=
        caseRuntimeRefines supported sourceStep stateRelated adapted
      obtain ⟨resultStore, resultWitness, resultKind, physical,
          continuationWP, resultRuntimeRelated, failureClear,
          valueRelated⟩ :=
        ih selectedAdapted stateRelated invariant
      exact ⟨resultStore, resultWitness, resultKind, physical,
        lift [] (ExactReturnControlPost resultStore physical)
          (by
            intro continuation returned
            subst continuation
            rfl)
          continuationWP,
        resultRuntimeRelated, failureClear, valueRelated⟩
  | effect supported sourceStep continued ih =>
      obtain ⟨targetRest, nextStore, nextWitness, continuationAdapted, step,
          nextInvariant⟩ :=
        effectRuntimeRefines supported sourceStep stateRelated invariant adapted
      obtain ⟨resultStore, resultWitness, resultKind, physical,
          continuationWP, resultRuntimeRelated, failureClear,
          valueRelated⟩ :=
        ih continuationAdapted step.2.2.2.1 nextInvariant
      exact ⟨resultStore, resultWitness, resultKind, physical,
        codeWP_effect step continuationWP,
        resultRuntimeRelated, failureClear, valueRelated⟩

/--
Public cost-indexed structural partial correctness for mixed direct/external
code with selected case branches and no-result effects.

`CaseRuntimeRefines` and `EffectRuntimeRefines` are the two additional theorem
conditions over the spine theorem. Both are uniform over production
compiler/adapter outputs and therefore remain implementation laws rather than
per-program certificates.
-/
theorem codeWP_of_budgetedCodeEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value}
    {requiredBytes : Nat}
    {targetFunction : Wasm.Function}
    {parameters callerTail : List Wasm.Value}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop}
    {EffectSupported : EffectSupportedPredicate}
    {directCost : LCNF.LetDecl .impure → Nat}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (evaluation :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue
        requiredBytes)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels sourceCode target)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (invariant :
      Invariant requiredBytes sourceRuntime sourceEnv initial locals witness)
    (directRuntimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction labels
        module hostEnv DirectSupported directCost Invariant)
    (externalRuntimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction
        labels module hostEnv externals ExternalSupported Invariant)
    (caseRuntimeRefines :
      CaseRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv CaseSupported)
    (effectRuntimeRefines :
      EffectRuntimeRefines context sourceModule sourceFunction labels module
        hostEnv EffectSupported Invariant)
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
  obtain ⟨resultStore, resultWitness, resultKind, physical, exactWP,
      runtimeRelated, failureClear, valueRelated⟩ :=
    codeWP_of_budgetedCodeEvaluates_exactReturn evaluation adapted localsAligned
      stateRelated invariant directRuntimeRefines externalRuntimeRefines
      caseRuntimeRefines effectRuntimeRefines
  refine ⟨resultStore, resultWitness, resultKind, physical, ?_,
    runtimeRelated, failureClear, valueRelated⟩
  apply exactWP.conseq
  intro continuation returned
  subst continuation
  simp [ConcreteFunctionBodyPost, ExactReturnPost, resultCount,
    ← parameterCount]

/--
Whole-export partial correctness for a mixed budgeted direct/external spine.

The operation-family runtime laws are reusable semantic implementation
theorems, not per-program certificates. The source evaluation and its cost
index determine the path; the production compiler and adapter determine the
target body.
-/
theorem ConcreteSupportedExport.correctBudgetedSpine
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {directCost : LCNF.LetDecl .impure → Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals DirectSupported
        ExternalSupported directCost sourceRuntime sourceEnv sourceCode
        resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (directRuntimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env DirectSupported directCost
        (ConcreteBudgetedLocalFrame sourceFunction))
    (externalRuntimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals ExternalSupported
        (ConcreteBudgetedLocalFrame sourceFunction))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  obtain ⟨resultStore, resultWitness, resultKind, physical, bodyWP,
      resultRuntimeRelated, failureClear, valueRelated⟩ :=
    codeWP_of_budgetedSpineEvaluates
      (parameters := parameters) (callerTail := callerTail)
      evaluation spec.bodyAdapted spec.localsAligned stateRelated
      ⟨frameAligned, budget⟩ directRuntimeRefines externalRuntimeRefines
      parameterCount spec.singleResult
  have parameterPrefix :
      (parameters ++ callerTail).take spec.targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  have targetTerminates :
      Wasm.TerminatesWith hosts.env target.wasmModule
        spec.targetFunctionIndex initial (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail) := by
    apply CodeWP.toConcreteTerminatesWith spec.notImport
      spec.targetFunctionFound
    simpa [parameterPrefix] using bodyWP
  refine
    ⟨evaluation.execEvaluates, resultKind,
      spec.targetFunctionIndex, spec.exported, ?_⟩
  obtain ⟨fuelBound, terminates⟩ := targetTerminates
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  obtain ⟨results, final, executed, finalEq, resultsEq⟩ :=
    terminates fuel enoughFuel
  subst final
  subst results
  exact ⟨physical :: callerTail, resultStore, executed, resultWitness, physical,
    resultRuntimeRelated, failureClear, valueRelated, rfl⟩

/--
Whole-export partial correctness for mixed direct/external code with selected
case branches and no-result effects.

The four runtime laws are operation-family implementation theorems,
universally quantified over production compiler outputs. The only
program-specific premise is a successful source evaluation and its selected
branches; no translation certificate is accepted.
-/
theorem ConcreteSupportedExport.correctBudgetedCode
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    {DirectSupported : LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop}
    {EffectSupported : EffectSupportedPredicate}
    {directCost : LCNF.LetDecl .impure → Nat}
    {Invariant :
      Nat → RuntimeState → Env → Wasm.Store Host → Wasm.Locals →
        RefinementWitness → Prop}
    (evaluation :
      BudgetedCodeEvaluates context externals DirectSupported
        ExternalSupported CaseSupported EffectSupported directCost
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue
        requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (invariant :
      Invariant requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (directRuntimeRefines :
      DirectLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env DirectSupported directCost Invariant)
    (externalRuntimeRefines :
      ExternalLetRuntimeRefinesWithCost context sourceModule sourceFunction []
        target.wasmModule hosts.env externals ExternalSupported Invariant)
    (caseRuntimeRefines :
      CaseRuntimeRefines context sourceModule sourceFunction []
        target.wasmModule hosts.env CaseSupported)
    (effectRuntimeRefines :
      EffectRuntimeRefines context sourceModule sourceFunction []
        target.wasmModule hosts.env EffectSupported Invariant)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  obtain ⟨resultStore, resultWitness, resultKind, physical, bodyWP,
      resultRuntimeRelated, failureClear, valueRelated⟩ :=
    codeWP_of_budgetedCodeEvaluates
      (parameters := parameters) (callerTail := callerTail)
      evaluation spec.bodyAdapted spec.localsAligned stateRelated invariant
      directRuntimeRefines externalRuntimeRefines caseRuntimeRefines
      effectRuntimeRefines parameterCount spec.singleResult
  have parameterPrefix :
      (parameters ++ callerTail).take spec.targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  have targetTerminates :
      Wasm.TerminatesWith hosts.env target.wasmModule
        spec.targetFunctionIndex initial (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail) := by
    apply CodeWP.toConcreteTerminatesWith spec.notImport
      spec.targetFunctionFound
    simpa [parameterPrefix] using bodyWP
  refine
    ⟨evaluation.execEvaluates, resultKind,
      spec.targetFunctionIndex, spec.exported, ?_⟩
  obtain ⟨fuelBound, terminates⟩ := targetTerminates
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  obtain ⟨results, final, executed, finalEq, resultsEq⟩ :=
    terminates fuel enoughFuel
  subst final
  subst results
  exact ⟨physical :: callerTail, resultStore, executed, resultWitness, physical,
    resultRuntimeRelated, failureClear, valueRelated, rfl⟩

/--
Concrete whole-export partial correctness for spines that interleave every
currently admitted direct operation with the pure integer construction and
arithmetic external family.

The caller supplies source evaluation, the initial representation/frame
relation, one exact path budget, and the installed external implementation's
integer-result family law. The direct and external runtime laws are derived
from the supported export rather than passed as program-specific evidence.
-/
theorem ConcreteSupportedExport.correctBudgetedIntegerExternalSpine
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals
        (BudgetedDirectSupported context)
        (PureIntegerExternalSupported context externals)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (implementation :
      initial.host.externals.IntegerResultRefines externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  obtain ⟨resultStore, resultWitness, resultKind, physical, bodyWP,
      resultRuntimeRelated, failureClear, valueRelated⟩ :=
    codeWP_of_budgetedSpineEvaluates
      (parameters := parameters) (callerTail := callerTail)
      evaluation spec.bodyAdapted spec.localsAligned stateRelated
      ⟨⟨frameAligned, budget⟩, implementation⟩
      (spec.directLetRuntimeRefines_budgetedDirect_integerExternal externals)
      (spec.externalLetRuntimeRefinesWithCost_pureInteger externals)
      parameterCount spec.singleResult
  have parameterPrefix :
      (parameters ++ callerTail).take spec.targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  have targetTerminates :
      Wasm.TerminatesWith hosts.env target.wasmModule
        spec.targetFunctionIndex initial (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail) := by
    apply CodeWP.toConcreteTerminatesWith spec.notImport
      spec.targetFunctionFound
    simpa [parameterPrefix] using bodyWP
  refine
    ⟨evaluation.execEvaluates, resultKind,
      spec.targetFunctionIndex, spec.exported, ?_⟩
  obtain ⟨fuelBound, terminates⟩ := targetTerminates
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  obtain ⟨results, final, executed, finalEq, resultsEq⟩ :=
    terminates fuel enoughFuel
  subst final
  subst results
  exact ⟨physical :: callerTail, resultStore, executed, resultWitness, physical,
    resultRuntimeRelated, failureClear, valueRelated, rfl⟩

/--
Concrete whole-export partial correctness for spines that interleave every
currently admitted direct operation with pure natural-result externals. The
initial implementation law covers `Int.natAbs`; the proof internally chooses
the immediate, promoted-tag, or limb-object result representation at each
source step.
-/
theorem ConcreteSupportedExport.correctBudgetedNaturalExternalSpine
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals
        (BudgetedDirectSupported context)
        (PureNaturalExternalSupported context externals)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (implementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  obtain ⟨resultStore, resultWitness, resultKind, physical, bodyWP,
      resultRuntimeRelated, failureClear, valueRelated⟩ :=
    codeWP_of_budgetedSpineEvaluates
      (parameters := parameters) (callerTail := callerTail)
      evaluation spec.bodyAdapted spec.localsAligned stateRelated
      ⟨⟨frameAligned, budget⟩, implementation⟩
      (spec.directLetRuntimeRefines_budgetedDirect_naturalExternal externals)
      (spec.externalLetRuntimeRefinesWithCost_pureNatural externals)
      parameterCount spec.singleResult
  have parameterPrefix :
      (parameters ++ callerTail).take spec.targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  have targetTerminates :
      Wasm.TerminatesWith hosts.env target.wasmModule
        spec.targetFunctionIndex initial (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail) := by
    apply CodeWP.toConcreteTerminatesWith spec.notImport
      spec.targetFunctionFound
    simpa [parameterPrefix] using bodyWP
  refine
    ⟨evaluation.execEvaluates, resultKind,
      spec.targetFunctionIndex, spec.exported, ?_⟩
  obtain ⟨fuelBound, terminates⟩ := targetTerminates
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  obtain ⟨results, final, executed, finalEq, resultsEq⟩ :=
    terminates fuel enoughFuel
  subst final
  subst results
  exact ⟨physical :: callerTail, resultStore, executed, resultWitness, physical,
    resultRuntimeRelated, failureClear, valueRelated, rfl⟩

/--
Concrete whole-export partial correctness for spines interleaving the current
direct family with admitted pure nonallocating scalar externals, initially
`Int.decLt`.
-/
theorem ConcreteSupportedExport.correctBudgetedScalarExternalSpine
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals
        (BudgetedDirectSupported context)
        (PureScalarExternalSupported context externals)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (implementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  obtain ⟨resultStore, resultWitness, resultKind, physical, bodyWP,
      resultRuntimeRelated, failureClear, valueRelated⟩ :=
    codeWP_of_budgetedSpineEvaluates
      (parameters := parameters) (callerTail := callerTail)
      evaluation spec.bodyAdapted spec.localsAligned stateRelated
      ⟨⟨frameAligned, budget⟩, implementation⟩
      (spec.directLetRuntimeRefines_budgetedDirect_scalarExternal externals)
      (spec.externalLetRuntimeRefinesWithCost_pureScalar externals)
      parameterCount spec.singleResult
  have parameterPrefix :
      (parameters ++ callerTail).take spec.targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  have targetTerminates :
      Wasm.TerminatesWith hosts.env target.wasmModule
        spec.targetFunctionIndex initial (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail) := by
    apply CodeWP.toConcreteTerminatesWith spec.notImport
      spec.targetFunctionFound
    simpa [parameterPrefix] using bodyWP
  refine
    ⟨evaluation.execEvaluates, resultKind,
      spec.targetFunctionIndex, spec.exported, ?_⟩
  obtain ⟨fuelBound, terminates⟩ := targetTerminates
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  obtain ⟨results, final, executed, finalEq, resultsEq⟩ :=
    terminates fuel enoughFuel
  subst final
  subst results
  exact ⟨physical :: callerTail, resultStore, executed, resultWitness, physical,
    resultRuntimeRelated, failureClear, valueRelated, rfl⟩

/--
Concrete whole-export partial correctness for spines that interleave every
currently admitted direct operation with any proved pure integer-, natural-,
or scalar-result external. One source execution may freely mix the three
families; the combined frame retains all installed implementation laws across
every direct and external step.
-/
theorem ConcreteSupportedExport.correctBudgetedPureExternalSpine
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedSpineEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  obtain ⟨resultStore, resultWitness, resultKind, physical, bodyWP,
      resultRuntimeRelated, failureClear, valueRelated⟩ :=
    codeWP_of_budgetedSpineEvaluates
      (parameters := parameters) (callerTail := callerTail)
      evaluation spec.bodyAdapted spec.localsAligned stateRelated
      ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
        scalarImplementation⟩
      (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
      (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
      parameterCount spec.singleResult
  have parameterPrefix :
      (parameters ++ callerTail).take spec.targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  have targetTerminates :
      Wasm.TerminatesWith hosts.env target.wasmModule
        spec.targetFunctionIndex initial (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail) := by
    apply CodeWP.toConcreteTerminatesWith spec.notImport
      spec.targetFunctionFound
    simpa [parameterPrefix] using bodyWP
  refine
    ⟨evaluation.execEvaluates, resultKind,
      spec.targetFunctionIndex, spec.exported, ?_⟩
  obtain ⟨fuelBound, terminates⟩ := targetTerminates
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  obtain ⟨results, final, executed, finalEq, resultsEq⟩ :=
    terminates fuel enoughFuel
  subst final
  subst results
  exact ⟨physical :: callerTail, resultStore, executed, resultWitness, physical,
    resultRuntimeRelated, failureClear, valueRelated, rfl⟩

/--
Concrete whole-export partial correctness for arbitrary nesting of
default-only cases around the complete current direct/pure-external family.

The source evaluation selects each sole default branch. The production
compiler erases each such wrapper to that branch, so the generic case law
requires no additional concrete step, certificate, or heap budget.
-/
theorem ConcreteSupportedExport.correctBudgetedPureExternalDefaultCases
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported NoEffectsSupported directLetAllocationCost
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue
        requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩
    (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
    (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
    caseRuntimeRefines_defaultOnly effectRuntimeRefines_noEffects
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of
compiler-erased persistent ownership operations, default-only cases, and the
complete current direct/pure-external family.

Every admitted persistent increment or decrement is an exact source and target
no-op. It therefore consumes no heap budget and preserves the complete
budgeted local frame, including world, trace, concrete heap, locals, witness,
and external implementation laws.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalPersistentOwnership
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported PersistentOwnershipEffectSupported
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩
    (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
    (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
    caseRuntimeRefines_defaultOnly
    effectRuntimeRefines_persistentOwnership parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of
successful ordinary reference-count increments, default-only cases, and the
complete current direct/pure-external family.

The source admission supplies only the semantic increment result, compiler
local kind, and count headroom. Production inversion and resolver alignment
recover and execute the generated unary host-call prefix. Header-only updates
preserve the heap frontier and therefore consume zero allocation budget.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOrdinaryIncrements
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OrdinaryIncrementEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩
    (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
    (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ordinaryIncrement (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of
successful ordinary recursive decrements, default-only cases, and the current
direct/pure-external family.

The sole additional entry premise is immutable closure-descriptor agreement.
It is threaded by the generic direct/external laws and consumed by decrement
only when recursive closure ownership is released.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOrdinaryDecrements
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OrdinaryDecrementEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩
    (spec.directLetRuntimeRefines_budgetedDirect_ownership externals)
    (spec.externalLetRuntimeRefinesWithCost_ownership externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ordinaryDecrement (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of
successful explicit deletions, default-only cases, and the complete current
direct/pure-external family.

The source admission permits both ordinary heap deletion and the exact erased
reset token. Compiler inversion and resolver alignment derive the generated
unary call, while exact frontier preservation keeps the allocation budget
unchanged.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOrdinaryDeletes
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OrdinaryDeleteEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩
    (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
    (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ordinaryDelete (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of every
currently proved successful ownership effect, default-only cases, and the
complete current direct/pure-external family.

Persistent increment/decrement, ordinary increment, recursive decrement, and
explicit deletion share one ownership-aware invariant. The source evaluation
may select any family at each effect node; no per-node target witness or
operation-specific runtime theorem appears in this endpoint.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOwnership
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OwnershipEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩
    (spec.directLetRuntimeRefines_budgetedDirect_ownership externals)
    (spec.externalLetRuntimeRefinesWithCost_ownership externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ownership (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of the
complete current ownership family, successful constructor-tag mutation,
default-only cases, and the direct/pure-external family.

All effect nodes are admitted solely by source/compiler facts. The production
compiler/adaptor inversion, resolver alignment, and executable runtime
refinement are recovered by the uniform effect law.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOwnershipAndTag
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported (OwnershipAndTagEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩
    (spec.directLetRuntimeRefines_budgetedDirect_ownership externals)
    (spec.externalLetRuntimeRefinesWithCost_ownership externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ownershipAndTag (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of the
ownership family, successful constructor-tag mutation, successful FVar
object-field mutation, default-only cases, and the direct/pure-external family.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOwnershipTagAndObjectFVar
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndObjectFVarEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩
    (spec.directLetRuntimeRefines_budgetedDirect_ownership externals)
    (spec.externalLetRuntimeRefinesWithCost_ownership externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ownershipTagAndObjectFVar
      (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of the
ownership family, constructor-tag mutation, both FVar and erased object-field
mutation, default-only cases, and the direct/pure-external family.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOwnershipTagAndObject
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndObjectEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩
    (spec.directLetRuntimeRefines_budgetedDirect_ownership externals)
    (spec.externalLetRuntimeRefinesWithCost_ownership externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ownershipTagAndObject
      (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of the
ownership family, constructor-tag mutation, object and `USize` field mutation,
default-only cases, and the direct/pure-external family.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOwnershipTagAndFieldMutation
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndFieldMutationEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩
    (spec.directLetRuntimeRefines_budgetedDirect_ownership externals)
    (spec.externalLetRuntimeRefinesWithCost_ownership externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ownershipTagAndFieldMutation
      (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of the
ownership family, constructor-tag mutation, all supported successful field
mutations, default-only cases, and the direct/pure-external family.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOwnershipTagAndAllFieldMutation
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩
    (spec.directLetRuntimeRefines_budgetedDirect_ownership externals)
    (spec.externalLetRuntimeRefinesWithCost_ownership externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ownershipTagAndAllFieldMutation
      (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary interleaving of
successful reset with the ownership family, constructor-tag mutation, all
supported successful field mutations, default-only cases, and the complete
direct/pure-external family.

The evaluation predicate admits reset only through
`OwnershipBudgetedDirectSupported`; the compiler theorem derives its runtime
branch rather than accepting a branch certificate.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalOwnershipTagAllFieldMutationAndReset
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (OwnershipBudgetedDirectSupported context)
        (PureExternalSupported context externals)
        DefaultOnlyCaseSupported
        (OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost sourceRuntime sourceEnv sourceCode resultRuntime
        resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (descriptorAgreement :
      initial.host.closureDescriptors =
        initialWitness.closureDescriptors)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩
    (spec.directLetRuntimeRefines_ownershipBudgetedDirect externals)
    (spec.externalLetRuntimeRefinesWithCost_ownership externals)
    caseRuntimeRefines_defaultOnly
    (spec.effectRuntimeRefines_ownershipTagAndAllFieldMutation
      (externals := externals))
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary nesting of normalized
object-constructor case chains around the complete current
direct/pure-external family.

There is no arity-specific case certificate. Each alternatives list is
admitted by `ObjectConstructorCaseAltsSupported`; the source evaluator selects
the branch, and production compiler inversion plus the recursive concrete
`getTag` theorem reconstructs and executes the exact generated chain.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalObjectConstructorCases
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        (ObjectConstructorCasesSupported context)
        NoEffectsSupported directLetAllocationCost sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩
    (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
    (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
    spec.caseRuntimeRefines_objectConstructorCases
    effectRuntimeRefines_noEffects parameterCount

/--
Concrete whole-export partial correctness for arbitrary nesting of normalized
scalar `UInt8` constructor case chains around the complete current
direct/pure-external family.

Every constructor tag is statically admitted in the `UInt8` lane. Source
evaluation selects the branch, and production compiler inversion plus the
related discriminator local reconstructs and executes the exact generated
comparison chain.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalScalarUInt8Cases
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        (ScalarUInt8CasesSupported context)
        NoEffectsSupported directLetAllocationCost sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩
    (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
    (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
    spec.caseRuntimeRefines_scalarUInt8Cases effectRuntimeRefines_noEffects
    parameterCount

/--
Concrete whole-export partial correctness for arbitrary nesting of singleton
object-constructor cases around the complete current direct/pure-external
family.

Each selected branch is established by the source evaluator. Production
compiler inversion recovers the exact `getTag` test, and the concrete resolver,
heap relation, and stable-return boundary discharge its execution.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalSingleObjectConstructorCases
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        (SingleObjectConstructorCaseSupported context)
        NoEffectsSupported directLetAllocationCost sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩
    (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
    (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
    spec.caseRuntimeRefines_singleObjectConstructor
    effectRuntimeRefines_noEffects parameterCount

/--
Concrete whole-export partial correctness for arbitrary nesting of ordered
two-constructor/default object cases around the current
direct/pure-external family.
-/
theorem
    ConcreteSupportedExport.correctBudgetedPureExternalTwoObjectConstructorDefaultCases
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
    {externals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      BudgetedCodeEvaluates context externals
        (BudgetedDirectSupported context)
        (PureExternalSupported context externals)
        (TwoObjectConstructorDefaultCasesSupported context)
        NoEffectsSupported directLetAllocationCost sourceRuntime sourceEnv
        sourceCode resultRuntime resultValue requiredBytes)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget requiredBytes)
    (integerImplementation :
      initial.host.externals.IntegerResultRefines externals)
    (naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        initial.host.externals externals)
    (scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        initial.host.externals externals)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  exact spec.correctBudgetedCode evaluation stateRelated
    ⟨⟨frameAligned, budget⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩
    (spec.directLetRuntimeRefines_budgetedDirect_pureExternal externals)
    (spec.externalLetRuntimeRefinesWithCost_pureExternal externals)
    spec.caseRuntimeRefines_twoObjectConstructorDefault
    effectRuntimeRefines_noEffects parameterCount

/--
Whole-export partial correctness for the current budgeted direct-value
fragment.

The premise is only a successful finite source evaluation through admitted
direct operations, the initial concrete-state relation, exact generated-frame
shape, and one source-computed wasm32 allocation budget. The production
compiler and adapter determine the complete target body. The conclusion pairs
the executable source observation with fuel-free termination of the named
concrete export and hides the final physical representation behind
`RefinedReturnPost`.
-/
theorem ConcreteSupportedExport.correctBudgetedDirect
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
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    (evaluation :
      DirectValueEvaluates context (BudgetedDirectSupported context)
        sourceRuntime sourceEnv sourceCode resultRuntime resultValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (budget :
      initial.host.runtime.heap.AddressSpaceBudget
        (DirectValuePathCost directLetAllocationCost sourceCode))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ∃ resultKind,
        ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
          initial (parameters ++ callerTail)
          (RefinedReturnPost resultRuntime resultValue resultKind
            callerTail) := by
  obtain ⟨resultStore, resultWitness, resultKind, physical, bodyWP,
      resultRuntimeRelated, failureClear, valueRelated⟩ :=
    codeWP_of_directValueEvaluates_withCost
      (parameters := parameters) (callerTail := callerTail)
      evaluation spec.bodyAdapted spec.localsAligned stateRelated
      ⟨frameAligned, budget⟩ spec.directLetRuntimeRefines_budgetedDirect
      parameterCount spec.singleResult
  have parameterPrefix :
      (parameters ++ callerTail).take spec.targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  have targetTerminates :
      Wasm.TerminatesWith hosts.env target.wasmModule
        spec.targetFunctionIndex initial (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail) := by
    apply CodeWP.toConcreteTerminatesWith spec.notImport
      spec.targetFunctionFound
    simpa [parameterPrefix] using bodyWP
  refine
    ⟨evaluation.execEvaluates sourceExternals, resultKind,
      spec.targetFunctionIndex, spec.exported, ?_⟩
  obtain ⟨fuelBound, terminates⟩ := targetTerminates
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  obtain ⟨results, final, executed, finalEq, resultsEq⟩ :=
    terminates fuel enoughFuel
  subst final
  subst results
  exact ⟨physical :: callerTail, resultStore, executed, resultWitness, physical,
    resultRuntimeRelated, failureClear, valueRelated, rfl⟩

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
          ConstructorArgumentsRelated initialWitness fieldKinds.toList
            physicalArgs semanticArgs.toList →
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
  obtain ⟨physicalArgs, argumentsReady, physicalArity, argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs spec.localsAligned argumentsCompiled
      argumentsAdapted evaluated stateRelated
  obtain ⟨nextStore, word, nextWitness, operation, extension,
      nextRuntimeRelated, failureClear, valueRelated⟩ :=
    concreteStep physicalArity argumentsRelated
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
Finite nonempty-constructor corollary with constructive concrete allocation.
No successful target allocation or operation-simulation function is supplied
by the caller.
-/
theorem ConcreteSupportedExport.correctConstructorNonemptyReturn_of_capacity
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
    (operationWellFormed :
      (RuntimeOp.allocCtor info fieldKinds resultKind).abiWellFormed = true)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
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
    (capacity :
      initial.host.runtime.heap.AllocationCapacity
        (ConstructorLayout.ofInfo info).allocationBytes)
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
  have operationFacts :
      (info.size = fieldKinds.size ∧
        fieldKinds.all AbiKind.isObjectField = true) ∧
        (constructorKind info).refines resultKind = true := by
    simpa [RuntimeOp.abiWellFormed] using operationWellFormed
  have semanticArity : semanticArgs.size = info.size := by
    by_contra mismatch
    simp [allocCtor, mismatch, Bind.bind, Except.bind] at semanticStep
  have tagFits : info.cidx < UInt32.size := by
    simpa [Fir.Wasm.constructorTagFitsI32] using fits
  apply spec.correctConstructorReturn valueEq fits valueKind argumentsCompiled
    localCompiled evaluated semanticStep stateRelated parameterCount
  · intro physicalArgs physicalArity argumentsRelated
    exact constructorNonemptyStep_of_capacity stateRelated.1 physicalArity
      argumentsRelated semanticStep semanticArity operationFacts.1.1.symm
      operationFacts.1.2 nonempty tagFits objectFieldsFit usizeFieldsFit
      scalarBytesFit operationFacts.2 capacity
  · exact localSetReady

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
