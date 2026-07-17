import FirTalos.Correctness.FunctionCtorProjectionExample

namespace FirTalos.Correctness

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples

private def caseBodyCheck : Wasm.Program → Bool
  | [.call alloc, .localSet cIndex,
      .localGet cLoad0, .call getTag0, .const falseTag, .eq,
      .iff depth0 results0
        [.call literal0, .localSet falseIndex, .localGet falseLoad, .ret]
        [.localGet cLoad1, .call getTag1, .const trueTag, .eq,
          .iff depth1 results1
            [.call literal1, .localSet trueIndex, .localGet trueLoad, .ret]
            [.unreachable]]] =>
      alloc == 0 && cIndex == 0 && cLoad0 == 0 && getTag0 == 1 &&
      falseTag == 0 && depth0 == 0 && results0 == 0 &&
      literal0 == 2 && falseIndex == 1 && falseLoad == 1 &&
      cLoad1 == 0 && getTag1 == 1 && trueTag == 1 &&
      depth1 == 0 && results1 == 0 && literal1 == 3 &&
      trueIndex == 1 && trueLoad == 1
  | _ => false

private theorem caseBody_eq_of_check {body : Wasm.Program}
    (checked : caseBodyCheck body = true) :
    body = [.call 0, .localSet 0,
      .localGet 0, .call 1, .const 0, .eq,
      .iff 0 0
        [.call 2, .localSet 1, .localGet 1, .ret]
        [.localGet 0, .call 1, .const 1, .eq,
          .iff 0 0
            [.call 3, .localSet 1, .localGet 1, .ret]
            [.unreachable]]] := by
  unfold caseBodyCheck at checked
  split at checked <;> simp_all

private def caseOperationsCheck : List HostOperation → Bool
  | [.allocCtor info fields resultKind, .getTag,
      .naturalLiteral falseValue falseKind,
      .naturalLiteral trueValue trueKind] =>
      decide (info = trueInfo) && fields == #[] && resultKind == .tagged &&
      falseValue == 0 && falseKind == .tobject &&
      trueValue == 1 && trueKind == .tobject
  | _ => false

private theorem caseOperations_eq_of_check {operations : List HostOperation}
    (checked : caseOperationsCheck operations = true) :
    operations = [
      .allocCtor trueInfo #[] .tagged,
      .getTag,
      .naturalLiteral 0 .tobject,
      .naturalLiteral 1 .tobject] := by
  unfold caseOperationsCheck at checked
  split at checked <;> simp_all

/-- Checked symbolic module for W3's explicit constructor-case fixture. -/
def abiCaseSourceModule : Fir.Wasm.Module :=
  match Fir.Wasm.lowerSupported abiCaseProgram with
  | .ok source => source
  | .error _ => default

theorem abiCaseSourceModule_lowered :
    Fir.Wasm.lowerSupported abiCaseProgram = .ok abiCaseSourceModule := by
  have success : (Fir.Wasm.lowerSupported abiCaseProgram).isOk = true := by
    native_decide
  cases lowered : Fir.Wasm.lowerSupported abiCaseProgram with
  | error error =>
      rw [lowered] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok source => simp [abiCaseSourceModule, lowered]

def abiCaseSourceFunction : Fir.Wasm.Function :=
  match abiCaseSourceModule.functions[0]? with
  | some function => function
  | none => default

theorem abiCaseSourceFunction_found :
    abiCaseSourceModule.functions[0]? = some abiCaseSourceFunction := by
  have present : abiCaseSourceModule.functions[0]?.isSome = true := by
    native_decide
  cases found : abiCaseSourceModule.functions[0]? with
  | none => simp [found] at present
  | some function => simp [abiCaseSourceFunction, found]

def abiCaseDeclC : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl c taggedType (.ctor trueInfo #[])

def abiCaseDeclFalse : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl r tobjectType (.lit (.nat 0))

def abiCaseDeclTrue : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl r tobjectType (.lit (.nat 1))

def abiCaseFalseCode : Lean.Compiler.LCNF.Code .impure :=
  .let abiCaseDeclFalse (.return r)

def abiCaseTrueCode : Lean.Compiler.LCNF.Code .impure :=
  .let abiCaseDeclTrue (.return r)

def abiCaseCases : Lean.Compiler.LCNF.Cases .impure :=
  .mk ``Bool tobjectType c #[
    .ctorAlt falseInfo abiCaseFalseCode,
    .ctorAlt trueInfo abiCaseTrueCode]

def abiCaseCode : Lean.Compiler.LCNF.Code .impure :=
  .let abiCaseDeclC (.cases abiCaseCases)

def abiCaseContext : Fir.Wasm.Context :=
  { program := abiCaseProgram
    localKinds := [(r, .tobject), (c, .tagged)] }

private def emptyCaseAdaptedModule : AdaptedModule :=
  { wasmModule := default, sourceMap := default }

/-- Executable Talos module adapted from the checked case fixture. -/
def abiCaseAdaptedModule : AdaptedModule :=
  match adapt abiCaseSourceModule with
  | .ok target => target
  | .error _ => emptyCaseAdaptedModule

theorem abiCaseAdaptedModule_adapted :
    adapt abiCaseSourceModule = .ok abiCaseAdaptedModule := by
  have success : (adapt abiCaseSourceModule).isOk = true := by
    native_decide
  cases adapted : adapt abiCaseSourceModule with
  | error error =>
      rw [adapted] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok target => simp [abiCaseAdaptedModule, adapted]

def abiCaseResolvedHosts : ResolvedHosts :=
  match resolveHosts abiCaseSourceModule with
  | .ok resolved => resolved
  | .error _ => { operations := [] }

theorem abiCaseResolvedHosts_resolved :
    resolveHosts abiCaseSourceModule = .ok abiCaseResolvedHosts := by
  have success : (resolveHosts abiCaseSourceModule).isOk = true := by
    native_decide
  cases resolved : resolveHosts abiCaseSourceModule with
  | error error =>
      rw [resolved] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok hosts => simp [abiCaseResolvedHosts, resolved]

theorem abiCaseResolvedHosts_operations :
    abiCaseResolvedHosts.operations = [
      .allocCtor trueInfo #[] .tagged,
      .getTag,
      .naturalLiteral 0 .tobject,
      .naturalLiteral 1 .tobject] := by
  apply caseOperations_eq_of_check
  native_decide

def abiCaseMainFunction : Wasm.Function :=
  match abiCaseAdaptedModule.wasmModule.funcs[
      4 - abiCaseAdaptedModule.wasmModule.imports.length]? with
  | some function => function
  | none => default

theorem abiCaseMain_found :
    abiCaseAdaptedModule.wasmModule.funcs[
        4 - abiCaseAdaptedModule.wasmModule.imports.length]? =
      some abiCaseMainFunction := by
  have present :
      (abiCaseAdaptedModule.wasmModule.funcs[
        4 - abiCaseAdaptedModule.wasmModule.imports.length]?).isSome = true := by
    native_decide
  cases found : abiCaseAdaptedModule.wasmModule.funcs[
      4 - abiCaseAdaptedModule.wasmModule.imports.length]? with
  | none => simp [found] at present
  | some function => simp [abiCaseMainFunction, found]

theorem abiCaseMain_body :
    abiCaseMainFunction.body = [.call 0, .localSet 0,
      .localGet 0, .call 1, .const 0, .eq,
      .iff 0 0
        [.call 2, .localSet 1, .localGet 1, .ret]
        [.localGet 0, .call 1, .const 1, .eq,
          .iff 0 0
            [.call 3, .localSet 1, .localGet 1, .ret]
            [.unreachable]]] := by
  apply caseBody_eq_of_check
  native_decide

theorem abiCaseMain_exported :
    abiCaseAdaptedModule.wasmModule.findExport "main" = some 4 := by
  native_decide

theorem abiCaseMain_notImport :
    abiCaseAdaptedModule.wasmModule.imports[4]? = none := by
  native_decide

theorem abiCaseMain_resultCount :
    abiCaseMainFunction.results.length = 1 := by
  native_decide

theorem abiCaseHostsMatch :
    HostsMatch abiCaseResolvedHosts abiCaseSourceModule := by
  unfold HostsMatch
  native_decide

theorem abiCaseHostsSatisfy :
    abiCaseResolvedHosts.env.Satisfies abiCaseAdaptedModule.wasmModule
      abiCaseResolvedHosts.spec :=
  resolvedHosts_satisfy_adapted abiCaseAdaptedModule_adapted abiCaseHostsMatch

def abiCaseTrueValue : Value :=
  .object (.tagged (UInt64.ofNat 1))

def abiCaseHandlesC : HandleTable :=
  { entries := [(1, abiCaseTrueValue)], next := 2 }

def abiCaseInitialStore : Wasm.Store RuntimeHost :=
  abiCaseAdaptedModule.wasmModule.initialStore

def abiCaseStoreC : Wasm.Store RuntimeHost :=
  successfulHostStore abiCaseInitialStore {} abiCaseHandlesC

def abiCaseStoreR : Wasm.Store RuntimeHost :=
  successfulHostStore abiCaseStoreC {} abiCaseHandlesC

def abiCaseLocalsC : Wasm.Locals :=
  { locals := [.i32 1, .i32 0] }

def abiCaseLocalsR : Wasm.Locals :=
  { locals := [.i32 1, .i32 1] }

def abiCaseEnvC : Env :=
  bind [] c abiCaseTrueValue

def abiCaseEnvR : Env :=
  bind abiCaseEnvC r abiCaseTrueValue

def abiCaseImport (index : Nat) : Wasm.ImportDecl :=
  abiCaseAdaptedModule.wasmModule.imports[index]!

theorem abiCaseImport0_found :
    abiCaseAdaptedModule.wasmModule.imports[0]? =
      some (abiCaseImport 0) := by
  native_decide

theorem abiCaseImport1_found :
    abiCaseAdaptedModule.wasmModule.imports[1]? =
      some (abiCaseImport 1) := by
  native_decide

theorem abiCaseImport2_found :
    abiCaseAdaptedModule.wasmModule.imports[2]? =
      some (abiCaseImport 2) := by
  native_decide

theorem abiCaseImport3_found :
    abiCaseAdaptedModule.wasmModule.imports[3]? =
      some (abiCaseImport 3) := by
  native_decide

theorem abiCaseInitialState_related :
    StateRelated abiCaseSourceFunction {} [] abiCaseInitialStore
      (abiCaseMainFunction.toLocals []) := by
  unfold StateRelated
  refine ⟨rfl, rfl, rfl, handleTableInvariant_empty, ?_⟩
  intro fvar value found
  simp [lookup] at found

theorem abiCaseAllocated :
    allocCtor abiCaseInitialStore.host.runtime trueInfo #[] =
      .ok ({}, abiCaseTrueValue) := by
  rfl

theorem abiCaseEncodeC :
    abiCaseInitialStore.host.handles.encode .tagged abiCaseTrueValue =
      .ok (abiCaseHandlesC, 1) := by
  rfl

theorem abiCaseSetC :
    (abiCaseMainFunction.toLocals []).set? 0 (.i32 1) =
      some abiCaseLocalsC := by
  native_decide

theorem abiCaseDecodedC :
    decodeArgs abiCaseStoreC.host.handles #[.tobject] [.i32 1] =
      .ok #[abiCaseTrueValue] := by
  rfl

theorem abiCaseTagC :
    getTag abiCaseStoreC.host.runtime abiCaseTrueValue = .ok 1 := by
  rfl

theorem abiCaseEncodeR :
    abiCaseStoreC.host.handles.encode .tobject abiCaseTrueValue =
      .ok (abiCaseHandlesC, 1) := by
  rfl

theorem abiCaseSetR :
    abiCaseLocalsC.set? 1 (.i32 1) = some abiCaseLocalsR := by
  native_decide

theorem abiCaseDeclC_kind :
    Fir.Wasm.letValueKind abiCaseDeclC = .ok .tagged := by
  simp [Fir.Wasm.letValueKind, abiCaseDeclC, letDecl, taggedType]

theorem abiCaseDeclFalse_kind :
    Fir.Wasm.letValueKind abiCaseDeclFalse = .ok .tobject := by
  simp [Fir.Wasm.letValueKind, abiCaseDeclFalse, letDecl, tobjectType]

theorem abiCaseDeclTrue_kind :
    Fir.Wasm.letValueKind abiCaseDeclTrue = .ok .tobject := by
  simp [Fir.Wasm.letValueKind, abiCaseDeclTrue, letDecl, tobjectType]

theorem abiCaseCompileArgs :
    Fir.Wasm.compileArgs abiCaseContext #[] = .ok ([], #[]) := by
  rfl

theorem abiCaseCompileC :
    Fir.Wasm.compileLetValue abiCaseContext abiCaseDeclC =
      .ok [.call (.runtime (.allocCtor trueInfo #[] .tagged))] := by
  simpa using compileLetValue_constructor
    (context := abiCaseContext) (decl := abiCaseDeclC)
    (info := trueInfo) (args := #[]) rfl (by native_decide)
    abiCaseDeclC_kind abiCaseCompileArgs

theorem abiCaseCompileFalse :
    Fir.Wasm.compileLetValue abiCaseContext abiCaseDeclFalse =
      .ok [.call (.runtime (.literal (.nat 0) .tobject))] :=
  compileLetValue_naturalLiteral rfl abiCaseDeclFalse_kind

theorem abiCaseCompileTrue :
    Fir.Wasm.compileLetValue abiCaseContext abiCaseDeclTrue =
      .ok [.call (.runtime (.literal (.nat 1) .tobject))] :=
  compileLetValue_naturalLiteral rfl abiCaseDeclTrue_kind

theorem abiCaseGetR :
    Fir.Wasm.getLocal abiCaseContext r = .ok (.localGet r, .tobject) := by
  simp [Fir.Wasm.getLocal, abiCaseContext, Fir.Wasm.findLocalKind?, r, c]

theorem abiCaseAllocCall_found :
    callIndex? abiCaseSourceModule
        (.runtime (.allocCtor trueInfo #[] .tagged)) = some 0 := by
  native_decide

theorem abiCaseGetTagCall_found :
    callIndex? abiCaseSourceModule (.runtime .getTag) = some 1 := by
  native_decide

theorem abiCaseLiteral0Call_found :
    callIndex? abiCaseSourceModule
        (.runtime (.literal (.nat 0) .tobject)) = some 2 := by
  native_decide

theorem abiCaseLiteral1Call_found :
    callIndex? abiCaseSourceModule
        (.runtime (.literal (.nat 1) .tobject)) = some 3 := by
  native_decide

theorem abiCaseC_found :
    findFVar? (functionBindings abiCaseSourceFunction) c = some 0 := by
  native_decide

theorem abiCaseR_found :
    findFVar? (functionBindings abiCaseSourceFunction) r = some 1 := by
  native_decide

theorem abiCaseArgumentsEvaluated :
    evalArgs [] #[] = .ok #[] := by
  unfold evalArgs
  simp
  rfl

theorem abiCaseFallbackCompiled :
    Fir.Wasm.compileCaseFallback abiCaseContext abiCaseCases.alts.toList =
      .ok [.unreachable] := by
  change Fir.Wasm.compileCaseFallbackWithM (Fir.Wasm.compileCode abiCaseContext)
    abiCaseCases.alts.toList = .ok [.unreachable]
  unfold Fir.Wasm.compileCaseFallbackWithM
  have missing :
      (abiCaseCases.alts.toList.find? Fir.Wasm.isDefaultAlt).isNone = true := by
    native_decide
  have noDefault :
      abiCaseCases.alts.toList.find? Fir.Wasm.isDefaultAlt = none := by
    cases found : abiCaseCases.alts.toList.find? Fir.Wasm.isDefaultAlt with
    | none => exact found
    | some alt =>
        rw [found] at missing
        contradiction
  rw [noDefault]
  rfl

theorem abiCaseStateC_related :
    StateRelated abiCaseSourceFunction {} abiCaseEnvC abiCaseStoreC
      abiCaseLocalsC := by
  have step := letStepSimulates_constructor
    (context := abiCaseContext)
    (sourceFunction := abiCaseSourceFunction)
    (module := abiCaseAdaptedModule.wasmModule)
    (hostEnv := abiCaseResolvedHosts.env)
    (spec := abiCaseResolvedHosts.spec)
    (id := 0) (imp := abiCaseImport 0)
    (decl := abiCaseDeclC) (info := trueInfo) (args := #[])
    (sourceEnv := []) (initial := abiCaseInitialStore)
    (locals := abiCaseMainFunction.toLocals [])
    (updated := abiCaseLocalsC) (indices := []) (physicalArgs := [])
    (semanticArgs := #[]) (nextRuntime := {})
    (sourceValue := abiCaseTrueValue) (resultIndex := 0)
    (fieldKinds := #[]) (resultKind := .tagged)
    (after := abiCaseHandlesC) (handle := 1)
    rfl abiCaseArgumentsEvaluated abiCaseAllocated abiCaseInitialState_related
    (by native_decide) (by native_decide) (by native_decide)
    abiCaseImport0_found abiCaseHostsSatisfy (by native_decide)
    (by simp [ResolvedHosts.spec, abiCaseResolvedHosts_operations])
    (by native_decide) (by native_decide) rfl rfl abiCaseEncodeC abiCaseSetC
  simpa [abiCaseEnvC, abiCaseStoreC, abiCaseDeclC, letDecl] using step.2.2.1

theorem abiCaseFalseBranch_adapted :
    CodeAdapted abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
      abiCaseFalseCode [.call 2, .localSet 1, .localGet 1, .ret] := by
  have valueAdapted :
      instructions abiCaseSourceModule abiCaseSourceFunction []
          [.call (.runtime (.literal (.nat 0) .tobject))] =
        .ok [.call 2] := by
    simp [instructions, instruction, abiCaseLiteral0Call_found]
    rfl
  have returned :
      CodeAdapted abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
        (.return r) [.localGet 1, .ret] := codeAdapted_return
    (sourceModule := abiCaseSourceModule)
    (sourceFunction := abiCaseSourceFunction) (labels := [])
    (resultIndex := 1) abiCaseGetR (by simpa [functionBindings] using abiCaseR_found)
  simpa [abiCaseFalseCode] using
    codeAdapted_let (resultIndex := 1) abiCaseCompileFalse valueAdapted
      (by simpa [functionBindings, abiCaseDeclFalse, letDecl] using abiCaseR_found)
      returned

theorem abiCaseTrueBranch_codeWP :
    CodeWP abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
      abiCaseAdaptedModule.wasmModule abiCaseResolvedHosts.env
      {} abiCaseEnvC abiCaseTrueCode
      [.call 3, .localSet 1, .localGet 1, .ret]
      abiCaseStoreC abiCaseLocalsC []
      (ReturnPost {} abiCaseTrueValue .tobject []) := by
  apply codeWP_naturalLiteral_return
    (spec := abiCaseResolvedHosts.spec)
    (id := 3) (imp := abiCaseImport 3)
    (decl := abiCaseDeclTrue) (resultIndex := 1) (value := 1)
    (after := abiCaseHandlesC) (handle := 1) (updated := abiCaseLocalsR)
  · rfl
  · exact abiCaseCompileTrue
  · exact abiCaseGetR
  · native_decide
  · native_decide
  · native_decide
  · exact abiCaseStateC_related
  · exact abiCaseImport3_found
  · exact abiCaseHostsSatisfy
  · native_decide
  · simp [ResolvedHosts.spec, abiCaseResolvedHosts_operations]
  · native_decide
  · native_decide
  · simpa [abiCaseTrueValue, literal, maxTaggedPayload] using abiCaseEncodeR
  · exact abiCaseSetR

/-- Local W4 proof for allocation followed by the generated two-test case chain. -/
theorem abiCaseMain_codeWP :
    CodeWP abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
      abiCaseAdaptedModule.wasmModule abiCaseResolvedHosts.env
      {} [] abiCaseCode abiCaseMainFunction.body abiCaseInitialStore
      (abiCaseMainFunction.toLocals []) []
      (ReturnPost {} abiCaseTrueValue .tobject []) := by
  let Q : Wasm.Assertion RuntimeHost := ReturnPost {} abiCaseTrueValue .tobject []
  have trueBranch :
      CodeWP abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
        abiCaseAdaptedModule.wasmModule abiCaseResolvedHosts.env
        {} abiCaseEnvC abiCaseTrueCode
        [.call 3, .localSet 1, .localGet 1, .ret]
        abiCaseStoreC abiCaseLocalsC []
        (CaseResumePost abiCaseAdaptedModule.wasmModule
          abiCaseResolvedHosts.env []
          (CaseResumePost abiCaseAdaptedModule.wasmModule
            abiCaseResolvedHosts.env [] Q []) []) := by
    apply abiCaseTrueBranch_codeWP.conseq
    intro continuation returned
    rcases returned with ⟨store, physical, rfl, runtimeEq, decoded⟩
    exact ⟨store, physical, rfl, runtimeEq, decoded⟩
  have fallbackAdapted :
      CaseChainAdapted abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
        c [] [.unreachable] [.unreachable] := by
    apply caseChainAdapted_nil
    simp [instructions, instruction]
    rfl
  have trueChain :
      CaseChainWP abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
        abiCaseAdaptedModule.wasmModule abiCaseResolvedHosts.env
        {} abiCaseEnvC c
        [.ctorAlt trueInfo abiCaseTrueCode] [.unreachable]
        [.localGet 0, .call 1, .const 1, .eq,
          .iff 0 0
            [.call 3, .localSet 1, .localGet 1, .ret]
            [.unreachable]]
        abiCaseStoreC abiCaseLocalsC []
        (CaseResumePost abiCaseAdaptedModule.wasmModule
          abiCaseResolvedHosts.env [] Q []) := by
    apply caseChainWP_constructor_hit
      (spec := abiCaseResolvedHosts.spec)
      (imp := abiCaseImport 1) (sourceObject := abiCaseTrueValue)
      (actualTag := 1) (handle := 1)
    · native_decide
    · exact trueBranch
    · exact fallbackAdapted
    · rfl
    · native_decide
    · native_decide
    · native_decide
    · exact abiCaseImport1_found
    · exact abiCaseHostsSatisfy
    · native_decide
    · simp [ResolvedHosts.spec, abiCaseResolvedHosts_operations]
    · native_decide
    · native_decide
    · exact abiCaseDecodedC
    · exact abiCaseTagC
    · native_decide
    · native_decide
  have wholeChain :
      CaseChainWP abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
        abiCaseAdaptedModule.wasmModule abiCaseResolvedHosts.env
        {} abiCaseEnvC c abiCaseCases.alts.toList [.unreachable]
        [.localGet 0, .call 1, .const 0, .eq,
          .iff 0 0
            [.call 2, .localSet 1, .localGet 1, .ret]
            [.localGet 0, .call 1, .const 1, .eq,
              .iff 0 0
                [.call 3, .localSet 1, .localGet 1, .ret]
                [.unreachable]]]
        abiCaseStoreC abiCaseLocalsC [] Q := by
    apply caseChainWP_constructor_miss
      (spec := abiCaseResolvedHosts.spec)
      (imp := abiCaseImport 1) (sourceObject := abiCaseTrueValue)
      (actualTag := 1) (handle := 1)
    · native_decide
    · exact abiCaseFalseBranch_adapted
    · simpa [abiCaseCases] using trueChain
    · native_decide
    · native_decide
    · native_decide
    · native_decide
    · exact abiCaseImport1_found
    · exact abiCaseHostsSatisfy
    · native_decide
    · simp [ResolvedHosts.spec, abiCaseResolvedHosts_operations]
    · native_decide
    · native_decide
    · exact abiCaseDecodedC
    · exact abiCaseTagC
    · native_decide
    · native_decide
  have casesCorrect :
      CodeWP abiCaseContext abiCaseSourceModule abiCaseSourceFunction []
        abiCaseAdaptedModule.wasmModule abiCaseResolvedHosts.env
        {} abiCaseEnvC (.cases abiCaseCases)
        [.localGet 0, .call 1, .const 0, .eq,
          .iff 0 0
            [.call 2, .localSet 1, .localGet 1, .ret]
            [.localGet 0, .call 1, .const 1, .eq,
              .iff 0 0
                [.call 3, .localSet 1, .localGet 1, .ret]
                [.unreachable]]]
        abiCaseStoreC abiCaseLocalsC [] Q :=
    codeWP_cases abiCaseFallbackCompiled wholeChain
  rw [abiCaseMain_body]
  apply codeWP_constructor_let
    (spec := abiCaseResolvedHosts.spec)
    (id := 0) (imp := abiCaseImport 0) (info := trueInfo) (args := #[])
    (fvarIds := []) (indices := []) (physicalArgs := [])
    (semanticArgs := #[]) (nextRuntime := {})
    (sourceValue := abiCaseTrueValue) (resultIndex := 0)
    (fieldKinds := #[]) (resultKind := .tagged)
    (after := abiCaseHandlesC) (handle := 1)
  · rfl
  · exact abiCaseCompileC
  · native_decide
  · native_decide
  · exact abiCaseArgumentsEvaluated
  · exact abiCaseAllocated
  · exact abiCaseInitialState_related
  · native_decide
  · native_decide
  · native_decide
  · exact abiCaseImport0_found
  · exact abiCaseHostsSatisfy
  · native_decide
  · simp [ResolvedHosts.spec, abiCaseResolvedHosts_operations]
  · native_decide
  · native_decide
  · rfl
  · rfl
  · exact abiCaseEncodeC
  · exact abiCaseSetC
  · simpa [abiCaseCode, abiCaseEnvC, abiCaseStoreC, abiCaseDeclC, letDecl]
      using casesCorrect

theorem abiCaseObservation_related :
    compareObservations
        (ReturnedObservation {} abiCaseTrueValue)
        (.returned abiCaseTrueValue {}) =
      .related (ReturnedObservation {} abiCaseTrueValue)
        (.returned abiCaseTrueValue {}) := by
  unfold compareObservations ReturnedObservation
  simp only [TargetObservation.toSource?]
  have noDifferences :
      observationDifferences
          { outcome := .returned abiCaseTrueValue
            heap := ({} : RuntimeState).heap
            world := ({} : RuntimeState).world
            trace := ({} : RuntimeState).trace }
          { outcome := .returned abiCaseTrueValue
            heap := ({} : RuntimeState).heap
            world := ({} : RuntimeState).world
            trace := ({} : RuntimeState).trace } = #[] := by
    native_decide
  rw [noDifferences]
  rfl

/-- End-to-end W3/W4 theorem for the generated explicit constructor case. -/
theorem abiCaseMain_export_correct :
    ExportTerminatesWith abiCaseResolvedHosts.env
      abiCaseAdaptedModule.wasmModule "main" abiCaseInitialStore []
      (RelatedPost #[.tobject]
        (ReturnedObservation {} abiCaseTrueValue)) := by
  apply CodeWP.toExportTerminatesWithRelated_of_return
    abiCaseMain_exported abiCaseMain_notImport abiCaseMain_found rfl
    abiCaseMain_resultCount abiCaseObservation_related
  simpa [abiCaseInitialStore] using abiCaseMain_codeWP

end FirTalos.Correctness
