import FirTalos.Correctness.FunctionCaseExample

namespace FirTalos.Correctness

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples

private def defaultCaseBodyCheck : Wasm.Program → Bool
  | [.call alloc, .localSet cIndex,
      .localGet cLoad, .call getTag, .const falseTag, .eq,
      .iff depth results
        [.call literal0, .localSet falseIndex, .localGet falseLoad, .ret]
        [.call literal5, .localSet defaultIndex, .localGet defaultLoad, .ret],
      .unreachable] =>
      alloc == 0 && cIndex == 0 && cLoad == 0 && getTag == 1 &&
      falseTag == 0 && depth == 0 && results == 0 &&
      literal0 == 2 && falseIndex == 2 && falseLoad == 2 &&
      literal5 == 3 && defaultIndex == 1 && defaultLoad == 1
  | _ => false

private theorem defaultCaseBody_eq_of_check {body : Wasm.Program}
    (checked : defaultCaseBodyCheck body = true) :
    body = [.call 0, .localSet 0,
      .localGet 0, .call 1, .const 0, .eq,
      .iff 0 0
        [.call 2, .localSet 2, .localGet 2, .ret]
        [.call 3, .localSet 1, .localGet 1, .ret],
      .unreachable] := by
  unfold defaultCaseBodyCheck at checked
  split at checked <;> simp_all

private def defaultCaseOperationsCheck : List HostOperation → Bool
  | [.allocCtor info fields resultKind, .getTag,
      .naturalLiteral falseValue falseKind,
      .naturalLiteral defaultValue defaultKind] =>
      decide (info = trueInfo) && fields == #[] && resultKind == .tagged &&
      falseValue == 0 && falseKind == .tobject &&
      defaultValue == 5 && defaultKind == .tobject
  | _ => false

private theorem defaultCaseOperations_eq_of_check
    {operations : List HostOperation}
    (checked : defaultCaseOperationsCheck operations = true) :
    operations = [
      .allocCtor trueInfo #[] .tagged,
      .getTag,
      .naturalLiteral 0 .tobject,
      .naturalLiteral 5 .tobject] := by
  unfold defaultCaseOperationsCheck at checked
  split at checked <;> simp_all

/-- Checked symbolic module for W3's default-case fixture. -/
def abiDefaultCaseSourceModule : Fir.Wasm.Module :=
  match Fir.Wasm.lowerSupported abiDefaultCaseProgram with
  | .ok source => source
  | .error _ => default

theorem abiDefaultCaseSourceModule_lowered :
    Fir.Wasm.lowerSupported abiDefaultCaseProgram =
      .ok abiDefaultCaseSourceModule := by
  have success : (Fir.Wasm.lowerSupported abiDefaultCaseProgram).isOk = true := by
    native_decide
  cases lowered : Fir.Wasm.lowerSupported abiDefaultCaseProgram with
  | error error =>
      rw [lowered] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok source => simp [abiDefaultCaseSourceModule, lowered]

def abiDefaultCaseSourceFunction : Fir.Wasm.Function :=
  match abiDefaultCaseSourceModule.functions[0]? with
  | some function => function
  | none => default

theorem abiDefaultCaseSourceFunction_found :
    abiDefaultCaseSourceModule.functions[0]? =
      some abiDefaultCaseSourceFunction := by
  have present : abiDefaultCaseSourceModule.functions[0]?.isSome = true := by
    native_decide
  cases found : abiDefaultCaseSourceModule.functions[0]? with
  | none => simp [found] at present
  | some function => simp [abiDefaultCaseSourceFunction, found]

def abiDefaultCaseDeclC : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl c taggedType (.ctor trueInfo #[])

def abiDefaultCaseDeclDefault : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl r tobjectType (.lit (.nat 5))

def abiDefaultCaseDeclFalse : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl u tobjectType (.lit (.nat 0))

def abiDefaultCaseDefaultCode : Lean.Compiler.LCNF.Code .impure :=
  .let abiDefaultCaseDeclDefault (.return r)

def abiDefaultCaseFalseCode : Lean.Compiler.LCNF.Code .impure :=
  .let abiDefaultCaseDeclFalse (.return u)

def abiDefaultCaseCases : Lean.Compiler.LCNF.Cases .impure :=
  .mk ``Bool tobjectType c #[
    .default abiDefaultCaseDefaultCode,
    .ctorAlt falseInfo abiDefaultCaseFalseCode]

def abiDefaultCaseCode : Lean.Compiler.LCNF.Code .impure :=
  .let abiDefaultCaseDeclC (.cases abiDefaultCaseCases)

def abiDefaultCaseContext : Fir.Wasm.Context :=
  { program := abiDefaultCaseProgram
    localKinds := [(u, .tobject), (r, .tobject), (c, .tagged)] }

private def emptyDefaultCaseAdaptedModule : AdaptedModule :=
  { wasmModule := default, sourceMap := default }

def abiDefaultCaseAdaptedModule : AdaptedModule :=
  match adapt abiDefaultCaseSourceModule with
  | .ok target => target
  | .error _ => emptyDefaultCaseAdaptedModule

theorem abiDefaultCaseAdaptedModule_adapted :
    adapt abiDefaultCaseSourceModule = .ok abiDefaultCaseAdaptedModule := by
  have success : (adapt abiDefaultCaseSourceModule).isOk = true := by
    native_decide
  cases adapted : adapt abiDefaultCaseSourceModule with
  | error error =>
      rw [adapted] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok target => simp [abiDefaultCaseAdaptedModule, adapted]

def abiDefaultCaseResolvedHosts : ResolvedHosts :=
  match resolveHosts abiDefaultCaseSourceModule with
  | .ok resolved => resolved
  | .error _ => { operations := [] }

theorem abiDefaultCaseResolvedHosts_resolved :
    resolveHosts abiDefaultCaseSourceModule = .ok abiDefaultCaseResolvedHosts := by
  have success : (resolveHosts abiDefaultCaseSourceModule).isOk = true := by
    native_decide
  cases resolved : resolveHosts abiDefaultCaseSourceModule with
  | error error =>
      rw [resolved] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok hosts => simp [abiDefaultCaseResolvedHosts, resolved]

theorem abiDefaultCaseResolvedHosts_operations :
    abiDefaultCaseResolvedHosts.operations = [
      .allocCtor trueInfo #[] .tagged,
      .getTag,
      .naturalLiteral 0 .tobject,
      .naturalLiteral 5 .tobject] := by
  apply defaultCaseOperations_eq_of_check
  native_decide

def abiDefaultCaseMainFunction : Wasm.Function :=
  match abiDefaultCaseAdaptedModule.wasmModule.funcs[
      4 - abiDefaultCaseAdaptedModule.wasmModule.imports.length]? with
  | some function => function
  | none => default

theorem abiDefaultCaseMain_found :
    abiDefaultCaseAdaptedModule.wasmModule.funcs[
        4 - abiDefaultCaseAdaptedModule.wasmModule.imports.length]? =
      some abiDefaultCaseMainFunction := by
  have present :
      (abiDefaultCaseAdaptedModule.wasmModule.funcs[
        4 - abiDefaultCaseAdaptedModule.wasmModule.imports.length]?).isSome =
          true := by
    native_decide
  cases found : abiDefaultCaseAdaptedModule.wasmModule.funcs[
      4 - abiDefaultCaseAdaptedModule.wasmModule.imports.length]? with
  | none => simp [found] at present
  | some function => simp [abiDefaultCaseMainFunction, found]

theorem abiDefaultCaseMain_body :
    abiDefaultCaseMainFunction.body = [.call 0, .localSet 0,
      .localGet 0, .call 1, .const 0, .eq,
      .iff 0 0
        [.call 2, .localSet 2, .localGet 2, .ret]
        [.call 3, .localSet 1, .localGet 1, .ret],
      .unreachable] := by
  apply defaultCaseBody_eq_of_check
  native_decide

/-- The compositional compiler body, before the adapter's validation marker. -/
def abiDefaultCaseMainCore : Wasm.Program :=
  [.call 0, .localSet 0,
    .localGet 0, .call 1, .const 0, .eq,
    .iff 0 0
      [.call 2, .localSet 2, .localGet 2, .ret]
      [.call 3, .localSet 1, .localGet 1, .ret]]

theorem abiDefaultCaseMain_body_eq_core :
    abiDefaultCaseMainFunction.body =
      abiDefaultCaseMainCore ++ [.unreachable] := by
  rw [abiDefaultCaseMain_body]
  rfl

theorem abiDefaultCaseMain_exported :
    abiDefaultCaseAdaptedModule.wasmModule.findExport "main" = some 4 := by
  native_decide

theorem abiDefaultCaseMain_notImport :
    abiDefaultCaseAdaptedModule.wasmModule.imports[4]? = none := by
  native_decide

theorem abiDefaultCaseMain_resultCount :
    abiDefaultCaseMainFunction.results.length = 1 := by
  native_decide

theorem abiDefaultCaseHostsMatch :
    HostsMatch abiDefaultCaseResolvedHosts abiDefaultCaseSourceModule := by
  unfold HostsMatch
  native_decide

/-- Checked whole-pipeline package for the default-case export. -/
def abiDefaultCaseSupportedExport :
    SupportedExport abiDefaultCaseProgram abiDefaultCaseContext
      abiDefaultCaseCode abiDefaultCaseSourceModule
      abiDefaultCaseSourceFunction abiDefaultCaseAdaptedModule
      abiDefaultCaseResolvedHosts "main" :=
  { programSupported := by
      unfold Fir.Wasm.WasmSupported
      native_decide
    contextProgram := rfl
    lowered := abiDefaultCaseSourceModule_lowered
    sourceFunctionIndex := 0
    sourceFunctionFound := abiDefaultCaseSourceFunction_found
    adapted := abiDefaultCaseAdaptedModule_adapted
    hostsResolved := abiDefaultCaseResolvedHosts_resolved
    hostsMatch := abiDefaultCaseHostsMatch
    targetFunctionIndex := 4
    targetFunction := abiDefaultCaseMainFunction
    exported := abiDefaultCaseMain_exported
    notImport := abiDefaultCaseMain_notImport
    targetFunctionFound := abiDefaultCaseMain_found
    singleResult := abiDefaultCaseMain_resultCount }

theorem abiDefaultCaseHostsSatisfy :
    abiDefaultCaseResolvedHosts.env.Satisfies
      abiDefaultCaseAdaptedModule.wasmModule abiDefaultCaseResolvedHosts.spec :=
  abiDefaultCaseSupportedExport.hostsSatisfy

def abiDefaultCaseTrueValue : Value :=
  .object (.tagged (UInt64.ofNat 1))

def abiDefaultCaseValue5 : Value :=
  .object (.tagged (UInt64.ofNat 5))

def abiDefaultCaseHandlesC : HandleTable :=
  { entries := [(1, abiDefaultCaseTrueValue)], next := 2 }

def abiDefaultCaseHandlesR : HandleTable :=
  { entries := [
      (2, abiDefaultCaseValue5),
      (1, abiDefaultCaseTrueValue)]
    next := 3 }

def abiDefaultCaseInitialStore : Wasm.Store RuntimeHost :=
  abiDefaultCaseAdaptedModule.wasmModule.initialStore

def abiDefaultCaseStoreC : Wasm.Store RuntimeHost :=
  successfulHostStore abiDefaultCaseInitialStore {} abiDefaultCaseHandlesC

def abiDefaultCaseStoreR : Wasm.Store RuntimeHost :=
  successfulHostStore abiDefaultCaseStoreC {} abiDefaultCaseHandlesR

def abiDefaultCaseLocalsC : Wasm.Locals :=
  { locals := [.i32 1, .i32 0, .i32 0] }

def abiDefaultCaseLocalsR : Wasm.Locals :=
  { locals := [.i32 1, .i32 2, .i32 0] }

def abiDefaultCaseEnvC : Env :=
  bind [] c abiDefaultCaseTrueValue

def abiDefaultCaseEnvR : Env :=
  bind abiDefaultCaseEnvC r abiDefaultCaseValue5

def abiDefaultCaseImport (index : Nat) : Wasm.ImportDecl :=
  abiDefaultCaseAdaptedModule.wasmModule.imports[index]!

theorem abiDefaultCaseImport0_found :
    abiDefaultCaseAdaptedModule.wasmModule.imports[0]? =
      some (abiDefaultCaseImport 0) := by
  native_decide

theorem abiDefaultCaseImport1_found :
    abiDefaultCaseAdaptedModule.wasmModule.imports[1]? =
      some (abiDefaultCaseImport 1) := by
  native_decide

theorem abiDefaultCaseImport2_found :
    abiDefaultCaseAdaptedModule.wasmModule.imports[2]? =
      some (abiDefaultCaseImport 2) := by
  native_decide

theorem abiDefaultCaseImport3_found :
    abiDefaultCaseAdaptedModule.wasmModule.imports[3]? =
      some (abiDefaultCaseImport 3) := by
  native_decide

theorem abiDefaultCaseInitialState_related :
    StateRelated abiDefaultCaseSourceFunction {} [] abiDefaultCaseInitialStore
      (abiDefaultCaseMainFunction.toLocals []) := by
  unfold StateRelated
  refine ⟨rfl, rfl, rfl, handleTableInvariant_empty, ?_⟩
  intro fvar value found
  simp [lookup] at found

theorem abiDefaultCaseAllocated :
    allocCtor abiDefaultCaseInitialStore.host.runtime trueInfo #[] =
      .ok ({}, abiDefaultCaseTrueValue) := by
  rfl

theorem abiDefaultCaseEncodeC :
    abiDefaultCaseInitialStore.host.handles.encode .tagged
        abiDefaultCaseTrueValue =
      .ok (abiDefaultCaseHandlesC, 1) := by
  rfl

theorem abiDefaultCaseSetC :
    (abiDefaultCaseMainFunction.toLocals []).set? 0 (.i32 1) =
      some abiDefaultCaseLocalsC := by
  native_decide

theorem abiDefaultCaseDecodedC :
    decodeArgs abiDefaultCaseStoreC.host.handles #[.tobject] [.i32 1] =
      .ok #[abiDefaultCaseTrueValue] := by
  rfl

theorem abiDefaultCaseTagC :
    getTag abiDefaultCaseStoreC.host.runtime abiDefaultCaseTrueValue =
      .ok 1 := by
  rfl

theorem abiDefaultCaseEncodeR :
    abiDefaultCaseStoreC.host.handles.encode .tobject abiDefaultCaseValue5 =
      .ok (abiDefaultCaseHandlesR, 2) := by
  rfl

theorem abiDefaultCaseSetR :
    abiDefaultCaseLocalsC.set? 1 (.i32 2) =
      some abiDefaultCaseLocalsR := by
  native_decide

theorem abiDefaultCaseDeclC_kind :
    Fir.Wasm.letValueKind abiDefaultCaseDeclC = .ok .tagged := by
  simp [Fir.Wasm.letValueKind, abiDefaultCaseDeclC, letDecl, taggedType]

theorem abiDefaultCaseDeclDefault_kind :
    Fir.Wasm.letValueKind abiDefaultCaseDeclDefault = .ok .tobject := by
  simp [Fir.Wasm.letValueKind, abiDefaultCaseDeclDefault, letDecl, tobjectType]

theorem abiDefaultCaseDeclFalse_kind :
    Fir.Wasm.letValueKind abiDefaultCaseDeclFalse = .ok .tobject := by
  simp [Fir.Wasm.letValueKind, abiDefaultCaseDeclFalse, letDecl, tobjectType]

theorem abiDefaultCaseCompileArgs :
    Fir.Wasm.compileArgs abiDefaultCaseContext #[] = .ok ([], #[]) := by
  rfl

theorem abiDefaultCaseCompileC :
    Fir.Wasm.compileLetValue abiDefaultCaseContext abiDefaultCaseDeclC =
      .ok [.call (.runtime (.allocCtor trueInfo #[] .tagged))] := by
  simpa using compileLetValue_constructor
    (context := abiDefaultCaseContext) (decl := abiDefaultCaseDeclC)
    (info := trueInfo) (args := #[]) rfl (by native_decide)
    abiDefaultCaseDeclC_kind abiDefaultCaseCompileArgs

theorem abiDefaultCaseCompileDefault :
    Fir.Wasm.compileLetValue abiDefaultCaseContext abiDefaultCaseDeclDefault =
      .ok [.call (.runtime (.literal (.nat 5) .tobject))] :=
  compileLetValue_naturalLiteral rfl abiDefaultCaseDeclDefault_kind

theorem abiDefaultCaseCompileFalse :
    Fir.Wasm.compileLetValue abiDefaultCaseContext abiDefaultCaseDeclFalse =
      .ok [.call (.runtime (.literal (.nat 0) .tobject))] :=
  compileLetValue_naturalLiteral rfl abiDefaultCaseDeclFalse_kind

theorem abiDefaultCaseGetR :
    Fir.Wasm.getLocal abiDefaultCaseContext r =
      .ok (.localGet r, .tobject) := by
  simp [Fir.Wasm.getLocal, abiDefaultCaseContext, Fir.Wasm.findLocalKind?,
    u, r, c]

theorem abiDefaultCaseLiteral0Call_found :
    callIndex? abiDefaultCaseSourceModule
        (.runtime (.literal (.nat 0) .tobject)) = some 2 := by
  native_decide

theorem abiDefaultCaseLiteral5Call_found :
    callIndex? abiDefaultCaseSourceModule
        (.runtime (.literal (.nat 5) .tobject)) = some 3 := by
  native_decide

theorem abiDefaultCaseR_found :
    findFVar? (functionBindings abiDefaultCaseSourceFunction) r = some 1 := by
  native_decide

theorem abiDefaultCaseU_found :
    findFVar? (functionBindings abiDefaultCaseSourceFunction) u = some 2 := by
  native_decide

theorem abiDefaultCaseCtorStep :
    LetStepSimulates abiDefaultCaseContext abiDefaultCaseSourceFunction
      abiDefaultCaseAdaptedModule.wasmModule abiDefaultCaseResolvedHosts.env
      abiDefaultCaseDeclC [.call 0] {} {} [] abiDefaultCaseTrueValue
      abiDefaultCaseInitialStore abiDefaultCaseStoreC
      (abiDefaultCaseMainFunction.toLocals []) abiDefaultCaseLocalsC 0 := by
  apply letStepSimulates_constructor
    (context := abiDefaultCaseContext)
    (sourceFunction := abiDefaultCaseSourceFunction)
    (module := abiDefaultCaseAdaptedModule.wasmModule)
    (hostEnv := abiDefaultCaseResolvedHosts.env)
    (spec := abiDefaultCaseResolvedHosts.spec)
    (id := 0) (imp := abiDefaultCaseImport 0)
    (decl := abiDefaultCaseDeclC) (info := trueInfo) (args := #[])
    (sourceEnv := []) (initial := abiDefaultCaseInitialStore)
    (locals := abiDefaultCaseMainFunction.toLocals [])
    (updated := abiDefaultCaseLocalsC) (indices := []) (physicalArgs := [])
    (semanticArgs := #[]) (nextRuntime := {})
    (sourceValue := abiDefaultCaseTrueValue) (resultIndex := 0)
    (fieldKinds := #[]) (resultKind := .tagged)
    (after := abiDefaultCaseHandlesC) (handle := 1)
    rfl abiCaseArgumentsEvaluated abiDefaultCaseAllocated
    abiDefaultCaseInitialState_related
    (by native_decide) (by native_decide) (by native_decide)
    abiDefaultCaseImport0_found abiDefaultCaseHostsSatisfy (by native_decide)
    (by simp [ResolvedHosts.spec, abiDefaultCaseResolvedHosts_operations])
    (by native_decide) (by native_decide) rfl rfl abiDefaultCaseEncodeC
    abiDefaultCaseSetC

theorem abiDefaultCaseStateC_related :
    StateRelated abiDefaultCaseSourceFunction {} abiDefaultCaseEnvC
      abiDefaultCaseStoreC abiDefaultCaseLocalsC := by
  simpa [abiDefaultCaseEnvC, abiDefaultCaseStoreC, abiDefaultCaseDeclC, letDecl]
    using abiDefaultCaseCtorStep.2.2.1

theorem abiDefaultCaseFalseBranch_adapted :
    CodeAdapted abiDefaultCaseContext abiDefaultCaseSourceModule
      abiDefaultCaseSourceFunction [] abiDefaultCaseFalseCode
      [.call 2, .localSet 2, .localGet 2, .ret] := by
  have valueAdapted :
      instructions abiDefaultCaseSourceModule abiDefaultCaseSourceFunction []
          [.call (.runtime (.literal (.nat 0) .tobject))] =
        .ok [.call 2] := by
    simp [instructions, instruction, abiDefaultCaseLiteral0Call_found]
    rfl
  have localU :
      Fir.Wasm.getLocal abiDefaultCaseContext u =
        .ok (.localGet u, .tobject) := by
    simp [Fir.Wasm.getLocal, abiDefaultCaseContext, Fir.Wasm.findLocalKind?,
      u, r, c]
  have returned :
      CodeAdapted abiDefaultCaseContext abiDefaultCaseSourceModule
        abiDefaultCaseSourceFunction [] (.return u) [.localGet 2, .ret] :=
    codeAdapted_return (resultIndex := 2) localU
      (by simpa [functionBindings] using abiDefaultCaseU_found)
  simpa [abiDefaultCaseFalseCode] using
    codeAdapted_let (resultIndex := 2) abiDefaultCaseCompileFalse valueAdapted
      (by simpa [functionBindings, abiDefaultCaseDeclFalse, letDecl]
        using abiDefaultCaseU_found)
      returned

theorem abiDefaultCaseDefaultBranch_simulation :
    CodeSimulation abiDefaultCaseContext abiDefaultCaseSourceModule
      abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
      abiDefaultCaseResolvedHosts.env {} abiDefaultCaseEnvC
      abiDefaultCaseDefaultCode [.call 3, .localSet 1, .localGet 1, .ret]
      abiDefaultCaseStoreC abiDefaultCaseLocalsC {} abiDefaultCaseValue5
      .tobject := by
  have valueAdapted :
      instructions abiDefaultCaseSourceModule abiDefaultCaseSourceFunction []
          [.call (.runtime (.literal (.nat 5) .tobject))] =
        .ok [.call 3] := by
    simp [instructions, instruction, abiDefaultCaseLiteral5Call_found]
    rfl
  have step := letStepSimulates_naturalLiteral
    (context := abiDefaultCaseContext)
    (sourceFunction := abiDefaultCaseSourceFunction)
    (module := abiDefaultCaseAdaptedModule.wasmModule)
    (hostEnv := abiDefaultCaseResolvedHosts.env)
    (spec := abiDefaultCaseResolvedHosts.spec)
    (id := 3) (imp := abiDefaultCaseImport 3)
    (decl := abiDefaultCaseDeclDefault) (resultIndex := 1) (value := 5)
    (after := abiDefaultCaseHandlesR) (handle := 2)
    (updated := abiDefaultCaseLocalsR)
    rfl abiDefaultCaseStateC_related (by native_decide) (by native_decide)
    abiDefaultCaseImport3_found abiDefaultCaseHostsSatisfy (by native_decide)
    (by simp [ResolvedHosts.spec, abiDefaultCaseResolvedHosts_operations])
    (by native_decide) (by native_decide)
    (by simpa [abiDefaultCaseValue5, literal, maxTaggedPayload] using
      abiDefaultCaseEncodeR)
    abiDefaultCaseSetR
  simp only [abiDefaultCaseDefaultCode]
  apply CodeSimulation.letValue abiDefaultCaseCompileDefault valueAdapted
    (by native_decide) step
  apply CodeSimulation.ret abiDefaultCaseGetR
    (by native_decide) (by native_decide)
    (lookup_bind_self abiDefaultCaseEnvC r abiDefaultCaseValue5)
  simpa [abiDefaultCaseDeclDefault, letDecl, abiDefaultCaseValue5, literal,
    maxTaggedPayload, successfulHostStore, abiDefaultCaseStoreR] using
    step.2.2.1

theorem abiDefaultCaseDefaultBranch_codeWP :
    CodeWP abiDefaultCaseContext abiDefaultCaseSourceModule
      abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
      abiDefaultCaseResolvedHosts.env {} abiDefaultCaseEnvC
      abiDefaultCaseDefaultCode [.call 3, .localSet 1, .localGet 1, .ret]
      abiDefaultCaseStoreC abiDefaultCaseLocalsC []
      (ReturnPost {} abiDefaultCaseValue5 .tobject []) :=
  abiDefaultCaseDefaultBranch_simulation.toCodeWP

/-- Path-sensitive transformer for the source-selected default branch. -/
theorem abiDefaultCaseCasesStep :
    CasesStepSimulates abiDefaultCaseContext abiDefaultCaseSourceModule
      abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
      abiDefaultCaseResolvedHosts.env {} abiDefaultCaseEnvC
      abiDefaultCaseCases abiDefaultCaseDefaultCode
      [.localGet 0, .call 1, .const 0, .eq,
        .iff 0 0
          [.call 2, .localSet 2, .localGet 2, .ret]
          [.call 3, .localSet 1, .localGet 1, .ret]]
      [.call 3, .localSet 1, .localGet 1, .ret]
      abiDefaultCaseStoreC abiDefaultCaseLocalsC {} abiDefaultCaseValue5
      .tobject := by
  constructor
  · refine ⟨abiDefaultCaseTrueValue, 1, ?_, abiDefaultCaseTagC, ?_⟩
    · have sameName : c.name = abiDefaultCaseCases.discr.name := by
        native_decide
      simp [lookupValue, abiDefaultCaseEnvC, Fir.LeanIR.Impure.bind, lookup,
        sameName]
    · rfl
  · intro selectedCorrect
    let Q : Wasm.Assertion RuntimeHost :=
      ReturnPost {} abiDefaultCaseValue5 .tobject []
    have defaultResumed :
        CodeWP abiDefaultCaseContext abiDefaultCaseSourceModule
          abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
          abiDefaultCaseResolvedHosts.env {} abiDefaultCaseEnvC
          abiDefaultCaseDefaultCode [.call 3, .localSet 1, .localGet 1, .ret]
          abiDefaultCaseStoreC abiDefaultCaseLocalsC []
          (CaseResumePost abiDefaultCaseAdaptedModule.wasmModule
            abiDefaultCaseResolvedHosts.env [] Q []) := by
      apply selectedCorrect.conseq
      intro continuation returned
      rcases returned with ⟨store, physical, rfl, runtimeEq, decoded⟩
      exact ⟨store, physical, rfl, runtimeEq, decoded⟩
    have defaultFound :
        abiDefaultCaseCases.alts.toList.find? Fir.Wasm.isDefaultAlt =
          some (.default abiDefaultCaseDefaultCode) := by
      rfl
    have fallbackAdapted :
        CaseFallbackAdapted abiDefaultCaseContext abiDefaultCaseSourceModule
          abiDefaultCaseSourceFunction [] abiDefaultCaseCases.alts.toList
          [.call 3, .localSet 1, .localGet 1, .ret] :=
      caseFallbackAdapted_default defaultFound selectedCorrect.1
    rcases fallbackAdapted with
      ⟨fallback, fallbackCompiled, fallbackTarget⟩
    have fallbackChain :
        CaseChainWP abiDefaultCaseContext abiDefaultCaseSourceModule
          abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
          abiDefaultCaseResolvedHosts.env {} abiDefaultCaseEnvC c [] fallback
          [.call 3, .localSet 1, .localGet 1, .ret]
          abiDefaultCaseStoreC abiDefaultCaseLocalsC []
          (CaseResumePost abiDefaultCaseAdaptedModule.wasmModule
            abiDefaultCaseResolvedHosts.env [] Q []) :=
      caseChainWP_nil fallbackTarget defaultResumed.2.1 defaultResumed.2.2
    have falseChain :
        CaseChainWP abiDefaultCaseContext abiDefaultCaseSourceModule
          abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
          abiDefaultCaseResolvedHosts.env {} abiDefaultCaseEnvC c
          [.ctorAlt falseInfo abiDefaultCaseFalseCode] fallback
          [.localGet 0, .call 1, .const 0, .eq,
            .iff 0 0
              [.call 2, .localSet 2, .localGet 2, .ret]
              [.call 3, .localSet 1, .localGet 1, .ret]]
          abiDefaultCaseStoreC abiDefaultCaseLocalsC [] Q := by
      apply caseChainWP_constructor_miss
        (spec := abiDefaultCaseResolvedHosts.spec)
        (imp := abiDefaultCaseImport 1)
        (sourceObject := abiDefaultCaseTrueValue)
        (actualTag := 1) (handle := 1)
      · native_decide
      · native_decide
      · exact abiDefaultCaseFalseBranch_adapted
      · exact fallbackChain
      · native_decide
      · native_decide
      · native_decide
      · native_decide
      · exact abiDefaultCaseImport1_found
      · exact abiDefaultCaseHostsSatisfy
      · native_decide
      · simp [ResolvedHosts.spec, abiDefaultCaseResolvedHosts_operations]
      · native_decide
      · native_decide
      · exact abiDefaultCaseDecodedC
      · exact abiDefaultCaseTagC
      · native_decide
      · native_decide
    have wholeChain :
        CaseChainWP abiDefaultCaseContext abiDefaultCaseSourceModule
          abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
          abiDefaultCaseResolvedHosts.env {} abiDefaultCaseEnvC c
          abiDefaultCaseCases.alts.toList fallback
          [.localGet 0, .call 1, .const 0, .eq,
            .iff 0 0
              [.call 2, .localSet 2, .localGet 2, .ret]
              [.call 3, .localSet 1, .localGet 1, .ret]]
          abiDefaultCaseStoreC abiDefaultCaseLocalsC [] Q := by
      have altsList :
          abiDefaultCaseCases.alts.toList = [
            .default abiDefaultCaseDefaultCode,
            .ctorAlt falseInfo abiDefaultCaseFalseCode] := by
        change (#[LCNF.Alt.default abiDefaultCaseDefaultCode,
          LCNF.Alt.ctorAlt falseInfo abiDefaultCaseFalseCode]).toList = _
        simp
      rw [altsList]
      exact caseChainWP_default falseChain
    exact codeWP_cases fallbackCompiled wholeChain

/-- Program-level W4 simulation for allocation followed by a default case. -/
theorem abiDefaultCaseMain_simulation :
    CodeSimulation abiDefaultCaseContext abiDefaultCaseSourceModule
      abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
      abiDefaultCaseResolvedHosts.env {} [] abiDefaultCaseCode
      abiDefaultCaseMainCore abiDefaultCaseInitialStore
      (abiDefaultCaseMainFunction.toLocals []) {} abiDefaultCaseValue5
      .tobject := by
  have callFound :
      callIndex? abiDefaultCaseSourceModule
        (.runtime (.allocCtor trueInfo #[] .tagged)) = some 0 := by
    native_decide
  have valueAdapted :
      instructions abiDefaultCaseSourceModule abiDefaultCaseSourceFunction []
          [.call (.runtime (.allocCtor trueInfo #[] .tagged))] =
        .ok [.call 0] := by
    simp [instructions, instruction, callFound]
    rfl
  simp only [abiDefaultCaseCode, abiDefaultCaseMainCore]
  apply CodeSimulation.letValue abiDefaultCaseCompileC valueAdapted
    (by native_decide) abiDefaultCaseCtorStep
  apply CodeSimulation.caseOf abiDefaultCaseCasesStep
  exact abiDefaultCaseDefaultBranch_simulation

/-- The local judgment is a corollary of the program-level induction. -/
theorem abiDefaultCaseMain_codeWP :
    CodeWP abiDefaultCaseContext abiDefaultCaseSourceModule
      abiDefaultCaseSourceFunction [] abiDefaultCaseAdaptedModule.wasmModule
      abiDefaultCaseResolvedHosts.env {} [] abiDefaultCaseCode
      abiDefaultCaseMainCore abiDefaultCaseInitialStore
      (abiDefaultCaseMainFunction.toLocals []) []
      (ReturnPost {} abiDefaultCaseValue5 .tobject []) :=
  abiDefaultCaseMain_simulation.toCodeWP

theorem abiDefaultCaseObservation_related :
    compareObservations
        (ReturnedObservation {} abiDefaultCaseValue5)
        (.returned abiDefaultCaseValue5 {}) =
      .related (ReturnedObservation {} abiDefaultCaseValue5)
        (.returned abiDefaultCaseValue5 {}) := by
  unfold compareObservations ReturnedObservation
  simp only [TargetObservation.toSource?]
  have noDifferences :
      observationDifferences
          { outcome := .returned abiDefaultCaseValue5
            heap := ({} : RuntimeState).heap
            world := ({} : RuntimeState).world
            trace := ({} : RuntimeState).trace }
          { outcome := .returned abiDefaultCaseValue5
            heap := ({} : RuntimeState).heap
            world := ({} : RuntimeState).world
            trace := ({} : RuntimeState).trace } = #[] := by
    native_decide
  rw [noDifferences]
  rfl

/-- The generic W4 theorem closes source evaluation and target default selection. -/
theorem abiDefaultCaseMain_correct :
    CodeEvaluates abiDefaultCaseContext {} [] abiDefaultCaseCode {}
        abiDefaultCaseValue5 ∧
      ExportTerminatesWith abiDefaultCaseResolvedHosts.env
        abiDefaultCaseAdaptedModule.wasmModule "main"
        abiDefaultCaseInitialStore []
        (RelatedPost #[.tobject]
          (ReturnedObservation {} abiDefaultCaseValue5)) := by
  apply abiDefaultCaseSupportedExport.correct_of_simulation_with_suffix
    abiDefaultCaseObservation_related (suffix := [.unreachable])
  · simpa [abiDefaultCaseSupportedExport, abiDefaultCaseInitialStore] using
      abiDefaultCaseMain_simulation
  · simpa [abiDefaultCaseSupportedExport] using
      abiDefaultCaseMain_body_eq_core
  · simp [abiDefaultCaseSupportedExport]

/-- End-to-end W3/W4 theorem for the generated default-case export. -/
theorem abiDefaultCaseMain_export_correct :
    ExportTerminatesWith abiDefaultCaseResolvedHosts.env
      abiDefaultCaseAdaptedModule.wasmModule "main"
      abiDefaultCaseInitialStore []
      (RelatedPost #[.tobject]
        (ReturnedObservation {} abiDefaultCaseValue5)) :=
  abiDefaultCaseMain_correct.2

/-- Successful source evaluation is supplied by the same default-case proof. -/
theorem abiDefaultCaseMain_source_evaluates :
    CodeEvaluates abiDefaultCaseContext {} [] abiDefaultCaseCode {}
      abiDefaultCaseValue5 :=
  abiDefaultCaseMain_correct.1

/-- Executable-source and exported-target correctness from one certificate. -/
theorem abiDefaultCaseMain_exec_correct (externals : ExternalImpl) :
    ExecEvaluates externals
        (sourceCodeState abiDefaultCaseContext {} [] abiDefaultCaseCode)
        (ReturnedObservation {} abiDefaultCaseValue5) ∧
      ExportTerminatesWith abiDefaultCaseResolvedHosts.env
        abiDefaultCaseAdaptedModule.wasmModule "main"
        abiDefaultCaseInitialStore []
        (RelatedPost #[.tobject]
          (ReturnedObservation {} abiDefaultCaseValue5)) := by
  exact ⟨abiDefaultCaseMain_correct.1.execEvaluates externals,
    abiDefaultCaseMain_correct.2⟩

end FirTalos.Correctness
