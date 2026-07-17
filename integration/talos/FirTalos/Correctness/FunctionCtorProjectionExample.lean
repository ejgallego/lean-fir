import FirTalos.Correctness.FunctionExamples
import Fir.Wasm.Examples

namespace FirTalos.Correctness

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples

deriving instance DecidableEq for Lean.Compiler.LCNF.CtorInfo

private def ctorProjectionBodyCheck : Wasm.Program → Bool
  | [.call literal7, .localSet xIndex,
      .call literal8, .localSet yIndex,
      .localGet xLoad, .localGet yLoad, .call constructor, .localSet pIndex,
      .localGet pLoad, .call projection, .localSet rIndex,
      .localGet rLoad, .ret] =>
      literal7 == 0 && xIndex == 0 && literal8 == 1 && yIndex == 1 &&
      xLoad == 0 && yLoad == 1 && constructor == 2 && pIndex == 2 &&
      pLoad == 2 && projection == 3 && rIndex == 3 && rLoad == 3
  | _ => false

private theorem ctorProjectionBody_eq_of_check {body : Wasm.Program}
    (checked : ctorProjectionBodyCheck body = true) :
    body = [.call 0, .localSet 0, .call 1, .localSet 1,
      .localGet 0, .localGet 1, .call 2, .localSet 2,
      .localGet 2, .call 3, .localSet 3, .localGet 3, .ret] := by
  unfold ctorProjectionBodyCheck at checked
  split at checked <;> simp_all

private def ctorProjectionOperationsCheck : List HostOperation → Bool
  | [.naturalLiteral first firstKind, .naturalLiteral second secondKind,
      .allocCtor info fields resultKind, .objectProj index projectionKind] =>
      first == 7 && firstKind == .tobject &&
      second == 8 && secondKind == .tobject &&
      decide (info = pairInfo) && fields == #[.tobject, .tobject] &&
      resultKind == .object && index == 0 && projectionKind == .tobject
  | _ => false

private theorem ctorProjectionOperations_eq_of_check
    {operations : List HostOperation}
    (checked : ctorProjectionOperationsCheck operations = true) :
    operations = [
      .naturalLiteral 7 .tobject,
      .naturalLiteral 8 .tobject,
      .allocCtor pairInfo #[.tobject, .tobject] .object,
      .objectProj 0 .tobject] := by
  unfold ctorProjectionOperationsCheck at checked
  split at checked <;> simp_all

/-- Checked symbolic module for W3's constructor/projection fixture. -/
def abiCtorProjectionSourceModule : Fir.Wasm.Module :=
  match Fir.Wasm.lowerSupported abiCtorProjectionProgram with
  | .ok source => source
  | .error _ => default

theorem abiCtorProjectionSourceModule_lowered :
    Fir.Wasm.lowerSupported abiCtorProjectionProgram =
      .ok abiCtorProjectionSourceModule := by
  have success :
      (Fir.Wasm.lowerSupported abiCtorProjectionProgram).isOk = true := by
    native_decide
  cases lowered : Fir.Wasm.lowerSupported abiCtorProjectionProgram with
  | error error =>
      rw [lowered] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok source => simp [abiCtorProjectionSourceModule, lowered]

def abiCtorProjectionSourceFunction : Fir.Wasm.Function :=
  match abiCtorProjectionSourceModule.functions[0]? with
  | some function => function
  | none => default

theorem abiCtorProjectionSourceFunction_found :
    abiCtorProjectionSourceModule.functions[0]? =
      some abiCtorProjectionSourceFunction := by
  have present : abiCtorProjectionSourceModule.functions[0]?.isSome = true := by
    native_decide
  cases found : abiCtorProjectionSourceModule.functions[0]? with
  | none => simp [found] at present
  | some function => simp [abiCtorProjectionSourceFunction, found]

def abiCtorProjectionDeclX : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl x tobjectType (.lit (.nat 7))

def abiCtorProjectionDeclY : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl y tobjectType (.lit (.nat 8))

def abiCtorProjectionDeclP : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl p objType (.ctor pairInfo #[.fvar x, .fvar y])

def abiCtorProjectionDeclR : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl r tobjectType (.oproj 0 p)

def abiCtorProjectionCode : Lean.Compiler.LCNF.Code .impure :=
  .let abiCtorProjectionDeclX <|
  .let abiCtorProjectionDeclY <|
  .let abiCtorProjectionDeclP <|
  .let abiCtorProjectionDeclR <|
  .return r

def abiCtorProjectionContext : Fir.Wasm.Context :=
  { program := abiCtorProjectionProgram
    localKinds := [(r, .tobject), (p, .object), (y, .tobject), (x, .tobject)] }

private def emptyCtorProjectionAdaptedModule : AdaptedModule :=
  { wasmModule := default, sourceMap := default }

/-- Executable Talos module adapted from the checked fixture. -/
def abiCtorProjectionAdaptedModule : AdaptedModule :=
  match adapt abiCtorProjectionSourceModule with
  | .ok target => target
  | .error _ => emptyCtorProjectionAdaptedModule

theorem abiCtorProjectionAdaptedModule_adapted :
    adapt abiCtorProjectionSourceModule = .ok abiCtorProjectionAdaptedModule := by
  have success : (adapt abiCtorProjectionSourceModule).isOk = true := by
    native_decide
  cases adapted : adapt abiCtorProjectionSourceModule with
  | error error =>
      rw [adapted] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok target => simp [abiCtorProjectionAdaptedModule, adapted]

def abiCtorProjectionResolvedHosts : ResolvedHosts :=
  match resolveHosts abiCtorProjectionSourceModule with
  | .ok resolved => resolved
  | .error _ => { operations := [] }

theorem abiCtorProjectionResolvedHosts_resolved :
    resolveHosts abiCtorProjectionSourceModule =
      .ok abiCtorProjectionResolvedHosts := by
  have success : (resolveHosts abiCtorProjectionSourceModule).isOk = true := by
    native_decide
  cases resolved : resolveHosts abiCtorProjectionSourceModule with
  | error error =>
      rw [resolved] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok hosts => simp [abiCtorProjectionResolvedHosts, resolved]

theorem abiCtorProjectionResolvedHosts_operations :
    abiCtorProjectionResolvedHosts.operations = [
      .naturalLiteral 7 .tobject,
      .naturalLiteral 8 .tobject,
      .allocCtor pairInfo #[.tobject, .tobject] .object,
      .objectProj 0 .tobject] := by
  apply ctorProjectionOperations_eq_of_check
  native_decide

def abiCtorProjectionMainFunction : Wasm.Function :=
  match abiCtorProjectionAdaptedModule.wasmModule.funcs[
      4 - abiCtorProjectionAdaptedModule.wasmModule.imports.length]? with
  | some function => function
  | none => default

theorem abiCtorProjectionMain_found :
    abiCtorProjectionAdaptedModule.wasmModule.funcs[
        4 - abiCtorProjectionAdaptedModule.wasmModule.imports.length]? =
      some abiCtorProjectionMainFunction := by
  have present :
      (abiCtorProjectionAdaptedModule.wasmModule.funcs[
        4 - abiCtorProjectionAdaptedModule.wasmModule.imports.length]?).isSome =
        true := by
    native_decide
  cases found : abiCtorProjectionAdaptedModule.wasmModule.funcs[
      4 - abiCtorProjectionAdaptedModule.wasmModule.imports.length]? with
  | none => simp [found] at present
  | some function => simp [abiCtorProjectionMainFunction, found]

theorem abiCtorProjectionMain_body :
    abiCtorProjectionMainFunction.body =
      [.call 0, .localSet 0, .call 1, .localSet 1,
        .localGet 0, .localGet 1, .call 2, .localSet 2,
        .localGet 2, .call 3, .localSet 3, .localGet 3, .ret] := by
  apply ctorProjectionBody_eq_of_check
  native_decide

theorem abiCtorProjectionMain_exported :
    abiCtorProjectionAdaptedModule.wasmModule.findExport "main" = some 4 := by
  native_decide

theorem abiCtorProjectionMain_notImport :
    abiCtorProjectionAdaptedModule.wasmModule.imports[4]? = none := by
  native_decide

theorem abiCtorProjectionMain_resultCount :
    abiCtorProjectionMainFunction.results.length = 1 := by
  native_decide

theorem abiCtorProjectionHostsMatch :
    HostsMatch abiCtorProjectionResolvedHosts abiCtorProjectionSourceModule := by
  unfold HostsMatch
  native_decide

theorem abiCtorProjectionHostsSatisfy :
    abiCtorProjectionResolvedHosts.env.Satisfies
      abiCtorProjectionAdaptedModule.wasmModule
      abiCtorProjectionResolvedHosts.spec :=
  resolvedHosts_satisfy_adapted abiCtorProjectionAdaptedModule_adapted
    abiCtorProjectionHostsMatch

def abiCtorProjectionValue7 : Value :=
  .object (.tagged (UInt64.ofNat 7))

def abiCtorProjectionValue8 : Value :=
  .object (.tagged (UInt64.ofNat 8))

def abiCtorProjectionPairValue : Value :=
  .object (.heap 0)

def abiCtorProjectionRuntime : RuntimeState :=
  { heap := [(0, {
      object := .ctor {
        tag := pairInfo.cidx
        objectFields := #[abiCtorProjectionValue7, abiCtorProjectionValue8]
        usizeFields := #[]
        scalarFields := [] } })]
    nextLocation := 1 }

def abiCtorProjectionHandlesX : HandleTable :=
  { entries := [(1, abiCtorProjectionValue7)], next := 2 }

def abiCtorProjectionHandlesY : HandleTable :=
  { entries := [
      (2, abiCtorProjectionValue8),
      (1, abiCtorProjectionValue7)]
    next := 3 }

def abiCtorProjectionHandlesP : HandleTable :=
  { entries := [
      (3, abiCtorProjectionPairValue),
      (2, abiCtorProjectionValue8),
      (1, abiCtorProjectionValue7)]
    next := 4 }

def abiCtorProjectionInitialStore : Wasm.Store RuntimeHost :=
  abiCtorProjectionAdaptedModule.wasmModule.initialStore

def abiCtorProjectionStoreX : Wasm.Store RuntimeHost :=
  successfulHostStore abiCtorProjectionInitialStore {} abiCtorProjectionHandlesX

def abiCtorProjectionStoreY : Wasm.Store RuntimeHost :=
  successfulHostStore abiCtorProjectionStoreX {} abiCtorProjectionHandlesY

def abiCtorProjectionStoreP : Wasm.Store RuntimeHost :=
  successfulHostStore abiCtorProjectionStoreY abiCtorProjectionRuntime
    abiCtorProjectionHandlesP

def abiCtorProjectionStoreR : Wasm.Store RuntimeHost :=
  successfulHostStore abiCtorProjectionStoreP abiCtorProjectionRuntime
    abiCtorProjectionHandlesP

def abiCtorProjectionLocalsX : Wasm.Locals :=
  { locals := [.i32 1, .i32 0, .i32 0, .i32 0] }

def abiCtorProjectionLocalsY : Wasm.Locals :=
  { locals := [.i32 1, .i32 2, .i32 0, .i32 0] }

def abiCtorProjectionLocalsP : Wasm.Locals :=
  { locals := [.i32 1, .i32 2, .i32 3, .i32 0] }

def abiCtorProjectionLocalsR : Wasm.Locals :=
  { locals := [.i32 1, .i32 2, .i32 3, .i32 1] }

def abiCtorProjectionEnvX : Env :=
  bind [] x abiCtorProjectionValue7

def abiCtorProjectionEnvY : Env :=
  bind abiCtorProjectionEnvX y abiCtorProjectionValue8

def abiCtorProjectionEnvP : Env :=
  bind abiCtorProjectionEnvY p abiCtorProjectionPairValue

def abiCtorProjectionEnvR : Env :=
  bind abiCtorProjectionEnvP r abiCtorProjectionValue7

theorem abiCtorProjectionInitialState_related :
    StateRelated abiCtorProjectionSourceFunction {} []
      abiCtorProjectionInitialStore
      (abiCtorProjectionMainFunction.toLocals []) := by
  unfold StateRelated
  refine ⟨rfl, rfl, rfl, handleTableInvariant_empty, ?_⟩
  intro fvar value found
  simp [lookup] at found

theorem abiCtorProjectionEncodeX :
    abiCtorProjectionInitialStore.host.handles.encode .tobject
        abiCtorProjectionValue7 =
      .ok (abiCtorProjectionHandlesX, 1) := by
  rfl

theorem abiCtorProjectionEncodeY :
    abiCtorProjectionStoreX.host.handles.encode .tobject
        abiCtorProjectionValue8 =
      .ok (abiCtorProjectionHandlesY, 2) := by
  rfl

theorem abiCtorProjectionAllocated :
    allocCtor abiCtorProjectionStoreY.host.runtime pairInfo
        #[abiCtorProjectionValue7, abiCtorProjectionValue8] =
      .ok (abiCtorProjectionRuntime, abiCtorProjectionPairValue) := by
  simp [allocCtor, abiCtorProjectionStoreY, successfulHostStore,
    abiCtorProjectionRuntime, abiCtorProjectionPairValue,
    abiCtorProjectionValue7, abiCtorProjectionValue8, pairInfo, alloc]
  rfl

theorem abiCtorProjectionEncodeP :
    abiCtorProjectionStoreY.host.handles.encode .object
        abiCtorProjectionPairValue =
      .ok (abiCtorProjectionHandlesP, 3) := by
  rfl

theorem abiCtorProjectionProjected :
    getObjectField abiCtorProjectionStoreP.host.runtime
        abiCtorProjectionPairValue 0 =
      .ok abiCtorProjectionValue7 := by
  rfl

theorem abiCtorProjectionEncodeR :
    abiCtorProjectionStoreP.host.handles.encode .tobject
        abiCtorProjectionValue7 =
      .ok (abiCtorProjectionHandlesP, 1) := by
  rfl

theorem abiCtorProjectionSetX :
    (abiCtorProjectionMainFunction.toLocals []).set? 0 (.i32 1) =
      some abiCtorProjectionLocalsX := by
  native_decide

theorem abiCtorProjectionSetY :
    abiCtorProjectionLocalsX.set? 1 (.i32 2) =
      some abiCtorProjectionLocalsY := by
  native_decide

theorem abiCtorProjectionSetP :
    abiCtorProjectionLocalsY.set? 2 (.i32 3) =
      some abiCtorProjectionLocalsP := by
  native_decide

theorem abiCtorProjectionSetR :
    abiCtorProjectionLocalsP.set? 3 (.i32 1) =
      some abiCtorProjectionLocalsR := by
  native_decide

def abiCtorProjectionImport (index : Nat) : Wasm.ImportDecl :=
  abiCtorProjectionAdaptedModule.wasmModule.imports[index]!

theorem abiCtorProjectionImport0_found :
    abiCtorProjectionAdaptedModule.wasmModule.imports[0]? =
      some (abiCtorProjectionImport 0) := by
  native_decide

theorem abiCtorProjectionImport1_found :
    abiCtorProjectionAdaptedModule.wasmModule.imports[1]? =
      some (abiCtorProjectionImport 1) := by
  native_decide

theorem abiCtorProjectionImport2_found :
    abiCtorProjectionAdaptedModule.wasmModule.imports[2]? =
      some (abiCtorProjectionImport 2) := by
  native_decide

theorem abiCtorProjectionImport3_found :
    abiCtorProjectionAdaptedModule.wasmModule.imports[3]? =
      some (abiCtorProjectionImport 3) := by
  native_decide

theorem abiCtorProjectionDeclX_kind :
    Fir.Wasm.letValueKind abiCtorProjectionDeclX = .ok .tobject := by
  simp [Fir.Wasm.letValueKind, abiCtorProjectionDeclX, letDecl, tobjectType]

theorem abiCtorProjectionDeclY_kind :
    Fir.Wasm.letValueKind abiCtorProjectionDeclY = .ok .tobject := by
  simp [Fir.Wasm.letValueKind, abiCtorProjectionDeclY, letDecl, tobjectType]

theorem abiCtorProjectionDeclP_kind :
    Fir.Wasm.letValueKind abiCtorProjectionDeclP = .ok .object := by
  simp [Fir.Wasm.letValueKind, abiCtorProjectionDeclP, letDecl, objType]

theorem abiCtorProjectionDeclR_kind :
    Fir.Wasm.letValueKind abiCtorProjectionDeclR = .ok .tobject := by
  simp [Fir.Wasm.letValueKind, abiCtorProjectionDeclR, letDecl, tobjectType]

theorem abiCtorProjectionCompileX :
    Fir.Wasm.compileLetValue abiCtorProjectionContext abiCtorProjectionDeclX =
      .ok [.call (.runtime (.literal (.nat 7) .tobject))] :=
  compileLetValue_naturalLiteral rfl abiCtorProjectionDeclX_kind

theorem abiCtorProjectionCompileY :
    Fir.Wasm.compileLetValue abiCtorProjectionContext abiCtorProjectionDeclY =
      .ok [.call (.runtime (.literal (.nat 8) .tobject))] :=
  compileLetValue_naturalLiteral rfl abiCtorProjectionDeclY_kind

theorem abiCtorProjectionCompileArgs :
    Fir.Wasm.compileArgs abiCtorProjectionContext #[.fvar x, .fvar y] =
      .ok ([.localGet x, .localGet y], #[.tobject, .tobject]) := by
  simp [Fir.Wasm.compileArgs, Fir.Wasm.compileArg, abiCtorProjectionContext,
    Fir.Wasm.findLocalKind?, x, y, p, r]
  rfl

theorem abiCtorProjectionCompileP :
    Fir.Wasm.compileLetValue abiCtorProjectionContext abiCtorProjectionDeclP =
      .ok ([.localGet x, .localGet y] ++ [
        .call (.runtime (.allocCtor pairInfo #[.tobject, .tobject] .object))]) := by
  apply compileLetValue_constructor rfl
  · native_decide
  · exact abiCtorProjectionDeclP_kind
  · exact abiCtorProjectionCompileArgs

theorem abiCtorProjectionGetP :
    Fir.Wasm.getLocal abiCtorProjectionContext p =
      .ok (.localGet p, .object) := by
  simp [Fir.Wasm.getLocal, abiCtorProjectionContext,
    Fir.Wasm.findLocalKind?, x, y, p, r]

theorem abiCtorProjectionCompileR :
    Fir.Wasm.compileLetValue abiCtorProjectionContext abiCtorProjectionDeclR =
      .ok [.localGet p, .call (.runtime (.objectProj 0 .tobject))] := by
  apply compileLetValue_objectProjection rfl abiCtorProjectionDeclR_kind
    abiCtorProjectionGetP

theorem abiCtorProjectionGetR :
    Fir.Wasm.getLocal abiCtorProjectionContext r =
      .ok (.localGet r, .tobject) := by
  simp [Fir.Wasm.getLocal, abiCtorProjectionContext,
    Fir.Wasm.findLocalKind?, x, y, p, r]

theorem abiCtorProjectionLiteral7 :
    literal abiCtorProjectionInitialStore.host.runtime (.nat 7) =
      ({}, abiCtorProjectionValue7) := by
  simp [literal, maxTaggedPayload, abiCtorProjectionValue7]
  rfl

theorem abiCtorProjectionLiteral8 :
    literal abiCtorProjectionStoreX.host.runtime (.nat 8) =
      ({}, abiCtorProjectionValue8) := by
  simp [literal, maxTaggedPayload, abiCtorProjectionStoreX,
    successfulHostStore, abiCtorProjectionValue8]

theorem abiCtorProjectionArgumentsEvaluated :
    evalArgs abiCtorProjectionEnvY #[.fvar x, .fvar y] =
      .ok #[abiCtorProjectionValue7, abiCtorProjectionValue8] := by
  have yNeX : (y.name == x.name) = false := by
    native_decide
  simp [evalArgs, evalArg, abiCtorProjectionEnvY, abiCtorProjectionEnvX,
    Fir.LeanIR.Impure.bind, lookup, yNeX]
  rfl

theorem abiCtorProjectionObjectLookup :
    lookupValue abiCtorProjectionEnvP p =
      .ok abiCtorProjectionPairValue := by
  simp [lookupValue, abiCtorProjectionEnvP, Fir.LeanIR.Impure.bind, lookup]

theorem abiCtorProjectionConstructorDecoded :
    decodeArgs abiCtorProjectionStoreY.host.handles #[.tobject, .tobject]
        [.i32 1, .i32 2] =
      .ok #[abiCtorProjectionValue7, abiCtorProjectionValue8] := by
  rfl

theorem abiCtorProjectionObjectDecoded :
    decodeArgs abiCtorProjectionStoreP.host.handles #[.tobject] [.i32 3] =
      .ok #[abiCtorProjectionPairValue] := by
  rfl

/-- Local W4 proof for the generated literal/literal/constructor/projection body. -/
theorem abiCtorProjectionMain_codeWP :
    CodeWP abiCtorProjectionContext abiCtorProjectionSourceModule
      abiCtorProjectionSourceFunction []
      abiCtorProjectionAdaptedModule.wasmModule
      abiCtorProjectionResolvedHosts.env
      {} [] abiCtorProjectionCode abiCtorProjectionMainFunction.body
      abiCtorProjectionInitialStore
      (abiCtorProjectionMainFunction.toLocals []) []
      (ReturnPost abiCtorProjectionRuntime abiCtorProjectionValue7 .tobject []) := by
  have contract0 :
      abiCtorProjectionResolvedHosts.spec.contracts[0]? =
        some (hostContract (.naturalLiteral 7 .tobject)) := by
    simp [ResolvedHosts.spec, abiCtorProjectionResolvedHosts_operations]
  have contract1 :
      abiCtorProjectionResolvedHosts.spec.contracts[1]? =
        some (hostContract (.naturalLiteral 8 .tobject)) := by
    simp [ResolvedHosts.spec, abiCtorProjectionResolvedHosts_operations]
  have contract2 :
      abiCtorProjectionResolvedHosts.spec.contracts[2]? =
        some (hostContract
          (.allocCtor pairInfo #[.tobject, .tobject] .object)) := by
    simp [ResolvedHosts.spec, abiCtorProjectionResolvedHosts_operations]
  have contract3 :
      abiCtorProjectionResolvedHosts.spec.contracts[3]? =
        some (hostContract (.objectProj 0 .tobject)) := by
    simp [ResolvedHosts.spec, abiCtorProjectionResolvedHosts_operations]

  have stepX := letStepSimulates_naturalLiteral
    (context := abiCtorProjectionContext)
    (sourceFunction := abiCtorProjectionSourceFunction)
    (module := abiCtorProjectionAdaptedModule.wasmModule)
    (hostEnv := abiCtorProjectionResolvedHosts.env)
    (spec := abiCtorProjectionResolvedHosts.spec)
    (id := 0) (imp := abiCtorProjectionImport 0)
    (decl := abiCtorProjectionDeclX) (sourceEnv := [])
    (initial := abiCtorProjectionInitialStore)
    (locals := abiCtorProjectionMainFunction.toLocals [])
    (updated := abiCtorProjectionLocalsX) (resultIndex := 0)
    (value := 7) (after := abiCtorProjectionHandlesX) (handle := 1)
    rfl abiCtorProjectionInitialState_related
    (by native_decide) (by native_decide)
    abiCtorProjectionImport0_found abiCtorProjectionHostsSatisfy
    (by native_decide) contract0 (by native_decide) (by native_decide)
    (by simpa [abiCtorProjectionLiteral7] using abiCtorProjectionEncodeX)
    abiCtorProjectionSetX
  have relatedX :
      StateRelated abiCtorProjectionSourceFunction {}
        abiCtorProjectionEnvX abiCtorProjectionStoreX
        abiCtorProjectionLocalsX := by
    simpa [abiCtorProjectionEnvX, abiCtorProjectionStoreX,
      abiCtorProjectionLiteral7, abiCtorProjectionDeclX, letDecl]
      using stepX.2.2.1

  have stepY := letStepSimulates_naturalLiteral
    (context := abiCtorProjectionContext)
    (sourceFunction := abiCtorProjectionSourceFunction)
    (module := abiCtorProjectionAdaptedModule.wasmModule)
    (hostEnv := abiCtorProjectionResolvedHosts.env)
    (spec := abiCtorProjectionResolvedHosts.spec)
    (id := 1) (imp := abiCtorProjectionImport 1)
    (decl := abiCtorProjectionDeclY) (sourceEnv := abiCtorProjectionEnvX)
    (initial := abiCtorProjectionStoreX) (locals := abiCtorProjectionLocalsX)
    (updated := abiCtorProjectionLocalsY) (resultIndex := 1)
    (value := 8) (after := abiCtorProjectionHandlesY) (handle := 2)
    rfl relatedX (by native_decide) (by native_decide)
    abiCtorProjectionImport1_found abiCtorProjectionHostsSatisfy
    (by native_decide) contract1 (by native_decide) (by native_decide)
    (by simpa [abiCtorProjectionLiteral8] using abiCtorProjectionEncodeY)
    abiCtorProjectionSetY
  have relatedY :
      StateRelated abiCtorProjectionSourceFunction {}
        abiCtorProjectionEnvY abiCtorProjectionStoreY
        abiCtorProjectionLocalsY := by
    simpa [abiCtorProjectionEnvY, abiCtorProjectionStoreY,
      abiCtorProjectionLiteral8, abiCtorProjectionDeclY, letDecl]
      using stepY.2.2.1

  have stepP := letStepSimulates_constructor
    (context := abiCtorProjectionContext)
    (sourceFunction := abiCtorProjectionSourceFunction)
    (module := abiCtorProjectionAdaptedModule.wasmModule)
    (hostEnv := abiCtorProjectionResolvedHosts.env)
    (spec := abiCtorProjectionResolvedHosts.spec)
    (id := 2) (imp := abiCtorProjectionImport 2)
    (decl := abiCtorProjectionDeclP) (info := pairInfo)
    (args := #[.fvar x, .fvar y]) (sourceEnv := abiCtorProjectionEnvY)
    (initial := abiCtorProjectionStoreY) (locals := abiCtorProjectionLocalsY)
    (updated := abiCtorProjectionLocalsP) (indices := [0, 1])
    (physicalArgs := [.i32 1, .i32 2])
    (semanticArgs := #[abiCtorProjectionValue7, abiCtorProjectionValue8])
    (nextRuntime := abiCtorProjectionRuntime)
    (sourceValue := abiCtorProjectionPairValue) (resultIndex := 2)
    (fieldKinds := #[.tobject, .tobject]) (resultKind := .object)
    (after := abiCtorProjectionHandlesP) (handle := 3)
    rfl abiCtorProjectionArgumentsEvaluated abiCtorProjectionAllocated relatedY
    (by native_decide) (by native_decide) (by native_decide)
    abiCtorProjectionImport2_found abiCtorProjectionHostsSatisfy
    (by native_decide) contract2 (by native_decide) (by native_decide)
    abiCtorProjectionConstructorDecoded rfl abiCtorProjectionEncodeP
    abiCtorProjectionSetP
  have relatedP :
      StateRelated abiCtorProjectionSourceFunction abiCtorProjectionRuntime
        abiCtorProjectionEnvP abiCtorProjectionStoreP
        abiCtorProjectionLocalsP := by
    simpa [abiCtorProjectionEnvP, abiCtorProjectionStoreP,
      abiCtorProjectionDeclP, letDecl] using stepP.2.2.1

  have stepR := letStepSimulates_objectProjection
    (context := abiCtorProjectionContext)
    (sourceFunction := abiCtorProjectionSourceFunction)
    (module := abiCtorProjectionAdaptedModule.wasmModule)
    (hostEnv := abiCtorProjectionResolvedHosts.env)
    (spec := abiCtorProjectionResolvedHosts.spec)
    (id := 3) (imp := abiCtorProjectionImport 3)
    (decl := abiCtorProjectionDeclR) (sourceEnv := abiCtorProjectionEnvP)
    (index := 0) (objectId := p) (initial := abiCtorProjectionStoreP)
    (locals := abiCtorProjectionLocalsP) (updated := abiCtorProjectionLocalsR)
    (objectIndex := 2) (resultIndex := 3) (objectHandle := 3)
    (sourceObject := abiCtorProjectionPairValue)
    (sourceValue := abiCtorProjectionValue7) (resultKind := .tobject)
    (after := abiCtorProjectionHandlesP) (resultHandle := 1)
    rfl abiCtorProjectionObjectLookup abiCtorProjectionProjected relatedP
    (by native_decide) (by native_decide) (by native_decide)
    abiCtorProjectionImport3_found abiCtorProjectionHostsSatisfy
    (by native_decide) contract3 (by native_decide) (by native_decide)
    abiCtorProjectionObjectDecoded rfl abiCtorProjectionEncodeR
    abiCtorProjectionSetR
  have relatedR :
      StateRelated abiCtorProjectionSourceFunction abiCtorProjectionRuntime
        abiCtorProjectionEnvR abiCtorProjectionStoreR
        abiCtorProjectionLocalsR := by
    simpa [abiCtorProjectionEnvR, abiCtorProjectionStoreR,
      abiCtorProjectionStoreP, abiCtorProjectionDeclR, letDecl,
      successfulHostStore]
      using stepR.2.2.1

  have returned :
      CodeWP abiCtorProjectionContext abiCtorProjectionSourceModule
        abiCtorProjectionSourceFunction []
        abiCtorProjectionAdaptedModule.wasmModule
        abiCtorProjectionResolvedHosts.env
        abiCtorProjectionRuntime abiCtorProjectionEnvR (.return r)
        [.localGet 3, .ret] abiCtorProjectionStoreR abiCtorProjectionLocalsR []
        (ReturnPost abiCtorProjectionRuntime abiCtorProjectionValue7
          .tobject []) := by
    apply codeWP_return abiCtorProjectionGetR
      (resultIndex := 3) (by native_decide) (by native_decide)
      (lookup_bind_self abiCtorProjectionEnvP r abiCtorProjectionValue7)
      relatedR

  have projected :
      CodeWP abiCtorProjectionContext abiCtorProjectionSourceModule
        abiCtorProjectionSourceFunction []
        abiCtorProjectionAdaptedModule.wasmModule
        abiCtorProjectionResolvedHosts.env
        abiCtorProjectionRuntime abiCtorProjectionEnvP
        (.let abiCtorProjectionDeclR (.return r))
        [.localGet 2, .call 3, .localSet 3, .localGet 3, .ret]
        abiCtorProjectionStoreP abiCtorProjectionLocalsP []
        (ReturnPost abiCtorProjectionRuntime abiCtorProjectionValue7
          .tobject []) := by
    apply codeWP_objectProjection_let
      (spec := abiCtorProjectionResolvedHosts.spec)
      (id := 3) (imp := abiCtorProjectionImport 3)
      (index := 0) (objectId := p) (objectIndex := 2) (resultIndex := 3)
      (objectHandle := 3) (sourceObject := abiCtorProjectionPairValue)
      (sourceValue := abiCtorProjectionValue7) (resultKind := .tobject)
      (after := abiCtorProjectionHandlesP) (resultHandle := 1)
    · rfl
    · exact abiCtorProjectionCompileR
    · native_decide
    · native_decide
    · exact abiCtorProjectionObjectLookup
    · exact abiCtorProjectionProjected
    · exact relatedP
    · native_decide
    · native_decide
    · native_decide
    · exact abiCtorProjectionImport3_found
    · exact abiCtorProjectionHostsSatisfy
    · native_decide
    · exact contract3
    · native_decide
    · native_decide
    · exact abiCtorProjectionObjectDecoded
    · rfl
    · exact abiCtorProjectionEncodeR
    · exact abiCtorProjectionSetR
    · simpa [abiCtorProjectionEnvR, abiCtorProjectionStoreR,
        abiCtorProjectionStoreP, abiCtorProjectionDeclR, letDecl,
        successfulHostStore]
        using returned

  have constructed :
      CodeWP abiCtorProjectionContext abiCtorProjectionSourceModule
        abiCtorProjectionSourceFunction []
        abiCtorProjectionAdaptedModule.wasmModule
        abiCtorProjectionResolvedHosts.env
        {} abiCtorProjectionEnvY
        (.let abiCtorProjectionDeclP <|
          .let abiCtorProjectionDeclR <| .return r)
        [.localGet 0, .localGet 1, .call 2, .localSet 2,
          .localGet 2, .call 3, .localSet 3, .localGet 3, .ret]
        abiCtorProjectionStoreY abiCtorProjectionLocalsY []
        (ReturnPost abiCtorProjectionRuntime abiCtorProjectionValue7
          .tobject []) := by
    apply codeWP_constructor_let
      (spec := abiCtorProjectionResolvedHosts.spec)
      (id := 2) (imp := abiCtorProjectionImport 2)
      (info := pairInfo) (args := #[.fvar x, .fvar y])
      (fvarIds := [x, y]) (indices := [0, 1])
      (physicalArgs := [.i32 1, .i32 2])
      (semanticArgs := #[abiCtorProjectionValue7, abiCtorProjectionValue8])
      (nextRuntime := abiCtorProjectionRuntime)
      (sourceValue := abiCtorProjectionPairValue) (resultIndex := 2)
      (fieldKinds := #[.tobject, .tobject]) (resultKind := .object)
      (after := abiCtorProjectionHandlesP) (handle := 3)
    · rfl
    · simpa using abiCtorProjectionCompileP
    · native_decide
    · native_decide
    · exact abiCtorProjectionArgumentsEvaluated
    · exact abiCtorProjectionAllocated
    · exact relatedY
    · native_decide
    · native_decide
    · native_decide
    · exact abiCtorProjectionImport2_found
    · exact abiCtorProjectionHostsSatisfy
    · native_decide
    · exact contract2
    · native_decide
    · native_decide
    · exact abiCtorProjectionConstructorDecoded
    · rfl
    · exact abiCtorProjectionEncodeP
    · exact abiCtorProjectionSetP
    · simpa [abiCtorProjectionEnvP, abiCtorProjectionStoreP,
        abiCtorProjectionDeclP, letDecl] using projected

  have literal8 :
      CodeWP abiCtorProjectionContext abiCtorProjectionSourceModule
        abiCtorProjectionSourceFunction []
        abiCtorProjectionAdaptedModule.wasmModule
        abiCtorProjectionResolvedHosts.env
        {} abiCtorProjectionEnvX
        (.let abiCtorProjectionDeclY <|
          .let abiCtorProjectionDeclP <|
          .let abiCtorProjectionDeclR <| .return r)
        [.call 1, .localSet 1, .localGet 0, .localGet 1, .call 2,
          .localSet 2, .localGet 2, .call 3, .localSet 3,
          .localGet 3, .ret]
        abiCtorProjectionStoreX abiCtorProjectionLocalsX []
        (ReturnPost abiCtorProjectionRuntime abiCtorProjectionValue7
          .tobject []) := by
    apply codeWP_naturalLiteral_let
      (spec := abiCtorProjectionResolvedHosts.spec)
      (id := 1) (imp := abiCtorProjectionImport 1)
      (resultIndex := 1) (value := 8)
      (after := abiCtorProjectionHandlesY) (handle := 2)
    · rfl
    · exact abiCtorProjectionCompileY
    · native_decide
    · native_decide
    · native_decide
    · exact relatedX
    · exact abiCtorProjectionImport1_found
    · exact abiCtorProjectionHostsSatisfy
    · native_decide
    · exact contract1
    · native_decide
    · native_decide
    · simpa [abiCtorProjectionLiteral8] using abiCtorProjectionEncodeY
    · exact abiCtorProjectionSetY
    · simpa [abiCtorProjectionEnvY, abiCtorProjectionStoreY,
        abiCtorProjectionDeclY, letDecl, abiCtorProjectionLiteral8]
        using constructed

  rw [abiCtorProjectionMain_body]
  apply codeWP_naturalLiteral_let
    (spec := abiCtorProjectionResolvedHosts.spec)
    (id := 0) (imp := abiCtorProjectionImport 0)
    (resultIndex := 0) (value := 7)
    (after := abiCtorProjectionHandlesX) (handle := 1)
  · rfl
  · exact abiCtorProjectionCompileX
  · native_decide
  · native_decide
  · native_decide
  · exact abiCtorProjectionInitialState_related
  · exact abiCtorProjectionImport0_found
  · exact abiCtorProjectionHostsSatisfy
  · native_decide
  · exact contract0
  · native_decide
  · native_decide
  · simpa [abiCtorProjectionLiteral7] using abiCtorProjectionEncodeX
  · exact abiCtorProjectionSetX
  · simpa [abiCtorProjectionCode, abiCtorProjectionEnvX,
      abiCtorProjectionStoreX, abiCtorProjectionDeclX, letDecl,
      abiCtorProjectionLiteral7] using literal8

theorem abiCtorProjectionObservation_related :
    compareObservations
        (ReturnedObservation abiCtorProjectionRuntime abiCtorProjectionValue7)
        (.returned abiCtorProjectionValue7 abiCtorProjectionRuntime) =
      .related
        (ReturnedObservation abiCtorProjectionRuntime abiCtorProjectionValue7)
        (.returned abiCtorProjectionValue7 abiCtorProjectionRuntime) := by
  unfold compareObservations ReturnedObservation
  simp only [TargetObservation.toSource?]
  have noDifferences :
      observationDifferences
          { outcome := .returned abiCtorProjectionValue7
            heap := abiCtorProjectionRuntime.heap
            world := abiCtorProjectionRuntime.world
            trace := abiCtorProjectionRuntime.trace }
          { outcome := .returned abiCtorProjectionValue7
            heap := abiCtorProjectionRuntime.heap
            world := abiCtorProjectionRuntime.world
            trace := abiCtorProjectionRuntime.trace } = #[] := by
    native_decide
  rw [noDifferences]
  rfl

/--
End-to-end W3/W4 theorem for the generated constructor/projection fixture.
The actual adapted `main` export terminates with an observation related to the
source pair allocation followed by projection of its first field.
-/
theorem abiCtorProjectionMain_export_correct :
    ExportTerminatesWith abiCtorProjectionResolvedHosts.env
      abiCtorProjectionAdaptedModule.wasmModule "main"
      abiCtorProjectionInitialStore []
      (RelatedPost #[.tobject]
        (ReturnedObservation abiCtorProjectionRuntime
          abiCtorProjectionValue7)) := by
  apply CodeWP.toExportTerminatesWithRelated_of_return
    abiCtorProjectionMain_exported abiCtorProjectionMain_notImport
    abiCtorProjectionMain_found rfl abiCtorProjectionMain_resultCount
    abiCtorProjectionObservation_related
  simpa [abiCtorProjectionInitialStore] using abiCtorProjectionMain_codeWP

end FirTalos.Correctness
