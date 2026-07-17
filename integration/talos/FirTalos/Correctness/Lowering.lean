import FirTalos.Correctness.ABI
import FirTalos.Correctness.Execution
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Tactic

namespace FirTalos.Correctness

open Fir.Wasm
open Fir.LeanIR.Impure

/--
The local result relation for one lowering step: the target host carries the
source runtime produced by the step, and the physical result decodes to the
source value at the retained semantic ABI kind.
-/
def StepResultRelated (sourceRuntime : RuntimeState) (sourceValue : Value)
    (kind : AbiKind) (target : Wasm.Store RuntimeHost) (physical : Wasm.Value) : Prop :=
  target.host.runtime = sourceRuntime ∧
    DecodesValue target.host.handles kind physical sourceValue

@[simp] theorem compileLiteral_natural (value : Nat) (result : AbiKind) :
    compileLiteral result (.nat value) =
      [.call (.runtime (.literal (.nat value) result))] := rfl

@[simp] theorem compileLiteral_string (value : String) (result : AbiKind) :
    compileLiteral result (.str value) =
      [.call (.runtime (.literal (.str value) result))] := rfl

@[simp] theorem checkedAbiKind_tagged :
    checkedAbiKind Lean.Compiler.LCNF.ImpureType.tagged = .ok .tagged := by
  have taggedNotObject :
      (Lean.Compiler.LCNF.ImpureType.tagged ==
        Lean.Compiler.LCNF.ImpureType.object) = false := by
    native_decide
  have taggedSelf :
      (Lean.Compiler.LCNF.ImpureType.tagged ==
        Lean.Compiler.LCNF.ImpureType.tagged) = true := by
    native_decide
  simp [checkedAbiKind, Fir.Wasm.abiKind, Fir.Wasm.abiKind?,
    taggedNotObject, taggedSelf]
  rfl

@[simp] theorem checkedAbiKind_object :
    checkedAbiKind Lean.Compiler.LCNF.ImpureType.object = .ok .object := by
  have objectSelf :
      (Lean.Compiler.LCNF.ImpureType.object ==
        Lean.Compiler.LCNF.ImpureType.object) = true := by
    native_decide
  simp [checkedAbiKind, Fir.Wasm.abiKind, Fir.Wasm.abiKind?, objectSelf]
  rfl

@[simp] theorem checkedAbiKind_tobject :
    checkedAbiKind Lean.Compiler.LCNF.ImpureType.tobject = .ok .tobject := by
  have tobjectNotObject :
      (Lean.Compiler.LCNF.ImpureType.tobject ==
        Lean.Compiler.LCNF.ImpureType.object) = false := by
    native_decide
  have tobjectNotTagged :
      (Lean.Compiler.LCNF.ImpureType.tobject ==
        Lean.Compiler.LCNF.ImpureType.tagged) = false := by
    native_decide
  have tobjectSelf :
      (Lean.Compiler.LCNF.ImpureType.tobject ==
        Lean.Compiler.LCNF.ImpureType.tobject) = true := by
    native_decide
  simp [checkedAbiKind, Fir.Wasm.abiKind, Fir.Wasm.abiKind?, tobjectNotObject,
    tobjectNotTagged, tobjectSelf]
  rfl

/-- A checked natural-literal declaration exposes its exact symbolic host call. -/
theorem compileLetValue_naturalLiteral
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {value : Nat}
    (valueEq : decl.value = .lit (.nat value))
    (resultEq : letValueKind decl = .ok .tobject) :
    compileLetValue context decl =
      .ok [.call (.runtime (.literal (.nat value) .tobject))] := by
  simp [compileLetValue, valueEq, resultEq, AbiKind.acceptsLiteral]
  rfl

/-- A checked string-literal declaration exposes its exact symbolic host call. -/
theorem compileLetValue_stringLiteral
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {value : String}
    (valueEq : decl.value = .lit (.str value))
    (resultEq : letValueKind decl = .ok .object) :
    compileLetValue context decl =
      .ok [.call (.runtime (.literal (.str value) .object))] := by
  simp [compileLetValue, valueEq, resultEq, AbiKind.acceptsLiteral]
  rfl

theorem compileLetValue_constructor
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {info : Lean.Compiler.LCNF.CtorInfo} {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {resultKind : AbiKind} {argumentCode : List Instruction}
    {fieldKinds : Array AbiKind}
    (valueEq : decl.value = .ctor info args)
    (fits : constructorTagFitsI32 info = true)
    (resultEq : letValueKind decl = .ok resultKind)
    (argumentsEq : compileArgs context args = .ok (argumentCode, fieldKinds)) :
    compileLetValue context decl =
      .ok (argumentCode ++ [.call (.runtime (.allocCtor info fieldKinds resultKind))]) := by
  simp [compileLetValue, valueEq, fits, resultEq, argumentsEq]
  rfl

theorem compileLetValue_objectProjection
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {index : Nat} {objectId : Lean.FVarId} {resultKind objectKind : AbiKind}
    {objectInstruction : Instruction}
    (valueEq : decl.value = .oproj index objectId)
    (resultEq : letValueKind decl = .ok resultKind)
    (objectEq : getLocal context objectId = .ok (objectInstruction, objectKind)) :
    compileLetValue context decl =
      .ok [objectInstruction, .call (.runtime (.objectProj index resultKind))] := by
  simp [compileLetValue, valueEq, resultEq, objectEq]
  rfl

theorem compileCaseChain_constructor
    {context : Context} {discr : Lean.FVarId}
    {info : Lean.Compiler.LCNF.CtorInfo} {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)} {fallback thenBody elseBody : List Instruction}
    (fits : constructorTagFitsI32 info = true)
    (thenEq : compileCode context code = .ok thenBody)
    (elseEq : compileCaseChain context discr alts fallback = .ok elseBody) :
    compileCaseChain context discr (.ctorAlt info code :: alts) fallback =
      .ok [
        .localGet discr,
        .call (.runtime .getTag),
      .i32Const .uint32 (UInt32.ofNat info.cidx),
      .i32Eq,
      .ifElse thenBody elseBody] := by
  change compileCaseChainWithM (compileCode context) discr alts fallback =
    .ok elseBody at elseEq
  change compileCaseChainWithM (compileCode context) discr (.ctorAlt info code :: alts)
    fallback = _
  rw [compileCaseChainWithM.eq_def]
  simp only [fits, ↓reduceIte]
  rw [thenEq, elseEq]
  rfl

theorem constructorTag_i32_eq_iff {left right : Nat}
    (leftFits : left < UInt32.size) (rightFits : right < UInt32.size) :
    UInt32.ofNat left = UInt32.ofNat right ↔ left = right := by
  constructor
  · intro equal
    have := congrArg UInt32.toNat equal
    simpa [UInt32.toNat_ofNat_of_lt' leftFits,
      UInt32.toNat_ofNat_of_lt' rightFits] using this
  · exact congrArg UInt32.ofNat

/--
The semantic host implementation of a compiler-produced natural literal
simulates the source runtime operation. Handle-space availability is explicit
in `encoded`; coherence turns the successful encoding into the decode half of
the result relation.
-/
theorem naturalLiteral_host_simulates
    (initial : Wasm.Store RuntimeHost) (value : Nat) {after : HandleTable}
    {handle : Handle}
    (invariant : HandleTableInvariant initial.host.handles)
    (encoded :
      initial.host.handles.encode .tobject (literal initial.host.runtime (.nat value)).2 =
        .ok (after, handle)) :
    ∃ final,
      hostStep (.naturalLiteral value .tobject) initial [] =
        .Return [.i32 handle] final ∧
      StepResultRelated (literal initial.host.runtime (.nat value)).1
        (literal initial.host.runtime (.nat value)).2 .tobject final (.i32 handle) ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := (literal initial.host.runtime (.nat value)).1
      handles := after
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_naturalLiteral_of_encode initial value encoded
  · constructor
    · rfl
    have decoded := decodeAs_of_encode invariant.coherent (kind := AbiKind.tobject)
      (value := (literal initial.host.runtime (.nat value)).2) (handle := handle)
      (after := after) (by rfl) encoded
    change decodeValue after .tobject (.i32 handle) =
      .ok (literal initial.host.runtime (.nat value)).2
    simp only [decodeValue]
    rw [decoded]
  · exact handleTableInvariant_of_encode invariant (by rfl) encoded

/-- String-literal analogue of `naturalLiteral_host_simulates`. -/
theorem stringLiteral_host_simulates
    (initial : Wasm.Store RuntimeHost) (value : String) {after : HandleTable}
    {handle : Handle}
    (invariant : HandleTableInvariant initial.host.handles)
    (encoded :
      initial.host.handles.encode .object (literal initial.host.runtime (.str value)).2 =
        .ok (after, handle)) :
    ∃ final,
      hostStep (.stringLiteral value .object) initial [] =
        .Return [.i32 handle] final ∧
      StepResultRelated (literal initial.host.runtime (.str value)).1
        (literal initial.host.runtime (.str value)).2 .object final (.i32 handle) ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := (literal initial.host.runtime (.str value)).1
      handles := after
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_stringLiteral_of_encode initial value encoded
  · constructor
    · rfl
    have decoded := decodeAs_of_encode invariant.coherent (kind := AbiKind.object)
      (value := (literal initial.host.runtime (.str value)).2) (handle := handle)
      (after := after) (by rfl) encoded
    change decodeValue after .object (.i32 handle) =
      .ok (literal initial.host.runtime (.str value)).2
    simp only [decodeValue]
    rw [decoded]
  · exact handleTableInvariant_of_encode invariant (by rfl) encoded

/-- Constructor-allocation analogue of the literal host simulations. -/
theorem constructor_host_simulates
    (initial : Wasm.Store RuntimeHost) (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (semanticArgs : Array Value)
    (sourceRuntime : RuntimeState) (sourceValue : Value) {after : HandleTable}
    {handle : Handle}
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs :
      decodeArgs initial.host.handles fieldKinds physicalArgs = .ok semanticArgs)
    (allocated : allocCtor initial.host.runtime info semanticArgs =
      .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, handle)) :
    ∃ final,
      hostStep (.allocCtor info fieldKinds resultKind) initial physicalArgs =
        .Return [.i32 handle] final ∧
      StepResultRelated sourceRuntime sourceValue resultKind final (.i32 handle) ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      handles := after
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_allocCtor_of_decode_encode initial info fieldKinds resultKind
      physicalArgs semanticArgs sourceRuntime sourceValue decodedArgs allocated usesHandle encoded
  · constructor
    · rfl
    have decoded := decodeAs_of_encode invariant.coherent usesHandle encoded
    exact decodeValue_handle_of_decodeAs usesHandle decoded
  · exact handleTableInvariant_of_encode invariant usesHandle encoded

/-- Object-field projection preserves the source runtime and decoded result. -/
theorem objectProjection_host_simulates
    (initial : Wasm.Store RuntimeHost) (index : Nat) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (sourceObject sourceValue : Value)
    {after : HandleTable} {handle : Handle}
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (projected : getObjectField initial.host.runtime sourceObject index = .ok sourceValue)
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, handle)) :
    ∃ final,
      hostStep (.objectProj index resultKind) initial physicalArgs =
        .Return [.i32 handle] final ∧
      StepResultRelated initial.host.runtime sourceValue resultKind final (.i32 handle) ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      handles := after
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_objectProj_of_decode_encode initial index resultKind physicalArgs
      sourceObject sourceValue decodedArgs projected usesHandle encoded
  · constructor
    · rfl
    have decoded := decodeAs_of_encode invariant.coherent usesHandle encoded
    exact decodeValue_handle_of_decodeAs usesHandle decoded
  · exact handleTableInvariant_of_encode invariant usesHandle encoded

/-- Constructor tag lookup preserves the source tag modulo the checked i32 lane. -/
theorem getTag_host_simulates
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (sourceObject : Value) (tag : Nat)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (tagged : getTag initial.host.runtime sourceObject = .ok tag) :
    ∃ final,
      hostStep .getTag initial physicalArgs =
        .Return [.i32 (UInt32.ofNat tag)] final ∧
      StepResultRelated initial.host.runtime (.scalar (.uint32 (UInt32.ofNat tag)))
        .uint32 final (.i32 (UInt32.ofNat tag)) ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_getTag_of_decode initial physicalArgs sourceObject tag decodedArgs tagged
  · exact ⟨rfl, decodeValue_uint32 initial.host.handles (UInt32.ofNat tag)⟩
  · exact invariant

/--
An exact successful semantic-host step discharges Talos's abstract
host-contract call rule. This is the common instruction-level lifting used by
literal, constructor, projection, and tag operations.
-/
theorem wp_host_call_of_return
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {operation : HostOperation} {rest : Wasm.Program}
    {Q : Wasm.Assertion RuntimeHost} {initial final : Wasm.Store RuntimeHost}
    {s : Wasm.Locals} {physicalArgs results : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract operation))
    (hArgs : (s.values.take imp.params.length).reverse = physicalArgs)
    (step : hostStep operation initial physicalArgs = .Return results final)
    (continued :
      Wasm.wp module rest Q final
        { s with values := results.take imp.results.length ++
            s.values.drop imp.params.length } env) :
    Wasm.wp module (.call id :: rest) Q initial s env := by
  apply Wasm.wp_call_host_contract hImp hSat hi hContract
  · intro actualResults actualFinal contract
    change Wasm.HostResult.Return actualResults actualFinal =
      hostStep operation initial (s.values.take imp.params.length).reverse at contract
    rw [hArgs, step] at contract
    injection contract with resultsEq finalEq
    subst resultsEq
    subst finalEq
    exact continued
  · intro trapped message contract
    change Wasm.HostResult.Trap trapped message =
      hostStep operation initial (s.values.take imp.params.length).reverse at contract
    rw [hArgs, step] at contract
    contradiction

/--
Stack-shaped form of `wp_host_call_of_return`. Generated argument code pushes
source-order arguments onto the front of the operand stack, so the physical
call stack contains `physicalArgs.reverse`; Talos reverses that prefix at the
host boundary and preserves the untouched tail after the call.
-/
theorem wp_host_call_on_stack_of_return
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {operation : HostOperation} {rest : Wasm.Program}
    {Q : Wasm.Assertion RuntimeHost} {initial final : Wasm.Store RuntimeHost}
    {locals : Wasm.Locals} {physicalArgs results tail : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract operation))
    (hParams : imp.params.length = physicalArgs.length)
    (hStack : locals.values = physicalArgs.reverse ++ tail)
    (step : hostStep operation initial physicalArgs = .Return results final)
    (continued :
      Wasm.wp module rest Q final
        { locals with values := results.take imp.results.length ++ tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_of_return
    (physicalArgs := physicalArgs) (results := results)
    hImp hSat hi hContract
  · rw [hStack, hParams]
    simp
  · exact step
  · simpa [hStack, hParams] using continued

/--
Instruction-level lifting for a natural-literal import. The premise about the
continuation is stated after the exact successful host state and physical
result; Talos's abstract host contract rules out both an unstructured trap and
dependence on the concrete resolver implementation.
-/
theorem wp_naturalLiteral_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost} {s : Wasm.Locals}
    (initial : Wasm.Store RuntimeHost) (value : Nat) {after : HandleTable}
    {handle : Handle}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.naturalLiteral value .tobject)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .tobject (literal initial.host.runtime (.nat value)).2 =
        .ok (after, handle))
    (continued :
      Wasm.wp module rest Q {
        initial with host := {
          initial.host with
          runtime := (literal initial.host.runtime (.nat value)).1
          handles := after
          fault? := none
          targetFailure? := none } }
        { s with values := .i32 handle :: s.values } env) :
    Wasm.wp module (.call id :: rest) Q initial s env := by
  apply Wasm.wp_call_host_contract hImp hSat hi hContract
  · intro results final contract
    change Wasm.HostResult.Return results final =
      hostStep (.naturalLiteral value .tobject) initial
        (s.values.take imp.params.length).reverse at contract
    rw [hParams] at contract
    simp only [List.length_nil, List.take_zero, List.reverse_nil] at contract
    rw [hostStep_naturalLiteral_of_encode initial value encoded] at contract
    injection contract with resultsEq finalEq
    subst resultsEq
    subst finalEq
    simpa [hParams, hResults] using continued
  · intro final message contract
    change Wasm.HostResult.Trap final message =
      hostStep (.naturalLiteral value .tobject) initial
        (s.values.take imp.params.length).reverse at contract
    rw [hParams] at contract
    simp only [List.length_nil, List.take_zero, List.reverse_nil] at contract
    rw [hostStep_naturalLiteral_of_encode initial value encoded] at contract
    contradiction

/-- Instruction-level lifting for a string-literal import. -/
theorem wp_stringLiteral_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost} {s : Wasm.Locals}
    (initial : Wasm.Store RuntimeHost) (value : String) {after : HandleTable}
    {handle : Handle}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.stringLiteral value .object)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .object (literal initial.host.runtime (.str value)).2 =
        .ok (after, handle))
    (continued :
      Wasm.wp module rest Q {
        initial with host := {
          initial.host with
          runtime := (literal initial.host.runtime (.str value)).1
          handles := after
          fault? := none
          targetFailure? := none } }
        { s with values := .i32 handle :: s.values } env) :
    Wasm.wp module (.call id :: rest) Q initial s env := by
  apply Wasm.wp_call_host_contract hImp hSat hi hContract
  · intro results final contract
    change Wasm.HostResult.Return results final =
      hostStep (.stringLiteral value .object) initial
        (s.values.take imp.params.length).reverse at contract
    rw [hParams] at contract
    simp only [List.length_nil, List.take_zero, List.reverse_nil] at contract
    rw [hostStep_stringLiteral_of_encode initial value encoded] at contract
    injection contract with resultsEq finalEq
    subst resultsEq
    subst finalEq
    simpa [hParams, hResults] using continued
  · intro final message contract
    change Wasm.HostResult.Trap final message =
      hostStep (.stringLiteral value .object) initial
        (s.values.take imp.params.length).reverse at contract
    rw [hParams] at contract
    simp only [List.length_nil, List.take_zero, List.reverse_nil] at contract
    rw [hostStep_stringLiteral_of_encode initial value encoded] at contract
    contradiction

/--
The exact stack transformer generated after a constructor-tag lookup: push the
candidate tag, compare it with the lookup result, and dispatch to the matching
branch. Both arms start with the pre-comparison operand tail, while normal
fallthrough from an arm restores that tail because the generated `if` has no
parameters or results.
-/
theorem wp_i32Eq_ifElse
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {store : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (actual expected : UInt32) (tail : List Wasm.Value)
    (hBody :
      Wasm.wp module (if actual = expected then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := tail } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := tail } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        store { locals with values := tail } env) :
    Wasm.wp module
      (.const expected :: .eq :: .iff 0 0 thenBody elseBody :: rest)
      Q store { locals with values := .i32 actual :: tail } env := by
  rw [Wasm.wp_const_cons, Wasm.wp_eq_cons]
  apply Wasm.wp_iff_cons
    (c := if actual = expected then 1 else 0) (vs := tail) rfl
  convert hBody using 1
  all_goals simp
  all_goals
    funext continuation
    cases continuation with
    | Break level nextStore nextLocals =>
        cases level <;> rfl
    | _ => rfl

/--
Composition rule for the exact Talos sequence produced by one constructor-case
test after adaptation. It resolves the discriminator local, invokes the
abstract `getTag` contract on the generated one-argument stack, compares the
returned lane, and selects the corresponding arm without exposing the
concrete host resolver.
-/
theorem wp_getTag_case_test_of_return
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial final : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {localIndex : Nat} {handle actual expected : UInt32}
    (hLocal : locals.get localIndex = some (.i32 handle))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract .getTag))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (step :
      hostStep .getTag initial [.i32 handle] =
        .Return [.i32 actual] final)
    (hBody :
      Wasm.wp module (if actual = expected then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        final { locals with values := locals.values } env) :
    Wasm.wp module
      (.localGet localIndex :: .call id :: .const expected :: .eq ::
        .iff 0 0 thenBody elseBody :: rest)
      Q initial locals env := by
  rw [Wasm.wp_localGet_cons, hLocal]
  apply wp_host_call_of_return
    (physicalArgs := [.i32 handle]) (results := [.i32 actual])
    hImp hSat hi hContract
  · simp [hParams]
  · exact step
  · simpa [hParams, hResults] using
      wp_i32Eq_ifElse actual expected locals.values hBody

/--
Source-facing constructor-case rule. The source discriminator and candidate
tags are compared as naturals, while the generated target compares their
`i32` encodings. The two explicit range premises are precisely the executable
invariants enforced for constructor allocations and case alternatives.
-/
theorem wp_getTag_case_test
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {localIndex : Nat} {handle : UInt32}
    (sourceObject : Value) (actualTag expectedTag : Nat)
    (hLocal : locals.get localIndex = some (.i32 handle))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract .getTag))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles #[.tobject] [.i32 handle] =
        .ok #[sourceObject])
    (tagged : getTag initial.host.runtime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (expectedFits : expectedTag < UInt32.size)
    (hBody :
      Wasm.wp module (if actualTag = expectedTag then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        { initial with host := {
            initial.host with
            fault? := none
            targetFailure? := none } }
        { locals with values := locals.values } env) :
    Wasm.wp module
      (.localGet localIndex :: .call id ::
        .const (UInt32.ofNat expectedTag) :: .eq ::
        .iff 0 0 thenBody elseBody :: rest)
      Q initial locals env := by
  apply wp_getTag_case_test_of_return
    hLocal hImp hSat hi hContract hParams hResults
  · exact hostStep_getTag_of_decode initial [.i32 handle]
      sourceObject actualTag decoded tagged
  · simpa only [constructorTag_i32_eq_iff actualFits expectedFits] using hBody

/--
Generated-stack rule for constructor allocation. Source-order physical fields
appear reversed on the Talos operand stack, are decoded in source order by the
host boundary, and are replaced by the single encoded constructor handle.
-/
theorem wp_constructor_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (info : Lean.Compiler.LCNF.CtorInfo) (fieldKinds : Array AbiKind)
    (resultKind : AbiKind) (physicalArgs : List Wasm.Value)
    (semanticArgs : Array Value) (sourceRuntime : RuntimeState)
    (sourceValue : Value) (after : HandleTable) (handle : Handle)
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (hostContract (.allocCtor info fieldKinds resultKind)))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = physicalArgs.reverse ++ tail)
    (decoded :
      decodeArgs initial.host.handles fieldKinds physicalArgs = .ok semanticArgs)
    (allocated :
      allocCtor initial.host.runtime info semanticArgs =
        .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded :
      initial.host.handles.encode resultKind sourceValue = .ok (after, handle))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            runtime := sourceRuntime
            handles := after
            fault? := none
            targetFailure? := none } }
        { locals with values := .i32 handle :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := physicalArgs) (results := [.i32 handle])
    hImp hSat hi hContract hParams hStack
  · exact hostStep_allocCtor_of_decode_encode initial info fieldKinds resultKind
      physicalArgs semanticArgs sourceRuntime sourceValue decoded allocated usesHandle encoded
  · simpa [hResults] using continued

/--
Generated-stack rule for object projection. The discriminator handle is the
single call argument and is replaced by the encoded projected field while the
operand tail and source runtime are preserved.
-/
theorem wp_objectProjection_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (index : Nat) (resultKind : AbiKind) (objectHandle : Handle)
    (sourceObject sourceValue : Value) (after : HandleTable)
    (resultHandle : Handle) (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (hostContract (.objectProj index resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = .i32 objectHandle :: tail)
    (decoded :
      decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
        .ok #[sourceObject])
    (projected :
      getObjectField initial.host.runtime sourceObject index = .ok sourceValue)
    (usesHandle : resultKind.usesHandle = true)
    (encoded :
      initial.host.handles.encode resultKind sourceValue = .ok (after, resultHandle))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            handles := after
            fault? := none
            targetFailure? := none } }
        { locals with values := .i32 resultHandle :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := [.i32 objectHandle]) (results := [.i32 resultHandle])
    hImp hSat hi hContract
  · simpa using hParams
  · simpa using hStack
  · exact hostStep_objectProj_of_decode_encode initial index resultKind
      [.i32 objectHandle] sourceObject sourceValue decoded projected usesHandle encoded
  · simpa [hResults] using continued

end FirTalos.Correctness
