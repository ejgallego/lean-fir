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

theorem compileLetValue_usizeProjection
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {index : Nat} {objectId : Lean.FVarId} {objectKind : AbiKind}
    {objectInstruction : Instruction}
    (valueEq : decl.value = .uproj index objectId)
    (resultEq : letValueKind decl = .ok .usize)
    (objectEq : getLocal context objectId = .ok (objectInstruction, objectKind)) :
    compileLetValue context decl =
      .ok [objectInstruction, .call (.runtime (.usizeProj index))] := by
  simp [compileLetValue, valueEq, resultEq, objectEq]
  rfl

theorem compileLetValue_scalarProjection
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {width offset : Nat} {objectId : Lean.FVarId}
    {resultKind objectKind : AbiKind} {objectInstruction : Instruction}
    (valueEq : decl.value = .sproj width offset objectId)
    (resultEq : letValueKind decl = .ok resultKind)
    (objectEq : getLocal context objectId = .ok (objectInstruction, objectKind)) :
    compileLetValue context decl =
      .ok [objectInstruction,
        .call (.runtime (.scalarProj width offset resultKind))] := by
  simp [compileLetValue, valueEq, resultEq, objectEq]
  rfl

theorem compileLetValue_box
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {type : Lean.Expr} {scalarId : Lean.FVarId}
    {scalarKind resultKind : AbiKind} {scalarInstruction : Instruction}
    (valueEq : decl.value = .box type scalarId)
    (resultEq : letValueKind decl = .ok resultKind)
    (scalarEq : getLocal context scalarId = .ok (scalarInstruction, scalarKind))
    (annotationEq : checkedAbiKind type = .ok scalarKind) :
    compileLetValue context decl =
      .ok [scalarInstruction, .call (.runtime (.box scalarKind resultKind))] := by
  have notDifferent : ¬(scalarKind != scalarKind) = true := by
    cases scalarKind <;> decide
  simp [compileLetValue, valueEq, resultEq, scalarEq, annotationEq]
  change (if (scalarKind != scalarKind) = true then _ else
    Except.ok [scalarInstruction, .call (.runtime (.box scalarKind resultKind))]) = _
  rw [if_neg notDifferent]

theorem compileLetValue_unbox
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {objectId : Lean.FVarId} {objectKind resultKind : AbiKind}
    {objectInstruction : Instruction}
    (valueEq : decl.value = .unbox objectId)
    (resultEq : letValueKind decl = .ok resultKind)
    (objectEq : getLocal context objectId = .ok (objectInstruction, objectKind)) :
    compileLetValue context decl =
      .ok [objectInstruction, .call (.runtime (.unbox resultKind))] := by
  simp [compileLetValue, valueEq, resultEq, objectEq]
  rfl

theorem compileLetValue_isShared
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {objectId : Lean.FVarId} {objectKind : AbiKind}
    {objectInstruction : Instruction}
    (valueEq : decl.value = .isShared objectId)
    (resultEq : letValueKind decl = .ok .uint8)
    (objectEq : getLocal context objectId = .ok (objectInstruction, objectKind)) :
    compileLetValue context decl =
      .ok [objectInstruction, .call (.runtime .isShared)] := by
  simp [compileLetValue, valueEq, resultEq, objectEq]
  rfl

theorem compileLetValue_reset
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {count : Nat} {objectId : Lean.FVarId} {objectKind : AbiKind}
    {objectInstruction : Instruction}
    (valueEq : decl.value = .reset count objectId)
    (resultEq : letValueKind decl = .ok .reuseToken)
    (objectEq : getLocal context objectId = .ok (objectInstruction, objectKind)) :
    compileLetValue context decl =
      .ok [objectInstruction, .call (.runtime (.reset count))] := by
  simp [compileLetValue, valueEq, resultEq, objectEq]
  rfl

theorem compileLetValue_reuse
    {context : Context} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {tokenId : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {tokenKind resultKind : AbiKind} {tokenInstruction : Instruction}
    {argumentCode : List Instruction} {fieldKinds : Array AbiKind}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (resultEq : letValueKind decl = .ok resultKind)
    (tokenEq : getLocal context tokenId = .ok (tokenInstruction, tokenKind))
    (argumentsEq : compileArgs context args = .ok (argumentCode, fieldKinds)) :
    compileLetValue context decl =
      .ok (tokenInstruction :: argumentCode ++
        [.call (.runtime (.reuse info updateHeader fieldKinds resultKind))]) := by
  simp [compileLetValue, valueEq, resultEq, tokenEq, argumentsEq]
  rfl

theorem compileCaseChain_constructor_of_mode
    {context : Context} {discr : Lean.FVarId}
    {mode : CaseDiscriminatorMode}
    {info : Lean.Compiler.LCNF.CtorInfo} {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)} {fallback thenBody elseBody : List Instruction}
    (modeEq : caseDiscriminatorMode context discr = mode)
    (fits : caseConstructorTagFits mode info = true)
    (thenEq : compileCode context code = .ok thenBody)
    (elseEq : compileCaseChain context discr alts fallback = .ok elseBody) :
    compileCaseChain context discr (.ctorAlt info code :: alts) fallback =
      .ok (caseTagTest mode discr info ++
        [.i32Eq, .ifElse thenBody elseBody]) := by
  change compileCaseChainWithM (compileCode context)
    (caseDiscriminatorMode context discr) discr alts fallback =
    .ok elseBody at elseEq
  change compileCaseChainWithM (compileCode context)
    (caseDiscriminatorMode context discr) discr (.ctorAlt info code :: alts)
      fallback = _
  rw [modeEq] at elseEq ⊢
  rw [compileCaseChainWithM.eq_def]
  simp only [fits, ↓reduceIte]
  rw [thenEq, elseEq]
  rfl

theorem compileCaseChain_constructor
    {context : Context} {discr : Lean.FVarId}
    {info : Lean.Compiler.LCNF.CtorInfo} {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback thenBody elseBody : List Instruction}
    (modeEq : caseDiscriminatorMode context discr = .objectTag)
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
  simpa [caseConstructorTagFits, caseTagTest] using
    compileCaseChain_constructor_of_mode modeEq fits thenEq elseEq

theorem compileCaseChain_scalarUInt8_constructor
    {context : Context} {discr : Lean.FVarId}
    {info : Lean.Compiler.LCNF.CtorInfo} {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback thenBody elseBody : List Instruction}
    (modeEq : caseDiscriminatorMode context discr = .scalarUInt8)
    (fits : constructorTagFitsUInt8 info = true)
    (thenEq : compileCode context code = .ok thenBody)
    (elseEq : compileCaseChain context discr alts fallback = .ok elseBody) :
    compileCaseChain context discr (.ctorAlt info code :: alts) fallback =
      .ok [
        .localGet discr,
        .i32Const .uint8 (UInt32.ofNat info.cidx),
        .i32Eq,
        .ifElse thenBody elseBody] := by
  simpa [caseConstructorTagFits, caseTagTest] using
    compileCaseChain_constructor_of_mode modeEq fits thenEq elseEq

theorem constructorTag_i32_eq_iff {left right : Nat}
    (leftFits : left < UInt32.size) (rightFits : right < UInt32.size) :
    UInt32.ofNat left = UInt32.ofNat right ↔ left = right := by
  constructor
  · intro equal
    have := congrArg UInt32.toNat equal
    simpa [UInt32.toNat_ofNat_of_lt' leftFits,
      UInt32.toNat_ofNat_of_lt' rightFits] using this
  · exact congrArg UInt32.ofNat

theorem constructorTag_uint8_eq_iff {left right : Nat}
    (leftFits : left < UInt8.size) (rightFits : right < UInt8.size) :
    UInt32.ofNat left = UInt32.ofNat right ↔ left = right := by
  have sizeLe : UInt8.size ≤ UInt32.size := by native_decide
  exact constructorTag_i32_eq_iff
    (lt_of_lt_of_le leftFits sizeLe) (lt_of_lt_of_le rightFits sizeLe)

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

/-- USize-field projection leaves both semantic runtime and handle table
unchanged while returning the direct `i64` lane. -/
theorem usizeProjection_host_simulates
    (initial : Wasm.Store RuntimeHost) (index : Nat)
    (physicalArgs : List Wasm.Value) (sourceObject : Value) (value : UInt64)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (projected : getUSizeField initial.host.runtime sourceObject index =
      .ok (.usize value)) :
    ∃ final,
      hostStep (.usizeProj index) initial physicalArgs =
        .Return [.i64 value] final ∧
      StepResultRelated initial.host.runtime (.usize value) .usize final
        (.i64 value) ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_usizeProj_of_decode initial index physicalArgs sourceObject value
      decodedArgs projected
  · exact ⟨rfl, decodeValue_usize initial.host.handles value⟩
  · exact invariant

/-- Integer scalar-field projection also preserves the handle table. The
explicit encode/decode facts state the dynamic type invariant connecting the
declared result kind to the stored scalar value. -/
theorem scalarProjection_host_simulates
    (initial : Wasm.Store RuntimeHost) (width offset : Nat)
    (resultKind : AbiKind) (physicalArgs : List Wasm.Value)
    (sourceObject sourceValue : Value) (physical : Wasm.Value)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (projected : getScalarField initial.host.runtime sourceObject width offset =
      .ok sourceValue)
    (encoded : encodeValue initial.host.handles resultKind sourceValue =
      .ok (initial.host.handles, physical))
    (decodedResult : DecodesValue initial.host.handles resultKind physical sourceValue) :
    ∃ final,
      hostStep (.scalarProj width offset resultKind) initial physicalArgs =
        .Return [physical] final ∧
      StepResultRelated initial.host.runtime sourceValue resultKind final physical ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_scalarProj_of_decode_encode initial width offset resultKind
      physicalArgs sourceObject sourceValue physical decodedArgs projected encoded
  · exact ⟨rfl, decodedResult⟩
  · exact invariant

/-- Boxing may allocate and therefore follows the handle-result invariant
path used by constructor allocation. -/
theorem box_host_simulates
    (initial : Wasm.Store RuntimeHost) (scalarKind resultKind : AbiKind)
    (type : Lean.Expr) (physicalArgs : List Wasm.Value) (sourceScalar : Value)
    (sourceRuntime : RuntimeState) (sourceValue : Value)
    {after : HandleTable} {handle : Handle}
    (invariant : HandleTableInvariant initial.host.handles)
    (typeEq : runtimeScalarType? scalarKind = some type)
    (decodedArgs : decodeArgs initial.host.handles #[scalarKind] physicalArgs =
      .ok #[sourceScalar])
    (boxed : Fir.LeanIR.Impure.box initial.host.runtime type sourceScalar =
      .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, handle)) :
    ∃ final,
      hostStep (.box scalarKind resultKind) initial physicalArgs =
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
  · exact hostStep_box_of_decode_encode initial scalarKind resultKind type
      physicalArgs sourceScalar sourceRuntime sourceValue typeEq decodedArgs boxed
      usesHandle encoded
  · exact ⟨rfl, decodeValue_handle_of_decodeAs usesHandle
      (decodeAs_of_encode invariant.coherent usesHandle encoded)⟩
  · exact handleTableInvariant_of_encode invariant usesHandle encoded

/-- Unboxing preserves the runtime and handle table and returns a direct
integer/usize lane. -/
theorem unbox_host_simulates
    (initial : Wasm.Store RuntimeHost) (scalarKind : AbiKind) (type : Lean.Expr)
    (physicalArgs : List Wasm.Value) (sourceObject sourceValue : Value)
    (physical : Wasm.Value)
    (invariant : HandleTableInvariant initial.host.handles)
    (typeEq : runtimeScalarType? scalarKind = some type)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (unboxed : Fir.LeanIR.Impure.unbox initial.host.runtime type sourceObject =
      .ok sourceValue)
    (encoded : encodeValue initial.host.handles scalarKind sourceValue =
      .ok (initial.host.handles, physical))
    (decodedResult : DecodesValue initial.host.handles scalarKind physical sourceValue) :
    ∃ final,
      hostStep (.unbox scalarKind) initial physicalArgs = .Return [physical] final ∧
      StepResultRelated initial.host.runtime sourceValue scalarKind final physical ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_unbox_of_decode_encode initial scalarKind type physicalArgs
      sourceObject sourceValue physical typeEq decodedArgs unboxed encoded
  · exact ⟨rfl, decodedResult⟩
  · exact invariant

/-- `isShared` preserves runtime and handles and returns Lean's checked UInt8
case discriminator. -/
theorem isShared_host_simulates
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (sourceObject : Value) (shared : UInt8)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (evaluated : Fir.LeanIR.Impure.isShared initial.host.runtime sourceObject =
      .ok (.scalar (.uint8 shared))) :
    ∃ final,
      hostStep .isShared initial physicalArgs =
        .Return [.i32 (UInt32.ofNat shared.toNat)] final ∧
      StepResultRelated initial.host.runtime (.scalar (.uint8 shared)) .uint8 final
        (.i32 (UInt32.ofNat shared.toNat)) ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_isShared_of_decode initial physicalArgs sourceObject shared
      decodedArgs evaluated
  · exact ⟨rfl, decodeValue_uint8 initial.host.handles shared⟩
  · exact invariant

/-- Reset returns an opaque reuse-token handle while threading the exact source
runtime update. -/
theorem reset_host_simulates
    (initial : Wasm.Store RuntimeHost) (objectFields : Nat)
    (physicalArgs : List Wasm.Value) (sourceObject : Value)
    (sourceRuntime : RuntimeState) (sourceToken : Value)
    {after : HandleTable} {handle : Handle}
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (resetResult : Fir.LeanIR.Impure.reset initial.host.runtime objectFields
      sourceObject = .ok (sourceRuntime, sourceToken))
    (encoded : initial.host.handles.encode .reuseToken sourceToken =
      .ok (after, handle)) :
    ∃ final,
      hostStep (.reset objectFields) initial physicalArgs =
        .Return [.i32 handle] final ∧
      StepResultRelated sourceRuntime sourceToken .reuseToken final (.i32 handle) ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      handles := after
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, ?_, ?_⟩
  · exact hostStep_reset_of_decode_encode initial objectFields physicalArgs
      sourceObject sourceRuntime sourceToken decodedArgs resetResult encoded
  · exact ⟨rfl, decodeValue_handle_of_decodeAs (by rfl)
      (decodeAs_of_encode invariant.coherent (by rfl) encoded)⟩
  · exact handleTableInvariant_of_encode invariant (by rfl) encoded

theorem reuse_host_simulates
    (initial : Wasm.Store RuntimeHost) (info : Lean.Compiler.LCNF.CtorInfo)
    (updateHeader : Bool) (fieldKinds : Array AbiKind) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (semanticArgs : Array Value)
    (sourceToken : Value) (sourceRuntime : RuntimeState) (sourceValue : Value)
    {after : HandleTable} {handle : Handle}
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles (#[.reuseToken] ++ fieldKinds)
      physicalArgs = .ok semanticArgs)
    (tokenHead : semanticArgs[0]? = some sourceToken)
    (reused : Fir.LeanIR.Impure.reuse initial.host.runtime sourceToken info
      updateHeader (semanticArgs.extract 1 semanticArgs.size) =
        .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, handle)) :
    ∃ final,
      hostStep (.reuse info updateHeader fieldKinds resultKind) initial physicalArgs =
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
  · exact hostStep_reuse_of_decode_encode initial info updateHeader fieldKinds
      resultKind physicalArgs semanticArgs sourceToken sourceRuntime sourceValue
      decodedArgs tokenHead reused usesHandle encoded
  · exact ⟨rfl, decodeValue_handle_of_decodeAs usesHandle
      (decodeAs_of_encode invariant.coherent usesHandle encoded)⟩
  · exact handleTableInvariant_of_encode invariant usesHandle encoded

/-- Object-field mutation changes only the semantic runtime. Existing handles
continue to denote the same object references. -/
theorem objectSet_host_simulates
    (initial : Wasm.Store RuntimeHost) (index : Nat) (fieldKind : AbiKind)
    (physicalArgs : List Wasm.Value) (sourceObject sourceField : Value)
    (sourceRuntime : RuntimeState)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.object, fieldKind] physicalArgs =
      .ok #[sourceObject, sourceField])
    (mutated : setObjectField initial.host.runtime sourceObject index sourceField =
      .ok sourceRuntime) :
    ∃ final,
      hostStep (.objectSet index fieldKind) initial physicalArgs =
        .Return [] final ∧
      final.host.runtime = sourceRuntime ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, rfl, invariant⟩
  exact hostStep_objectSet_of_decode initial index fieldKind physicalArgs
    sourceObject sourceField sourceRuntime decodedArgs mutated

theorem usizeSet_host_simulates
    (initial : Wasm.Store RuntimeHost) (index : Nat)
    (physicalArgs : List Wasm.Value) (sourceObject sourceField : Value)
    (sourceRuntime : RuntimeState)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.object, .usize] physicalArgs =
      .ok #[sourceObject, sourceField])
    (mutated : setUSizeField initial.host.runtime sourceObject index sourceField =
      .ok sourceRuntime) :
    ∃ final,
      hostStep (.usizeSet index) initial physicalArgs = .Return [] final ∧
      final.host.runtime = sourceRuntime ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, rfl, invariant⟩
  exact hostStep_usizeSet_of_decode initial index physicalArgs sourceObject
    sourceField sourceRuntime decodedArgs mutated

theorem scalarSet_host_simulates
    (initial : Wasm.Store RuntimeHost) (width offset : Nat)
    (fieldKind : AbiKind) (physicalArgs : List Wasm.Value)
    (sourceObject sourceField : Value) (sourceRuntime : RuntimeState)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.object, fieldKind] physicalArgs =
      .ok #[sourceObject, sourceField])
    (mutated : setScalarField initial.host.runtime sourceObject width offset sourceField =
      .ok sourceRuntime) :
    ∃ final,
      hostStep (.scalarSet width offset fieldKind) initial physicalArgs =
        .Return [] final ∧
      final.host.runtime = sourceRuntime ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, rfl, invariant⟩
  exact hostStep_scalarSet_of_decode initial width offset fieldKind physicalArgs
    sourceObject sourceField sourceRuntime decodedArgs mutated

theorem setTag_host_simulates
    (initial : Wasm.Store RuntimeHost) (tag : Nat)
    (physicalArgs : List Wasm.Value) (sourceObject : Value)
    (sourceRuntime : RuntimeState)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.object] physicalArgs =
      .ok #[sourceObject])
    (mutated : Fir.LeanIR.Impure.setTag initial.host.runtime sourceObject tag =
      .ok sourceRuntime) :
    ∃ final,
      hostStep (.setTag tag) initial physicalArgs = .Return [] final ∧
      final.host.runtime = sourceRuntime ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, rfl, invariant⟩
  exact hostStep_setTag_of_decode initial tag physicalArgs sourceObject
    sourceRuntime decodedArgs mutated

theorem inc_host_simulates
    (initial : Wasm.Store RuntimeHost) (amount : Nat) (check : Bool)
    (physicalArgs : List Wasm.Value) (sourceObject : Value)
    (sourceRuntime : RuntimeState)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (updated : incValue initial.host.runtime sourceObject amount check =
      .ok sourceRuntime) :
    ∃ final,
      hostStep (.inc amount check) initial physicalArgs = .Return [] final ∧
      final.host.runtime = sourceRuntime ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, rfl, invariant⟩
  exact hostStep_inc_of_decode initial amount check physicalArgs sourceObject
    sourceRuntime decodedArgs updated

theorem dec_host_simulates
    (initial : Wasm.Store RuntimeHost) (amount : Nat) (check : Bool)
    (objectFields? : Option Nat) (physicalArgs : List Wasm.Value)
    (sourceObject : Value) (sourceRuntime : RuntimeState)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[sourceObject])
    (updated : decValue initial.host.runtime sourceObject amount check =
      .ok sourceRuntime) :
    ∃ final,
      hostStep (.dec amount check objectFields?) initial physicalArgs =
        .Return [] final ∧
      final.host.runtime = sourceRuntime ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, rfl, invariant⟩
  exact hostStep_dec_of_decode initial amount check objectFields? physicalArgs
    sourceObject sourceRuntime decodedArgs updated

theorem delete_host_simulates
    (initial : Wasm.Store RuntimeHost) (physicalArgs : List Wasm.Value)
    (sourceObject : Value) (sourceRuntime : RuntimeState)
    (invariant : HandleTableInvariant initial.host.handles)
    (decodedArgs : decodeArgs initial.host.handles #[.object] physicalArgs =
      .ok #[sourceObject])
    (updated : deleteValue initial.host.runtime sourceObject = .ok sourceRuntime) :
    ∃ final,
      hostStep .delete initial physicalArgs = .Return [] final ∧
      final.host.runtime = sourceRuntime ∧
      HandleTableInvariant final.host.handles := by
  let final : Wasm.Store RuntimeHost := {
    initial with host := {
      initial.host with
      runtime := sourceRuntime
      fault? := none
      targetFailure? := none } }
  refine ⟨final, ?_, rfl, invariant⟩
  exact hostStep_delete_of_decode initial physicalArgs sourceObject sourceRuntime
    decodedArgs updated

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

/-- A successful no-result semantic host call consumes its arguments, updates
the host state, and resumes with the untouched operand tail. -/
theorem wp_host_effect_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {operation : HostOperation} {rest : Wasm.Program}
    {Q : Wasm.Assertion RuntimeHost} {initial final : Wasm.Store RuntimeHost}
    {locals : Wasm.Locals} {physicalArgs tail : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract operation))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 0)
    (hStack : locals.values = physicalArgs.reverse ++ tail)
    (step : hostStep operation initial physicalArgs = .Return [] final)
    (continued :
      Wasm.wp module rest Q final { locals with values := tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return hImp hSat hi hContract hParams hStack step
  simpa [hResults] using continued

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

/-- Direct scalar-case dispatch: load the `UInt8` discriminator, compare it
with the range-checked constructor index, and select the corresponding arm. -/
theorem wp_scalarUInt8_case_test
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {store : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {localIndex : Nat} (actualTag expectedTag : Nat)
    (hLocal :
      locals.get localIndex = some (.i32 (UInt32.ofNat actualTag)))
    (actualFits : actualTag < UInt8.size)
    (expectedFits : expectedTag < UInt8.size)
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
        store { locals with values := locals.values } env) :
    Wasm.wp module
      (.localGet localIndex :: .const (UInt32.ofNat expectedTag) :: .eq ::
        .iff 0 0 thenBody elseBody :: rest)
      Q store locals env := by
  rw [Wasm.wp_localGet_cons, hLocal]
  apply wp_i32Eq_ifElse (UInt32.ofNat actualTag)
    (UInt32.ofNat expectedTag) locals.values
  simpa only [constructorTag_uint8_eq_iff actualFits expectedFits] using hBody

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

/-- Generated-stack rule for a USize projection. The object handle is
replaced by the direct `i64` field and the operand tail is preserved. -/
theorem wp_usizeProjection_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (index : Nat) (objectHandle : Handle) (sourceObject : Value)
    (value : UInt64) (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract (.usizeProj index)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = .i32 objectHandle :: tail)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject])
    (projected : getUSizeField initial.host.runtime sourceObject index =
      .ok (.usize value))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            fault? := none
            targetFailure? := none } }
        { locals with values := .i64 value :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := [.i32 objectHandle]) (results := [.i64 value])
    hImp hSat hi hContract
  · simpa using hParams
  · simpa using hStack
  · exact hostStep_usizeProj_of_decode initial index [.i32 objectHandle]
      sourceObject value decoded projected
  · simpa [hResults] using continued

/-- Generated-stack rule for an integer scalar projection. The explicit
successful encoding records the source-value/result-kind agreement. -/
theorem wp_scalarProjection_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (width offset : Nat) (resultKind : AbiKind) (objectHandle : Handle)
    (sourceObject sourceValue : Value) (physical : Wasm.Value)
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.scalarProj width offset resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = .i32 objectHandle :: tail)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject])
    (projected : getScalarField initial.host.runtime sourceObject width offset =
      .ok sourceValue)
    (encoded : encodeValue initial.host.handles resultKind sourceValue =
      .ok (initial.host.handles, physical))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            fault? := none
            targetFailure? := none } }
        { locals with values := physical :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := [.i32 objectHandle]) (results := [physical])
    hImp hSat hi hContract
  · simpa using hParams
  · simpa using hStack
  · exact hostStep_scalarProj_of_decode_encode initial width offset resultKind
      [.i32 objectHandle] sourceObject sourceValue physical decoded projected encoded
  · simpa [hResults] using continued

/-- Generated-stack rule for boxing a direct scalar into an opaque object
handle. -/
theorem wp_box_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (scalarKind resultKind : AbiKind) (type : Lean.Expr)
    (physicalScalar : Wasm.Value) (sourceScalar : Value)
    (sourceRuntime : RuntimeState) (sourceValue : Value)
    (after : HandleTable) (resultHandle : Handle) (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.box scalarKind resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = physicalScalar :: tail)
    (typeEq : runtimeScalarType? scalarKind = some type)
    (decoded : decodeArgs initial.host.handles #[scalarKind] [physicalScalar] =
      .ok #[sourceScalar])
    (boxed : Fir.LeanIR.Impure.box initial.host.runtime type sourceScalar =
      .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, resultHandle))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            runtime := sourceRuntime
            handles := after
            fault? := none
            targetFailure? := none } }
        { locals with values := .i32 resultHandle :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := [physicalScalar]) (results := [.i32 resultHandle])
    hImp hSat hi hContract
  · simpa using hParams
  · simpa using hStack
  · exact hostStep_box_of_decode_encode initial scalarKind resultKind type
      [physicalScalar] sourceScalar sourceRuntime sourceValue typeEq decoded boxed
      usesHandle encoded
  · simpa [hResults] using continued

/-- Generated-stack rule for unboxing an object handle into a direct scalar. -/
theorem wp_unbox_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (scalarKind : AbiKind) (type : Lean.Expr) (objectHandle : Handle)
    (sourceObject sourceValue : Value) (physical : Wasm.Value)
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract (.unbox scalarKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = .i32 objectHandle :: tail)
    (typeEq : runtimeScalarType? scalarKind = some type)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject])
    (unboxed : Fir.LeanIR.Impure.unbox initial.host.runtime type sourceObject =
      .ok sourceValue)
    (encoded : encodeValue initial.host.handles scalarKind sourceValue =
      .ok (initial.host.handles, physical))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            fault? := none
            targetFailure? := none } }
        { locals with values := physical :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := [.i32 objectHandle]) (results := [physical])
    hImp hSat hi hContract
  · simpa using hParams
  · simpa using hStack
  · exact hostStep_unbox_of_decode_encode initial scalarKind type [.i32 objectHandle]
      sourceObject sourceValue physical typeEq decoded unboxed encoded
  · simpa [hResults] using continued

/-- Generated-stack rule for the direct UInt8 `isShared` result. -/
theorem wp_isShared_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (objectHandle : Handle) (sourceObject : Value) (shared : UInt8)
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract .isShared))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = .i32 objectHandle :: tail)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject])
    (evaluated : Fir.LeanIR.Impure.isShared initial.host.runtime sourceObject =
      .ok (.scalar (.uint8 shared)))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            fault? := none
            targetFailure? := none } }
        { locals with values := .i32 (UInt32.ofNat shared.toNat) :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := [.i32 objectHandle])
    (results := [.i32 (UInt32.ofNat shared.toNat)]) hImp hSat hi hContract
  · simpa using hParams
  · simpa using hStack
  · exact hostStep_isShared_of_decode initial [.i32 objectHandle] sourceObject shared
      decoded evaluated
  · simpa [hResults] using continued

/-- Generated-stack rule for a successful singleton-result external call.
Unlike runtime primitives, the exact host step is driven by the
`ExternalImpl` installed in the initial `RuntimeHost`; the resulting runtime
therefore carries the same heap, world, and trace transition as the source
interpreter. -/
theorem wp_external_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (operation : ExternalOperation) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (semanticArgs : Array Value)
    (response : ExternalResponse) (after : HandleTable)
    (physicalResult : Wasm.Value) (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.external operation)))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = physicalArgs.reverse ++ tail)
    (resultSignature : operation.signature.results = #[resultKind])
    (decoded : decodeArgs initial.host.handles operation.signature.params
      physicalArgs = .ok semanticArgs)
    (called : initial.host.externals.call (operation.request semanticArgs)
      initial.host.runtime = .ok response)
    (encoded : encodeValue initial.host.handles resultKind response.value =
      .ok (after, physicalResult))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            runtime := applyExternalResponse (operation.request semanticArgs)
              initial.host.runtime response
            handles := after
            fault? := none
            targetFailure? := none } }
        { locals with values := physicalResult :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := physicalArgs) (results := [physicalResult])
    hImp hSat hi hContract hParams hStack
  · exact hostStep_external_singleton_of_decode_call_encode operation resultKind
      initial physicalArgs semanticArgs response resultSignature decoded called encoded
  · simpa [hResults] using continued

/-- Generated-stack rule for the cache-miss runtime write. The operation
returns the same physical value while extending the semantic runtime's global
environment, so the subsequent Wasm `global.set` can store that lane without
losing the source-level cache transition. -/
theorem wp_cacheSet_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (declaration : Lean.Name) (kind : AbiKind)
    (physicalArgs : List Wasm.Value) (sourceValue : Value)
    (after : HandleTable) (physicalResult : Wasm.Value)
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.cacheSet declaration kind)))
    (hParams : imp.params.length = 1)
    (hArgCount : physicalArgs.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = physicalArgs.reverse ++ tail)
    (decoded : decodeArgs initial.host.handles #[kind] physicalArgs =
      .ok #[sourceValue])
    (encoded : encodeValue initial.host.handles kind sourceValue =
      .ok (after, physicalResult))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            runtime := initial.host.runtime.setGlobal declaration sourceValue
            handles := after
            fault? := none
            targetFailure? := none } }
        { locals with values := physicalResult :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := physicalArgs) (results := [physicalResult])
    hImp hSat hi hContract
  · omega
  · exact hStack
  · exact hostStep_cacheSet_of_decode_encode declaration kind initial
      physicalArgs sourceValue decoded encoded
  · simpa [hResults] using continued

/-- Generated-stack rule for allocating a semantic partial-application
closure. The host only records the function identity and captured values; it
does not execute target code. -/
theorem wp_partialApply_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (function : Lean.Name) (arity fixed : Nat) (fieldKinds : Array AbiKind)
    (resultKind : AbiKind) (physicalArgs : List Wasm.Value)
    (semanticArgs : Array Value) (sourceRuntime : RuntimeState)
    (reference : ObjectRef) (after : HandleTable) (handle : Handle)
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (hostContract (.partialApply function arity fixed fieldKinds resultKind)))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = physicalArgs.reverse ++ tail)
    (decoded : decodeArgs initial.host.handles fieldKinds physicalArgs =
      .ok semanticArgs)
    (allocated : alloc initial.host.runtime (.closure function arity semanticArgs) =
      (sourceRuntime, reference))
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind (.object reference) =
      .ok (after, handle))
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
  · exact hostStep_partialApply_of_decode_encode function arity fixed fieldKinds
      resultKind initial physicalArgs semanticArgs sourceRuntime reference decoded
      allocated usesHandle encoded
  · simpa [hResults] using continued

/-- A successful trampoline discriminator returns direct i32 one and leaves
the semantic runtime and handle table unchanged. -/
theorem wp_closureMatches_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (function : Lean.Name) (arity fixed : Nat)
    (physicalArgs : List Wasm.Value) (closure : Value)
    (captured : Array Value) (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (hostContract (.closureMatches function arity fixed)))
    (hParams : imp.params.length = 1)
    (hArgCount : physicalArgs.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = physicalArgs.reverse ++ tail)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[closure])
    (read : closureData initial.host.runtime closure =
      .ok (function, arity, captured))
    (fixedSize : captured.size = fixed)
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            fault? := none
            targetFailure? := none } }
        { locals with values := .i32 1 :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := physicalArgs) (results := [.i32 1])
    hImp hSat hi hContract
  · omega
  · exact hStack
  · exact hostStep_closureMatches_of_decode_read function arity fixed initial
      physicalArgs closure captured decoded read fixedSize
  · simpa [hResults] using continued

/-- A successful capture projection is a pure semantic read followed by the
ordinary ABI encoding of the captured value. -/
theorem wp_closureProj_call
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    (function : Lean.Name) (arity fixed index : Nat) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value) (closure sourceValue : Value)
    (captured : Array Value) (after : HandleTable)
    (physicalResult : Wasm.Value) (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (hostContract (.closureProj function arity fixed index resultKind)))
    (hParams : imp.params.length = 1)
    (hArgCount : physicalArgs.length = 1)
    (hResults : imp.results.length = 1)
    (hStack : locals.values = physicalArgs.reverse ++ tail)
    (decoded : decodeArgs initial.host.handles #[.tobject] physicalArgs =
      .ok #[closure])
    (read : closureData initial.host.runtime closure =
      .ok (function, arity, captured))
    (fixedSize : captured.size = fixed)
    (projected : captured[index]? = some sourceValue)
    (encoded : encodeValue initial.host.handles resultKind sourceValue =
      .ok (after, physicalResult))
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            handles := after
            fault? := none
            targetFailure? := none } }
        { locals with values := physicalResult :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply wp_host_call_on_stack_of_return
    (physicalArgs := physicalArgs) (results := [physicalResult])
    hImp hSat hi hContract
  · omega
  · exact hStack
  · exact hostStep_closureProj_of_decode_read_encode function arity fixed index
      resultKind initial physicalArgs closure sourceValue captured decoded read
      fixedSize projected encoded
  · simpa [hResults] using continued

end FirTalos.Correctness
