import Fir.Validation.LCNF

namespace Fir.Validation.DirectLcnf

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure

def nativeBackend : String := "direct-native"

def lcnfBackend : String := "direct-lcnf"

private def x : FVarId := ⟨`x⟩
private def y : FVarId := ⟨`y⟩
private def z : FVarId := ⟨`z⟩
private def c : FVarId := ⟨`c⟩
private def e : FVarId := ⟨`e⟩
private def p : FVarId := ⟨`p⟩
private def q : FVarId := ⟨`q⟩
private def r : FVarId := ⟨`r⟩
private def s : FVarId := ⟨`s⟩
private def t : FVarId := ⟨`t⟩

private def objType : Expr :=
  LCNF.ImpureType.object

private def u8Type : Expr :=
  LCNF.ImpureType.uint8

private def param (fvarId : FVarId) : LCNF.Param .impure :=
  { fvarId, binderName := fvarId.name, type := objType, borrow := false }

private def typedDecl (name : Name) (params : Array (LCNF.Param .impure))
    (type : Expr)
    (value : LCNF.DeclValue .impure) : LCNF.Decl .impure :=
  { name
    levelParams := []
    type
    params
    value
    safe := true
    recursive := false
    inlineAttr? := none }

private def decl (name : Name) (params : Array (LCNF.Param .impure))
    (value : LCNF.DeclValue .impure) : LCNF.Decl .impure :=
  typedDecl name params objType value

private def typedLetDecl (fvarId : FVarId) (type : Expr)
    (value : LCNF.LetValue .impure) :
    LCNF.LetDecl .impure :=
  { fvarId, binderName := fvarId.name, type, value }

private def letDecl (fvarId : FVarId) (value : LCNF.LetValue .impure) :
    LCNF.LetDecl .impure :=
  typedLetDecl fvarId objType value

/--
A validation case whose candidate is an explicit final-impure program rather
than source compiled by Lean. These cases cover machine transitions that the
current source compiler does not emit.
-/
structure NativeOracleAttestation where
  entry : Name
  dependencies : Array Name := #[]
  claim : String
  requiredArtifactFragments : Array String := #[]
  requiredOwnershipFacts : Array String := #[]
  expectedArtifactSha256 : String
  deriving Inhabited

structure NativeOracleDescriptor where
  version : Nat := protocolVersion
  caseId : String
  entry : String
  dependencies : Array String
  claim : String
  requiredArtifactFragments : Array String
  requiredOwnershipFacts : Array String
  expectedArtifactSha256 : String
  deriving Inhabited, BEq, Repr, Lean.ToJson, Lean.FromJson

structure Case where
  validationCase : Corpus.Case
  program : ImpureProgram
  externalNames : Array Name := #[]
  nativeOracle? : Option NativeOracleAttestation := none

def Case.artifact (directCase : Case) : Lcnf.Artifact := {
  entry := directCase.validationCase.entry
  program := directCase.program
  externalNames := directCase.externalNames
  forms := Lcnf.collectForms directCase.program }

@[noinline]
private def returnIdentity (_captured : Nat) : Nat → Nat :=
  fun value => value

private def nativeYieldApply : Nat :=
  returnIdentity 42 7

private def nativeClosureYieldApply : Nat :=
  let closure := returnIdentity
  closure 42 7

private structure NativeErasedOwner where
  proof : True

private structure NativePayloadOwner where
  payload : Nat

private structure NativeReplacement where
  payload : Nat
  marker : Nat

private structure NativeRepeatedReplacement where
  payload : Nat
  marker : Nat
  spare : Nat

private structure NativeHeapChild where
  first : Nat
  second : Nat

private structure NativeMixedOwner where
  proof : True
  child : NativeHeapChild
  marker : Nat

private structure NativeNestedChild where
  grandchild : NativeHeapChild
  marker : Nat

private structure NativeNestedOwner where
  proof : True
  child : NativeNestedChild
  marker : Nat

private structure NativeRepeatedOwner where
  proof : True
  first : NativeHeapChild
  second : NativeHeapChild
  marker : Nat

@[extern "lean_is_exclusive_obj"]
private opaque nativeIsExclusive {α : Type} (value : α) : Bool

@[noinline]
private def replaceErasedOwner (_owner : NativeErasedOwner) (payload : Nat) :
    NativePayloadOwner :=
  { payload }

@[noinline]
private def replaceMixedOwner (owner : NativeMixedOwner) (payload : Nat) :
    NativeReplacement :=
  { payload, marker := owner.marker }

@[noinline]
private def replaceNestedOwner (owner : NativeNestedOwner) (payload : Nat) :
    NativeReplacement :=
  { payload, marker := owner.marker }

@[noinline]
private def replaceRepeatedOwner (owner : NativeRepeatedOwner) (payload : Nat) :
    NativeRepeatedReplacement :=
  { payload, marker := owner.marker, spare := 0 }

@[noinline]
private def observeMixedReset (payload : Nat) (shared : Bool) : Nat :=
  if shared then payload + 1 else payload

@[noinline]
private def observeSharedMixedReset (payload : Nat) (childShared ownerShared : Bool) :
    Nat :=
  payload + (if childShared then 1 else 0) + (if ownerShared then 2 else 0)

private def nativeResetErasedField : Nat :=
  let erased : NativeErasedOwner := { proof := True.intro }
  (replaceErasedOwner erased 72).payload

@[noinline]
private def nativeResetErasedAndOwnedFields (first : Nat) : Nat :=
  let child : NativeHeapChild := { first, second := first + 1 }
  let owner : NativeMixedOwner := { proof := True.intro, child, marker := 0 }
  let replacement := replaceMixedOwner owner 73
  observeMixedReset replacement.payload (!nativeIsExclusive child)

@[noinline]
private def nativeSharedResetErasedAndOwnedFields (first : Nat) : Nat :=
  let child : NativeHeapChild := { first, second := first + 1 }
  let owner : NativeMixedOwner := { proof := True.intro, child, marker := 0 }
  let replacement := replaceMixedOwner owner 73
  observeSharedMixedReset replacement.payload
    (!nativeIsExclusive child) (!nativeIsExclusive owner)

private def nativePersistentMixedOwner : NativeMixedOwner :=
  { proof := True.intro
    child := { first := 41, second := 42 }
    marker := 0 }

@[noinline]
private def nativePersistentResetErasedAndOwnedFields (payload : Nat) : Nat :=
  let owner := nativePersistentMixedOwner
  let child := owner.child
  let replacement := replaceMixedOwner owner payload
  observeSharedMixedReset replacement.payload
    (!nativeIsExclusive child) (!nativeIsExclusive owner)

@[noinline]
private def nativeResetErasedAndNestedOwnedFields (first : Nat) : Nat :=
  let grandchild : NativeHeapChild := { first, second := first + 1 }
  let child : NativeNestedChild := { grandchild, marker := 0 }
  let owner : NativeNestedOwner := { proof := True.intro, child, marker := 0 }
  let replacement := replaceNestedOwner owner 73
  observeMixedReset replacement.payload (!nativeIsExclusive grandchild)

@[noinline]
private def nativeResetErasedAndSharedNestedOwnedFields (first : Nat) : Nat :=
  let grandchild : NativeHeapChild := { first, second := first + 1 }
  let child : NativeNestedChild := { grandchild, marker := 0 }
  let owner : NativeNestedOwner := { proof := True.intro, child, marker := 0 }
  let replacement := replaceNestedOwner owner 73
  observeSharedMixedReset replacement.payload
    (!nativeIsExclusive grandchild) (!nativeIsExclusive child)

@[noinline]
private def nativeResetErasedAndRepeatedOwnedFields (first : Nat) : Nat :=
  let child : NativeHeapChild := { first, second := first + 1 }
  let owner : NativeRepeatedOwner :=
    { proof := True.intro, first := child, second := child, marker := 0 }
  let replacement := replaceRepeatedOwner owner 73
  observeMixedReset replacement.payload (!nativeIsExclusive child)

private def identityDecl : LCNF.Decl .impure :=
  decl `directIdentity #[param z] (.code (.return z))

private def returnsIdentityCode : LCNF.Code .impure :=
  .let (letDecl c (.pap `directIdentity #[])) <|
  .return c

private def returnsIdentityDecl : LCNF.Decl .impure :=
  decl `returnsIdentity #[param x] (.code returnsIdentityCode)

private def yieldApplyMainCode : LCNF.Code .impure :=
  .let (letDecl x (.lit (.nat 42))) <|
  .let (letDecl y (.lit (.nat 7))) <|
  .let (letDecl r (.fap `returnsIdentity #[.fvar x, .fvar y])) <|
  .return r

private def yieldApplyProgram : ImpureProgram := {
  decls := #[
    identityDecl,
    returnsIdentityDecl,
    decl `directMain #[] (.code yieldApplyMainCode)
  ] }

private def yieldApplyFormTrace : Array String :=
  #["lit", "lit", "fap", "pap", "return", "return", "return"]

private def closureYieldApplyMainCode : LCNF.Code .impure :=
  .let (letDecl c (.pap `returnsIdentity #[])) <|
  .let (letDecl x (.lit (.nat 42))) <|
  .let (letDecl y (.lit (.nat 7))) <|
  .let (letDecl r (.fvar c #[.fvar x, .fvar y])) <|
  .return r

private def closureYieldApplyProgram : ImpureProgram := {
  decls := #[
    identityDecl,
    returnsIdentityDecl,
    decl `directClosureMain #[] (.code closureYieldApplyMainCode)
  ] }

private def closureYieldApplyFormTrace : Array String :=
  #["pap", "lit", "lit", "fvar", "pap", "return", "return", "return"]

private def erasedOwnerInfo : LCNF.CtorInfo :=
  { name := `NativeErasedOwner.mk, cidx := 0, size := 1, usize := 0, ssize := 0 }

private def payloadOwnerInfo : LCNF.CtorInfo :=
  { name := `NativePayloadOwner.mk, cidx := 0, size := 1, usize := 0, ssize := 0 }

private def heapChildInfo : LCNF.CtorInfo :=
  { name := `NativeHeapChild.mk, cidx := 0, size := 2, usize := 0, ssize := 0 }

private def replacementInfo : LCNF.CtorInfo :=
  { name := `NativeReplacement.mk, cidx := 0, size := 2, usize := 0, ssize := 0 }

private def repeatedReplacementInfo : LCNF.CtorInfo :=
  { name := `NativeRepeatedReplacement.mk, cidx := 0, size := 3, usize := 0, ssize := 0 }

private def mixedOwnerInfo : LCNF.CtorInfo :=
  { name := `NativeMixedOwner.mk, cidx := 0, size := 3, usize := 0, ssize := 0 }

private def nestedChildInfo : LCNF.CtorInfo :=
  { name := `NativeNestedChild.mk, cidx := 0, size := 2, usize := 0, ssize := 0 }

private def nestedOwnerInfo : LCNF.CtorInfo :=
  { name := `NativeNestedOwner.mk, cidx := 0, size := 3, usize := 0, ssize := 0 }

private def repeatedOwnerInfo : LCNF.CtorInfo :=
  { name := `NativeRepeatedOwner.mk, cidx := 0, size := 4, usize := 0, ssize := 0 }

private def falseInfo : LCNF.CtorInfo :=
  { name := ``Bool.false, cidx := 0, size := 0, usize := 0, ssize := 0 }

private def trueInfo : LCNF.CtorInfo :=
  { name := ``Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0 }

private def resetErasedFieldCode : LCNF.Code .impure :=
  .let (letDecl e .erased) <|
  .let (letDecl p (.ctor erasedOwnerInfo #[.fvar e])) <|
  .let (letDecl r (.reset 1 p)) <|
  .let (letDecl y (.lit (.nat 72))) <|
  .let (letDecl z (.reuse r payloadOwnerInfo true #[.fvar y])) <|
  .let (letDecl x (.oproj 0 z)) <|
  .return x

private def resetErasedFieldProgram : ImpureProgram := {
  decls := #[decl `directResetErasedField #[] (.code resetErasedFieldCode)] }

private def resetErasedFieldFormTrace : Array String :=
  #["erased", "ctor", "reset", "lit", "reuse", "oproj", "return"]

private def resetErasedAndOwnedFieldsCode : LCNF.Code .impure :=
  .let (letDecl x (.lit (.nat 41))) <|
  .let (letDecl y (.lit (.nat 42))) <|
  .let (letDecl q (.ctor heapChildInfo #[.fvar x, .fvar y])) <|
  .inc q 1 false false <|
  .let (letDecl e .erased) <|
  .let (letDecl x (.lit (.nat 0))) <|
  .let (letDecl p (.ctor mixedOwnerInfo #[.fvar e, .fvar q, .fvar x])) <|
  .let (letDecl r (.reset 3 p)) <|
  .let (letDecl y (.lit (.nat 73))) <|
  .let (letDecl z (.reuse r replacementInfo true #[.fvar y, .fvar x])) <|
  .let (letDecl x (.oproj 0 z)) <|
  .let (typedLetDecl s u8Type (.isShared q)) <|
  .cases (.mk ``Bool objType s #[
    .ctorAlt falseInfo (.return x),
    .ctorAlt trueInfo <|
      .let (letDecl y (.lit (.nat 74))) (.return y)])

private def resetErasedAndOwnedFieldsProgram : ImpureProgram := {
  decls := #[
    typedDecl `directResetErasedAndOwnedFields #[] objType
      (.code resetErasedAndOwnedFieldsCode)
  ] }

private def resetErasedAndOwnedFieldsFormTrace : Array String :=
  #["lit", "lit", "ctor", "inc", "erased", "lit", "ctor", "reset", "lit",
    "reuse", "oproj", "isShared", "cases", "return"]

private def sharedResetErasedAndOwnedFieldsCode : LCNF.Code .impure :=
  .let (letDecl x (.lit (.nat 41))) <|
  .let (letDecl y (.lit (.nat 42))) <|
  .let (letDecl q (.ctor heapChildInfo #[.fvar x, .fvar y])) <|
  .inc q 1 false false <|
  .let (letDecl e .erased) <|
  .let (letDecl x (.lit (.nat 0))) <|
  .let (letDecl p (.ctor mixedOwnerInfo #[.fvar e, .fvar q, .fvar x])) <|
  .inc p 1 false false <|
  .let (letDecl r (.reset 3 p)) <|
  .let (letDecl y (.lit (.nat 73))) <|
  .let (letDecl z (.reuse r replacementInfo true #[.fvar y, .fvar x])) <|
  .let (letDecl x (.oproj 0 z)) <|
  .let (typedLetDecl s u8Type (.isShared q)) <|
  .let (typedLetDecl t u8Type (.isShared p)) <|
  .cases (.mk ``Bool objType s #[
    .ctorAlt falseInfo <| .cases (.mk ``Bool objType t #[
      .ctorAlt falseInfo (.return x),
      .ctorAlt trueInfo <|
        .let (letDecl y (.lit (.nat 75))) (.return y)]),
    .ctorAlt trueInfo <| .cases (.mk ``Bool objType t #[
      .ctorAlt falseInfo <|
        .let (letDecl y (.lit (.nat 74))) (.return y),
      .ctorAlt trueInfo <|
        .let (letDecl y (.lit (.nat 76))) (.return y)])])

private def sharedResetErasedAndOwnedFieldsProgram : ImpureProgram := {
  decls := #[
    typedDecl `directSharedResetErasedAndOwnedFields #[] objType
      (.code sharedResetErasedAndOwnedFieldsCode)
  ] }

private def sharedResetErasedAndOwnedFieldsFormTrace : Array String :=
  #["lit", "lit", "ctor", "inc", "erased", "lit", "ctor", "inc", "reset",
    "lit", "reuse", "oproj", "isShared", "isShared", "cases", "cases", "lit",
    "return"]

private def persistentMixedOwnerCode : LCNF.Code .impure :=
  .let (letDecl x (.lit (.nat 41))) <|
  .let (letDecl y (.lit (.nat 42))) <|
  .let (letDecl q (.ctor heapChildInfo #[.fvar x, .fvar y])) <|
  .let (letDecl e .erased) <|
  .let (letDecl x (.lit (.nat 0))) <|
  .let (letDecl p (.ctor mixedOwnerInfo #[.fvar e, .fvar q, .fvar x])) <|
  .return p

private def persistentResetErasedAndOwnedFieldsCode : LCNF.Code .impure :=
  .let (letDecl p (.fap `directPersistentMixedOwner #[])) <|
  .let (letDecl q (.oproj 1 p)) <|
  .let (letDecl x (.oproj 2 p)) <|
  .let (letDecl r (.reset 3 p)) <|
  .let (letDecl y (.lit (.nat 73))) <|
  .let (letDecl z (.reuse r replacementInfo true #[.fvar y, .fvar x])) <|
  .let (letDecl x (.oproj 0 z)) <|
  .let (typedLetDecl s u8Type (.isShared q)) <|
  .let (typedLetDecl t u8Type (.isShared p)) <|
  .cases (.mk ``Bool objType s #[
    .ctorAlt falseInfo <| .cases (.mk ``Bool objType t #[
      .ctorAlt falseInfo (.return x),
      .ctorAlt trueInfo <|
        .let (letDecl y (.lit (.nat 75))) (.return y)]),
    .ctorAlt trueInfo <| .cases (.mk ``Bool objType t #[
      .ctorAlt falseInfo <|
        .let (letDecl y (.lit (.nat 74))) (.return y),
      .ctorAlt trueInfo <|
        .let (letDecl y (.lit (.nat 76))) (.return y)])])

private def persistentResetErasedAndOwnedFieldsProgram : ImpureProgram := {
  decls := #[
    typedDecl `directPersistentMixedOwner #[] objType (.code persistentMixedOwnerCode),
    typedDecl `directPersistentResetErasedAndOwnedFields #[] objType
      (.code persistentResetErasedAndOwnedFieldsCode)
  ] }

private def persistentResetErasedAndOwnedFieldsFormTrace : Array String :=
  #["fap", "lit", "lit", "ctor", "erased", "lit", "ctor", "return", "oproj",
    "oproj", "reset", "lit", "reuse", "oproj", "isShared", "isShared", "cases",
    "cases", "lit", "return"]

private def resetErasedAndNestedOwnedFieldsCode : LCNF.Code .impure :=
  .let (letDecl x (.lit (.nat 41))) <|
  .let (letDecl y (.lit (.nat 42))) <|
  .let (letDecl q (.ctor heapChildInfo #[.fvar x, .fvar y])) <|
  .inc q 1 false false <|
  .let (letDecl x (.lit (.nat 0))) <|
  .let (letDecl c (.ctor nestedChildInfo #[.fvar q, .fvar x])) <|
  .let (letDecl e .erased) <|
  .let (letDecl p (.ctor nestedOwnerInfo #[.fvar e, .fvar c, .fvar x])) <|
  .let (letDecl r (.reset 3 p)) <|
  .let (letDecl y (.lit (.nat 73))) <|
  .let (letDecl z (.reuse r replacementInfo true #[.fvar y, .fvar x])) <|
  .let (letDecl x (.oproj 0 z)) <|
  .let (typedLetDecl s u8Type (.isShared q)) <|
  .cases (.mk ``Bool objType s #[
    .ctorAlt falseInfo (.return x),
    .ctorAlt trueInfo <|
      .let (letDecl y (.lit (.nat 74))) (.return y)])

private def resetErasedAndNestedOwnedFieldsProgram : ImpureProgram := {
  decls := #[
    typedDecl `directResetErasedAndNestedOwnedFields #[] objType
      (.code resetErasedAndNestedOwnedFieldsCode)
  ] }

private def resetErasedAndNestedOwnedFieldsFormTrace : Array String :=
  #["lit", "lit", "ctor", "inc", "lit", "ctor", "erased", "ctor", "reset",
    "lit", "reuse", "oproj", "isShared", "cases", "return"]

private def resetErasedAndSharedNestedOwnedFieldsCode : LCNF.Code .impure :=
  .let (letDecl x (.lit (.nat 41))) <|
  .let (letDecl y (.lit (.nat 42))) <|
  .let (letDecl q (.ctor heapChildInfo #[.fvar x, .fvar y])) <|
  .inc q 1 false false <|
  .let (letDecl x (.lit (.nat 0))) <|
  .let (letDecl c (.ctor nestedChildInfo #[.fvar q, .fvar x])) <|
  .inc c 1 false false <|
  .let (letDecl e .erased) <|
  .let (letDecl p (.ctor nestedOwnerInfo #[.fvar e, .fvar c, .fvar x])) <|
  .let (letDecl r (.reset 3 p)) <|
  .let (letDecl y (.lit (.nat 73))) <|
  .let (letDecl z (.reuse r replacementInfo true #[.fvar y, .fvar x])) <|
  .let (letDecl x (.oproj 0 z)) <|
  .let (typedLetDecl s u8Type (.isShared q)) <|
  .let (typedLetDecl t u8Type (.isShared c)) <|
  .cases (.mk ``Bool objType s #[
    .ctorAlt falseInfo <| .cases (.mk ``Bool objType t #[
      .ctorAlt falseInfo (.return x),
      .ctorAlt trueInfo <|
        .let (letDecl y (.lit (.nat 75))) (.return y)]),
    .ctorAlt trueInfo <| .cases (.mk ``Bool objType t #[
      .ctorAlt falseInfo <|
        .let (letDecl y (.lit (.nat 74))) (.return y),
      .ctorAlt trueInfo <|
        .let (letDecl y (.lit (.nat 76))) (.return y)])])

private def resetErasedAndSharedNestedOwnedFieldsProgram : ImpureProgram := {
  decls := #[
    typedDecl `directResetErasedAndSharedNestedOwnedFields #[] objType
      (.code resetErasedAndSharedNestedOwnedFieldsCode)
  ] }

private def resetErasedAndSharedNestedOwnedFieldsFormTrace : Array String :=
  #["lit", "lit", "ctor", "inc", "lit", "ctor", "inc", "erased", "ctor",
    "reset", "lit", "reuse", "oproj", "isShared", "isShared", "cases", "cases",
    "lit", "return"]

private def resetErasedAndRepeatedOwnedFieldsCode : LCNF.Code .impure :=
  .let (letDecl x (.lit (.nat 41))) <|
  .let (letDecl y (.lit (.nat 42))) <|
  .let (letDecl q (.ctor heapChildInfo #[.fvar x, .fvar y])) <|
  .inc q 2 false false <|
  .let (letDecl e .erased) <|
  .let (letDecl x (.lit (.nat 0))) <|
  .let (letDecl p (.ctor repeatedOwnerInfo #[.fvar e, .fvar q, .fvar q, .fvar x])) <|
  .let (letDecl r (.reset 4 p)) <|
  .let (letDecl y (.lit (.nat 73))) <|
  .let (letDecl z (.reuse r repeatedReplacementInfo true #[.fvar y, .fvar x, .fvar x])) <|
  .let (letDecl x (.oproj 0 z)) <|
  .let (typedLetDecl s u8Type (.isShared q)) <|
  .cases (.mk ``Bool objType s #[
    .ctorAlt falseInfo (.return x),
    .ctorAlt trueInfo <|
      .let (letDecl y (.lit (.nat 74))) (.return y)])

private def resetErasedAndRepeatedOwnedFieldsProgram : ImpureProgram := {
  decls := #[
    typedDecl `directResetErasedAndRepeatedOwnedFields #[] objType
      (.code resetErasedAndRepeatedOwnedFieldsCode)
  ] }

private def resetErasedAndRepeatedOwnedFieldsFormTrace : Array String :=
  #["lit", "lit", "ctor", "inc", "erased", "lit", "ctor", "reset", "lit",
    "reuse", "oproj", "isShared", "cases", "return"]

def cases : Array Case := #[
  { validationCase := {
      id := "machine-yield-apply"
      entry := `directMain
      resultSchema := .nat
      native := fun _ => .nat nativeYieldApply
      tags := #["direct-lcnf", "machine", "overapplication"]
      requiredLcnfForms := #["fap", "lit", "pap", "return"]
      requiredExecutedLcnfForms := #["fap", "lit", "pap", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "fap", minimum := 1, maximum := some 1 },
        { form := "lit", minimum := 2, maximum := some 2 },
        { form := "pap", minimum := 1, maximum := some 1 },
        { form := "return", minimum := 3, maximum := some 3 }
      ]
      requiredExecutedLcnfFormTrace := some yieldApplyFormTrace
      requiredAdministrativeStepKinds := #["admin:yield-apply"]
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note := "Exercise the interpreter apply frame against native curried application"
      }
    }
    program := yieldApplyProgram },
  { validationCase := {
      id := "machine-closure-yield-apply"
      entry := `directClosureMain
      resultSchema := .nat
      native := fun _ => .nat nativeClosureYieldApply
      tags := #["direct-lcnf", "machine", "overapplication", "function-value"]
      requiredLcnfForms := #["fvar", "lit", "pap", "return"]
      requiredExecutedLcnfForms := #["fvar", "lit", "pap", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "fvar", minimum := 1, maximum := some 1 },
        { form := "lit", minimum := 2, maximum := some 2 },
        { form := "pap", minimum := 2, maximum := some 2 },
        { form := "return", minimum := 3, maximum := some 3 }
      ]
      requiredExecutedLcnfFormTrace := some closureYieldApplyFormTrace
      requiredAdministrativeStepKinds := #["admin:invoke-value", "admin:yield-apply"]
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note := "Enter the interpreter apply frame through a closure value and compare with native"
      }
    }
    program := closureYieldApplyProgram },
  { validationCase := {
      id := "machine-reset-erased-field"
      entry := `directResetErasedField
      resultSchema := .nat
      native := fun _ => .nat nativeResetErasedField
      tags :=
        #["direct-lcnf", "machine", "ownership", "constructor", "reset", "reuse",
          "erased", "boundary"]
      requiredLcnfForms :=
        #["erased", "ctor", "reset", "lit", "reuse", "oproj", "return"]
      requiredExecutedLcnfForms :=
        #["erased", "ctor", "reset", "lit", "reuse", "oproj", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "erased", minimum := 1, maximum := some 1 },
        { form := "ctor", minimum := 1, maximum := some 1 },
        { form := "reset", minimum := 1, maximum := some 1 },
        { form := "lit", minimum := 1, maximum := some 1 },
        { form := "reuse", minimum := 1, maximum := some 1 },
        { form := "oproj", minimum := 1, maximum := some 1 },
        { form := "return", minimum := 1, maximum := some 1 }
      ]
      requiredExecutedLcnfFormTrace := some resetErasedFieldFormTrace
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note :=
          "Reset an erased ownership slot, reuse its storage, and compare with native replacement"
      }
    }
    program := resetErasedFieldProgram },
  { validationCase := {
      id := "machine-reset-erased-and-owned-fields"
      entry := `directResetErasedAndOwnedFields
      resultSchema := .nat
      native := fun _ => .nat (nativeResetErasedAndOwnedFields 41)
      tags :=
        #["direct-lcnf", "machine", "ownership", "constructor", "reset", "reuse",
          "erased", "isShared", "reference-count", "boundary"]
      requiredLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "lit", minimum := 4, maximum := some 4 },
        { form := "ctor", minimum := 2, maximum := some 2 },
        { form := "inc", minimum := 1, maximum := some 1 },
        { form := "erased", minimum := 1, maximum := some 1 },
        { form := "reset", minimum := 1, maximum := some 1 },
        { form := "reuse", minimum := 1, maximum := some 1 },
        { form := "oproj", minimum := 1, maximum := some 1 },
        { form := "isShared", minimum := 1, maximum := some 1 },
        { form := "cases", minimum := 1, maximum := some 1 },
        { form := "return", minimum := 1, maximum := some 1 }
      ]
      requiredExecutedLcnfFormTrace := some resetErasedAndOwnedFieldsFormTrace
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note :=
          "Reset mixed erased/owned fields and expose the owned child's release through isShared"
      }
    }
    program := resetErasedAndOwnedFieldsProgram },
  { validationCase := {
      id := "machine-shared-reset-erased-and-owned-fields"
      entry := `directSharedResetErasedAndOwnedFields
      resultSchema := .nat
      native := fun _ => .nat (nativeSharedResetErasedAndOwnedFields 41)
      tags :=
        #["direct-lcnf", "machine", "ownership", "constructor", "reset", "reuse",
          "erased", "isShared", "reference-count", "shared", "slow-path",
          "boundary"]
      requiredLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "lit", minimum := 5, maximum := some 5 },
        { form := "ctor", minimum := 2, maximum := some 2 },
        { form := "inc", minimum := 2, maximum := some 2 },
        { form := "erased", minimum := 1, maximum := some 1 },
        { form := "reset", minimum := 1, maximum := some 1 },
        { form := "reuse", minimum := 1, maximum := some 1 },
        { form := "oproj", minimum := 1, maximum := some 1 },
        { form := "isShared", minimum := 2, maximum := some 2 },
        { form := "cases", minimum := 2, maximum := some 2 },
        { form := "return", minimum := 1, maximum := some 1 }
      ]
      requiredExecutedLcnfFormTrace := some sharedResetErasedAndOwnedFieldsFormTrace
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note :=
          "Keep a mixed owner shared across reset and observe owner decrement without child release"
      }
    }
    program := sharedResetErasedAndOwnedFieldsProgram
    nativeOracle? := some {
      entry := ``nativeSharedResetErasedAndOwnedFields
      dependencies := #[``replaceMixedOwner]
      claim :=
        "shared owner reset decrements only the owner and allocates the replacement"
      requiredOwnershipFacts :=
        #["inc:owner:amount=1:persistent=false:reference=true",
          "isShared:owner", "dec:owner:reference=false",
          "ctor:NativeReplacement.mk", "oset:index=0"]
      expectedArtifactSha256 :=
        "4e45f9af8557f2f90ce7ff564fc0fdd2d6eea4faa3d29f85ce0d9b708f9064b5"
    } },
  { validationCase := {
      id := "machine-persistent-reset-erased-and-owned-fields"
      entry := `directPersistentResetErasedAndOwnedFields
      resultSchema := .nat
      native := fun _ => .nat (nativePersistentResetErasedAndOwnedFields 73)
      tags :=
        #["direct-lcnf", "machine", "ownership", "constructor", "reset", "reuse",
          "erased", "isShared", "reference-count", "persistent", "cache", "slow-path",
          "boundary"]
      requiredLcnfForms :=
        #["fap", "lit", "ctor", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfForms :=
        #["fap", "lit", "ctor", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "fap", minimum := 1, maximum := some 1 },
        { form := "lit", minimum := 5, maximum := some 5 },
        { form := "ctor", minimum := 2, maximum := some 2 },
        { form := "erased", minimum := 1, maximum := some 1 },
        { form := "reset", minimum := 1, maximum := some 1 },
        { form := "reuse", minimum := 1, maximum := some 1 },
        { form := "oproj", minimum := 3, maximum := some 3 },
        { form := "isShared", minimum := 2, maximum := some 2 },
        { form := "cases", minimum := 2, maximum := some 2 },
        { form := "return", minimum := 2, maximum := some 2 }
      ]
      requiredExecutedLcnfFormTrace := some persistentResetErasedAndOwnedFieldsFormTrace
      requiredAdministrativeStepKinds :=
        #["admin:yield-bind", "admin:yield-cache"]
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note :=
          "Reset a cached persistent mixed owner and preserve both owner and child reachability"
      }
    }
    program := persistentResetErasedAndOwnedFieldsProgram
    nativeOracle? := some {
      entry := ``nativePersistentResetErasedAndOwnedFields
      dependencies := #[``nativePersistentMixedOwner, ``replaceMixedOwner]
      claim :=
        "cached persistent owner stays shared while reset allocates a replacement and preserves its child"
      requiredOwnershipFacts :=
        #["inc:owner:amount=1:persistent=true:reference=true",
          "isShared:owner", "dec:owner:reference=false",
          "ctor:NativeMixedOwner.mk", "ctor:NativeHeapChild.mk",
          "ctor:NativeReplacement.mk",
          "declaration:nativePersistentMixedOwner._closed_1",
          "declaration:nativePersistentMixedOwner._closed_0"]
      expectedArtifactSha256 :=
        "81560717dd22a90fc4b40e2d41f5a1cad8ed8c08f8824a9ccec37d82b6ee96d7"
    } },
  { validationCase := {
      id := "machine-reset-erased-and-nested-owned-fields"
      entry := `directResetErasedAndNestedOwnedFields
      resultSchema := .nat
      native := fun _ => .nat (nativeResetErasedAndNestedOwnedFields 41)
      tags :=
        #["direct-lcnf", "machine", "ownership", "constructor", "reset", "reuse",
          "erased", "isShared", "reference-count", "recursive-release", "nested",
          "boundary"]
      requiredLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "lit", minimum := 4, maximum := some 4 },
        { form := "ctor", minimum := 3, maximum := some 3 },
        { form := "inc", minimum := 1, maximum := some 1 },
        { form := "erased", minimum := 1, maximum := some 1 },
        { form := "reset", minimum := 1, maximum := some 1 },
        { form := "reuse", minimum := 1, maximum := some 1 },
        { form := "oproj", minimum := 1, maximum := some 1 },
        { form := "isShared", minimum := 1, maximum := some 1 },
        { form := "cases", minimum := 1, maximum := some 1 },
        { form := "return", minimum := 1, maximum := some 1 }
      ]
      requiredExecutedLcnfFormTrace := some resetErasedAndNestedOwnedFieldsFormTrace
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note :=
          "Reset a unique nested owner and observe recursive release making its grandchild exclusive"
      }
    }
    program := resetErasedAndNestedOwnedFieldsProgram },
  { validationCase := {
      id := "machine-reset-erased-and-shared-nested-owned-fields"
      entry := `directResetErasedAndSharedNestedOwnedFields
      resultSchema := .nat
      native := fun _ => .nat (nativeResetErasedAndSharedNestedOwnedFields 41)
      tags :=
        #["direct-lcnf", "machine", "ownership", "constructor", "reset", "reuse",
          "erased", "isShared", "reference-count", "recursive-release", "nested",
          "shared", "stop-recursion", "boundary"]
      requiredLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "lit", minimum := 5, maximum := some 5 },
        { form := "ctor", minimum := 3, maximum := some 3 },
        { form := "inc", minimum := 2, maximum := some 2 },
        { form := "erased", minimum := 1, maximum := some 1 },
        { form := "reset", minimum := 1, maximum := some 1 },
        { form := "reuse", minimum := 1, maximum := some 1 },
        { form := "oproj", minimum := 1, maximum := some 1 },
        { form := "isShared", minimum := 2, maximum := some 2 },
        { form := "cases", minimum := 2, maximum := some 2 },
        { form := "return", minimum := 1, maximum := some 1 }
      ]
      requiredExecutedLcnfFormTrace :=
        some resetErasedAndSharedNestedOwnedFieldsFormTrace
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note :=
          "Stop recursive reset release at a shared child while preserving its grandchild alias"
      }
    }
    program := resetErasedAndSharedNestedOwnedFieldsProgram
    nativeOracle? := some {
      entry := ``nativeResetErasedAndSharedNestedOwnedFields
      dependencies := #[``replaceNestedOwner]
      claim :=
        "unique owner reset decrements a shared child without recursively releasing its grandchild"
      requiredOwnershipFacts :=
        #["inc:grandchild:amount=1:persistent=false:reference=true",
          "inc:child:amount=1:persistent=false:reference=true",
          "isShared:owner", "project-dec:owner:index=0", "oset:index=0"]
      expectedArtifactSha256 :=
        "97aee3e462f7ba25269a1a449d56f478d215b0681af63c1f980e5518016f7ab3"
    } },
  { validationCase := {
      id := "machine-reset-erased-and-repeated-owned-fields"
      entry := `directResetErasedAndRepeatedOwnedFields
      resultSchema := .nat
      native := fun _ => .nat (nativeResetErasedAndRepeatedOwnedFields 41)
      tags :=
        #["direct-lcnf", "machine", "ownership", "constructor", "reset", "reuse",
          "erased", "isShared", "reference-count", "repeated-alias", "multiplicity",
          "boundary"]
      requiredLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfForms :=
        #["lit", "ctor", "inc", "erased", "reset", "reuse", "oproj", "isShared",
          "cases", "return"]
      requiredExecutedLcnfFormCounts := #[
        { form := "lit", minimum := 4, maximum := some 4 },
        { form := "ctor", minimum := 2, maximum := some 2 },
        { form := "inc", minimum := 1, maximum := some 1 },
        { form := "erased", minimum := 1, maximum := some 1 },
        { form := "reset", minimum := 1, maximum := some 1 },
        { form := "reuse", minimum := 1, maximum := some 1 },
        { form := "oproj", minimum := 1, maximum := some 1 },
        { form := "isShared", minimum := 1, maximum := some 1 },
        { form := "cases", minimum := 1, maximum := some 1 },
        { form := "return", minimum := 1, maximum := some 1 }
      ]
      requiredExecutedLcnfFormTrace := some resetErasedAndRepeatedOwnedFieldsFormTrace
      provenance := {
        suite := "fir-direct-lcnf"
        path := "Fir/Validation/DirectLCNF.lean"
        note :=
          "Release two ownership slots that alias the same child and observe exact decrement multiplicity"
      }
    }
    program := resetErasedAndRepeatedOwnedFieldsProgram
    nativeOracle? := some {
      entry := ``nativeResetErasedAndRepeatedOwnedFields
      dependencies := #[``replaceRepeatedOwner]
      claim :=
        "unique owner reset releases both aliased child slots before reusing its storage"
      requiredOwnershipFacts :=
        #["inc:child:amount=2:persistent=false:reference=true",
          "project-dec:owner:index=1", "project-dec:owner:index=0",
          "oset:index=2", "oset:index=1", "oset:index=0",
          "ctor:NativeRepeatedReplacement.mk"]
      expectedArtifactSha256 :=
        "34469861bd43393e0c221989ea0f71a3a58431d8c92cb82144f48843dc83f721"
    } }
]

#guard cases.size == 9

#guard cases.all fun directCase =>
  directCase.validationCase.requiredExecutedLcnfFormTrace.isSome

def findCase? (id : String) : Option Case :=
  cases.find? (·.validationCase.id == id)

def descriptors : Array Corpus.CaseDescriptor :=
  cases.map (·.validationCase.descriptor)

def nativeOracleDescriptors : Array NativeOracleDescriptor :=
  cases.filterMap fun directCase =>
    directCase.nativeOracle?.map fun attestation => {
      caseId := directCase.validationCase.id
      entry := toString attestation.entry
      dependencies := attestation.dependencies.map toString
      claim := attestation.claim
      requiredArtifactFragments := attestation.requiredArtifactFragments
      requiredOwnershipFacts := attestation.requiredOwnershipFacts
      expectedArtifactSha256 := attestation.expectedArtifactSha256
    }

#guard nativeOracleDescriptors.size == 4

private def failure (backend caseId message : String) : BackendResult := {
  caseId
  backend
  outcome := .failure message }

def runNativeCase (directCase : Case) : IO BackendResult := do
  let validationCase := directCase.validationCase
  validationCase.nativeBefore
  let value := validationCase.native ()
  let effects ← validationCase.nativeEffects value
  if !validationCase.resultSchema.accepts value then
    return failure nativeBackend validationCase.id
      "native result did not match the case result schema"
  return {
    caseId := validationCase.id
    backend := nativeBackend
    outcome := .success {
      termination := .returned value
      effects
    }
  }

def runLcnfCase (directCase : Case) : IO BackendResult :=
  return {
    Lcnf.execute directCase.validationCase directCase.artifact with
    backend := lcnfBackend
  }

def usage (backend : String) : String :=
  s!"usage: fir-{backend} --case ID\n" ++
    s!"       fir-{backend} --list [--tag TAG]\n" ++
    s!"       fir-{backend} --manifest\n" ++
    s!"       fir-{backend} --native-oracle-manifest"

def main (backend : String) (runCase : Case → IO BackendResult)
    (args : List String) : IO UInt32 := do
  match args with
  | ["--case", caseId] =>
      let some directCase := findCase? caseId
        | Jsonl.emit (failure backend caseId s!"unknown direct LCNF case: {caseId}")
          return 2
      Jsonl.emit (← runCase directCase)
      return 0
  | ["--list"] =>
      for directCase in cases do
        IO.println directCase.validationCase.id
      return 0
  | ["--list", "--tag", tag] =>
      for directCase in cases do
        if directCase.validationCase.tags.contains tag then
          IO.println directCase.validationCase.id
      return 0
  | ["--manifest"] =>
      for descriptor in descriptors do
        Jsonl.emit descriptor
      return 0
  | ["--native-oracle-manifest"] =>
      for descriptor in nativeOracleDescriptors do
        Jsonl.emit descriptor
      return 0
  | _ =>
      IO.eprintln (usage backend)
      return 2

end Fir.Validation.DirectLcnf
