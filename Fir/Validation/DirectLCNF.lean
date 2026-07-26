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
structure Case where
  validationCase : Corpus.Case
  program : ImpureProgram
  externalNames : Array Name := #[]

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

private structure NativeHeapChild where
  first : Nat
  second : Nat

private structure NativeMixedOwner where
  proof : True
  child : NativeHeapChild
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
private def observeMixedReset (payload : Nat) (shared : Bool) : Nat :=
  if shared then payload + 1 else payload

private def nativeResetErasedField : Nat :=
  let erased : NativeErasedOwner := { proof := True.intro }
  (replaceErasedOwner erased 72).payload

@[noinline]
private def nativeResetErasedAndOwnedFields (first : Nat) : Nat :=
  let child : NativeHeapChild := { first, second := first + 1 }
  let owner : NativeMixedOwner := { proof := True.intro, child, marker := 0 }
  let replacement := replaceMixedOwner owner 73
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

private def mixedOwnerInfo : LCNF.CtorInfo :=
  { name := `NativeMixedOwner.mk, cidx := 0, size := 3, usize := 0, ssize := 0 }

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
    program := resetErasedAndOwnedFieldsProgram }
]

#guard cases.size == 4

#guard cases.all fun directCase =>
  directCase.validationCase.requiredExecutedLcnfFormTrace.isSome

def findCase? (id : String) : Option Case :=
  cases.find? (·.validationCase.id == id)

def descriptors : Array Corpus.CaseDescriptor :=
  cases.map (·.validationCase.descriptor)

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
    s!"       fir-{backend} --manifest"

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
  | _ =>
      IO.eprintln (usage backend)
      return 2

end Fir.Validation.DirectLcnf
