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
private def r : FVarId := ⟨`r⟩

private def objType : Expr :=
  LCNF.ImpureType.object

private def param (fvarId : FVarId) : LCNF.Param .impure :=
  { fvarId, binderName := fvarId.name, type := objType, borrow := false }

private def decl (name : Name) (params : Array (LCNF.Param .impure))
    (value : LCNF.DeclValue .impure) : LCNF.Decl .impure :=
  { name
    levelParams := []
    type := objType
    params
    value
    safe := true
    recursive := false
    inlineAttr? := none }

private def letDecl (fvarId : FVarId) (value : LCNF.LetValue .impure) :
    LCNF.LetDecl .impure :=
  { fvarId, binderName := fvarId.name, type := objType, value }

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
    program := yieldApplyProgram }
]

#guard cases.all fun directCase =>
  directCase.validationCase.requiredAdministrativeStepKinds.contains
    "admin:yield-apply"

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
