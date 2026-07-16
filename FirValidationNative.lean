import Fir.Validation.Corpus

open Fir.Validation

namespace FirValidationNative

def usage : String :=
  "usage: fir-validation-native --case ID\n" ++
    "       fir-validation-native --list [--tag TAG]\n" ++
    "       fir-validation-native --manifest"

def emitFailure (caseId message : String) : IO Unit :=
  Jsonl.emit ({
    caseId
    backend := "native"
    outcome := .failure message
  } : BackendResult)

def runCase (caseId : String) : IO UInt32 := do
  let some validationCase := Corpus.findCase? caseId
    | emitFailure caseId s!"unknown validation case: {caseId}"
      return 2
  validationCase.nativeBefore
  let value := validationCase.native ()
  let effects ← validationCase.nativeEffects value
  if !validationCase.resultSchema.accepts value then
    emitFailure caseId "native result did not match the case result schema"
    return 1
  let observation : ValidationObservation := {
    termination := .returned value
    effects
  }
  Jsonl.emit ({
    caseId
    backend := "native"
    outcome := .success observation
  } : BackendResult)
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--case", caseId] => runCase caseId
  | ["--list"] =>
      for caseId in Corpus.caseIds do
        IO.println caseId
      return 0
  | ["--list", "--tag", tag] =>
      for validationCase in Corpus.cases do
        if validationCase.tags.contains tag then
          IO.println validationCase.id
      return 0
  | ["--manifest"] =>
      for descriptor in Corpus.descriptors do
        Jsonl.emit descriptor
      return 0
  | _ =>
      IO.eprintln usage
      return 2

end FirValidationNative

def main (args : List String) : IO UInt32 :=
  FirValidationNative.main args
