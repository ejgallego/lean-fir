import Fir.Validation.LCNF
import Lean.Elab.Command

open Lean Elab Command
open Fir.Validation

syntax (name := firValidationLcnf) "#fir_validation_lcnf" : command

@[command_elab firValidationLcnf]
def elabFirValidationLcnf : CommandElab := fun _ => do
  liftCoreM Fir.LeanIR.installSimpCaseCapture
  for validationCase in Corpus.cases do
    let (result, artifact) ← liftCoreM <| Lcnf.runCase validationCase
    let formatted ← liftCoreM artifact.format
    let artifactDir : System.FilePath :=
      "_build" / "validation" / validationCase.id / "lcnf"
    liftIO <| IO.FS.createDirAll artifactDir
    liftIO <| IO.FS.writeFile (artifactDir / "program.lcnf") (formatted ++ "\n")
    liftIO <| IO.FS.writeFile (artifactDir / "declarations.txt")
      (String.intercalate "\n" (artifact.program.decls.toList.map (toString ·.name)) ++ "\n")
    liftIO <| IO.FS.writeFile (artifactDir / "forms.txt")
      (String.intercalate "\n" artifact.forms.toList ++ "\n")
    liftIO <| Jsonl.emit result

#fir_validation_lcnf
