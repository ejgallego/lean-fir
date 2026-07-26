import Fir.Validation.DirectLCNF
import Lean.Elab.Command

open Lean Elab Command
open Fir.Validation

private def outputRoot : IO System.FilePath := do
  let some path ← IO.getEnv "FIR_DIRECT_NATIVE_IR_OUT_DIR"
    | return "_build" / "validation-direct-native-ir"
  return System.FilePath.mk path

syntax (name := firValidationDirectNativeIr)
  "#fir_validation_direct_native_ir" : command

@[command_elab firValidationDirectNativeIr]
def elabFirValidationDirectNativeIr : CommandElab := fun _ => do
  liftCoreM Fir.LeanIR.installSimpCaseCapture
  let root ← liftIO outputRoot
  for directCase in DirectLcnf.cases do
    match directCase.nativeOracle? with
    | none => pure ()
    | some attestation => do
        let artifact ← liftCoreM <|
          Lcnf.compileEntry attestation.entry attestation.dependencies
        let formatted ← liftCoreM artifact.format
        let artifactDir := root / directCase.validationCase.id
        liftIO <| IO.FS.createDirAll artifactDir
        liftIO <| IO.FS.writeFile (artifactDir / "program.lcnf")
          (formatted ++ "\n")
        liftIO <| IO.FS.writeFile (artifactDir / "declarations.txt")
          (String.intercalate "\n"
            (artifact.program.decls.toList.map (toString ·.name)) ++ "\n")
        liftIO <| IO.FS.writeFile (artifactDir / "forms.txt")
          (String.intercalate "\n" artifact.forms.toList ++ "\n")
        liftIO <| IO.FS.writeFile (artifactDir / "entry.txt")
          (toString attestation.entry ++ "\n")

#fir_validation_direct_native_ir
