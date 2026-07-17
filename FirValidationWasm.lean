import Fir.Validation.Corpus
import Fir.Wasm.Emit.Source
import Lean.Elab.Command

open Lean Elab Command
open Fir.Validation

namespace FirValidationWasm

def caseIds : Array String :=
  #["uint8-max", "uint16-max", "uint32-max", "uint64-max", "usize-max"]

syntax (name := firValidationWasm) "#fir_validation_wasm" : command

@[command_elab firValidationWasm]
def elabFirValidationWasm : CommandElab := fun _ => do
  let outputDirectory :=
    (← liftIO <| IO.getEnv "FIR_VALIDATION_OUT_DIR").getD
      "_build/validation-v8/v8"
  let moduleDirectory : System.FilePath :=
    (outputDirectory : System.FilePath) / "modules"
  liftIO <| IO.FS.createDirAll moduleDirectory
  for caseId in caseIds do
    let some validationCase := Corpus.findCase? caseId
      | throwError "unknown validation case: {caseId}"
    let result ← liftCoreM <|
      Fir.Wasm.Emit.Source.compileClosed
        validationCase.entry validationCase.dependencies
    let artifact ←
      match result with
      | .ok artifact => pure artifact
      | .error error =>
          throwError "Wasm compilation failed for {caseId}: {repr error}"
    unless artifact.module.imports.isEmpty do
      throwError "{caseId} unexpectedly requires Wasm imports"
    unless artifact.module.exports == #[validationCase.entry] do
      throwError "Wasm module does not export {validationCase.entry}"
    let modulePath := moduleDirectory / s!"{caseId}.wasm"
    liftIO <| IO.FS.writeBinFile modulePath artifact.bytes
    liftIO <| IO.FS.writeFile (modulePath.toString ++ ".json")
      artifact.manifest.compress

end FirValidationWasm

#fir_validation_wasm
