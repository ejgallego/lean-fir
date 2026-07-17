import Fir.Validation.Corpus
import Fir.Wasm.Emit.Source
import Lean.Elab.Command

open Lean Elab Command
open Fir.Validation

namespace FirValidationWasm

def caseIds : Array String :=
  #["uint8-max", "uint16-max", "uint32-max", "uint64-max", "usize-max"]

def productJson (kind path : String) : Json :=
  Json.mkObj [("kind", kind), ("path", path)]

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
  let manifestProducts :=
    caseIds.map (fun caseId =>
      productJson "wasm-manifest" s!"modules/{caseId}.wasm.json") ++
    caseIds.map (fun caseId =>
      productJson "wasm-module" s!"modules/{caseId}.wasm")
  let productManifest := Json.mkObj [
    ("version", Json.num 1),
    ("products", Json.arr manifestProducts)]
  liftIO <| IO.FS.writeFile
    ((outputDirectory : System.FilePath) / "products.json")
    productManifest.compress

end FirValidationWasm

#fir_validation_wasm
