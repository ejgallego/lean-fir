import Fir.Validation.Corpus
import Fir.Validation.LCNF
import Fir.Wasm.Emit.Source
import Lean.Elab.Command

open Lean Elab Command
open Fir.Validation

namespace FirValidationWasm

def caseIds : Array String :=
  #["boxed-uint32", "packed-project-usize",
    "direct-call", "captured-partial", "capture-17-list",
    "recursive-empty", "recursive-traversal", "nat-add-small",
    "uint8-max", "uint16-max", "uint32-max", "uint64-max", "usize-max",
    "uint8-roundtrip", "uint16-roundtrip", "uint32-roundtrip", "uint64-roundtrip",
    "usize-roundtrip", "nat-list-nonempty", "nat-list-nonempty-bool",
    "nat-list-empty-bool", "unicode-string-roundtrip",
    "int-positive-roundtrip", "int-negative-roundtrip",
    "int-immediate-max", "int-immediate-min",
    "int-heap-positive-boundary", "int-heap-negative-boundary",
    "byte-array-roundtrip", "byte-array-size",
    "byte-array-get-zero", "byte-array-get-high-bit", "byte-array-get-max",
    "byte-array-set-unique", "byte-array-set-shared",
    "int-literal-immediate-positive", "int-literal-heap-positive",
    "int-literal-immediate-negative", "int-literal-heap-negative"]

def productJson (kind path : String) : Json :=
  Json.mkObj [("kind", kind), ("path", path)]

def buildInputJson (kind name : String) (path : System.FilePath) : Json :=
  Json.mkObj [
    ("kind", kind),
    ("name", name),
    ("path", path.toString)]

def parseSelectedCaseIds (raw : String) : Except String (Array String) := do
  let .arr values ← Json.parse raw
    | throw "FIR_VALIDATION_CASES must be a JSON array"
  let selected ← values.mapM fun
    | .str caseId => pure caseId
    | _ => throw "FIR_VALIDATION_CASES must contain only strings"
  if selected.isEmpty then
    throw "FIR_VALIDATION_CASES must be nonempty"
  if selected.toList.eraseDups.length != selected.size then
    throw "FIR_VALIDATION_CASES contains duplicate cases"
  return selected

def selectedCaseIds : IO (Array String) := do
  let some raw ← IO.getEnv "FIR_VALIDATION_CASES"
    | return caseIds
  IO.ofExcept (parseSelectedCaseIds raw)

syntax (name := firValidationWasm) "#fir_validation_wasm" : command

@[command_elab firValidationWasm]
def elabFirValidationWasm : CommandElab := fun _ => do
  let env ← getEnv
  let selected ← liftIO selectedCaseIds
  let outputDirectory :=
    (← liftIO <| IO.getEnv "FIR_VALIDATION_OUT_DIR").getD
      "_build/validation-v8/v8"
  let moduleDirectory : System.FilePath :=
    (outputDirectory : System.FilePath) / "modules"
  liftIO <| IO.FS.createDirAll moduleDirectory
  for caseId in selected do
    let some validationCase := Corpus.findCase? caseId
      | throwError "unknown validation case: {caseId}"
    let result ← liftCoreM <|
      Fir.Wasm.Emit.Source.compileValidationInvocation validationCase.id validationCase.entry
        validationCase.argSchemas validationCase.args validationCase.resultSchema
        validationCase.dependencies
    let artifact ←
      match result with
      | .ok artifact => pure artifact
      | .error error =>
          throwError "Wasm compilation failed for {caseId}: {repr error}"
    unless artifact.module.exports == #[validationCase.entry] do
      throwError "Wasm module does not export {validationCase.entry}"
    let modulePath := moduleDirectory / s!"{caseId}.wasm"
    liftIO <| IO.FS.writeBinFile modulePath artifact.bytes
    liftIO <| IO.FS.writeFile (modulePath.toString ++ ".json")
      artifact.manifest.compress
  let manifestProducts :=
    selected.map (fun caseId =>
      productJson "wasm-manifest" s!"modules/{caseId}.wasm.json") ++
    selected.map (fun caseId =>
      productJson "wasm-module" s!"modules/{caseId}.wasm")
  let leanInput ← liftIO do
    return buildInputJson "lean-compiler" "bin/lean" (← IO.appPath)
  let oleanInputs ← env.header.moduleNames.mapM fun moduleName => do
    let path ← liftIO <| findOLean moduleName
    let name := moduleName.toString.replace "." "/" ++ ".olean"
    return buildInputJson "lean-olean" name path
  let buildInputManifest := Json.mkObj [
    ("version", Json.num 1),
    ("scope", "reported-loaded"),
    ("inputs", Json.arr <| #[leanInput] ++ oleanInputs)]
  liftIO <| IO.FS.writeFile
    ((outputDirectory : System.FilePath) / "build-inputs.json")
    buildInputManifest.compress
  let productManifest := Json.mkObj [
    ("version", Json.num 1),
    ("products", Json.arr manifestProducts)]
  liftIO <| IO.FS.writeFile
    ((outputDirectory : System.FilePath) / "products.json")
    productManifest.compress

end FirValidationWasm

#fir_validation_wasm
