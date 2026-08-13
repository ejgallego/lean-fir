import Fir.Validation.Corpus
import Fir.Validation.LCNF
import Fir.Wasm.Emit.Source
import Lean.Elab.Command

open Lean Elab Command
open Fir.Validation

namespace FirValidationWasm

def caseIds : Array String :=
  #["lit-nat", "id-nat", "pair-first", "local-tail", "big-ctor-70", "large-nat",
    "boxed-uint32", "packed-project-usize",
    "direct-call", "captured-partial", "capture-17-list",
    "recursive-empty", "recursive-traversal", "nat-add-small",
    "nat-add-tagged-to-heap", "nat-add-heap-input",
    "effect-record-nat", "effect-record-twice", "effect-record-byte-array-twice",
    "uint8-max", "uint16-max", "uint32-max", "uint64-max", "usize-max",
    "uint8-roundtrip", "uint16-roundtrip", "uint32-roundtrip", "uint64-roundtrip",
    "usize-roundtrip", "nat-list-roundtrip", "nat-list-nonempty", "nat-list-nonempty-bool",
    "nat-list-empty-bool", "unicode-string-roundtrip",
    "int-positive-roundtrip", "int-negative-roundtrip",
    "int-immediate-max", "int-immediate-min",
    "int-heap-positive-boundary", "int-heap-negative-boundary",
    "byte-array-roundtrip", "byte-array-size",
    "byte-array-get-zero", "byte-array-get-high-bit", "byte-array-get-max",
    "byte-array-set-unique", "byte-array-set-shared",
    "int-literal-immediate-positive", "int-literal-heap-positive",
    "int-literal-immediate-negative", "int-literal-heap-negative",
    "branch-nat", "branch-nat-false", "scalar-enum-cases",
    "int-classify-immediate-positive", "int-classify-immediate-negative",
    "int-classify-heap-positive", "int-classify-heap-negative",
    "packed-preserve", "tuple-rotate", "reuse-assoc", "reuse-change-tag",
    "reuse-grow-delete", "reuse-grow-delete-shared"]

def productJson (kind path : String) : Json :=
  Json.mkObj [("kind", kind), ("path", path)]

def semanticWasmContract : Json :=
  Json.mkObj [
    ("format", "wasm"),
    ("target", "wasm32"),
    ("runtimeFlavor", "fir-semantic-runtime-v1"),
    ("abi", "fir-semantic-abi-v1")]

def caseProducts (caseId : String) : Array Json :=
  #[productJson "wasm-manifest" s!"modules/{caseId}.wasm.json",
    productJson "wasm-module" s!"modules/{caseId}.wasm"]

def caseProductsJson (caseId : String) : Json :=
  Json.mkObj [
    ("caseId", caseId),
    ("products", Json.arr <| caseProducts caseId)]

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

/--
The validation provider publishes the source entry and, for floating
signatures, the canonical integer-lane facade selected by the checked
manifest. Recovering the descriptor here both validates the facade body and
keeps the provider's export check aligned with the released bit-exact
transport contract.
-/
def expectedValidationExports (module : Fir.Wasm.Module) (entry : Name) :
    Except String (Array Name) := do
  let descriptor? ← Fir.Wasm.Emit.BitExactFloat.descriptor? module entry
  return match descriptor? with
    | none => #[entry]
    | some descriptor => #[entry, descriptor.entry]

private def exportShapeEntry : Name := `firValidationExportShape
private def exportShapeArgument : FVarId := ⟨`firValidationExportShapeArgument⟩

private def exportShapeModule : Fir.Wasm.Module := {
  imports := #[]
  functions := #[{
    name := exportShapeEntry
    params := #[(exportShapeArgument, .float32)]
    results := #[.float32]
    locals := #[]
    body := [.localGet exportShapeArgument, .ret] }]
  exports := #[exportShapeEntry]
  initializers := #[]
  runtimeOperations := #[] }

#guard match Fir.Wasm.Emit.BitExactFloat.install exportShapeModule exportShapeEntry with
  | .ok module => match expectedValidationExports module exportShapeEntry with
      | .ok exports => exports == #[exportShapeEntry,
          Fir.Wasm.Emit.BitExactFloat.facadeName exportShapeEntry]
      | .error _ => false
  | .error _ => false

syntax (name := firValidationWasm) "#fir_validation_wasm" : command

@[command_elab firValidationWasm]
def elabFirValidationWasm : CommandElab := fun _ => do
  let env ← getEnv
  let selected ← liftIO selectedCaseIds
  let sortedSelected := selected.qsort (· < ·)
  let sortedManifestProducts := selected.qsort fun left right =>
    s!"modules/{left}.wasm.json" < s!"modules/{right}.wasm.json"
  let sortedModuleProducts := selected.qsort fun left right =>
    s!"modules/{left}.wasm" < s!"modules/{right}.wasm"
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
        validationCase.dependencies validationCase.argumentAliases
    let artifact ←
      match result with
      | .ok artifact => pure artifact
      | .error error =>
          throwError "Wasm compilation failed for {caseId}: {repr error}"
    let expectedExports ←
      match expectedValidationExports artifact.module validationCase.entry with
      | .ok exports => pure exports
      | .error error =>
          throwError "Wasm module export verification failed for {caseId}: {error}"
    unless artifact.module.exports == expectedExports do
      throwError
        "Wasm module export mismatch for {caseId}: expected {repr expectedExports}, got {repr artifact.module.exports}"
    let modulePath := moduleDirectory / s!"{caseId}.wasm"
    liftIO <| IO.FS.writeBinFile modulePath artifact.bytes
    liftIO <| IO.FS.writeFile (modulePath.toString ++ ".json")
      artifact.manifest.compress
  let manifestProducts :=
    sortedManifestProducts.map (fun caseId =>
      productJson "wasm-manifest" s!"modules/{caseId}.wasm.json") ++
    sortedModuleProducts.map (fun caseId =>
      productJson "wasm-module" s!"modules/{caseId}.wasm")
  let leanInput ← liftIO do
    return buildInputJson "lean-compiler" "bin/lean" (← IO.appPath)
  let oleanInputs ← env.header.moduleNames.mapM fun moduleName => do
    let path ← liftIO <| findOLean moduleName
    let name := moduleName.toString.replace "." "/" ++ ".olean"
    return buildInputJson "lean-olean" name path
  let buildInputManifest := Json.mkObj [
    ("version", Json.num protocolVersion),
    ("scope", "reported-loaded"),
    ("inputs", Json.arr <| #[leanInput] ++ oleanInputs)]
  liftIO <| IO.FS.writeFile
    ((outputDirectory : System.FilePath) / "build-inputs.json")
    buildInputManifest.compress
  let productManifest := Json.mkObj [
    ("version", Json.num protocolVersion),
    ("contract", semanticWasmContract),
    ("products", Json.arr manifestProducts),
    ("cases", Json.arr <| sortedSelected.map caseProductsJson)]
  liftIO <| IO.FS.writeFile
    ((outputDirectory : System.FilePath) / "products.json")
    productManifest.compress

end FirValidationWasm

#fir_validation_wasm
