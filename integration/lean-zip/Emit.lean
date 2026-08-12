import LeanZipFir.Compile
import Lean.Elab.Command

open Lean Elab Command

private def nameArrayJson (names : Array Name) : Json :=
  Json.arr <| names.map fun name => (name.toString : Json)

private def functionSignatureJson (function : Fir.Wasm.Function) : Json :=
  Json.mkObj [
    ("name", function.name.toString),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson (function.params.map (·.2))),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson function.results)]

set_option maxHeartbeats 0 in
run_cmd do
  IO.FS.createDirAll "_build"
  let baseResult ← liftCoreM LeanZipFir.Compile.compileStoredBase
  let base ← match baseResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile stored source: {repr error}"
  match ← base.write "_build/lean-zip-stored-base.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write stored base module: {repr error}"
  let linkedResult ← liftCoreM LeanZipFir.Compile.compileStored
  let linked ← match linkedResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link stored runtime: {repr error}"
  match ← linked.write "_build/lean-zip-stored.wasm" with
  | .error error => throwError "failed to write resident stored module: {repr error}"
  | .ok () =>
      unless linked.module.imports.isEmpty do
        throwError "stored module retained function imports"
      unless linked.module.runtimeOperations.isEmpty do
        throwError "stored module retained runtime operations"
      let functionNames := linked.module.functions.map (·.name)
      let sourceFunctionNames := linked.source.program.decls.filterMap fun decl =>
        match decl.value with
        | .code _ => some decl.name
        | .extern _ => none
      let retainedSourceFunctions := sourceFunctionNames.filter functionNames.contains
      let residentHelpers := functionNames.filter fun name =>
        !retainedSourceFunctions.contains name
      let inventory := Json.mkObj [
        ("entry", LeanZipFir.Compile.storedEntry.toString),
        ("capturedDeclarations", linked.source.program.decls.size),
        ("reviewedExternalsBeforeLink", linked.source.externalNames.size),
        ("externals", nameArrayJson linked.source.externalNames),
        ("functions", nameArrayJson functionNames),
        ("publicFunctions", nameArrayJson linked.module.exports),
        ("publicSignatures", Json.arr <| linked.module.functions.filterMap fun function =>
          if linked.module.exports.contains function.name then
            some (functionSignatureJson function)
          else none),
        ("sourceFunctions", nameArrayJson retainedSourceFunctions),
        ("residentHelpers", nameArrayJson residentHelpers),
        ("residentGlobals", linked.module.globals.size),
        ("runtimeOperations", linked.module.runtimeOperations.size)]
      IO.FS.writeFile "_build/lean-zip-stored.inventory.json"
        (inventory.pretty ++ "\n")
      logInfo m!"wrote {linked.bytes.size} stored bytes, {retainedSourceFunctions.size} source functions, and {residentHelpers.size} resident helpers"
  let level1BaseResult ← liftCoreM LeanZipFir.Compile.compileLevel1Base
  let level1Base ← match level1BaseResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile Level-1 source: {repr error}"
  match ← level1Base.write "_build/lean-zip-level1-base.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write Level-1 base module: {repr error}"
  let level1Result ← liftCoreM LeanZipFir.Compile.compileLevel1
  let level1 ← match level1Result with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to link Level-1 runtime: {repr error}"
  match ← level1.write "_build/lean-zip-level1.wasm" with
  | .error error => throwError "failed to write resident Level-1 module: {repr error}"
  | .ok () =>
      unless level1.module.imports.isEmpty do
        throwError "Level-1 module retained function imports"
      unless level1.module.runtimeOperations.isEmpty do
        throwError "Level-1 module retained runtime operations"
      let functionNames := level1.module.functions.map (·.name)
      let sourceFunctionNames := level1.source.program.decls.filterMap fun decl =>
        match decl.value with
        | .code _ => some decl.name
        | .extern _ => none
      let retainedSourceFunctions := sourceFunctionNames.filter functionNames.contains
      let residentHelpers := functionNames.filter fun name =>
        !retainedSourceFunctions.contains name
      let inventory := Json.mkObj [
        ("entry", LeanZipFir.Compile.level1Entry.toString),
        ("capturedDeclarations", level1.source.program.decls.size),
        ("reviewedExternalsBeforeLink", level1.source.externalNames.size),
        ("externals", nameArrayJson level1.source.externalNames),
        ("functions", nameArrayJson functionNames),
        ("publicFunctions", nameArrayJson level1.module.exports),
        ("publicSignatures", Json.arr <| level1.module.functions.filterMap fun function =>
          if level1.module.exports.contains function.name then
            some (functionSignatureJson function)
          else none),
        ("sourceFunctions", nameArrayJson retainedSourceFunctions),
        ("residentHelpers", nameArrayJson residentHelpers),
        ("residentGlobals", level1.module.globals.size),
        ("runtimeOperations", level1.module.runtimeOperations.size)]
      IO.FS.writeFile "_build/lean-zip-level1.inventory.json"
        (inventory.pretty ++ "\n")
      logInfo m!"wrote {level1.bytes.size} Level-1 bytes, {retainedSourceFunctions.size} source functions, and {residentHelpers.size} resident helpers"
