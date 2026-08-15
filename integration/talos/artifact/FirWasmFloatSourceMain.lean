import Fir.Wasm.Emit.ResidentFloatSource
import Fir.Wasm.Emit.Manifest

open Lean

private def functionSignatureJson (function : Fir.Wasm.Function) : Json :=
  Json.mkObj [
    ("name", function.name.toString),
    ("params", Fir.Wasm.Emit.Manifest.abiKindsJson (function.params.map (·.2))),
    ("results", Fir.Wasm.Emit.Manifest.abiKindsJson function.results)]

private def bitString (value : Float) : String :=
  toString value.toBits.toNat

private def naturalOracleCases : Array Nat := #[
  0,
  1,
  2 ^ 53 - 1,
  2 ^ 53,
  2 ^ 53 + 1,
  2 ^ 64 - 1,
  2 ^ 64,
  2 ^ 64 + 1,
  2 ^ 127 + 2 ^ 65 + 3,
  10 ^ 308,
  2 ^ 1024]

private def scientificOracleCases : Array (Nat × Bool × Nat) := #[
  (12345, false, 0),
  (1, false, 22),
  (1, true, 22),
  (2 ^ 53 - 1, false, 22),
  (2 ^ 53, false, 0),
  (1, false, 23),
  (1, false, 308),
  (1, false, 309),
  (5, true, 324),
  (4, true, 324),
  (1, true, 400),
  (9007199254740993, true, 0),
  (2 ^ 127 + 1, true, 37)]

private def oracleJson : Json := Json.mkObj [
  ("ofNat", Json.arr <| naturalOracleCases.map fun value => Json.mkObj [
    ("value", toString value),
    ("bits", bitString (Float.ofNat value))]),
  ("ofScientific", Json.arr <| scientificOracleCases.map
    fun (mantissa, hasDot, exponent) => Json.mkObj [
      ("mantissa", toString mantissa),
      ("hasDot", hasDot),
      ("exponent", toString exponent),
      ("bits", bitString (Float.ofScientific mantissa hasDot exponent))])]

private unsafe def compileArtifact : IO Fir.Wasm.Emit.Source.ModuleArtifact := do
  Lean.initSearchPath (← Lean.findSysroot) [
    ".lake/build/lib/lean",
    "../../../.lake/build/lib/lean"]
  Lean.enableInitializersExecution
  let options := maxHeartbeats.set ({} : Options) 0
  let env ← Lean.importModules
    #[{ module := `Fir.Wasm.Emit.ResidentFloatSource }] options
    (leakEnv := true) (loadExts := true)
  let (result, _) ← Lean.Core.CoreM.toIO
    (ctx := { fileName := "FirWasmFloatSourceMain.lean", fileMap := default, options })
    (s := { env })
    Fir.Wasm.Emit.ResidentFloatSource.compile
  IO.ofExcept <| result.mapError fun error => s!"{repr error}"

private def writeArtifact (artifact : Fir.Wasm.Emit.Source.ModuleArtifact)
    (output : System.FilePath) : IO Unit := do
  IO.ofExcept <| (← artifact.write output).mapError fun error => s!"{repr error}"
  unless artifact.module.imports.isEmpty do
    let names := artifact.module.imports.filterMap (·.declaration?)
    throw <| IO.userError
      s!"source Float module retained imports: {names}"
  unless artifact.module.runtimeOperations.isEmpty do
    throw <| IO.userError
      s!"source Float module retained {artifact.module.runtimeOperations.size} runtime operation(s)"
  let expectedExports := Fir.Wasm.Emit.ResidentFloatSource.publicExports ++
    Fir.Wasm.Emit.ResidentLinker.allocatorExports
  unless artifact.module.exports == expectedExports do
    throw <| IO.userError
      s!"source Float export mismatch: {repr artifact.module.exports}"
  let functions := artifact.module.functions.map (·.name)
  let sourceFunctions := artifact.source.program.decls.filterMap fun declaration =>
    match declaration.value with
    | .code _ => some declaration.name
    | .extern _ => none
  let retainedSourceFunctions := sourceFunctions.filter functions.contains
  let residentHelpers := functions.filter fun name =>
    !retainedSourceFunctions.contains name
  let inventory := Json.mkObj [
    ("entries", Json.arr <| Fir.Wasm.Emit.ResidentFloatSource.entries.map
      fun name => (name.toString : Json)),
    ("capturedDeclarations", artifact.source.program.decls.size),
    ("reviewedExternalsBeforeLink", artifact.source.externalNames.size),
    ("externalsBeforeLink", Json.arr <| artifact.source.externalNames.map
      fun name => (name.toString : Json)),
    ("functions", Json.arr <| functions.map fun name => (name.toString : Json)),
    ("sourceFunctions", Json.arr <| retainedSourceFunctions.map
      fun name => (name.toString : Json)),
    ("residentHelpers", Json.arr <| residentHelpers.map
      fun name => (name.toString : Json)),
    ("publicFunctions", Json.arr <| artifact.module.exports.map
      fun name => (name.toString : Json)),
    ("publicSignatures", Json.arr <| artifact.module.functions.filterMap
      fun function => if artifact.module.exports.contains function.name then
        some (functionSignatureJson function) else none),
    ("functionImports", artifact.module.imports.size),
    ("runtimeOperations", artifact.module.runtimeOperations.size)]
  IO.FS.writeFile (output.toString ++ ".inventory.json")
    (inventory.pretty ++ "\n")
  IO.FS.writeFile (output.toString ++ ".oracle.json")
    (oracleJson.pretty ++ "\n")

unsafe def main (args : List String) : IO UInt32 := do
  try
    let output : System.FilePath ← match args with
      | [output] => pure output
      | _ => throw (IO.userError
          "usage: fir-wasm-float-source <output.wasm>")
    let artifact ← compileArtifact
    writeArtifact artifact output
    IO.println s!"source-float: wrote {artifact.bytes.size} bytes to {output}"
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
