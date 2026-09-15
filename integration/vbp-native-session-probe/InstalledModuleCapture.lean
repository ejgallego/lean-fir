import Probe.InstalledInputs

open Lean Lean.Compiler.LCNF Fir.Wasm.Emit.ModuleSource InstalledInputs

def main (args : List String) : IO UInt32 := do
  let [inputFile, moduleName, outputDir] := args |
    throw <| IO.userError "usage: InstalledModuleCapture.lean inputs.json module output-dir"
  let inputs ← IO.ofExcept <| Json.parse (← IO.FS.readFile inputFile)
  let modules : Array Json := ← get inputs "modules"
  let rows ← modules.filterM fun row => return (← get row "name" : String) == moduleName
  unless rows.size == 1 do throw <| IO.userError "missing or ambiguous installed module"
  let row := rows[0]!
  let (source, setup) ← verify inputs row
  if outputDir == "--verify" then
    IO.println s!"{moduleName}: derived inputs verified"
    return 0
  unsafe enableInitializersExecution
  let captured ← match ← compile source setup with
    | .ok captured => pure captured
    | .error messages => do
      for message in messages.toList do IO.eprintln (← message.toString)
      throw <| IO.userError s!"installed frontend failed: {moduleName}"
  let entries : Array String := ← get row "entries"
  let out : System.FilePath := outputDir
  IO.FS.createDirAll out
  let mut results := #[]
  for entry in entries do
    let artifact ← captured.artifact entry.toName
    let text ← artifact.format.toIO' {
      fileName := source.toString
      fileMap := default
      options := captured.options } { env := captured.environment }
    IO.FS.writeFile (out / s!"{results.size}.lcnf") text
    results := results.push <| Json.mkObj [
      ("entry", toJson entry), ("locals", toJson (artifact.program.decls.size - artifact.externalNames.size)),
      ("externals", toJson artifact.externalNames.size)]
  IO.FS.writeFile (out / "capture.json") <| (Json.mkObj [
    ("module", toJson moduleName), ("kind", "pinned-bootstrap-derived-capture-inputs/v1"),
    ("groups", toJson (captured.groups.map (·.map (·.name.toString)))),
    ("entries", toJson results), ("options", toJson setup.options),
    ("recursiveCapture", toJson false), ("lowered", toJson false)]).pretty ++ "\n"
  IO.println s!"{moduleName}: {captured.groups.size} groups; {entries.size} requested entries captured"
  return 0
