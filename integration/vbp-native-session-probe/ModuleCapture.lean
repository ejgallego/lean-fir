import Fir.Wasm.Emit.ModuleSource

open Lean Lean.Compiler.LCNF Fir.Wasm.Emit.ModuleSource

namespace OrdinaryModuleCapture

private def reportMessages (messages : MessageLog) : IO Unit :=
  messages.toList.forM fun message => do IO.eprintln (← message.toString)

/-- Exercise the production adapter against unchanged real module source. -/
def capture (sourceFile setupFile outputDir : System.FilePath) (entry : Name) : IO UInt32 := do
  let setup ← ModuleSetup.load setupFile
  IO.eprintln s!"Ordinary module capture begin: {setup.name}"
  let captured ← match ← compile sourceFile setup with
    | .ok captured => pure captured
    | .error messages => do
      reportMessages messages
      throw <| IO.userError "ordinary module frontend failed"
  let declarations := captured.groups.flatten
  unless !declarations.isEmpty do
    throw <| IO.userError "ordinary frontend completed without recorded final LCNF"
  let artifact ← captured.artifact entry
  let text ← artifact.format.toIO' {
    fileName := sourceFile.toString
    fileMap := default
    options := captured.options } { env := captured.environment }
  -- A missing local root must not silently become an external signature.
  let missingRejected ← try
    discard <| captured.artifact `firDeliberatelyMissingModuleEntry
    pure false
  catch _ => pure true
  unless missingRejected do throw <| IO.userError "missing entry was accepted"
  let nonModuleRejected ← try
    discard <| compile sourceFile { setup with isModule := false }
    pure false
  catch _ => pure true
  unless nonModuleRejected do throw <| IO.userError "non-module setup was accepted"
  IO.FS.createDirAll outputDir
  IO.FS.writeFile (outputDir / "entry.lcnf") text
  let rows := captured.groups.map fun group => toJson (group.map fun decl => decl.name.toString)
  let imports := artifact.externalNames.map fun name => Json.mkObj [
    ("name", toJson name.toString),
    ("module", toJson <| (captured.environment.getModuleIdxFor? name).map fun idx =>
      captured.environment.header.moduleNames[idx.toNat]!.toString)]
  IO.FS.writeFile (outputDir / "module-capture.json") <| (Json.mkObj [
    ("module", toJson setup.name.toString),
    ("source", toJson sourceFile.toString),
    ("setup", toJson setupFile.toString),
    ("groups", toJson rows),
    ("declarationCount", toJson declarations.size),
    ("entry", toJson entry.toString),
    ("entryDeclarations", toJson <| artifact.program.decls.map (·.name.toString)),
    ("imports", toJson imports),
    ("postponeCompile", toJson false),
    ("asyncElaboration", toJson false),
    ("targetImported", toJson false),
    ("missingEntryRejected", toJson missingRejected),
    ("nonModuleSetupRejected", toJson nonModuleRejected),
    ("capturePhase", "final-impure")]).pretty ++ "\n"
  IO.eprintln s!"Ordinary module capture complete: {captured.groups.size} groups, {declarations.size} declarations"
  IO.eprintln s!"Entry closure: {artifact.program.decls.size - artifact.externalNames.size} local declarations, {artifact.externalNames.size} external signatures"
  return 0

end OrdinaryModuleCapture

def main (args : List String) : IO UInt32 := do
  unsafe enableInitializersExecution
  let [source, setup, output, entry] := args |
    throw <| IO.userError "usage: ModuleCapture.lean source.lean module.setup.json output-directory entry"
  OrdinaryModuleCapture.capture source setup output entry.toName
