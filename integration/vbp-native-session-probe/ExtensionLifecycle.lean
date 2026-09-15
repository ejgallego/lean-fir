import Fir.Wasm.Emit.ModuleSource

open Lean Fir.Wasm.Emit.ModuleSource

namespace ExtensionLifecycle

/-- Observation only: never reset the registry, alter a plugin, or free an
environment whose initializer closures may remain registered. -/
def snapshot : IO Json := do
  let extensions ← persistentEnvExtensionsRef.get
  let names := extensions.map (·.name.toString)
  let maps ← IO.FS.readFile "/proc/self/maps"
  let libraries := (maps.splitOn "\n").foldl (init := #[]) fun found line =>
    match (line.splitOn " ").getLast? with
    | some path =>
      if path.endsWith ".so" && (path.splitOn "VersoManual").length > 1 && !found.contains path then
        found.push path
      else found
    | none => found
  return Json.mkObj [
    ("inlineCount", toJson (names.filter (· == "Verso.Genre.Manual.inlineExtensionExt")).size),
    ("blockCount", toJson (names.filter (· == "Verso.Genre.Manual.blockExtensionExt")).size),
    ("manualLibraries", toJson (libraries.qsort (· < ·)))]

def run (mode : String) (rootSource rootSetup basicSource basicSetup out : System.FilePath) : IO Unit := do
  let root ← ModuleSetup.load rootSetup
  let basic ← ModuleSetup.load basicSetup
  unless root.name == `VersoBlueprintVir.Preview.Renderer && basic.name == `VersoManual.Basic do
    throw <| IO.userError "unexpected actual setup owners"
  let rows ← IO.mkRef (#[] : Array Json)
  let retained ← IO.mkRef (#[] : Array CapturedModule)
  let record (label : String) (action : IO Json) : IO Unit := do
    let before ← snapshot
    try
      let result ← action
      rows.modify (·.push (Json.mkObj [
        ("step", toJson label), ("before", before), ("after", ← snapshot),
        ("ok", toJson true), ("result", result)]))
    catch e =>
      rows.modify (·.push (Json.mkObj [
        ("step", toJson label), ("before", before), ("after", ← snapshot),
        ("ok", toJson false), ("error", toJson e.toString)]))
      throw e
  let capture (source : System.FilePath) (setup : ModuleSetup) : IO Unit :=
    record s!"capture:{setup.name}" do
      unsafe enableInitializersExecution
      match ← compile source setup with
      | .error messages =>
        let rendered ← messages.toList.mapM (·.toString)
        throw <| IO.userError (String.intercalate "\n" rendered)
      | .ok c =>
        retained.modify (·.push c)
        let entry := if setup.name == basic.name then
          `Verso.Genre.Manual.instToJsonInline.toJson
          else `VersoBlueprint.Experimental.VirPreview.Renderer.render
        let a ← c.artifact entry
        return Json.mkObj [("groups", toJson c.groups.size),
          ("localDeclarations", toJson (a.program.decls.size - a.externalNames.size)),
          ("externalSignatures", toJson a.externalNames.size)]
  let plugins (setup : ModuleSetup) : IO Unit := do
    unless setup.dynlibs.isEmpty do throw <| IO.userError "unreviewed dynlib input"
    for plugin in setup.plugins do
      record s!"plugin:{plugin.path}" do
        withImporting <| loadPlugin plugin.path plugin.initFn?
        return Json.null
  let initial ← snapshot
  let failure ← try
    match mode with
    | "fresh-basic" => capture basicSource basic
    | "root-basic" => capture rootSource root; capture basicSource basic
    | "basic-basic" => capture basicSource basic; capture basicSource basic
    | "plugins-root-repeat" => plugins root; plugins root
    | "plugins-root-ext" =>
      plugins root
      let some ext := basic.plugins.find? (fun p =>
          p.path.fileName == some "verso_VersoManual_Ext.so") |
        throw <| IO.userError "actual Basic setup has no Ext plugin"
      record s!"plugin:{ext.path}" do
        withImporting <| loadPlugin ext.path ext.initFn?
        return Json.null
    | _ => throw <| IO.userError s!"unknown lifecycle mode {mode}"
    pure none
  catch e => pure (some e.toString)
  -- Keep all captured environments live until every observation has completed.
  let count := (← retained.get).size
  if let some parent := out.parent then IO.FS.createDirAll parent
  IO.FS.writeFile out <| (Json.mkObj [
    ("mode", toJson mode), ("initial", initial), ("steps", toJson (← rows.get)),
    ("failure", toJson failure), ("retainedCaptures", toJson count),
    ("worklistResumed", toJson false), ("registryReset", toJson false)]).pretty ++ "\n"
  IO.println s!"{mode}: {count} captures; failure={failure}"

end ExtensionLifecycle

def main (args : List String) : IO Unit := do
  let [mode, rootSource, rootSetup, basicSource, basicSetup, out] := args |
    throw <| IO.userError "usage: ExtensionLifecycle.lean mode root.lean root.setup.json basic.lean basic.setup.json output.json"
  ExtensionLifecycle.run mode rootSource rootSetup basicSource basicSetup out
