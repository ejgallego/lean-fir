import Fir.Wasm.Emit.ModuleSource
import Vir.HostMetadata

open Lean Lean.Compiler.LCNF Fir.Wasm.Emit.ModuleSource

namespace ModuleAssembly

private def entry := `VersoBlueprint.Experimental.VirPreview.Renderer.render
private def selected := `VersoReact.Renderer.render

private def signatureMatches (a b : Decl .impure) : Bool :=
  a.type == b.type && a.safe == b.safe && a.levelParams == b.levelParams &&
    a.params.map (fun p => (p.type, p.borrow)) == b.params.map (fun p => (p.type, p.borrow))

/-- Fixture-only capture composition. Names are not enough: both incoming
signatures and every duplicated external must agree before assembly. -/
private def assemble (root dependency : Fir.Compiler.Lcnf.Artifact) :
    Except String Fir.Compiler.Lcnf.Artifact := do
  let roots := root.program.decls.filter fun d => !root.externalNames.contains d.name
  let deps := dependency.program.decls.filter fun d => !dependency.externalNames.contains d.name
  let mut bodies := roots
  for decl in deps do
    if bodies.any (·.name == decl.name) then
      throw s!"duplicate local definition: {decl.name}"
    bodies := bodies.push decl
  let mut externals : Array (Decl .impure) := #[]
  for decl in root.program.decls ++ dependency.program.decls do
    unless root.externalNames.contains decl.name || dependency.externalNames.contains decl.name do
      continue
    if let some body := bodies.find? (·.name == decl.name) then
      unless signatureMatches decl body do throw s!"body/signature mismatch: {decl.name}"
    else if let some previous := externals.find? (·.name == decl.name) then
      unless signatureMatches decl previous do throw s!"external signature mismatch: {decl.name}"
    else
      externals := externals.push decl
  let program : Fir.LeanIR.ImpureProgram := { decls := bodies ++ externals }
  return {
    entry := root.entry
    program
    externalNames := externals.map (·.name)
    forms := Fir.Compiler.Lcnf.collectForms program }

private def compileChecked (source : System.FilePath) (setup : ModuleSetup) : IO CapturedModule := do
  -- Each withImporting clears this flag. These frontend invocations are serial,
  -- use one pinned native/imported source version, and retain their environments.
  unsafe enableInitializersExecution
  match ← compile source setup with
  | .ok captured => return captured
  | .error messages =>
    for message in messages.toList do IO.eprintln (← message.toString)
    throw <| IO.userError s!"owning module compilation failed: {setup.name}"

private def format (captured : CapturedModule) (artifact : Fir.Compiler.Lcnf.Artifact) : IO String :=
  artifact.format.toIO' {
    fileName := captured.sourceFile.toString
    fileMap := default
    options := captured.options } { env := captured.environment }

private def groupsArtifact (captured : CapturedModule) : Fir.Compiler.Lcnf.Artifact := {
  entry
  program := { decls := captured.groups.flatten }
  externalNames := #[]
  forms := #[] }

private def frontierRow (captured : CapturedModule) (name : Name) : IO Json := do
  let owner := (captured.environment.getModuleIdxFor? name).map fun idx =>
    captured.environment.header.moduleNames[idx.toNat]!
  let symbols := (getExternAttrData? captured.environment name).toArray.flatMap fun data =>
    data.entries.toArray.filterMap fun e => match e with
      | .standard _ symbol => some symbol
      | _ => none
  let targets := symbols.filterMap fun symbol =>
    (Vir.HostMetadata.decodeExternSymbol? symbol).map (·.target)
  let mut sources : Array String := #[]
  if let some owner := owner then
    for dir in ← getSrcSearchPath do
      let path := modToFilePath dir owner "lean"
      if ← path.pathExists then
        let real := (← IO.FS.realPath path).toString
        if !sources.contains real then sources := sources.push real
  return Json.mkObj [
    ("name", toJson name.toString), ("module", toJson (owner.map Name.toString)),
    ("externSymbols", toJson symbols), ("virTargets", toJson targets),
    ("sources", toJson sources)]

def run (rootSource rootSetup dependencySetup out : System.FilePath) : IO Unit := do
  let root ← compileChecked rootSource (← ModuleSetup.load rootSetup)
  let initial ← root.artifact entry
  unless initial.externalNames.contains selected do
    throw <| IO.userError "selected dependency is not an actual renderer external"
  let some ownerIdx := root.environment.getModuleIdxFor? selected |
    throw <| IO.userError "selected external has no defining-module provenance"
  let owner := root.environment.header.moduleNames[ownerIdx.toNat]!
  let setup ← ModuleSetup.load dependencySetup
  unless setup.name == owner do
    throw <| IO.userError s!"dependency setup {setup.name} differs from recorded owner {owner}"
  -- Lake's source search path, not a copy or a guessed generated-name owner.
  let source ← findLean (← getSrcSearchPath) owner
  let rootText ← format root initial
  let groupsText ← format root (groupsArtifact root)
  IO.eprintln s!"Capturing selected owner {owner} from {source}"
  let dependency ← compileChecked source setup
  let selectedArtifact ← dependency.artifact selected
  let product ← IO.ofExcept (assemble initial selectedArtifact)
  unless product.program.decls.any (fun d => d.name == selected && !product.externalNames.contains d.name) do
    throw <| IO.userError "selected dependency body is absent after assembly"
  unless rootText == (← format root (← root.artifact entry)) &&
      groupsText == (← format root (groupsArtifact root)) do
    throw <| IO.userError "root capture changed while compiling dependency"
  -- Signature sensitivity: corrupt the actual selected signature's borrow bit.
  let corrupted := { initial with program := { decls := initial.program.decls.map fun d =>
    if d.name == selected then
      { d with params := d.params.modify 0 fun p => { p with borrow := !p.borrow } }
    else d } }
  if let .ok _ := assemble corrupted selectedArtifact then
    throw <| IO.userError "signature mismatch negative control was accepted"
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "root.lcnf") rootText
  IO.FS.writeFile (out / "root-groups.lcnf") groupsText
  IO.FS.writeFile (out / "dependency.lcnf") (← format dependency selectedArtifact)
  IO.FS.writeFile (out / "assembled.lcnf") (← format root product)
  let frontier ← initial.externalNames.mapM (frontierRow root)
  let imports := product.externalNames.map fun name => Json.mkObj [
    ("name", toJson name.toString),
    ("module", toJson <| ((root.environment.getModuleIdxFor? name).map fun idx =>
      root.environment.header.moduleNames[idx.toNat]!.toString) <|>
      ((dependency.environment.getModuleIdxFor? name).map fun idx =>
        dependency.environment.header.moduleNames[idx.toNat]!.toString))]
  IO.FS.writeFile (out / "assembly.json") <| (Json.mkObj [
    ("entry", toJson entry.toString), ("selected", toJson selected.toString),
    ("owner", toJson owner.toString), ("source", toJson source.toString),
    ("setup", toJson dependencySetup.toString),
    ("rootGroups", toJson <| root.groups.map fun g => g.map (·.name.toString)),
    ("dependencyGroups", toJson <| dependency.groups.map fun g => g.map (·.name.toString)),
    ("localDeclarations", toJson <| product.program.decls.filterMap fun d =>
      if product.externalNames.contains d.name then none else some d.name.toString),
    ("imports", toJson imports),
    ("rootFrontier", toJson frontier),
    ("rootUnchanged", toJson true), ("signatureMismatchRejected", toJson true),
    ("recursiveCapture", toJson false), ("lowered", toJson false)]).pretty ++ "\n"
  IO.eprintln s!"Assembly: {product.program.decls.size - product.externalNames.size} locals / {product.externalNames.size} external signatures"

end ModuleAssembly

def main (args : List String) : IO Unit := do
  let [source, setup, dependencySetup, out] := args |
    throw <| IO.userError "usage: ModuleAssembly.lean root.lean root.setup.json dependency.setup.json out"
  ModuleAssembly.run source setup dependencySetup out
