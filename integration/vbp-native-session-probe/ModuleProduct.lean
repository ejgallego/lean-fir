import Probe.InstalledInputs
import Vir.HostMetadata

open Lean Lean.Compiler.LCNF Fir.Wasm.Emit.ModuleSource

namespace RendererModuleProduct

def entry := `VersoBlueprint.Experimental.VirPreview.Renderer.render

def signatureMatches (a b : Decl .impure) : Bool :=
  a.type == b.type && a.safe == b.safe && a.levelParams == b.levelParams &&
    a.params.map (fun p => (p.type, p.borrow)) == b.params.map (fun p => (p.type, p.borrow))

structure OwnedBody where
  owner : Name
  decl : Decl .impure

structure External where
  decl : Decl .impure
  owner : Name
  symbols : Array String
  targets : Array String
  sources : Array String

def External.row (e : External) : Json := Json.mkObj [
  ("name", toJson e.decl.name.toString), ("module", toJson e.owner.toString),
  ("externSymbols", toJson e.symbols), ("virTargets", toJson e.targets),
  ("sources", toJson e.sources),
  ("category", toJson (if !e.targets.isEmpty then "VIR boundary"
    else if !e.symbols.isEmpty then "runtime/primitive boundary" else "source pending"))]

def External.isBoundary (e : External) : Bool := !e.symbols.isEmpty

structure Product where
  bodies : Array OwnedBody := #[]
  externals : Array External := #[]
  modules : Array CapturedModule := #[]
  selections : Array Json := #[]

def Product.artifact (p : Product) : Fir.Compiler.Lcnf.Artifact := {
  entry
  program := { decls := p.bodies.map (·.decl) ++ p.externals.map (·.decl) }
  externalNames := p.externals.map (·.decl.name)
  forms := #[] }

def format (c : CapturedModule) (a : Fir.Compiler.Lcnf.Artifact) : IO String :=
  a.format.toIO' {
    fileName := c.sourceFile.toString
    fileMap := default
    options := c.options } { env := c.environment }

def compileChecked (source : System.FilePath) (setup : ModuleSetup) : IO CapturedModule := do
  unsafe enableInitializersExecution
  match ← compile source setup with
  | .ok captured => return captured
  | .error messages =>
    for msg in messages.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError s!"compiler diagnostic in {setup.name}"

def external (c : CapturedModule) (decl : Decl .impure) : IO External := do
  let owner ← match c.environment.getModuleIdxFor? decl.name with
    | some idx => pure c.environment.header.moduleNames[idx.toNat]!
    | none =>
      if c.groups.any (·.any (·.name == decl.name)) then pure c.moduleName
      else throw <| IO.userError s!"unknown owner: {decl.name}"
  let symbols := (getExternAttrData? c.environment decl.name).toArray.flatMap fun data =>
    data.entries.toArray.filterMap fun e => match e with
      | .standard _ symbol => some symbol
      | _ => none
  let targets := symbols.filterMap fun symbol =>
    (Vir.HostMetadata.decodeExternSymbol? symbol).map (·.target)
  let mut sources := #[]
  for dir in ← getSrcSearchPath do
    let path := modToFilePath dir owner "lean"
    if ← path.pathExists then
      let real := (← IO.FS.realPath path).toString
      if !sources.contains real then sources := sources.push real
  return { decl, owner, symbols, targets, sources }

/-- Admission uses one canonical recorded body per module/name. Re-selecting
that same module product may reuse its body; a second provider may not define it.
Every external edge is checked even if its body was admitted earlier. -/
def admit (p : Product) (c : CapturedModule) (a : Fir.Compiler.Lcnf.Artifact) : IO Product := do
  let mut p := p
  for decl in a.program.decls do
    if let .extern _ := decl.value then continue
    let some canonical := c.groups.flatten.find? (·.name == decl.name) |
      throw <| IO.userError s!"body not in owning capture: {decl.name}"
    unless signatureMatches canonical decl do
      throw <| IO.userError s!"canonical body/signature mismatch: {decl.name}"
    if let some prior := p.bodies.find? (·.decl.name == decl.name) then
      unless prior.owner == c.moduleName && signatureMatches prior.decl canonical do
        throw <| IO.userError s!"duplicate body/provider: {decl.name}"
    else
      p := { p with bodies := p.bodies.push { owner := c.moduleName, decl := canonical } }
  for decl in a.program.decls do
    unless (match decl.value with | .extern _ => true | _ => false) do continue
    let next ← external c decl
    if let some prior := p.externals.find? (·.decl.name == decl.name) then
      unless signatureMatches prior.decl decl && prior.owner == next.owner &&
          prior.symbols == next.symbols && prior.targets == next.targets do
        throw <| IO.userError s!"external signature/provenance mismatch: {decl.name}"
    else
      p := { p with externals := p.externals.push next }
  let mut unresolved := #[]
  for e in p.externals do
    if let some body := p.bodies.find? (·.decl.name == e.decl.name) then
      unless body.owner == e.owner && signatureMatches body.decl e.decl do
        throw <| IO.userError s!"body/signature mismatch: {e.decl.name}"
      unless !e.isBoundary do
        throw <| IO.userError s!"source body conflicts with native boundary: {e.decl.name}"
    else unresolved := unresolved.push e
  return { p with externals := unresolved }

def save (p : Product) (out : System.FilePath) (complete : Bool) (failure : Option String) : IO Unit := do
  IO.FS.createDirAll out
  let some root := p.modules[0]? | throw <| IO.userError "empty module product"
  IO.FS.writeFile (out / "product.lcnf") (← format root p.artifact)
  IO.FS.writeFile (out / "product.json") <| (Json.mkObj [
    ("entry", toJson entry.toString), ("complete", toJson complete), ("failure", toJson failure),
    ("negativeControls", toJson true),
    ("lowered", toJson false), ("hostProfileAdmitted", toJson false),
    ("modules", toJson (p.modules.map fun c => Json.mkObj [
      ("name", toJson c.moduleName.toString), ("source", toJson c.sourceFile.toString),
      ("groups", toJson (c.groups.map (·.map (·.name.toString))))])),
    ("bodies", toJson (p.bodies.map fun b => Json.mkObj [
      ("name", toJson b.decl.name.toString), ("owner", toJson b.owner.toString)])),
    ("selections", toJson p.selections),
    ("frontier", toJson (p.externals.map (·.row)))]).pretty ++ "\n"

def mustReject (label : String) (action : IO Unit) : IO Unit := do
  let rejected ← try action; pure false catch _ => pure true
  unless rejected do throw <| IO.userError s!"negative control accepted: {label}"

def controls (root : CapturedModule) (p : Product) : IO Unit := do
  let a ← root.artifact entry
  let some d := a.program.decls.find? (fun d => !d.params.isEmpty) |
    throw <| IO.userError "no parameterized declaration for signature controls"
  let mutations := #[
    { d with params := d.params.modify 0 fun p => { p with borrow := !p.borrow } },
    { d with safe := !d.safe },
    { d with levelParams := `firNegativeUniverse :: d.levelParams },
    { d with type := mkConst `firNegativeResultType },
    { d with params := d.params.modify 0 fun p =>
      { p with type := mkConst `firNegativeParameterType } }]
  for bad in mutations do
    if signatureMatches d bad then throw <| IO.userError "signature mutation accepted"
    let corrupted := { a with program := { decls := a.program.decls.map fun x =>
      if x.name == d.name then bad else x } }
    mustReject "signature admission" (discard <| admit p root corrupted)
  mustReject "duplicate provider" (discard <| admit p { root with moduleName := `firOtherOwner } a)
  mustReject "unknown owner" (discard <| external root { d with name := `firUnknownOwner })
  mustReject "missing entry" (discard <| root.artifact `firMissingLocalEntry)

def run (rootSource rootSetup resolver out : System.FilePath) : IO Unit := do
  let root ← compileChecked rootSource (← ModuleSetup.load rootSetup)
  let mut p ← admit { modules := #[root] } root (← root.artifact entry)
  controls root p
  let original ← format root (← root.artifact entry)
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "root.lcnf") original
  let mut stopped := false
  while !stopped do
    let some next := p.externals.find? (fun e => !e.isBoundary) | break
    try
      IO.eprintln s!"Selecting {next.decl.name} from {next.owner}"
      let c ← if let some cached := p.modules.find? (·.moduleName == next.owner) then
          pure cached
        else do
          let request := out / "request.json"
          IO.FS.writeFile request next.row.pretty
          let response ← IO.Process.output { cmd := "node", args := #[resolver.toString, request.toString] }
          unless response.exitCode == 0 do
            throw <| IO.userError s!"input unavailable for {next.owner}: {response.stderr.trimAscii}"
          let resolved ← IO.ofExcept (Json.parse response.stdout)
          let route : String ← InstalledInputs.get resolved "route"
          let (source, setup) ← if route == "lake" then do
              let source : System.FilePath ← InstalledInputs.get resolved "source"
              let setupPath : System.FilePath ← InstalledInputs.get resolved "setup"
              let setup ← ModuleSetup.load setupPath
              unless setup.name == next.owner do throw <| IO.userError "Lake setup owner mismatch"
              pure (source, setup)
            else if route == "installed" then do
              let inputs : Json ← InstalledInputs.get resolved "inputs"
              let rows : Array Json ← InstalledInputs.get inputs "modules"
              unless rows.size == 1 do throw <| IO.userError "ambiguous installed input"
              InstalledInputs.verify inputs rows[0]!
            else throw <| IO.userError s!"unknown input route: {route}"
          let c ← compileChecked source setup
          unless c.moduleName == next.owner do throw <| IO.userError "captured owner mismatch"
          p := { p with modules := p.modules.push c }
          IO.eprintln s!"Captured {c.moduleName}: {c.groups.size} groups"
          pure c
      let selected ← c.artifact next.decl.name
      -- Repeat selected bodies are selected from this exact cached environment,
      -- never from a second compilation with the same module name.
      let updated ← admit p c selected
      unless updated.bodies.any (·.decl.name == next.decl.name) &&
          !updated.externals.any (·.decl.name == next.decl.name) do
        throw <| IO.userError s!"selection did not close source edge: {next.decl.name}"
      p := { updated with selections := updated.selections.push (Json.mkObj [
        ("name", toJson next.decl.name.toString), ("module", toJson next.owner.toString),
        ("bodies", toJson updated.bodies.size), ("externals", toJson updated.externals.size)]) }
      unless original == (← format root (← root.artifact entry)) do
        throw <| IO.userError "root capture changed during worklist"
      save p out false none
    catch error =>
      let msg := error.toString
      IO.eprintln s!"STOP {msg}"
      save p out false (some msg)
      stopped := true
  unless stopped do save p out true none
  IO.println s!"Module product: {p.modules.size} captures, {p.bodies.size} bodies, {p.externals.size} boundaries/pending"

end RendererModuleProduct

def main (args : List String) : IO Unit := do
  let [source, setup, resolver, out] := args |
    throw <| IO.userError "usage: ModuleProduct.lean root.lean root.setup.json resolver.mjs output"
  RendererModuleProduct.run source setup resolver out
