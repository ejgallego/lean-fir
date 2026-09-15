import Fir.Wasm.Emit.ModuleSource

open Lean Lean.Compiler.LCNF Fir.Wasm.Emit.ModuleSource

namespace ProductTransport

def entry := `Verso.Genre.Manual.instToJsonInline.toJson

/-- Experiment-local data type, not a durable compiler-product format. No
environment, function closure, external handle or borrowed compacted region. -/
structure Product where
  moduleName : Name
  entry : Name
  identity : String
  groups : Array (Array (Decl .impure))
  selected : Array (Decl .impure)
  externalNames : Array Name
  owners : Array (Name × Name)
  deriving BEq

def manualImages : IO (Array String) := do
  let maps ← IO.FS.readFile "/proc/self/maps"
  let paths := (maps.splitOn "\n").foldl (init := #[]) fun found line =>
    match (line.splitOn " ").getLast? with
    | some path =>
      if path.endsWith ".so" && (path.splitOn "VersoManual").length > 1 && !found.contains path then
        found.push path
      else found
    | none => found
  return paths.qsort (· < ·)

def owner (c : CapturedModule) (name : Name) : IO Name := do
  if let some idx := c.environment.getModuleIdxFor? name then
    return c.environment.header.moduleNames[idx.toNat]!
  if c.groups.any (·.any (·.name == name)) then return c.moduleName
  throw <| IO.userError s!"unknown owner {name}"

def capture (source setupFile : System.FilePath) : IO CapturedModule := do
  unsafe enableInitializersExecution
  let setup ← ModuleSetup.load setupFile
  match ← compile source setup with
  | .ok c => return c
  | .error messages =>
    let rendered ← messages.toList.mapM (·.toString)
    throw <| IO.userError (String.intercalate "\n" rendered)

def exportProduct (source setup identityFile out : System.FilePath) : IO Unit := do
  let c ← capture source setup
  unless c.moduleName == `VersoManual.Basic do throw <| IO.userError "unexpected producer owner"
  let a ← c.artifact entry
  let identity ← IO.FS.readFile identityFile
  let owners ← a.program.decls.mapM fun d => return (d.name, ← owner c d.name)
  let p : Product := {
    moduleName := c.moduleName
    entry
    identity
    groups := c.groups
    selected := a.program.decls
    externalNames := a.externalNames
    owners }
  -- Upstream v2 object compaction; no executable closure support and no
  -- cross-file dependency regions. Keep every source/loaded region live.
  let _ ← unsafe CompactedRegion.save out `firBasicTransport p #[] none (allowClosures := false)
  let (q, _region) ← unsafe CompactedRegion.read (α := Product) out #[]
  unless p == q do throw <| IO.userError "local full-data roundtrip differs"
  IO.FS.writeFile (out.addExtension "json") <| (Json.mkObj [
    ("module", toJson p.moduleName.toString), ("entry", toJson entry.toString),
    ("groups", toJson p.groups.size), ("recordedDeclarations", toJson p.groups.flatten.size),
    ("selected", toJson (p.selected.map (·.name.toString))),
    ("externals", toJson (p.externalNames.map (·.toString))),
    ("owners", toJson (p.owners.map fun (n, o) => (n.toString, o.toString))),
    ("roundTripEqual", toJson true), ("allowClosures", toJson false),
    ("manualImages", toJson (← manualImages))]).pretty ++ "\n"

def signatureMatches (a b : Signature .impure) : Bool :=
  a.name == b.name && a.type == b.type && a.safe == b.safe && a.levelParams == b.levelParams &&
    a.params.map (fun p => (p.type, p.borrow)) == b.params.map (fun p => (p.type, p.borrow))

def verify (root : CapturedModule) (p : Product) (identity : String) : IO (Array Name) := do
  unless p.moduleName == `VersoManual.Basic && p.entry == entry && p.identity == identity do
    throw <| IO.userError "product identity mismatch"
  let mut names : Array Name := #[]
  for d in p.groups.flatten do
    if names.contains d.name then throw <| IO.userError "duplicate recorded declaration"
    names := names.push d.name
  names := #[]
  let mut internalOnly := #[]
  let externalDecls := p.selected.filter fun d => match d.value with | .extern _ => true | _ => false
  unless externalDecls.size == p.externalNames.size &&
      externalDecls.all (fun d => p.externalNames.contains d.name) do
    throw <| IO.userError "external inventory mismatch"
  unless p.owners.size == p.selected.size do throw <| IO.userError "owner inventory size mismatch"
  for d in p.selected do
    if names.contains d.name then throw <| IO.userError "duplicate selected declaration"
    names := names.push d.name
    let rows := p.owners.filter (·.1 == d.name)
    unless rows.size == 1 do throw <| IO.userError "ambiguous selected owner"
    unless rows[0]!.2 == (← owner root d.name) do
      throw <| IO.userError s!"renderer/product owner mismatch: {d.name}"
    let imported ← (getImpureSignature? d.name).toIO'
      { fileName := root.sourceFile.toString, fileMap := default, options := root.options }
      { env := root.environment }
    if let some imported := imported then
      unless signatureMatches imported d.toSignature do
        throw <| IO.userError s!"renderer/product signature mismatch: {d.name}"
    else
      -- Imported interfaces must exist. Private implementation declarations
      -- instead have their entire declaration checked against the owning
      -- capture below; they are not inferred from an absent signature.
      if d.name == entry || p.externalNames.contains d.name ||
          isDeclPublic root.environment d.name then
        throw <| IO.userError s!"no renderer-context interface signature: {d.name}"
      internalOnly := internalOnly.push d.name
    if p.externalNames.contains d.name then
      unless (match d.value with | .extern _ => true | _ => false) do
        throw <| IO.userError "external has body"
    else
      unless rows[0]!.2 == p.moduleName do throw <| IO.userError "local owner mismatch"
      let some canonical := p.groups.flatten.find? (·.name == d.name) |
        throw <| IO.userError "selected body missing from recorded groups"
      unless canonical == d do throw <| IO.userError s!"selected full declaration differs: {d.name}"
  unless names.contains entry && !p.externalNames.contains entry do
    throw <| IO.userError "selected entry missing or external"
  return internalOnly

def mustReject (label : String) (act : IO Unit) : IO Unit := do
  let rejected ← try act; pure false catch _ => pure true
  unless rejected do throw <| IO.userError s!"negative control accepted: {label}"

def importProduct (rootSource rootSetup identityFile first second out : System.FilePath) : IO Unit := do
  let root ← capture rootSource rootSetup
  let before ← manualImages
  let identity ← IO.FS.readFile identityFile
  -- The launcher verifies immutable producer/schema/toolchain/input identities
  -- and both blob digests before entering this trusted, type-erased upstream API.
  let (p, _regionP) ← unsafe CompactedRegion.read (α := Product) first #[]
  let (q, _regionQ) ← unsafe CompactedRegion.read (α := Product) second #[]
  unless p == q do throw <| IO.userError "independent products differ structurally"
  let internalOnly ← verify root p identity
  mustReject "identity" (discard <| verify root { p with identity := p.identity ++ "corrupt" } identity)
  mustReject "owner" (discard <| verify root { p with owners := p.owners.modify 0 fun (n, _) => (n, `WrongOwner) } identity)
  let some parameterized := p.selected.find? (fun d => !d.params.isEmpty) |
    throw <| IO.userError "no parameter for signature negative control"
  mustReject "signature" (discard <| verify root { p with selected := p.selected.map fun d =>
    if d.name == parameterized.name then { d with params := d.params.modify 0 fun param =>
      { param with borrow := !param.borrow } } else d } identity)
  let some internalName := internalOnly[0]? |
    throw <| IO.userError "no private definition for full-body negative control"
  mustReject "private body" (discard <| verify root { p with selected := p.selected.map fun d =>
    if d.name == internalName then { d with value := .code (.unreach d.type) } else d } identity)
  mustReject "external inventory" (discard <| verify root { p with externalNames := #[] } identity)
  mustReject "duplicate declaration" (discard <| verify root { p with
    selected := p.selected ++ p.selected } identity)
  let after ← manualImages
  unless before == after do throw <| IO.userError "transport changed manual native images"
  IO.FS.writeFile out <| (Json.mkObj [
    ("accepted", toJson true), ("structuralEquality", toJson true),
    ("signatureOwnerChecks", toJson true), ("negativeControls", toJson true),
    ("groups", toJson p.groups.size), ("selected", toJson p.selected.size),
    ("externalSignatures", toJson p.externalNames.size),
    ("internalOnlySignatures", toJson (internalOnly.map (·.toString))),
    ("imagesBefore", toJson before), ("imagesAfter", toJson after),
    ("worklistResumed", toJson false)]).pretty ++ "\n"

end ProductTransport

def main (args : List String) : IO Unit := do
  match args with
  | ["export", source, setup, identity, out] =>
    ProductTransport.exportProduct source setup identity out
  | ["import", source, setup, identity, first, second, out] =>
    ProductTransport.importProduct source setup identity first second out
  | _ => throw <| IO.userError "usage: ProductTransport.lean export/import source setup identity ..."
