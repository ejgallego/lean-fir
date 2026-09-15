import Fir.Compiler.LCNF
import Fir.Wasm.Validate
import Lean.Compiler.ExportAttr

/-!
Native-symbol links between compiler products. Externs are not Lean fallback
bodies: a source provider must advertise the exact symbol through upstream's
export metadata. Capture stays module-owned; linking adds explicit ABI-exact
forwarders without changing captured LCNF or closure target identities.
-/
namespace Fir.Wasm.Emit.NativeSymbol

open Lean Lean.Compiler.LCNF

abbrev ExportIndex := Array (String × Name)

def exportIndex (env : Environment) : ExportIndex :=
  (env.constants.toList.toArray.filterMap fun (name, _) =>
    (getExportNameFor? env name).map fun symbol => (symbol.toString, name)).qsort
      (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.toString < b.2.toString))

def sameInterface (a b : Lean.Compiler.LCNF.Signature .impure) : Bool :=
  a.type == b.type && a.safe == b.safe && a.levelParams == b.levelParams &&
    a.params.map (fun p => (p.type, p.borrow)) == b.params.map (fun p => (p.type, p.borrow))

structure Provider where
  declaration : Name
  symbol : String
  name : Name
  owner : Name
  signature : Lean.Compiler.LCNF.Signature .impure

def uniqueProvider (exports : ExportIndex) (symbol : String) : Except String (Option Name) :=
  match (exports.filter (·.1 == symbol)).toList with
  | [] => .ok none
  | [(_, name)] => .ok (some name)
  | _ => .error s!"ambiguous Lean export for native symbol {symbol}"

/-- Use the same C-backend extern entry selection as upstream EmitC. Opaque,
inline and backend-inapplicable entries are not guessed into named links. -/
def resolve (exports : ExportIndex) (decl : Decl .impure) : CoreM (Option Provider) := do
  let env ← getEnv
  let .extern data := decl.value | return none
  let some (.standard _ symbol) := getExternEntryFor data `c | return none
  unless getExternNameFor env `c decl.name == some symbol do
    throwError "captured extern metadata changed: {decl.name}"
  let some name ← ofExcept (uniqueProvider exports symbol) | return none
  unless name != decl.name do throwError "native symbol self-alias: {name}"
  -- EmitC accepts only a single, unmangled export identifier.
  unless getExportNameFor? env name == some (.str .anonymous symbol) do
    throwError "native export metadata changed: {name} / {symbol}"
  if (getExternAttrData? env name).isSome then
    throwError "native export provider is itself external: {name}"
  -- Module imports may hide a definition's body behind an axiom-like view.
  -- Imported compiled metadata selects the owner; checkBody subsequently
  -- requires actual code from that owner's ordinary final-LCNF capture.
  let some signature ← getImpureSignature? name |
    throwError "native export has no final-LCNF signature: {name}"
  unless sameInterface decl.toSignature signature do
    throwError "native export interface mismatch: {decl.name} -> {name}"
  let owner := match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  return some { declaration := decl.name, symbol, name, owner, signature }

/-- Recheck the actual owning compiler product, not just imported metadata. -/
def checkBody (p : Provider) (owner : Name) (body : Decl .impure) : Except String Unit := do
  unless owner == p.owner && body.name == p.name do
    throw s!"native export owner/name mismatch: {p.name}"
  unless sameInterface p.signature body.toSignature do
    throw s!"native export captured interface mismatch: {p.name}"
  unless (match body.value with | .code _ => true | _ => false) do
    throw s!"native export lacks captured code: {p.name}"

/-- One adapter preserves the external declaration identity for ordinary calls,
closure dispatch and exports. No instruction-pattern rewriting is needed. -/
def link (providers : Array Provider) (module : Fir.Wasm.Module) :
    Except String Fir.Wasm.Module := do
  let mut seen : Array Name := #[]
  let mut adapters := #[]
  for p in providers do
    if seen.contains p.declaration then throw s!"duplicate native link: {p.declaration}"
    seen := seen.push p.declaration
    if providers.any (·.declaration == p.name) then
      throw s!"native link provider is an alias rather than a body: {p.name}"
    let some imported := module.imports.find? (·.declaration? == some p.declaration) |
      throw s!"native link import missing: {p.declaration}"
    if module.functions.any (·.name == p.declaration) then
      throw s!"native link name already defined: {p.declaration}"
    let some body := module.functions.find? (·.name == p.name) |
      throw s!"native link function missing: {p.name}"
    unless imported.signature.params == body.params.map (·.2) &&
        imported.signature.results == body.results do
      throw s!"native link Wasm signature mismatch: {p.declaration} -> {p.name}"
    let params := imported.signature.params.mapIdx fun i kind =>
      (⟨Name.mkSimple s!"native_arg_{i}"⟩, kind)
    adapters := adapters.push {
      name := p.declaration, params, results := imported.signature.results, locals := #[],
      body := params.toList.map (fun (id, _) => .localGet id) ++
        [.call (.declaration p.name), .ret] : Fir.Wasm.Function }
  let linked := { module with
    imports := module.imports.filter (fun i => !(i.declaration?.any seen.contains))
    functions := module.functions ++ adapters }
  match Fir.Wasm.validateModule linked with
  | .ok () => pure linked
  | .error error => throw s!"invalid native-symbol link: {repr error}"

#guard (uniqueProvider #[] "missing").toOption == some none
#guard (uniqueProvider #[("x", `provider)] "x").toOption == some (some `provider)
#guard (uniqueProvider #[("x", `a), ("x", `b)] "x").toOption.isNone
#guard (uniqueProvider #[("other", `provider)] "x").toOption == some none

private def testProvider : Provider := {
  declaration := `externalTest, symbol := "test_symbol", name := `providerTest,
  owner := `TestModule,
  signature := {
    name := `providerTest, levelParams := [], params := #[],
    type := mkConst ``UInt32, safe := true } }

private def testModule : Fir.Wasm.Module := {
  imports := #[{
    key := .external `externalTest, moduleName := "lean.extern",
    itemName := "externalTest", signature := { params := #[], results := #[.uint32] } }],
  functions := #[{
    name := `providerTest, params := #[], results := #[.uint32],
    locals := #[], body := [.i32Const .uint32 42, .ret] }],
  exports := #[`externalTest], initializers := #[], runtimeOperations := #[] }

#guard (link #[testProvider] testModule).toOption.any fun linked =>
  linked.imports.isEmpty && linked.functions.size == 2 &&
    linked.functions[0]! == testModule.functions[0]! &&
    linked.functions[1]!.body == [.call (.declaration `providerTest), .ret] &&
    linked.exports == testModule.exports
#guard (link #[testProvider, testProvider] testModule).toOption.isNone
#guard (link #[testProvider] { testModule with functions := #[] }).toOption.isNone
#guard (link #[testProvider] { testModule with imports := #[] }).toOption.isNone
#guard (link #[testProvider] { testModule with
  functions := testModule.functions.map fun f => { f with results := #[.uint64] } }).toOption.isNone
#guard (link #[{ testProvider with name := testProvider.declaration }] testModule).toOption.isNone

end Fir.Wasm.Emit.NativeSymbol
