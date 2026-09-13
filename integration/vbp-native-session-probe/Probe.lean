import Fir.Wasm.Emit.ResidentLinker
import VersoBlueprintVir.Preview.Renderer
import Vir.HostMetadata

open Lean

namespace NativeSessionProbe

def entries : Array Name := #[`VersoBlueprint.Experimental.VirPreview.Renderer.render]

/-- Use VIR's actual extern metadata, not a historical consumer import list. -/
def hostTarget? (env : Environment) (name : Name) : Option String := do
  let data ← getExternAttrData? env name
  data.entries.findSome? fun entry => match entry with
    | .standard _ symbol => (Vir.HostMetadata.decodeExternSymbol? symbol).map (·.target)
    | _ => none

def capture : CoreM (Fir.Compiler.Lcnf.Artifact × Array Name) := do
  let env ← getEnv
  let candidates := env.constants.toList.toArray.filterMap fun (name, _) =>
    if (hostTarget? env name).isSome then some name else none
  let retained := candidates.flatMap fun name =>
    #[name.toString, (name.str "_boxed").toString]
  let retained := retained ++
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames
  let captured ← Fir.Wasm.Emit.Source.compileEntriesIndividuallyInternalized entries retained
  let captured ← Fir.Wasm.Emit.Source.internalizeExternalBoxedAdapters captured candidates
  let captured ← Fir.Wasm.Emit.Source.internalizeFinalDependencies captured
    (candidates.map Name.toString ++
      Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames)
    (entries.extract 1 entries.size)
  let hosts := captured.externalNames.filter fun name => (hostTarget? env name).isSome
  return (captured, hosts)

def link (base : Fir.Wasm.Emit.Source.ModuleArtifact) (hosts : Array Name) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  Fir.Wasm.Emit.ResidentLinker.linkArtifact {
    Fir.Wasm.Emit.ResidentLinker.closedApplicationAvailablePolicy base.module entries with
    allowedExternalImports := some hosts
    requireZeroImports := false } base

end NativeSessionProbe
