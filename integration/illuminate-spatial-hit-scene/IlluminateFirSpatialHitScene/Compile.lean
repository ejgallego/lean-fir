import Fir.Wasm.Emit.ResidentLinker
import Illuminate.Diagram.HitScene.Spatial

namespace IlluminateFirSpatialHitScene

/-- Borrowed persistent-host boundary implemented in the package root module. -/
def queryBorrowed (scene : @& Illuminate.SpatialHitScene)
    (x y : Float) : Illuminate.HitSceneResult :=
  Illuminate.SpatialHitScene.query scene x y

end IlluminateFirSpatialHitScene

namespace IlluminateFirSpatialHitScene.Compile

open Lean

/-- Builds the guarded scene once inside compiled Lean. -/
def prepareEntry : Name := ``Illuminate.SpatialHitScene.ofHitScene

/-- Queries one retained guarded scene through Lean's borrowed ABI. -/
def queryEntry : Name := ``IlluminateFirSpatialHitScene.queryBorrowed

/-- The real Illuminate declarations compiled into one final-LCNF closure. -/
def entries : Array Name := #[prepareEntry, queryEntry]

/--
The raw Float query stays internal. JavaScript calls its generated integer-lane
facade so binary64 payload bits cross the boundary unchanged.
-/
def sourcePublicExports : Array Name := #[
  prepareEntry,
  Fir.Wasm.Emit.BitExactFloat.facadeName queryEntry]

/-- Capture the two real spatial declarations without an application-specific facade. -/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact :=
  Fir.Wasm.Emit.Source.compileEntriesFinalCapturedInternalized entries
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/-- Lower the unmodified final-LCNF closure before resident runtime linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  let result ← Fir.Wasm.Emit.Source.compileModuleArtifactWithExports source entries .ok
  return result.bind Fir.Wasm.Emit.ResidentLinker.prepareArenaArtifact

/-- Public structured entries plus the module-owned arena operations. -/
def publicExports : Array Name :=
  sourcePublicExports ++ Fir.Wasm.Emit.ResidentLinker.allocatorExports

/-- Link every accepted resident family and retain the exact browser surface. -/
def residentFrontierPolicy : Fir.Wasm.Emit.ResidentLinker.Policy := {
  Fir.Wasm.Emit.ResidentLinker.closedApplicationFrontierPolicy sourcePublicExports with
  publicExports := some publicExports }

/-- Close the reusable resident frontier while leaving only native math externals. -/
def linkResidentFrontier
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  Fir.Wasm.Emit.ResidentLinker.linkArtifact residentFrontierPolicy artifact

end IlluminateFirSpatialHitScene.Compile
