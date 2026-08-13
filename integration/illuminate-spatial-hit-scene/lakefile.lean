import Lake

open Lake DSL

package «IlluminateFirSpatialHitScene»

require Fir from "../.."

/-- Path to the read-only Illuminate source view. -/
def illuminateRoot : String :=
  get_config? illuminateRoot |>.getD ".illuminate"

/-- Expose Illuminate modules while Lake builds only the imported dependency cone. -/
lean_lib «IlluminateSpatialHitSceneSource» where
  srcDir := System.FilePath.mk illuminateRoot / "src"
  globs := #[.submodules `Illuminate]

@[default_target]
lean_lib «IlluminateFirSpatialHitScene»
