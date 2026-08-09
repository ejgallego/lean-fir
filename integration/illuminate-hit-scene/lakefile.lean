import Lake

open Lake DSL

package «IlluminateFirHitScene»

require Fir from "../.."

/--
Path to the clean Illuminate source checkout. Build products remain in this
integration project; FIR never consumes the source checkout's `.lake`.
-/
def illuminateRoot : String :=
  get_config? illuminateRoot |>.getD ".illuminate"

lean_lib «IlluminateHitSceneSource» where
  srcDir := System.FilePath.mk illuminateRoot / "src"
  globs := #[.submodules `Illuminate]
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]

@[default_target]
lean_lib «IlluminateFirHitScene»
