import Lake

open Lake DSL

package «IlluminateFirNative»

require Fir from "../.."

/--
Path to the real Illuminate checkout. Build scripts pass an absolute
`-KilluminateRoot=...`; `.illuminate` is an ignored local source link used by
editor and Lean Beam sessions that cannot inject Lake configuration flags.
-/
def illuminateRoot : String :=
  get_config? illuminateRoot |>.getD ".illuminate"

def illuminateSrc : System.FilePath :=
  System.FilePath.mk illuminateRoot / "src"

/--
Read-only source view of the exact Illuminate player modules. Build products
belong to this integration project, never to Illuminate's 4.33 `.lake`.
-/
lean_lib «IlluminatePlayerSource» where
  srcDir := illuminateSrc
  roots := #[`Illuminate.Animation.Types, `Illuminate.Animation.Player]

@[default_target]
lean_lib «IlluminateFirNative»
