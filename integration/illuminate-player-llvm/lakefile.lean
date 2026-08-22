import Lake

open Lake DSL

package «IlluminateLlvmSelection»

/--
Path to the read-only Illuminate checkout used by Lean Beam and native checks.
The deterministic Emscripten build extracts the pinned revision into `.deps`
instead of consuming this editor convenience link.
-/
def illuminateRoot : String :=
  get_config? illuminateRoot |>.getD ".illuminate"

def illuminateSrc : System.FilePath :=
  System.FilePath.mk illuminateRoot / "src"

lean_lib «IlluminateSelectionSource» where
  srcDir := illuminateSrc
  roots := #[
    `Illuminate.Animation.Types,
    `Illuminate.Animation.Player,
    `Illuminate.Animation.FirLive,
    `Illuminate.Animation.FirSelection]

@[default_target]
lean_lib «IlluminateLlvmSelection»

lean_exe «wireTests» where
  root := `WireTests
