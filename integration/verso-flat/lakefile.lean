import Lake

open Lake DSL

package «VersoFirFlat»

require Fir from "../.."

/--
Path to the clean Verso source checkout. Build products remain in this
integration project; FIR never consumes the source checkout's `.lake`.
-/
def versoRoot : String :=
  get_config? versoRoot |>.getD ".verso"

lean_lib «VersoFlatSource» where
  srcDir := System.FilePath.mk versoRoot
  roots := #[`VersoSlides.Pretty]

@[default_target]
lean_lib «VersoFirFlat»
