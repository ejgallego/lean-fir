import Lake

open Lake DSL

package «VersoFirHtml»

require Fir from "../.."

/--
Path to the clean Verso source checkout. Build products remain in this
integration project; FIR never consumes the source checkout's `.lake`.
-/
def versoRoot : String :=
  get_config? versoRoot |>.getD ".verso"

/-- Preserve Lean's ordinary module compilation boundary for final-LCNF replay. -/
lean_lib «VersoHtmlSource» where
  srcDir := System.FilePath.mk versoRoot
  roots := #[`VersoSlides.Pretty]

@[default_target]
lean_lib «VersoFirHtml»
