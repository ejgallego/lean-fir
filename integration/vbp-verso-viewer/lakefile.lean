import Lake

open Lake DSL

package «FirVbpVersoViewer»

require Fir from "../../.deps/source-views/fir-vbp-verso-viewer"

require lean_vir from "../../.deps/source-views/vir-generic-90aa3f49"

require verso from git
  "https://github.com/leanprover/verso" @
    "99e9df791e46ec647f81d98b109965f166b9b6b4"

def vbpRoot : String :=
  get_config? vbpRoot |>.getD
    "../../.deps/source-views/vbp-widget-cad90a2f"

/-- Compile the exact VBP widget source with postponed final LCNF. -/
lean_lib «VbpVersoViewerSource» where
  srcDir := System.FilePath.mk vbpRoot / "src"
  roots := #[
    `VersoBlueprintVir.Preview.Model,
    `VersoBlueprintVir.Preview.Renderer,
    `VersoBlueprintVir.Preview.Component.Style,
    `VersoBlueprintVir.Preview.Component.Session,
    `VersoBlueprintVir.Preview.Component.Content,
    `VersoBlueprintVir.Preview.Component,
    `VersoBlueprintVir.Preview.Widget]
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]

@[default_target]
lean_lib «FirVbpVersoViewer»
