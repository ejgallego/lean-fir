import VersoManual
import VersoBlueprint.PreviewManifest
import FirBlueprint.Blueprint
import FirBlueprint.SourceLinks

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 := do
  let model : Informal.RenderModel := by exact blueprint_render_model%
  let sources ← FirBlueprint.SourceLinks.capture model
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc FirBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (model := model)
    (extraSteps := [sources.emit])
