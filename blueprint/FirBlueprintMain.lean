import VersoManual
import VersoBlueprint.PreviewManifest
import FirBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc FirBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
