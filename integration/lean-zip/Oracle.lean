import Zip.Wasm.Stored
import Zip.Wasm.Level1
import Zip.Wasm.Entry

private def usage : String :=
  "usage: leanZipFirOracle (stored|level1) <input> <output> | raw <level> <input> <output>"

private def parseLevel (text : String) : IO UInt8 := do
  let some level := text.toNat?
    | throw (IO.userError s!"invalid compression level `{text}`")
  unless 1 ≤ level && level ≤ 10 do
    throw (IO.userError s!"compression level must be in 1..10, got {level}")
  return level.toUInt8

def main (args : List String) : IO Unit := do
  match args with
  | ["stored", inputPath, outputPath] =>
      let input ← IO.FS.readBinFile inputPath
      IO.FS.writeBinFile outputPath (Zip.Wasm.compressStored input)
  | ["level1", inputPath, outputPath] =>
      let input ← IO.FS.readBinFile inputPath
      IO.FS.writeBinFile outputPath (Zip.Wasm.compressLevel1 input)
  | ["raw", levelText, inputPath, outputPath] =>
      let level ← parseLevel levelText
      let input ← IO.FS.readBinFile inputPath
      IO.FS.writeBinFile outputPath (Zip.Wasm.compressRaw input level)
  | _ => throw (IO.userError usage)
