import Zip.Wasm.Stored
import Zip.Wasm.Level1

private def usage : String :=
  "usage: leanZipFirOracle (stored|level1) <input> <output>"

def main (args : List String) : IO Unit := do
  match args with
  | ["stored", inputPath, outputPath] =>
      let input ← IO.FS.readBinFile inputPath
      IO.FS.writeBinFile outputPath (Zip.Wasm.compressStored input)
  | ["level1", inputPath, outputPath] =>
      let input ← IO.FS.readBinFile inputPath
      IO.FS.writeBinFile outputPath (Zip.Wasm.compressLevel1 input)
  | _ => throw (IO.userError usage)
