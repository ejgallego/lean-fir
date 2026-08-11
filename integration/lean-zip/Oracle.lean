import Zip.Wasm.Stored

private def usage : String :=
  "usage: leanZipFirOracle stored <input> <output>"

def main (args : List String) : IO Unit := do
  match args with
  | ["stored", inputPath, outputPath] =>
      let input ← IO.FS.readBinFile inputPath
      IO.FS.writeBinFile outputPath (Zip.Wasm.compressStored input)
  | _ => throw (IO.userError usage)
