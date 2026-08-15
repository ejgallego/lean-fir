import Fir.Wasm.Emit.Examples

open Fir.Wasm

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | [path] => pure (System.FilePath.mk path)
    | _ => do
        IO.eprintln "usage: fir-wasm-scalar-surface <output.wasm>"
        return 2
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let bytes ← IO.ofExcept <|
    Fir.Wasm.Emit.encode Fir.Wasm.Emit.Examples.scalarSurfaceModule |>.mapError
      fun error => s!"failed to encode scalar surface: {repr error}"
  IO.FS.writeBinFile path bytes
  IO.println s!"wrote {bytes.size} bytes and 163 scalar exports to {path}"
  return 0
