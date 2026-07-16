import Fir.Wasm.Emit.Source
import Lean.Elab.Command

namespace Fir.Wasm.Emit.Source

open Lean Elab Command

syntax (name := firWasmEmit) "#fir_wasm_emit " ident " to " str : command

@[command_elab firWasmEmit]
def elabFirWasmEmit : CommandElab
  | stx@`(#fir_wasm_emit $entry:ident to $output:str) => do
      let entryName ← resolveGlobalConstNoOverload entry
      let some outputPath := output.raw.isStrLit? |
        throwErrorAt output "expected an output path"
      let result ← liftCoreM <| compileClosed entryName
      let artifact ← match result with
        | .ok artifact => pure artifact
        | .error error => throwErrorAt entry "failed to emit {entryName}: {repr error}"
      artifact.write outputPath
      logInfoAt stx s!"wrote {artifact.bytes.size} bytes to {outputPath}"
  | _ => throwUnsupportedSyntax

end Fir.Wasm.Emit.Source
