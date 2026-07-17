import Fir.Wasm.Emit.Source
import Lean.Elab.Command

namespace Fir.Wasm.Emit.Source

open Lean Elab Command

syntax (name := firWasmEmit) "#fir_wasm_emit " ident " to " str : command
declare_syntax_cat firWasmArg
syntax "erased" : firWasmArg
syntax "tagged" "(" num ")" : firWasmArg
syntax "uint8" "(" num ")" : firWasmArg
syntax "uint16" "(" num ")" : firWasmArg
syntax "uint32" "(" num ")" : firWasmArg
syntax "uint64" "(" num ")" : firWasmArg
syntax "usize" "(" num ")" : firWasmArg
syntax "string" "(" str ")" : firWasmArg
syntax (name := firWasmEmitWith)
  "#fir_wasm_emit " ident " with " "[" firWasmArg,* "]" " to " str : command

private def checkedNat (kind : String) (literal : TSyntax `num) (max : Nat) :
    CommandElabM Nat := do
  let some value := literal.raw.isNatLit? |
    throwErrorAt literal "expected a natural-number literal"
  unless value ≤ max do
    throwErrorAt literal "{kind} argument exceeds {max}"
  return value

private def elabArgument (runtime : Fir.LeanIR.Impure.RuntimeState) :
    TSyntax `firWasmArg →
      CommandElabM (Fir.LeanIR.Impure.RuntimeState × Fir.LeanIR.Impure.Value)
  | `(firWasmArg| erased) => pure (runtime, .erased)
  | `(firWasmArg| tagged($value:num)) => do
      pure (runtime, .object (.tagged (UInt64.ofNat
        (← checkedNat "tagged" value 18446744073709551615))))
  | `(firWasmArg| uint8($value:num)) => do
      pure (runtime, .scalar (.uint8 (UInt8.ofNat (← checkedNat "uint8" value 255))))
  | `(firWasmArg| uint16($value:num)) => do
      pure (runtime, .scalar (.uint16 (UInt16.ofNat (← checkedNat "uint16" value 65535))))
  | `(firWasmArg| uint32($value:num)) => do
      pure (runtime, .scalar (.uint32 (UInt32.ofNat
        (← checkedNat "uint32" value 4294967295))))
  | `(firWasmArg| uint64($value:num)) => do
      pure (runtime, .scalar (.uint64 (UInt64.ofNat
        (← checkedNat "uint64" value 18446744073709551615))))
  | `(firWasmArg| usize($value:num)) => do
      pure (runtime, .usize (UInt64.ofNat
        (← checkedNat "usize" value 18446744073709551615)))
  | `(firWasmArg| string($value:str)) => do
      let some value := value.raw.isStrLit? |
        throwErrorAt value "expected a string literal"
      let (runtime, reference) := Fir.LeanIR.Impure.alloc runtime (.string value)
      pure (runtime, .object reference)
  | stx => throwErrorAt stx "unsupported Wasm semantic argument"

private def writeArtifact (stx entry output : Syntax)
    (runtime : Fir.LeanIR.Impure.RuntimeState)
    (args : Array Fir.LeanIR.Impure.Value) : CommandElabM Unit := do
  let entryName ← resolveGlobalConstNoOverload entry
  let some outputPath := output.isStrLit? |
    throwErrorAt output "expected an output path"
  let result ← liftCoreM <|
    if runtime.heap.isEmpty then compile entryName args
    else compileWithRuntime entryName runtime args
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwErrorAt entry "failed to emit {entryName}: {repr error}"
  artifact.write outputPath
  logInfoAt stx s!"wrote {artifact.bytes.size} bytes to {outputPath}"

@[command_elab firWasmEmit]
def elabFirWasmEmit : CommandElab
  | stx@`(#fir_wasm_emit $entry:ident to $output:str) => do
      writeArtifact stx entry output {} #[]
  | _ => throwUnsupportedSyntax

@[command_elab firWasmEmitWith]
def elabFirWasmEmitWith : CommandElab
  | stx@`(#fir_wasm_emit $entry:ident with [$[$args],*] to $output:str) => do
      let (runtime, args) ← args.foldlM (init := ({}, #[]))
        fun (runtime, values) argument => do
          let (runtime, value) ← elabArgument runtime argument
          return (runtime, values.push value)
      writeArtifact stx entry output runtime args
  | _ => throwUnsupportedSyntax

end Fir.Wasm.Emit.Source
