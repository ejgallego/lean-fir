import Fir.Validation.Corpus
import Fir.Wasm.Emit.Source
import Lean.Elab.Command

namespace Fir.Wasm.Emit.SourceExamples

open Lean Elab Command
open Fir.Wasm.Emit.Source

run_cmd do
  let result ← liftCoreM <|
    compileClosed ``Fir.Validation.Corpus.Source.litNat
  match result with
  | .error (.lowering (.validation (.unsupportedCode name))) =>
      unless name == ``Fir.Validation.Corpus.Source.litNat do
        throwError "unexpected unsupported declaration: {name}"
  | .error error => throwError "unexpected source literal failure: {repr error}"
  | .ok _ => throwError "remove FIR-BUG-wasm-none-compiler-nat-literal-kind"

run_cmd do
  let result ← liftCoreM <|
    compileClosed ``Fir.Validation.Corpus.Source.maxUInt64
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "source UInt64 literal did not compile: {repr error}"
  unless artifact.source.externalNames.isEmpty do
    throwError "source UInt64 literal unexpectedly retained externals"
  unless artifact.module.exports == #[``Fir.Validation.Corpus.Source.maxUInt64] do
    throwError "source UInt64 literal export mismatch: {repr artifact.module.exports}"
  unless artifact.bytes.size > Fir.Wasm.Emit.header.size do
    throwError "source UInt64 literal did not produce a complete Wasm module"

end Fir.Wasm.Emit.SourceExamples
