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

run_cmd do
  let result ← liftCoreM <|
    compileModule ``Fir.Validation.Corpus.Source.idUSize
  let moduleArtifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "parameterized source did not compile: {repr error}"
  let artifact ← match moduleArtifact.withInvocation
      "id-usize-42" ``Fir.Validation.Corpus.Source.idUSize
      ``Fir.Validation.Corpus.Source.idUSize #[.usize 42] with
    | .ok artifact => pure artifact
    | .error error => throwError "parameterized invocation was rejected: {repr error}"
  let function ← match Fir.Wasm.Emit.Manifest.entryFunction artifact.module
      ``Fir.Validation.Corpus.Source.idUSize with
    | .ok function => pure function
    | .error error => throwError "parameterized source export failure: {error}"
  unless function.params.map (·.snd) == #[.usize] do
    throwError "parameterized source schema mismatch: {repr function.params}"
  unless artifact.manifest.compress.contains
      "\"arguments\":[{\"kind\":\"usize\",\"value\":\"42\"}]" do
    throwError "parameterized source manifest did not retain the invocation"
  let secondArtifact ← match moduleArtifact.withInvocation
      "id-usize-7" ``Fir.Validation.Corpus.Source.idUSize
      ``Fir.Validation.Corpus.Source.idUSize #[.usize 7] with
    | .ok artifact => pure artifact
    | .error error => throwError "second parameterized invocation was rejected: {repr error}"
  unless artifact.bytes == secondArtifact.bytes &&
      artifact.formattedLcnf == secondArtifact.formattedLcnf do
    throwError "invocation data changed the reusable source artifact"
  if artifact.manifest.compress == secondArtifact.manifest.compress then
    throwError "distinct parameterized invocations produced the same manifest"
  match moduleArtifact.withInvocation
      "id-usize-wrong-kind" ``Fir.Validation.Corpus.Source.idUSize
      ``Fir.Validation.Corpus.Source.idUSize #[.scalar (.uint64 42)] with
  | .error (.manifest message) =>
      unless message.contains "does not match ABI kind" do
        throwError "unexpected argument-schema rejection: {message}"
  | .error error => throwError "unexpected parameterized source failure: {repr error}"
  | .ok _ => throwError "parameterized source accepted the wrong semantic argument kind"
  match moduleArtifact.withValidationInvocation
      "id-usize-wrong-result" ``Fir.Validation.Corpus.Source.idUSize
      ``Fir.Validation.Corpus.Source.idUSize #[.usize] #[.usize 42] (.bits 64) with
  | .error (.manifest message) =>
      unless message.contains "result schema" do
        throwError "unexpected result-schema rejection: {message}"
  | .error error => throwError "unexpected validation invocation failure: {repr error}"
  | .ok _ => throwError "validation invocation accepted the wrong result schema"

end Fir.Wasm.Emit.SourceExamples
