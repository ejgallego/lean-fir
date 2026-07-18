import Fir.Validation.Corpus
import Fir.Wasm.Emit.Source
import Lean.Elab.Command

namespace Fir.Wasm.Emit.SourceExamples

open Lean Elab Command
open Fir.Wasm.Emit.Source

run_cmd do
  unless validationSchemaAcceptsAbiKind .bool .uint8 do
    throwError "validation Bool schema rejected Lean's scalar result ABI"
  unless validationSchemaAcceptsAbiKind .bool .tagged do
    throwError "validation Bool schema rejected its tagged object ABI"
  if validationSchemaAcceptsAbiKind .bool .uint16 then
    throwError "validation Bool schema accepted an unrelated scalar ABI"
  match validationArgumentForAbi .bool .uint8 (.object (.tagged 1)) with
  | .ok (.scalar (.uint8 value)) =>
      unless value == 1 do
        throwError "validation Bool argument normalized to {value}, expected one"
  | .ok value =>
      throwError "validation Bool argument normalized to wrong kind: {repr value}"
  | .error message =>
      throwError "validation Bool argument normalization failed: {message}"
  match validationArgumentForAbi .bool .uint8 (.object (.tagged 2)) with
  | .error message =>
      unless message.contains "zero or one" do
        throwError "unexpected invalid Bool tag error: {message}"
  | .ok value =>
      throwError "validation Bool argument accepted invalid tag as {repr value}"

run_cmd do
  let result ← liftCoreM <|
    compileClosed ``Fir.Validation.Corpus.Source.litNat
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "source Nat literal did not compile: {repr error}"
  unless artifact.source.externalNames.isEmpty do
    throwError "source Nat literal unexpectedly retained externals"
  unless artifact.module.exports == #[``Fir.Validation.Corpus.Source.litNat] do
    throwError "source Nat literal export mismatch: {repr artifact.module.exports}"
  unless artifact.bytes.size > Fir.Wasm.Emit.header.size do
    throwError "source Nat literal did not produce a complete Wasm module"

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
    compileModule ``Fir.Validation.Corpus.Source.boxedUInt32
      #[``Fir.Validation.Corpus.Source.polyId]
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "source dependency export regression did not compile: {repr error}"
  unless artifact.module.exports == #[``Fir.Validation.Corpus.Source.boxedUInt32] do
    throwError "source dependency escaped the artifact export surface: {repr artifact.module.exports}"
  unless artifact.module.functions.any
      (fun function => function.name == ``Fir.Validation.Corpus.Source.polyId) do
    throwError "source dependency was not retained as an internal function"

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
