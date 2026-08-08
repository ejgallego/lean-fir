import Fir.Validation.Corpus
import Fir.Wasm.Emit.PrettyFormat
import Fir.Wasm.Emit.Source
import Fir.Wasm.PrettyFormat
import Lean.Elab.Command

namespace Fir.Wasm.Emit.SourceExamples

open Lean Elab Command
open Fir.Wasm.Emit.Source

def idFloat32Fixture (value : Float32) : Float32 := value

def idFloatFixture (value : Float) : Float := value

#guard validationSchemaAcceptsAbiKind .float32 .float32
#guard validationSchemaAcceptsAbiKind .float64 .float
#guard !validationSchemaAcceptsAbiKind .float32 .float
#guard !validationSchemaAcceptsAbiKind .float64 .float32

#fir_wasm_pretty_facade prettyRawFixture

private def prettyRuntimeImports : Array String := #[
  "Int.ofNat",
  "Int.decLt",
  "Int.natAbs",
  "String.Internal.pushn",
  "String.Internal.append",
  "Int.sub",
  "String.Internal.length",
  "Nat.add",
  "Nat.decEq",
  "Nat.sub",
  "Int.add",
  "String.Internal.posOf",
  "String.Internal.offsetOfPos",
  "String.utf8ByteSize",
  "Nat.decLt",
  "Nat.decLe",
  "panicCore",
  "String.Internal.extract",
  "String.Internal.next",
  Fir.Wasm.Emit.PrettyFormat.weakMonadInhabitedName]

run_cmd do
  let artifact ← liftCoreM <| withoutModifyingEnv <|
    Fir.Validation.Lcnf.compileEntry ``prettyRawFixture
  let program := artifact.program
  let some entry := program.findDecl? ``prettyRawFixture
    | throwError "raw Format facade was absent from its compiler dependency closure"
  let paramKinds := entry.params.mapM fun param => Fir.Wasm.abiValueKind? param.type
  unless paramKinds ==
      some #[.tobject, .tobject, .tobject, .tobject] do
    throwError "raw Format facade parameter ABI changed: {repr paramKinds}"
  unless Fir.Wasm.abiValueKind? entry.type == some .object do
    throwError "raw Format facade result ABI changed: {repr entry.type}"
  unless artifact.externalNames.size == 23 do
    throwError "raw Format helper inventory changed size:\n{repr artifact.externalNames}"
  for required in #["String.Internal.append", "Nat.add", "panicCore",
      Fir.Wasm.Emit.PrettyFormat.weakMonadInhabitedName] do
    unless artifact.externalNames.any fun name => name.toString == required do
      throwError "raw Format helper inventory lost {required}"
  let unsupported := program.decls.filter fun decl => !Fir.Wasm.supportedDecl program decl
  unless unsupported.size == 1 do
    throwError "raw Format facade has {unsupported.size} unsupported declarations, expected one"
  unless unsupported.any fun decl => decl.name.toString.contains "panic" do
    throwError "raw Format facade no longer records the unreachable panic specialization"
  match Fir.Wasm.validateSupported program with
  | .error (.unsupportedCode name) =>
      unless name.toString.contains "panic" do
        throwError "raw Format facade failed first at an unexpected declaration: {name}"
  | .error error => throwError "raw Format facade failed with an unexpected error: {repr error}"
  | .ok _ => throwError "raw Format facade unexpectedly passed before its refinement fix"

run_cmd do
  let impureDeclsBefore ← liftCoreM Lean.Compiler.LCNF.getLocalImpureDecls
  let result ← liftCoreM <|
    Fir.Wasm.Emit.PrettyFormat.compileModule ``prettyRawFixture
  let impureDeclsAfter ← liftCoreM Lean.Compiler.LCNF.getLocalImpureDecls
  unless impureDeclsAfter == impureDeclsBefore do
    throwError "internalized Format capture polluted Lean's local final-LCNF environment"
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "internalized Format facade did not compile: {repr error}"
  unless artifact.source.externalNames.map (fun name => name.toString) ==
      #[Fir.Wasm.Emit.PrettyFormat.weakMonadInhabitedName] do
    throwError "internalized Format facade retained unexpected declarations:\n{repr artifact.source.externalNames}"
  let declarationImports := artifact.module.imports.filterMap (·.declaration?)
  unless declarationImports.map (fun name => name.toString) == prettyRuntimeImports do
    throwError "internalized Format facade retained declaration imports: {repr declarationImports}"
  unless artifact.module.exports == #[``prettyRawFixture] do
    throwError "internalized Format facade export changed: {repr artifact.module.exports}"
  unless artifact.bytes.size > Fir.Wasm.Emit.header.size do
    throwError "internalized Format facade did not encode a complete Wasm module"

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
    compileModule ``idFloat32Fixture
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "Float32 source facade did not compile: {repr error}"
  let facade := Fir.Wasm.Emit.BitExactFloat.facadeName
    ``idFloat32Fixture
  unless artifact.module.exports ==
      #[``idFloat32Fixture, facade] do
    throwError "Float32 source facade export mismatch: {repr artifact.module.exports}"
  let descriptor ← match artifact.moduleManifest with
    | .ok descriptor => pure descriptor
    | .error error => throwError "Float32 module descriptor failed: {repr error}"
  let text := descriptor.compress
  unless text.contains "\"bitExactFloatTransport\":" &&
      text.contains "\"encoding\":\"wasm-reinterpret-i32-i64\"" &&
      text.contains s!"\"entry\":\"{facade}\"" &&
      text.contains "\"params\":[\"uint32\"]" &&
      text.contains "\"result\":\"uint32\"" do
    throwError "Float32 module descriptor lost its exact-bit facade: {text}"

run_cmd do
  let result ← liftCoreM <|
    compileModule ``idFloatFixture
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "Float source facade did not compile: {repr error}"
  let facade := Fir.Wasm.Emit.BitExactFloat.facadeName
    ``idFloatFixture
  unless artifact.module.exports ==
      #[``idFloatFixture, facade] do
    throwError "Float source facade export mismatch: {repr artifact.module.exports}"
  let descriptor ← match artifact.moduleManifest with
    | .ok descriptor => pure descriptor
    | .error error => throwError "Float module descriptor failed: {repr error}"
  let text := descriptor.compress
  unless text.contains "\"bitExactFloatTransport\":" &&
      text.contains "\"params\":[\"uint64\"]" &&
      text.contains "\"result\":\"uint64\"" do
    throwError "Float module descriptor lost its exact-bit facade: {text}"

run_cmd do
  let entries := #[``idFloat32Fixture, ``idFloatFixture]
  let source ← liftCoreM <|
    compileEntriesFinalCapturedInternalized entries
  unless source.entry == ``idFloat32Fixture do
    throwError "multi-entry capture changed its canonical entry: {source.entry}"
  for entry in entries do
    unless ((source.program.findDecl? entry).isSome &&
        !source.externalNames.contains entry) do
      throwError "multi-entry capture did not retain local root {entry}"
  let result ← liftCoreM <|
    compileModuleArtifactWithExports source entries .ok
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "multi-entry Float source did not compile: {repr error}"
  let facade32 := Fir.Wasm.Emit.BitExactFloat.facadeName ``idFloat32Fixture
  let facade64 := Fir.Wasm.Emit.BitExactFloat.facadeName ``idFloatFixture
  unless artifact.module.exports ==
      #[``idFloat32Fixture, ``idFloatFixture, facade32, facade64] do
    throwError "multi-entry Float export mismatch: {repr artifact.module.exports}"
  let unavailable := ``Fir.Validation.Corpus.Source.litNat
  let unavailableResult ← liftCoreM <|
    compileModuleArtifactWithExports source
      #[``idFloat32Fixture, unavailable] .ok
  match unavailableResult with
  | .error (.manifest message) =>
      unless message.contains "not a lowered source function" do
        throwError "unavailable multi-entry export reported the wrong error: {message}"
  | .error error =>
      throwError "unavailable multi-entry export reported the wrong error kind: {repr error}"
  | .ok _ =>
      throwError "unavailable multi-entry export did not fail closed"

run_cmd do
  let result ← liftCoreM <|
    compileModule ``idFloat32Fixture
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "Float facade fail-closed fixture did not compile: {repr error}"
  let facade := Fir.Wasm.Emit.BitExactFloat.facadeName
    ``idFloat32Fixture
  let missingExport := {
    artifact with
    module := { artifact.module with exports := #[``idFloat32Fixture] } }
  match missingExport.moduleManifest with
  | .error (.manifest message) =>
      unless message.contains "is not exported" do
        throwError "missing Float facade reported the wrong error: {message}"
  | .error error =>
      throwError "missing Float facade reported the wrong error kind: {repr error}"
  | .ok descriptor =>
      throwError "missing Float facade emitted a descriptor: {descriptor.compress}"
  let malformedBody := {
    artifact with
    module := {
      artifact.module with
      functions := artifact.module.functions.map fun
          (function : Fir.Wasm.Function) =>
        if function.name == facade then
          { function with body := [Fir.Wasm.Instruction.ret] }
        else
          function } }
  match malformedBody.moduleManifest with
  | .error (.manifest message) =>
      unless message.contains "does not match its source signature" do
        throwError "malformed Float facade reported the wrong error: {message}"
  | .error error =>
      throwError "malformed Float facade reported the wrong error kind: {repr error}"
  | .ok descriptor =>
      throwError "malformed Float facade emitted a descriptor: {descriptor.compress}"
  match Fir.Wasm.Emit.BitExactFloat.install artifact.module
      ``idFloat32Fixture with
  | .error message =>
      unless message.contains "already reserved" do
        throwError "duplicate Float facade reported the wrong error: {message}"
  | .ok _ =>
      throwError "duplicate Float facade installation did not fail closed"

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
  let moduleManifest ← match moduleArtifact.moduleManifest with
    | .ok manifest => pure manifest
    | .error error => throwError "parameterized module descriptor failed: {repr error}"
  let moduleManifestText := moduleManifest.compress
  unless moduleManifestText.contains
      "\"entry\":\"Fir.Validation.Corpus.Source.idUSize\"" &&
      moduleManifestText.contains "\"params\":[\"usize\"]" &&
      moduleManifestText.contains "\"result\":\"usize\"" do
    throwError "parameterized module descriptor lost its raw ABI: {moduleManifestText}"
  for invocationField in #["\"fixture\"", "\"arguments\"", "\"initialRuntime\""] do
    if moduleManifestText.contains invocationField then
      throwError "module descriptor retained invocation field {invocationField}"
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
