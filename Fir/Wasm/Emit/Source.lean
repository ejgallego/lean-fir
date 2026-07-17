import Fir.Validation.LCNF
import Fir.Wasm.Emit.Manifest
import Fir.Wasm.WellFormed

namespace Fir.Wasm.Emit.Source

open Lean
open Fir.LeanIR.Impure

inductive CompileError where
  | lowering (error : Fir.Wasm.SupportedLoweringError)
  | encoding (error : Fir.Wasm.Emit.EncodeError)
  | manifest (message : String)
  deriving Inhabited, Repr

structure ModuleArtifact where
  source : Fir.Validation.Lcnf.Artifact
  module : Fir.Wasm.Module
  bytes : ByteArray
  formattedLcnf : String

structure Artifact extends ModuleArtifact where
  manifest : Json

/--
Compile one Lean declaration through final impure LCNF into a reusable Wasm
module. Invocation data is attached separately with `withInvocation`.
-/
def compileModule (entry : Name) (dependencies : Array Name := #[]) :
    CoreM (Except CompileError ModuleArtifact) := do
  let source ← Fir.Validation.Lcnf.compileEntry entry dependencies
  let module ←
    match Fir.Wasm.lowerSupported source.program with
    | .ok module => pure module
    | .error error => return .error (.lowering error)
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => return .error (.encoding error)
  let formattedLcnf ← source.format
  return .ok { source, module, bytes, formattedLcnf }

/-- Attach one checked semantic invocation to an already compiled module. -/
def ModuleArtifact.withInvocation (artifact : ModuleArtifact) (artifactName : String)
    (sourceEntry entry : Name) (args : Array Value) : Except CompileError Artifact := do
  let manifest ← Manifest.artifactJson artifactName sourceEntry entry artifact.module args
    |>.mapError .manifest
  return {
    source := artifact.source
    module := artifact.module
    bytes := artifact.bytes
    formattedLcnf := artifact.formattedLcnf
    manifest }

/--
Attach one checked semantic invocation whose arguments may refer to an explicit
initial FIR runtime. The runtime is invocation data and does not affect the
captured declaration, lowered module, or encoded Wasm bytes.
-/
def ModuleArtifact.withRuntimeInvocation (artifact : ModuleArtifact) (artifactName : String)
    (sourceEntry entry : Name) (runtime : RuntimeState) (args : Array Value) :
    Except CompileError Artifact := do
  let manifest ← Manifest.artifactJsonWithRuntime artifactName sourceEntry entry artifact.module
      runtime args
    |>.mapError .manifest
  return {
    source := artifact.source
    module := artifact.module
    bytes := artifact.bytes
    formattedLcnf := artifact.formattedLcnf
    manifest }

/-- Check that a backend-neutral validation result schema agrees with the emitted ABI lane. -/
def validationSchemaAcceptsAbiKind : Fir.Validation.ValidationSchema → Fir.Wasm.AbiKind → Bool
  | .usize, .usize => true
  | .bits 8, .uint8 => true
  | .bits 16, .uint16 => true
  | .bits 32, .uint32 => true
  | .bits 64, .uint64 => true
  | .unit, kind
  | .bool, kind
  | .nat, kind
  | .int, kind
  | .string, kind
  | .bytes, kind
  | .seq _, kind
  | .ctor .., kind => kind.isObjectLike
  | _, _ => false

/--
Attach an invocation encoded from the validation protocol. This is the common
boundary for corpus-driven emitters: schemas check both the source arguments
and the emitted result lane, while validation datums construct the initial FIR
runtime and semantic argument values.
-/
def ModuleArtifact.withValidationInvocation (artifact : ModuleArtifact)
    (artifactName : String) (sourceEntry entry : Name)
    (argSchemas : Array Fir.Validation.ValidationSchema)
    (data : Array Fir.Validation.ValidationDatum)
    (resultSchema : Fir.Validation.ValidationSchema) : Except CompileError Artifact := do
  let function ← Manifest.entryFunction artifact.module entry |>.mapError .manifest
  let resultKind ← Manifest.entryResultKind entry function |>.mapError .manifest
  unless validationSchemaAcceptsAbiKind resultSchema resultKind do
    throw (.manifest s!"result schema {repr resultSchema} does not match ABI kind {repr resultKind}")
  let (runtime, args) ← Fir.Validation.Lcnf.encodeArgs argSchemas data |>.mapError .manifest
  if runtime.heap.isEmpty then
    artifact.withInvocation artifactName sourceEntry entry args
  else
    artifact.withRuntimeInvocation artifactName sourceEntry entry runtime args

/--
Compile a Lean declaration and attach one checked semantic invocation. The
arguments affect only the manifest, never capture, lowering, or Wasm bytes.
-/
def compile (entry : Name) (args : Array Value) (dependencies : Array Name := #[]) :
    CoreM (Except CompileError Artifact) := do
  let result ← compileModule entry dependencies
  return result.bind fun artifact =>
    artifact.withInvocation entry.toString entry entry args

/-- Compile a Lean declaration and attach an invocation with an explicit initial runtime. -/
def compileWithRuntime (entry : Name) (runtime : RuntimeState) (args : Array Value)
    (dependencies : Array Name := #[]) : CoreM (Except CompileError Artifact) := do
  let result ← compileModule entry dependencies
  return result.bind fun artifact =>
    artifact.withRuntimeInvocation entry.toString entry entry runtime args

/-- Compile a source declaration and attach one validation-protocol invocation. -/
def compileValidationInvocation (artifactName : String) (entry : Name)
    (argSchemas : Array Fir.Validation.ValidationSchema)
    (data : Array Fir.Validation.ValidationDatum)
    (resultSchema : Fir.Validation.ValidationSchema)
    (dependencies : Array Name := #[]) : CoreM (Except CompileError Artifact) := do
  let result ← compileModule entry dependencies
  return result.bind fun artifact =>
    artifact.withValidationInvocation artifactName entry entry argSchemas data resultSchema

/-- Compile a zero-argument Lean declaration and record its closed invocation. -/
def compileClosed (entry : Name) (dependencies : Array Name := #[]) :
    CoreM (Except CompileError Artifact) :=
  compile entry #[] dependencies

def Artifact.write (artifact : Artifact) (path : System.FilePath) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path artifact.bytes
  IO.FS.writeFile (path.toString ++ ".json") artifact.manifest.compress
  IO.FS.writeFile (path.toString ++ ".lcnf") (artifact.formattedLcnf ++ "\n")

end Fir.Wasm.Emit.Source
