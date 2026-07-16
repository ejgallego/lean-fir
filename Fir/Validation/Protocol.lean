import Lean.Data.Json

namespace Fir.Validation

open Lean

/-- Version of the JSONL protocol shared by validation backends and the runner. -/
def protocolVersion : Nat := 1

/--
A backend-neutral semantic value.

`bits` carries fixed-width integers and floating-point bit patterns without
depending on a host language's numeric representation. Byte values are stored
as naturals so the JSON representation stays a simple array; producers must
only emit values below 256.
-/
inductive ValidationDatum where
  | unit
  | bool (value : Bool)
  | nat (value : Nat)
  | int (value : Int)
  | bits (width : Nat) (value : UInt64)
  | string (value : String)
  | bytes (value : Array Nat)
  | seq (value : Array ValidationDatum)
  | ctor (name : String) (tag : Nat) (fields : Array ValidationDatum)
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-- Expected source-level shape used to decode an untyped backend result. -/
inductive ValidationSchema where
  | unit
  | bool
  | nat
  | int
  | bits (width : Nat)
  | string
  | bytes
  | seq (element : ValidationSchema)
  | ctor (name : String) (tag : Nat) (fields : Array ValidationSchema)
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-- Check that a datum has the recursive shape promised by a case. -/
partial def ValidationSchema.accepts : ValidationSchema → ValidationDatum → Bool
  | .unit, .unit => true
  | .bool, .bool _ => true
  | .nat, .nat _ => true
  | .int, .int _ => true
  | .bits expected, .bits actual _ => expected == actual
  | .string, .string _ => true
  | .bytes, .bytes values => values.all (· < 256)
  | .seq element, .seq values => values.all (element.accepts ·)
  | .ctor expectedName expectedTag expectedFields,
      .ctor actualName actualTag actualFields =>
      expectedName == actualName && expectedTag == actualTag &&
        acceptFields expectedFields.toList actualFields.toList
  | _, _ => false
where
  acceptFields : List ValidationSchema → List ValidationDatum → Bool
    | [], [] => true
    | schema :: schemas, value :: values =>
        schema.accepts value && acceptFields schemas values
    | _, _ => false

/-- A controlled external effect observed while executing a case. -/
structure EffectEvent where
  operation : String
  args : Array ValidationDatum := #[]
  result : Option ValidationDatum := none
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-- The part of termination that belongs to source-program semantics. -/
inductive SemanticTermination where
  | returned (value : ValidationDatum)
  | exception (kind : String) (message : String)
  | exited (code : Int)
  | runtimeFault (kind : String) (message : String)
  | diverged
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-- Semantic output compared across native Lean and candidate backends. -/
structure ValidationObservation where
  termination : SemanticTermination
  stdout : String := ""
  stderr : String := ""
  effects : Array EffectEvent := #[]
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-- One protocol request sent to a backend process. -/
structure CaseRequest where
  version : Nat := protocolVersion
  caseId : String
  entry : String
  args : Array ValidationDatum := #[]
  resultSchema : ValidationSchema
  fuel : Option Nat := none
  timeoutMs : Option Nat := none
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-- Classification of a backend result, independent of its payload. -/
inductive BackendStatus where
  | success
  | unsupported
  | timeout
  | crash
  | outOfFuel
  | malformedOutput
  | failure
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/--
The result of executing a case in one backend.

Only `success` contains a semantic observation. All other constructors describe
the validation harness or backend, and must not be compared as source behavior.
-/
inductive BackendOutcome where
  | success (observation : ValidationObservation)
  | unsupported (reason : String)
  | timeout (limitMs : Nat)
  | crash (exitCode : Int) (message : String)
  | outOfFuel (fuel : Nat)
  | malformedOutput (message : String)
  | failure (message : String)
  deriving Inhabited, BEq, Repr, ToJson, FromJson

def BackendOutcome.status : BackendOutcome → BackendStatus
  | .success _ => .success
  | .unsupported _ => .unsupported
  | .timeout _ => .timeout
  | .crash .. => .crash
  | .outOfFuel _ => .outOfFuel
  | .malformedOutput _ => .malformedOutput
  | .failure _ => .failure

/-- Non-semantic metadata retained for reports and debugging. -/
structure Diagnostic where
  key : String
  value : String
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-- One versioned response emitted by a backend process. -/
structure BackendResult where
  version : Nat := protocolVersion
  caseId : String
  backend : String
  outcome : BackendOutcome
  diagnostics : Array Diagnostic := #[]
  deriving Inhabited, BEq, Repr, ToJson, FromJson

def CaseRequest.checkVersion (request : CaseRequest) : Except String Unit :=
  if request.version == protocolVersion then
    .ok ()
  else
    .error s!"unsupported validation protocol version {request.version}; expected {protocolVersion}"

def BackendResult.checkVersion (result : BackendResult) : Except String Unit :=
  if result.version == protocolVersion then
    .ok ()
  else
    .error s!"unsupported validation protocol version {result.version}; expected {protocolVersion}"

namespace Jsonl

/-- Encode one value as a compact JSONL record, without the trailing newline. -/
def encode [ToJson α] (value : α) : String :=
  (toJson value).compress

/-- Decode one JSONL record. Leading and trailing JSON whitespace are allowed. -/
def decode [FromJson α] (line : String) : Except String α := do
  fromJson? (← Json.parse line)

/-- Emit one complete JSONL record to standard output. -/
def emit [ToJson α] (value : α) : IO Unit :=
  IO.println (encode value)

/-- Decode a case request and reject protocol versions unsupported by this build. -/
def decodeCaseRequest (line : String) : Except String CaseRequest := do
  let request ← decode line
  request.checkVersion
  return request

/-- Decode a backend result and reject protocol versions unsupported by this build. -/
def decodeBackendResult (line : String) : Except String BackendResult := do
  let result ← decode line
  result.checkVersion
  return result

end Jsonl

private def protocolRoundTripRequest : CaseRequest := {
  caseId := "protocol.round-trip"
  entry := "Fir.Validation.protocolRoundTrip"
  args := #[
    .nat 42,
    .bits 64 18446744073709551615,
    .ctor "Prod.mk" 0 #[.bool true, .bytes #[0, 127, 255]]]
  resultSchema := .seq (.bits 64)
  fuel := some 1000
  timeoutMs := some 250 }

#guard match Jsonl.decodeCaseRequest (Jsonl.encode protocolRoundTripRequest) with
  | .ok request => request == protocolRoundTripRequest
  | .error _ => false

private def protocolRoundTripResult : BackendResult := {
  caseId := protocolRoundTripRequest.caseId
  backend := "protocol-test"
  outcome := .success {
    termination := .returned (.seq #[.bits 64 0, .bits 64 18446744073709551615])
    stdout := "out\n"
    stderr := "err\n"
    effects := #[{
      operation := "test.effect"
      args := #[.string "argument"]
      result := some (.unit) }] }
  diagnostics := #[{ key := "steps", value := "7" }] }

#guard match Jsonl.decodeBackendResult (Jsonl.encode protocolRoundTripResult) with
  | .ok result => result == protocolRoundTripResult
  | .error _ => false

#guard match Jsonl.decodeCaseRequest
    (Jsonl.encode { protocolRoundTripRequest with version := protocolVersion + 1 }) with
  | .error _ => true
  | .ok _ => false

end Fir.Validation
