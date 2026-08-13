import Lean.Data.Json

namespace Fir.Validation

open Lean

/-- Version of the JSONL protocol shared by validation backends and the runner. -/
def protocolVersion : Nat := 3

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
  | usize (value : UInt64)
  | bits (width : Nat) (value : UInt64)
  | string (value : String)
  | bytes (value : Array Nat)
  | seq (value : Array ValidationDatum)
  | ctor (name : String) (tag : Nat) (fields : Array ValidationDatum)
  deriving Inhabited, BEq, Repr

/--
The protocol-v3 wire representation. Arbitrary source naturals and signed
integers use canonical decimal strings so JSON consumers with an IEEE-754
numeric type cannot silently round them. The remaining natural fields are
structural metadata or bytes and retain their compact numeric representation.
-/
private inductive ValidationDatumWire where
  | unit
  | bool (value : Bool)
  | nat (value : String)
  | int (value : String)
  | usize (value : UInt64)
  | bits (width : Nat) (value : UInt64)
  | string (value : String)
  | bytes (value : Array Nat)
  | seq (value : Array ValidationDatumWire)
  | ctor (name : String) (tag : Nat) (fields : Array ValidationDatumWire)
  deriving Inhabited, ToJson, FromJson

private partial def ValidationDatum.toWire : ValidationDatum → ValidationDatumWire
  | .unit => .unit
  | .bool value => .bool value
  | .nat value => .nat s!"{value}"
  | .int value => .int s!"{value}"
  | .usize value => .usize value
  | .bits width value => .bits width value
  | .string value => .string value
  | .bytes value => .bytes value
  | .seq value => .seq (value.map ValidationDatum.toWire)
  | .ctor name tag fields => .ctor name tag (fields.map ValidationDatum.toWire)

private partial def ValidationDatumWire.decode : ValidationDatumWire → Except String ValidationDatum
  | .unit => return .unit
  | .bool value => return .bool value
  | .nat text => do
      let some value := text.toNat?
        | throw s!"natural payload is not a decimal string: {text}"
      unless s!"{value}" == text do
        throw s!"natural payload is not canonical decimal: {text}"
      return .nat value
  | .int text => do
      let some value := text.toInt?
        | throw s!"integer payload is not a decimal string: {text}"
      unless s!"{value}" == text do
        throw s!"integer payload is not canonical decimal: {text}"
      return .int value
  | .usize value => return .usize value
  | .bits width value => return .bits width value
  | .string value => return .string value
  | .bytes value => return .bytes value
  | .seq value => return .seq (← value.mapM ValidationDatumWire.decode)
  | .ctor name tag fields =>
      return .ctor name tag (← fields.mapM ValidationDatumWire.decode)

instance : ToJson ValidationDatum where
  toJson value := toJson value.toWire

instance : FromJson ValidationDatum where
  fromJson? json := do
    let wire : ValidationDatumWire ← fromJson? json
    wire.decode

/-- Expected source-level shape used to decode an untyped backend result. -/
inductive ValidationSchema where
  | unit
  | bool
  | nat
  | int
  | usize
  | bits (width : Nat)
  /-- A source `Float32`, transported and compared by its exact IEEE bits. -/
  | float32
  /-- A source `Float`, transported and compared by its exact IEEE bits. -/
  | float64
  | string
  | bytes
  /-- A source `Array α`, distinct from `seq`, which denotes `List α`.

  The datum remains a backend-neutral sequence. Runtime consumers preserve
  Array identity, ownership, size, and capacity while comparing only the live
  element prefix at the protocol boundary. -/
  | array (element : ValidationSchema)
  | seq (element : ValidationSchema)
  /--
  A scalar transported through Lean's generic object representation.

  This marker is physical: it does not add a node to `ValidationDatum`.
  Consumers must reject inner schemas other than `Bool`, the fixed-width
  integer, `USize`, and floating-point scalar schemas accepted by
  `isBoxableScalar`.
  -/
  | boxed (scalar : ValidationSchema)
  | ctor (name : String) (tag : Nat) (fields : Array ValidationSchema)
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-- Whether a schema denotes a scalar accepted by final-LCNF `box`/`unbox`. -/
def ValidationSchema.isBoxableScalar : ValidationSchema → Bool
  | .bool | .usize | .bits 8 | .bits 16 | .bits 32 | .bits 64
  | .float32 | .float64 => true
  | _ => false

/-- Check that a datum has the recursive shape promised by a case. -/
partial def ValidationSchema.accepts : ValidationSchema → ValidationDatum → Bool
  | .unit, .unit => true
  | .bool, .bool _ => true
  | .nat, .nat _ => true
  | .int, .int _ => true
  | .usize, .usize _ => true
  | .bits expected, .bits actual _ => expected == actual
  | .float32, .bits 32 _ => true
  | .float64, .bits 64 _ => true
  | .string, .string _ => true
  | .bytes, .bytes values => values.all (· < 256)
  | .array element, .seq values => values.all (element.accepts ·)
  | .seq element, .seq values => values.all (element.accepts ·)
  | .boxed scalar, datum => scalar.isBoxableScalar && scalar.accepts datum
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

/--
Declare that one runner-supplied argument is the same source object as an
earlier argument.

Aliases use a canonical star representation: `source` is an independently
materialized root and `target` is a later argument that reuses it.  A case with
several aliases of one object repeats the same source with increasing targets.
-/
structure ArgumentAlias where
  source : Nat
  target : Nat
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/--
A logical position inside one runner-supplied argument. Each child index selects
a constructor field or a sequence element. Empty child paths name argument
roots and are reserved for `ArgumentAlias`.
-/
structure ArgumentPath where
  argument : Nat
  children : Array Nat
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/--
Declare that two nested positions in the runner-supplied argument graph are
the same source object. The source is independently materialized and the later
target reuses it, matching the canonical star convention of `ArgumentAlias`.
-/
structure NestedArgumentAlias where
  source : ArgumentPath
  target : ArgumentPath
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/--
Validate the backend-neutral argument-alias graph.

Targets must be strictly increasing, sources must be earlier independently
materialized roots, and an alias may only connect equal schema/datum pairs.
This makes the manifest representation canonical before a backend assigns heap
locations or reference counts.
-/
def checkArgumentAliases (schemas : Array ValidationSchema)
    (data : Array ValidationDatum) (aliases : Array ArgumentAlias) :
    Except String Unit := do
  unless schemas.size == data.size do
    throw s!"argument schema/fixture arity mismatch: {schemas.size} schemas, {data.size} values"
  let _ ← aliases.foldlM (init := (none, #[]))
    fun (lastTarget?, targets) alias => do
      unless alias.source < alias.target do
        throw s!"argument alias source {alias.source} must precede target {alias.target}"
      unless alias.target < data.size do
        throw s!"argument alias target {alias.target} is out of bounds for {data.size} arguments"
      if let some lastTarget := lastTarget? then
        unless lastTarget < alias.target do
          throw "argument alias targets must be strictly increasing"
      if targets.contains alias.source then
        throw s!"argument alias source {alias.source} must be an independently materialized root"
      let some sourceSchema := schemas[alias.source]? |
        throw s!"argument alias source {alias.source} is out of bounds"
      let some targetSchema := schemas[alias.target]? |
        throw s!"argument alias target {alias.target} is out of bounds"
      unless sourceSchema == targetSchema do
        throw s!"argument alias {alias.source}->{alias.target} connects different schemas"
      let some sourceDatum := data[alias.source]? |
        throw s!"argument alias source {alias.source} is out of bounds"
      let some targetDatum := data[alias.target]? |
        throw s!"argument alias target {alias.target} is out of bounds"
      unless sourceDatum == targetDatum do
        throw s!"argument alias {alias.source}->{alias.target} connects different fixtures"
      return (some alias.target, targets.push alias.target)
  return ()

private def pathChildrenPrecede : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | left :: lefts, right :: rights =>
      left < right || (left == right && pathChildrenPrecede lefts rights)
  | _, _ => false

/-- Canonical preorder on logical argument-graph positions. -/
def ArgumentPath.precedes (left right : ArgumentPath) : Bool :=
  left.argument < right.argument ||
    (left.argument == right.argument &&
      pathChildrenPrecede left.children.toList right.children.toList)

private partial def resolveArgumentPathChildren
    (schema : ValidationSchema) (datum : ValidationDatum) :
    List Nat → Except String (ValidationSchema × ValidationDatum)
  | [] => return (schema, datum)
  | index :: remaining =>
      match schema, datum with
      | .array element, .seq values | .seq element, .seq values => do
          let some value := values[index]? |
            throw s!"container child {index} is out of bounds for {values.size} elements"
          resolveArgumentPathChildren element value remaining
      | .ctor _ _ schemas, .ctor _ _ fields => do
          let some childSchema := schemas[index]? |
            throw s!"constructor child {index} is out of bounds for {schemas.size} fields"
          let some childDatum := fields[index]? |
            throw s!"constructor child {index} is out of bounds for {fields.size} fixtures"
          resolveArgumentPathChildren childSchema childDatum remaining
      | _, _ =>
          throw s!"child {index} descends through non-container schema {repr schema}"

/-- Resolve one logical argument-graph path before a backend assigns locations. -/
def resolveArgumentPath (schemas : Array ValidationSchema)
    (data : Array ValidationDatum) (path : ArgumentPath) :
    Except String (ValidationSchema × ValidationDatum) := do
  let some schema := schemas[path.argument]? |
    throw s!"argument {path.argument} is out of bounds for {schemas.size} schemas"
  let some datum := data[path.argument]? |
    throw s!"argument {path.argument} is out of bounds for {data.size} fixtures"
  resolveArgumentPathChildren schema datum path.children.toList

/--
Validate nested input-graph aliases before a backend materializes the graph.

Nested paths must be nonempty, targets must be strictly increasing in logical
preorder, and a source must precede its target without itself being an alias
target. Paths below top-level alias targets are rejected because the root alias
already transfers the complete graph. Equal source/target schemas and fixtures
ensure that identity metadata cannot change the semantic tree value.
-/
def checkNestedArgumentAliases (schemas : Array ValidationSchema)
    (data : Array ValidationDatum) (argumentAliases : Array ArgumentAlias)
    (aliases : Array NestedArgumentAlias) : Except String Unit := do
  checkArgumentAliases schemas data argumentAliases
  let rootTargets := argumentAliases.map (fun alias => alias.target)
  let _ ← aliases.foldlM (init := (none, #[]))
    fun (lastTarget?, targets) alias => do
      if alias.source.children.isEmpty || alias.target.children.isEmpty then
        throw "nested argument alias paths must contain at least one child"
      if rootTargets.contains alias.source.argument ||
          rootTargets.contains alias.target.argument then
        throw "nested argument aliases cannot descend below a top-level alias target"
      unless alias.source.precedes alias.target do
        throw s!"nested argument alias source {repr alias.source} must precede target {repr alias.target}"
      if let some lastTarget := lastTarget? then
        unless lastTarget.precedes alias.target do
          throw "nested argument alias targets must be strictly increasing"
      if targets.contains alias.source then
        throw s!"nested argument alias source {repr alias.source} must be independently materialized"
      let (sourceSchema, sourceDatum) ← resolveArgumentPath schemas data alias.source
        |>.mapError fun error => s!"nested argument alias source: {error}"
      let (targetSchema, targetDatum) ← resolveArgumentPath schemas data alias.target
        |>.mapError fun error => s!"nested argument alias target: {error}"
      unless sourceSchema == targetSchema do
        throw s!"nested argument alias {repr alias.source}->{repr alias.target} connects different schemas"
      unless sourceDatum == targetDatum do
        throw s!"nested argument alias {repr alias.source}->{repr alias.target} connects different fixtures"
      return (some alias.target, targets.push alias.target)
  return ()

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
    .nat 18446744073709551617,
    .int (-2147483648),
    .int (-2147483649),
    .int 340282366920938463463374607431768211473,
    .int (-340282366920938463463374607431768211473),
    .usize 18446744073709551615,
    .bits 64 18446744073709551615,
    .ctor "Prod.mk" 0 #[.bool true, .bytes #[0, 127, 255]]]
  resultSchema := .seq .usize
  fuel := some 1000
  timeoutMs := some 250 }

#guard match Jsonl.decodeCaseRequest (Jsonl.encode protocolRoundTripRequest) with
  | .ok request => request == protocolRoundTripRequest
  | .error _ => false

#guard ValidationSchema.float32.accepts (.bits 32 0x7fc00001)
#guard !ValidationSchema.float32.accepts (.bits 64 0x7fc00001)
#guard ValidationSchema.float64.accepts (.bits 64 0x7ff8000000000001)
#guard !ValidationSchema.float64.accepts (.bits 32 0x7fc00001)
#guard (ValidationSchema.boxed .bool).accepts (.bool true)
#guard (ValidationSchema.boxed (.bits 8)).accepts (.bits 8 0xff)
#guard !(ValidationSchema.boxed (.bits 8)).accepts (.bits 16 0xff)
#guard !(ValidationSchema.boxed .nat).accepts (.nat 1)
#guard (ValidationSchema.array (.boxed .bool)).accepts (.seq #[.bool true, .bool false])
#guard !(ValidationSchema.array (.boxed .bool)).accepts (.seq #[.bool true, .nat 0])

#guard match (fromJson? (toJson (ValidationSchema.boxed (.bits 8))) :
    Except String ValidationSchema) with
  | .ok schema => schema == .boxed (.bits 8)
  | .error _ => false

#guard match (fromJson? (toJson (ValidationSchema.array (.boxed .float64))) :
    Except String ValidationSchema) with
  | .ok schema => schema == .array (.boxed .float64)
  | .error _ => false

#guard toJson (.nat 18446744073709551617 : ValidationDatum) ==
  Json.mkObj [("nat", Json.mkObj [("value", "18446744073709551617")])]

#guard match (fromJson?
    (Json.mkObj [("nat", Json.mkObj [("value", "018446744073709551617")])]) :
    Except String ValidationDatum) with
  | .error _ => true
  | .ok _ => false

#guard match (fromJson?
    (Json.mkObj [("nat", Json.mkObj [("value", Json.num 42)])]) :
    Except String ValidationDatum) with
  | .error _ => true
  | .ok _ => false

#guard toJson (.int (-340282366920938463463374607431768211473) :
    ValidationDatum) ==
  Json.mkObj [("int", Json.mkObj [
    ("value", "-340282366920938463463374607431768211473")])]

#guard match (fromJson?
    (Json.mkObj [("int", Json.mkObj [
      ("value", "-0340282366920938463463374607431768211473")])]) :
    Except String ValidationDatum) with
  | .error _ => true
  | .ok _ => false

#guard match (fromJson?
    (Json.mkObj [("int", Json.mkObj [("value", "-0")])]) :
    Except String ValidationDatum) with
  | .error _ => true
  | .ok _ => false

#guard match (fromJson?
    (Json.mkObj [("int", Json.mkObj [("value", Json.num 42)])]) :
    Except String ValidationDatum) with
  | .error _ => true
  | .ok _ => false

private def protocolRoundTripResult : BackendResult := {
  caseId := protocolRoundTripRequest.caseId
  backend := "protocol-test"
  outcome := .success {
    termination := .returned (.seq #[.usize 0, .usize 18446744073709551615])
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
