import Fir.LeanIR.Runtime
import Fir.Wasm.Emit.Binary
import Fir.Wasm.Handle

namespace Fir.Wasm.Emit.Manifest

open Fir.LeanIR.Impure
open Fir.Wasm
open Lean

def abiKindName : AbiKind → String
  | .object => "object"
  | .tagged => "tagged"
  | .tobject => "tobject"
  | .erased => "erased"
  | .reuseToken => "reuseToken"
  | .uint8 => "uint8"
  | .uint16 => "uint16"
  | .uint32 => "uint32"
  | .uint64 => "uint64"
  | .usize => "usize"
  | .float32 => "float32"
  | .float => "float"

def operationJson : RuntimeOp → Except String Json
  | .literal (.nat value) result =>
      return Json.mkObj [
        ("kind", "naturalLiteral"),
        ("value", s!"{value}"),
        ("result", abiKindName result)]
  | .literal (.str value) result =>
      return Json.mkObj [
        ("kind", "stringLiteral"),
        ("value", value),
        ("result", abiKindName result)]
  | .allocCtor info fields result =>
      return Json.mkObj [
        ("kind", "allocCtor"),
        ("name", info.name.toString),
        ("tag", s!"{info.cidx}"),
        ("size", info.size),
        ("usize", info.usize),
        ("ssize", info.ssize),
        ("fields", Json.arr (fields.map fun kind => abiKindName kind)),
        ("result", abiKindName result)]
  | .objectProj index result =>
      return Json.mkObj [
        ("kind", "objectProj"),
        ("index", index),
        ("result", abiKindName result)]
  | .getTag => return Json.mkObj [("kind", "getTag")]
  | operation => throw s!"unsupported A0 host operation: {operation.stem}"

def importJson (import_ : Fir.Wasm.Import) : Except String Json := do
  let some operation := import_.operation? |
    throw s!"external import is outside A0: {import_.moduleName}.{import_.itemName}"
  return Json.mkObj [
    ("module", import_.moduleName),
    ("name", import_.itemName),
    ("operation", ← operationJson operation)]

def scalarValueJson : ScalarValue → Json
  | .uint8 value => Json.mkObj [("kind", "uint8"), ("value", s!"{value}")]
  | .uint16 value => Json.mkObj [("kind", "uint16"), ("value", s!"{value}")]
  | .uint32 value => Json.mkObj [("kind", "uint32"), ("value", s!"{value}")]
  | .uint64 value => Json.mkObj [("kind", "uint64"), ("value", s!"{value}")]

def valueJson : Value → Json
  | .object (.tagged payload) =>
      Json.mkObj [
        ("kind", "object"),
        ("reference", Json.mkObj [("kind", "tagged"), ("payload", s!"{payload}")])]
  | .object (.heap location) =>
      Json.mkObj [
        ("kind", "object"),
        ("reference", Json.mkObj [("kind", "heap"), ("location", location)])]
  | .usize value => Json.mkObj [("kind", "usize"), ("value", s!"{value}")]
  | .scalar value => Json.mkObj [("kind", "scalar"), ("scalar", scalarValueJson value)]
  | .erased => Json.mkObj [("kind", "erased")]
  | .reuseToken location? =>
      Json.mkObj [
        ("kind", "reuseToken"),
        ("location", location?.map (fun location => (location : Json)) |>.getD Json.null)]

def scalarFieldJson (field : ScalarField) : Json :=
  Json.mkObj [
    ("width", field.width),
    ("offset", field.offset),
    ("value", scalarValueJson field.value)]

def heapObjectJson : HeapObject → Except String Json
  | .ctor object =>
      return Json.mkObj [
        ("kind", "ctor"),
        ("tag", s!"{object.tag}"),
        ("objectFields", Json.arr (object.objectFields.map valueJson)),
        ("usizeFields", Json.arr (object.usizeFields.map fun value => s!"{value}")),
        ("scalarFields", Json.arr (object.scalarFields.toArray.map scalarFieldJson))]
  | .string value => return Json.mkObj [("kind", "string"), ("value", value)]
  | .natural value => return Json.mkObj [("kind", "natural"), ("value", s!"{value}")]
  | .closure .. => throw "closure objects are outside the A0 initial-runtime contract"
  | .boxed .. => throw "boxed objects are outside the A0 initial-runtime contract"
  | .integer .. => throw "integer objects are outside the A0 initial-runtime contract"
  | .byteArray .. => throw "byte-array objects are outside the A0 initial-runtime contract"
  | .opaque .. => throw "opaque objects are outside the A0 initial-runtime contract"

def heapCellJson (entry : Location × HeapCell) : Except String Json := do
  return Json.mkObj [
    ("location", entry.fst),
    ("rc", entry.snd.rc),
    ("persistent", entry.snd.persistent),
    ("live", entry.snd.live),
    ("object", ← heapObjectJson entry.snd.object)]

private def validateHeap (runtime : RuntimeState) : Except String Unit := do
  unless runtime.nextLocation ≤ 9007199254740991 do
    throw s!"nextLocation {runtime.nextLocation} exceeds the A0 JSON integer range"
  let rec loop : Heap → List Location → Except String Unit
    | [], _ => pure ()
    | (location, cell) :: rest, seen => do
        unless location < runtime.nextLocation do
          throw s!"heap location {location} is not below nextLocation {runtime.nextLocation}"
        unless cell.rc ≤ 9007199254740991 do
          throw s!"reference count {cell.rc} at location {location} exceeds the A0 JSON integer range"
        if seen.contains location then
          throw s!"duplicate initial heap location {location}"
        loop rest (location :: seen)
  loop runtime.heap []

private def validateRuntimeValue (runtime : RuntimeState) : Value → Except String Unit
  | .object (.heap location) | .reuseToken (some location) =>
      getLiveCell runtime location
        |>.map (fun _ => ())
        |>.mapError fun _ => s!"initial runtime refers to dead or unknown heap location {location}"
  | _ => pure ()

private def validateHeapObjectReferences (runtime : RuntimeState) : HeapObject → Except String Unit
  | .ctor object => object.objectFields.forM (validateRuntimeValue runtime)
  | .closure _ _ fixed => fixed.forM (validateRuntimeValue runtime)
  | .boxed _ value => validateRuntimeValue runtime value
  | _ => pure ()

def runtimeJson (runtime : RuntimeState) : Except String Json := do
  unless runtime.globals.isEmpty do
    throw "initial runtime globals are outside the A0 artifact contract"
  unless runtime.world == 0 do
    throw "nonzero initial worlds are outside the A0 artifact contract"
  unless runtime.trace.isEmpty do
    throw "nonempty initial traces are outside the A0 artifact contract"
  validateHeap runtime
  runtime.heap.forM fun entry => validateHeapObjectReferences runtime entry.snd.object
  let heap ← runtime.heap.mapM heapCellJson
  return Json.mkObj [
    ("nextLocation", runtime.nextLocation),
    ("heap", Json.arr heap.toArray)]

private def requireLiveLocation (runtime : RuntimeState) (location : Location) : Except String Unit :=
  getLiveCell runtime location
    |>.map (fun _ => ())
    |>.mapError fun _ => s!"argument refers to dead or unknown heap location {location}"

def argumentJsonWithRuntime (runtime : RuntimeState) (kind : AbiKind)
    (value : Value) : Except String Json := do
  unless kind.acceptsValue value do
    throw s!"argument {repr value} does not match ABI kind {repr kind}"
  match value with
  | .object (.tagged payload) =>
      return Json.mkObj [("kind", "tagged"), ("payload", s!"{payload}")]
  | .object (.heap location) =>
      requireLiveLocation runtime location
      return Json.mkObj [("kind", "heap"), ("location", location)]
  | .usize value => return Json.mkObj [("kind", "usize"), ("value", s!"{value}")]
  | .scalar (.uint8 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint8"), ("value", s!"{value}")]
  | .scalar (.uint16 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint16"), ("value", s!"{value}")]
  | .scalar (.uint32 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint32"), ("value", s!"{value}")]
  | .scalar (.uint64 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint64"), ("value", s!"{value}")]
  | .erased => return Json.mkObj [("kind", "erased")]
  | .reuseToken none =>
      return Json.mkObj [("kind", "reuseToken"), ("location", Json.null)]
  | .reuseToken (some location) =>
      requireLiveLocation runtime location
      return Json.mkObj [("kind", "reuseToken"), ("location", location)]

def argumentJson (kind : AbiKind) (value : Value) : Except String Json := do
  unless kind.acceptsValue value do
    throw s!"argument {repr value} does not match ABI kind {repr kind}"
  match value with
  | .object (.tagged payload) =>
      return Json.mkObj [("kind", "tagged"), ("payload", s!"{payload}")]
  | .object (.heap _) => throw "heap-backed arguments require an explicit initial runtime"
  | .usize value => return Json.mkObj [("kind", "usize"), ("value", s!"{value}")]
  | .scalar (.uint8 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint8"), ("value", s!"{value}")]
  | .scalar (.uint16 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint16"), ("value", s!"{value}")]
  | .scalar (.uint32 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint32"), ("value", s!"{value}")]
  | .scalar (.uint64 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint64"), ("value", s!"{value}")]
  | .erased => return Json.mkObj [("kind", "erased")]
  | .reuseToken none =>
      return Json.mkObj [("kind", "reuseToken"), ("location", Json.null)]
  | .reuseToken (some _) => throw "heap-backed arguments require an explicit initial runtime"

def entryFunction (module : Fir.Wasm.Module) (entry : Name) : Except String Fir.Wasm.Function := do
  unless module.exports.contains entry do
    throw s!"entry {entry} is not exported"
  let some function := module.functions.toList.find? (·.name == entry) |
    throw s!"entry {entry} is not a lowered function"
  return function

def entryResultKind (entry : Name) (function : Fir.Wasm.Function) : Except String AbiKind := do
  match function.results.toList with
  | [kind] => pure kind
  | results => throw s!"entry {entry} must return exactly one ABI value, got {results.length}"

def artifactJson (artifactName : String) (sourceEntry entry : Name)
    (module : Fir.Wasm.Module) (args : Array Value) : Except String Json := do
  let function ← entryFunction module entry
  let result ← entryResultKind entry function
  let params := function.params.map (·.snd)
  unless params.size == args.size do
    throw s!"entry {entry} expects {params.size} arguments, got {args.size}"
  let arguments ← (params.toList.zip args.toList).mapM fun (kind, value) =>
    argumentJson kind value
  let imports ← module.imports.toList.mapM importJson
  return Json.mkObj [
    ("fixture", artifactName),
    ("sourceEntry", sourceEntry.toString),
    ("entry", entry.toString),
    ("result", abiKindName result),
    ("params", Json.arr (params.map fun kind => (abiKindName kind : Json))),
    ("arguments", Json.arr arguments.toArray),
    ("imports", Json.arr imports.toArray)]

def artifactJsonWithRuntime (artifactName : String) (sourceEntry entry : Name)
    (module : Fir.Wasm.Module) (runtime : RuntimeState) (args : Array Value) : Except String Json := do
  let function ← entryFunction module entry
  let result ← entryResultKind entry function
  let params := function.params.map (·.snd)
  unless params.size == args.size do
    throw s!"entry {entry} expects {params.size} arguments, got {args.size}"
  let arguments ← (params.toList.zip args.toList).mapM fun (kind, value) =>
    argumentJsonWithRuntime runtime kind value
  let imports ← module.imports.toList.mapM importJson
  let initialRuntime ← runtimeJson runtime
  return Json.mkObj [
    ("fixture", artifactName),
    ("sourceEntry", sourceEntry.toString),
    ("entry", entry.toString),
    ("result", abiKindName result),
    ("params", Json.arr (params.map fun kind => (abiKindName kind : Json))),
    ("arguments", Json.arr arguments.toArray),
    ("imports", Json.arr imports.toArray),
    ("initialRuntime", initialRuntime)]

end Fir.Wasm.Emit.Manifest
