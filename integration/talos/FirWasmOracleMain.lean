import FirTalos.Differential
import Fir.Wasm.Emit.Examples

open Fir.LeanIR.Impure
open Fir.Wasm.Emit.Examples
open FirTalos
open Lean

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

def heapObjectJson : HeapObject → Json
  | .ctor object =>
      Json.mkObj [
        ("kind", "ctor"),
        ("tag", s!"{object.tag}"),
        ("objectFields", Json.arr (object.objectFields.map valueJson)),
        ("usizeFields", Json.arr (object.usizeFields.map fun value => s!"{value}")),
        ("scalarFields", Json.arr (object.scalarFields.toArray.map scalarFieldJson))]
  | .closure function arity fixed =>
      Json.mkObj [
        ("kind", "closure"),
        ("function", function.toString),
        ("arity", arity),
        ("fixed", Json.arr (fixed.map valueJson))]
  | .boxed type value =>
      Json.mkObj [("kind", "boxed"), ("type", s!"{repr type}"), ("value", valueJson value)]
  | .string value => Json.mkObj [("kind", "string"), ("value", value)]
  | .natural value => Json.mkObj [("kind", "natural"), ("value", s!"{value}")]
  | .integer value => Json.mkObj [("kind", "integer"), ("value", s!"{value}")]
  | .byteArray value =>
      Json.mkObj [("kind", "byteArray"), ("value", Json.arr (value.map fun byte => byte.toNat))]
  | .opaque typeName => Json.mkObj [("kind", "opaque"), ("typeName", typeName.toString)]

def heapCellJson (entry : Location × HeapCell) : Json :=
  Json.mkObj [
    ("location", entry.fst),
    ("rc", entry.snd.rc),
    ("persistent", entry.snd.persistent),
    ("live", entry.snd.live),
    ("object", heapObjectJson entry.snd.object)]

def outcomeJson : Outcome → Json
  | .returned value => Json.mkObj [("kind", "returned"), ("value", valueJson value)]
  | .fault fault => Json.mkObj [("kind", "fault"), ("fault", s!"{repr fault}")]

def externalEventJson (event : ExternalEvent) : Json :=
  Json.mkObj [
    ("name", event.name.toString),
    ("args", Json.arr (event.args.map valueJson)),
    ("result", valueJson event.result)]

def comparableObservationJson (observation : Observation) : Json :=
  let comparable := comparableObservation observation
  Json.mkObj [
    ("outcome", outcomeJson comparable.outcome),
    ("reachableHeap", Json.arr (comparable.reachableHeap.toArray.map heapCellJson)),
    ("world", comparable.world),
    ("trace", Json.arr (comparable.trace.map externalEventJson))]

def oracleObservation (fixture : CorpusFixture) : Except String Observation :=
  match runDifferential fixture.program `main #[] with
  | .related source _ => .ok source
  | result => .error s!"W3 oracle rejected {fixture.name}: {result.describe}"

def emitOracle (fixture : CorpusFixture) (outputDirectory : System.FilePath) : IO Unit := do
  let observation ← IO.ofExcept (oracleObservation fixture)
  IO.FS.createDirAll outputDirectory
  let path := outputDirectory / s!"{fixture.name}.expected.json"
  IO.FS.writeFile path (comparableObservationJson observation).compress
  IO.println s!"{fixture.name}: wrote live W3 observation to {path}"

def usage : String :=
  "usage: fir-wasm-oracle all <output-directory>"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["all", outputDirectory] =>
        for fixture in initialFixtures do
          emitOracle fixture outputDirectory
        return 0
    | _ =>
        IO.eprintln usage
        return 2
  catch error =>
    IO.eprintln error.toString
    return 1
