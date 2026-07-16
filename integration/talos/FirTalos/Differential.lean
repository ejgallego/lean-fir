import FirTalos.Runtime
import Fir.LeanIR.PassCorrectness
import Fir.Wasm.WellFormed
import Interpreter.Wasm.Semantics

namespace FirTalos

open Fir.Wasm
open Fir.LeanIR.Impure

/-- A decoded target outcome, retaining FIR runtime state whenever Talos returns one. -/
inductive TargetObservation where
  | returned (value : Value) (runtime : RuntimeState)
  | sourceFault (fault : RuntimeFault) (runtime : RuntimeState)
  | targetTrap (failure : TargetFailure) (runtime : RuntimeState)
  | unexpectedTrap (message : String) (runtime : RuntimeState)
  | invalidWasm (message : String)
  | outOfFuel
  | unexpectedResults (values : Array Value) (runtime : RuntimeState)
  | thrown (tag : Nat) (args : List Wasm.Value) (runtime : RuntimeState)
  deriving Inhabited, BEq

def TargetObservation.runtime? : TargetObservation → Option RuntimeState
  | .returned _ runtime
  | .sourceFault _ runtime
  | .targetTrap _ runtime
  | .unexpectedTrap _ runtime
  | .unexpectedResults _ runtime
  | .thrown _ _ runtime => some runtime
  | .invalidWasm _ | .outOfFuel => none

/-- Only decoded returns and source faults inhabit FIR's source observation type. -/
def TargetObservation.toSource? : TargetObservation → Option Observation
  | .returned value runtime => some {
      outcome := .returned value
      heap := runtime.heap
      world := runtime.world
      trace := runtime.trace }
  | .sourceFault fault runtime => some {
      outcome := .fault fault
      heap := runtime.heap
      world := runtime.world
      trace := runtime.trace }
  | _ => none

private def runtimeSummary (runtime : RuntimeState) : String :=
  s!"heap cells={runtime.heap.length}, world={runtime.world}, trace events={runtime.trace.size}"

def TargetObservation.describe : TargetObservation → String
  | .returned value runtime => s!"returned {repr value}; {runtimeSummary runtime}"
  | .sourceFault fault runtime => s!"source fault {repr fault}; {runtimeSummary runtime}"
  | .targetTrap failure runtime => s!"target trap {repr failure}; {runtimeSummary runtime}"
  | .unexpectedTrap message runtime =>
      s!"unstructured Wasm trap {repr message}; {runtimeSummary runtime}"
  | .invalidWasm message => s!"invalid Wasm: {message}"
  | .outOfFuel => "Talos exhausted its runner fuel"
  | .unexpectedResults values runtime =>
      s!"unexpected decoded result vector {repr values}; {runtimeSummary runtime}"
  | .thrown tag args runtime =>
      s!"uncaught Wasm exception tag {tag}, args {repr args}; {runtimeSummary runtime}"

private def heapLocation? : Value → Option Location
  | .object (.heap location) => some location
  | _ => none

private def childLocations (heap : Heap) (location : Location) : List Location :=
  match findCell? heap location with
  | some cell => cell.object.ownedValues.toList.filterMap heapLocation?
  | none => []

private partial def closeReachable (heap : Heap) :
    List Location → List Location → List Location
  | [], seen => seen
  | location :: pending, seen =>
      if seen.contains location then
        closeReachable heap pending seen
      else
        closeReachable heap (childLocations heap location ++ pending) (location :: seen)

/-- Heap locations transitively reachable from observable object roots. -/
def reachableLocations (heap : Heap) (roots : List Value) : List Location :=
  closeReachable heap (roots.filterMap heapLocation?) []

/-- Canonical reachable heap slice, kept in the runtime heap's deterministic order. -/
def reachableHeap (heap : Heap) (roots : List Value) : Heap :=
  let reachable := reachableLocations heap roots
  heap.filter fun entry => reachable.contains entry.fst

def missingReachableLocations (heap : Heap) (roots : List Value) : List Location :=
  (reachableLocations heap roots).filter fun location =>
    (findCell? heap location).isNone

structure ComparableObservation where
  outcome : Outcome
  reachableHeap : Heap
  world : Nat
  trace : Array ExternalEvent
  deriving Inhabited, BEq

def comparableObservation (observation : Observation) : ComparableObservation :=
  { outcome := observation.outcome
    reachableHeap := reachableHeap observation.heap observation.roots
    world := observation.world
    trace := observation.trace }

private def heapObjectSummary : HeapObject → String
  | .ctor object =>
      s!"ctor(tag={object.tag}, objects={repr object.objectFields}, usizes={
        repr object.usizeFields}, scalars={repr object.scalarFields})"
  | .closure function arity fixed =>
      s!"closure(function={function}, arity={arity}, fixed={repr fixed})"
  | .boxed type value => s!"boxed(type={repr type}, value={repr value})"
  | .string value => s!"string({repr value})"
  | .natural value => s!"natural({value})"
  | .integer value => s!"integer({value})"
  | .byteArray value => s!"byteArray({repr value})"
  | .opaque typeName => s!"opaque({typeName})"

private def heapSummary (heap : Heap) : String :=
  String.intercalate ", " <| heap.map fun (location, cell) =>
    s!"{location}:(rc={cell.rc}, persistent={cell.persistent}, live={cell.live}, object={
      heapObjectSummary cell.object})"

/-- Reproducible field-level evidence when two executable observations disagree. -/
def observationDifferences (source target : Observation) : Array String := Id.run do
  let mut differences := #[]
  if source.outcome != target.outcome then
    differences := differences.push
      s!"outcome: source={repr source.outcome}, target={repr target.outcome}"
  if source.world != target.world then
    differences := differences.push
      s!"world: source={source.world}, target={target.world}"
  if source.trace != target.trace then
    differences := differences.push
      s!"trace: source={repr source.trace}, target={repr target.trace}"
  let sourceHeap := reachableHeap source.heap source.roots
  let targetHeap := reachableHeap target.heap target.roots
  let sourceMissing := missingReachableLocations source.heap source.roots
  let targetMissing := missingReachableLocations target.heap target.roots
  if !sourceMissing.isEmpty || !targetMissing.isEmpty then
    differences := differences.push s!"dangling reachable locations: source={
      repr sourceMissing}, target={repr targetMissing}"
  if sourceHeap != targetHeap then
    differences := differences.push s!"reachable heap: source locations={
      repr (reachableLocations source.heap source.roots)}, target locations={
      repr (reachableLocations target.heap target.roots)}, source cells={
      sourceHeap.length} [{heapSummary sourceHeap}], target cells={targetHeap.length} [{
      heapSummary targetHeap}]"
  return differences

inductive DifferentialStage where
  | loweringAndValidation
  | adaptation
  | hostResolution
  | entryResolution
  | argumentEncoding
  deriving Inhabited, BEq, Repr

inductive DifferentialResult where
  | related (source : Observation) (target : TargetObservation)
  | mismatch (source : Observation) (target : TargetObservation)
      (differences : Array String)
  | targetFailure (source : Observation) (target : TargetObservation)
  | preparationFailure (source : Observation) (stage : DifferentialStage)
      (message : String)
  | sourceOutOfFuel
  deriving Inhabited, BEq

def DifferentialResult.isRelated : DifferentialResult → Bool
  | .related .. => true
  | _ => false

def DifferentialResult.describe : DifferentialResult → String
  | .related source target =>
      s!"related observations: source outcome={repr source.outcome}; target {target.describe}"
  | .mismatch _ target differences =>
      s!"semantic mismatch: {String.intercalate "; " differences.toList}; target {target.describe}"
  | .targetFailure source target =>
      s!"backend failure after source outcome {repr source.outcome}: {target.describe}"
  | .preparationFailure source stage message =>
      s!"preparation failure at {repr stage} after source outcome {repr source.outcome}: {message}"
  | .sourceOutOfFuel => "FIR interpreter exhausted its runner fuel"

private def resolverErrorMessage : ResolverError → String
  | .invalidModule error => s!"invalid FIR symbolic module: {repr error}"
  | .malformedRuntimeImport index => s!"malformed runtime import at index {index}"
  | .unsupportedRuntimeImport index operation =>
      s!"unsupported runtime import at index {index}: {operation.stem}"
  | .externalImport index declaration =>
      s!"unsupported external import at index {index}: {declaration}"

def observeTarget (results : Array AbiKind) :
    Wasm.Result RuntimeHost → TargetObservation
  | .Success physical store =>
      match decodeArgs store.host.handles results physical with
      | .ok #[value] => .returned value store.host.runtime
      | .ok values => .unexpectedResults values store.host.runtime
      | .error failure => .targetTrap failure store.host.runtime
  | .Trap store message =>
      match store.host.trap? with
      | some (.source fault) => .sourceFault fault store.host.runtime
      | some (.target failure) => .targetTrap failure store.host.runtime
      | none => .unexpectedTrap message store.host.runtime
  | .Invalid message => .invalidWasm message
  | .OutOfFuel => .outOfFuel
  | .Thrown tag args store => .thrown tag args store.host.runtime

/-- A successful singleton ABI decode determines the successful target observation. -/
theorem observeTarget_success_singleton
    {results : Array AbiKind} {physical : List Wasm.Value}
    {store : Wasm.Store RuntimeHost} {value : Value}
    (decoded : decodeArgs store.host.handles results physical = .ok #[value]) :
    observeTarget results (.Success physical store) =
      .returned value store.host.runtime := by
  rw [observeTarget]
  rw [decoded]
  rfl

def compareObservations (source : Observation) (target : TargetObservation) :
    DifferentialResult :=
  match target.toSource? with
  | none => .targetFailure source target
  | some targetSource =>
      let differences := observationDifferences source targetSource
      if differences.isEmpty then
        .related source target
      else
        .mismatch source target differences

def sourceFuel : Nat := 1000
def targetFuel : Nat := 1000

private def requiresInitialHeap : Value → Bool
  | .object (.heap _) | .reuseToken (some _) => true
  | _ => false

/--
Run final impure LCNF and its generated Talos module from the same entry and
semantic arguments, then compare outcome, world, trace, and reachable heap.
-/
def runDifferential (program : Fir.LeanIR.ImpureProgram) (entry : Lean.Name)
    (args : Array Value) : DifferentialResult :=
  match Fir.LeanIR.Impure.runProgram sourceFuel rejectExternals program entry args with
  | .outOfFuel _ => .sourceOutOfFuel
  | .done sourceObservation =>
      if args.any requiresInitialHeap then
        .preparationFailure sourceObservation .argumentEncoding
          "heap-backed entry arguments require an explicit initial runtime"
      else
        match Fir.Wasm.lowerSupported program with
        | .error error =>
            .preparationFailure sourceObservation .loweringAndValidation s!"{repr error}"
        | .ok sourceModule =>
            match adapt sourceModule with
            | .error error =>
                .preparationFailure sourceObservation .adaptation s!"{repr error}"
            | .ok adapted =>
                match resolveHosts sourceModule with
                | .error error =>
                    .preparationFailure sourceObservation .hostResolution
                      (resolverErrorMessage error)
                | .ok hosts =>
                    match sourceModule.functions.findIdx? (·.name == entry) with
                    | none =>
                        .preparationFailure sourceObservation .entryResolution
                          s!"entry {entry} is not a lowered function"
                    | some functionIndex =>
                        match sourceModule.functions[functionIndex]? with
                        | none =>
                            .preparationFailure sourceObservation .entryResolution
                              s!"lowered entry index {functionIndex} is out of bounds"
                        | some function =>
                            let paramKinds := function.params.map (·.snd)
                            match encodeResults {} paramKinds args with
                            | .error failure =>
                                .preparationFailure sourceObservation .argumentEncoding
                                  s!"{repr failure}"
                            | .ok (handles, physicalArgs) =>
                                let initial := adapted.wasmModule.initialStore (α := RuntimeHost)
                                let initial := { initial with host := { handles } }
                                let targetResult := Wasm.run targetFuel adapted.wasmModule
                                  (sourceModule.imports.size + functionIndex) initial
                                  physicalArgs.reverse hosts.env
                                compareObservations sourceObservation
                                  (observeTarget function.results targetResult)

end FirTalos
