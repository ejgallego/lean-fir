import FirTalos.Differential
import Fir.Wasm.Examples

namespace FirTalos

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples

def relatedReturn? (result : DifferentialResult) (expected : Value) : Bool :=
  match result with
  | .related source (.returned target _) =>
      source.outcome == .returned expected && target == expected
  | _ => false

def relatedSourceFault? (result : DifferentialResult) (expected : RuntimeFault) : Bool :=
  match result with
  | .related source (.sourceFault target _) =>
      source.outcome == .fault expected && target == expected
  | _ => false

def relatedReachableHeapSize? (result : DifferentialResult) (expected : Nat) : Bool :=
  match result with
  | .related source target =>
      match target.toSource? with
      | some target =>
          (reachableHeap source.heap source.roots).length == expected &&
            (reachableHeap target.heap target.roots).length == expected
      | none => false
  | _ => false

def differentialCorpus : List Fir.LeanIR.ImpureProgram := [
  abiLiteralProgram,
  abiCtorProjectionProgram,
  abiCaseProgram,
  abiDefaultCaseProgram]

#guard differentialCorpus.all fun program =>
  (runDifferential program `main #[]).isRelated

#guard relatedReturn? (runDifferential abiLiteralProgram `main #[])
  (.object (.tagged 42))

#guard relatedReturn? (runDifferential abiCtorProjectionProgram `main #[])
  (.object (.tagged 7))

#guard relatedReturn? (runDifferential abiCaseProgram `main #[])
  (.object (.tagged 1))

#guard relatedReturn? (runDifferential abiDefaultCaseProgram `main #[])
  (.object (.tagged 5))

def abiStringProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] objType (.code <|
      .let (letDecl x objType (.lit (.str "reachable"))) (.return x))] }

#guard supportedProgram abiStringProgram

#guard (runDifferential abiStringProgram `main #[]).isRelated

#guard relatedReachableHeapSize? (runDifferential abiStringProgram `main #[]) 1

def a : FVarId := ⟨`a⟩
def b : FVarId := ⟨`b⟩

def abiFirstArgumentProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param a tobjectType, param b tobjectType]
      tobjectType (.code (.return a))] }

#guard supportedProgram abiFirstArgumentProgram

#guard relatedReturn?
  (runDifferential abiFirstArgumentProgram `main
    #[.object (.tagged 11), .object (.tagged 22)])
  (.object (.tagged 11))

#guard match runDifferential abiFirstArgumentProgram `main
    #[.object (.heap 0), .object (.tagged 22)] with
  | .preparationFailure _ .argumentEncoding message => !message.isEmpty
  | _ => false

def abiProjectionFaultProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 7))) <|
      .let (letDecl y tobjectType (.lit (.nat 8))) <|
      .let (letDecl p objType (.ctor pairInfo #[.fvar x, .fvar y])) <|
      .let (letDecl r tobjectType (.oproj 2 p)) <|
      .return r)] }

#guard supportedProgram abiProjectionFaultProgram

#guard relatedSourceFault? (runDifferential abiProjectionFaultProgram `main #[])
  (.objectFieldOutOfBounds 2 2)

#guard relatedReachableHeapSize?
  (runDifferential abiCtorProjectionProgram `main #[]) 0

/-- The original fixture is intentionally rejected under the existing
`FIR-BUG-wasm-none-object-nat-fixture` card after its source run is recorded. -/
def malformedNatFixtureIsExplained : Bool :=
  match runDifferential literalProgram `main #[] with
  | .preparationFailure source .loweringAndValidation message =>
      source.outcome == .returned (.object (.tagged 42)) && !message.isEmpty
  | _ => false

#guard malformedNatFixtureIsExplained

def mismatchEvidenceIsSpecific : Bool :=
  let source : Observation := {
    outcome := .returned (.object (.tagged 1)), heap := [], world := 0, trace := #[] }
  let target : TargetObservation := .returned (.object (.tagged 2)) {}
  match compareObservations source target with
  | .mismatch _ _ differences =>
      differences.size == 1 && differences[0]?.any (·.startsWith "outcome:")
  | _ => false

#guard mismatchEvidenceIsSpecific

end FirTalos
