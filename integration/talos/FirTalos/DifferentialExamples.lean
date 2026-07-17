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
  abiDefaultCaseProgram,
  abiMutationProgram,
  abiObjectMutationProgram,
  abiTagMutationProgram,
  rcProgram,
  persistentRcProgram,
  deletedProgram,
  abiResetReuseProgram,
  abiSharedResetProgram]

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

#guard relatedReturn? (runDifferential abiMutationProgram `main #[])
  (.scalar (.uint64 66))

#guard relatedReturn? (runDifferential abiObjectMutationProgram `main #[])
  (.object (.tagged 88))

#guard relatedReturn? (runDifferential abiTagMutationProgram `main #[])
  (.object (.tagged 99))

#guard relatedReturn? (runDifferential rcProgram `main #[])
  (.scalar (.uint8 0))

#guard relatedReturn? (runDifferential persistentRcProgram `main #[])
  (.scalar (.uint8 0))

#guard relatedSourceFault? (runDifferential deletedProgram `main #[])
  (.deadObject 0)

#guard relatedReturn? (runDifferential abiResetReuseProgram `main #[])
  (.object (.tagged 71))

#guard relatedReturn? (runDifferential abiSharedResetProgram `main #[])
  (.object (.tagged 81))

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

def projectionInfo : LCNF.CtorInfo :=
  { name := `Projection.mk, cidx := 3, size := 0, usize := 1, ssize := 8 }

def abiUSizeProjectionProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] usizeType (.code <|
      .let (letDecl p objType (.ctor projectionInfo #[])) <|
      .let (letDecl r usizeType (.uproj 0 p)) <|
      .return r)] }

#guard supportedProgram abiUSizeProjectionProgram

#guard relatedReturn? (runDifferential abiUSizeProjectionProgram `main #[])
  (.usize 0)

/-- Constructor allocation reserves scalar storage but does not initialize a
typed scalar field. Until the W5 mutation slice supplies `sset`, this fixture
checks that a compiler-shaped `sproj` source fault is reproduced exactly. -/
def abiScalarProjectionFaultProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code <|
      .let (letDecl p objType (.ctor projectionInfo #[])) <|
      .let (letDecl r u64Type (.sproj 1 0 p)) <|
      .return r)] }

#guard supportedProgram abiScalarProjectionFaultProgram

#guard relatedSourceFault? (runDifferential abiScalarProjectionFaultProgram `main #[])
  (.scalarFieldMissing 1 0)

def abiBoxRoundtripProgram (value : UInt64) : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code <|
      .let (letDecl s u64Type (.lit (.uint64 value))) <|
      .let (letDecl b tobjectType (.box u64Type s)) <|
      .let (letDecl r u64Type (.unbox b)) <|
      .return r)] }

#guard supportedProgram (abiBoxRoundtripProgram 44)

#guard relatedReturn? (runDifferential (abiBoxRoundtripProgram 44) `main #[])
  (.scalar (.uint64 44))

def differentialMaxUInt64 : UInt64 := 18446744073709551615

#guard relatedReturn?
  (runDifferential (abiBoxRoundtripProgram differentialMaxUInt64) `main #[])
  (.scalar (.uint64 differentialMaxUInt64))

def abiHeapBoxProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl s u64Type (.lit (.uint64 differentialMaxUInt64))) <|
      .let (letDecl b tobjectType (.box u64Type s)) <|
      .return b)] }

#guard supportedProgram abiHeapBoxProgram

#guard (runDifferential abiHeapBoxProgram `main #[]).isRelated

#guard relatedReachableHeapSize? (runDifferential abiHeapBoxProgram `main #[]) 1

def abiIsSharedTaggedProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u8Type (.code <|
      .let (letDecl x tobjectType (.lit (.nat 9))) <|
      .let (letDecl r u8Type (.isShared x)) <|
      .return r)] }

#guard supportedProgram abiIsSharedTaggedProgram

#guard relatedReturn? (runDifferential abiIsSharedTaggedProgram `main #[])
  (.scalar (.uint8 1))

def abiIsSharedUniqueProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u8Type (.code <|
      .let (letDecl p objType (.ctor projectionInfo #[])) <|
      .let (letDecl r u8Type (.isShared p)) <|
      .return r)] }

#guard supportedProgram abiIsSharedUniqueProgram

#guard relatedReturn? (runDifferential abiIsSharedUniqueProgram `main #[])
  (.scalar (.uint8 0))

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
