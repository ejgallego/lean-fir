import Fir.Validation.Protocol

namespace Fir.Validation.Corpus

/-!
Source-level fixtures shared by the native oracle and candidate backends.

The functions in `Source` are deliberately small, but each non-trivial helper is
marked `noinline` so the final impure LCNF retains the operation that its case is
intended to exercise.  The native oracle calls these exact declarations; expected
answers are not stored in the corpus.
-/

namespace Source

def litNat : Nat :=
  42

def idNat (x : Nat) : Nat :=
  x

def branchNat (b : Bool) : Nat :=
  if b then 1 else 0

def pairFirst (p : Nat × Nat) : Nat :=
  p.1

@[noinline]
def directTarget (x : Nat) : Nat :=
  x

def directCall (x : Nat) : Nat :=
  directTarget x

@[noinline]
def firstNat (x _y : Nat) : Nat :=
  x

@[noinline]
def applyNat (f : Nat → Nat) (x : Nat) : Nat :=
  f x

def capturedPartial (captured x : Nat) : Nat :=
  applyNat (firstNat captured) x

@[noinline]
def lastOr (fallback : Nat) : List Nat → Nat
  | [] => fallback
  | x :: xs => lastOr x xs

def recursiveTraversal (xs : List Nat) : Nat :=
  lastOr 0 xs

def localTailControl (xs : List Nat) : Nat :=
  let rec loop : List Nat → Nat → Nat
    | [], acc => acc
    | x :: tail, _ => loop tail x
  loop xs 0

def largeNat : Nat :=
  18446744073709551616

def idNatList (xs : List Nat) : List Nat :=
  xs

def idString (value : String) : String :=
  value

def maxUInt64 : UInt64 :=
  18446744073709551615

@[noinline]
def polyId (α : Type) (value : α) : α :=
  value

def boxedUInt32 (value : UInt32) : UInt32 :=
  polyId UInt32 value

structure PackedPoint where
  x : USize
  y : UInt32

@[noinline]
def PackedPoint.setX (point : PackedPoint) : PackedPoint :=
  { point with x := 1 }

def packedPreserve (y : UInt32) : UInt32 :=
  (PackedPoint.setX { x := 0, y }).y

def tupleRotate (value : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (value.2.2, value.1, value.2.1)

def idUSize (value : USize) : USize :=
  value

end Source

/-- Stable provenance for a fixture, suitable for carrying into backend reports. -/
structure Provenance where
  suite : String
  path : String
  revision : String := ""
  note : String := ""
  deriving Inhabited, BEq, Repr, Lean.ToJson, Lean.FromJson

def firProvenance (note : String) : Provenance := {
  suite := "fir"
  path := "Fir/Validation/Corpus.lean"
  note }

def leanCompileProvenance (path note : String) : Provenance := {
  suite := "lean-tests-compile"
  path
  revision := "b4812ae53eea93439ad5dce5a5c26591c31cb697"
  note }

/-- A source case and the backend-neutral metadata needed to run it. -/
structure Case where
  id : String
  entry : Lean.Name
  /-- Source helpers that must be compiled with the entry instead of treated as imported externs. -/
  dependencies : Array Lean.Name := #[]
  args : Array ValidationDatum := #[]
  argSchemas : Array ValidationSchema := #[]
  resultSchema : ValidationSchema
  native : Unit → ValidationDatum
  tags : Array String := #[]
  fuel : Nat := 10000
  requiredLcnfForms : Array String := #[]
  provenance : Provenance := firProvenance "FIR validation fixture"

/-- Closure-free case metadata consumed by runners and future backend adapters. -/
structure CaseDescriptor where
  version : Nat := protocolVersion
  id : String
  entry : String
  dependencies : Array String
  args : Array ValidationDatum
  argSchemas : Array ValidationSchema
  resultSchema : ValidationSchema
  tags : Array String
  fuel : Nat
  requiredLcnfForms : Array String
  provenance : Provenance
  deriving Inhabited, BEq, Repr, Lean.ToJson, Lean.FromJson

def Case.descriptor (validationCase : Case) : CaseDescriptor := {
  id := validationCase.id
  entry := toString validationCase.entry
  dependencies := validationCase.dependencies.map toString
  args := validationCase.args
  argSchemas := validationCase.argSchemas
  resultSchema := validationCase.resultSchema
  tags := validationCase.tags
  fuel := validationCase.fuel
  requiredLcnfForms := validationCase.requiredLcnfForms
  provenance := validationCase.provenance }

private def natListDatum (xs : List Nat) : ValidationDatum :=
  .seq (xs.toArray.map .nat)

def cases : Array Case := #[
  { id := "lit-nat"
    entry := ``Source.litNat
    resultSchema := .nat
    native := fun _ => .nat Source.litNat
    tags := #["quick", "literal"]
    requiredLcnfForms := #["lit", "return"] },
  { id := "id-nat"
    entry := ``Source.idNat
    args := #[.nat 42]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.idNat 42)
    tags := #["quick", "borrowed"]
    requiredLcnfForms := #["inc", "return"] },
  { id := "branch-nat"
    entry := ``Source.branchNat
    args := #[.bool true]
    argSchemas := #[.bool]
    resultSchema := .nat
    native := fun _ => .nat (Source.branchNat true)
    tags := #["quick", "control-flow"]
    requiredLcnfForms := #["cases", "lit", "return"] },
  { id := "branch-nat-false"
    entry := ``Source.branchNat
    args := #[.bool false]
    argSchemas := #[.bool]
    resultSchema := .nat
    native := fun _ => .nat (Source.branchNat false)
    tags := #["quick", "control-flow", "boundary"]
    requiredLcnfForms := #["cases", "lit", "return"] },
  { id := "pair-first"
    entry := ``Source.pairFirst
    args := #[.ctor "Prod.mk" 0 #[.nat 41, .nat 42]]
    argSchemas := #[.ctor "Prod.mk" 0 #[.nat, .nat]]
    resultSchema := .nat
    native := fun _ => .nat (Source.pairFirst (41, 42))
    tags := #["quick", "constructor", "projection"]
    requiredLcnfForms := #["oproj", "inc", "return"] },
  { id := "direct-call"
    entry := ``Source.directCall
    dependencies := #[``Source.directTarget]
    args := #[.nat 41]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.directCall 41)
    tags := #["quick", "call"]
    requiredLcnfForms := #["fap", "return"] },
  { id := "captured-partial"
    entry := ``Source.capturedPartial
    dependencies := #[``Source.firstNat, ``Source.applyNat]
    args := #[.nat 40, .nat 2]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.capturedPartial 40 2)
    tags := #["quick", "closure", "partial-application"]
    requiredLcnfForms := #["pap", "fap", "return"] },
  { id := "recursive-traversal"
    entry := ``Source.recursiveTraversal
    dependencies := #[``Source.lastOr]
    args := #[natListDatum [10, 20, 12]]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recursiveTraversal [10, 20, 12])
    tags := #["quick", "constructor", "recursion"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"] },
  { id := "recursive-empty"
    entry := ``Source.recursiveTraversal
    dependencies := #[``Source.lastOr]
    args := #[natListDatum []]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recursiveTraversal [])
    tags := #["quick", "constructor", "recursion", "boundary"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"] },
  { id := "local-tail"
    entry := ``Source.localTailControl
    dependencies := #[`Fir.Validation.Corpus.Source.localTailControl.loop]
    args := #[natListDatum [10, 20, 42]]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.localTailControl [10, 20, 42])
    tags := #["quick", "tail-control"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"] },
  { id := "large-nat"
    entry := ``Source.largeNat
    resultSchema := .nat
    native := fun _ => .nat Source.largeNat
    tags := #["quick", "literal", "boundary", "heap"]
    requiredLcnfForms := #["lit", "return"]
    provenance := firProvenance "Natural larger than the tagged immediate range" },
  { id := "nat-list-roundtrip"
    entry := ``Source.idNatList
    args := #[natListDatum [0, Source.largeNat, 42]]
    argSchemas := #[.seq .nat]
    resultSchema := .seq .nat
    native := fun _ => natListDatum (Source.idNatList [0, Source.largeNat, 42])
    tags := #["quick", "constructor", "boundary", "heap", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    provenance := firProvenance "Recursive value round-trip containing a heap natural" },
  { id := "unicode-string-roundtrip"
    entry := ``Source.idString
    args := #[.string "hello α_world_β"]
    argSchemas := #[.string]
    resultSchema := .string
    native := fun _ => .string (Source.idString "hello α_world_β")
    tags := #["quick", "string", "unicode", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    provenance := leanCompileProvenance "tests/compile/str.lean"
      "Unicode fixture adapted to a pure source-level identity" },
  { id := "uint64-max"
    entry := ``Source.maxUInt64
    resultSchema := .bits 64
    native := fun _ => .bits 64 Source.maxUInt64
    tags := #["quick", "scalar", "boundary"]
    requiredLcnfForms := #["lit", "return"]
    provenance := leanCompileProvenance "tests/compile/uint_fold.lean"
      "Maximum-width UInt64 literal" },
  { id := "boxed-uint32"
    entry := ``Source.boxedUInt32
    dependencies := #[``Source.polyId]
    args := #[.bits 32 4294967295]
    argSchemas := #[.bits 32]
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat (Source.boxedUInt32 4294967295).toNat)
    tags := #["quick", "scalar", "boxing", "polymorphism", "boundary"]
    requiredLcnfForms := #["box", "unbox", "fap", "return"]
    provenance := leanCompileProvenance "tests/compile/typeFormerPolymorphism.lean"
      "Unboxed scalar passed through a noinline polymorphic identity" },
  { id := "packed-preserve"
    entry := ``Source.packedPreserve
    dependencies := #[``Source.PackedPoint.setX]
    args := #[.bits 32 4294967295]
    argSchemas := #[.bits 32]
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat (Source.packedPreserve 4294967295).toNat)
    tags := #["quick", "scalar", "packed-layout", "update", "boundary"]
    requiredLcnfForms := #["ctor", "uset", "sset", "sproj", "fap", "return"]
    provenance := leanCompileProvenance "tests/compile/uset.lean"
      "Packed USize/UInt32 structure update preserving the scalar field" },
  { id := "tuple-rotate"
    entry := ``Source.tupleRotate
    args := #[.ctor "Prod.mk" 0 #[.nat 1, .ctor "Prod.mk" 0 #[.nat 2, .nat 3]]]
    argSchemas := #[.ctor "Prod.mk" 0 #[.nat, .ctor "Prod.mk" 0 #[.nat, .nat]]]
    resultSchema := .ctor "Prod.mk" 0 #[.nat, .ctor "Prod.mk" 0 #[.nat, .nat]]
    native := fun _ =>
      let result := Source.tupleRotate (1, 2, 3)
      .ctor "Prod.mk" 0 #[.nat result.1, .ctor "Prod.mk" 0 #[.nat result.2.1, .nat result.2.2]]
    tags := #["quick", "constructor", "projection", "allocation"]
    requiredLcnfForms := #["oproj", "ctor", "return"]
    provenance := leanCompileProvenance "tests/compile/tuple.lean"
      "Tuple projection/allocation without IO" },
  { id := "usize-roundtrip"
    entry := ``Source.idUSize
    args := #[.usize 42]
    argSchemas := #[.usize]
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat (Source.idUSize 42).toNat)
    tags := #["quick", "usize", "roundtrip"]
    requiredLcnfForms := #["return"]
    provenance := firProvenance "Portable USize fixture below the Wasm32 boundary" }
]

def findCase? (id : String) : Option Case :=
  cases.find? (·.id == id)

def caseIds : Array String :=
  cases.map (·.id)

def descriptors : Array CaseDescriptor :=
  cases.map Case.descriptor

end Fir.Validation.Corpus
