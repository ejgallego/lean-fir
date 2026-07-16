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

inductive Assoc where
  | atom (value : Nat)
  | node (left right : Assoc)

namespace Assoc

@[noinline] partial def reassoc : Assoc → Assoc
  | .node (.node a b) c => reassoc (.node a (.node b c))
  | value => value

end Assoc

@[noinline]
def applyCaptureList (f : Nat → List Nat) (y : Nat) : List Nat :=
  f y

def capture17List
    (x01 x02 x03 x04 x05 x06 x07 x08 x09 : Nat)
    (x10 x11 x12 x13 x14 x15 x16 x17 : Nat)
    (y : Nat) : List Nat :=
  applyCaptureList
    (fun z =>
      [x01, x02, x03, x04, x05, x06, x07, x08, x09,
       x10, x11, x12, x13, x14, x15, x16, x17, z])
    y

set_option genInjectivity false in
structure BigCtor where
  f01 : Nat := 0
  f02 : Nat := 0
  f03 : Nat := 0
  f04 : Nat := 0
  f05 : Nat := 0
  f06 : Nat := 0
  f07 : Nat := 0
  f08 : Nat := 0
  f09 : Nat := 0
  f10 : Nat := 0
  f11 : Nat := 0
  f12 : Nat := 0
  f13 : Nat := 0
  f14 : Nat := 0
  f15 : Nat := 0
  f16 : Nat := 0
  f17 : Nat := 0
  f18 : Nat := 0
  f19 : Nat := 0
  f20 : Nat := 0
  f21 : Nat := 0
  f22 : Nat := 0
  f23 : Nat := 0
  f24 : Nat := 0
  f25 : Nat := 0
  f26 : Nat := 0
  f27 : Nat := 0
  f28 : Nat := 0
  f29 : Nat := 0
  f30 : Nat := 0
  f31 : Nat := 0
  f32 : Nat := 0
  f33 : Nat := 0
  f34 : Nat := 0
  f35 : Nat := 0
  f36 : Nat := 0
  f37 : Nat := 0
  f38 : Nat := 0
  f39 : Nat := 0
  f40 : Nat := 0
  f41 : Nat := 0
  f42 : Nat := 0
  f43 : Nat := 0
  f44 : Nat := 0
  f45 : Nat := 0
  f46 : Nat := 0
  f47 : Nat := 0
  f48 : Nat := 0
  f49 : Nat := 0
  f50 : Nat := 0
  f51 : Nat := 0
  f52 : Nat := 0
  f53 : Nat := 0
  f54 : Nat := 0
  f55 : Nat := 0
  f56 : Nat := 0
  f57 : Nat := 0
  f58 : Nat := 0
  f59 : Nat := 0
  f60 : Nat := 0
  f61 : Nat := 0
  f62 : Nat := 0
  f63 : Nat := 0
  f64 : Nat := 0
  f65 : Nat := 0
  f66 : Nat := 0
  f67 : Nat := 0
  f68 : Nat := 0
  f69 : Nat := 0
  f70 : Nat := 0

@[noinline]
def mkBigCtor (x : Nat) : BigCtor :=
  { f70 := x }

def bigCtorField (x : Nat) : Nat :=
  (mkBigCtor x).f70

inductive ScalarChoice where
  | first
  | second
  | third

@[noinline]
def selectScalarChoice : ScalarChoice → Nat
  | .first => 10
  | .second => 20
  | .third => 30

def scalarCasesInternal : Nat :=
  selectScalarChoice .third

@[noinline]
def idInt (value : Int) : Int :=
  value

@[noinline]
def addNat (left right : Nat) : Nat :=
  left + right

@[noinline]
def idByteArray (value : ByteArray) : ByteArray :=
  value

@[noinline]
def byteArraySize (value : ByteArray) : Nat :=
  value.size

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
  /-- Forms that this fixture must actually step through, not merely retain in the artifact. -/
  requiredExecutedLcnfForms : Array String := #[]
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
  requiredExecutedLcnfForms : Array String
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
  requiredExecutedLcnfForms := validationCase.requiredExecutedLcnfForms
  provenance := validationCase.provenance }

private def natListDatum (xs : List Nat) : ValidationDatum :=
  .seq (xs.toArray.map .nat)

private def byteArrayDatum (value : ByteArray) : ValidationDatum :=
  .bytes (value.data.map (UInt8.toNat ·))

private partial def assocDatum : Source.Assoc → ValidationDatum
  | .atom value => .ctor "Assoc.atom" 0 #[.nat value]
  | .node left right => .ctor "Assoc.node" 1 #[assocDatum left, assocDatum right]

private partial def assocSchema : Source.Assoc → ValidationSchema
  | .atom _ => .ctor "Assoc.atom" 0 #[.nat]
  | .node left right => .ctor "Assoc.node" 1 #[assocSchema left, assocSchema right]

private def assocInput : Source.Assoc :=
  .node (.node (.atom 1) (.atom 2)) (.node (.atom 3) (.atom 4))

private def assocExpected : Source.Assoc :=
  .node (.atom 1) (.node (.atom 2) (.node (.atom 3) (.atom 4)))

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
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"] },
  { id := "branch-nat-false"
    entry := ``Source.branchNat
    args := #[.bool false]
    argSchemas := #[.bool]
    resultSchema := .nat
    native := fun _ => .nat (Source.branchNat false)
    tags := #["quick", "control-flow", "boundary"]
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"] },
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
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfForms := #["cases", "oproj", "inc", "fap", "return"] },
  { id := "recursive-empty"
    entry := ``Source.recursiveTraversal
    dependencies := #[``Source.lastOr]
    args := #[natListDatum []]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recursiveTraversal [])
    tags := #["quick", "constructor", "recursion", "boundary"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfForms := #["cases", "inc", "fap", "return"] },
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
    requiredExecutedLcnfForms :=
      #["ctor", "uset", "sset", "sproj", "fap", "isShared", "cases", "jump", "return"]
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
    requiredExecutedLcnfForms := #["oproj", "isShared", "cases", "oset", "jump", "return"]
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
    provenance := firProvenance "Portable USize fixture below the Wasm32 boundary" },
  { id := "reuse-assoc"
    entry := ``Source.Assoc.reassoc
    args := #[assocDatum assocInput]
    argSchemas := #[assocSchema assocInput]
    resultSchema := assocSchema assocExpected
    native := fun _ => assocDatum (Source.Assoc.reassoc assocInput)
    tags := #["stress", "ownership", "reuse", "recursion", "constructor"]
    fuel := 100000
    requiredLcnfForms :=
      #["cases", "oproj", "inc", "join", "fap", "oset", "jump", "ctor", "isShared",
        "dec", "return"]
    requiredExecutedLcnfForms :=
      #["cases", "oproj", "inc", "join", "isShared", "dec", "jump", "oset", "fap",
        "return"]
    provenance := leanCompileProvenance "tests/compile/reusebug.lean"
      "Pure terminating reassociation adapted to execute the ownership/reuse path" },
  { id := "capture-17-list"
    entry := ``Source.capture17List
    dependencies := #[``Source.applyCaptureList]
    args := #[
      .nat 1, .nat 2, .nat 3, .nat 4, .nat 5, .nat 6, .nat 7, .nat 8, .nat 9,
      .nat 10, .nat 11, .nat 12, .nat 13, .nat 14, .nat 15, .nat 16, .nat 17,
      .nat 18]
    argSchemas := #[
      .nat, .nat, .nat, .nat, .nat, .nat, .nat, .nat, .nat,
      .nat, .nat, .nat, .nat, .nat, .nat, .nat, .nat, .nat]
    resultSchema := .seq .nat
    native := fun _ => natListDatum
      (Source.capture17List 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18)
    tags := #["stress", "closure", "capture", "boundary", "constructor"]
    requiredLcnfForms := #["pap", "fap", "fvar", "ctor", "return"]
    requiredExecutedLcnfForms := #["pap", "fap", "fvar", "ctor", "return"]
    provenance := leanCompileProvenance "tests/compile/closure_bug1.lean"
      "Pure list-valued adaptation retaining 17 captured values" },
  { id := "big-ctor-70"
    entry := ``Source.bigCtorField
    dependencies := #[``Source.mkBigCtor]
    args := #[.nat 70]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.bigCtorField 70)
    tags := #["stress", "constructor", "large-object", "boundary", "projection"]
    requiredLcnfForms := #["fap", "oproj", "inc", "dec", "lit", "ctor", "return"]
    requiredExecutedLcnfForms := #["fap", "oproj", "inc", "dec", "lit", "ctor", "return"]
    provenance := leanCompileProvenance "tests/compile/bigctor.lean"
      "70-object-field constructor preserving the original stress size" },
  { id := "scalar-enum-cases"
    entry := ``Source.scalarCasesInternal
    dependencies := #[``Source.selectScalarChoice]
    resultSchema := .nat
    native := fun _ => .nat Source.scalarCasesInternal
    tags := #["quick", "scalar", "control-flow", "enum", "regression"]
    requiredLcnfForms := #["fap", "inc", "return", "lit", "cases"]
    requiredExecutedLcnfForms := #["fap", "lit", "cases", "return", "inc"]
    provenance := firProvenance "Nullary enum lowered to UInt8 and matched internally" },
  { id := "int-positive-roundtrip"
    entry := ``Source.idInt
    args := #[.int 42]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt 42)
    tags := #["quick", "int", "signed", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Positive immediate Int ABI round-trip" },
  { id := "int-negative-roundtrip"
    entry := ``Source.idInt
    args := #[.int (-42)]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt (-42))
    tags := #["quick", "int", "signed", "negative", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Negative immediate Int ABI round-trip" },
  { id := "int-immediate-max"
    entry := ``Source.idInt
    args := #[.int 2147483647]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt 2147483647)
    tags := #["stress", "int", "signed", "boundary", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Largest Lean immediate Int payload" },
  { id := "int-immediate-min"
    entry := ``Source.idInt
    args := #[.int (-2147483648)]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt (-2147483648))
    tags := #["stress", "int", "signed", "negative", "boundary", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Smallest Lean immediate Int payload" },
  { id := "nat-add-small"
    entry := ``Source.addNat
    args := #[.nat 20, .nat 22]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.addNat 20 22)
    tags := #["quick", "external", "pure", "nat", "arithmetic"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    provenance := firProvenance "Controlled Nat.add external on tagged operands" },
  { id := "nat-add-tagged-to-heap"
    entry := ``Source.addNat
    args := #[.nat 9223372036854775807, .nat 1]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.addNat 9223372036854775807 1)
    tags := #["stress", "external", "pure", "nat", "arithmetic", "boundary", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    provenance := firProvenance "Nat.add crossing the tagged-to-heap result boundary" },
  { id := "nat-add-heap-input"
    entry := ``Source.addNat
    args := #[.nat Source.largeNat, .nat 7]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.addNat Source.largeNat 7)
    tags := #["stress", "external", "pure", "nat", "arithmetic", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    provenance := firProvenance "Nat.add decoding and returning heap natural values" },
  { id := "byte-array-roundtrip"
    entry := ``Source.idByteArray
    args := #[.bytes #[0, 127, 128, 255]]
    argSchemas := #[.bytes]
    resultSchema := .bytes
    native := fun _ => byteArrayDatum
      (Source.idByteArray ⟨#[0, 127, 128, 255]⟩)
    tags := #["quick", "bytes", "packed-layout", "roundtrip", "boundary"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Runner-supplied packed ByteArray ABI round-trip" },
  { id := "byte-array-size"
    entry := ``Source.byteArraySize
    args := #[.bytes #[0, 127, 128, 255]]
    argSchemas := #[.bytes]
    resultSchema := .nat
    native := fun _ => .nat (Source.byteArraySize ⟨#[0, 127, 128, 255]⟩)
    tags := #["quick", "bytes", "packed-layout", "external", "pure", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    provenance := firProvenance "Controlled ByteArray.size external on packed boundary bytes" }
]

def findCase? (id : String) : Option Case :=
  cases.find? (·.id == id)

def caseIds : Array String :=
  cases.map (·.id)

def descriptors : Array CaseDescriptor :=
  cases.map Case.descriptor

end Fir.Validation.Corpus
