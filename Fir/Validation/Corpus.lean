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

end Source

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
  { id := "local-tail"
    entry := ``Source.localTailControl
    dependencies := #[`Fir.Validation.Corpus.Source.localTailControl.loop]
    args := #[natListDatum [10, 20, 42]]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.localTailControl [10, 20, 42])
    tags := #["quick", "tail-control"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"] }
]

def findCase? (id : String) : Option Case :=
  cases.find? (·.id == id)

def caseIds : Array String :=
  cases.map (·.id)

end Fir.Validation.Corpus
