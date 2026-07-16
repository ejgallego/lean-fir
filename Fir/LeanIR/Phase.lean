import Fir.LeanIR.Hygiene

namespace Fir.LeanIR

open Lean
open Lean.Compiler

/--
An LCNF declaration group whose compiler phase is visible in its type.

Lean uses the same `.pure` syntax index for base and mono LCNF. Indexing FIR
programs by `LCNF.Phase` prevents those two semantically different snapshots
from being exchanged accidentally.
-/
structure Program (phase : LCNF.Phase) where
  decls : Array (LCNF.Decl phase.toPurity)
  deriving Inhabited

abbrev BaseProgram := Program .base
abbrev MonoProgram := Program .mono
abbrev ImpureProgram := Program .impure

namespace Program

def names (program : Program phase) : Array Name :=
  program.decls.map (·.name)

def findDecl? (program : Program phase) (name : Name) : Option (LCNF.Decl phase.toPurity) :=
  program.decls.find? (·.name == name)

def contains (program : Program phase) (name : Name) : Bool :=
  (program.findDecl? name).isSome

/-- The minimum phase-independent invariant required by program semantics. -/
def NamesUnique (program : Program phase) : Prop :=
  program.decls.toList.Pairwise fun left right => left.name ≠ right.name

/--
The inherited structural invariant needed by impure semantics and
alpha-renaming proofs. Lean's pure checker enforces the corresponding property
before lowering; the impure checker is currently a no-op, so FIR records it at
the phase boundary.
-/
def ImpureHygienic (program : ImpureProgram) : Prop :=
  program.decls.all ImpureHygiene.declHygienic = true

end Program

/--
Phase-aware well-formedness. The shared invariant is deliberately small;
phase-specific checker facts can be added without changing `Program` or any
consumer that accepts a `CheckedProgram`.
-/
inductive WellFormedAt : (phase : LCNF.Phase) → Program phase → Prop where
  | base {program : BaseProgram} (namesUnique : program.NamesUnique) :
      WellFormedAt .base program
  | mono {program : MonoProgram} (namesUnique : program.NamesUnique) :
      WellFormedAt .mono program
  | impure {program : ImpureProgram} (namesUnique : program.NamesUnique)
      (hygienic : program.ImpureHygienic) :
      WellFormedAt .impure program

structure CheckedProgram (phase : LCNF.Phase) where
  program : Program phase
  wellFormed : WellFormedAt phase program

abbrev CheckedBaseProgram := CheckedProgram .base
abbrev CheckedMonoProgram := CheckedProgram .mono
abbrev CheckedImpureProgram := CheckedProgram .impure

end Fir.LeanIR
