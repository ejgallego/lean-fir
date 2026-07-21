import Fir.LeanIR.Phase
import Fir.LeanIR.Passes.SimpCaseScopedBridge

namespace Fir.LeanIR.Passes.SimpCaseWellFormed

open Lean
open Lean.Compiler
open Fir.LeanIR.Passes.AlphaEqv

/-!
This module is the compiler-facing entry point for the `simpCase` proof.
The recursive certificates consumed by `SimpCaseScopedBridge` are deliberately
absent from the definitions below.  Instead, a source program records the
three independent invariants that the compiler can check or preserve:

* ordinary phase well-formedness (unique declaration names and impure LCNF
  hygiene);
* deterministic selector normalization at every case node;
* canonical runtime-observed type metadata.

The next layer proves that these invariants synthesize the proof-facing scoped
certificate tree.  Keeping this boundary separate prevents callers from
having to construct those certificates by hand.
-/

/-- Recursive case-table normalization for a declaration value. External
declarations have no executable body and therefore no case table. -/
def DeclValueNormalizationTree : LCNF.DeclValue .impure → Prop
  | .code code => CodeNormalizationTree code
  | .extern _ => True

def DeclNormalizationTree (declaration : LCNF.Decl .impure) : Prop :=
  DeclValueNormalizationTree declaration.value

def DeclListNormalizationTree
    (declarations : List (LCNF.Decl .impure)) : Prop :=
  ∀ declaration, declaration ∈ declarations →
    DeclNormalizationTree declaration

def ProgramNormalizationTree (program : ImpureProgram) : Prop :=
  DeclListNormalizationTree program.decls.toList

/-- The minimal declaration-local compiler invariant.  This contains no
alpha, structural, semantic, or pass-specific certificate. -/
structure DeclWellFormed (declaration : LCNF.Decl .impure) : Prop where
  hygienic : ImpureHygiene.declHygienic declaration = true
  normalization : DeclNormalizationTree declaration
  canonical : DeclRuntimeTypesCanonical declaration

/-- Compiler-shaped source premise for the preferred whole-program theorem.
`phase` is the shared LeanIR invariant; the two remaining fields are the
independent invariants used only by the `simpCase` alpha-fold proof. -/
structure ProgramWellFormed (program : ImpureProgram) : Prop where
  phase : WellFormedAt .impure program
  normalization : ProgramNormalizationTree program
  canonical : ProgramRuntimeTypesCanonical program

theorem ProgramWellFormed.namesUnique
    (wellFormed : ProgramWellFormed program) : program.NamesUnique := by
  cases wellFormed.phase with
  | impure namesUnique _ => exact namesUnique

theorem ProgramWellFormed.hygienic
    (wellFormed : ProgramWellFormed program) : program.ImpureHygienic := by
  cases wellFormed.phase with
  | impure _ hygienic => exact hygienic

theorem ProgramWellFormed.declarationHygienic
    (wellFormed : ProgramWellFormed program)
    {declaration : LCNF.Decl .impure}
    (member : declaration ∈ program.decls.toList) :
    ImpureHygiene.declHygienic declaration = true := by
  have allHygienic := wellFormed.hygienic
  unfold Program.ImpureHygienic at allHygienic
  rw [Array.all_eq_true'] at allHygienic
  exact allHygienic declaration (Array.mem_def.mpr member)

theorem ProgramWellFormed.declaration
    (wellFormed : ProgramWellFormed program)
    {declaration : LCNF.Decl .impure}
    (member : declaration ∈ program.decls.toList) :
    DeclWellFormed declaration := {
  hygienic := wellFormed.declarationHygienic member
  normalization := wellFormed.normalization declaration member
  canonical := wellFormed.canonical declaration member
}

/-- Assemble the public premise from the shared phase checker and the two
pass-specific compiler-output invariants. -/
theorem ProgramWellFormed.ofCompilerInvariants
    (phase : WellFormedAt .impure program)
    (normalization : ProgramNormalizationTree program)
    (canonical : ProgramRuntimeTypesCanonical program) :
    ProgramWellFormed program := {
  phase
  normalization
  canonical
}

end Fir.LeanIR.Passes.SimpCaseWellFormed
