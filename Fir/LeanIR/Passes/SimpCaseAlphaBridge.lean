import Fir.LeanIR.Passes.SimpCaseCompilerBridge
import Fir.LeanIR.Passes.AlphaEqvCode

namespace Fir.LeanIR.Passes.SimpCaseAlphaBridge

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.NonLockstep.Structural
open Fir.LeanIR.Passes.SimpCaseCompilerBridge
open Fir.LeanIR.Passes.SimpCaseRelation

/-!
`CodeRel` and `AlphaEqv.CodeRelated` deliberately expose different proof
interfaces.  The recursive simpCase relation is scope-free and carries the
runtime readiness invariant needed at case nodes.  The alpha relation is
indexed by declaration-local variable and join scopes.  Consequently their
sound composition belongs at the whole-program boundary, after each relation
has discharged its own indexing obligations.

The witness below makes that boundary reusable.  It also prevents an alpha
edge from being hidden inside `CaseBoundarySound`, whose statement does not
contain enough scope information to justify one.
-/

/-- A pass result factored through recursive structural simplification and
then bidirectional alpha equivalence. -/
structure StructuralThenAlphaPrograms
    (validCase : LCNF.Cases .impure → Nat → Prop)
    (before after : ImpureProgram) where
  middle : ImpureProgram
  structural : ProgramRelated (CodeRel validCase) before middle
  alpha : ProgramsBirelated middle after

/-- The structural leg determines the runtime readiness required of callers;
the following alpha leg is correct for all entry arguments. -/
def StructuralThenAlphaAdmissible (externals : ExternalSpec)
    (witness : StructuralThenAlphaPrograms validCase before after)
    (entry : Name) (args : Array Value) : Prop :=
  ReachablyReadyAdmissible externals validCase
    before witness.middle entry args

/-- Reusable correctness theorem for a structural simpCase result followed by
an alpha-equivalent presentation of that result. -/
theorem structuralThenAlphaSamePhaseCorrectOn
    (witness : StructuralThenAlphaPrograms validCase before after) :
    SamePhaseCorrectOn (Impure.semantics externals) before after entries
      (StructuralThenAlphaAdmissible externals witness) := by
  intro entry member args admissible observation
  exact
    (SimpCaseRelation.samePhaseCorrectOn_reachablyReady
      (externals := externals) (entries := entries) witness.structural
      entry member args admissible observation).trans
    (AlphaEqv.samePhaseCorrect_of_programsBirelated
      (externals := externals) (entries := entries) witness.alpha
      entry member args observation)

/-- Evidence for the transparent compiler shadow followed by an alpha step.
`caseSound` remains explicit because Lean 4.32's actual recursive simpCase
implementation is private and opaque to downstream kernel proofs. -/
structure ShadowThenAlphaPrograms
    (validCase : LCNF.Cases .impure → Nat → Prop) (fuel : Nat)
    (before after : ImpureProgram) where
  middle : ImpureProgram
  caseSound : CaseBoundarySound validCase
  shadow : shadowProgram? fuel before = some middle
  alpha : ProgramsBirelated middle after

/-- Turn a checked transparent-shadow run into the generic composed witness. -/
def ShadowThenAlphaPrograms.toStructural
    (witness : ShadowThenAlphaPrograms validCase fuel before after) :
    StructuralThenAlphaPrograms validCase before after := {
  middle := witness.middle
  structural := shadowProgram_related witness.caseSound witness.shadow
  alpha := witness.alpha
}

/-- Compiler-shadow corollary of the reusable structural/alpha theorem. -/
theorem shadowThenAlphaSamePhaseCorrectOn
    (witness : ShadowThenAlphaPrograms validCase fuel before after) :
    SamePhaseCorrectOn (Impure.semantics externals) before after entries
      (StructuralThenAlphaAdmissible externals witness.toStructural) :=
  structuralThenAlphaSamePhaseCorrectOn witness.toStructural

end Fir.LeanIR.Passes.SimpCaseAlphaBridge
