import Fir.LeanIR.Phase
import Lean.Compiler.LCNF.Passes

namespace Fir.LeanIR

open Lean
open Lean.Compiler

structure PassKey where
  phase : LCNF.Phase
  phaseOut : LCNF.Phase
  name : Name
  occurrence : Nat
  deriving Inhabited, BEq

def PassKey.ofPass (pass : LCNF.Pass) : PassKey :=
  { phase := pass.phase
    phaseOut := pass.phaseOut
    name := pass.name
    occurrence := pass.occurrence }

def pass (phase : LCNF.Phase) (name : Name) (occurrence := 0)
    (phaseOut := phase) : PassKey :=
  { phase, phaseOut, name, occurrence }

def expectedBasePasses : Array PassKey := #[
  pass .base `init,
  pass .base `pullInstances,
  pass .base `cse 0,
  pass .base `simp 0,
  pass .base `floatLetIn 0,
  pass .base `findJoinPoints 0,
  pass .base `pullFunDecls,
  pass .base `reduceJpArity 0,
  pass .base `simp 1,
  pass .base `eagerLambdaLifting,
  pass .base `checkTemplateVisibility,
  pass .base `specialize,
  pass .base `findJoinPoints 1,
  pass .base `simp 2,
  pass .base `cse 1,
  pass .base `saveBase,
  pass .base `inferVisibility,
  pass .base `toMono 0 .mono]

def expectedMonoPasses : Array PassKey := #[
  pass .mono `simp 3,
  pass .mono `reduceJpArity,
  pass .mono `structProjCases,
  pass .mono `extendJoinPointContext 0,
  pass .mono `floatLetIn 1,
  pass .mono `reduceArity,
  pass .mono `commonJoinPointArgs,
  pass .mono `simp 4,
  pass .mono `floatLetIn 2,
  pass .mono `lambdaLifting]

def expectedLateMonoPasses : Array PassKey := #[
  pass .mono `extendJoinPointContext 1,
  pass .mono `simp 5,
  pass .mono `elimDeadBranches,
  pass .mono `cse 2,
  pass .mono `saveMono,
  pass .mono `inferVisibility,
  pass .mono `extractClosed,
  pass .mono `toImpure 0 .impure]

def expectedImpurePasses : Array PassKey := #[
  pass .impure `pushProj 0,
  pass .impure `resetReuse,
  pass .impure `elimDeadVars 0,
  pass .impure `simpCase,
  pass .impure `inferBorrow,
  pass .impure `explicitBoxing,
  pass .impure `explicitRc,
  pass .impure `expandResetReuse,
  pass .impure `coalesceRc,
  pass .impure `pushProj 1,
  pass .impure `detectSimpleGround,
  pass .impure `inferVisibility,
  pass .impure `toposort,
  pass .impure `saveImpure]

def actualBasePasses : Array PassKey :=
  LCNF.builtinPassManager.basePasses.map PassKey.ofPass

def actualMonoPasses : Array PassKey :=
  LCNF.builtinPassManager.monoPasses.map PassKey.ofPass

def actualLateMonoPasses : Array PassKey :=
  LCNF.builtinPassManager.monoPassesNoLambda.map PassKey.ofPass

def actualImpurePasses : Array PassKey :=
  LCNF.builtinPassManager.impurePasses.map PassKey.ofPass

#guard actualBasePasses == expectedBasePasses
#guard actualMonoPasses == expectedMonoPasses
#guard actualLateMonoPasses == expectedLateMonoPasses
#guard actualImpurePasses == expectedImpurePasses

inductive ProofTarget where
  | pass (key : PassKey)
  | splitSCC
  | toLCNF
  deriving Inhabited, BEq

/--
The implementation order for the backward proof campaign. Updating Lean's
pipeline without updating this value fails one of the guards above.
-/
def reverseProofCampaign : Array ProofTarget :=
  expectedImpurePasses.reverse.map .pass ++
  expectedLateMonoPasses.reverse.map .pass ++
  #[.splitSCC] ++
  expectedMonoPasses.reverse.map .pass ++
  expectedBasePasses.reverse.map .pass ++
  #[.toLCNF]

def isAdministrative : PassKey → Bool
  | { name := `saveBase, .. }
  | { name := `saveMono, .. }
  | { name := `saveImpure, .. }
  | { name := `inferVisibility, .. }
  | { name := `toposort, .. } => true
  | _ => false

end Fir.LeanIR
