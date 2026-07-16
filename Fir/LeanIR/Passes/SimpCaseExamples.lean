import Fir.LeanIR.Passes.SimpCase
import Fir.LeanIR.Passes.AlphaEqvTrusted
import Fir.LeanIR.InterpreterExamples
import Lean.Elab.Command

namespace Fir.LeanIR.Passes.SimpCaseExamples

open Lean
open Lean.Elab.Command
open Lean.Compiler
open Fir.LeanIR.InterpreterExamples
open Fir.LeanIR.Passes.AlphaEqv

def selectedBranch : LCNF.Code .impure :=
  .return x

def singletonDefaultCode : LCNF.Code .impure :=
  .cases (.mk ``Bool objType c #[.default selectedBranch])

def filterUnreachableCode : LCNF.Code .impure :=
  .cases (.mk ``Bool objType c #[
    .ctorAlt falseInfo (.unreach objType),
    .ctorAlt trueInfo selectedBranch])

def alphaLeftId : FVarId := ⟨`alphaLeft⟩

def alphaRightId : FVarId := ⟨`alphaRight⟩

def alphaLeft : LCNF.Code .impure :=
  .let (letDecl alphaLeftId objType (.lit (.nat 5))) (.return alphaLeftId)

def alphaRight : LCNF.Code .impure :=
  .let (letDecl alphaRightId objType (.lit (.nat 5))) (.return alphaRightId)

#guard alphaLeft.alphaEqv alphaRight

def thirdInfo : LCNF.CtorInfo :=
  { name := `Third, cidx := 2, size := 0, usize := 0, ssize := 0 }

def alphaFoldCode : LCNF.Code .impure :=
  .cases (.mk `Three objType c #[
    .ctorAlt falseInfo alphaLeft,
    .ctorAlt trueInfo alphaRight,
    .ctorAlt thirdInfo selectedBranch])

def alphaFoldExpected : LCNF.Code .impure :=
  .cases (.mk `Three objType c #[
    .ctorAlt thirdInfo selectedBranch,
    .default alphaLeft])

/-!
`Code.alphaEqv` relies on the compiler invariant that every local `FVarId` is
globally fresh within a declaration. Reusing `x` below makes the Boolean test
accept programs with different observations; this is the minimized witness in
`FIR-BUG-impure-simpCase-alpha-hygiene`.
-/
def nonHygienicAlphaLeft : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 5))) <|
  .let (letDecl x objType (.lit (.nat 6))) <|
  .return x

def nonHygienicAlphaRight : LCNF.Code .impure :=
  .let (letDecl y objType (.lit (.nat 5))) <|
  .let (letDecl z objType (.lit (.nat 6))) <|
  .return y

#guard nonHygienicAlphaLeft.alphaEqv nonHygienicAlphaRight

def localMatchesUpstream (left right : LCNF.Code .impure) : Bool :=
  Local.check 512 left right == left.alphaEqv right

/-!
The local copy is executable despite the opacity of Lean's recursive checker.
These guards compare both implementations over alpha-renamed, rejected, and
compiler-shape fixtures spanning every impure `Code` constructor.
-/
#guard Local.check 512 alphaLeft alphaRight
#guard localMatchesUpstream alphaLeft alphaRight
#guard localMatchesUpstream nonHygienicAlphaLeft nonHygienicAlphaRight
#guard localMatchesUpstream alphaLeft selectedBranch

def alphaEqvRegressionCodes : Array (LCNF.Code .impure) := #[
  literalCode,
  erasedCode,
  ctorProjectionCode,
  caseCode,
  directCallCode,
  closureCallCode,
  joinCode,
  scalarBoxCode,
  mutationCode,
  usizeProjectionCode,
  objectMutationCode,
  tagMutationCode,
  defaultCaseCode,
  rcCode,
  persistentRcCode,
  isSharedCaseCode,
  resetReuseCode,
  sharedResetCode,
  deletedCode,
  externalCode,
  .unreach objType
]

#guard alphaEqvRegressionCodes.all fun code => localMatchesUpstream code code

def nonHygienicAlphaLeftProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code nonHygienicAlphaLeft)] }

def nonHygienicAlphaRightProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code nonHygienicAlphaRight)] }

#guard returned? (runMain nonHygienicAlphaLeftProgram) (.object (.tagged 6))
#guard returned? (runMain nonHygienicAlphaRightProgram) (.object (.tagged 5))

def fixtureDecl (name : Name) (code : LCNF.Code .impure) : LCNF.Decl .impure :=
  decl name #[param c, param x] objType (.code code)

def checkActualSimpCase (name : Name) (before expected : LCNF.Code .impure) : CoreM Unit := do
  let output ← LCNF.CompilerM.run
    (LCNF.simpCase.run #[fixtureDecl name before]) (phase := .impure)
  let some after := output[0]? | throwError "simpCase fixture {name} produced no declaration"
  let .code actual := after.value | throwError "simpCase fixture {name} ceased to be code"
  unless actual == expected do
    throwError "simpCase fixture {name} did not produce the specification result"

def checkFixtures : CoreM Unit := do
  checkActualSimpCase `singletonDefault singletonDefaultCode selectedBranch
  checkActualSimpCase `filterUnreachable filterUnreachableCode selectedBranch
  checkActualSimpCase `foldAlphaEquivalent alphaFoldCode alphaFoldExpected

elab "#check_simp_case_fixtures" : command =>
  liftCoreM checkFixtures

#check_simp_case_fixtures

end Fir.LeanIR.Passes.SimpCaseExamples
