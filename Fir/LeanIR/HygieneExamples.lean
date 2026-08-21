import Fir.LeanIR.Hygiene
import Fir.LeanIR.InterpreterExamples

namespace Fir.LeanIR.HygieneExamples

open Lean
open Lean.Compiler
open ImpureHygiene
open InterpreterExamples

def hygienicCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 5))) (.return x)

def hygienicDecl : LCNF.Decl .impure :=
  decl `hygienic #[] objType (.code hygienicCode)

#guard declHygienic hygienicDecl

def reusedBinderCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 5))) <|
  .let (letDecl x objType (.lit (.nat 6))) <|
  .return x

def reusedBinderDecl : LCNF.Decl .impure :=
  decl `reusedBinder #[] objType (.code reusedBinderCode)

#guard !declHygienic reusedBinderDecl

def twoBinderCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 5))) <|
  .let (letDecl y objType (.lit (.nat 6))) <|
  .return y

def twoBinderDecl : LCNF.Decl .impure :=
  decl `twoBinder #[] objType (.code twoBinderCode)

#guard declHygienic twoBinderDecl

/-- Kernel regression: executable hygiene exposes the structural freshness of
the two sequential let binders, rather than remaining an opaque Boolean. -/
theorem twoBinderNamesDistinct : x.name ≠ y.name := by
  have accepted : declHygienic twoBinderDecl = true := by native_decide
  have unique := declHygienic_binderNamesUnique accepted
  simpa [twoBinderDecl, decl, declBinders, twoBinderCode, codeBinders,
    BinderNamesUnique, paramIds, letDecl] using unique

/-- Kernel regression for the formerly opaque terminal scope equation. -/
theorem returnScoped_of_codeScoped
    (scope : Scope) (accepted : codeScoped scope (.return x) = true) :
    scope.vars.contains x = true := by
  simpa [codeScoped] using accepted

def unscopedReturnDecl : LCNF.Decl .impure :=
  decl `unscopedReturn #[] objType (.code (.return x))

#guard !declHygienic unscopedReturnDecl

def interpreterCorpus : Array ImpureProgram := #[
  literalProgram,
  erasedProgram,
  ctorProjectionProgram,
  caseProgram,
  directCallProgram,
  closureCallProgram,
  joinProgram,
  scalarBoxProgram,
  mutationProgram,
  usizeProjectionProgram,
  objectMutationProgram,
  tagMutationProgram,
  defaultCaseProgram,
  rcProgram,
  persistentRcProgram,
  resetReuseProgram,
  sharedResetProgram,
  deletedProgram,
  externalProgram]

#guard interpreterCorpus.all fun program => program.decls.all declHygienic

end Fir.LeanIR.HygieneExamples
