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
