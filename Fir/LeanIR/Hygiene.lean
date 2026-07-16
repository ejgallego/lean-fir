import Lean.Compiler.LCNF.PassManager
import Lean.Util.CollectFVars

namespace Fir.LeanIR.ImpureHygiene

open Lean
open Lean.Compiler

/-- The two namespaces that matter operationally in impure LCNF. -/
structure Scope where
  vars : List FVarId := []
  joins : List FVarId := []

def exprScoped (scope : List FVarId) (expr : Expr) : Bool :=
  (collectFVars {} expr).fvarIds.all scope.contains

def argScoped (scope : List FVarId) : LCNF.Arg .impure → Bool
  | .erased => true
  | .fvar fvarId => scope.contains fvarId
  | .type _ impossible => nomatch impossible

def argsScoped (scope : List FVarId) (args : Array (LCNF.Arg .impure)) : Bool :=
  args.all (argScoped scope)

def letValueScoped (scope : List FVarId) : LCNF.LetValue .impure → Bool
  | .lit _ | .erased => true
  | .proj _ _ _ impossible | .const _ _ _ impossible => nomatch impossible
  | .fvar fvarId args => scope.contains fvarId && argsScoped scope args
  | .ctor _ args => argsScoped scope args
  | .oproj _ fvarId | .uproj _ fvarId | .sproj _ _ fvarId => scope.contains fvarId
  | .fap _ args | .pap _ args => argsScoped scope args
  | .reset _ fvarId => scope.contains fvarId
  | .reuse fvarId _ _ args => scope.contains fvarId && argsScoped scope args
  | .box type fvarId => exprScoped scope type && scope.contains fvarId
  | .unbox fvarId | .isShared fvarId => scope.contains fvarId

def paramIds (params : Array (LCNF.Param .impure)) : List FVarId :=
  params.toList.map (fun param => param.fvarId)

mutual

partial def codeScoped (scope : Scope) : LCNF.Code .impure → Bool
  | .let decl continuation =>
      exprScoped scope.vars decl.type &&
        letValueScoped scope.vars decl.value &&
        codeScoped { scope with vars := decl.fvarId :: scope.vars } continuation
  | .fun _ _ impossible => nomatch impossible
  | .jp decl continuation =>
      funDeclScoped scope decl &&
        codeScoped { scope with joins := decl.fvarId :: scope.joins } continuation
  | .jmp fvarId args => scope.joins.contains fvarId && argsScoped scope.vars args
  | .cases cases =>
      exprScoped scope.vars cases.resultType &&
        scope.vars.contains cases.discr &&
        cases.alts.all (altScoped scope)
  | .return fvarId => scope.vars.contains fvarId
  | .unreach type => exprScoped scope.vars type
  | .oset fvarId _ arg continuation =>
      scope.vars.contains fvarId &&
        argScoped scope.vars arg &&
        codeScoped scope continuation
  | .uset fvarId _ fieldId continuation =>
      scope.vars.contains fvarId &&
        scope.vars.contains fieldId &&
        codeScoped scope continuation
  | .sset fvarId _ _ fieldId type continuation =>
      scope.vars.contains fvarId &&
        scope.vars.contains fieldId &&
        exprScoped scope.vars type &&
        codeScoped scope continuation
  | .setTag fvarId _ continuation
  | .inc fvarId _ _ _ continuation
  | .dec fvarId _ _ _ _ continuation
  | .del fvarId continuation =>
      scope.vars.contains fvarId && codeScoped scope continuation

partial def altScoped (scope : Scope) : LCNF.Alt .impure → Bool
  | .alt _ _ _ impossible => nomatch impossible
  | .ctorAlt _ code | .default code => codeScoped scope code

partial def funDeclScoped (scope : Scope) (decl : LCNF.FunDecl .impure) : Bool :=
  let vars := paramIds decl.params ++ scope.vars
  decl.params.all (fun param => exprScoped vars param.type) &&
    exprScoped vars decl.type &&
    codeScoped { scope with vars } decl.value

end

mutual

partial def codeBinders : LCNF.Code .impure → List FVarId
  | .let decl continuation => decl.fvarId :: codeBinders continuation
  | .fun _ _ impossible => nomatch impossible
  | .jp decl continuation =>
      decl.fvarId :: (paramIds decl.params ++ codeBinders decl.value ++ codeBinders continuation)
  | .cases cases => cases.alts.toList.flatMap altBinders
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation => codeBinders continuation
  | .jmp _ _ | .return _ | .unreach _ => []

partial def altBinders : LCNF.Alt .impure → List FVarId
  | .alt _ _ _ impossible => nomatch impossible
  | .ctorAlt _ code | .default code => codeBinders code

end

def bindersUnique (binders : List FVarId) : Bool :=
  go {} binders
where
  go (seen : FVarIdSet) : List FVarId → Bool
    | [] => true
    | fvarId :: rest => !seen.contains fvarId && go (seen.insert fvarId) rest

def declHygienic (decl : LCNF.Decl .impure) : Bool :=
  let params := paramIds decl.params
  let scope : Scope := { vars := params }
  let signatureScoped :=
    decl.params.all (fun param => exprScoped params param.type) && exprScoped params decl.type
  match decl.value with
  | .extern _ => bindersUnique params && signatureScoped
  | .code code =>
      bindersUnique (params ++ codeBinders code) && signatureScoped && codeScoped scope code

end Fir.LeanIR.ImpureHygiene
