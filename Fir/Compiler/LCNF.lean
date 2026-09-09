import Fir.LeanIR.Phase
import Lean.Compiler.LCNF
import Lean.Compiler.LCNF.EmitUtil

/-!
Production final-LCNF capture. This module owns the reusable artifact and
capture implementation; validation schemas, corpus entries and instrumented
execution belong to clients. Form names and textual formatting are descriptive
metadata. Their existing eager collection is intentionally unchanged here.
-/

namespace Fir.Compiler.Lcnf

open Lean Lean.Compiler Fir.LeanIR

/-- Final impure LCNF and descriptive metadata shared by production and validation clients. -/
structure Artifact where
  entry : Name
  program : ImpureProgram
  externalNames : Array Name
  forms : Array String

private def pushUnique (forms : Array String) (form : String) : Array String :=
  if forms.contains form then forms else forms.push form

private def addForms (forms : Array String) (more : Array String) : Array String :=
  more.foldl (init := forms) pushUnique

private def letValueForm : LCNF.LetValue .impure -> String
  | .lit _ => "lit"
  | .erased => "erased"
  | .proj .. => "proj"
  | .const .. => "const"
  | .fvar .. => "fvar"
  | .ctor .. => "ctor"
  | .oproj .. => "oproj"
  | .uproj .. => "uproj"
  | .sproj .. => "sproj"
  | .fap .. => "fap"
  | .pap .. => "pap"
  | .reset .. => "reset"
  | .reuse .. => "reuse"
  | .box .. => "box"
  | .unbox .. => "unbox"
  | .isShared .. => "isShared"

/-- Name the head operation without depending on coverage or execution instrumentation. -/
def codeHeadForm : LCNF.Code .impure → String
  | .let decl _ => letValueForm decl.value
  | .fun .. => "fun"
  | .jp .. => "join"
  | .jmp .. => "jump"
  | .cases .. => "cases"
  | .return .. => "return"
  | .unreach .. => "unreach"
  | .oset .. => "oset"
  | .uset .. => "uset"
  | .sset .. => "sset"
  | .setTag .. => "setTag"
  | .inc .. => "inc"
  | .dec .. => "dec"
  | .del .. => "del"

private partial def codeForms (code : LCNF.Code .impure) : Array String :=
  let own := #[codeHeadForm code]
  match code with
  | .let _ k => addForms own (codeForms k)
  | .fun decl k _ => addForms own (addForms (codeForms decl.value) (codeForms k))
  | .jp decl k => addForms own (addForms (codeForms decl.value) (codeForms k))
  | .jmp .. => own
  | .cases cases =>
      cases.alts.foldl (init := own) fun forms alt =>
        addForms forms (codeForms alt.getCode)
  | .return _ | .unreach _ => own
  | .oset (k := k) .. | .uset (k := k) .. | .sset (k := k) .. |
      .setTag (k := k) .. | .inc (k := k) .. | .dec (k := k) .. | .del (k := k) .. =>
      addForms own (codeForms k)

def collectForms (program : ImpureProgram) : Array String :=
  program.decls.foldl (init := #[]) fun forms decl =>
    match decl.value with
    | .code code => addForms forms (codeForms code)
    | .extern _ => pushUnique forms "extern"

/-- Stable human-readable compiler artifact retained beside the machine result. -/
def Artifact.format (artifact : Artifact) : CoreM String := do
  let declarations ← artifact.program.decls.mapM fun decl => do
    return toString (← LCNF.ppDecl' decl .impure)
  return String.intercalate "\n\n" declarations.toList

private def externDecl (sig : LCNF.Signature .impure) (data : ExternAttrData) :
    LCNF.Decl .impure :=
  { name := sig.name
    levelParams := sig.levelParams
    type := sig.type
    params := sig.params
    safe := sig.safe
    value := .extern data
    inlineAttr? := none }

/-- Compile an entry and retain its complete local dependency closure plus imported extern stubs. -/
def compileEntry (entry : Name) (dependencies : Array Name := #[]) : CoreM Artifact := do
  let roots := #[entry] ++ dependencies
  LCNF.main roots (← getOptions)
  let (localDecls, externalSigs) ← LCNF.collectUsedDecls roots
  let env ← getEnv
  let externalDecls := externalSigs.map fun sig =>
    let data := getExternAttrData? env sig.name |>.getD { entries := [.opaque] }
    externDecl sig data
  let program : ImpureProgram := { decls := localDecls ++ externalDecls }
  return {
    entry
    program
    externalNames := externalSigs.map (·.name)
    forms := collectForms program }

end Fir.Compiler.Lcnf

/-! Compatibility names: aliases only, with no dependency on the validation harness. -/
namespace Fir.Validation.Lcnf

export Fir.Compiler.Lcnf (Artifact collectForms compileEntry)

namespace Artifact
export Fir.Compiler.Lcnf.Artifact (mk entry program externalNames forms format)
end Artifact

end Fir.Validation.Lcnf
