import Fir.Compiler.LCNF
import Fir.Compiler.LCNF.Structural

/-! Structural quotation for final impure LCNF. A checked definition is the
single source for proof equations and subsequent production lowering. -/
namespace Fir.Compiler.Lcnf.Reify
open Lean Lean.Compiler Fir.LeanIR Structural

private def impure := mkConst ``LCNF.Purity.impure
private def phase := mkConst ``LCNF.Phase.impure
private def reflImpure := mkApp2 (mkConst ``Eq.refl [.succ .zero])
  (mkConst ``LCNF.Purity) impure
private def iapp (n : Name) (xs : Array Expr := #[]) := app n (#[impure] ++ xs)
private def happ (n : Name) (xs : Array Expr) := iapp n (xs.push reflImpure)

private instance : Codec LCNF.CtorInfo where
  type := mkConst ``LCNF.CtorInfo
  quote x := return app ``LCNF.CtorInfo.mk #[← q x.name, ← q x.cidx, ← q x.size, ← q x.usize, ← q x.ssize]
  read e := do
    let xs ← fields e ``LCNF.CtorInfo.mk 5
    return ⟨← r xs[0]!, ← r xs[1]!, ← r xs[2]!, ← r xs[3]!, ← r xs[4]!⟩

private instance : Codec (LCNF.Param .impure) where
  type := iapp ``LCNF.Param
  quote x := return iapp ``LCNF.Param.mk #[← q x.fvarId, ← q x.binderName, ← q x.type, ← q x.borrow]
  read e := do
    let xs ← fields e ``LCNF.Param.mk 5
    return ⟨← r xs[1]!, ← r xs[2]!, ← r xs[3]!, ← r xs[4]!⟩

private instance : Codec (LCNF.Arg .impure) where
  type := iapp ``LCNF.Arg
  quote
    | .erased => pure (iapp ``LCNF.Arg.erased)
    | .fvar x => return iapp ``LCNF.Arg.fvar #[← q x]
    | .type _ h => nomatch h
  read e := do
    if e.getAppFn.isConstOf ``LCNF.Arg.erased then
      let _ ← fields e ``LCNF.Arg.erased 1
      return .erased
    return .fvar (← r (← fields e ``LCNF.Arg.fvar 2)[1]!)

private instance : Codec LCNF.LitValue where
  type := mkConst ``LCNF.LitValue
  quote
    | .nat n => return app ``LCNF.LitValue.nat #[← q n]
    | .str s => return app ``LCNF.LitValue.str #[← q s]
    | .uint8 n => return app ``LCNF.LitValue.uint8 #[app ``UInt8.ofNat #[← q n.toNat]]
    | .uint16 n => return app ``LCNF.LitValue.uint16 #[app ``UInt16.ofNat #[← q n.toNat]]
    | .uint32 n => return app ``LCNF.LitValue.uint32 #[app ``UInt32.ofNat #[← q n.toNat]]
    | .uint64 n => return app ``LCNF.LitValue.uint64 #[app ``UInt64.ofNat #[← q n.toNat]]
    | .usize n => return app ``LCNF.LitValue.usize #[app ``UInt64.ofNat #[← q n.toNat]]
  read e := do
    let n := e.getAppFn.constName?.getD .anonymous
    let x := (← fields e n 1)[0]!
    if n == ``LCNF.LitValue.nat then return .nat (← r x)
    if n == ``LCNF.LitValue.str then return .str (← r x)
    if n == ``LCNF.LitValue.uint8 then return .uint8 (← r (α := Nat) (← fields x ``UInt8.ofNat 1)[0]!).toUInt8
    if n == ``LCNF.LitValue.uint16 then return .uint16 (← r (α := Nat) (← fields x ``UInt16.ofNat 1)[0]!).toUInt16
    if n == ``LCNF.LitValue.uint32 then return .uint32 (← r (α := Nat) (← fields x ``UInt32.ofNat 1)[0]!).toUInt32
    if n == ``LCNF.LitValue.uint64 then return .uint64 (← r (α := Nat) (← fields x ``UInt64.ofNat 1)[0]!).toUInt64
    if n == ``LCNF.LitValue.usize then return .usize (← r (α := Nat) (← fields x ``UInt64.ofNat 1)[0]!).toUInt64
    throw "structural quotation: unsupported LCNF literal"

private instance : Codec (LCNF.LetValue .impure) where
  type := iapp ``LCNF.LetValue
  quote
    | .lit x => return iapp ``LCNF.LetValue.lit #[← q x]
    | .erased => pure (iapp ``LCNF.LetValue.erased)
    | .fvar x args => return iapp ``LCNF.LetValue.fvar #[← q x, ← q args]
    | .ctor i args => return happ ``LCNF.LetValue.ctor #[← q i, ← q args]
    | .oproj i x => return happ ``LCNF.LetValue.oproj #[← q i, ← q x]
    | .uproj i x => return happ ``LCNF.LetValue.uproj #[← q i, ← q x]
    | .sproj i o x => return happ ``LCNF.LetValue.sproj #[← q i, ← q o, ← q x]
    | .fap n args => return happ ``LCNF.LetValue.fap #[← q n, ← q args]
    | .pap n args => return happ ``LCNF.LetValue.pap #[← q n, ← q args]
    | .reset i x => return happ ``LCNF.LetValue.reset #[← q i, ← q x]
    | .reuse x i u args => return happ ``LCNF.LetValue.reuse #[← q x, ← q i, ← q u, ← q args]
    | .box t x => return happ ``LCNF.LetValue.box #[← q t, ← q x]
    | .unbox x => return happ ``LCNF.LetValue.unbox #[← q x]
    | .isShared x => return happ ``LCNF.LetValue.isShared #[← q x]
    | .proj _ _ _ h | .const _ _ _ h => nomatch h
  read e := do
    let n := e.getAppFn.constName?.getD .anonymous
    if n == ``LCNF.LetValue.erased then
      let _ ← fields e n 1
      return .erased
    if n == ``LCNF.LetValue.lit then return .lit (← r (← fields e n 2)[1]!)
    if n == ``LCNF.LetValue.fvar then
      let xs ← fields e n 3
      return .fvar (← r xs[1]!) (← r xs[2]!)
    if n == ``LCNF.LetValue.ctor then
      let xs ← fields e n 4
      return .ctor (← r xs[1]!) (← r xs[2]!)
    if n == ``LCNF.LetValue.oproj || n == ``LCNF.LetValue.uproj || n == ``LCNF.LetValue.reset then
      let xs ← fields e n 4
      let i ← r xs[1]!
      let x ← r xs[2]!
      return if n == ``LCNF.LetValue.oproj then .oproj i x else if n == ``LCNF.LetValue.uproj then .uproj i x else .reset i x
    if n == ``LCNF.LetValue.sproj then
      let xs ← fields e n 5
      return .sproj (← r xs[1]!) (← r xs[2]!) (← r xs[3]!)
    if n == ``LCNF.LetValue.fap || n == ``LCNF.LetValue.pap then
      let xs ← fields e n 4
      let fn ← r xs[1]!
      let args ← r xs[2]!
      return if n == ``LCNF.LetValue.fap then .fap fn args else .pap fn args
    if n == ``LCNF.LetValue.reuse then
      let xs ← fields e n 6
      return .reuse (← r xs[1]!) (← r xs[2]!) (← r xs[3]!) (← r xs[4]!)
    if n == ``LCNF.LetValue.box then
      let xs ← fields e n 4
      return .box (← r xs[1]!) (← r xs[2]!)
    if n == ``LCNF.LetValue.unbox || n == ``LCNF.LetValue.isShared then
      let x ← r (← fields e n 3)[1]!
      return if n == ``LCNF.LetValue.unbox then .unbox x else .isShared x
    throw "structural quotation: unsupported impure LetValue"

private instance : Codec (LCNF.LetDecl .impure) where
  type := iapp ``LCNF.LetDecl
  quote x := return iapp ``LCNF.LetDecl.mk #[← q x.fvarId, ← q x.binderName, ← q x.type, ← q x.value]
  read e := do
    let xs ← fields e ``LCNF.LetDecl.mk 5
    return ⟨← r xs[1]!, ← r xs[2]!, ← r xs[3]!, ← r xs[4]!⟩

mutual
private partial def quoteCode : LCNF.Code .impure → Result Expr
  | .let d k => return iapp ``LCNF.Code.let #[← q d, ← quoteCode k]
  | .jp d k => return iapp ``LCNF.Code.jp #[← quoteFun d, ← quoteCode k]
  | .jmp x args => return iapp ``LCNF.Code.jmp #[← q x, ← q args]
  | .cases c => return iapp ``LCNF.Code.cases #[← quoteCases c]
  | .return x => return iapp ``LCNF.Code.return #[← q x]
  | .unreach t => return iapp ``LCNF.Code.unreach #[← q t]
  | .oset x i y k => return happ ``LCNF.Code.oset #[← q x, ← q i, ← q y, ← quoteCode k]
  | .uset x i y k => return happ ``LCNF.Code.uset #[← q x, ← q i, ← q y, ← quoteCode k]
  | .sset x i o y t k => return happ ``LCNF.Code.sset #[← q x, ← q i, ← q o, ← q y, ← q t, ← quoteCode k]
  | .setTag x i k => return happ ``LCNF.Code.setTag #[← q x, ← q i, ← quoteCode k]
  | .inc x n c p k => return happ ``LCNF.Code.inc #[← q x, ← q n, ← q c, ← q p, ← quoteCode k]
  | .dec x n c p os k => return happ ``LCNF.Code.dec #[← q x, ← q n, ← q c, ← q p, ← q os, ← quoteCode k]
  | .del x k => return happ ``LCNF.Code.del #[← q x, ← quoteCode k]
  | .fun _ _ h => nomatch h

private partial def quoteFun (d : LCNF.FunDecl .impure) : Result Expr := do
  return iapp ``LCNF.FunDecl.mk #[← q d.fvarId, ← q d.binderName, ← q d.params, ← q d.type, ← quoteCode d.value]

private partial def quoteCases (c : LCNF.Cases .impure) : Result Expr := do
  let alts ← c.alts.toList.foldrM (fun a tail => do
    return mkAppN (mkConst ``List.cons [.zero]) #[iapp ``LCNF.Alt, ← quoteAlt a, tail])
    (mkApp (mkConst ``List.nil [.zero]) (iapp ``LCNF.Alt))
  let alts := mkAppN (mkConst ``Array.mk [.zero]) #[iapp ``LCNF.Alt, alts]
  return iapp ``LCNF.Cases.mk #[← q c.typeName, ← q c.resultType, ← q c.discr, alts]

private partial def quoteAlt : LCNF.Alt .impure → Result Expr
  | .default k => return iapp ``LCNF.Alt.default #[← quoteCode k]
  | .ctorAlt i k => return happ ``LCNF.Alt.ctorAlt #[← q i, ← quoteCode k]
  | .alt _ _ _ h => nomatch h
end

mutual
private partial def readCode (e : Expr) : Result (LCNF.Code .impure) := do
  let n := e.getAppFn.constName?.getD .anonymous
  if n == ``LCNF.Code.let then
    let xs ← fields e n 3
    return .let (← r xs[1]!) (← readCode xs[2]!)
  if n == ``LCNF.Code.jp then
    let xs ← fields e n 3
    return .jp (← readFun xs[1]!) (← readCode xs[2]!)
  if n == ``LCNF.Code.jmp then
    let xs ← fields e n 3
    return .jmp (← r xs[1]!) (← r xs[2]!)
  if n == ``LCNF.Code.cases then return .cases (← readCases (← fields e n 2)[1]!)
  if n == ``LCNF.Code.return then return .return (← r (← fields e n 2)[1]!)
  if n == ``LCNF.Code.unreach then return .unreach (← r (← fields e n 2)[1]!)
  if n == ``LCNF.Code.oset then
    let xs ← fields e n 6
    return .oset (← r xs[1]!) (← r xs[2]!) (← r xs[3]!) (← readCode xs[4]!)
  if n == ``LCNF.Code.uset then
    let xs ← fields e n 6
    return .uset (← r xs[1]!) (← r xs[2]!) (← r xs[3]!) (← readCode xs[4]!)
  if n == ``LCNF.Code.sset then
    let xs ← fields e n 8
    return .sset (← r xs[1]!) (← r xs[2]!) (← r xs[3]!) (← r xs[4]!) (← r xs[5]!) (← readCode xs[6]!)
  if n == ``LCNF.Code.setTag then
    let xs ← fields e n 5
    return .setTag (← r xs[1]!) (← r xs[2]!) (← readCode xs[3]!)
  if n == ``LCNF.Code.inc then
    let xs ← fields e n 7
    return .inc (← r xs[1]!) (← r xs[2]!) (← r xs[3]!) (← r xs[4]!) (← readCode xs[5]!)
  if n == ``LCNF.Code.dec then
    let xs ← fields e n 8
    return .dec (← r xs[1]!) (← r xs[2]!) (← r xs[3]!) (← r xs[4]!) (← r xs[5]!) (← readCode xs[6]!)
  if n == ``LCNF.Code.del then
    let xs ← fields e n 4
    return .del (← r xs[1]!) (← readCode xs[2]!)
  throw "structural quotation: unsupported impure Code"

private partial def readFun (e : Expr) : Result (LCNF.FunDecl .impure) := do
  let xs ← fields e ``LCNF.FunDecl.mk 6
  return .mk (← r xs[1]!) (← r xs[2]!) (← r xs[3]!) (← r xs[4]!) (← readCode xs[5]!)

private partial def readCases (e : Expr) : Result (LCNF.Cases .impure) := do
  let xs ← fields e ``LCNF.Cases.mk 5
  let arr ← fields xs[4]! ``Array.mk 2
  return .mk (← r xs[1]!) (← r xs[2]!) (← r xs[3]!) (← readAlts arr[1]!).toArray

private partial def readAlts (e : Expr) : Result (List (LCNF.Alt .impure)) := do
  if e.getAppFn.isConstOf ``List.nil then
    let _ ← fields e ``List.nil 1
    return []
  let xs ← fields e ``List.cons 3
  return (← readAlt xs[1]!) :: (← readAlts xs[2]!)

private partial def readAlt (e : Expr) : Result (LCNF.Alt .impure) := do
  if e.getAppFn.isConstOf ``LCNF.Alt.default then
    return .default (← readCode (← fields e ``LCNF.Alt.default 2)[1]!)
  let xs ← fields e ``LCNF.Alt.ctorAlt 4
  return .ctorAlt (← r xs[1]!) (← readCode xs[2]!)
end

private instance : Codec ExternEntry where
  type := mkConst ``ExternEntry
  quote
    | .opaque => pure (app ``ExternEntry.opaque)
    | .adhoc n => return app ``ExternEntry.adhoc #[← q n]
    | .inline n s => return app ``ExternEntry.inline #[← q n, ← q s]
    | .standard n s => return app ``ExternEntry.standard #[← q n, ← q s]
  read e := do
    if e == app ``ExternEntry.opaque then return .opaque
    if e.getAppFn.isConstOf ``ExternEntry.adhoc then
      return .adhoc (← r (← fields e ``ExternEntry.adhoc 1)[0]!)
    if e.getAppFn.isConstOf ``ExternEntry.inline then
      let xs ← fields e ``ExternEntry.inline 2
      return .inline (← r xs[0]!) (← r xs[1]!)
    let xs ← fields e ``ExternEntry.standard 2
    return .standard (← r xs[0]!) (← r xs[1]!)

private instance : Codec ExternAttrData where
  type := mkConst ``ExternAttrData
  quote x := return app ``ExternAttrData.mk #[← q x.entries]
  read e := do return ⟨← r (← fields e ``ExternAttrData.mk 1)[0]!⟩

private instance : Codec (LCNF.DeclValue .impure) where
  type := iapp ``LCNF.DeclValue
  quote
    | .code c => return iapp ``LCNF.DeclValue.code #[← quoteCode c]
    | .extern d => return iapp ``LCNF.DeclValue.extern #[← q d]
  read e := do
    if e.getAppFn.isConstOf ``LCNF.DeclValue.code then
      return .code (← readCode (← fields e ``LCNF.DeclValue.code 2)[1]!)
    return .extern (← r (← fields e ``LCNF.DeclValue.extern 2)[1]!)

private def inlineName : InlineAttributeKind → Name
  | .inline => ``InlineAttributeKind.inline
  | .noinline => ``InlineAttributeKind.noinline
  | .macroInline => ``InlineAttributeKind.macroInline
  | .inlineIfReduce => ``InlineAttributeKind.inlineIfReduce
  | .alwaysInline => ``InlineAttributeKind.alwaysInline

private instance : Codec InlineAttributeKind where
  type := mkConst ``InlineAttributeKind
  quote x := pure (app (inlineName x))
  read e := do
    for x in [InlineAttributeKind.inline, .noinline, .macroInline, .inlineIfReduce, .alwaysInline] do
      if e == app (inlineName x) then return x
    throw "structural quotation: unsupported inline attribute"

private instance : Codec (LCNF.Signature .impure) where
  type := iapp ``LCNF.Signature
  quote x := return iapp ``LCNF.Signature.mk #[← q x.name, ← q x.levelParams, ← q x.type, ← q x.params, ← q x.safe]
  read e := do
    let xs ← fields e ``LCNF.Signature.mk 6
    return ⟨← r xs[1]!, ← r xs[2]!, ← r xs[3]!, ← r xs[4]!, ← r xs[5]!⟩

private instance : Codec (LCNF.Decl .impure) where
  type := iapp ``LCNF.Decl
  quote x := return iapp ``LCNF.Decl.mk #[← q x.toSignature, ← q x.value, ← q x.recursive, ← q x.inlineAttr?]
  read e := do
    let xs ← fields e ``LCNF.Decl.mk 5
    return ⟨← r xs[1]!, ← r xs[2]!, ← r xs[3]!, ← r xs[4]!⟩

/-- Quote every field, including names and embedded expressions, without executing the program. -/
def quoteProgram (program : ImpureProgram) : Result Expr := do
  return app ``Program.mk #[phase, ← q program.decls]

/-- Read only the canonical constructor grammar. Re-quotation rejects malformed
type arguments, purity witnesses, overlarge integer payloads and extra syntax. -/
def readProgram (e : Expr) : Result ImpureProgram := do
  let xs ← fields e ``Program.mk 2
  let program : ImpureProgram := ⟨← r xs[1]!⟩
  unless (← quoteProgram program) == e do
    throw "structural quotation: non-canonical or malformed program"
  return program

private def liftResult (result : Result α) : CoreM α :=
  match result with
  | .ok a => pure a
  | .error e => throwError "{e}"

/-- Wait for kernel checking before readback/lowering, and retain the concrete
body in module-system exports as well as legacy modules. -/
private def addChecked (decl : Declaration) : CoreM Unit := do
  withOptions (fun o => (o.setBool `Elab.async false).setBool `debug.skipKernelTC false) <|
    addDecl decl (forceExpose := true)

/-- Read the body of an existing checked safe definition, with no evaluation or deserialization. -/
def readDefinition (name : Name) : CoreM ImpureProgram := do
  let .defnInfo info ← getConstInfo name
    | throwError "checked LCNF input must be a definition: {name}"
  unless info.safety == .safe && info.levelParams.isEmpty do
    throwError "checked LCNF input must be safe and closed: {name}"
  liftResult (readProgram info.value)

/-- Add an ordinary safe definition through Lean's kernel; then read *that* body
back and check every captured field. Clients lower the returned readback value. -/
def defineProgram (name : Name) (program : ImpureProgram) : CoreM ImpureProgram := do
  let value ← liftResult (quoteProgram program)
  addChecked <| .defnDecl {
    name, levelParams := [], type := mkConst ``ImpureProgram, value
    hints := .abbrev, safety := .safe }
  let checked ← readDefinition name
  unless (← liftResult (quoteProgram checked)) == value do
    throwError "checked LCNF readback differs from capture: {name}"
  return checked

/-- Retain capture metadata, replacing its program only with the checked
definition's canonical readback. Lowerers can consume this artifact unchanged. -/
def defineArtifact (name : Name) (source : Artifact) : CoreM Artifact := do
  return { source with program := ← defineProgram name source.program }

/-- Generate an exact lookup equation and a concrete body equation, both checked
by the kernel using reflexivity. The declaration is selected from the checked program. -/
def defineDeclEquations (programName target declarationName : Name) : MetaM Unit := do
  let program ← readDefinition programName
  let some decl := program.findDecl? target
    | throwError "checked LCNF target absent: {target}"
  let value ← liftResult (q decl)
  let declType := iapp ``LCNF.Decl
  addChecked <| .defnDecl {
    name := declarationName, levelParams := [], type := declType
    value := value, hints := .abbrev, safety := .safe }
  let lhs ← Meta.mkAppM ``Program.findDecl? #[mkConst programName, ← liftResult (q target)]
  let rhs ← Meta.mkAppM ``Option.some #[mkConst declarationName]
  addChecked <| .thmDecl {
    name := declarationName ++ `findDecl, levelParams := []
    type := ← Meta.mkEq lhs rhs, value := ← Meta.mkEqRefl rhs }
  let lhs ← Meta.mkAppM ``LCNF.Decl.value #[mkConst declarationName]
  let rhs ← liftResult (q decl.value)
  addChecked <| .thmDecl {
    name := declarationName ++ `body, levelParams := []
    type := ← Meta.mkEq lhs rhs, value := ← Meta.mkEqRefl rhs }

end Fir.Compiler.Lcnf.Reify
