import Fir.Wasm.Lower

namespace Fir.Wasm

open Lean
open Lean.Compiler

/--
The proof-oriented backend fragment: literals, erased values, constructors,
object/usize/integer-scalar projections, boxing, object mutation, constructor
cases, ownership operations, reset/reuse, exact external calls (including
lazy caching of zero-argument declarations), returns, and unreachable code.
Internal calls, joins, closures, indirect dispatch, and recursion remain
deliberate later gates.
-/
def supportedLetValue : LCNF.LetValue .impure → Bool
  | .lit _ | .erased | .ctor _ _ | .oproj _ _ => true
  | .proj _ _ _ h | .const _ _ _ h => nomatch h
  | .fvar .. | .uproj .. | .sproj .. | .fap .. | .pap .. | .reset ..
  | .reuse .. | .box .. | .unbox .. | .isShared .. => false

def abiTypeKnown (type : Expr) : Bool :=
  match abiKind? type with
  | .ok _ => true
  | .error _ => false

def abiValueKind? (type : Expr) : Option AbiKind :=
  match abiKind? type with
  | .ok kind? => kind?
  | .error _ => none

/-- Scalar field values currently represented by the shared impure runtime.
Float fields remain gated by `FIR-BUG-wasm-none-float-runtime-gap`; `USize`
uses the distinct `uproj` instruction. -/
def supportedScalarProjectionKind : AbiKind → Bool
  | .uint8 | .uint16 | .uint32 | .uint64 => true
  | _ => false

def supportedBoxScalarKind (kind : AbiKind) : Bool :=
  supportedScalarProjectionKind kind || kind == .usize

def addSupportedParams? (locals : LocalKinds) (params : Array (LCNF.Param .impure)) :
    Option LocalKinds :=
  params.foldlM (init := locals) fun locals param => do
    if !abiTypeKnown param.type then
      none
    else
      match abiValueKind? param.type with
      | some kind => some (insertLocal locals param.fvarId kind)
      | none => some locals

def supportedArgKind? (locals : LocalKinds) : LCNF.Arg .impure → Option AbiKind
  | .erased => some .erased
  | .fvar fvarId => findLocalKind? locals fvarId
  | .type _ h => nomatch h

def supportedExternalCall (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (declared : AbiKind) (name : Name)
    (args : Array (LCNF.Arg .impure)) : Bool :=
  match program.findDecl? name with
  | none => false
  | some target =>
      match target.value, abiValueKind? target.type,
          target.params.mapM (fun param => abiValueKind? param.type),
          args.mapM (supportedArgKind? locals) with
      | .extern _, some result, some paramKinds, some argKinds =>
          declared == result && argKinds.size == paramKinds.size &&
            (argKinds.zip paramKinds).all fun pair => pair.fst.refines pair.snd
      | _, _, _, _ => false

def supportedLetDeclKind? (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (decl : LCNF.LetDecl .impure) :
    Option AbiKind := do
  let declared ← abiValueKind? decl.type
  match decl.value with
  | .lit literal =>
      if declared.acceptsLiteralInvariant literal then some declared else none
  | .erased =>
      if declared == .erased then some declared else none
  | .ctor info args =>
      let kinds ← args.mapM (supportedArgKind? locals)
      if constructorTagFitsI32 info && info.size == args.size &&
          kinds.all AbiKind.isObjectField &&
          (constructorKind info).refines declared then
        some declared
      else
        none
  | .oproj _ objectId =>
      let objectKind ← findLocalKind? locals objectId
      if (objectKind == .object || objectKind == .tobject) && declared.isObjectField then
        some declared
      else
        none
  | .uproj _ objectId =>
      let objectKind ← findLocalKind? locals objectId
      if (objectKind == .object || objectKind == .tobject) && declared == .usize then
        some declared
      else
        none
  | .sproj _ _ objectId =>
      let objectKind ← findLocalKind? locals objectId
      if (objectKind == .object || objectKind == .tobject) &&
          supportedScalarProjectionKind declared then
        some declared
      else
        none
  | .box type scalarId =>
      let scalarKind ← findLocalKind? locals scalarId
      let annotationKind ← abiValueKind? type
      if annotationKind == scalarKind && supportedBoxScalarKind scalarKind &&
          declared == .tobject then
        some declared
      else
        none
  | .unbox objectId =>
      let objectKind ← findLocalKind? locals objectId
      if objectKind.isObjectLike && supportedBoxScalarKind declared then
        some declared
      else
        none
  | .isShared objectId =>
      let objectKind ← findLocalKind? locals objectId
      if objectKind.isObjectLike && declared == .uint8 then
        some declared
      else
        none
  | .reset _ objectId =>
      let objectKind ← findLocalKind? locals objectId
      if objectKind.isObjectLike then some .reuseToken else none
  | .reuse tokenId info _ args =>
      let tokenKind ← findLocalKind? locals tokenId
      let kinds ← args.mapM (supportedArgKind? locals)
      if tokenKind == .reuseToken && constructorTagFitsI32 info &&
          info.size == args.size && kinds.all AbiKind.isObjectField &&
          (constructorKind info).refines declared then
        some declared
      else
        none
  | .fap name args =>
      if supportedExternalCall program locals declared name args then
        some declared
      else
        none
  | value => if supportedLetValue value then some declared else none

def resultKindRefines (actual expected : Option AbiKind) : Bool :=
  match actual, expected with
  | none, none => true
  | some actual, some expected => actual.refines expected
  | _, _ => false

mutual

partial def supportedCode (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (expectedResult : Option AbiKind) :
    LCNF.Code .impure → Bool
  | .let decl continuation =>
      match supportedLetDeclKind? program locals decl with
      | some kind => supportedCode program (insertLocal locals decl.fvarId kind)
          expectedResult continuation
      | none => false
  | .fun _ _ h => nomatch h
  | .cases cases =>
      let resultKnown := abiTypeKnown cases.resultType
      let discrSupported :=
        (findLocalKind? locals cases.discr).any AbiKind.isObjectLike
      resultKnown && discrSupported &&
        resultKindRefines (abiValueKind? cases.resultType) expectedResult &&
        cases.alts.all (supportedAlt program locals expectedResult)
  | .return fvarId =>
      match findLocalKind? locals fvarId, expectedResult with
      | some actual, some expected => actual.refines expected
      | _, _ => false
  | .unreach type =>
      abiTypeKnown type && resultKindRefines (abiValueKind? type) expectedResult
  | .oset objectId _ arg continuation =>
      match findLocalKind? locals objectId, supportedArgKind? locals arg with
      | some .object, some fieldKind =>
          fieldKind.isObjectField &&
            supportedCode program locals expectedResult continuation
      | _, _ => false
  | .uset objectId _ fieldId continuation =>
      findLocalKind? locals objectId == some .object &&
        findLocalKind? locals fieldId == some .usize &&
        supportedCode program locals expectedResult continuation
  | .sset objectId _ _ fieldId type continuation =>
      match findLocalKind? locals objectId, findLocalKind? locals fieldId,
          abiValueKind? type with
      | some .object, some fieldKind, some annotationKind =>
          fieldKind == annotationKind && supportedScalarProjectionKind fieldKind &&
            supportedCode program locals expectedResult continuation
      | _, _, _ => false
  | .setTag objectId _ continuation =>
      findLocalKind? locals objectId == some .object &&
        supportedCode program locals expectedResult continuation
  | .inc objectId _ _ persistent continuation =>
      if persistent then
        supportedCode program locals expectedResult continuation
      else
        (findLocalKind? locals objectId).any AbiKind.isObjectLike &&
          supportedCode program locals expectedResult continuation
  | .dec objectId _ _ persistent _ continuation =>
      if persistent then
        supportedCode program locals expectedResult continuation
      else
        (findLocalKind? locals objectId).any AbiKind.isObjectLike &&
          supportedCode program locals expectedResult continuation
  | .del objectId continuation =>
      findLocalKind? locals objectId == some .object &&
        supportedCode program locals expectedResult continuation
  | .jp .. | .jmp .. => false

partial def supportedAlt (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (expectedResult : Option AbiKind) :
    LCNF.Alt .impure → Bool
  | .ctorAlt info code =>
      constructorTagFitsI32 info &&
        supportedCode program locals expectedResult code
  | .default code => supportedCode program locals expectedResult code
  | .alt _ _ _ h => nomatch h

end

def supportedDecl (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) : Bool :=
  !decl.recursive && abiTypeKnown decl.type &&
    match addSupportedParams? [] decl.params, decl.value with
    | some _, .extern _ => true
    | some locals, .code code =>
        supportedCode program locals (abiValueKind? decl.type) code
    | _, _ => false

def supportedProgram (program : Fir.LeanIR.ImpureProgram) : Bool :=
  program.decls.all (supportedDecl program)

/-- Proposition used as the domain of the initial lowering theorem. -/
def WasmSupported (program : Fir.LeanIR.ImpureProgram) : Prop :=
  supportedProgram program = true

inductive ValidationError where
  | recursiveDeclaration (name : Name)
  | externalDeclaration (name : Name)
  | unsupportedCode (name : Name)
  deriving Inhabited, BEq, Repr

def validateSupportedDecl (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) : Except ValidationError Unit := do
  if decl.recursive then
    throw (.recursiveDeclaration decl.name)
  match decl.value with
  | .extern _ =>
      unless supportedDecl program decl do
        throw (.externalDeclaration decl.name)
  | .code _ =>
      unless supportedDecl program decl do
        throw (.unsupportedCode decl.name)

def validateSupported (program : Fir.LeanIR.ImpureProgram) : Except ValidationError Unit :=
  program.decls.forM (validateSupportedDecl program)

inductive SupportedLoweringError where
  | validation (error : ValidationError)
  | lowering (error : CompileError)
  deriving Inhabited, BEq, Repr

def lowerSupported (program : Fir.LeanIR.ImpureProgram) :
    Except SupportedLoweringError Module := do
  match validateSupported program with
  | .ok _ => pure ()
  | .error error => throw (.validation error)
  match lower program with
  | .ok module => pure module
  | .error error => throw (.lowering error)

end Fir.Wasm
