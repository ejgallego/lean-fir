import Fir.Wasm.Lower

namespace Fir.Wasm

open Lean
open Lean.Compiler

/--
The proof-oriented backend fragment: literals, erased values, constructors,
object/usize/integer-scalar projections, boxing, object mutation, constructor
cases, ownership operations, reset/reuse, exact external calls (including
lazy caching of zero-argument declarations), direct calls, statically tracked
partial applications, closure dispatch, recursion, returns, and unreachable
code. Closure applications use the generated metadata trampoline; the flow
gate deliberately rejects oversaturation and closure values whose provenance
is not statically known.
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

/-- Final-impure cases use either an object tag or the compiler's scalar
`UInt8` constructor-index lane. Other scalar widths are not accepted merely
because they share a physical Wasm representation. -/
def supportedCaseDiscriminatorMode? : AbiKind → Option CaseDiscriminatorMode
  | .object | .tagged | .tobject => some .objectTag
  | .uint8 => some .scalarUInt8
  | _ => none

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

def supportedNamedCall (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (declared : AbiKind) (name : Name)
    (args : Array (LCNF.Arg .impure)) : Bool :=
  match program.findDecl? name with
  | none => false
  | some target =>
      match target.value, abiValueKind? target.type,
          target.params.mapM (fun param => abiValueKind? param.type),
          args.mapM (supportedArgKind? locals) with
      | .extern _, some result, some paramKinds, some argKinds
      | .code _, some result, some paramKinds, some argKinds =>
          result.refines declared && argKinds.size == paramKinds.size &&
            (argKinds.zip paramKinds).all fun pair => pair.fst.refines pair.snd
      | _, _, _, _ => false

def supportedPartialApply (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (declared : AbiKind) (name : Name)
    (args : Array (LCNF.Arg .impure)) : Bool :=
  match program.findDecl? name,
      args.mapM (supportedArgKind? locals) with
  | some target, some argKinds =>
      match target.params.mapM (fun param => abiValueKind? param.type) with
      | some paramKinds =>
          argKinds.size < paramKinds.size && declared.isObjectLike &&
            kindsRefine argKinds (paramKinds.extract 0 argKinds.size)
      | none => false
  | _, _ => false

def supportedClosureCall (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (declared : AbiKind) (closureId : FVarId)
    (args : Array (LCNF.Arg .impure)) : Bool :=
  match findLocalKind? locals closureId,
      args.mapM (supportedArgKind? locals) with
  | some closureKind, some argKinds =>
      if args.isEmpty then closureKind.refines declared
      else closureKind.isObjectLike && program.decls.any fun target =>
        match target.params.mapM (fun param => abiValueKind? param.type),
            abiValueKind? target.type with
        | some paramKinds, some resultKind =>
            argKinds.size <= paramKinds.size &&
              let fixed := paramKinds.size - argKinds.size
              fixed < paramKinds.size &&
                kindsRefine argKinds (paramKinds.extract fixed paramKinds.size) &&
                resultKind.refines declared
        | _, _ => false
  | _, _ => false

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
  | .pap name args =>
      if supportedPartialApply program locals declared name args then
        some declared
      else
        none
  | .fvar closureId args =>
      if supportedClosureCall program locals declared closureId args then
        some declared
      else
        none
  | .fap name args =>
      if supportedNamedCall program locals declared name args then
        some declared
      else
        none
  | value => if supportedLetValue value then some declared else none

def resultKindRefines (actual expected : Option AbiKind) : Bool :=
  match actual, expected with
  | none, none => true
  | some actual, some expected => actual.refines expected
  | _, _ => false

abbrev SupportedCaseFacts := List (FVarId × Nat)
abbrev SupportedSharingFacts := List (FVarId × FVarId)

def findSupportedCaseFact? : SupportedCaseFacts → FVarId → Option Nat
  | [], _ => none
  | (candidate, tag) :: rest, fvarId =>
      if sameFVar candidate fvarId then some tag else findSupportedCaseFact? rest fvarId

def eraseSupportedCaseFact (facts : SupportedCaseFacts) (fvarId : FVarId) :
    SupportedCaseFacts :=
  facts.filter fun entry => !sameFVar entry.fst fvarId

def insertSupportedCaseFact (facts : SupportedCaseFacts) (fvarId : FVarId) (tag : Nat) :
    SupportedCaseFacts :=
  (fvarId, tag) :: eraseSupportedCaseFact facts fvarId

def findSupportedSharingObject? : SupportedSharingFacts → FVarId → Option FVarId
  | [], _ => none
  | (candidate, objectId) :: rest, fvarId =>
      if sameFVar candidate fvarId then some objectId
      else findSupportedSharingObject? rest fvarId

def eraseSupportedSharingFact (facts : SupportedSharingFacts) (fvarId : FVarId) :
    SupportedSharingFacts :=
  facts.filter fun entry => !sameFVar entry.fst fvarId

def insertSupportedSharingFact (facts : SupportedSharingFacts)
    (fvarId objectId : FVarId) : SupportedSharingFacts :=
  (fvarId, objectId) :: eraseSupportedSharingFact facts fvarId

def guardedErasedJoinArgumentSafe (facts : SupportedCaseFacts)
    (sharing : SupportedSharingFacts) (decl : LCNF.FunDecl .impure)
    (args : Array (LCNF.Arg .impure)) (targetParam : LCNF.Param .impure) : Bool :=
  (decl.params.zip args).any fun pair =>
    abiValueKind? pair.fst.type == some .uint8 &&
      match pair.snd with
      | .fvar actualGuard =>
          findSupportedCaseFact? facts actualGuard == some 1 &&
            (findSupportedSharingObject? sharing actualGuard).isSome &&
            fvarUsesOnlyInFalseGuard targetParam.fvarId pair.fst.fvarId false decl.value
      | _ => false

def supportedJumpArgs (locals : LocalKinds) (facts : SupportedCaseFacts)
    (sharing : SupportedSharingFacts) (decl : LCNF.FunDecl .impure)
    (args : Array (LCNF.Arg .impure)) : Bool :=
  args.size == decl.params.size &&
    (decl.params.zip args).all fun pair =>
      match joinParamAbiKind? decl pair.fst, supportedArgKind? locals pair.snd with
      | some expected, some actual =>
          actual.refines expected ||
            (actual == .erased && expected == .object &&
              guardedErasedJoinArgumentSafe facts sharing decl args pair.fst)
      | _, _ => false

mutual

partial def supportedCodeWithJoins (program : Fir.LeanIR.ImpureProgram)
    (joins : JoinPoints) (locals : LocalKinds) (expectedResult : Option AbiKind)
    (facts : SupportedCaseFacts) (sharing : SupportedSharingFacts) :
    LCNF.Code .impure → Bool
  | .let decl continuation =>
      match supportedLetDeclKind? program locals decl with
      | some kind =>
          let sharing :=
            match decl.value with
            | .isShared objectId =>
                insertSupportedSharingFact sharing decl.fvarId objectId
            | _ => eraseSupportedSharingFact sharing decl.fvarId
          supportedCodeWithJoins program joins (insertLocal locals decl.fvarId kind)
            expectedResult facts sharing continuation
      | none => false
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      let joins := (decl.fvarId, decl) :: joins
      match decl.params.foldlM (init := locals) (fun locals param => do
          let kind ← joinParamAbiKind? decl param
          some (insertLocal locals param.fvarId kind)) with
      | some bodyLocals =>
          abiTypeKnown decl.type &&
            resultKindRefines (abiValueKind? decl.type) expectedResult &&
            supportedCodeWithJoins program joins bodyLocals
              (abiValueKind? decl.type) [] [] decl.value &&
            supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
      | none => false
  | .jmp fvarId args =>
      match findJoinPoint? joins fvarId with
      | some decl =>
          resultKindRefines (abiValueKind? decl.type) expectedResult &&
            supportedJumpArgs locals facts sharing decl args
      | none => false
  | .cases cases =>
      let resultKnown := abiTypeKnown cases.resultType
      let altsSupported :=
        match findLocalKind? locals cases.discr with
        | some kind =>
            match supportedCaseDiscriminatorMode? kind with
            | some mode =>
                cases.alts.all (supportedAltWithJoins program joins locals expectedResult
                  facts sharing mode cases.discr)
            | none => false
        | none => false
      resultKnown &&
        resultKindRefines (abiValueKind? cases.resultType) expectedResult &&
        altsSupported
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
            supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
      | _, _ => false
  | .uset objectId _ fieldId continuation =>
      findLocalKind? locals objectId == some .object &&
        findLocalKind? locals fieldId == some .usize &&
        supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
  | .sset objectId _ _ fieldId type continuation =>
      match findLocalKind? locals objectId, findLocalKind? locals fieldId,
          abiValueKind? type with
      | some .object, some fieldKind, some annotationKind =>
          fieldKind == annotationKind && supportedScalarProjectionKind fieldKind &&
            supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
      | _, _, _ => false
  | .setTag objectId _ continuation =>
      findLocalKind? locals objectId == some .object &&
        supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
  | .inc objectId _ _ persistent continuation =>
      if persistent then
        supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
      else
        (findLocalKind? locals objectId).any AbiKind.isObjectLike &&
          supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
  | .dec objectId _ _ persistent _ continuation =>
      if persistent then
        supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
      else
        (findLocalKind? locals objectId).any AbiKind.isObjectLike &&
          supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
  | .del objectId continuation =>
      findLocalKind? locals objectId == some .object &&
        supportedCodeWithJoins program joins locals expectedResult facts sharing continuation

partial def supportedAltWithJoins (program : Fir.LeanIR.ImpureProgram)
    (joins : JoinPoints) (locals : LocalKinds) (expectedResult : Option AbiKind)
    (facts : SupportedCaseFacts) (sharing : SupportedSharingFacts)
    (mode : CaseDiscriminatorMode) (discr : FVarId) : LCNF.Alt .impure → Bool
  | .ctorAlt info code =>
      caseConstructorTagFits mode info &&
        supportedCodeWithJoins program joins locals expectedResult
          (insertSupportedCaseFact facts discr info.cidx) sharing code
  | .default code => supportedCodeWithJoins program joins locals expectedResult
      (eraseSupportedCaseFact facts discr) sharing code
  | .alt _ _ _ h => nomatch h

end

def supportedCode (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (expectedResult : Option AbiKind) :
    LCNF.Code .impure → Bool :=
  supportedCodeWithJoins program [] locals expectedResult [] []

def supportedAlt (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (expectedResult : Option AbiKind)
    (mode : CaseDiscriminatorMode) : LCNF.Alt .impure → Bool :=
  supportedAltWithJoins program [] locals expectedResult [] [] mode ⟨`discr⟩

structure ClosureShape where
  function : Name
  arity : Nat
  fixed : Nat
  deriving Inhabited, BEq

abbrev ClosureShapes := List (FVarId × ClosureShape)

def findClosureShape? : ClosureShapes → FVarId → Option ClosureShape
  | [], _ => none
  | (candidate, shape) :: rest, fvarId =>
      if candidate.name == fvarId.name then some shape
      else findClosureShape? rest fvarId

def insertClosureShape (shapes : ClosureShapes) (fvarId : FVarId)
    (shape? : Option ClosureShape) : ClosureShapes :=
  let rest := shapes.filter fun entry => entry.fst.name != fvarId.name
  match shape? with
  | some shape => (fvarId, shape) :: rest
  | none => rest

def closureResultShape? (program : Fir.LeanIR.ImpureProgram)
    (shapes : ClosureShapes) : LCNF.LetValue .impure → Option ClosureShape
  | .pap name args => do
      let target ← program.findDecl? name
      if args.size < target.params.size then
        some { function := name, arity := target.params.size, fixed := args.size }
      else
        none
  | .fvar fvarId args => do
      let shape ← findClosureShape? shapes fvarId
      let newFixed := shape.fixed + args.size
      if args.isEmpty then some shape
      else if newFixed < shape.arity then some { shape with fixed := newFixed }
      else none
  | _ => none

def closureApplicationSafe (shapes : ClosureShapes) : LCNF.LetValue .impure → Bool
  | .fvar fvarId args =>
      if args.isEmpty then (findClosureShape? shapes fvarId).isSome
      else
        (findClosureShape? shapes fvarId).any fun shape =>
          shape.fixed + args.size <= shape.arity
  | _ => true

mutual

partial def closureFlowSafeCode (program : Fir.LeanIR.ImpureProgram)
    (shapes : ClosureShapes) : LCNF.Code .impure → Bool
  | .let decl continuation =>
      closureApplicationSafe shapes decl.value &&
        closureFlowSafeCode program
          (insertClosureShape shapes decl.fvarId
            (closureResultShape? program shapes decl.value)) continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      let bodyShapes := decl.params.foldl (init := shapes) fun shapes param =>
        insertClosureShape shapes param.fvarId none
      closureFlowSafeCode program bodyShapes decl.value &&
        closureFlowSafeCode program shapes continuation
  | .jmp .. => true
  | .cases cases => cases.alts.all (closureFlowSafeAlt program shapes)
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation => closureFlowSafeCode program shapes continuation
  | .return .. | .unreach .. => true

partial def closureFlowSafeAlt (program : Fir.LeanIR.ImpureProgram)
    (shapes : ClosureShapes) : LCNF.Alt .impure → Bool
  | .ctorAlt _ code | .default code => closureFlowSafeCode program shapes code
  | .alt _ _ _ h => nomatch h

end

def closureFlowSafeProgram (program : Fir.LeanIR.ImpureProgram) : Bool :=
  program.decls.all fun decl =>
    match decl.value with
    | .code code => closureFlowSafeCode program [] code
    | .extern _ => true

def supportedDecl (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) : Bool :=
  abiTypeKnown decl.type &&
    match addSupportedParams? [] decl.params, decl.value with
    | some _, .extern _ => true
    | some locals, .code code =>
        supportedCode program locals (abiValueKind? decl.type) code
    | _, _ => false

def supportedProgram (program : Fir.LeanIR.ImpureProgram) : Bool :=
  program.decls.all (supportedDecl program) && closureFlowSafeProgram program

/-- Proposition used as the domain of the initial lowering theorem. -/
def WasmSupported (program : Fir.LeanIR.ImpureProgram) : Prop :=
  supportedProgram program = true

inductive ValidationError where
  | externalDeclaration (name : Name)
  | unsupportedCode (name : Name)
  deriving Inhabited, BEq, Repr

def validateSupportedDecl (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) : Except ValidationError Unit := do
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
