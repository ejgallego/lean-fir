import Fir.Wasm.Lower
import Fir.Wasm.Concrete.Layout

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

/-- Declaration parameters occupy one source scope and therefore must have
distinct free-variable identities. The symbolic Wasm local namespace has the
same requirement. -/
def declarationParameterIdsUnique (decl : LCNF.Decl .impure) : Bool :=
  let ids := decl.params.toList.map (·.fvarId)
  ids.all fun id => (ids.filter (sameFVar id)).length == 1

/-- Scalar field values represented by the shared impure runtime.
`USize` uses the distinct `uproj` instruction. -/
def supportedScalarProjectionKind : AbiKind → Bool
  | .uint8 | .uint16 | .uint32 | .uint64 | .float32 | .float => true
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

def addSupportedDeclarationParams? (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) (locals : LocalKinds := []) :
    Option LocalKinds := do
  decl.params.foldlM (init := locals) fun locals param => do
    if !abiTypeKnown param.type then none
    match abiValueKind? param.type with
    | none => some locals
    | some _ => do
        let kind ← declarationParamKind? program decl param
        some (insertLocal locals param.fvarId kind)

def supportedArgKind? (locals : LocalKinds) : LCNF.Arg .impure → Option AbiKind
  | .erased => some .erased
  | .fvar fvarId => findLocalKind? locals fvarId
  | .type _ h => nomatch h

/-- Validate the fixed capture descriptor against the effective declaration
parameter kinds selected by the lowerer. -/
def supportedPartialArgumentKinds? (locals : LocalKinds)
    (args : Array (LCNF.Arg .impure)) (expected : Array AbiKind) :
    Option (Array AbiKind) := do
  if args.size != expected.size then none
  (args.zip expected).mapM fun pair => do
    let actual ← supportedArgKind? locals pair.fst
    if actual.refines pair.snd then some actual else none

def supportedNamedCall (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (declared : AbiKind) (name : Name)
    (args : Array (LCNF.Arg .impure)) : Bool :=
  match program.findDecl? name with
  | none => false
  | some target =>
      match target.value, effectiveDeclarationResultKind? target,
          declarationParameterKinds? program target,
          args.mapM (supportedArgKind? locals) with
      | .extern _, some result, some paramKinds, some argKinds
      | .code _, some result, some paramKinds, some argKinds =>
          result.leanCompatible declared && argKinds.size == paramKinds.size &&
            (argKinds.zip paramKinds).all fun pair =>
              pair.fst.leanCompatible pair.snd
      | _, _, _, _ => false

def supportedPartialApply (program : Fir.LeanIR.ImpureProgram)
    (locals : LocalKinds) (declared : AbiKind) (name : Name)
    (args : Array (LCNF.Arg .impure)) : Bool :=
  match program.findDecl? name,
      args.mapM (supportedArgKind? locals) with
  | some target, some argKinds =>
      match declarationParameterKinds? program target with
      | some paramKinds =>
          argKinds.size < paramKinds.size && declared.isObjectLike &&
            (supportedPartialArgumentKinds? locals args
              (paramKinds.extract 0 argKinds.size)).isSome
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
        match declarationParameterKinds? program target,
            effectiveDeclarationResultKind? target with
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
      let resultKind := boxResultKind type .tobject
      if annotationKind == scalarKind && supportedBoxScalarKind scalarKind &&
          (declared == .tobject || declared == resultKind) then
        some resultKind
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
      if supportedNamedCall program locals declared name args then do
        let target ← program.findDecl? name
        effectiveDeclarationResultKind? target
      else none
  | value => if supportedLetValue value then some declared else none

def resultKindCompatible (actual expected : Option AbiKind) : Bool :=
  match actual, expected with
  | none, none => true
  | some actual, some expected => actual.leanCompatible expected
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

/--
The false result of `isShared actualObject` refines that exact `tobject` value
to a heap object: tagged values always report shared. The join-body check keeps
the refined parameter out of every path where that fact is unavailable.
-/
def guardedObjectJoinArgumentSafe (facts : SupportedCaseFacts)
    (sharing : SupportedSharingFacts) (decl : LCNF.FunDecl .impure)
    (args : Array (LCNF.Arg .impure)) (targetParam : LCNF.Param .impure)
    (targetArg : LCNF.Arg .impure) : Bool :=
  match targetArg with
  | .fvar actualObject =>
      (decl.params.zip args).any fun pair =>
        abiValueKind? pair.fst.type == some .uint8 &&
          match pair.snd with
          | .fvar actualGuard =>
              findSupportedCaseFact? facts actualGuard == some 0 &&
                (match findSupportedSharingObject? sharing actualGuard with
                | some sharingObject => sameFVar sharingObject actualObject
                | none => false) &&
                fvarUsesOnlyInFalseGuard targetParam.fvarId pair.fst.fvarId false decl.value
          | _ => false
  | _ => false

def supportedJumpArgs (locals : LocalKinds) (facts : SupportedCaseFacts)
    (sharing : SupportedSharingFacts) (decl : LCNF.FunDecl .impure)
    (args : Array (LCNF.Arg .impure)) : Bool :=
  args.size == decl.params.size &&
    (decl.params.zip args).all fun pair =>
      match joinParamAbiKind? decl pair.fst, supportedArgKind? locals pair.snd with
      | some expected, some actual =>
          actual.leanCompatible expected ||
            (actual == .erased && expected == .object &&
              guardedErasedJoinArgumentSafe facts sharing decl args pair.fst) ||
            (actual == .tobject && expected == .object &&
              guardedObjectJoinArgumentSafe facts sharing decl args pair.fst pair.snd)
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
            resultKindCompatible (abiValueKind? decl.type) expectedResult &&
            supportedCodeWithJoins program joins bodyLocals
              (abiValueKind? decl.type) [] [] decl.value &&
            supportedCodeWithJoins program joins locals expectedResult facts sharing continuation
      | none => false
  | .jmp fvarId args =>
      match findJoinPoint? joins fvarId with
      | some decl =>
          resultKindCompatible (abiValueKind? decl.type) expectedResult &&
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
        resultKindCompatible (abiValueKind? cases.resultType) expectedResult &&
        altsSupported
  | .return fvarId =>
      match findLocalKind? locals fvarId, expectedResult with
      | some actual, some expected => actual.leanCompatible expected
      | _, _ => false
  | .unreach type =>
      abiTypeKnown type && resultKindCompatible (abiValueKind? type) expectedResult
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

/--
Static evidence carried from a constructor value through `reset` to `reuse`.

`emptyToken` means that resetting the value can only produce the zero reuse
token. `retainedAtLeast bytes` means that every nonzero token produced by
reset retains an allocation of at least `bytes`; reset may still produce zero
for a shared or persistent object.
-/
inductive ReuseCapacityEvidence where
  | emptyToken
  | retainedAtLeast (bytes : Nat)
  deriving Inhabited, BEq, Repr

abbrev ReuseCapacityFacts := List (FVarId × ReuseCapacityEvidence)

def eraseReuseCapacityFact (facts : ReuseCapacityFacts) (fvarId : FVarId) :
    ReuseCapacityFacts :=
  facts.filter fun entry => entry.fst.name != fvarId.name

def insertReuseCapacityFact (facts : ReuseCapacityFacts) (fvarId : FVarId)
    (evidence : ReuseCapacityEvidence) : ReuseCapacityFacts :=
  (fvarId, evidence) :: eraseReuseCapacityFact facts fvarId

def findReuseCapacityEvidence? : ReuseCapacityFacts → FVarId →
    Option ReuseCapacityEvidence
  | [], _ => none
  | (candidate, evidence) :: rest, fvarId =>
      if candidate.name == fvarId.name then some evidence
      else findReuseCapacityEvidence? rest fvarId

def constructorAllocatesHeap (info : LCNF.CtorInfo) : Bool :=
  info.size != 0 || info.usize != 0 || info.ssize != 0

def constructorReuseCapacityEvidence (info : LCNF.CtorInfo) :
    ReuseCapacityEvidence :=
  if constructorAllocatesHeap info then
    .retainedAtLeast (Concrete.ConstructorLayout.ofInfo info).allocationBytes
  else
    .emptyToken

/--
An empty token always allocates fresh storage. A nonempty token is safe only
when the replacement fits the lower bound carried from its reset source.
-/
def ReuseCapacityEvidence.fits (evidence : ReuseCapacityEvidence)
    (info : LCNF.CtorInfo) : Bool :=
  match evidence with
  | .emptyToken => true
  | .retainedAtLeast bytes =>
      decide ((Concrete.ConstructorLayout.ofInfo info).allocationBytes ≤ bytes)

/--
Capacity evidence for the value returned by a successful reuse. A definitely
empty token follows ordinary constructor allocation. Otherwise either the
operation allocated fresh storage or it retained a fitting old allocation, so
the replacement layout is a valid lower bound for subsequent reuse.
-/
def ReuseCapacityEvidence.afterReuse (evidence : ReuseCapacityEvidence)
    (info : LCNF.CtorInfo) : ReuseCapacityEvidence :=
  match evidence with
  | .emptyToken => constructorReuseCapacityEvidence info
  | .retainedAtLeast _ =>
      .retainedAtLeast (Concrete.ConstructorLayout.ofInfo info).allocationBytes

def findFittingReuseCapacityEvidence? (facts : ReuseCapacityFacts)
    (tokenId : FVarId) (info : LCNF.CtorInfo) :
    Option ReuseCapacityEvidence := do
  let evidence ← findReuseCapacityEvidence? facts tokenId
  if evidence.fits info then some evidence else none

/-
Conservative wasm32 retained-capacity analysis for reset/reuse.

Facts are created by direct constructor allocation and preserved through
successful fitting reuse. Unknown object-producing operations remain
admissible, but a later reuse of a token reset from such an object is rejected
until a stronger provenance theorem is supplied. Join parameters likewise do
not inherit facts implicitly.
-/

private theorem reuseCapacity_caseAlts_sizeOf_lt (cases : LCNF.Cases .impure) :
    sizeOf cases.alts.toList < sizeOf (LCNF.Code.cases cases) := by
  rcases cases with ⟨typeName, resultType, discr, alts⟩
  rcases alts with ⟨alts⟩
  simp [LCNF.Cases.alts]
  omega

private theorem reuseCapacity_funDeclValue_sizeOf_lt
    (declaration : LCNF.FunDecl .impure)
    (continuation : LCNF.Code .impure) :
    sizeOf declaration.value <
      sizeOf (LCNF.Code.jp declaration continuation) := by
  cases declaration
  simp_wf
  simp only [LCNF.FunDecl.value]
  omega

/-- Authoritative static fact transfer for one result-producing `let`.
`none` is the validator's rejection of a reuse whose token provenance is
unknown or whose retained allocation is too small. -/
def reuseCapacityLetFacts? (facts : ReuseCapacityFacts)
    (decl : LCNF.LetDecl .impure) : Option ReuseCapacityFacts :=
  match decl.value with
  | .ctor info _ =>
      some (insertReuseCapacityFact facts decl.fvarId
        (constructorReuseCapacityEvidence info))
  | .reset _ objectId =>
      some <| match findReuseCapacityEvidence? facts objectId with
        | some evidence => insertReuseCapacityFact facts decl.fvarId evidence
        | none => eraseReuseCapacityFact facts decl.fvarId
  | .reuse tokenId info _ _ =>
      match findFittingReuseCapacityEvidence? facts tokenId info with
      | some evidence =>
          some (insertReuseCapacityFact facts decl.fvarId
            (evidence.afterReuse info))
      | none => none
  | _ => some (eraseReuseCapacityFact facts decl.fvarId)

mutual

def reuseCapacitySafeCode (facts : ReuseCapacityFacts) :
    LCNF.Code .impure → Bool
  | .let decl continuation =>
      match reuseCapacityLetFacts? facts decl with
      | some nextFacts => reuseCapacitySafeCode nextFacts continuation
      | none => false
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      reuseCapacitySafeCode facts decl.value &&
        reuseCapacitySafeCode facts continuation
  | .cases cases => reuseCapacitySafeAlts facts cases.alts.toList
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation => reuseCapacitySafeCode facts continuation
  | .jmp .. | .return .. | .unreach .. => true

termination_by code => sizeOf code
decreasing_by
  all_goals simp_all <;> try omega
  all_goals first
    | apply reuseCapacity_caseAlts_sizeOf_lt
    | apply reuseCapacity_funDeclValue_sizeOf_lt

def reuseCapacitySafeAlts (facts : ReuseCapacityFacts) :
    List (LCNF.Alt .impure) → Bool
  | [] => true
  | .ctorAlt _ code :: rest
  | .default code :: rest =>
      reuseCapacitySafeCode facts code && reuseCapacitySafeAlts facts rest
  | .alt _ _ _ h :: _ => nomatch h

termination_by alts => sizeOf alts
decreasing_by all_goals simp_all <;> omega

end

def reuseCapacitySafeProgram (program : Fir.LeanIR.ImpureProgram) : Bool :=
  program.decls.all fun decl =>
    match decl.value with
    | .code code => reuseCapacitySafeCode [] code
    | .extern _ => true

theorem ReuseCapacityEvidence.retainedAtLeast_fits_iff
    (available : Nat) (info : LCNF.CtorInfo) :
    (ReuseCapacityEvidence.retainedAtLeast available).fits info = true ↔
      (Concrete.ConstructorLayout.ofInfo info).allocationBytes ≤ available := by
  simp [ReuseCapacityEvidence.fits]

/--
The reuse gate can return evidence only when it came from the token's tracked
provenance and fits the concrete replacement layout.
-/
theorem findFittingReuseCapacityEvidence?_eq_some
    (facts : ReuseCapacityFacts) (tokenId : FVarId)
    (info : LCNF.CtorInfo) (evidence : ReuseCapacityEvidence)
    (found :
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence) :
    findReuseCapacityEvidence? facts tokenId = some evidence ∧
      evidence.fits info = true := by
  cases trackedEq : findReuseCapacityEvidence? facts tokenId with
  | none =>
      simp [findFittingReuseCapacityEvidence?, trackedEq] at found
  | some tracked =>
      by_cases fits : tracked.fits info = true
      · simp [findFittingReuseCapacityEvidence?, trackedEq, fits] at found
        subst tracked
        exact ⟨rfl, fits⟩
      · simp [findFittingReuseCapacityEvidence?, trackedEq, fits] at found

theorem findFittingReuseCapacityEvidence?_retained_layoutFits
    (facts : ReuseCapacityFacts) (tokenId : FVarId)
    (info : LCNF.CtorInfo) (available : Nat)
    (found : findFittingReuseCapacityEvidence? facts tokenId info =
      some (.retainedAtLeast available)) :
    (Concrete.ConstructorLayout.ofInfo info).allocationBytes ≤ available := by
  have fits :=
    (findFittingReuseCapacityEvidence?_eq_some facts tokenId info
      (.retainedAtLeast available) found).2
  exact
    (ReuseCapacityEvidence.retainedAtLeast_fits_iff available info).mp fits

/-- An accepted result-producing head checks its continuation under the
authoritative fact transfer. -/
theorem reuseCapacitySafeCode_let_head
    (facts nextFacts : ReuseCapacityFacts)
    (decl : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure)
    (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
    (safe : reuseCapacitySafeCode facts (.let decl continuation) = true) :
    reuseCapacitySafeCode nextFacts continuation = true := by
  simpa only [reuseCapacitySafeCode, transfer] using safe

/--
Every reuse at the head of an accepted code spine has tracked, fitting
capacity evidence. This is the decomposition rule used by the
syntax-directed concrete simulation.
-/
theorem reuseCapacitySafeCode_reuse_head
    (facts : ReuseCapacityFacts) (decl : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure) (tokenId : FVarId)
    (info : LCNF.CtorInfo) (updateHeader : Bool)
    (args : Array (LCNF.Arg .impure))
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (safe : reuseCapacitySafeCode facts (.let decl continuation) = true) :
    ∃ evidence,
      findFittingReuseCapacityEvidence? facts tokenId info = some evidence ∧
        findReuseCapacityEvidence? facts tokenId = some evidence ∧
        evidence.fits info = true := by
  cases found :
      findFittingReuseCapacityEvidence? facts tokenId info with
  | some evidence =>
    have tracked :=
      findFittingReuseCapacityEvidence?_eq_some facts tokenId info evidence found
    exact ⟨evidence, rfl, tracked⟩
  | none =>
    simp [reuseCapacitySafeCode, reuseCapacityLetFacts?, valueEq, found] at safe

theorem reuseCapacitySafeProgram_code
    (program : Fir.LeanIR.ImpureProgram) (decl : LCNF.Decl .impure)
    (code : LCNF.Code .impure)
    (safe : reuseCapacitySafeProgram program = true)
    (member : decl ∈ program.decls)
    (valueEq : decl.value = .code code) :
    reuseCapacitySafeCode [] code = true := by
  unfold reuseCapacitySafeProgram at safe
  have declSafe := (Array.all_eq_true'.mp safe) decl member
  simpa [valueEq] using declSafe

def supportedDecl (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) : Bool :=
  declarationParameterIdsUnique decl && abiTypeKnown decl.type &&
    match addSupportedDeclarationParams? program decl, decl.value with
    | some _, .extern _ => true
    | some locals, .code code =>
        supportedCode program locals (effectiveDeclarationResultKind? decl) code
    | _, _ => false

def supportedProgram (program : Fir.LeanIR.ImpureProgram) : Bool :=
  program.decls.all (supportedDecl program) &&
    closureFlowSafeProgram program &&
    reuseCapacitySafeProgram program

/-- Proposition used as the domain of the initial lowering theorem. -/
def WasmSupported (program : Fir.LeanIR.ImpureProgram) : Prop :=
  supportedProgram program = true

theorem WasmSupported.reuseCapacitySafe
    {program : Fir.LeanIR.ImpureProgram} (supported : WasmSupported program) :
    reuseCapacitySafeProgram program = true := by
  simp [WasmSupported, supportedProgram] at supported
  exact supported.2

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
  | .code code =>
      unless supportedDecl program decl && reuseCapacitySafeCode [] code do
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
