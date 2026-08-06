import Fir.Wasm.ABI

namespace Fir.Wasm

open Lean
open Lean.Compiler

inductive CallTarget where
  | declaration (name : Name)
  | runtime (operation : RuntimeOp)
  deriving Inhabited, BEq

inductive Instruction where
  | i32Const (kind : AbiKind) (value : UInt32)
  | i64Const (kind : AbiKind) (value : UInt64)
  /-- A bit-exact IEEE-754 binary64 constant. -/
  | f64Const (bits : UInt64)
  | localGet (fvarId : FVarId)
  /-- Read a `tobject` local under a proved `isShared(value) == 0` heap refinement. -/
  | localGetObject (fvarId : FVarId)
  | localSet (fvarId : FVarId)
  | globalGet (index : Nat) (kind : AbiKind)
  | globalSet (index : Nat) (kind : AbiKind)
  | call (target : CallTarget)
  | i32Eq
  /-- Physical wasm32 bit operations used inside Wasm-resident runtime helpers. -/
  | i32And
  | i32ShrU
  /-- Physical wasm32 arithmetic/comparison used by resident allocation helpers. -/
  | i32Add
  | i32Sub
  | i32RemU
  | i32LtU
  /-- Physical wasm64 integer operations used by numeric conversion helpers. -/
  | i64Or
  | i64Shl
  | i64ShrU
  | i64LtU
  /-- IEEE-754 binary64 comparisons and arithmetic used by resident externals. -/
  | f64Eq
  | f64Lt
  | f64Le
  | f64Add
  | f64Sub
  | f64Mul
  | f64Div
  | f64Ceil
  | f64Floor
  /-- Load from the module-owned memory at `address + offset`. -/
  | i32Load (result : AbiKind) (offset : UInt32)
  /-- Zero-extend one byte from module-owned memory at `address + offset`. -/
  | i32Load8U (result : AbiKind) (offset : UInt32)
  /-- Zero-extend two bytes from module-owned memory at `address + offset`. -/
  | i32Load16U (result : AbiKind) (offset : UInt32)
  | i64Load (result : AbiKind) (offset : UInt32)
  /-- Store a typed physical lane into module-owned memory. -/
  | i32Store8 (value : AbiKind) (offset : UInt32)
  | i32Store16 (value : AbiKind) (offset : UInt32)
  | i32Store (value : AbiKind) (offset : UInt32)
  | i64Store (value : AbiKind) (offset : UInt32)
  /-- Query or grow the module-owned wasm32 memory in 64-KiB pages. -/
  | memorySize
  | memoryGrow
  /-- Retag the low 32 bits of an i64 physical lane. -/
  | i32WrapI64 (result : AbiKind)
  /-- Zero-extend an i32 physical lane to i64. -/
  | i64ExtendI32U (result : AbiKind)
  /-- Convert an unsigned i64 lane to IEEE-754 binary64. -/
  | f64ConvertI64U
  /-- Lean-compatible saturating conversion from binary64 to unsigned i64. -/
  | i64TruncSatF64U (result : AbiKind)
  /-- Preserve the exact 32-bit payload while retagging an `f32` lane as `i32`. -/
  | i32ReinterpretF32 (result : AbiKind)
  /-- Preserve the exact 64-bit payload while retagging an `f64` lane as `i64`. -/
  | i64ReinterpretF64 (result : AbiKind)
  /-- Preserve the exact 32-bit payload while retagging an `i32` lane as `f32`. -/
  | f32ReinterpretI32 (result : AbiKind)
  /-- Preserve the exact 64-bit payload while retagging an `i64` lane as `f64`. -/
  | f64ReinterpretI64 (result : AbiKind)
  | block (label : FVarId) (body : List Instruction)
  /-- Structured repetition; branching to `label` starts the next iteration. -/
  | loop (label : FVarId) (body : List Instruction)
  | ifElse (thenBody elseBody : List Instruction)
  | br (label : FVarId)
  | ret
  | unreachable
  deriving Inhabited, BEq

structure Function where
  name : Name
  params : Array (FVarId × AbiKind)
  results : Array AbiKind
  locals : Array (FVarId × AbiKind)
  body : List Instruction
  deriving Inhabited, BEq

structure MemoryDecl where
  pagesMin : UInt32
  pagesMax : Option UInt32 := none
  exportName : Option String := none
  deriving Inhabited, BEq

inductive GlobalInit where
  | i32 (value : UInt32)
  | i64 (value : UInt64)
  | f32 (bits : UInt32)
  | f64 (bits : UInt64)
  deriving Inhabited, BEq, Repr

def GlobalInit.valueType : GlobalInit → ValueType
  | .i32 _ => .i32
  | .i64 _ => .i64
  | .f32 _ => .f32
  | .f64 _ => .f64

/--
An initialized mutable Wasm global owned by resident runtime code. These
globals are appended after the lazy-cache flag/value pairs, preserving every
existing cache index while giving resident helpers stable private state.
-/
structure GlobalDecl where
  kind : AbiKind
  init : GlobalInit
  deriving Inhabited, BEq, Repr

structure Module where
  imports : Array Import
  functions : Array Function
  exports : Array Name
  initializers : Array Name
  runtimeOperations : Array RuntimeOp
  /--
  Stable target-ID table for concrete closure headers. Unlike runtime imports,
  this metadata survives resident-runtime internalization.
  -/
  closureDispatch : Array Name := #[]
  /--
  Stable descriptor-ID table for concrete closure capture layouts. This
  survives removal of every `partialApply` runtime import.
  -/
  closureDescriptors : Array (Array AbiKind) := #[]
  /-- Optional module-owned wasm32 memory. Existing semantic-host modules omit it. -/
  memory : Option MemoryDecl := none
  /-- Resident-runtime globals, physically appended after lazy-cache globals. -/
  globals : Array GlobalDecl := #[]
  deriving Inhabited, BEq

inductive CompileError where
  | abi (error : AbiError)
  | unknownVariable (fvarId : FVarId)
  | unknownDeclaration (name : Name)
  | unknownJoinPoint (fvarId : FVarId)
  | arityMismatch (expected actual : Nat)
  | malformed (message : String)
  deriving Inhabited, BEq, Repr

abbrev LocalKinds := List (FVarId × AbiKind)
abbrev JoinPoints := List (FVarId × LCNF.FunDecl .impure)

structure Context where
  program : Fir.LeanIR.ImpureProgram
  localKinds : LocalKinds
  joins : JoinPoints := []
  cachedDeclarations : Array Name := #[]

def addUniqueName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

mutual

partial def collectCachedCallsCode (names : Array Name) :
    LCNF.Code .impure → Array Name
  | .let decl continuation =>
      let names :=
        match decl.value with
        | .fap name args => if args.isEmpty then addUniqueName names name else names
        | _ => names
      collectCachedCallsCode names continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      collectCachedCallsCode (collectCachedCallsCode names decl.value) continuation
  | .cases cases => cases.alts.foldl collectCachedCallsAlt names
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation => collectCachedCallsCode names continuation
  | .jmp .. | .return .. | .unreach .. => names

partial def collectCachedCallsAlt (names : Array Name) :
    LCNF.Alt .impure → Array Name
  | .ctorAlt _ code | .default code => collectCachedCallsCode names code
  | .alt _ _ _ h => nomatch h

end

def cachedDeclarationNames (program : Fir.LeanIR.ImpureProgram) : Array Name :=
  program.decls.foldl (init := #[]) fun names decl =>
    match decl.value with
    | .code code => collectCachedCallsCode names code
    | .extern _ => names

def insertLocal (locals : LocalKinds) (fvarId : FVarId) (kind : AbiKind) : LocalKinds :=
  (fvarId, kind) :: locals.filter fun entry => entry.fst.name != fvarId.name

def findLocalKind? : LocalKinds → FVarId → Option AbiKind
  | [], _ => none
  | (candidate, kind) :: rest, fvarId =>
      if candidate.name == fvarId.name then some kind else findLocalKind? rest fvarId

/-- The two source representations for which final-impure constructor cases are lowered. -/
inductive CaseDiscriminatorMode where
  | objectTag
  | scalarUInt8
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Select direct scalar comparison only for the compiler's `UInt8` case lane.
All other kinds retain the historical object-tag lowering; `WasmSupported`
separately rejects kinds outside the two accepted modes. -/
def caseDiscriminatorMode (context : Context) (discr : FVarId) :
    CaseDiscriminatorMode :=
  if findLocalKind? context.localKinds discr == some .uint8 then
    .scalarUInt8
  else
    .objectTag

def caseConstructorTagFits : CaseDiscriminatorMode → LCNF.CtorInfo → Bool
  | .objectTag => constructorTagFitsI32
  | .scalarUInt8 => constructorTagFitsUInt8

def caseTagTest (mode : CaseDiscriminatorMode) (discr : FVarId)
    (info : LCNF.CtorInfo) : List Instruction :=
  match mode with
  | .objectTag =>
      [.localGet discr,
        .call (.runtime .getTag),
        .i32Const .uint32 (UInt32.ofNat info.cidx)]
  | .scalarUInt8 =>
      [.localGet discr,
        .i32Const .uint8 (UInt32.ofNat info.cidx)]

def findJoinPoint? : JoinPoints → FVarId → Option (LCNF.FunDecl .impure)
  | [], _ => none
  | (candidate, decl) :: rest, fvarId =>
      if candidate.name == fvarId.name then some decl else findJoinPoint? rest fvarId

def checkedAbiKind? (type : Expr) : Except CompileError (Option AbiKind) :=
  match abiKind? type with
  | .ok kind? => pure kind?
  | .error error => throw (.abi error)

def checkedAbiKind (type : Expr) : Except CompileError AbiKind :=
  match abiKind type with
  | .ok kind => pure kind
  | .error error => throw (.abi error)

def sameFVar (left right : FVarId) : Bool :=
  left.name == right.name

def argReferencesFVar (target : FVarId) : LCNF.Arg .impure → Bool
  | .erased => false
  | .fvar fvarId => sameFVar target fvarId
  | .type _ h => nomatch h

def argsReferenceFVar (target : FVarId) (args : Array (LCNF.Arg .impure)) : Bool :=
  args.any (argReferencesFVar target)

def letValueReferencesFVar (target : FVarId) : LCNF.LetValue .impure → Bool
  | .lit _ | .erased => false
  | .proj _ _ _ h | .const _ _ _ h => nomatch h
  | .fvar fvarId args => sameFVar target fvarId || argsReferenceFVar target args
  | .ctor _ args | .fap _ args | .pap _ args => argsReferenceFVar target args
  | .oproj _ fvarId | .uproj _ fvarId | .sproj _ _ fvarId
  | .reset _ fvarId | .box _ fvarId | .unbox fvarId | .isShared fvarId =>
      sameFVar target fvarId
  | .reuse fvarId _ _ args =>
      sameFVar target fvarId || argsReferenceFVar target args

/-- One argument position either does not mention the tracked parameter or
forwards it exactly to a parameter whose final-LCNF type is erased. -/
def argUsesOnlyAtErasedParameter (tracked : FVarId)
    (param : LCNF.Param .impure) (arg : LCNF.Arg .impure) : Bool :=
  match arg with
  | .erased => true
  | .fvar fvarId =>
      !sameFVar tracked fvarId || param.type == LCNF.ImpureType.erased
  | .type _ h => nomatch h

/-- Check the tracked parameter's uses in one statically named call. -/
def namedArgsUseOnlyAtErasedParameters (program : Fir.LeanIR.ImpureProgram)
    (tracked : FVarId) (name : Name) (args : Array (LCNF.Arg .impure)) : Bool :=
  if !argsReferenceFVar tracked args then
    true
  else
    match program.findDecl? name with
    | some target =>
        args.size <= target.params.size &&
          ((target.params.extract 0 args.size).zip args |>.all fun pair =>
            argUsesOnlyAtErasedParameter tracked pair.fst pair.snd)
    | none => false

/-- A let-value use is admissible for an erased-only parameter exactly when
it is forwarded through a statically named erased parameter. -/
def letValueUsesOnlyAtErasedParameters (program : Fir.LeanIR.ImpureProgram)
    (tracked : FVarId) : LCNF.LetValue .impure → Bool
  | .fap name args | .pap name args =>
      namedArgsUseOnlyAtErasedParameters program tracked name args
  | value => !letValueReferencesFVar tracked value

/-
Conservative structural recognizer for the compiler's erased type-parameter
facade. A tracked parameter may be absent or forwarded through named erased
parameters, but may not participate in a value operation, ownership effect,
closure call, branch, case, or return.
-/
mutual

partial def fvarUsesOnlyAtErasedParameters
    (program : Fir.LeanIR.ImpureProgram) (tracked : FVarId) :
    LCNF.Code .impure → Bool
  | .let decl continuation =>
      !sameFVar decl.fvarId tracked &&
        letValueUsesOnlyAtErasedParameters program tracked decl.value &&
        fvarUsesOnlyAtErasedParameters program tracked continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      !decl.params.any (fun param => sameFVar param.fvarId tracked) &&
        fvarUsesOnlyAtErasedParameters program tracked decl.value &&
        fvarUsesOnlyAtErasedParameters program tracked continuation
  | .jmp _ args => !argsReferenceFVar tracked args
  | .cases cases =>
      !sameFVar tracked cases.discr &&
        cases.alts.all (fvarUsesOnlyAtErasedParametersAlt program tracked)
  | .return fvarId => !sameFVar tracked fvarId
  | .unreach _ => true
  | .oset objectId _ arg continuation =>
      !(sameFVar tracked objectId || argReferencesFVar tracked arg) &&
        fvarUsesOnlyAtErasedParameters program tracked continuation
  | .uset objectId _ fieldId continuation
  | .sset objectId _ _ fieldId _ continuation =>
      !(sameFVar tracked objectId || sameFVar tracked fieldId) &&
        fvarUsesOnlyAtErasedParameters program tracked continuation
  | .setTag objectId _ continuation
  | .inc objectId _ _ _ continuation
  | .dec objectId _ _ _ _ continuation
  | .del objectId continuation =>
      !sameFVar tracked objectId &&
        fvarUsesOnlyAtErasedParameters program tracked continuation

partial def fvarUsesOnlyAtErasedParametersAlt
    (program : Fir.LeanIR.ImpureProgram) (tracked : FVarId) :
    LCNF.Alt .impure → Bool
  | .ctorAlt _ code | .default code =>
      fvarUsesOnlyAtErasedParameters program tracked code
  | .alt _ _ _ h => nomatch h

end

def namedArgsForwardToErasedParameter (program : Fir.LeanIR.ImpureProgram)
    (tracked : FVarId) (name : Name) (args : Array (LCNF.Arg .impure)) : Bool :=
  match program.findDecl? name with
  | some target =>
      ((target.params.extract 0 args.size).zip args).any fun pair =>
        match pair.snd with
        | .fvar fvarId =>
            sameFVar tracked fvarId && pair.fst.type == LCNF.ImpureType.erased
        | .erased => false
        | .type _ h => nomatch h
  | none => false

def letValueForwardsToErasedParameter (program : Fir.LeanIR.ImpureProgram)
    (tracked : FVarId) : LCNF.LetValue .impure → Bool
  | .fap name args | .pap name args =>
      namedArgsForwardToErasedParameter program tracked name args
  | _ => false

mutual

partial def fvarForwardedToErasedParameter
    (program : Fir.LeanIR.ImpureProgram) (tracked : FVarId) :
    LCNF.Code .impure → Bool
  | .let decl continuation =>
      letValueForwardsToErasedParameter program tracked decl.value ||
        fvarForwardedToErasedParameter program tracked continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      fvarForwardedToErasedParameter program tracked decl.value ||
        fvarForwardedToErasedParameter program tracked continuation
  | .cases cases =>
      cases.alts.any (fvarForwardedToErasedParameterAlt program tracked)
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation =>
      fvarForwardedToErasedParameter program tracked continuation
  | .jmp .. | .return .. | .unreach .. => false

partial def fvarForwardedToErasedParameterAlt
    (program : Fir.LeanIR.ImpureProgram) (tracked : FVarId) :
    LCNF.Alt .impure → Bool
  | .ctorAlt _ code | .default code =>
      fvarForwardedToErasedParameter program tracked code
  | .alt _ _ _ h => nomatch h

end

/-- A compiler-declared `tobject` parameter which is semantically erased by
every use in its declaration body. -/
def erasedOnlyParameter (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) (param : LCNF.Param .impure) : Bool :=
  param.type == LCNF.ImpureType.tobject &&
    match decl.value with
    | .code code =>
        fvarUsesOnlyAtErasedParameters program param.fvarId code &&
          fvarForwardedToErasedParameter program param.fvarId code
    | .extern _ => false

/-
Check the source-level control invariant emitted by Lean 4.32's
`ExpandResetReuse`: an optional object parameter may be consumed only below
the constructor-zero arm of its companion `UInt8` sharing discriminator.
The explicit `del` operation is the sole exception because the shared runtime
contract treats its erased failed-reset sentinel as a no-op.
-/
mutual

partial def fvarUsesOnlyInFalseGuard (target guard : FVarId) (guarded : Bool) :
    LCNF.Code .impure → Bool
  | .let decl continuation =>
      !sameFVar decl.fvarId target && !sameFVar decl.fvarId guard &&
        (!letValueReferencesFVar target decl.value || guarded) &&
        fvarUsesOnlyInFalseGuard target guard guarded continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      !decl.params.any (fun param =>
          sameFVar param.fvarId target || sameFVar param.fvarId guard) &&
        fvarUsesOnlyInFalseGuard target guard guarded decl.value &&
        fvarUsesOnlyInFalseGuard target guard guarded continuation
  | .jmp _ args => !argsReferenceFVar target args || guarded
  | .cases cases =>
      (!sameFVar target cases.discr || guarded) &&
        cases.alts.all (fvarUsesOnlyInFalseGuardAlt target guard guarded cases.discr)
  | .return fvarId => !sameFVar target fvarId || guarded
  | .unreach _ => true
  | .oset objectId _ arg continuation =>
      (!(sameFVar target objectId || argReferencesFVar target arg) || guarded) &&
        fvarUsesOnlyInFalseGuard target guard guarded continuation
  | .uset objectId _ fieldId continuation
  | .sset objectId _ _ fieldId _ continuation =>
      (!(sameFVar target objectId || sameFVar target fieldId) || guarded) &&
        fvarUsesOnlyInFalseGuard target guard guarded continuation
  | .setTag objectId _ continuation
  | .inc objectId _ _ _ continuation
  | .dec objectId _ _ _ _ continuation =>
      (!sameFVar target objectId || guarded) &&
        fvarUsesOnlyInFalseGuard target guard guarded continuation
  | .del _ continuation =>
      fvarUsesOnlyInFalseGuard target guard guarded continuation

partial def fvarUsesOnlyInFalseGuardAlt (target guard : FVarId) (guarded : Bool)
    (discr : FVarId) : LCNF.Alt .impure → Bool
  | .ctorAlt info code =>
      let guarded := guarded || (sameFVar discr guard && info.cidx == 0)
      fvarUsesOnlyInFalseGuard target guard guarded code
  | .default code => fvarUsesOnlyInFalseGuard target guard guarded code
  | .alt _ _ _ h => nomatch h

end

/-- A `tobject` reset-join parameter whose live path is known to contain a heap object. -/
def guardedObjectJoinParam (decl : LCNF.FunDecl .impure)
    (targetParam : LCNF.Param .impure) : Bool :=
  targetParam.type == LCNF.ImpureType.tobject &&
    decl.params.any fun guardParam =>
      guardParam.type == LCNF.ImpureType.uint8 &&
        fvarUsesOnlyInFalseGuard targetParam.fvarId guardParam.fvarId false decl.value

def joinParamAbiKind? (decl : LCNF.FunDecl .impure)
    (param : LCNF.Param .impure) : Option AbiKind :=
  match abiKind? param.type with
  | .ok (some kind) =>
      if kind == .tobject && guardedObjectJoinParam decl param then some .object else some kind
  | _ => none

def checkedJoinParamKind (decl : LCNF.FunDecl .impure)
    (param : LCNF.Param .impure) : Except CompileError AbiKind := do
  let kind ← checkedAbiKind param.type
  return if kind == .tobject && guardedObjectJoinParam decl param then .object else kind

/--
Refine compiler-declared `tobject` boxes when their source type fixes the
representation. Every `UInt8` payload is tagged; Lean 4.32 always
heap-allocates Float32 and Float boxes. Precise kinds let closure capture and
ownership retain those facts without changing the physical i32 lane.
-/
def boxResultKind (type : Expr) (declared : AbiKind) : AbiKind :=
  if type == LCNF.ImpureType.uint8 then
    .tagged
  else if type == LCNF.ImpureType.float32 || type == LCNF.ImpureType.float then
    .object
  else
    declared

@[simp] theorem boxResultKind_uint8_tobject :
    boxResultKind LCNF.ImpureType.uint8 .tobject = .tagged := by
  have same :
      (LCNF.ImpureType.uint8 == LCNF.ImpureType.uint8) = true := by
    native_decide
  simp only [boxResultKind, same, if_true]

@[simp] theorem boxResultKind_uint16_tobject :
    boxResultKind LCNF.ImpureType.uint16 .tobject = .tobject := by
  have not8 :
      (LCNF.ImpureType.uint16 == LCNF.ImpureType.uint8) = false := by
    native_decide
  have notF32 :
      (LCNF.ImpureType.uint16 == LCNF.ImpureType.float32) = false := by
    native_decide
  have notF :
      (LCNF.ImpureType.uint16 == LCNF.ImpureType.float) = false := by
    native_decide
  simp only [boxResultKind, not8, notF32, notF, Bool.false_or,
    Bool.false_eq_true, if_false]

@[simp] theorem boxResultKind_uint32_tobject :
    boxResultKind LCNF.ImpureType.uint32 .tobject = .tobject := by
  have not8 :
      (LCNF.ImpureType.uint32 == LCNF.ImpureType.uint8) = false := by
    native_decide
  have notF32 :
      (LCNF.ImpureType.uint32 == LCNF.ImpureType.float32) = false := by
    native_decide
  have notF :
      (LCNF.ImpureType.uint32 == LCNF.ImpureType.float) = false := by
    native_decide
  simp only [boxResultKind, not8, notF32, notF, Bool.false_or,
    Bool.false_eq_true, if_false]

@[simp] theorem boxResultKind_uint64_tobject :
    boxResultKind LCNF.ImpureType.uint64 .tobject = .tobject := by
  have not8 :
      (LCNF.ImpureType.uint64 == LCNF.ImpureType.uint8) = false := by
    native_decide
  have notF32 :
      (LCNF.ImpureType.uint64 == LCNF.ImpureType.float32) = false := by
    native_decide
  have notF :
      (LCNF.ImpureType.uint64 == LCNF.ImpureType.float) = false := by
    native_decide
  simp only [boxResultKind, not8, notF32, notF, Bool.false_or,
    Bool.false_eq_true, if_false]

@[simp] theorem boxResultKind_usize_tobject :
    boxResultKind LCNF.ImpureType.usize .tobject = .tobject := by
  have not8 :
      (LCNF.ImpureType.usize == LCNF.ImpureType.uint8) = false := by
    native_decide
  have notF32 :
      (LCNF.ImpureType.usize == LCNF.ImpureType.float32) = false := by
    native_decide
  have notF :
      (LCNF.ImpureType.usize == LCNF.ImpureType.float) = false := by
    native_decide
  simp only [boxResultKind, not8, notF32, notF, Bool.false_or,
    Bool.false_eq_true, if_false]

def letValueKind (decl : LCNF.LetDecl .impure) : Except CompileError AbiKind :=
  match decl.value with
  | .erased => pure .erased
  | .reset .. => pure .reuseToken
  | .box type _ => return boxResultKind type (← checkedAbiKind decl.type)
  | _ => checkedAbiKind decl.type

/-- Proof-relevant parameter kind selected for one complete declaration.
Compiler-declared `tobject` parameters whose uses are structurally erased are
tracked as `.erased`; every other parameter retains its declared ABI kind. -/
def declarationParamKind? (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) (param : LCNF.Param .impure) : Option AbiKind :=
  match abiKind? param.type with
  | .ok (some kind) =>
      if kind == .tobject && erasedOnlyParameter program decl param then
        some .erased
      else
        some kind
  | _ => none

def checkedDeclarationParamKind (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) (param : LCNF.Param .impure) :
    Except CompileError AbiKind := do
  let kind ← checkedAbiKind param.type
  return if kind == .tobject && erasedOnlyParameter program decl param then
    .erased
  else
    kind

def declarationParameterKinds? (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) : Option (Array AbiKind) :=
  decl.params.mapM (declarationParamKind? program decl)

def checkedDeclarationParameterKinds (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) : Except CompileError (Array AbiKind) :=
  decl.params.mapM (checkedDeclarationParamKind program decl)

/-- The refined erased ABI is selected exactly at the structural admission
boundary: the compiler declared an ordinary `tobject` lane, while this
declaration uses it only by forwarding it to a genuinely erased parameter.
This is the proof-facing contract; no declaration-name convention and no
global ABI subtyping rule is involved. -/
theorem declarationParamKind?_eq_erased_iff
    (program : Fir.LeanIR.ImpureProgram) (decl : LCNF.Decl .impure)
    (param : LCNF.Param .impure)
    (declared : abiKind? param.type = .ok (some .tobject)) :
    declarationParamKind? program decl param = some .erased ↔
      erasedOnlyParameter program decl param = true := by
  unfold declarationParamKind?
  rw [declared]
  change (if ((AbiKind.tobject == AbiKind.tobject) &&
      erasedOnlyParameter program decl param) = true then
      some AbiKind.erased else some AbiKind.tobject) = some AbiKind.erased ↔
    erasedOnlyParameter program decl param = true
  have same : (AbiKind.tobject == AbiKind.tobject) = true := by decide
  rw [same]
  simp

def addParams (locals : LocalKinds) (params : Array (LCNF.Param .impure)) :
    Except CompileError LocalKinds := do
  params.foldlM (init := locals) fun locals param => do
    match ← checkedAbiKind? param.type with
    | some kind => return insertLocal locals param.fvarId kind
    | none => return locals

/-- Add declaration parameters using the same erased-only refinement consumed
by partial-application descriptors and closure dispatch. -/
def addDeclarationParams (program : Fir.LeanIR.ImpureProgram)
    (decl : LCNF.Decl .impure) (locals : LocalKinds := []) :
    Except CompileError LocalKinds := do
  decl.params.foldlM (init := locals) fun locals param => do
    match ← checkedAbiKind? param.type with
    | none => return locals
    | some kind =>
        let kind :=
          if kind == .tobject && erasedOnlyParameter program decl param then
            .erased
          else
            kind
        return insertLocal locals param.fvarId kind

def addJoinParams (locals : LocalKinds) (decl : LCNF.FunDecl .impure) :
    Except CompileError LocalKinds := do
  decl.params.foldlM (init := locals) fun locals param => do
    let kind ← checkedJoinParamKind decl param
    return insertLocal locals param.fvarId kind

partial def collectLocals (locals : LocalKinds) :
    LCNF.Code .impure → Except CompileError LocalKinds
  | .let decl continuation => do
      let kind ← letValueKind decl
      collectLocals (insertLocal locals decl.fvarId kind) continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation => do
      let locals ← addJoinParams locals decl
      let locals ← collectLocals locals decl.value
      collectLocals locals continuation
  | .jmp .. | .return .. | .unreach .. => pure locals
  | .cases cases => do
      cases.alts.foldlM (init := locals) fun locals alt =>
        match alt with
        | .ctorAlt _ code => collectLocals locals code
        | .default code => collectLocals locals code
        | .alt _ _ _ h => nomatch h
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation => collectLocals locals continuation

def compileArg (context : Context) :
    LCNF.Arg .impure → Except CompileError (List Instruction × AbiKind)
  | .erased => .ok ([.i32Const .erased 0], .erased)
  | .fvar fvarId =>
      match findLocalKind? context.localKinds fvarId with
      | some kind => .ok ([.localGet fvarId], kind)
      | none => .error (.unknownVariable fvarId)
  | .type _ h => nomatch h

def compileArgs (context : Context) (args : Array (LCNF.Arg .impure)) :
    Except CompileError (List Instruction × Array AbiKind) := do
  args.foldlM (init := ([], #[])) fun (instructions, kinds) arg => do
    let (argument, kind) ← compileArg context arg
    return (instructions ++ argument, kinds.push kind)

/-- Compile one fixed argument against the effective parameter slot it will
occupy in a closure. Compiler-declared `tobject` parameters which are
structurally erased have already been refined to `.erased`; no global
`erased ≤ tobject` compatibility is introduced here. -/
def compilePartialArgument (context : Context) (expected : AbiKind)
    (arg : LCNF.Arg .impure) :
    Except CompileError (List Instruction × AbiKind) := do
  let (argument, actual) ← compileArg context arg
  if !actual.refines expected then
    throw (.malformed "partial-application argument does not refine its parameter ABI")
  return (argument, actual)

/-- Compile the supplied prefix of a partial application's effective target
parameters. The returned kinds are the exact closure-capture descriptor. -/
def compilePartialArguments (context : Context)
    (target : LCNF.Decl .impure) (args : Array (LCNF.Arg .impure)) :
    Except CompileError (List Instruction × Array AbiKind) := do
  if args.size > target.params.size then
    throw (.malformed "partial application fixes too many parameters")
  let expectedKinds ← checkedDeclarationParameterKinds context.program target
  (expectedKinds.extract 0 args.size).zip args |>.foldlM
    (init := ([], #[])) fun (instructions, kinds) pair => do
      let expected := pair.fst
      let (argument, kind) ← compilePartialArgument context expected pair.snd
      return (instructions ++ argument, kinds.push kind)

def directAbiKind? (type : Expr) : Option AbiKind :=
  match abiKind? type with
  | .ok (some kind) => some kind
  | _ => none

def parameterKinds? (params : Array (LCNF.Param .impure)) : Option (Array AbiKind) :=
  params.mapM fun param => directAbiKind? param.type

def kindsRefine (actual expected : Array AbiKind) : Bool :=
  actual.size == expected.size &&
    (actual.zip expected).all fun pair => pair.fst.refines pair.snd

def compileFixedClosureFields (closureId : FVarId) (target : LCNF.Decl .impure)
    (arity fixed : Nat) (kinds : Array AbiKind) : List Instruction :=
  (List.range fixed).flatMap fun index =>
    match kinds[index]? with
    | some AbiKind.erased => [.i32Const .erased 0]
    | some kind => [
        .localGet closureId,
        .call (.runtime (.closureProj target.name arity fixed index kind))]
    | none => []

def compileClosureCandidateAt (declId closureId : FVarId) (resultKind : AbiKind)
    (argumentCode : List Instruction) (argumentKinds : Array AbiKind)
    (target : LCNF.Decl .impure) (paramKinds : Array AbiKind)
    (fixed : Nat) : Option (List Instruction × List Instruction) := do
  if fixed >= paramKinds.size || fixed + argumentKinds.size > paramKinds.size then none else
  let newFixed := fixed + argumentKinds.size
  let expectedArgs := paramKinds.extract fixed newFixed
  if !kindsRefine argumentKinds expectedArgs then none else
  let matcher := [
    .localGet closureId,
    .call (.runtime (.closureMatches target.name paramKinds.size fixed))]
  let fields :=
    compileFixedClosureFields closureId target paramKinds.size fixed paramKinds ++
      argumentCode
  if newFixed < paramKinds.size then
    if !resultKind.isObjectLike then none else
    let body := fields ++ [
      .call (.runtime (.partialApply target.name paramKinds.size newFixed
        (paramKinds.extract 0 newFixed) resultKind)),
      .localSet declId]
    some (matcher, body)
  else
    let targetResult ← directAbiKind? target.type
    if !targetResult.refines resultKind then none else
    some (matcher, fields ++ [.call (.declaration target.name), .localSet declId])

def compileClosureCandidatesForTarget (program : Fir.LeanIR.ImpureProgram)
    (declId closureId : FVarId)
    (resultKind : AbiKind)
    (argumentCode : List Instruction) (argumentKinds : Array AbiKind)
    (target : LCNF.Decl .impure) : List (List Instruction × List Instruction) :=
  match declarationParameterKinds? program target with
  | none => []
  | some paramKinds =>
      if argumentKinds.isEmpty || argumentKinds.size > paramKinds.size then [] else
      (List.range (paramKinds.size - argumentKinds.size + 1)).filterMap fun fixed =>
        compileClosureCandidateAt declId closureId resultKind argumentCode argumentKinds
          target paramKinds fixed

/-- Build the nested matcher/branch chain used by generated closure dispatch.
Naming this compiler boundary lets correctness proofs follow the exact fold
without duplicating its executable definition. -/
def compileClosureCandidateChain
    (candidates : List (List Instruction × List Instruction)) :
    List Instruction :=
  candidates.foldr (init := [.unreachable]) fun candidate rest =>
    candidate.fst ++ [.ifElse candidate.snd rest]

def compileClosureDispatch (context : Context) (declId closureId : FVarId)
    (resultKind : AbiKind) (argumentCode : List Instruction)
    (argumentKinds : Array AbiKind) : List Instruction :=
  let candidates := context.program.decls.toList.flatMap fun target =>
    compileClosureCandidatesForTarget context.program declId closureId resultKind
      argumentCode argumentKinds target
  compileClosureCandidateChain candidates ++ [.localGet declId]

def getLocal (context : Context) (fvarId : FVarId) :
    Except CompileError (Instruction × AbiKind) :=
  match findLocalKind? context.localKinds fvarId with
  | some kind => .ok (.localGet fvarId, kind)
  | none => .error (.unknownVariable fvarId)

def compileLiteral (result : AbiKind) : LCNF.LitValue → List Instruction
  | .uint8 value => [.i32Const .uint8 (UInt32.ofNat value.toNat)]
  | .uint16 value => [.i32Const .uint16 (UInt32.ofNat value.toNat)]
  | .uint32 value => [.i32Const .uint32 value]
  | .uint64 value => [.i64Const .uint64 value]
  | .usize value => [.i64Const .usize value]
  | value@(.nat _) | value@(.str _) => [.call (.runtime (.literal value result))]

def compileLetValue (context : Context) (decl : LCNF.LetDecl .impure) :
    Except CompileError (List Instruction) := do
  let resultKind ← letValueKind decl
  match decl.value with
  | .lit literal =>
      unless resultKind.acceptsLiteral literal do
        throw (.malformed "literal kind does not match its declaration")
      return compileLiteral resultKind literal
  | .erased => return [.i32Const .erased 0]
  | .proj _ _ _ h => nomatch h
  | .const _ _ _ h => nomatch h
  | .fvar fvarId args =>
      let (function, _) ← getLocal context fvarId
      let (arguments, kinds) ← compileArgs context args
      if args.isEmpty then
        return [function]
      return compileClosureDispatch context decl.fvarId fvarId resultKind arguments kinds
  | .ctor info args =>
      unless constructorTagFitsI32 info do
        throw (.malformed s!"allocated constructor tag {info.cidx} does not fit the i32 tag ABI")
      let (arguments, kinds) ← compileArgs context args
      return arguments ++ [.call (.runtime (.allocCtor info kinds resultKind))]
  | .oproj index fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.objectProj index resultKind))]
  | .uproj index fvarId =>
      let (object, _) ← getLocal context fvarId
      unless resultKind == .usize do
        throw (.malformed "usize projection must produce USize")
      return [object, .call (.runtime (.usizeProj index))]
  | .sproj width offset fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.scalarProj width offset resultKind))]
  | .fap name args =>
      let (arguments, _) ← compileArgs context args
      let some target := context.program.findDecl? name | throw (.unknownDeclaration name)
      if args.isEmpty && target.params.isEmpty then
        let some cacheIndex := context.cachedDeclarations.findIdx? (· == name) |
          throw (.malformed s!"missing lazy cache slot for {name}")
        let flagIndex := 2 * cacheIndex
        let valueIndex := flagIndex + 1
        return [
          .globalGet flagIndex .uint32,
          .ifElse
            []
            ([.call (.declaration name),
              .call (.runtime (.cacheSet name resultKind)),
              .globalSet valueIndex resultKind,
              .i32Const .uint32 1,
              .globalSet flagIndex .uint32]),
          .globalGet valueIndex resultKind]
      else
        return arguments ++ [.call (.declaration name)]
  | .pap name args =>
      let some target := context.program.findDecl? name | throw (.unknownDeclaration name)
      if args.size >= target.params.size then
        throw (.malformed s!"partial application {name} fixes too many parameters")
      let (arguments, kinds) ← compilePartialArguments context target args
      return arguments ++ [
        .call (.runtime (.partialApply name target.params.size args.size kinds resultKind))]
  | .reset count fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.reset count))]
  | .reuse fvarId info updateHeader args =>
      let (token, _) ← getLocal context fvarId
      let (arguments, kinds) ← compileArgs context args
      return token :: arguments ++
        [.call (.runtime (.reuse info updateHeader kinds resultKind))]
  | .box type fvarId =>
      let (scalar, scalarKind) ← getLocal context fvarId
      let annotationKind ← checkedAbiKind type
      if annotationKind != scalarKind then
        throw (.malformed "box operand type does not match its annotation")
      return [scalar, .call (.runtime (.box scalarKind resultKind))]
  | .unbox fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.unbox resultKind))]
  | .isShared fvarId =>
      let (object, _) ← getLocal context fvarId
      unless resultKind == .uint8 do
        throw (.malformed "isShared must produce UInt8")
      return [object, .call (.runtime .isShared)]

/-- Transparent compiler equation for a zero-argument call with an allocated
lazy-cache slot. This fixes the exact flag/value layout and miss sequence used
by the adapter and semantic proofs. -/
theorem compileLetValue_fap_cached
    (context : Context) (fvarId : FVarId) (type : Expr) (name : Name)
    (target : LCNF.Decl .impure) (resultKind : AbiKind) (cacheIndex : Nat)
    (kindEq : checkedAbiKind type = .ok resultKind)
    (targetEq : context.program.findDecl? name = some target)
    (paramsEq : target.params.isEmpty = true)
    (cacheEq : context.cachedDeclarations.findIdx? (· == name) = some cacheIndex) :
    compileLetValue context {
      fvarId
      binderName := fvarId.name
      type
      value := .fap name #[] } = .ok [
        .globalGet (2 * cacheIndex) .uint32,
        .ifElse [] [
          .call (.declaration name),
          .call (.runtime (.cacheSet name resultKind)),
          .globalSet (2 * cacheIndex + 1) resultKind,
          .i32Const .uint32 1,
          .globalSet (2 * cacheIndex) .uint32],
        .globalGet (2 * cacheIndex + 1) resultKind] := by
  simp [compileLetValue, letValueKind, kindEq, compileArgs, targetEq, paramsEq,
    cacheEq]
  rfl

/-- Transparent compiler equation for closure allocation by partial
application. -/
theorem compileLetValue_pap
    (context : Context) (fvarId : FVarId) (type : Expr) (name : Name)
    (args : Array (LCNF.Arg .impure)) (target : LCNF.Decl .impure)
    (resultKind : AbiKind) (argumentCode : List Instruction)
    (argumentKinds : Array AbiKind)
    (kindEq : checkedAbiKind type = .ok resultKind)
    (argumentsEq :
      compilePartialArguments context target args =
        .ok (argumentCode, argumentKinds))
    (targetEq : context.program.findDecl? name = some target)
    (fixedLt : args.size < target.params.size) :
    compileLetValue context {
      fvarId
      binderName := fvarId.name
      type
      value := .pap name args } =
      .ok (argumentCode ++ [
        .call (.runtime (.partialApply name target.params.size args.size
          argumentKinds resultKind))]) := by
  simp [compileLetValue, letValueKind, kindEq, argumentsEq, targetEq,
    Nat.not_le.mpr fixedLt]
  rfl

/-- Transparent compiler equation for nonempty closure application. The
generated trampoline is pure Wasm control flow around semantic metadata and
capture reads; target declarations remain ordinary direct calls. -/
theorem compileLetValue_fvar_dispatch
    (context : Context) (declId closureId : FVarId) (type : Expr)
    (args : Array (LCNF.Arg .impure)) (resultKind closureKind : AbiKind)
    (argumentCode : List Instruction) (argumentKinds : Array AbiKind)
    (kindEq : checkedAbiKind type = .ok resultKind)
    (closureEq : getLocal context closureId =
      .ok (.localGet closureId, closureKind))
    (argumentsEq : compileArgs context args = .ok (argumentCode, argumentKinds))
    (nonempty : args.isEmpty = false) :
    compileLetValue context {
      fvarId := declId
      binderName := declId.name
      type
      value := .fvar closureId args } =
      .ok (compileClosureDispatch context declId closureId resultKind
        argumentCode argumentKinds) := by
  simp [compileLetValue, letValueKind, kindEq, closureEq, argumentsEq, nonempty]
  rfl

def compileJump (context : Context) (fvarId : FVarId) (args : Array (LCNF.Arg .impure)) :
    Except CompileError (List Instruction) := do
  let some decl := findJoinPoint? context.joins fvarId | throw (.unknownJoinPoint fvarId)
  if args.size != decl.params.size then
    throw (.arityMismatch decl.params.size args.size)
  let arguments ← (decl.params.zip args).foldlM (init := []) fun instructions pair => do
    let expected ← checkedJoinParamKind decl pair.fst
    let (argument, actual) ←
      match pair.snd, expected with
      | .erased, .object =>
          /-
          `ExpandResetReuse` uses zero as an optional-object sentinel on its
          guarded slow path. `WasmSupported` proves that the corresponding
          join parameter is dead outside the companion `Bool.false` arm.
          Physically the value is still zero; the annotation records the
          local lane selected by that proved source invariant.
          -/
          pure ([.i32Const .object 0], .object)
      | arg@(.fvar fvarId), .object =>
          let compiled@(_, actual) ← compileArg context arg
          if actual == .tobject && guardedObjectJoinParam decl pair.fst then
            /-
            The support gate ties this exact argument to the companion
            `isShared` discriminator's false path. Tagged values report true,
            so the unchanged physical local is a heap object on this path.
            -/
            pure ([.localGetObject fvarId], .object)
          else
            pure compiled
      | arg, _ => compileArg context arg
    unless actual.refines expected do
      throw (.malformed "jump argument does not refine its join parameter ABI")
    return instructions ++ argument
  let assignments := decl.params.toList.reverse.map fun param => .localSet param.fvarId
  return arguments ++ assignments ++ [.br fvarId]

def compileCaseChainWithM [Monad m] [MonadExceptOf CompileError m]
    (compile : LCNF.Code .impure → m (List Instruction))
    (mode : CaseDiscriminatorMode)
    (discr : FVarId)
    (alts : List (LCNF.Alt .impure)) (fallback : List Instruction) : m (List Instruction) := do
  match alts with
  | [] => return fallback
  | .default _ :: rest => compileCaseChainWithM compile mode discr rest fallback
  | .alt _ _ _ h :: _ => nomatch h
  | .ctorAlt info code :: rest =>
      unless caseConstructorTagFits mode info do
        throw (.malformed s!"constructor tag {info.cidx} does not fit the case discriminator ABI")
      let thenBody ← compile code
      let elseBody ← compileCaseChainWithM compile mode discr rest fallback
      return caseTagTest mode discr info ++ [
        .i32Eq, .ifElse thenBody elseBody]

termination_by sizeOf alts

def compileCaseChainWith
    (compile : LCNF.Code .impure → Except CompileError (List Instruction))
    (mode : CaseDiscriminatorMode)
    (discr : FVarId)
    (alts : List (LCNF.Alt .impure)) (fallback : List Instruction) :
    Except CompileError (List Instruction) :=
  compileCaseChainWithM compile mode discr alts fallback

def isDefaultAlt : LCNF.Alt .impure → Bool
  | .default _ => true
  | _ => false

def compileCaseFallbackWithM [Monad m]
    (compile : LCNF.Code .impure → m (List Instruction))
    (alts : List (LCNF.Alt .impure)) : m (List Instruction) := do
  match alts.find? isDefaultAlt with
  | some (.default code) => compile code
  | some (.alt _ _ _ h) => nomatch h
  | some (.ctorAlt _ _) | none => pure [.unreachable]

/--
Proof-transparent partiality for the recursive compiler. `Option.none` is the
least element used by `partial_fixpoint`; every finite compiler result observed
through `compileCode` is an `Except` value inside `some`.
-/
abbrev CompileM (α : Type) := ExceptT CompileError Option α

def liftCompileResult {α : Type} (result : Except CompileError α) : CompileM α :=
  some result

open Lean.Order in
@[partial_fixpoint_monotone]
theorem monotone_compileCaseChainWithM
    {γ : Type} [PartialOrder γ]
    (compile : γ → LCNF.Code .impure → CompileM (List Instruction))
    (mode : CaseDiscriminatorMode) (discr : FVarId)
    (alts : List (LCNF.Alt .impure)) (fallback : List Instruction)
    (hmono : monotone compile) :
    monotone (fun x => compileCaseChainWithM (compile x) mode discr alts fallback) := by
  induction alts with
  | nil =>
      simp only [compileCaseChainWithM]
      apply monotone_const
  | cons alt alts ih =>
      cases alt with
      | alt _ _ _ impossible => nomatch impossible
      | default code =>
          simp only [compileCaseChainWithM]
          exact ih
      | ctorAlt info code =>
          simp only [compileCaseChainWithM]
          by_cases fits : caseConstructorTagFits mode info = true
          · simp only [fits, ↓reduceIte]
            apply monotone_bind
            · apply monotone_apply
              exact hmono
            · apply monotone_of_monotone_apply
              intro thenBody
              apply monotone_bind
              · exact ih
              · apply monotone_const
          · simp [fits]
            apply monotone_const

open Lean.Order in
@[partial_fixpoint_monotone]
theorem monotone_compileCaseFallbackWithM
    {γ : Type} [PartialOrder γ]
    (compile : γ → LCNF.Code .impure → CompileM (List Instruction))
    (alts : List (LCNF.Alt .impure))
    (hmono : monotone compile) :
    monotone (fun x => compileCaseFallbackWithM (compile x) alts) := by
  intro left right less
  unfold compileCaseFallbackWithM
  generalize foundEq : alts.find? isDefaultAlt = found
  cases found with
  | none => exact PartialOrder.rel_refl
  | some alt =>
      cases alt with
      | alt _ _ _ impossible => nomatch impossible
      | ctorAlt info code => exact PartialOrder.rel_refl
      | default code =>
          exact hmono left right less code

def compileCodeCore (context : Context) : LCNF.Code .impure → CompileM (List Instruction)
  | .let decl continuation => do
      let value ← liftCompileResult (compileLetValue context decl)
      let rest ← compileCodeCore context continuation
      return value ++ [.localSet decl.fvarId] ++ rest
  | .fun _ _ h => nomatch h
  | .jp decl continuation => do
      let context := { context with joins := (decl.fvarId, decl) :: context.joins }
      let entry ← compileCodeCore context continuation
      let body ← compileCodeCore context decl.value
      return [.block decl.fvarId entry] ++ body
  | .jmp fvarId args => liftCompileResult (compileJump context fvarId args)
  | .cases cases => do
      let fallback ← compileCaseFallbackWithM (compileCodeCore context) cases.alts.toList
      compileCaseChainWithM (compileCodeCore context)
        (caseDiscriminatorMode context cases.discr) cases.discr cases.alts.toList fallback
  | .return fvarId => do
      let (value, _) ← liftCompileResult (getLocal context fvarId)
      return [value, .ret]
  | .unreach _ => return [.unreachable]
  | .oset fvarId index arg continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let (field, fieldType) ← liftCompileResult (compileArg context arg)
      let rest ← compileCodeCore context continuation
      return object :: field ++ [.call (.runtime (.objectSet index fieldType))] ++ rest
  | .uset fvarId index fieldId continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let (field, _) ← liftCompileResult (getLocal context fieldId)
      let rest ← compileCodeCore context continuation
      return [object, field, .call (.runtime (.usizeSet index))] ++ rest
  | .sset fvarId width offset fieldId _ continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let (field, fieldType) ← liftCompileResult (getLocal context fieldId)
      let rest ← compileCodeCore context continuation
      return [object, field, .call (.runtime (.scalarSet width offset fieldType))] ++ rest
  | .setTag fvarId tag continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let rest ← compileCodeCore context continuation
      return [object, .call (.runtime (.setTag tag))] ++ rest
  | .inc fvarId amount check persistent continuation => do
      let rest ← compileCodeCore context continuation
      if persistent then return rest
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      return [object, .call (.runtime (.inc amount check))] ++ rest
  | .dec fvarId amount check persistent objectFields? continuation => do
      let rest ← compileCodeCore context continuation
      if persistent then return rest
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      return [object, .call (.runtime (.dec amount check objectFields?))] ++ rest
  | .del fvarId continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let rest ← compileCodeCore context continuation
      return [object, .call (.runtime .delete)] ++ rest
partial_fixpoint

def finishCompileResult {α : Type} (result : CompileM α) : Except CompileError α :=
  result.getD (.error (.malformed "recursive compiler produced no result"))

def compileCode (context : Context) (code : LCNF.Code .impure) :
    Except CompileError (List Instruction) :=
  finishCompileResult (compileCodeCore context code)

theorem finishCompileResult_eq_ok_iff {α : Type} {result : CompileM α} {value : α} :
    finishCompileResult result = .ok value ↔ result = some (.ok value) := by
  cases result with
  | none => simp [finishCompileResult]
  | some result =>
      change result = .ok value ↔ some result = some (.ok value)
      exact ⟨congrArg some, Option.some.inj⟩

/-- Transparent one-layer equation for a successfully compiled `let`. -/
theorem compileCode_let
    {context : Context} {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure} {valueCode restCode : List Instruction}
    (valueCompiled : compileLetValue context decl = .ok valueCode)
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.let decl continuation) =
      .ok (valueCode ++ [.localSet decl.fvarId] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [valueCompiled, restCore]
  rfl

/-- Transparent successful equation for a source return. -/
theorem compileCode_return
    {context : Context} {fvarId : FVarId} {value : Instruction} {kind : AbiKind}
    (localCompiled : getLocal context fvarId = .ok (value, kind)) :
    compileCode context (.return fvarId) = .ok [value, .ret] := by
  apply finishCompileResult_eq_ok_iff.mpr
  rw [compileCodeCore.eq_def]
  simp only
  rw [localCompiled]
  rfl

/-- Transparent successful equation for source unreachability. -/
@[simp] theorem compileCode_unreach (context : Context) (type : Expr) :
    compileCode context (.unreach type) = .ok [.unreachable] := by
  apply finishCompileResult_eq_ok_iff.mpr
  rw [compileCodeCore.eq_def]
  rfl

theorem compileCode_oset
    {context : Context} {objectId : FVarId} {index : Nat}
    {arg : LCNF.Arg .impure} {continuation : LCNF.Code .impure}
    {objectInstruction : Instruction} {objectKind fieldKind : AbiKind}
    {fieldCode restCode : List Instruction}
    (objectCompiled :
      getLocal context objectId = .ok (objectInstruction, objectKind))
    (fieldCompiled : compileArg context arg = .ok (fieldCode, fieldKind))
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.oset objectId index arg continuation) =
      .ok (objectInstruction :: fieldCode ++
        [.call (.runtime (.objectSet index fieldKind))] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [objectCompiled, fieldCompiled, restCore]
  change some (Except.ok (objectInstruction :: fieldCode ++
    [.call (.runtime (.objectSet index fieldKind))] ++ restCode)) = _
  rfl

theorem compileCode_uset
    {context : Context} {objectId fieldId : FVarId} {index : Nat}
    {continuation : LCNF.Code .impure}
    {objectInstruction fieldInstruction : Instruction}
    {objectKind fieldKind : AbiKind} {restCode : List Instruction}
    (objectCompiled :
      getLocal context objectId = .ok (objectInstruction, objectKind))
    (fieldCompiled :
      getLocal context fieldId = .ok (fieldInstruction, fieldKind))
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.uset objectId index fieldId continuation) =
      .ok ([objectInstruction, fieldInstruction,
        .call (.runtime (.usizeSet index))] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [objectCompiled, fieldCompiled, restCore]
  change some (Except.ok ([objectInstruction, fieldInstruction,
    .call (.runtime (.usizeSet index))] ++ restCode)) = _
  rfl

theorem compileCode_sset
    {context : Context} {objectId fieldId : FVarId} {width offset : Nat}
    {type : Expr} {continuation : LCNF.Code .impure}
    {objectInstruction fieldInstruction : Instruction}
    {objectKind fieldKind : AbiKind} {restCode : List Instruction}
    (objectCompiled :
      getLocal context objectId = .ok (objectInstruction, objectKind))
    (fieldCompiled :
      getLocal context fieldId = .ok (fieldInstruction, fieldKind))
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.sset objectId width offset fieldId type continuation) =
      .ok ([objectInstruction, fieldInstruction,
        .call (.runtime (.scalarSet width offset fieldKind))] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [objectCompiled, fieldCompiled, restCore]
  change some (Except.ok ([objectInstruction, fieldInstruction,
    .call (.runtime (.scalarSet width offset fieldKind))] ++ restCode)) = _
  rfl

theorem compileCode_setTag
    {context : Context} {objectId : FVarId} {tag : Nat}
    {continuation : LCNF.Code .impure}
    {objectInstruction : Instruction} {objectKind : AbiKind}
    {restCode : List Instruction}
    (objectCompiled :
      getLocal context objectId = .ok (objectInstruction, objectKind))
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.setTag objectId tag continuation) =
      .ok ([objectInstruction, .call (.runtime (.setTag tag))] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [objectCompiled, restCore]
  change some (Except.ok ([objectInstruction,
    .call (.runtime (.setTag tag))] ++ restCode)) = _
  rfl

theorem compileCode_inc
    {context : Context} {objectId : FVarId} {amount : Nat} {check : Bool}
    {continuation : LCNF.Code .impure} {objectInstruction : Instruction}
    {objectKind : AbiKind} {restCode : List Instruction}
    (objectCompiled :
      getLocal context objectId = .ok (objectInstruction, objectKind))
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.inc objectId amount check false continuation) =
      .ok ([objectInstruction, .call (.runtime (.inc amount check))] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [restCore, objectCompiled]
  change some (Except.ok ([objectInstruction,
    .call (.runtime (.inc amount check))] ++ restCode)) = _
  rfl

theorem compileCode_inc_persistent
    {context : Context} {objectId : FVarId} {amount : Nat} {check : Bool}
    {continuation : LCNF.Code .impure} {restCode : List Instruction}
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.inc objectId amount check true continuation) =
      .ok restCode := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [restCore]
  rfl

theorem compileCode_dec
    {context : Context} {objectId : FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat} {continuation : LCNF.Code .impure}
    {objectInstruction : Instruction} {objectKind : AbiKind}
    {restCode : List Instruction}
    (objectCompiled :
      getLocal context objectId = .ok (objectInstruction, objectKind))
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context
        (.dec objectId amount check false objectFields? continuation) =
      .ok ([objectInstruction,
        .call (.runtime (.dec amount check objectFields?))] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [restCore, objectCompiled]
  change some (Except.ok ([objectInstruction,
    .call (.runtime (.dec amount check objectFields?))] ++ restCode)) = _
  rfl

theorem compileCode_dec_persistent
    {context : Context} {objectId : FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat} {continuation : LCNF.Code .impure}
    {restCode : List Instruction}
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context
        (.dec objectId amount check true objectFields? continuation) =
      .ok restCode := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [restCore]
  rfl

theorem compileCode_delete
    {context : Context} {objectId : FVarId}
    {continuation : LCNF.Code .impure} {objectInstruction : Instruction}
    {objectKind : AbiKind} {restCode : List Instruction}
    (objectCompiled :
      getLocal context objectId = .ok (objectInstruction, objectKind))
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.del objectId continuation) =
      .ok ([objectInstruction, .call (.runtime .delete)] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [objectCompiled, restCore]
  change some (Except.ok
    ([objectInstruction, .call (.runtime .delete)] ++ restCode)) = _
  rfl

def compileCaseChain (context : Context) (discr : FVarId)
    (alts : List (LCNF.Alt .impure)) (fallback : List Instruction) :
    Except CompileError (List Instruction) :=
  compileCaseChainWith (compileCode context) (caseDiscriminatorMode context discr)
    discr alts fallback

def compileCaseFallback (context : Context) (alts : List (LCNF.Alt .impure)) :
    Except CompileError (List Instruction) :=
  compileCaseFallbackWithM (compileCode context) alts

/--
A successful public fallback selection exposes the corresponding recursive
compiler result. This is the bridge needed to unfold the `.cases` equation
without exposing `Option`-based partiality to downstream proofs.
-/
theorem compileCaseFallbackCore_of_compileCaseFallback
    {context : Context} {alts : List (LCNF.Alt .impure)}
    {fallback : List Instruction}
    (compiled : compileCaseFallback context alts = .ok fallback) :
    compileCaseFallbackWithM (compileCodeCore context) alts =
      some (.ok fallback) := by
  unfold compileCaseFallback at compiled
  unfold compileCaseFallbackWithM at compiled ⊢
  generalize foundEq : alts.find? isDefaultAlt = found at compiled ⊢
  cases found with
  | none =>
      change (.ok [.unreachable] : Except CompileError (List Instruction)) =
        .ok fallback at compiled
      change (some (.ok [.unreachable]) : CompileM (List Instruction)) =
        some (.ok fallback)
      exact congrArg some compiled
  | some alt =>
      cases alt with
      | alt _ _ _ impossible => nomatch impossible
      | ctorAlt info code =>
          change (.ok [.unreachable] : Except CompileError (List Instruction)) =
            .ok fallback at compiled
          change (some (.ok [.unreachable]) : CompileM (List Instruction)) =
            some (.ok fallback)
          exact congrArg some compiled
      | default code =>
          change compileCode context code = .ok fallback at compiled
          change compileCodeCore context code = some (.ok fallback)
          exact finishCompileResult_eq_ok_iff.mp compiled

/--
A successful public constructor chain likewise exposes the recursive compiler
result. Constructor bodies are converted one at a time, so the theorem follows
the executable chain rather than duplicating it in a proof-only definition.
-/
theorem compileCaseChainCore_of_compileCaseChain
    {context : Context} {discr : FVarId}
    {alts : List (LCNF.Alt .impure)} {fallback result : List Instruction}
    (compiled : compileCaseChain context discr alts fallback = .ok result) :
    compileCaseChainWithM (compileCodeCore context)
      (caseDiscriminatorMode context discr) discr alts fallback =
      some (.ok result) := by
  induction alts generalizing result with
  | nil =>
      simp [compileCaseChain, compileCaseChainWith, compileCaseChainWithM]
        at compiled ⊢
      exact compiled.symm ▸ rfl
  | cons alt alts ih =>
      cases alt with
      | alt _ _ _ impossible => nomatch impossible
      | default code =>
          rw [compileCaseChainWithM.eq_def]
          apply ih
          change compileCaseChainWithM (compileCode context)
            (caseDiscriminatorMode context discr) discr alts fallback =
            .ok result
          change compileCaseChainWithM (compileCode context)
            (caseDiscriminatorMode context discr) discr
            (.default code :: alts) fallback = .ok result at compiled
          rw [compileCaseChainWithM.eq_def] at compiled
          exact compiled
      | ctorAlt info code =>
          by_cases fits :
              caseConstructorTagFits (caseDiscriminatorMode context discr) info = true
          · cases thenResult : compileCode context code with
            | error error =>
                have fullError :
                    compileCaseChain context discr (.ctorAlt info code :: alts)
                        fallback = .error error := by
                  change compileCaseChainWithM (compileCode context)
                    (caseDiscriminatorMode context discr) discr
                    (.ctorAlt info code :: alts) fallback = .error error
                  rw [compileCaseChainWithM.eq_def]
                  simp only [fits, ↓reduceIte]
                  rw [thenResult]
                  rfl
                rw [fullError] at compiled
                contradiction
            | ok thenBody =>
                cases elseResult : compileCaseChain context discr alts fallback with
                | error error =>
                    have fullError :
                        compileCaseChain context discr
                            (.ctorAlt info code :: alts) fallback = .error error := by
                      change compileCaseChainWithM (compileCode context)
                        (caseDiscriminatorMode context discr) discr
                        (.ctorAlt info code :: alts) fallback = .error error
                      rw [compileCaseChainWithM.eq_def]
                      simp only [fits, ↓reduceIte]
                      rw [thenResult]
                      have elseResult' :
                          compileCaseChainWithM (compileCode context)
                            (caseDiscriminatorMode context discr) discr alts fallback =
                            .error error := elseResult
                      rw [elseResult']
                      rfl
                    rw [fullError] at compiled
                    contradiction
                | ok elseBody =>
                    change compileCaseChainWithM (compileCode context)
                      (caseDiscriminatorMode context discr) discr
                      (.ctorAlt info code :: alts) fallback = .ok result at compiled
                    rw [compileCaseChainWithM.eq_def] at compiled
                    simp only [fits, ↓reduceIte] at compiled
                    rw [thenResult] at compiled
                    have elseResult' :
                        compileCaseChainWithM (compileCode context)
                          (caseDiscriminatorMode context discr) discr alts fallback =
                          .ok elseBody := elseResult
                    rw [elseResult'] at compiled
                    injection compiled with resultEq
                    subst result
                    have thenCore :
                        compileCodeCore context code = some (.ok thenBody) :=
                      finishCompileResult_eq_ok_iff.mp thenResult
                    have elseCore :
                        compileCaseChainWithM (compileCodeCore context)
                          (caseDiscriminatorMode context discr) discr alts fallback =
                          some (.ok elseBody) :=
                      ih elseResult
                    rw [compileCaseChainWithM.eq_def]
                    simp only [fits, ↓reduceIte]
                    rw [thenCore, elseCore]
                    rfl
          · change compileCaseChainWithM (compileCode context)
              (caseDiscriminatorMode context discr) discr
              (.ctorAlt info code :: alts) fallback = .ok result at compiled
            have notFits :
                caseConstructorTagFits (caseDiscriminatorMode context discr) info = false := by
              cases tagFits :
                  caseConstructorTagFits (caseDiscriminatorMode context discr) info with
              | false => rfl
              | true => exact (fits tagFits).elim
            have fullError :
                compileCaseChainWithM (compileCode context)
                    (caseDiscriminatorMode context discr) discr
                    (.ctorAlt info code :: alts) fallback =
                  .error (.malformed
                    s!"constructor tag {info.cidx} does not fit the case discriminator ABI") := by
              rw [compileCaseChainWithM.eq_def]
              simp only [notFits, Bool.false_eq_true, ↓reduceIte]
              rfl
            rw [fullError] at compiled
            contradiction

/-- Transparent successful equation for source constructor cases. -/
theorem compileCode_cases
    {context : Context} {cases : LCNF.Cases .impure}
    {fallback body : List Instruction}
    (fallbackCompiled :
      compileCaseFallback context cases.alts.toList = .ok fallback)
    (bodyCompiled :
      compileCaseChain context cases.discr cases.alts.toList fallback = .ok body) :
    compileCode context (.cases cases) = .ok body := by
  apply finishCompileResult_eq_ok_iff.mpr
  have fallbackCore :=
    compileCaseFallbackCore_of_compileCaseFallback fallbackCompiled
  have bodyCore := compileCaseChainCore_of_compileCaseChain bodyCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [fallbackCore]
  change compileCaseChainWithM (compileCodeCore context)
    (caseDiscriminatorMode context cases.discr) cases.discr
    cases.alts.toList fallback = some (.ok body)
  exact bodyCore

def addUnique [BEq α] (values : Array α) (value : α) : Array α :=
  if values.contains value then values else values.push value

partial def collectRuntimeOpsInstruction (operations : Array RuntimeOp) : Instruction → Array RuntimeOp
  | .call (.runtime operation) => addUnique operations operation
  | .block _ body => body.foldl collectRuntimeOpsInstruction operations
  | .loop _ body => body.foldl collectRuntimeOpsInstruction operations
  | .ifElse thenBody elseBody =>
      elseBody.foldl collectRuntimeOpsInstruction
        (thenBody.foldl collectRuntimeOpsInstruction operations)
  | _ => operations

def collectRuntimeOps (functions : Array Function) : Array RuntimeOp :=
  functions.foldl (init := #[]) fun operations function =>
    function.body.foldl collectRuntimeOpsInstruction operations

def lowerDecl (program : Fir.LeanIR.ImpureProgram)
    (cachedDeclarations : Array Name) (decl : LCNF.Decl .impure) :
    Except CompileError (Option Function) := do
  match decl.value with
  | .extern _ => return none
  | .code code =>
      let paramLocals ← addDeclarationParams program decl
      let allLocals ← collectLocals paramLocals code
      let context : Context := { program, localKinds := allLocals, cachedDeclarations }
      let body ← compileCode context code
      let isParam (fvarId : FVarId) := decl.params.any (·.fvarId.name == fvarId.name)
      let locals := allLocals.reverse.filter fun entry => !isParam entry.fst
      let results ←
        match resultKinds decl.type with
        | .ok results => pure results
        | .error error => throw (.abi error)
      return some {
        name := decl.name
        params := paramLocals.reverse.toArray
        results
        locals := locals.toArray
        body }

def lower (program : Fir.LeanIR.ImpureProgram) : Except CompileError Module := do
  let cachedDeclarations := cachedDeclarationNames program
  let functions ← program.decls.filterMapM (lowerDecl program cachedDeclarations)
  let operations := collectRuntimeOps functions
  unless operations.all RuntimeOp.abiWellFormed do
    throw (.malformed "generated runtime operation violates the semantic ABI")
  let runtimeImports := operations.mapIdx runtimeImport
  let externalImports ← program.decls.filterMapM fun decl =>
    match decl.value with
    | .extern _ => do
        match externalImport decl with
        | .ok import_ => return some import_
        | .error error => throw (.abi error)
    | .code _ => pure none
  let exports := functions.map (·.name)
  return {
    imports := runtimeImports ++ externalImports
    functions
    exports
    initializers := cachedDeclarations
    runtimeOperations := operations
    closureDispatch := collectClosureDispatch operations
    closureDescriptors := collectClosureDescriptors operations }

end Fir.Wasm
