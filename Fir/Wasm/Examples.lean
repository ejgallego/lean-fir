import Fir.Wasm.Lower
import Fir.Wasm.Handle
import Fir.Wasm.Validate
import Fir.Wasm.WellFormed
import Fir.LeanIR.InterpreterExamples

namespace Fir.Wasm

open Lean
open Lean.Compiler
open Fir.LeanIR.InterpreterExamples
open Fir.LeanIR.Impure

def allKinds : Array AbiKind := #[
  .object, .tagged, .tobject, .erased, .reuseToken,
  .uint8, .uint16, .uint32, .uint64, .usize, .float32, .float]

#guard allKinds.map AbiKind.valueType == #[
  .i32, .i32, .i32, .i32, .i32,
  .i32, .i32, .i32, .i64, .i64, .f32, .f64]

def classifiesAs (type : Lean.Expr) (expected : AbiKind) : Bool :=
  match abiKind? type with
  | .ok (some kind) => kind == expected
  | _ => false

#guard classifiesAs LCNF.ImpureType.object .object
#guard classifiesAs LCNF.ImpureType.tagged .tagged
#guard classifiesAs LCNF.ImpureType.tobject .tobject
#guard classifiesAs LCNF.ImpureType.erased .erased
#guard classifiesAs LCNF.ImpureType.uint8 .uint8
#guard classifiesAs LCNF.ImpureType.uint16 .uint16
#guard classifiesAs LCNF.ImpureType.uint32 .uint32
#guard classifiesAs LCNF.ImpureType.uint64 .uint64
#guard classifiesAs LCNF.ImpureType.usize .usize
#guard classifiesAs LCNF.ImpureType.float32 .float32
#guard classifiesAs LCNF.ImpureType.float .float
#guard match abiKind? LCNF.ImpureType.void with
  | .ok none => true
  | _ => false

def unknownAbiType : Lean.Expr := .const `Fir.Wasm.unknownAbiType []

#guard match abiKind? unknownAbiType with
  | .error (.unsupportedType type) => type == unknownAbiType
  | _ => false

#guard ({ params := #[.float32, .float], results := #[.usize] : Signature }).physical ==
  { params := #[.f32, .f64], results := #[.i64] }

#guard (runtimeImport 0 .getTag).key == (runtimeImport 99 .getTag).key
#guard (runtimeImport 0 .getTag).itemName != (runtimeImport 99 .getTag).itemName

def runtimeSignatureCases : Array (RuntimeOp × Signature) := #[
  (.literal (.nat 1) .tobject, { params := #[], results := #[.tobject] }),
  (.allocCtor pairInfo #[.tobject, .tobject] .object,
    { params := #[.tobject, .tobject], results := #[.object] }),
  (.objectProj 0 .tobject, { params := #[.tobject], results := #[.tobject] }),
  (.usizeProj 0, { params := #[.tobject], results := #[.usize] }),
  (.scalarProj 8 0 .uint64, { params := #[.tobject], results := #[.uint64] }),
  (.partialApply `f 2 1 #[.tobject] .object,
    { params := #[.tobject], results := #[.object] }),
  (.closureApply #[.uint32] #[.float],
    { params := #[.tobject, .uint32], results := #[.float] }),
  (.closureMatches `f 2 1,
    { params := #[.tobject], results := #[.uint32] }),
  (.closureProj `f 2 1 0 .tobject,
    { params := #[.tobject], results := #[.tobject] }),
  (.reset 1, { params := #[.tobject], results := #[.reuseToken] }),
  (.reuse pairInfo false #[.tobject, .tobject] .object,
    { params := #[.reuseToken, .tobject, .tobject], results := #[.object] }),
  (.box .float32 .object, { params := #[.float32], results := #[.object] }),
  (.unbox .float, { params := #[.tobject], results := #[.float] }),
  (.isShared, { params := #[.tobject], results := #[.uint8] }),
  (.objectSet 0 .tobject, { params := #[.object, .tobject], results := #[] }),
  (.usizeSet 0, { params := #[.object, .usize], results := #[] }),
  (.scalarSet 8 0 .uint64, { params := #[.object, .uint64], results := #[] }),
  (.setTag 1, { params := #[.object], results := #[] }),
  (.inc 1 true, { params := #[.tobject], results := #[] }),
  (.dec 1 true none, { params := #[.tobject], results := #[] }),
  (.delete, { params := #[.object], results := #[] }),
  (.getTag, { params := #[.tobject], results := #[.uint32] })]

#guard runtimeSignatureCases.all fun (operation, expected) =>
  operation.abiWellFormed && operation.signature == expected

def importOrderFunction : Function :=
  { name := `importOrder
    params := #[]
    results := #[]
    locals := #[]
    body := [
      .call (.runtime .getTag),
      .call (.runtime .isShared),
      .call (.runtime .getTag)] }

#guard collectRuntimeOps #[importOrderFunction] == #[.getTag, .isShared]
#guard ((collectRuntimeOps #[importOrderFunction]).mapIdx runtimeImport).map (·.key) ==
  #[.runtime .getTag, .runtime .isShared]

def lowers? (program : Fir.LeanIR.ImpureProgram) : Bool :=
  match lower program with
  | .ok _ => true
  | .error _ => false

#guard lowers? literalProgram
#guard lowers? erasedProgram
#guard lowers? ctorProjectionProgram
#guard lowers? caseProgram
#guard lowers? directCallProgram
#guard lowers? closureCallProgram
#guard lowers? joinProgram
#guard lowers? scalarBoxProgram
#guard lowers? mutationProgram
#guard lowers? usizeProjectionProgram
#guard lowers? objectMutationProgram
#guard lowers? tagMutationProgram
#guard lowers? defaultCaseProgram
#guard lowers? rcProgram
#guard lowers? persistentRcProgram
#guard lowers? resetReuseProgram
#guard lowers? sharedResetProgram
#guard lowers? deletedProgram
#guard lowers? externalProgram

def literalModule? : Option Module :=
  match lower literalProgram with
  | .ok module => some module
  | .error _ => none

#guard literalModule?.any fun module =>
  module.functions.size == 1 &&
  module.exports == #[`main] &&
  module.initializers.isEmpty &&
  module.runtimeOperations.contains (.literal (.nat 42) .object) &&
  module.imports.map (·.key) == module.runtimeOperations.map (.runtime ·)

def externalModule? : Option Module :=
  match lower externalProgram with
  | .ok module => some module
  | .error _ => none

#guard externalModule?.any fun module =>
  module.functions.size == 1 &&
  module.imports.any fun import_ =>
    import_.declaration? == some `external &&
      import_.externalTypes?.any fun types =>
        types.params == #[u64Type] && types.result == u64Type

def scalarIdProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `scalarId #[param x u64Type] u64Type (.code (.return x))] }

def scalarIdModule? : Option Module :=
  match lower scalarIdProgram with
  | .ok module => some module
  | .error _ => none

#guard scalarIdModule?.any fun module =>
  module.imports.isEmpty && module.functions.size == 1 &&
  module.functions[0]?.any fun function =>
    function.params.map (·.snd) == #[.uint64] && function.results == #[.uint64]

def floatIdProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `floatId #[param x LCNF.ImpureType.float32]
    LCNF.ImpureType.float32 (.code (.return x))] }

def floatIdModule? : Option Module :=
  match lower floatIdProgram with
  | .ok module => some module
  | .error _ => none

#guard floatIdModule?.any fun module =>
  module.functions[0]?.any fun function =>
    function.params.map (·.snd) == #[.float32] &&
    function.results == #[.float32]

def floatExternalDecl : LCNF.Decl .impure :=
  decl `floatExternal #[param x LCNF.ImpureType.float32]
    LCNF.ImpureType.float (.extern { entries := [] })

def floatExternalImport? : Option Import :=
  match externalImport floatExternalDecl with
  | .ok import_ => some import_
  | .error _ => none

#guard floatExternalImport?.any fun import_ =>
  import_.key == .external `floatExternal &&
  import_.signature == { params := #[.float32], results := #[.float] } &&
  import_.signature.physical == { params := #[.f32], results := #[.f64] }

def voidProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `voidFunction #[param x LCNF.ImpureType.void]
    LCNF.ImpureType.void (.code (.unreach LCNF.ImpureType.void))] }

#guard match lower voidProgram with
  | .ok module => module.functions[0]?.any fun function =>
      function.params.isEmpty && function.results.isEmpty && function.locals.isEmpty
  | .error _ => false

#guard supportedProgram voidProgram

def abiDirectIdDecl : LCNF.Decl .impure :=
  decl `abiDirectId #[param x LCNF.ImpureType.tobject]
    LCNF.ImpureType.tobject (.code (.return x))

def abiDirectCallProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[abiDirectIdDecl, decl `main #[] LCNF.ImpureType.tobject (.code <|
      .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 11))) <|
      .let (letDecl r LCNF.ImpureType.tobject (.fap `abiDirectId #[.fvar x])) <|
      .return r)] }

def abiClosureFirstDecl : LCNF.Decl .impure :=
  decl `abiClosureFirst #[param x LCNF.ImpureType.tobject,
    param y LCNF.ImpureType.tobject] LCNF.ImpureType.tobject (.code (.return x))

def abiClosureCallProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[abiClosureFirstDecl, decl `main #[] LCNF.ImpureType.tobject (.code <|
      .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 21))) <|
      .let (letDecl c LCNF.ImpureType.tobject (.pap `abiClosureFirst #[.fvar x])) <|
      .let (letDecl y LCNF.ImpureType.tobject (.lit (.nat 22))) <|
      .let (letDecl r LCNF.ImpureType.tobject (.fvar c #[.fvar y])) <|
      .return r)] }

#guard supportedProgram abiDirectCallProgram
#guard supportedProgram abiClosureCallProgram

def erasedCapture : FVarId := ⟨`erasedCapture⟩
def erasedClosure : FVarId := ⟨`erasedClosure⟩
def erasedArgument : FVarId := ⟨`erasedArgument⟩
def erasedResult : FVarId := ⟨`erasedResult⟩

def abiClosureErasedFirstDecl : LCNF.Decl .impure :=
  decl `abiClosureErasedFirst #[param erasedCapture LCNF.ImpureType.erased,
    param erasedArgument LCNF.ImpureType.tobject]
    LCNF.ImpureType.tobject (.code (.return erasedArgument))

def abiClosureErasedCaptureProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[abiClosureErasedFirstDecl,
      decl `main #[] LCNF.ImpureType.tobject (.code <|
        .let (letDecl erasedCapture LCNF.ImpureType.erased .erased) <|
        .let (letDecl erasedClosure LCNF.ImpureType.tobject
          (.pap `abiClosureErasedFirst #[.fvar erasedCapture])) <|
        .let (letDecl erasedArgument LCNF.ImpureType.tobject (.lit (.nat 23))) <|
        .let (letDecl erasedResult LCNF.ImpureType.tobject
          (.fvar erasedClosure #[.fvar erasedArgument])) <|
        .return erasedResult)] }

#guard supportedProgram abiClosureErasedCaptureProgram

#guard match lowerSupported abiClosureErasedCaptureProgram with
  | .ok module =>
      module.runtimeOperations.all fun
        | .closureProj _ _ _ _ .erased => false
        | _ => true
  | .error _ => false

def underClosure : FVarId := ⟨`underClosure⟩
def underClosure2 : FVarId := ⟨`underClosure2⟩
def underThird : FVarId := ⟨`underThird⟩

def abiClosureFirst3Decl : LCNF.Decl .impure :=
  decl `abiClosureFirst3 #[param x LCNF.ImpureType.tobject,
    param y LCNF.ImpureType.tobject, param underThird LCNF.ImpureType.tobject]
    LCNF.ImpureType.tobject (.code (.return x))

def abiClosureUnderApplyProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[abiClosureFirst3Decl, decl `main #[] LCNF.ImpureType.tobject (.code <|
      .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 31))) <|
      .let (letDecl underClosure LCNF.ImpureType.tobject
        (.pap `abiClosureFirst3 #[.fvar x])) <|
      .let (letDecl y LCNF.ImpureType.tobject (.lit (.nat 32))) <|
      .let (letDecl underClosure2 LCNF.ImpureType.tobject
        (.fvar underClosure #[.fvar y])) <|
      .let (letDecl underThird LCNF.ImpureType.tobject (.lit (.nat 33))) <|
      .let (letDecl r LCNF.ImpureType.tobject
        (.fvar underClosure2 #[.fvar underThird])) <|
      .return r)] }

#guard supportedProgram abiClosureUnderApplyProgram

def abiClosureOversaturatedProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[abiClosureFirstDecl, decl `main #[] LCNF.ImpureType.tobject (.code <|
      .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 41))) <|
      .let (letDecl underClosure LCNF.ImpureType.tobject
        (.pap `abiClosureFirst #[.fvar x])) <|
      .let (letDecl y LCNF.ImpureType.tobject (.lit (.nat 42))) <|
      .let (letDecl underThird LCNF.ImpureType.tobject (.lit (.nat 43))) <|
      .let (letDecl r LCNF.ImpureType.tobject
        (.fvar underClosure #[.fvar y, .fvar underThird])) <|
      .return r)] }

#guard !supportedProgram abiClosureOversaturatedProgram

def recursionFallback : FVarId := ⟨`recursionFallback⟩
def recursionList : FVarId := ⟨`recursionList⟩
def recursionHead : FVarId := ⟨`recursionHead⟩
def recursionTail : FVarId := ⟨`recursionTail⟩
def recursionNil : FVarId := ⟨`recursionNil⟩
def recursionOne : FVarId := ⟨`recursionOne⟩
def recursionTwo : FVarId := ⟨`recursionTwo⟩

def recursionNilInfo : LCNF.CtorInfo :=
  { name := ``List.nil, cidx := 0, size := 0, usize := 0, ssize := 0 }

def recursionConsInfo : LCNF.CtorInfo :=
  { name := ``List.cons, cidx := 1, size := 2, usize := 0, ssize := 0 }

def abiRecursiveLastDecl : LCNF.Decl .impure :=
  { decl `abiRecursiveLast #[
      param recursionFallback LCNF.ImpureType.tobject,
      param recursionList LCNF.ImpureType.tobject]
      LCNF.ImpureType.tobject (.code <|
        .cases (.mk ``List LCNF.ImpureType.tobject recursionList #[
          .ctorAlt recursionNilInfo (.return recursionFallback),
          .ctorAlt recursionConsInfo <|
            .let (letDecl recursionHead LCNF.ImpureType.tobject
              (.oproj 0 recursionList)) <|
            .let (letDecl recursionTail LCNF.ImpureType.tobject
              (.oproj 1 recursionList)) <|
            .let (letDecl r LCNF.ImpureType.tobject
              (.fap `abiRecursiveLast #[.fvar recursionHead, .fvar recursionTail])) <|
            .return r])) with
    recursive := true }

def abiRecursiveCallProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[abiRecursiveLastDecl,
      decl `main #[] LCNF.ImpureType.tobject (.code <|
        .let (letDecl recursionOne LCNF.ImpureType.tobject (.lit (.nat 10))) <|
        .let (letDecl recursionTwo LCNF.ImpureType.tobject (.lit (.nat 20))) <|
        .let (letDecl recursionNil LCNF.ImpureType.tobject
          (.ctor recursionNilInfo #[])) <|
        .let (letDecl recursionTail LCNF.ImpureType.tobject
          (.ctor recursionConsInfo #[.fvar recursionTwo, .fvar recursionNil])) <|
        .let (letDecl recursionList LCNF.ImpureType.tobject
          (.ctor recursionConsInfo #[.fvar recursionOne, .fvar recursionTail])) <|
        .let (letDecl recursionFallback LCNF.ImpureType.tobject (.lit (.nat 0))) <|
        .let (letDecl r LCNF.ImpureType.tobject
          (.fap `abiRecursiveLast #[.fvar recursionFallback, .fvar recursionList])) <|
        .return r)] }

#guard supportedProgram abiRecursiveCallProgram

def supportedUSizeProjectionProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `supportedUSizeProjection #[param p objType] usizeType (.code <|
      .let (letDecl r usizeType (.uproj 0 p)) (.return r))] }

#guard supportedProgram supportedUSizeProjectionProgram

def supportedScalarProjectionProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `supportedScalarProjection #[param p objType] u64Type (.code <|
      .let (letDecl r u64Type (.sproj 1 0 p)) (.return r))] }

#guard supportedProgram supportedScalarProjectionProgram

def malformedUSizeAsScalarProjectionProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `malformedUSizeAsScalarProjection #[param p objType]
      usizeType (.code <|
        .let (letDecl r usizeType (.sproj 1 0 p)) (.return r))] }

#guard !supportedProgram malformedUSizeAsScalarProjectionProgram

def unsupportedFloatProjectionProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `unsupportedFloatProjection #[param p objType]
      LCNF.ImpureType.float (.code <|
        .let (letDecl r LCNF.ImpureType.float (.sproj 1 0 p)) (.return r))] }

#guard !supportedProgram unsupportedFloatProjectionProgram

def boxed : FVarId := ⟨`boxed⟩

def supportedBoxRoundtripProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `supportedBoxRoundtrip #[] u64Type (.code <|
      .let (letDecl s u64Type (.lit (.uint64 44))) <|
      .let (letDecl boxed LCNF.ImpureType.tobject (.box u64Type s)) <|
      .let (letDecl r u64Type (.unbox boxed)) <|
      .return r)] }

#guard supportedProgram supportedBoxRoundtripProgram

def supportedIsSharedProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `supportedIsShared #[param x LCNF.ImpureType.tobject] u8Type (.code <|
      .let (letDecl r u8Type (.isShared x)) (.return r))] }

#guard supportedProgram supportedIsSharedProgram

def malformedPreciseBoxProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `malformedPreciseBox #[param s u64Type] objType (.code <|
      .let (letDecl boxed objType (.box u64Type s)) (.return boxed))] }

#guard !supportedProgram malformedPreciseBoxProgram

def unsupportedTypeProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `unsupported #[param x unknownAbiType] unknownAbiType
    (.code (.return x))] }

#guard match lower unsupportedTypeProgram with
  | .error (.abi (.unsupportedType type)) => type == unknownAbiType
  | _ => false

def invalidRuntimeSignatureProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `invalidRuntime #[param p objType] objType (.code <|
      .let (letDecl r objType (.sproj 8 0 p)) (.return r))] }

#guard match lower invalidRuntimeSignatureProgram with
  | .error (.malformed "generated runtime operation violates the semantic ABI") => true
  | _ => false

def tobjectType : Lean.Expr := LCNF.ImpureType.tobject
def erasedType : Lean.Expr := LCNF.ImpureType.erased

def abiLiteralProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 42))) (.return x))] }

def abiErasedProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] erasedType (.code <|
      .let (letDecl x erasedType .erased) (.return x))] }

def abiCtorProjectionProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 7))) <|
      .let (letDecl y tobjectType (.lit (.nat 8))) <|
      .let (letDecl p objType (.ctor pairInfo #[.fvar x, .fvar y])) <|
      .let (letDecl r tobjectType (.oproj 0 p)) <|
      .return r)] }

def abiCaseProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl c taggedType (.ctor trueInfo #[])) <|
      .cases (.mk ``Bool tobjectType c #[
        .ctorAlt falseInfo
          (.let (letDecl r tobjectType (.lit (.nat 0))) (.return r)),
        .ctorAlt trueInfo
          (.let (letDecl r tobjectType (.lit (.nat 1))) (.return r))]))] }

def scalarUInt8CaseProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param c u8Type] tobjectType (.code <|
      .cases (.mk ``Bool tobjectType c #[
        .ctorAlt falseInfo
          (.let (letDecl r tobjectType (.lit (.nat 0))) (.return r)),
        .ctorAlt trueInfo
          (.let (letDecl r tobjectType (.lit (.nat 1))) (.return r))]))] }

def guardedResetJoinBody : LCNF.Code .impure :=
  .cases (.mk ``Bool objType u #[
    .ctorAlt falseInfo (.return p),
    .ctorAlt trueInfo (.return x)])

def abiJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x objType] objType (.code <|
      .jp (.mk j `abiJoin #[param p objType] objType (.return p))
        (.jmp j #[.fvar x]))] }

def guardedResetJoinDecl : LCNF.FunDecl .impure :=
  .mk j `guardedResetJoin #[param p tobjectType, param u u8Type]
    objType guardedResetJoinBody

def guardedResetJoinContinuation : LCNF.Code .impure :=
  .cases (.mk ``Bool objType c #[
    .ctorAlt falseInfo (.jmp j #[.fvar x, .fvar c]),
    .ctorAlt trueInfo (.jmp j #[.erased, .fvar c])])

/-- Minimal form of Lean 4.32's guarded optional-object reset join. -/
def guardedResetJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x objType] objType (.code <|
      .let (letDecl c u8Type (.isShared x)) <|
      .jp guardedResetJoinDecl guardedResetJoinContinuation)] }

/-- The false sharing path refines the exact `tobject` candidate to a heap object. -/
def guardedTObjectResetJoinDecl : LCNF.FunDecl .impure :=
  .mk j `guardedTObjectResetJoin #[param p tobjectType, param u u8Type]
    objType <| .cases (.mk ``Bool objType u #[
      .ctorAlt falseInfo (.return p),
      .ctorAlt trueInfo (.return z)])

def guardedTObjectResetJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x tobjectType, param z objType] objType (.code <|
      .let (letDecl c u8Type (.isShared x)) <|
      .jp guardedTObjectResetJoinDecl guardedResetJoinContinuation)] }

def mismatchedGuardObjectJoinContinuation : LCNF.Code .impure :=
  .cases (.mk ``Bool objType c #[
    .ctorAlt falseInfo (.jmp j #[.fvar y, .fvar c]),
    .ctorAlt trueInfo (.jmp j #[.erased, .fvar c])])

/-- A guard for one `tobject` cannot refine a different fast-path argument. -/
def mismatchedGuardObjectJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main
      #[param x tobjectType, param y tobjectType, param z objType] objType (.code <|
      .let (letDecl c u8Type (.isShared x)) <|
      .jp guardedTObjectResetJoinDecl mismatchedGuardObjectJoinContinuation)] }

/-- A guarded optional object may be deleted before inspecting its sharing guard. -/
def guardedDeleteJoinDecl : LCNF.FunDecl .impure :=
  .mk j `guardedDeleteJoin #[param p tobjectType, param u u8Type]
    objType (.del p (.return x))

def guardedDeleteJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x objType] objType (.code <|
      .let (letDecl c u8Type (.isShared x)) <|
      .jp guardedDeleteJoinDecl guardedResetJoinContinuation)] }

/-- `del` does not make a later unguarded object use of the sentinel safe. -/
def guardedDeleteThenReturnJoinDecl : LCNF.FunDecl .impure :=
  .mk j `guardedDeleteThenReturnJoin #[param p tobjectType, param u u8Type]
    objType (.del p (.return p))

def guardedDeleteThenReturnJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x objType] objType (.code <|
      .let (letDecl c u8Type (.isShared x)) <|
      .jp guardedDeleteThenReturnJoinDecl guardedResetJoinContinuation)] }

def unknownJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] objType (.code (.jmp j #[]))] }

def joinArityMismatchProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] objType (.code <|
      .jp (.mk j `joinArity #[param p objType] objType (.return p))
        (.jmp j #[]))] }

def joinKindMismatchProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] objType (.code <|
      .jp (.mk j `joinKind #[param p objType] objType (.return p)) <|
      .let (letDecl s u64Type (.lit (.uint64 1))) <|
      .jmp j #[.fvar s])] }

def unguardedErasedJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x objType] objType (.code <|
      .jp (.mk j `unguardedErased #[param p tobjectType] objType (.return x))
        (.jmp j #[.erased]))] }

/-- A Boolean-looking guard is insufficient without `isShared(object)` provenance. -/
def unprovenGuardedJoinProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x objType, param c u8Type] objType (.code <|
      .jp guardedResetJoinDecl guardedResetJoinContinuation)] }

def abiDefaultCaseProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl c taggedType (.ctor trueInfo #[])) <|
      .cases (.mk ``Bool tobjectType c #[
        .default
          (.let (letDecl r tobjectType (.lit (.nat 5))) (.return r)),
        .ctorAlt falseInfo
          (.let (letDecl u tobjectType (.lit (.nat 0))) (.return u))]))] }

def abiMutationProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code <|
      .let (letDecl x tobjectType (.lit (.nat 1))) <|
      .let (letDecl y tobjectType (.lit (.nat 2))) <|
      .let (letDecl p objType (.ctor layoutInfo #[.fvar x])) <|
      .let (letDecl u usizeType (.lit (.usize 55))) <|
      .uset p 1 u <|
      .let (letDecl s u64Type (.lit (.uint64 66))) <|
      .sset p 1 0 s u64Type <|
      .oset p 0 (.fvar y) <|
      .setTag p 4 <|
      .let (letDecl r u64Type (.sproj 1 0 p)) <|
      .return r)] }

def abiObjectMutationProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 1))) <|
      .let (letDecl y tobjectType (.lit (.nat 88))) <|
      .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .oset p 0 (.fvar y) <|
      .let (letDecl r tobjectType (.oproj 0 p)) <|
      .return r)] }

def abiTagMutationProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 1))) <|
      .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .setTag p 9 <|
      .cases (.mk `Changed tobjectType p #[
        .ctorAlt changedTagInfo
          (.let (letDecl r tobjectType (.lit (.nat 99))) (.return r)),
        .default
          (.let (letDecl u tobjectType (.lit (.nat 0))) (.return u))]))] }

def abiResetReuseProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 70))) <|
      .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .let (letDecl r objType (.reset 1 p)) <|
      .let (letDecl y tobjectType (.lit (.nat 71))) <|
      .let (letDecl z objType
        (.reuse r { pairInfo with size := 1 } false #[.fvar y])) <|
      .let (letDecl s tobjectType (.oproj 0 z)) <|
      .return s)] }

def abiSharedResetProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 80))) <|
      .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .inc p 1 false false <|
      .let (letDecl r objType (.reset 1 p)) <|
      .let (letDecl y tobjectType (.lit (.nat 81))) <|
      .let (letDecl z objType (.reuse r changedTagInfo true #[.fvar y])) <|
      .let (letDecl s tobjectType (.oproj 0 z)) <|
      .return s)] }

def oversizedTagInfo : LCNF.CtorInfo :=
  { name := `Oversized.tag, cidx := UInt32.size, size := 1, usize := 0, ssize := 0 }

def oversizedTagCaseProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 0))) <|
      .let (letDecl c taggedType (.ctor falseInfo #[])) <|
      .cases (.mk `Oversized tobjectType c #[
        .ctorAlt oversizedTagInfo (.return x)]))] }

def oversizedScalarTagInfo : LCNF.CtorInfo :=
  { name := `Oversized.scalar, cidx := UInt8.size,
    size := 0, usize := 0, ssize := 0 }

def oversizedScalarTagCaseProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param c u8Type] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 0))) <|
      .cases (.mk `OversizedScalar tobjectType c #[
        .ctorAlt oversizedScalarTagInfo (.return x)]))] }

/--
The allocated discriminator is out of range while the compared alternative
is representable. Without the allocation-side check, both tags become zero in
the semantic i32 ABI and the target selects the wrong branch.
-/
def oversizedAllocatedTagProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 7))) <|
      .let (letDecl c taggedType (.ctor { oversizedTagInfo with size := 0 } #[])) <|
      .cases (.mk `Oversized tobjectType c #[
        .ctorAlt falseInfo
          (.let (letDecl r tobjectType (.lit (.nat 0))) (.return r)),
        .default (.return x)]))] }

#guard !supportedProgram literalProgram
#guard !supportedProgram erasedProgram
#guard !supportedProgram ctorProjectionProgram
#guard !supportedProgram caseProgram
#guard !supportedProgram defaultCaseProgram
#guard supportedProgram abiLiteralProgram
#guard supportedProgram abiErasedProgram
#guard supportedProgram abiCtorProjectionProgram
#guard supportedProgram abiCaseProgram
#guard supportedProgram scalarUInt8CaseProgram
#guard supportedProgram abiJoinProgram
#guard supportedProgram guardedResetJoinProgram
#guard supportedProgram guardedTObjectResetJoinProgram
#guard !supportedProgram mismatchedGuardObjectJoinProgram
#guard supportedProgram guardedDeleteJoinProgram
#guard !supportedProgram guardedDeleteThenReturnJoinProgram
#guard !supportedProgram unknownJoinProgram
#guard !supportedProgram joinArityMismatchProgram
#guard !supportedProgram joinKindMismatchProgram
#guard !supportedProgram unguardedErasedJoinProgram
#guard !supportedProgram unprovenGuardedJoinProgram
#guard supportedProgram abiDefaultCaseProgram
#guard !supportedProgram oversizedTagCaseProgram
#guard !supportedProgram oversizedScalarTagCaseProgram
#guard !supportedProgram oversizedAllocatedTagProgram
#guard !supportedProgram directCallProgram
#guard !supportedProgram closureCallProgram
#guard !supportedProgram mutationProgram
#guard supportedProgram abiMutationProgram
#guard supportedProgram abiObjectMutationProgram
#guard supportedProgram abiTagMutationProgram
#guard supportedProgram rcProgram
#guard supportedProgram persistentRcProgram
#guard supportedProgram deletedProgram
#guard supportedProgram abiResetReuseProgram
#guard supportedProgram abiSharedResetProgram
#guard supportedProgram externalProgram

#guard match lowerSupported abiCaseProgram with
  | .ok _ => true
  | .error _ => false

#guard match lowerSupported scalarUInt8CaseProgram with
  | .ok module =>
      !module.runtimeOperations.contains .getTag &&
        module.functions[0]?.any fun function =>
          function.body[0]? == some (.localGet c) &&
            function.body[1]? == some (.i32Const .uint8 0) &&
            function.body[2]? == some .i32Eq
  | .error _ => false

#guard match lowerSupported guardedResetJoinProgram with
  | .ok module =>
      match validateModule module with
      | .ok _ => true
      | .error _ => false
  | .error _ => false

#guard match lower oversizedTagCaseProgram with
  | .error (.malformed message) => message.contains "does not fit the case discriminator ABI"
  | _ => false

#guard match lower oversizedScalarTagCaseProgram with
  | .error (.malformed message) => message.contains "does not fit the case discriminator ABI"
  | _ => false

#guard match lower oversizedAllocatedTagProgram with
  | .error (.malformed message) =>
      message.contains "allocated constructor tag" && message.contains "does not fit the i32 tag ABI"
  | _ => false

#guard match validateSupported directCallProgram with
  | .error (.unsupportedCode `main) => true
  | _ => false

def validates? (program : Fir.LeanIR.ImpureProgram) : Bool :=
  match lower program with
  | .error _ => false
  | .ok module =>
      match validateModule module with
      | .ok _ => true
      | .error _ => false

#guard ([
  literalProgram,
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
  resetReuseProgram,
  sharedResetProgram,
  deletedProgram,
  externalProgram,
  scalarIdProgram,
  floatIdProgram,
  voidProgram,
  abiLiteralProgram,
  abiErasedProgram,
  abiCtorProjectionProgram,
  abiCaseProgram,
  guardedResetJoinProgram,
  guardedTObjectResetJoinProgram,
  guardedDeleteJoinProgram,
  abiDefaultCaseProgram] : List Fir.LeanIR.ImpureProgram).all validates?

#guard !validates? erasedProgram

#guard match lower closureCallProgram with
  | .ok module =>
      match validateModule module with
      | .ok _ => true
      | .error _ => false
  | .error _ => false

def fixtureFunction (body : List Instruction) (results : Array AbiKind := #[])
    (locals : Array (FVarId × AbiKind) := #[]) : Function :=
  { name := `fixture, params := #[], results, locals, body }

def fixtureModule (function : Function) : Module :=
  { imports := #[]
    functions := #[function]
    exports := #[]
    initializers := #[]
    runtimeOperations := #[] }

def ghost : Lean.FVarId := ⟨`ghost⟩
def outer : Lean.FVarId := ⟨`outer⟩
def inner : Lean.FVarId := ⟨`inner⟩

#guard match validateModule (fixtureModule <| fixtureFunction [.localGet ghost]) with
  | .error (.unknownLocal `fixture fvarId) => fvarId.name == ghost.name
  | _ => false

#guard match validateModule (fixtureModule <| fixtureFunction [.unreachable, .localGet ghost]) with
  | .error (.unknownLocal `fixture fvarId) => fvarId.name == ghost.name
  | _ => false

#guard match validateModule (fixtureModule <| fixtureFunction [.br ghost]) with
  | .error (.unknownLabel `fixture fvarId) => fvarId.name == ghost.name
  | _ => false

#guard match validateModule (fixtureModule <| fixtureFunction [.call (.declaration `missing)]) with
  | .error (.unknownCallTarget `fixture) => true
  | _ => false

#guard match validateModule (fixtureModule <|
    fixtureFunction [.i32Const .uint64 0]) with
  | .error (.invalidConstant `fixture .uint64 .i32) => true
  | _ => false

#guard match validateModule (fixtureModule <|
    fixtureFunction [.i64Const .uint64 0, .localSet x] #[] #[(x, .uint32)]) with
  | .error (.stackMismatch `fixture [.uint32] [.uint64]) => true
  | _ => false

#guard match validateModule (fixtureModule <|
    fixtureFunction [.i32Const .uint32 0, .ret] #[.uint64]) with
  | .error (.stackMismatch `fixture [.uint64] [.uint32]) => true
  | _ => false

#guard match validateModule (fixtureModule <| fixtureFunction [
    .i32Const .uint32 0,
    .ifElse [.i32Const .uint32 1] [.i64Const .uint64 1]]) with
  | .error (.branchMergeMismatch `fixture [.uint32] [.uint64]) => true
  | _ => false

#guard match validateModule (fixtureModule <| fixtureFunction [
    .i32Const .uint32 0,
    .ifElse [.i32Const .uint32 1] [.unreachable],
    .ret] #[.uint32]) with
  | .error (.stackMismatch `fixture [] [.uint32]) => true
  | _ => false

#guard match validateModule (fixtureModule <| fixtureFunction [
    .block outer [.block inner [.br outer]]]) with
  | .ok _ => true
  | _ => false

#guard match validateModule (fixtureModule <| fixtureFunction [
    .block outer [.block outer [.br outer]]]) with
  | .error (.duplicateLabel `fixture fvarId) => fvarId.name == outer.name
  | _ => false

#guard match validateModule (fixtureModule <|
    fixtureFunction [] #[] #[(x, .uint32), (x, .uint64)]) with
  | .error (.duplicateLocal `fixture fvarId) => fvarId.name == x.name
  | _ => false

#guard match validateModule { fixtureModule (fixtureFunction []) with exports := #[`missing] } with
  | .error (.unknownExport `missing) => true
  | _ => false

#guard match validateModule { fixtureModule (fixtureFunction []) with
    exports := #[`fixture, `fixture] } with
  | .error (.duplicateExport `fixture) => true
  | _ => false

#guard match validateModule { fixtureModule (fixtureFunction []) with
    functions := #[fixtureFunction [], fixtureFunction []] } with
  | .error (.duplicateFunction `fixture) => true
  | _ => false

def directCallArityModule : Module :=
  let callee : Function := {
    name := `callee
    params := #[(x, .uint64)]
    results := #[.uint64]
    locals := #[]
    body := [.localGet x, .ret] }
  let caller : Function := {
    name := `caller
    params := #[]
    results := #[.uint64]
    locals := #[]
    body := [.call (.declaration `callee), .ret] }
  { imports := #[]
    functions := #[callee, caller]
    exports := #[]
    initializers := #[]
    runtimeOperations := #[] }

#guard match validateModule directCallArityModule with
  | .error (.stackUnderflow `caller [.uint64]) => true
  | _ => false

def ctorProjectionModule? : Option Module :=
  match lower ctorProjectionProgram with
  | .ok module => some module
  | .error _ => none

#guard ctorProjectionModule?.any fun module =>
  match validateModule { module with imports := module.imports.reverse } with
  | .error (.invalidRuntimeImport 0) => true
  | _ => false

#guard ctorProjectionModule?.any fun module =>
  match validateModule { module with runtimeOperations := module.runtimeOperations.reverse } with
  | .error .runtimeOperationOrder => true
  | _ => false

#guard externalModule?.any fun module =>
  match validateModule { module with imports := module.imports ++ module.imports } with
  | .error .duplicateImportKey => true
  | _ => false

#guard externalModule?.any fun module =>
  let imports := module.imports.map fun import_ =>
    { import_ with externalTypes? := none }
  match validateModule { module with imports } with
  | .error (.invalidExternalImport 0) => true
  | _ => false

#guard literalModule?.any fun module =>
  match validateModule { module with initializers := #[`missing] } with
  | .error (.invalidInitializer `missing) => true
  | _ => false

def taggedValue : Value := .object (.tagged 42)

def decodesAs (table : HandleTable) (kind : AbiKind) (handle : Handle)
    (expected : Value) : Bool :=
  match table.decodeAs kind handle with
  | .ok value => value == expected
  | .error _ => false

def handleRoundTrip : Bool :=
  match ({} : HandleTable).encode .tagged taggedValue with
  | .error _ => false
  | .ok (table, handle) =>
      handle != reservedHandle && decodesAs table .tagged handle taggedValue

#guard handleRoundTrip

def allHandleKindsRoundTrip : Bool :=
  ([
    (.object, .object (.heap 7)),
    (.tagged, taggedValue),
    (.tobject, taggedValue),
    (.erased, .erased),
    (.reuseToken, .reuseToken (some 7))] : List (AbiKind × Value)).all fun (kind, value) =>
      match ({} : HandleTable).encode kind value with
      | .error _ => false
      | .ok (table, handle) => decodesAs table kind handle value

#guard allHandleKindsRoundTrip

def handleAliasStable : Bool :=
  match ({} : HandleTable).encode .tagged taggedValue with
  | .error _ => false
  | .ok (table, first) =>
      match table.encode .tobject taggedValue with
      | .error _ => false
      | .ok (table', second) => first == second && table' == table

#guard handleAliasStable

def distinctHandles : Bool :=
  match ({} : HandleTable).encode .tagged taggedValue with
  | .error _ => false
  | .ok (table, first) =>
      match table.encode .tagged (.object (.tagged 43)) with
      | .error _ => false
      | .ok (table', second) =>
          first != second &&
          decodesAs table' .tagged first taggedValue &&
          decodesAs table' .tagged second (.object (.tagged 43))

#guard distinctHandles

#guard match ({} : HandleTable).decode reservedHandle with
  | .error (.unknownHandle handle) => handle == reservedHandle
  | _ => false

#guard match ({} : HandleTable).encode .erased .erased with
  | .ok (table, handle) => table == {} && handle == reservedHandle
  | .error _ => false

#guard match ({} : HandleTable).encode .uint64 (.scalar (.uint64 1)) with
  | .error (.kindDoesNotUseHandles .uint64) => true
  | _ => false

#guard match ({} : HandleTable).encode .object taggedValue with
  | .error (.valueKindMismatch .object value) => value == taggedValue
  | _ => false

#guard match ({ next := maxHandle + 1 } : HandleTable).encode .tagged taggedValue with
  | .error .handleSpaceExhausted => true
  | _ => false

#guard HandleError.handleSpaceExhausted.toTargetFailure == .handleSpaceExhausted
#guard (HandleError.unknownHandle 7).toTargetFailure == .invalidHandle 7

end Fir.Wasm
