import Fir.Wasm.Emit.Binary

namespace Fir.Wasm.Emit.TailCall

open Lean
open Fir.Wasm

structure Result where
  module : Module
  rewrittenCalls : Nat

private def sameFVar (left right : FVarId) : Bool :=
  left.name == right.name

private def parameterAssignments (function : Function) : List Instruction :=
  function.params.toList.reverse.map fun (fvarId, _) => .localSet fvarId

private def zeroValue : AbiKind → List Instruction
  | .object => [.i32Const .object 0]
  | .tagged => [.i32Const .tagged 0]
  | .tobject => [.i32Const .tobject 0]
  | .erased => [.i32Const .erased 0]
  | .reuseToken => [.i32Const .reuseToken 0]
  | .uint8 => [.i32Const .uint8 0]
  | .uint16 => [.i32Const .uint16 0]
  | .uint32 => [.i32Const .uint32 0]
  | .uint64 => [.i64Const .uint64 0]
  | .usize => [.i64Const .usize 0]
  | .float32 => [.i32Const .uint32 0, .f32ReinterpretI32 .float32]
  | .float => [.f64Const 0]

private abbrev FVarNames := Std.HashSet Name

private def functionLocalNames (function : Function) : FVarNames :=
  function.locals.foldl
    (init := Std.HashSet.emptyWithCapacity function.locals.size)
    fun names (fvarId, _) => names.insert fvarId.name

private def containsFVar (fvarIds : FVarNames) (candidate : FVarId) : Bool :=
  fvarIds.contains candidate.name

private def insertFVar (fvarIds : FVarNames) (candidate : FVarId) : FVarNames :=
  fvarIds.insert candidate.name

private def intersectFVars (left right : FVarNames) : FVarNames :=
  left.fold
    (fun common name => if right.contains name then common.insert name else common)
    (Std.HashSet.emptyWithCapacity (min left.size right.size))

private def isFunctionLocal (localNames : FVarNames) (candidate : FVarId) : Bool :=
  localNames.contains candidate.name

private structure AssignmentFlow where
  fallthrough : Option FVarNames
  branches : List (FVarId × FVarNames) := []
  needsInitialization : FVarNames
  deriving Inhabited

private def mergeAssigned : Option FVarNames → FVarNames → Option FVarNames
  | none, assigned => some assigned
  | some previous, assigned => some (intersectFVars previous assigned)

mutual

/--
Track locals definitely assigned on every reachable path and record any local
read before such an assignment. Structured branch states are consumed by their
target block or loop, so assignments after an early branch cannot make a local
look initialized on that path.
-/
private partial def analyzeInstructions (localNames : FVarNames) :
    FVarNames → FVarNames → List Instruction → AssignmentFlow
  | assigned, needsInitialization, [] =>
      { fallthrough := some assigned, needsInitialization }
  | assigned, needsInitialization, instruction :: rest =>
      let instructionFlow :=
        analyzeInstruction localNames assigned needsInitialization instruction
      match instructionFlow.fallthrough with
      | none => instructionFlow
      | some assigned =>
          let restFlow := analyzeInstructions localNames assigned
            instructionFlow.needsInitialization rest
          { restFlow with
            branches := instructionFlow.branches ++ restFlow.branches }

private partial def analyzeInstruction (localNames : FVarNames)
    (assigned needsInitialization : FVarNames) :
    Instruction → AssignmentFlow
  | .localGet fvarId | .localGetObject fvarId =>
      if isFunctionLocal localNames fvarId && !containsFVar assigned fvarId then
        { fallthrough := some assigned
          needsInitialization := insertFVar needsInitialization fvarId }
      else
        { fallthrough := some assigned, needsInitialization }
  | .localSet fvarId =>
      if isFunctionLocal localNames fvarId then
        { fallthrough := some (insertFVar assigned fvarId), needsInitialization }
      else
        { fallthrough := some assigned, needsInitialization }
  | .block label body =>
      let bodyFlow := analyzeInstructions localNames assigned needsInitialization body
      let exits := bodyFlow.branches.filter fun (target, _) => sameFVar target label
      let escaping := bodyFlow.branches.filter fun (target, _) => !sameFVar target label
      let fallthrough := exits.foldl
        (fun fallthrough (_, branchAssigned) =>
          mergeAssigned fallthrough branchAssigned)
        bodyFlow.fallthrough
      { fallthrough, branches := escaping
        needsInitialization := bodyFlow.needsInitialization }
  | .loop label body =>
      let bodyFlow := analyzeInstructions localNames assigned needsInitialization body
      let escaping := bodyFlow.branches.filter fun (target, _) => !sameFVar target label
      { bodyFlow with branches := escaping }
  | .ifElse thenBody elseBody =>
      let thenFlow := analyzeInstructions localNames assigned needsInitialization thenBody
      let elseFlow := analyzeInstructions localNames assigned
        thenFlow.needsInitialization elseBody
      let fallthrough := match thenFlow.fallthrough, elseFlow.fallthrough with
        | none, none => none
        | some assigned, none | none, some assigned => some assigned
        | some thenAssigned, some elseAssigned =>
            some (intersectFVars thenAssigned elseAssigned)
      { fallthrough
        branches := thenFlow.branches ++ elseFlow.branches
        needsInitialization := elseFlow.needsInitialization }
  | .br label =>
      { fallthrough := none, branches := [(label, assigned)], needsInitialization }
  | .ret | .unreachable =>
      { fallthrough := none, needsInitialization }
  | _ => { fallthrough := some assigned, needsInitialization }

end

private def localsNeedingInitialization (function : Function) : FVarNames :=
  let localNames := functionLocalNames function
  let empty := Std.HashSet.emptyWithCapacity function.locals.size
  (analyzeInstructions localNames empty empty function.body).needsInitialization

/-- Restore the fresh zeroed locals observable at a real Wasm call boundary. -/
private def localInitializations (function : Function) : List Instruction :=
  let needed := localsNeedingInitialization function
  function.locals.toList.flatMap fun (fvarId, kind) =>
    if containsFVar needed fvarId then
      zeroValue kind ++ [.localSet fvarId]
    else
      []

private def restartInstructions (function : Function) (loopLabel : FVarId) :
    List Instruction :=
  parameterAssignments function ++ localInitializations function ++ [.br loopLabel]

private partial def containsLabel (candidate : FVarId) : List Instruction → Bool
  | [] => false
  | .block label body :: rest | .loop label body :: rest =>
      sameFVar candidate label || containsLabel candidate body ||
        containsLabel candidate rest
  | .ifElse thenBody elseBody :: rest =>
      containsLabel candidate thenBody || containsLabel candidate elseBody ||
        containsLabel candidate rest
  | _ :: rest => containsLabel candidate rest

private partial def freshLoopLabel (function : Function) (ordinal : Nat := 0) : FVarId :=
  let candidate : FVarId :=
    ⟨Name.num (Name.str function.name "_firSelfTailLoop") ordinal⟩
  if containsLabel candidate function.body then
    freshLoopLabel function (ordinal + 1)
  else
    candidate

mutual

private partial def rewriteInstructions (function : Function) (loopLabel : FVarId)
    (restart : List Instruction) :
    List Instruction → List Instruction × Nat
  | [.call (.declaration callee), .ret] =>
      if callee == function.name then
        (restart, 1)
      else
        ([.call (.declaration callee), .ret], 0)
  | [.call (.declaration callee), .localSet result,
      .localGet returned, .ret] =>
      if callee == function.name && sameFVar result returned &&
          function.results.size == 1 then
        (restart, 1)
      else
        ([.call (.declaration callee), .localSet result,
          .localGet returned, .ret], 0)
  | instruction :: rest =>
      let (instruction, instructionCount) :=
        rewriteInstruction function loopLabel restart instruction
      let (rest, restCount) := rewriteInstructions function loopLabel restart rest
      (instruction :: rest, instructionCount + restCount)
  | [] => ([], 0)

private partial def rewriteInstruction (function : Function) (loopLabel : FVarId)
    (restart : List Instruction) :
    Instruction → Instruction × Nat
  | .block label body =>
      let (body, count) := rewriteInstructions function loopLabel restart body
      (.block label body, count)
  | .loop label body =>
      let (body, count) := rewriteInstructions function loopLabel restart body
      (.loop label body, count)
  | .ifElse thenBody elseBody =>
      let (thenBody, thenCount) :=
        rewriteInstructions function loopLabel restart thenBody
      let (elseBody, elseCount) :=
        rewriteInstructions function loopLabel restart elseBody
      (.ifElse thenBody elseBody, thenCount + elseCount)
  | instruction => (instruction, 0)

end

private partial def containsDirectSelfTailCall (function : Function) :
    List Instruction → Bool
  | [.call (.declaration callee), .ret] => callee == function.name
  | [.call (.declaration callee), .localSet result,
      .localGet returned, .ret] =>
      callee == function.name && sameFVar result returned && function.results.size == 1
  | .block _ body :: rest | .loop _ body :: rest =>
      containsDirectSelfTailCall function body ||
        containsDirectSelfTailCall function rest
  | .ifElse thenBody elseBody :: rest =>
      containsDirectSelfTailCall function thenBody ||
        containsDirectSelfTailCall function elseBody ||
        containsDirectSelfTailCall function rest
  | _ :: rest => containsDirectSelfTailCall function rest
  | [] => false

def rewriteFunction (function : Function) : Function × Nat :=
  if !containsDirectSelfTailCall function function.body then
    (function, 0)
  else
    let loopLabel := freshLoopLabel function
    let restart := restartInstructions function loopLabel
    let (body, count) := rewriteInstructions function loopLabel restart function.body
    ({ function with body := [.loop loopLabel body] }, count)

/--
Turn direct self calls in Wasm tail position into parameter reassignment,
non-parameter-local reinitialization, and a branch to a structured
function-body loop. This keeps the standard Wasm MVP instruction set while
making native call-stack usage independent of the number of tail-recursive
steps. Reinitializing locals preserves the fresh zeroed locals supplied by a
real Wasm call.

The pass recognizes both the direct `call; return` form and Lean final LCNF's
single-result `call; local.set; local.get; return` round trip. It validates the
symbolic module on both sides of the rewrite.
-/
def eliminateDirectSelfCalls (module : Module) (validate : Bool := true) :
    Except String Result := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw s!"tail-call input module is invalid: {repr error}"
  let (functions, count) := module.functions.foldl
    (init := (#[], 0)) fun (functions, count) function =>
      let (function, rewritten) := rewriteFunction function
      (functions.push function, count + rewritten)
  let result := { module with functions }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => pure ()
    | .error error => throw s!"tail-call output module is invalid: {repr error}"
  return { module := result, rewrittenCalls := count }

private def argument : FVarId := ⟨`argument⟩
private def resultLocal : FVarId := ⟨`result⟩
private def scratchLocal : FVarId := ⟨`scratch⟩
private def exampleName : Name := `tail_recursive_example

private def exampleFunction : Function := {
  name := exampleName
  params := #[(argument, .uint32)]
  results := #[.uint32]
  locals := #[(resultLocal, .uint32), (scratchLocal, .uint32)]
  body := [
    .localGet argument,
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse
      [.localGet scratchLocal, .ret]
      [.i32Const .uint32 1,
        .localSet scratchLocal,
        .localGet argument,
        .i32Const .uint32 1,
        .i32Sub,
        .call (.declaration exampleName),
        .localSet resultLocal,
        .localGet resultLocal,
        .ret]] }

private def exampleModule : Module := {
  imports := #[]
  functions := #[exampleFunction]
  exports := #[exampleName]
  initializers := #[]
  runtimeOperations := #[] }

#guard match eliminateDirectSelfCalls exampleModule with
  | .ok result =>
      result.rewrittenCalls == 1 && match result.module.functions[0]!.body with
        | [.loop loopLabel
            [.localGet actualArgument, .i32Const .uint32 0, .i32Eq,
              .ifElse _ elseBody]] =>
            sameFVar actualArgument argument && elseBody ==
              [.i32Const .uint32 1,
                .localSet scratchLocal,
                .localGet argument,
                .i32Const .uint32 1,
                .i32Sub,
                .localSet argument,
                .i32Const .uint32 0,
                .localSet scratchLocal,
                .br loopLabel]
        | _ => false
  | .error _ => false

#guard zeroValue .object == [.i32Const .object 0]
#guard zeroValue .uint64 == [.i64Const .uint64 0]
#guard zeroValue .float32 == [.i32Const .uint32 0, .f32ReinterpretI32 .float32]
#guard zeroValue .float == [.f64Const 0]
#guard (localsNeedingInitialization exampleFunction).contains scratchLocal.name

end Fir.Wasm.Emit.TailCall
