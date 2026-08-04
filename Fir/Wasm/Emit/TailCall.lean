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

private partial def rewriteInstructions (function : Function) (loopLabel : FVarId) :
    List Instruction → List Instruction × Nat
  | [.call (.declaration callee), .ret] =>
      if callee == function.name then
        (parameterAssignments function ++ [.br loopLabel], 1)
      else
        ([.call (.declaration callee), .ret], 0)
  | [.call (.declaration callee), .localSet result,
      .localGet returned, .ret] =>
      if callee == function.name && sameFVar result returned &&
          function.results.size == 1 then
        (parameterAssignments function ++ [.br loopLabel], 1)
      else
        ([.call (.declaration callee), .localSet result,
          .localGet returned, .ret], 0)
  | instruction :: rest =>
      let (instruction, instructionCount) :=
        rewriteInstruction function loopLabel instruction
      let (rest, restCount) := rewriteInstructions function loopLabel rest
      (instruction :: rest, instructionCount + restCount)
  | [] => ([], 0)

private partial def rewriteInstruction (function : Function) (loopLabel : FVarId) :
    Instruction → Instruction × Nat
  | .block label body =>
      let (body, count) := rewriteInstructions function loopLabel body
      (.block label body, count)
  | .loop label body =>
      let (body, count) := rewriteInstructions function loopLabel body
      (.loop label body, count)
  | .ifElse thenBody elseBody =>
      let (thenBody, thenCount) := rewriteInstructions function loopLabel thenBody
      let (elseBody, elseCount) := rewriteInstructions function loopLabel elseBody
      (.ifElse thenBody elseBody, thenCount + elseCount)
  | instruction => (instruction, 0)

end

def rewriteFunction (function : Function) : Function × Nat :=
  let loopLabel := freshLoopLabel function
  let (body, count) := rewriteInstructions function loopLabel function.body
  if count == 0 then
    (function, 0)
  else
    ({ function with body := [.loop loopLabel body] }, count)

/--
Turn direct self calls in Wasm tail position into parameter reassignment and a
branch to a structured function-body loop. This keeps the standard Wasm MVP
instruction set while making native call-stack usage independent of the
number of tail-recursive steps.

The pass recognizes both the direct `call; return` form and Lean final LCNF's
single-result `call; local.set; local.get; return` round trip. It validates the
symbolic module on both sides of the rewrite.
-/
def eliminateDirectSelfCalls (module : Module) : Except String Result := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error => throw s!"tail-call input module is invalid: {repr error}"
  let (functions, count) := module.functions.foldl
    (init := (#[], 0)) fun (functions, count) function =>
      let (function, rewritten) := rewriteFunction function
      (functions.push function, count + rewritten)
  let result := { module with functions }
  match Fir.Wasm.validateModule result with
  | .ok () => pure ()
  | .error error => throw s!"tail-call output module is invalid: {repr error}"
  return { module := result, rewrittenCalls := count }

private def argument : FVarId := ⟨`argument⟩
private def result : FVarId := ⟨`result⟩
private def exampleName : Name := `tail_recursive_example

private def exampleFunction : Function := {
  name := exampleName
  params := #[(argument, .uint32)]
  results := #[.uint32]
  locals := #[(result, .uint32)]
  body := [
    .localGet argument,
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse
      [.localGet argument, .ret]
      [.localGet argument,
        .i32Const .uint32 1,
        .i32Sub,
        .call (.declaration exampleName),
        .localSet result,
        .localGet result,
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
        | [.loop _ _] => true
        | _ => false
  | .error _ => false

end Fir.Wasm.Emit.TailCall
