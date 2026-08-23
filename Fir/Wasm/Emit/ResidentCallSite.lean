import Fir.Wasm.Lower

namespace Fir.Wasm.Emit.ResidentCallSite

open Fir.Wasm
open Lean

/-!
# Resident call-site rewrites

Some operations in Lean's C runtime are `static inline` wrappers around a
cold out-of-line helper. Resident Wasm helpers retain the cold implementation,
while these rules describe the caller-local state needed to reproduce the
inline wrapper at a symbolic call site.
-/

/-- One explicit call replacement and the fresh locals it requires. -/
structure Rewrite where
  target : CallTarget
  body : List Instruction
  locals : Array (FVarId × AbiKind) := #[]
  deriving Inhabited, BEq

inductive Error where
  | reservedLocal (function : Name) (localId : FVarId)
  | conflictingRequirement (localId : FVarId)
  deriving Inhabited, Repr

private partial def instructionCalls (target : CallTarget) : Instruction → Bool
  | .call actual => actual == target
  | .block _ body | .loop _ body => body.any (instructionCalls target)
  | .ifElse thenBody elseBody =>
      thenBody.any (instructionCalls target) ||
        elseBody.any (instructionCalls target)
  | _ => false

/-- Add only the rule locals needed by calls actually present in `function`. -/
def reserveLocals (rewrites : Array Rewrite) (function : Function) :
    Except Error Function := do
  let mut required : Array (FVarId × AbiKind) := #[]
  for rewrite in rewrites do
    if function.body.any (instructionCalls rewrite.target) then
      for requirement in rewrite.locals do
        if function.params.any (·.1 == requirement.1) ||
            function.locals.any (·.1 == requirement.1) then
          throw (.reservedLocal function.name requirement.1)
        if let some previous := required.find? (·.1 == requirement.1) then
          unless previous.2 == requirement.2 do
            throw (.conflictingRequirement requirement.1)
        else
          required := required.push requirement
  return { function with locals := function.locals ++ required }

mutual
  private partial def rewriteInstructions (rewrites : Array Rewrite) :
      List Instruction → List Instruction
    | instructions => instructions.flatMap (rewriteInstruction rewrites)

  private partial def rewriteInstruction (rewrites : Array Rewrite) :
      Instruction → List Instruction
    | .call target =>
        match rewrites.find? (·.target == target) with
        | some rewrite => rewrite.body
        | none => [.call target]
    | .block label body =>
        [.block label (rewriteInstructions rewrites body)]
    | .loop label body =>
        [.loop label (rewriteInstructions rewrites body)]
    | .ifElse thenBody elseBody =>
        [.ifElse (rewriteInstructions rewrites thenBody)
          (rewriteInstructions rewrites elseBody)]
    | instruction => [instruction]
end

/-- Apply checked caller-local reservation followed by call replacement. -/
def rewriteFunction (rewrites : Array Rewrite) (function : Function) :
    Except Error Function := do
  let function ← reserveLocals rewrites function
  return { function with body := rewriteInstructions rewrites function.body }

private def exampleValue : FVarId := ⟨`exampleValue⟩
private def exampleResult : FVarId := ⟨`exampleResult⟩
private def exampleTarget : CallTarget := .declaration `Example.inline

private def exampleRewrite : Rewrite := {
  target := exampleTarget
  locals := #[(exampleResult, .uint32)]
  body := [.localSet exampleResult, .localGet exampleResult] }

private def exampleFunction : Function := {
  name := `Example.caller
  params := #[(exampleValue, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [.localGet exampleValue, .call exampleTarget, .ret] }

#guard match rewriteFunction #[exampleRewrite] exampleFunction with
  | .ok function =>
      function.locals == #[(exampleResult, .uint32)] &&
        function.body == [.localGet exampleValue, .localSet exampleResult,
          .localGet exampleResult, .ret]
  | .error _ => false

#guard match rewriteFunction #[{
    exampleRewrite with locals := #[(exampleValue, .uint32)]
  }] exampleFunction with
  | .error (.reservedLocal function localId) =>
      function == exampleFunction.name && localId == exampleValue
  | _ => false

end Fir.Wasm.Emit.ResidentCallSite
