import Fir.Wasm.Validate

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

/-- One typed call replacement and the fresh locals it requires.

`signature` is deliberately semantic rather than merely physical: a rewrite
for an `object`/`tobject`/`tagged` operation must not be accepted just because
all three happen to occupy an `i32` Wasm lane.  `validateRewrites` checks this
contract against the source module before any caller body is changed. -/
structure Rewrite where
  target : CallTarget
  signature : Signature
  body : List Instruction
  locals : Array (FVarId × AbiKind) := #[]
  deriving Inhabited, BEq

inductive Error where
  | duplicateTarget (rewriteIndex previousIndex : Nat)
  | missingTarget (rewriteIndex : Nat)
  | incompatibleSignature (rewriteIndex : Nat)
  | reservedLocal (function : Name) (localId : FVarId)
  | conflictingRequirement (localId : FVarId)
  deriving Inhabited, Repr

/-- Check the semantic declaration contract of every registered rewrite.

This is separate from the ordinary symbolic module validator: the registry
check prevents a stale or duplicate primitive specification, while final
module validation checks the replacement instruction body at every concrete
caller stack boundary. -/
def validateRewrites (rewrites : Array Rewrite) (module : Module) :
    Except Error Unit := do
  let mut seen : Std.HashMap CallTarget Nat :=
    Std.HashMap.emptyWithCapacity rewrites.size
  for (rewrite, index) in rewrites.zipIdx do
    if let some previousIndex := seen.get? rewrite.target then
      throw (.duplicateTarget index previousIndex)
    seen := seen.insert rewrite.target index
    let some signature := module.callSignature? rewrite.target |
      throw (.missingTarget index)
    unless signature == rewrite.signature do
      throw (.incompatibleSignature index)

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
private def rewriteFunction (rewrites : Array Rewrite) (function : Function) :
    Except Error Function := do
  let function ← reserveLocals rewrites function
  return { function with body := rewriteInstructions rewrites function.body }

/-- Validate one typed rewrite registry and apply it to every module function. -/
def rewriteModuleFunctions (rewrites : Array Rewrite) (module : Module) :
    Except Error (Array Function) := do
  validateRewrites rewrites module
  module.functions.mapM (rewriteFunction rewrites)

private def exampleValue : FVarId := ⟨`exampleValue⟩
private def exampleResult : FVarId := ⟨`exampleResult⟩
private def exampleTarget : CallTarget := .declaration `Example.inline

private def exampleRewrite : Rewrite := {
  target := exampleTarget
  signature := { params := #[.uint32], results := #[.uint32] }
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

private def exampleModule : Module := {
  functions := #[exampleFunction]
  imports := #[{
    key := .external `Example.inline
    moduleName := "example"
    itemName := "inline"
    signature := exampleRewrite.signature }]
  exports := #[]
  initializers := #[]
  runtimeOperations := #[] }

#guard (validateRewrites #[exampleRewrite] exampleModule).isOk

#guard match validateRewrites #[{
    exampleRewrite with
    signature := { params := #[.tobject], results := #[.tobject] }
  }] exampleModule with
  | .error (.incompatibleSignature 0) => true
  | _ => false

#guard match validateRewrites #[{
    exampleRewrite with target := .declaration `Example.missing
  }] exampleModule with
  | .error (.missingTarget 0) => true
  | _ => false

#guard match validateRewrites #[exampleRewrite, exampleRewrite] exampleModule with
  | .error (.duplicateTarget 1 0) => true
  | _ => false

end Fir.Wasm.Emit.ResidentCallSite
