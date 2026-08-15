import Fir.Wasm.Emit.ResidentArray
import Fir.Wasm.Emit.ResidentBigNumeric
import Fir.Wasm.Emit.ResidentByteArray
import Fir.Wasm.Emit.ResidentCache
import Fir.Wasm.Emit.ResidentClosureAllocation
import Fir.Wasm.Emit.ResidentConstructor
import Fir.Wasm.Emit.ResidentDeadCode
import Fir.Wasm.Emit.ExternalRuntime
import Fir.Wasm.Emit.ResidentFallback
import Fir.Wasm.Emit.ResidentFloat
import Fir.Wasm.Emit.ResidentFixedWidth
import Fir.Wasm.Emit.ResidentLiteral
import Fir.Wasm.Emit.ResidentMutation
import Fir.Wasm.Emit.ResidentNatArithmetic
import Fir.Wasm.Emit.ResidentNatMod
import Fir.Wasm.Emit.ResidentNatShift
import Fir.Wasm.Emit.ResidentNumeric
import Fir.Wasm.Emit.ResidentPlatform
import Fir.Wasm.Emit.ResidentReferenceCount
import Fir.Wasm.Emit.ResidentRelease
import Fir.Wasm.Emit.ResidentRuntime
import Fir.Wasm.Emit.ResidentScalarBox
import Fir.Wasm.Emit.ResidentString
import Fir.Wasm.Emit.ResidentUSize
import Fir.Wasm.Emit.Source
import Fir.Wasm.Emit.TailCall

namespace Fir.Wasm.Emit.ResidentLinker

open Lean
open Fir.Wasm

/--
One checked symbolic linking operation. A policy is an explicit ordered list
of these steps: the linker does not infer missing runtime support or install
host fallbacks.
-/
inductive Step where
  | getTag
  | isShared
  | readProjections
  | closureProjections
  | closureMatches
  | allocator
  | constructors
  | immediateNaturals
  | partialApplications
  | setters
  | increments
  | releases
  | tagSetters
  | cacheSets
  | scalarBoxesAvailable
  | numericStrict
  | numericAvailable
  | bigNumeric
  | natArithmeticAvailable
  | fixedWidthAvailable
  | stringOperations
  | stringOperationsAvailable
  | stringLiterals
  | fallbacks
  | fallbacksAvailable
  | floatStrict
  | floatAvailable
  | arraysStrict
  | arraysAvailable
  | arraysTrustedStrict
  | arraysTrustedAvailable
  | byteArraysAvailable
  | natModStrict
  | natModAvailable
  | natShiftAvailable
  | platformAvailable
  | usizeAvailable
  | directSelfTailCallsRequired
  | directSelfTailCallsAvailable
  deriving Inhabited, BEq, Repr

/--
An explicit resident-link policy. Optional public exports are applied only
after every helper family has been linked, so dead-code pruning sees the full
direct-call graph. The postconditions make package closure fail closed.
-/
structure Policy where
  steps : Array Step
  /-- Revalidate both sides of every internal step for diagnostics. The
  production default validates once at linker entry and once at exit. -/
  validateEachStep : Bool := false
  publicExports : Option (Array Name) := none
  allowedExternalImports : Option (Array Name) := none
  requireResidentMemory : Bool := true
  requireZeroImports : Bool := true
  requireNoRuntimeOperations : Bool := true

private def addUnique [BEq α] (items : Array α) (item : α) : Array α :=
  if items.contains item then items else items.push item

private def hasDuplicates [BEq α] (items : Array α) : Bool :=
  !((items.foldl addUnique #[]).size == items.size)

private def incompatiblePair (steps : Array Step) (left right : Step) : Bool :=
  steps.contains left && steps.contains right

private def validatePolicy (policy : Policy) : Except Source.CompileError Unit := do
  if hasDuplicates policy.steps then
    throw (.manifest
      s!"resident linker policy contains duplicate steps: {repr policy.steps}")
  if incompatiblePair policy.steps .numericStrict .numericAvailable then
    throw (.manifest "resident linker policy selects both strict and available Numeric linking")
  if incompatiblePair policy.steps .floatStrict .floatAvailable then
    throw (.manifest "resident linker policy selects both strict and available Float linking")
  let arraySteps := policy.steps.filter fun step =>
    step == .arraysStrict || step == .arraysAvailable ||
      step == .arraysTrustedStrict || step == .arraysTrustedAvailable
  if arraySteps.size > 1 then
    throw (.manifest
      s!"resident linker policy selects multiple Array linking modes: {repr arraySteps}")
  if incompatiblePair policy.steps .natModStrict .natModAvailable then
    throw (.manifest "resident linker policy selects both strict and available Nat.mod linking")
  if let some exports := policy.publicExports then
    if exports.isEmpty then
      throw (.manifest "resident linker policy requires at least one public export")
    if hasDuplicates exports then
      throw (.manifest s!"resident linker policy contains duplicate public exports: {exports}")
  if let some declarations := policy.allowedExternalImports then
    if hasDuplicates declarations then
      throw (.manifest
        s!"resident linker policy contains duplicate allowed imports: {declarations}")

private def transform [Repr error] (label : String)
    (link : Module → Except error Module) (module : Module) :
    Except Source.CompileError Module :=
  link module |>.mapError fun error =>
    .manifest s!"failed to internalize resident {label}: {repr error}"

private def applyStep (validate : Bool) (step : Step) (module : Module) :
    Except Source.CompileError Module :=
  match step with
  | .getTag => transform "getTag" (ResidentRuntime.internalizeGetTag · validate) module
  | .isShared => transform "isShared" (ResidentRuntime.internalizeIsShared · validate) module
  | .readProjections =>
      transform "read projections"
        (ResidentRuntime.internalizeReadProjections · validate) module
  | .closureProjections =>
      transform "closure projections"
        (ResidentRuntime.internalizeClosureProjections · validate) module
  | .closureMatches =>
      transform "closure matches"
        (ResidentRuntime.internalizeClosureMatches · validate) module
  | .allocator => transform "allocator" (ResidentAllocator.install · validate) module
  | .constructors =>
      transform "constructor allocation"
        (ResidentConstructor.internalizeConstructors · validate) module
  | .immediateNaturals =>
      transform "immediate Naturals"
        (ResidentLiteral.internalizeImmediateNaturals · validate) module
  | .partialApplications =>
      transform "partial applications"
        (ResidentClosureAllocation.internalizePartialApplications · validate) module
  | .setters =>
      transform "setters" (ResidentMutation.internalizeSetters · validate) module
  | .increments =>
      transform "increments"
        (ResidentReferenceCount.internalizeIncrements · validate) module
  | .releases =>
      transform "releases" (ResidentRelease.internalizeReleases · validate) module
  | .tagSetters =>
      transform "tag setters" (ResidentMutation.internalizeTagSetters · validate) module
  | .cacheSets =>
      transform "cache publication" (ResidentCache.internalizeCacheSets · validate) module
  | .scalarBoxesAvailable =>
      transform "available scalar boxes"
        (ResidentScalarBox.internalizeAvailable · validate) module
  | .numericStrict =>
      transform "Nat/Int operations" (ResidentNumeric.internalize · validate) module
  | .numericAvailable =>
      transform "available Nat/Int operations"
        (ResidentNumeric.internalizeAvailable · validate) module
  | .bigNumeric =>
      transform "arbitrary-precision Nat/Int operations"
        (ResidentBigNumeric.internalize · validate) module
  | .natArithmeticAvailable =>
      transform "available arbitrary-precision Nat arithmetic"
        (ResidentNatArithmetic.internalizeAvailable · validate) module
  | .fixedWidthAvailable =>
      transform "available fixed-width operations"
        (ResidentFixedWidth.internalizeAvailable · validate) module
  | .stringOperations =>
      transform "String operations" (ResidentString.internalize · validate) module
  | .stringOperationsAvailable =>
      transform "available String operations"
        (ResidentString.internalizeAvailable · validate) module
  | .stringLiterals =>
      transform "String literals" (ResidentLiteral.internalizeStrings · validate) module
  | .fallbacks =>
      transform "fallbacks" (ResidentFallback.internalize · validate) module
  | .fallbacksAvailable =>
      transform "available fallbacks"
        (ResidentFallback.internalizeAvailable · validate) module
  | .floatStrict =>
      transform "Float operations" (ResidentFloat.internalize · validate) module
  | .floatAvailable =>
      transform "available Float operations"
        (ResidentFloat.internalizeAvailable · validate) module
  | .arraysStrict =>
      transform "Array operations" (ResidentArray.internalize · validate) module
  | .arraysAvailable =>
      transform "available Array operations"
        (ResidentArray.internalizeAvailable · validate) module
  | .arraysTrustedStrict =>
      transform "trusted Array operations"
        (ResidentArray.internalizeTrusted · validate) module
  | .arraysTrustedAvailable =>
      transform "available trusted Array operations"
        (ResidentArray.internalizeAvailableTrusted · validate) module
  | .byteArraysAvailable =>
      transform "available ByteArray operations"
        (ResidentByteArray.internalizeAvailable · validate) module
  | .natModStrict =>
      transform "Nat.mod" (ResidentNatMod.internalize · validate) module
  | .natModAvailable =>
      transform "available Nat.mod" (ResidentNatMod.internalizeAvailable · validate) module
  | .natShiftAvailable =>
      transform "available Nat.shiftRight"
        (ResidentNatShift.internalizeAvailable · validate) module
  | .platformAvailable =>
      transform "available platform operations"
        (ResidentPlatform.internalizeAvailable · validate) module
  | .usizeAvailable =>
      transform "available USize operations"
        (ResidentUSize.internalizeAvailable · validate) module
  | .directSelfTailCallsRequired => do
      let result ← TailCall.eliminateDirectSelfCalls module validate
        |>.mapError Source.CompileError.manifest
      unless result.rewrittenCalls > 0 do
        throw (.manifest "resident linker found no direct self-tail calls")
      return result.module
  | .directSelfTailCallsAvailable =>
      return (← TailCall.eliminateDirectSelfCalls module validate
        |>.mapError Source.CompileError.manifest).module

private def applySteps (validate : Bool) (steps : List Step) (module : Module) :
    Except Source.CompileError Module := do
  match steps with
  | [] => return module
  | step :: steps => applySteps validate steps (← applyStep validate step module)

private structure RewritePlan where
  callRewrites : Std.HashMap CallTarget (List Instruction) := {}
  deriving Inhabited

mutual
  private partial def rewriteInstructionsBatch (plan : RewritePlan) :
      List Instruction → List Instruction
    | instructions => instructions.flatMap (rewriteInstructionBatch plan)

  private partial def rewriteInstructionBatch (plan : RewritePlan) :
      Instruction → List Instruction
    | .call target => plan.callRewrites.getD target [.call target]
    | .block label body =>
        [.block label (rewriteInstructionsBatch plan body)]
    | .loop label body =>
        [.loop label (rewriteInstructionsBatch plan body)]
    | .ifElse thenBody elseBody =>
        [.ifElse (rewriteInstructionsBatch plan thenBody)
          (rewriteInstructionsBatch plan elseBody)]
    | instruction => [instruction]
end

private def rewriteFunctionBatch (plan : RewritePlan) (function : Function) : Function :=
  if plan.callRewrites.isEmpty then function
  else { function with body := rewriteInstructionsBatch plan function.body }

/-- Steps that inspect or replace existing function bodies cannot run against
the skeleton/probe planning view. Materialize the persistent planning phase
before applying one of these steps. -/
private def requiresMaterializedBodies : Step → Bool
  | .cacheSets
  | .directSelfTailCallsRequired
  | .directSelfTailCallsAvailable => true
  | _ => false

private def rewriteProbeName : Name := `_fir_resident_link_rewrite_probe

private def rewriteProbeLabel (index : Nat) : FVarId :=
  ⟨Name.mkSimple s!"_fir_resident_link_rewrite_probe_{index}"⟩

/--
Run a contiguous group of helper-family installers against one persistent
planning view. Source bodies are replaced by headers and one synthetic call
probe; generated helper bodies remain materialized so later families rewrite
them directly. Each probe call occupies one uniquely labelled block, allowing
the whole group to replace it with any composed instruction sequence without
losing the boundary.

The group therefore constructs and verifies headers and rewrite metadata once,
then rewrites the source cohort once. The previous per-family plans rebuilt and
rescanned the same probe and headers and composed a suffix plan for every helper
cohort, making planning grow with both policy length and module size.
-/
private def applyPersistentPlan (steps : Array Step) (module : Module) :
    Except Source.CompileError Module := do
  if steps.isEmpty then return module
  if module.functions.any (·.name == rewriteProbeName) then
    throw (.manifest s!"reserved linker rewrite-probe declaration {rewriteProbeName}")
  let externalDeclarations := module.imports.filterMap (·.declaration?)
  let declarations := externalDeclarations.foldl
    (init := module.functions.map (·.name)) addUnique
  let targets := module.runtimeOperations.map CallTarget.runtime ++
    declarations.map CallTarget.declaration
  let probe : Function := {
    name := rewriteProbeName
    params := #[]
    results := #[]
    locals := #[]
    body := targets.toList.zipIdx.map fun (target, index) =>
      .block (rewriteProbeLabel index) [.call target] }
  let skeletons := module.functions.map fun function => { function with body := [] }
  let prefixSize := skeletons.size + 1
  let planned ← applySteps false steps.toList {
    module with functions := skeletons.push probe }
  unless prefixSize ≤ planned.functions.size do
    throw (.manifest s!"resident plan {repr steps} removed function declarations")
  for index in [:skeletons.size] do
    let before := skeletons[index]!
    let after := planned.functions[index]!
    unless before.name == after.name && before.params == after.params &&
        before.results == after.results && before.locals == after.locals &&
        after.body.isEmpty do
      throw (.manifest
        s!"resident plan {repr steps} changed a function declaration shape")
  let rewrittenProbe := planned.functions[skeletons.size]!
  unless rewrittenProbe.name == rewriteProbeName &&
      rewrittenProbe.body.length == targets.size do
    throw (.manifest s!"resident plan {repr steps} changed the linker rewrite probe shape")
  let mut callRewrites : Std.HashMap CallTarget (List Instruction) := {}
  for ((target, instruction), index) in
      (targets.zip rewrittenProbe.body.toArray).zipIdx do
    let .block label body := instruction |
      throw (.manifest s!"resident plan {repr steps} removed a rewrite probe boundary")
    unless label == rewriteProbeLabel index do
      throw (.manifest s!"resident plan {repr steps} changed a rewrite probe label")
    unless body == [.call target] do
      callRewrites := callRewrites.insert target body
  let plan : RewritePlan := { callRewrites }
  let newFunctions := planned.functions.extract prefixSize planned.functions.size
  let functions := module.functions.map (rewriteFunctionBatch plan) ++ newFunctions
  /- The persistent planning view orders the probe before generated helpers.
  Recollect once after replacing the probe with the real source cohort so the
  public runtime-operation order remains exactly the module's function order. -/
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let externalImports := planned.imports.filter (·.operation?.isNone)
  return {
    planned with
    functions
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    runtimeOperations }

private def applyStepsPlanned (steps : List Step) (pending : Array Step)
    (module : Module) : Except Source.CompileError Module := do
  match steps with
  | [] => applyPersistentPlan pending module
  | step :: steps =>
      if requiresMaterializedBodies step then
        let module ← applyPersistentPlan pending module
        let module ← applyStep false step module
        applyStepsPlanned steps #[] module
      else
        applyStepsPlanned steps (pending.push step) module

private def checkPostconditions (policy : Policy) (module : Module) :
    Except Source.CompileError Unit := do
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error =>
      throw (.manifest s!"resident linker produced an invalid module: {repr error}")
  if policy.requireResidentMemory &&
      module.memory != some ResidentRuntime.residentMemory then
    throw (.manifest "resident linker did not produce module-owned resident memory")
  if policy.requireZeroImports && !module.imports.isEmpty then
    throw (.manifest
      s!"resident linker left {module.imports.size} function import(s)")
  if let some declarations := policy.allowedExternalImports then
    for import_ in module.imports do
      let some declaration := import_.declaration?
        | throw (.manifest "resident linker retained a non-external import")
      unless declarations.contains declaration do
        throw (.manifest
          s!"resident linker retained unsupported external {declaration}")
  if policy.requireNoRuntimeOperations && !module.runtimeOperations.isEmpty then
    throw (.manifest
      s!"resident linker left {module.runtimeOperations.size} runtime operation(s)")
  if let some exports := policy.publicExports then
    unless module.exports == exports do
      throw (.manifest
        s!"resident linker produced exports {repr module.exports}, expected {repr exports}")

/-- Apply a resident-link policy to one symbolic module and validate its closure. -/
def linkModule (policy : Policy) (module : Module) :
    Except Source.CompileError Module := do
  validatePolicy policy
  match Fir.Wasm.validateModule module with
  | .ok () => pure ()
  | .error error =>
      throw (.manifest s!"resident linker received an invalid module: {repr error}")
  let module ← if policy.validateEachStep then
      applySteps true policy.steps.toList module
    else do
      applyStepsPlanned policy.steps.toList
        #[] module
  let module ← match policy.publicExports with
    | none => pure module
    | some exports =>
        transform "dead-code pruning"
          (fun module => ResidentDeadCode.pruneToExports module exports
            policy.validateEachStep) module
  checkPostconditions policy module
  return module

/-- Apply one symbolic policy and encode only the final linked module. -/
def linkArtifact (policy : Policy) (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ← linkModule policy artifact.module
  let bytes ← Fir.Wasm.Emit.encodeValidated module
    |>.mapError Source.CompileError.encoding
  return { artifact with module, bytes }

/--
Prepare a symbolic source module for an instance-lifetime arena. Pure lazy
constants become direct calls so no runtime root can retain scratch values;
the source module must then contain no globals before the resident allocator
is linked.
-/
def prepareArenaModule (module : Module) (validate : Bool := true) :
    Except Source.CompileError Module := do
  let module ← ResidentCache.eliminateLazyInitializers module validate
    |>.mapError fun error =>
      Source.CompileError.manifest
        s!"failed to eliminate lazy initializers for the arena: {repr error}"
  unless module.globals.isEmpty do
    throw (.manifest "arena source module retained resident globals")
  return module

/-- Prepare and encode a standalone source artifact for an instance-lifetime arena. -/
def prepareArenaArtifact (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ← prepareArenaModule artifact.module
  let bytes ← Fir.Wasm.Emit.encodeValidated module
    |>.mapError Source.CompileError.encoding
  return { artifact with module, bytes }

/--
Prepare an arena module, choose its resident-link policy from that prepared
module, and encode only the final linked artifact. `linkModule` supplies the
validation boundary for the unchecked arena rewrite and validates its output
before `encodeValidated` consumes it.
-/
def prepareArenaAndLinkArtifact (policyFor : Module → Policy)
    (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ← prepareArenaModule artifact.module false
  let module ← linkModule (policyFor module) module
  let bytes ← Fir.Wasm.Emit.encodeValidated module
    |>.mapError Source.CompileError.encoding
  return { artifact with module, bytes }

/--
Diagnostic-only preparation of a two-region instance arena by eagerly forcing
compiler lazy caches.
The synthesized idempotent initializer is exported from the source module and
must be called by the consumer before input allocation. Its post-call frontier
becomes the persistent lower region; public-call scratch is allocated above
that checkpoint and may be rewound safely.

This is unsafe for arbitrary source closures because it changes lazy
evaluation. Production packages use ordinary `linkArtifact` and the
cache-aware rewind floor instead.
-/
def prepareUnsafeEagerPersistentCacheArenaModule
    (module : Module) (validate : Bool := true) :
    Except Source.CompileError Module :=
  ResidentCache.installUnsafeEagerPersistentInitializer module validate
    |>.mapError fun error =>
      Source.CompileError.manifest
        s!"failed to install persistent lazy-cache initializer: {repr error}"

/-- Prepare and encode a source artifact with persistent lazy-cache globals. -/
def prepareUnsafeEagerPersistentCacheArenaArtifact
    (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ← prepareUnsafeEagerPersistentCacheArenaModule artifact.module
  let bytes ← Fir.Wasm.Emit.encodeValidated module
    |>.mapError Source.CompileError.encoding
  return { artifact with module, bytes }

/--
Prepare the persistent-cache arena, derive its resident policy from the
prepared module, link it, and encode the final zero-import artifact.
-/
def prepareUnsafeEagerPersistentCacheArenaAndLinkArtifact
    (policyFor : Module → Policy)
    (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ← prepareUnsafeEagerPersistentCacheArenaModule
    artifact.module false
  let module ← linkModule (policyFor module) module
  let bytes ← Fir.Wasm.Emit.encodeValidated module
    |>.mapError Source.CompileError.encoding
  return { artifact with module, bytes }

/-- The accepted common physical helper prefix, in dependency order. -/
def commonSteps : Array Step := #[
  .getTag,
  .isShared,
  .readProjections,
  .closureProjections,
  .closureMatches,
  .allocator,
  .constructors,
  .immediateNaturals,
  .partialApplications,
  .setters,
  .increments,
  .releases,
  .tagSetters,
  .cacheSets,
  .scalarBoxesAvailable]

/--
The common physical prefix specialized to the runtime operations that are
actually present in one lowered module. `getTag` and `isShared` each install a
single exact runtime operation and therefore deliberately fail when that
operation is absent; the remaining common families already internalize every
matching operation and are valid no-ops on a narrow closure.

This operation-derived prefix lets generic consumers link small source
closures without maintaining application-specific helper lists. The fixed
`commonSteps` value remains the accepted policy for packages whose reviewed
closure contains both singleton operations.
-/
def availableCommonSteps (module : Module) : Array Step :=
  commonSteps.filter fun step =>
    match step with
    | .getTag => module.runtimeOperations.contains .getTag
    | .isShared => module.runtimeOperations.contains .isShared
    | _ => true

/-- Exact resident pipeline used by the accepted `Std.Format.prettyM` closure. -/
def prettyFormatPolicy : Policy := {
  steps := commonSteps ++ #[
    .numericStrict,
    .bigNumeric,
    .stringOperations,
    .stringLiterals,
    .fallbacks,
    .directSelfTailCallsRequired] }

/-- Public allocator operations required by persistent and scratch-arena adapters. -/
def allocatorExports : Array Name := #[
  ResidentAllocator.frontierName,
  ResidentAllocator.setFrontierName,
  ResidentAllocator.rewindName,
  ResidentAllocator.allocateName]

/--
Standard external declarations that a closed application asks source capture
to retain.  Every declaration is then either internalized by a checked resident
helper family or left in `ExternalRuntime.mathDeclarations` for the separately
compiled standard math runtime.  This inventory is independent of source entry
names and replaces per-application retained-external lists.
-/
def closedApplicationExternalDeclarations : Array Name :=
  let declarations :=
    ResidentNumeric.externalDeclarations ++
    ResidentNatArithmetic.externalDeclarations ++
    ResidentFixedWidth.externalDeclarations ++
    ResidentFloat.externalDeclarations ++
    ExternalRuntime.mathDeclarations ++
    ResidentArray.availableExternalDeclarations ++
    ResidentByteArray.externalDeclarations ++
    #[ResidentNatMod.declaration, ResidentNatShift.declaration,
      ResidentNatShift.log2Declaration] ++
    #[ResidentPlatform.declaration] ++
    ResidentUSize.externalDeclarations ++
    ResidentString.availableExternalDeclarations ++
    ResidentScalarBox.externalDeclarations ++
    ResidentFallback.externalDeclarations
  declarations.foldl addUnique #[]

def closedApplicationRetainedExternalNames : Array String :=
  closedApplicationExternalDeclarations.map Name.toString

/-- Available external-helper families in their dependency order. -/
def closedApplicationFamilySteps : Array Step := #[
  .numericAvailable,
  .bigNumeric,
  .natArithmeticAvailable,
  .fixedWidthAvailable,
  .floatAvailable,
  .arraysTrustedAvailable,
  .byteArraysAvailable,
  .natModAvailable,
  .natShiftAvailable,
  .platformAvailable,
  .usizeAvailable,
  .stringOperationsAvailable,
  .stringLiterals,
  .fallbacksAvailable,
  .directSelfTailCallsAvailable]

/--
Runtime policy for a closed structured application. It links only the
available operations in the larger scalar families, then retains the requested
source entries plus the low-level arena surface.
-/
def closedApplicationPolicy (sourceExports : Array Name) : Policy := {
  steps := commonSteps ++ closedApplicationFamilySteps
  publicExports := some (sourceExports ++ allocatorExports) }

/--
Generic closed-application policy derived from the lowered source module.
Unlike `closedApplicationPolicy`, it does not require singleton common runtime
operations that the source closure never emitted. Helper-family selection is
still explicit and fail-closed; only absence of those exact operations removes
their otherwise-strict linking steps.
-/
def closedApplicationAvailablePolicy (module : Module)
    (sourceExports : Array Name) : Policy := {
  steps := availableCommonSteps module ++ closedApplicationFamilySteps
  publicExports := some (sourceExports ++ allocatorExports) }

/--
The same generic resident closure with standard math externals deliberately
left for the checked external-runtime linker.
-/
def closedApplicationFrontierPolicy (sourceExports : Array Name) : Policy := {
  closedApplicationPolicy sourceExports with
  allowedExternalImports := some ExternalRuntime.mathDeclarations
  requireZeroImports := false }

#guard !hasDuplicates prettyFormatPolicy.steps

#guard !hasDuplicates (closedApplicationPolicy #[`entry]).steps

#guard closedApplicationFamilySteps.contains .arraysTrustedAvailable

#guard !closedApplicationFamilySteps.contains .arraysAvailable

#guard match validatePolicy {
  steps := #[.arraysAvailable, .arraysTrustedAvailable]
} with
  | .error _ => true
  | .ok _ => false

private def emptyPolicyProbeModule : Module := {
  imports := #[]
  functions := #[]
  exports := #[]
  initializers := #[]
  runtimeOperations := #[] }

#guard (availableCommonSteps emptyPolicyProbeModule).contains .getTag == false

#guard (availableCommonSteps { emptyPolicyProbeModule with
  runtimeOperations := #[.getTag, .isShared]
}).take 2 == #[.getTag, .isShared]

#guard !hasDuplicates
  (closedApplicationAvailablePolicy emptyPolicyProbeModule #[`entry]).steps

#guard (closedApplicationPolicy #[`entry]).publicExports ==
  some (#[`entry] ++ allocatorExports)

#guard !closedApplicationRetainedExternalNames.contains "Float.ofScientific"

#guard ExternalRuntime.sourceDeclarations.contains `Float.ofScientific

#guard (closedApplicationFrontierPolicy #[`entry]).allowedExternalImports ==
  some ExternalRuntime.mathDeclarations

#guard (closedApplicationRetainedExternalNames.foldl addUnique #[]).size ==
  closedApplicationRetainedExternalNames.size

#guard match validatePolicy { steps := #[.getTag, .getTag] } with
  | .error (.manifest _) => true
  | _ => false

#guard match validatePolicy { steps := #[.numericStrict, .numericAvailable] } with
  | .error (.manifest _) => true
  | _ => false

private def expandingRewriteProbePolicy (validateEachStep : Bool) : Policy := {
  steps := #[.allocator, .partialApplications]
  validateEachStep
  publicExports := some ResidentClosureAllocation.exampleModule.exports }

#guard match
    linkModule (expandingRewriteProbePolicy false)
      ResidentClosureAllocation.exampleModule,
    linkModule (expandingRewriteProbePolicy true)
      ResidentClosureAllocation.exampleModule with
  | .ok planned, .ok materialized =>
      match Fir.Wasm.Emit.encode planned, Fir.Wasm.Emit.encode materialized with
      | .ok plannedBytes, .ok materializedBytes =>
          plannedBytes == materializedBytes
      | _, _ => false
  | _, _ => false

end Fir.Wasm.Emit.ResidentLinker
