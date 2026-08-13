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
  if incompatiblePair policy.steps .arraysStrict .arraysAvailable then
    throw (.manifest "resident linker policy selects both strict and available Array linking")
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
  runtimeNames : Std.HashMap RuntimeOp Name := {}
  declarationNames : Std.HashMap Name Name := {}
  deriving Inhabited

private partial def rewriteInstructionBatch (plan : RewritePlan) :
    Instruction → Instruction
  | .call (.runtime operation) =>
      match plan.runtimeNames.get? operation with
      | some name => .call (.declaration name)
      | none => .call (.runtime operation)
  | .call (.declaration declaration) =>
      match plan.declarationNames.get? declaration with
      | some name => .call (.declaration name)
      | none => .call (.declaration declaration)
  | .block label body => .block label (body.map (rewriteInstructionBatch plan))
  | .loop label body => .loop label (body.map (rewriteInstructionBatch plan))
  | .ifElse thenBody elseBody =>
      .ifElse (thenBody.map (rewriteInstructionBatch plan))
        (elseBody.map (rewriteInstructionBatch plan))
  | instruction => instruction

private def rewriteFunctionBatch (plan : RewritePlan) (function : Function) : Function :=
  if plan.runtimeNames.isEmpty && plan.declarationNames.isEmpty then function
  else { function with body := function.body.map (rewriteInstructionBatch plan) }

private structure RewriteCohort where
  start : Nat
  stop : Nat
  firstPlan : Nat := 0

private def resolveDeclaration (plan : RewritePlan) (name : Name) : Name :=
  plan.declarationNames.getD name name

/-- Compose call rewrites in policy order: `later (earlier call)`. -/
private def composeRewritePlans (earlier later : RewritePlan) : RewritePlan :=
  let runtimeNames := earlier.runtimeNames.fold
    (fun names operation target =>
      names.insert operation (resolveDeclaration later target))
    (Std.HashMap.emptyWithCapacity
      (earlier.runtimeNames.size + later.runtimeNames.size))
  let runtimeNames := later.runtimeNames.fold
    (fun names operation target =>
      if earlier.runtimeNames.contains operation then names
      else names.insert operation target)
    runtimeNames
  let declarationNames := earlier.declarationNames.fold
    (fun names source target =>
      names.insert source (resolveDeclaration later target))
    (Std.HashMap.emptyWithCapacity
      (earlier.declarationNames.size + later.declarationNames.size))
  let declarationNames := later.declarationNames.fold
    (fun names source target =>
      if earlier.declarationNames.contains source then names
      else names.insert source target)
    declarationNames
  { runtimeNames, declarationNames }

private def rewriteCohortsFor (size : Nat) : Array RewriteCohort :=
  if size == 0 then #[] else #[{ start := 0, stop := size }]

private def rewritePlanSuffixes (plans : Array RewritePlan) : Array RewritePlan :=
  (plans.foldr
    (fun plan suffixes => suffixes.push
      (composeRewritePlans plan suffixes.back!))
    #[{}]).reverse

private def applyRewriteCohorts (plans : Array RewritePlan)
    (cohorts : Array RewriteCohort)
    (module : Module) : Module :=
  let suffixes := rewritePlanSuffixes plans
  { module with
    functions := cohorts.flatMap fun cohort =>
      let plan := suffixes[cohort.firstPlan]!
      (module.functions.extract cohort.start cohort.stop).map
        (rewriteFunctionBatch plan) }

/-- Steps that inspect or replace existing function bodies cannot run against
the skeleton/probe planning view. Flush accumulated rewrites first. -/
private def requiresMaterializedBodies : Step → Bool
  | .cacheSets
  | .directSelfTailCallsRequired
  | .directSelfTailCallsAvailable => true
  | _ => false

private def rewriteProbeName : Name := `_fir_resident_link_rewrite_probe

/--
Run one helper-family installer against function headers and a synthetic call
probe. The installer still performs all dependency, signature, collision and
helper-generation work, while the probe records its exact call substitutions.
Real function bodies are rewritten once when the accumulated plan is flushed.
-/
private def planStep (step : Step) (module : Module) :
    Except Source.CompileError (RewritePlan × Module) := do
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
    body := targets.toList.map Instruction.call }
  let skeletons := module.functions.map fun function => { function with body := [] }
  let prefixSize := skeletons.size + 1
  let planned ← applyStep false step { module with functions := skeletons.push probe }
  unless prefixSize ≤ planned.functions.size do
    throw (.manifest s!"resident {repr step} removed function declarations")
  for index in [:skeletons.size] do
    let before := skeletons[index]!
    let after := planned.functions[index]!
    unless before.name == after.name && before.params == after.params &&
        before.results == after.results && before.locals == after.locals &&
        after.body.isEmpty do
      throw (.manifest s!"resident {repr step} changed a function declaration shape")
  let rewrittenProbe := planned.functions[skeletons.size]!
  unless rewrittenProbe.name == rewriteProbeName &&
      rewrittenProbe.body.length == targets.size do
    throw (.manifest s!"resident {repr step} changed the linker rewrite probe shape")
  let mut runtimeNames : Std.HashMap RuntimeOp Name := {}
  let mut declarationNames : Std.HashMap Name Name := {}
  let mut removedOperations := #[]
  for (target, instruction) in targets.zip rewrittenProbe.body.toArray do
    match target, instruction with
    | .runtime operation, .call (.declaration name) =>
        runtimeNames := runtimeNames.insert operation
          (declarationNames.getD name name)
        removedOperations := removedOperations.push operation
    | .runtime operation, .call (.runtime remaining) =>
        unless operation == remaining do
          throw (.manifest s!"resident {repr step} changed a runtime probe operation")
    | .declaration declaration, .call (.declaration name) =>
        if declaration != name then
          runtimeNames := runtimeNames.fold
            (fun names operation target =>
              names.insert operation (if target == declaration then name else target))
            (Std.HashMap.emptyWithCapacity runtimeNames.size)
          declarationNames := declarationNames.fold
            (fun names source target =>
              names.insert source (if target == declaration then name else target))
            (Std.HashMap.emptyWithCapacity declarationNames.size)
            |>.insert declaration name
    | _, _ =>
        throw (.manifest s!"resident {repr step} changed a rewrite probe instruction")
  let newFunctions := planned.functions.extract prefixSize planned.functions.size
  let runtimeOperations := Fir.Wasm.updateRuntimeOps module.runtimeOperations
    removedOperations newFunctions
  let externalImports := planned.imports.filter (·.operation?.isNone)
  let result : Module := {
    planned with
    functions := module.functions ++ newFunctions
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    runtimeOperations }
  return ({ runtimeNames, declarationNames }, result)

private def applyStepsPlanned (steps : List Step) (plans : Array RewritePlan)
    (cohorts : Array RewriteCohort)
    (module : Module) : Except Source.CompileError Module := do
  match steps with
  | [] => return applyRewriteCohorts plans cohorts module
  | step :: steps =>
      if requiresMaterializedBodies step then
        let module := applyRewriteCohorts plans cohorts module
        let module ← applyStep false step module
        applyStepsPlanned steps #[] (rewriteCohortsFor module.functions.size) module
      else
        let oldSize := module.functions.size
        let (stepPlan, module) ← planStep step module
        let plans := plans.push stepPlan
        let mut cohorts := cohorts
        if oldSize < module.functions.size then
          cohorts := cohorts.push {
            start := oldSize
            stop := module.functions.size
            firstPlan := plans.size }
        applyStepsPlanned steps plans cohorts module

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
        #[] (rewriteCohortsFor module.functions.size) module
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

/-- Available external-helper families in their checked dependency order. -/
def closedApplicationFamilySteps : Array Step := #[
  .numericAvailable,
  .bigNumeric,
  .natArithmeticAvailable,
  .fixedWidthAvailable,
  .floatAvailable,
  .arraysAvailable,
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

#guard closedApplicationRetainedExternalNames.contains "Float.ofScientific"

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

end Fir.Wasm.Emit.ResidentLinker
