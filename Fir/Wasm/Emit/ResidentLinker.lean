import Fir.Wasm.Emit.ResidentArray
import Fir.Wasm.Emit.ResidentBigNumeric
import Fir.Wasm.Emit.ResidentCache
import Fir.Wasm.Emit.ResidentClosureAllocation
import Fir.Wasm.Emit.ResidentConstructor
import Fir.Wasm.Emit.ResidentDeadCode
import Fir.Wasm.Emit.ExternalRuntime
import Fir.Wasm.Emit.ResidentFallback
import Fir.Wasm.Emit.ResidentFloat
import Fir.Wasm.Emit.ResidentLiteral
import Fir.Wasm.Emit.ResidentMutation
import Fir.Wasm.Emit.ResidentNatMod
import Fir.Wasm.Emit.ResidentNatShift
import Fir.Wasm.Emit.ResidentNumeric
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
  | stringOperations
  | stringOperationsAvailable
  | stringLiterals
  | fallbacks
  | fallbacksAvailable
  | floatStrict
  | floatAvailable
  | arraysStrict
  | arraysAvailable
  | natModStrict
  | natModAvailable
  | natShiftAvailable
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

private def applyStep (step : Step) (module : Module) :
    Except Source.CompileError Module :=
  match step with
  | .getTag => transform "getTag" ResidentRuntime.internalizeGetTag module
  | .isShared => transform "isShared" ResidentRuntime.internalizeIsShared module
  | .readProjections =>
      transform "read projections" ResidentRuntime.internalizeReadProjections module
  | .closureProjections =>
      transform "closure projections" ResidentRuntime.internalizeClosureProjections module
  | .closureMatches =>
      transform "closure matches" ResidentRuntime.internalizeClosureMatches module
  | .allocator => transform "allocator" ResidentAllocator.install module
  | .constructors =>
      transform "constructor allocation" ResidentConstructor.internalizeConstructors module
  | .immediateNaturals =>
      transform "immediate Naturals" ResidentLiteral.internalizeImmediateNaturals module
  | .partialApplications =>
      transform "partial applications"
        ResidentClosureAllocation.internalizePartialApplications module
  | .setters => transform "setters" ResidentMutation.internalizeSetters module
  | .increments =>
      transform "increments" ResidentReferenceCount.internalizeIncrements module
  | .releases => transform "releases" ResidentRelease.internalizeReleases module
  | .tagSetters => transform "tag setters" ResidentMutation.internalizeTagSetters module
  | .cacheSets =>
      transform "cache publication" ResidentCache.internalizeCacheSets module
  | .scalarBoxesAvailable =>
      transform "available scalar boxes" ResidentScalarBox.internalizeAvailable module
  | .numericStrict =>
      transform "Nat/Int operations" ResidentNumeric.internalize module
  | .numericAvailable =>
      transform "available Nat/Int operations" ResidentNumeric.internalizeAvailable module
  | .bigNumeric =>
      transform "arbitrary-precision Nat/Int operations" ResidentBigNumeric.internalize module
  | .stringOperations =>
      transform "String operations" ResidentString.internalize module
  | .stringOperationsAvailable =>
      transform "available String operations" ResidentString.internalizeAvailable module
  | .stringLiterals =>
      transform "String literals" ResidentLiteral.internalizeStrings module
  | .fallbacks => transform "fallbacks" ResidentFallback.internalize module
  | .fallbacksAvailable =>
      transform "available fallbacks" ResidentFallback.internalizeAvailable module
  | .floatStrict => transform "Float operations" ResidentFloat.internalize module
  | .floatAvailable =>
      transform "available Float operations" ResidentFloat.internalizeAvailable module
  | .arraysStrict => transform "Array operations" ResidentArray.internalize module
  | .arraysAvailable =>
      transform "available Array operations" ResidentArray.internalizeAvailable module
  | .natModStrict => transform "Nat.mod" ResidentNatMod.internalize module
  | .natModAvailable =>
      transform "available Nat.mod" ResidentNatMod.internalizeAvailable module
  | .natShiftAvailable =>
      transform "available Nat.shiftRight" ResidentNatShift.internalizeAvailable module
  | .usizeAvailable =>
      transform "available USize operations" ResidentUSize.internalizeAvailable module
  | .directSelfTailCallsRequired => do
      let result ← TailCall.eliminateDirectSelfCalls module
        |>.mapError Source.CompileError.manifest
      unless result.rewrittenCalls > 0 do
        throw (.manifest "resident linker found no direct self-tail calls")
      return result.module
  | .directSelfTailCallsAvailable =>
      return (← TailCall.eliminateDirectSelfCalls module
        |>.mapError Source.CompileError.manifest).module

private def applySteps (steps : List Step) (module : Module) :
    Except Source.CompileError Module := do
  match steps with
  | [] => return module
  | step :: steps => applySteps steps (← applyStep step module)

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
  let module ← applySteps policy.steps.toList module
  let module ← match policy.publicExports with
    | none => pure module
    | some exports =>
        transform "dead-code pruning"
          (fun module => ResidentDeadCode.pruneToExports module exports) module
  checkPostconditions policy module
  return module

/-- Apply one symbolic policy and encode only the final linked module. -/
def linkArtifact (policy : Policy) (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ← linkModule policy artifact.module
  let bytes ← Fir.Wasm.Emit.encode module |>.mapError Source.CompileError.encoding
  return { artifact with module, bytes }

/--
Prepare a source artifact for an instance-lifetime arena. Pure lazy constants
become direct calls so no runtime root can retain scratch values; the source
module must then contain no globals before the resident allocator is linked.
-/
def prepareArenaArtifact (artifact : Source.ModuleArtifact) :
    Except Source.CompileError Source.ModuleArtifact := do
  let module ← ResidentCache.eliminateLazyInitializers artifact.module
    |>.mapError fun error =>
      Source.CompileError.manifest
        s!"failed to eliminate lazy initializers for the arena: {repr error}"
  unless module.globals.isEmpty do
    throw (.manifest "arena source module retained resident globals")
  let bytes ← Fir.Wasm.Emit.encode module |>.mapError Source.CompileError.encoding
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
    ResidentFloat.externalDeclarations ++
    ExternalRuntime.mathDeclarations ++
    ResidentArray.availableExternalDeclarations ++
    #[ResidentNatMod.declaration, ResidentNatShift.declaration] ++
    ResidentUSize.externalDeclarations ++
    ResidentString.externalDeclarations ++
    ResidentFallback.externalDeclarations
  declarations.foldl addUnique #[]

def closedApplicationRetainedExternalNames : Array String :=
  closedApplicationExternalDeclarations.map Name.toString

/--
Runtime policy for a closed structured application. It links only the
available operations in the larger scalar families, then retains the requested
source entries plus the low-level arena surface.
-/
def closedApplicationPolicy (sourceExports : Array Name) : Policy := {
  steps := commonSteps ++ #[
    .numericAvailable,
    .bigNumeric,
    .floatAvailable,
    .arraysAvailable,
    .natModAvailable,
    .natShiftAvailable,
    .usizeAvailable,
    .stringOperationsAvailable,
    .stringLiterals,
    .fallbacksAvailable,
    .directSelfTailCallsAvailable]
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
