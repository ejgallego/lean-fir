import Fir.Wasm.Emit.ResidentLinker
import FirVbpVersoViewer.Bridge

namespace FirVbpVersoViewer.Compile

open Lean

def sourceModule : Name := `VersoBlueprintVir.Preview.Widget

def mountEntry : Name :=
  `VersoBlueprint.Experimental.VirPreview.Widget.mount

def unmountEntry : Name :=
  `VersoBlueprint.Experimental.VirPreview.Widget.unmount

def bridgeEntries : Array Name := #[
  `FirVbpVersoViewer.Bridge.invokeComponent,
  `FirVbpVersoViewer.Bridge.invokeEvent,
  `FirVbpVersoViewer.Bridge.invokeStringStateUpdate,
  `FirVbpVersoViewer.Bridge.invokeEffectSetup,
  `FirVbpVersoViewer.Bridge.invokeEffectCleanup]

def publicEntries : Array Name :=
  #[mountEntry, unmountEntry] ++ bridgeEntries

/-- Adapter-private physical release for one host-owned retained callback. -/
def releaseOwnedEntry : Name :=
  Fir.Wasm.Emit.ResidentRelease.decrementOnceName

def residentPublicExports : Array Name :=
  publicEntries ++ #[releaseOwnedEntry] ++
    Fir.Wasm.Emit.ResidentLinker.allocatorExports

/-- The exact reviewed VIR React/browser host frontier used by this widget. -/
def hostNames : Array Name := #[
  `Lean.Vir.JsValue.ofString,
  `Lean.Vir.React.Root.unmountSelectorJs,
  `Lean.Vir.JsValue.toBool,
  `Lean.Vir.React.Props.empty,
  `Lean.Vir.React.Props.setKeyJs,
  `Lean.Vir.React.Props.setRef,
  `Lean.Vir.React.Property.toJs,
  `Lean.Vir.React.Props.setProperty,
  `Lean.Vir.React.EventHandler.toJs,
  `Lean.Vir.React.Props.setEventHandler,
  `Lean.Vir.Js.Array.empty,
  `Lean.Vir.Js.Array.push,
  `Lean.Vir.React.ElementType.tagJs,
  `Lean.Vir.React.Node.createElement,
  `Lean.Vir.Browser.Performance.nowJs,
  `Lean.Vir.JsValue.toFloat,
  `Lean.Vir.React.Hooks.useRef,
  `Lean.Vir.React.Ref.get,
  `Lean.Vir.JsValue.toString,
  `Lean.Vir.React.Ref.set,
  `Lean.Vir.React.Hooks.DependencyList.empty,
  `Lean.Vir.React.Hooks.DependencyList.push,
  `Lean.Vir.React.Hooks.useLeanEffectWithoutDepsJs,
  `Lean.Vir.React.Hooks.useLeanEffectWithDepsJs,
  `Lean.Vir.React.Hooks.useState,
  `Lean.Vir.React.StateTuple.value,
  `Lean.Vir.React.StateTuple.setter,
  `Lean.Vir.React.Node.textJs,
  `Lean.Vir.React.StateSetter.modify,
  `Lean.Vir.Browser.Event.getCurrentTarget,
  `Lean.Vir.Js.Nullable.isNullJs,
  `Lean.Vir.Js.Nullable.get,
  `Lean.Vir.Browser.Event.getTarget,
  `Lean.Vir.Browser.HTMLInputElement.fromElementNullable,
  `Lean.Vir.Browser.HTMLInputElement.getChecked,
  `Lean.Vir.React.Node.componentThunkJs,
  `Lean.Vir.React.Node.fragmentWithKeyJs,
  `Lean.Vir.Browser.Performance.usedHeapBytesNullable,
  `Lean.Vir.JsValue.toNat,
  `Lean.Vir.Browser.Performance.heapLimitBytesNullable,
  `Lean.Vir.React.Root.renderComponentIntoSelectorThunkJs]

def retainedHostNames : Array String :=
  hostNames.flatMap fun name => #[name.toString, (name.str "_boxed").toString]

def retainedExternalNames : Array String :=
  retainedHostNames ++
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames

/-- Capture the exact real widget roots and the neutral callback bridges. -/
def captureSource : CoreM Fir.Validation.Lcnf.Artifact := do
  let captured ← Fir.Wasm.Emit.Source.compileEntriesIndividuallyInternalized
    publicEntries retainedExternalNames
  let source ← Fir.Wasm.Emit.Source.internalizeExternalBoxedAdapters
    captured hostNames
  Fir.Wasm.Emit.Source.internalizeFinalDependencies source
    (hostNames.map Name.toString ++
      Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames)
    (publicEntries.extract 1 publicEntries.size)

def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  Fir.Wasm.Emit.Source.compileModuleArtifactWithExports
    source publicEntries .ok

def residentPolicy (module : Fir.Wasm.Module) :
    Fir.Wasm.Emit.ResidentLinker.Policy := {
  Fir.Wasm.Emit.ResidentLinker.closedApplicationAvailablePolicy
    module publicEntries with
  publicExports := some residentPublicExports
  allowedExternalImports := some hostNames
  requireZeroImports := false }

def linkResidentRuntime (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  Fir.Wasm.Emit.ResidentLinker.linkArtifact
    (residentPolicy artifact.module) artifact

def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind linkResidentRuntime

end FirVbpVersoViewer.Compile
