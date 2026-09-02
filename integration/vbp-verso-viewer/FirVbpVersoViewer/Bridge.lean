import VersoBlueprintVir.Preview.Widget

namespace FirVbpVersoViewer.Bridge

open Lean.Vir
open Lean.Vir.Browser
open Lean.Vir.React

/-- Re-enter a retained Lean React component thunk synchronously. -/
def invokeComponent
    (callback : @& (Unit → ReactM (Js Node))) : ReactM (Js Node) :=
  callback ()

/-- Re-enter a retained Lean DOM event callback synchronously. -/
def invokeEvent
    (callback : @& (Js Event → DomM Unit)) (event : Js Event) : DomM Unit :=
  callback event

/-- Re-enter the string-valued updater used by this widget's managed state. -/
def invokeStringStateUpdate
    (callback : @& (Js String → RuntimeM (Js String)))
    (value : Js String) : RuntimeM (Js String) :=
  callback value

/-- Execute a retained Lean effect setup action. -/
def invokeEffectSetup
    (callback : @& (DomM (Option (DomM Unit)))) :
    DomM (Option (DomM Unit)) :=
  callback

/-- Execute a cleanup action returned by a retained Lean effect setup. -/
def invokeEffectCleanup (callback : @& (DomM Unit)) : DomM Unit :=
  callback

end FirVbpVersoViewer.Bridge
