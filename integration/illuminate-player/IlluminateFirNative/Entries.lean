import Fir.Wasm.Emit.BitExactFloat

namespace IlluminateFirNative.Entries

open Lean

/-- Entry names are data; this module does not import the application. -/
def full : Array Name := #[
  `Illuminate.AnimationPlayer.initialLive,
  `Illuminate.AnimationPlayer.transitionLive]

def selection : Array Name := #[
  `Illuminate.AnimationPlayer.initialSelectionLive,
  `Illuminate.AnimationPlayer.transitionSelectionLive,
  `IlluminateFirNative.transitionSelectionTickLive]

def selectionPublic : Array Name := #[
  `Illuminate.AnimationPlayer.initialSelectionLive,
  `Illuminate.AnimationPlayer.transitionSelectionLive,
  Fir.Wasm.Emit.BitExactFloat.facadeName `IlluminateFirNative.transitionSelectionTickLive]

end IlluminateFirNative.Entries
