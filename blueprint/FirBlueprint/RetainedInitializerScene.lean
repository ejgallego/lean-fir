import Illuminate

/-! Symbolic checkpoints of the existing retained-initializer proof.
These diagrams explain source-reviewed theorems; they do not execute a fixture
or add a simulation invariant. Diagram coordinates are layout units only. -/

namespace FirBlueprint.RetainedInitializerScene

open Illuminate

private def ink : Color := { r := 30, g := 41, b := 59 }
private def blue : Color := { r := 30, g := 84, b := 137 }
private def paleBlue : Color := { r := 235, g := 245, b := 255 }
private def amber : Color := { r := 158, g := 87, b := 9 }
private def paleAmber : Color := { r := 255, g := 248, b := 230 }
private def gray : Color := { r := 244, g := 246, b := 249 }

private def layers (ds : List (Diagram SVG)) : Diagram SVG :=
  ds.foldl Diagram.compose .empty

-- Downward page coordinates, independent of both machines' address spaces.
private def placed (x y : Float) (d : Diagram SVG) : Diagram SVG :=
  Diagram.translate x (-y) d

private def label (x y : Float) (s : String) (size : Float := 20)
    (color : Color := ink) (bold : Bool := false) : Diagram SVG :=
  placed x y <| Diagram.text s {
    fontFamily := "text", fontSize := size, color, bold, anchor := .start }

private def card (x y width height : Float) (s : String)
    (fill : Color := gray) (color : Color := ink) : Diagram SVG :=
  layers [
    placed x y <| Diagram.roundedRect width height 8
      (fill := .solid { color := fill }) (stroke := { color, width := 1.2 }),
    placed x y <| Diagram.text s { fontFamily := "text", fontSize := 20, color }]

private def shell (title sourceControl targetControl sourceFrames targetFrames
    derived : String) : Diagram SVG :=
  layers [
    placed 360 325 <| Diagram.rect 720 650
      (fill := .solid { color := Color.white }) (stroke := { color := Color.white }),
    label 16 30 title 26 ink true,
    label 20 70 "SOURCE · impure LCNF" 22 blue true,
    label 392 70 "TARGET · contracted Wasm" 22 blue true,
    card 174 125 316 86 sourceControl,
    card 548 125 316 86 targetControl,
    label 20 191 "Source heap locations" 19 ink true,
    label 392 191 "Concrete byte addresses" 19 ink true,
    Diagram.line ⟨26, -294⟩ ⟨336, -294⟩
      { color := blue, width := 1.5, dash := .dashed },
    label 20 343 "fixed cutoff c = r₀.nextLocation" 18 blue,
    placed 70 375 <| Diagram.circle 14
      (fill := .solid { color := paleAmber }) (stroke := { color := amber }),
    label 94 379 "tracked retained token ℓ < c" 18 amber,
    label 20 434 "SOURCE continuation" 19 ink true,
    label 392 434 "TARGET continuation" 19 ink true,
    card 174 482 316 76 sourceFrames paleAmber amber,
    card 548 482 316 76 targetFrames paleBlue blue,
    label 20 548 "FIXED caller history: (rₕ, Sₕ, wₕ), possibly older" 18,
    label 20 574 "FIXED initializer entry: (r₀, S₀, w₀), cutoff c; root ABI A" 18,
    label 20 613 derived 18 blue true]

private def freshHeap (phase : String) (persistent : Bool)
    (showRegion : Bool := true) : Diagram SVG :=
  layers [
    card 191 294 124 62 (if persistent then "c: Array\npersistent" else "c: Array\ncapacity 5")
      paleBlue blue,
    card 270 230 175 50 "tagged 0\ndata; no heap edge" paleBlue blue,
    Diagram.line ⟨228, -270⟩ ⟨245, -255⟩ { color := blue, width := 1.5 },
    label 20 246 (if showRegion then "fresh graph j ≥ c"
      else "returned Array") 18 blue,
    card 548 274 238 62 s!"a{phase}: represented Array\nz{phase}: tagged element" paleBlue blue,
    Diagram.line ⟨253, -294⟩ ⟨358, -316⟩
      { color := blue, width := 1.2, dash := .dotted },
    Diagram.line ⟨358, -316⟩ ⟨429, -274⟩
      { color := blue, width := 1.2, dash := .dotted },
    Diagram.line ⟨419, -273⟩ ⟨429, -274⟩ { color := blue, width := 1.5 },
    Diagram.line ⟨423, -284⟩ ⟨429, -274⟩ { color := blue, width := 1.5 },
    label 345 340 s!"proof ∃ w{phase}: c ↦ a{phase}" 17 blue,
    label 392 379 s!"q{phase} represents heap(c)" 18 blue]

/-- Cold entry: no fresh object mapping has yet been produced. -/
def entered : Diagram SVG :=
  layers [
    shell "2 · Cold initializer entry"
      "initializer body\nlocals empty; cache cold"
      "callee body\ncallee locals"
      "cache(initializer)\nbind(d,k,E,J) · Fₛ"
      "generated call · label · Fₜ"
      "DERIVED entry region/frame · entry segment: 3 target steps",
    label 34 260 "no fresh Array yet" 22 blue,
    label 397 260 "no fresh address asserted" 20 blue,
    label 392 355 "current witness w₀" 19 blue]

/-- Local return: the body produced the fresh singleton and physical result. -/
def returned : Diagram SVG :=
  layers [
    shell "12 · Initializer local return"
      "yielded heap(c)\ncallee env / joins"
      "returning q₁₂\ngenerated frames still active"
      "cache(initializer)\nbind(d,k,E,J) · Fₛ"
      "generated call · label · Fₜ"
      "DERIVED fresh yield · body path length T is existential",
    freshHeap "₁₂" false]

/-- Publication restores the target continuation before the source bind. -/
def published : Diagram SVG :=
  layers [
    shell "13 · Published; source bind still pending"
      "yielded heap(c)\ncallee env / joins remain"
      "q₁₃ on operand head\nlocal.set i · rest pending"
      "bind(d,k,E,J) · Fₛ\ncaller not resumed yet"
      "Fₜ ALREADY restored\ncaller locals + q₁₃"
      "DERIVED rooted relation at A + Closed(c) · publication: 7 steps",
    freshHeap "₁₃" true,
    label 20 409 "source global: initializer ↦ heap(c)" 17 blue,
    label 392 409 "cache value q₁₃; initialized flag 1" 17 blue]

/-- The companion endpoint binds the source destination and target local. -/
def resumed : Diagram SVG :=
  layers [
    shell "14 · Caller resumed (separate theorem)"
      "continuation k\nenv E[d ↦ heap(c)]; joins J"
      "rest after local.set i\ndestination local updated"
      "Fₛ restored\npending bind popped"
      "Fₜ REMAINS restored\ncaller local i now holds q₁₄"
      "DERIVED validated caller at A · budget B−Δ; erase only d's fact",
    freshHeap "₁₄" true false,
    label 20 409 "source global: initializer ↦ heap(c)" 17 blue,
    label 392 409 "cache value q₁₄; initialized flag 1" 17 blue]

end FirBlueprint.RetainedInitializerScene
