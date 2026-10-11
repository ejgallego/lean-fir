import VersoBlueprint.Macros

/-!
Shared presentation notation for the compiler argument and heap construction.
These TeX commands abbreviate mathematical notation; they define no Lean
predicates. Each chapter explains the predicate and its hypotheses at first use.

* `FirSourceStep` is one successful source advance; `FirSourceSteps{n}` is a
  path of exactly `n` advances, with the source external implementation fixed.
* `FirTargetSteps{M}{m}` is a path of `m` structured target steps in package `M`.
  The two path notations are introduced in the source/target machine section.
* `FirRooted{A}{w}` is the rooted relation at original export ABI `A`, with
  current witness `w`; `FirRootedAt{A}` hides that witness. The observation and
  representation section introduces both and their fixed ambient parameters.
* `FirReturned{r}{v}` is the returned observation of source runtime `r` and
  value `v`; `FirSuccess{p}` is the successful-return property for program `p`.
  The successful-return section explains the universal invocation scope.
* `FirClosed{c}{h}` means whole-region closure at or above source cutoff `c` in heap
  `h`; `FirOwnedReach{h}{v}` follows owned edges from source value `v` in `h`.
  `FirHeap{l}` is the source heap value referring to location `l`, not a byte address.
  The worked initializer and heap-separation sections introduce these objects.
-/

tex_prelude r#"
\newcommand{\FirSourceStep}{\leadsto_s}
\newcommand{\FirSourceSteps}[1]{\overset{#1}{\leadsto}_s}
\newcommand{\FirTargetSteps}[2]{\overset{#2}{\longrightarrow}_{#1}}
\newcommand{\FirRooted}[2]{R_{#1,#2}}
\newcommand{\FirRootedAt}[1]{R_{#1}}
\newcommand{\FirReturned}[2]{O(#1,#2)}
\newcommand{\FirSuccess}[1]{P_{\mathrm{success}}(#1)}
\newcommand{\FirClosed}[2]{\operatorname{Closed}_{#1}(#2)}
\newcommand{\FirOwnedReach}[2]{\operatorname{ownedReach}_{#1}(#2)}
\newcommand{\FirHeap}[1]{\operatorname{heap}(#1)}
"#
