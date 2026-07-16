import Fir.LeanIR.Passes.AlphaEqvLocalSound

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler

/--
SHA-256 of `Lean/Compiler/LCNF/AlphaEqv.lean` in the pinned Lean 4.32.0
toolchain. This records the exact source audited when introducing the bridge.
-/
def lean432AlphaEqvSourceSha256 : String :=
  "f62bf73971d21483f1e285ecc74980bdc12baa0bf5c494fed4dc5d021aeded43"

/--
Trusted correspondence between Lean 4.32's opaque `partial def` and FIR's
transparent, fuel-indexed copy. This is deliberately the only axiom in the
adapter: semantic theorems should consume `UpstreamBridge` explicitly, while
axiom-free local-checker theorems import `AlphaEqvLocal` instead.
-/
axiom lean432UpstreamBridge : UpstreamBridge

/-- The named trusted conversion used by compiler-facing corollaries. -/
theorem localAccepts_of_upstream
    (accepted : left.alphaEqv right = true) : Local.Accepts left right :=
  lean432UpstreamBridge.accepted left right accepted

/--
Compiler-facing construction of the declarative code relation for the
currently modeled fragment. All semantic side conditions remain explicit;
only correspondence with Lean's opaque Boolean checker is trusted.
-/
theorem trustedCodeRelated_of_upstream
    (side : CodeSideConditions ({} : FVarIdMap Lean.FVarId)
      scope scope left right)
    (accepted : left.alphaEqv right = true) :
    CodeRelated ({} : FVarIdMap Lean.FVarId) scope scope left right :=
  codeRelated_of_local_accepts side (localAccepts_of_upstream accepted)

/-- Compiler-facing construction for one canonical impure case table. -/
theorem trustedCasesCodeRelated_of_upstream
    (scope : List Lean.FVarId)
    (leftCases rightCases : LCNF.Cases .impure)
    (leftDiscrScoped : scope.contains leftCases.discr = true)
    (rightDiscrScoped : scope.contains rightCases.discr = true)
    (leftCanonical :
      LCNF.AlphaEqv.sortAlts leftCases.alts = leftCases.alts)
    (rightCanonical :
      LCNF.AlphaEqv.sortAlts rightCases.alts = rightCases.alts)
    (side : AltsSideConditions ({} : FVarIdMap Lean.FVarId) scope scope
      leftCases.alts.toList rightCases.alts.toList)
    (accepted :
      (LCNF.Code.cases leftCases).alphaEqv (.cases rightCases) = true) :
    CodeRelated ({} : FVarIdMap Lean.FVarId) scope scope
      (.cases leftCases) (.cases rightCases) :=
  codeRelated_cases_of_local_accepts leftDiscrScoped rightDiscrScoped
    leftCanonical rightCanonical side (localAccepts_of_upstream accepted)

/--
Compiler-facing terminal soundness using the single Lean-4.32 trust axiom.
The substantive semantic proof remains independent of that project axiom in
`AlphaEqvCode` and consumes the local-soundness premise explicitly.
-/
theorem trustedAlphaEqvSoundAt_of_local_terminal_sound
    (localSound : Local.Accepts left right →
      TerminalCodeRelated ({} : FVarIdMap Lean.FVarId) scope scope left right) :
    Fir.LeanIR.Passes.SimpCase.AlphaEqvSoundAt externals state left right :=
  alphaEqvSoundAt_of_local_terminal_sound lean432UpstreamBridge localSound

/-- End-to-end compiler-facing soundness for the return-code slice. -/
theorem trustedReturnAlphaEqvSoundAt
    (scope : List Lean.FVarId) (leftId rightId : Lean.FVarId)
    (leftScoped : scope.contains leftId = true)
    (rightScoped : scope.contains rightId = true) :
    Fir.LeanIR.Passes.SimpCase.AlphaEqvSoundAt externals state
      ((.return leftId : LCNF.Code .impure)) (.return rightId) :=
  trustedAlphaEqvSoundAt_of_local_terminal_sound
    (terminalCodeRelated_of_local_return leftScoped rightScoped)

end Fir.LeanIR.Passes.AlphaEqv
