import Fir.LeanIR.Passes.AlphaEqvCode

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
Compiler-facing terminal soundness using the single Lean-4.32 trust axiom.
The substantive semantic proof remains in the axiom-free `AlphaEqvCode`
module and consumes the local-soundness premise explicitly.
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
