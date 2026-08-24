# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: e367c3ce, current main after the accepted Nat shift caller fast path
functional-head: b9f96699
contract-base: e367c3ce; W7's exact resident Nat.add body and all checked-add helper signatures are consumed unchanged
clean-at-update: true
slice: The exact checked heap/heap Natural-add fallback is now one installed semantic theorem across the computed result-count split. `CheckedNaturalAddPost` is a branch-neutral existential simulation post that retains the resulting concrete heap and memory, witness extension and closure-allocation persistence, the exact semantic `Nat` literal/reference, and its typed returned Wasm word. `NaturalSumWriterInstallation.wp_checkedNatAddFallbackProgram_of_installedAdmissions` constructs the installed validation/count/carry prefix, splits on the actual computed result count, invokes the installed scalar one-limb theorem or allocator/writer multi-limb theorem, and proves that both physical producers establish this common post. Its branch premises expose genuine producer executions/allocation resources; no compiler certificate is introduced.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, semantic ABI, concrete runtime operation, helper signature, symbolic Wasm surface, emitter, ownership behavior, or layout changed. `CheckedNaturalAddPost` and the unified theorem are proof-side abstractions over the existing concrete runtime and exact installed resident functions.
checks: Branch remains based on current main e367c3ce and is 0 commits behind. `git diff --check` passed. Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentNat.lean (source hash 30c0cc70604bf0bd). Independent batch `lake build +FirTalos.ConcreteResidentNat` passed all 3,123 jobs. `make check` passed with 721 unique cases, 2,145/2,145 comparisons equal, zero findings, 194 active bug cards, and 25 mailbox tests. `make talos-setup` selected Talos 0e05edbc and `make talos-check` passed all 3,172 jobs.
bug-cards: none
blockers: none
handoff: Integration may land functional head b9f96699. W7 may consume `CheckedNaturalAddPost` and `NaturalSumWriterInstallation.wp_checkedNatAddFallbackProgram_of_installedAdmissions` as the single typed refinement boundary for the exact checked heap/heap fallback. The theorem covers the actual installed prefix and both generated result branches while keeping real producer resources explicit.
next: Lift the unified checked heap/heap theorem through the outer immediate/heap representation dispatcher and the actual adapted `natAddFunction` call. First factor common producer-resource packaging so the function-level theorem does not repeat scalar-constructor and allocator capacity plumbing. Treat immediate/immediate, heap/heap, and promoted tagged/heap combinations as explicit admission arms rather than weakening canonical heap admission.
```
