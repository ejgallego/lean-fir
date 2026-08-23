# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: in-progress
base: 63204d2e, current main after sparse constructor initialization
functional-head: cd4f6689
contract-base: 63204d2e; W7's exact resident Nat.add body and all resident Natural helper signatures are consumed unchanged
clean-at-update: true
slice: Canonical validator admission now proves exact completed base-2^64 addition words and closes the generated multi-limb typed producer without a caller certificate. The whole compiler-emitted checked fallback is named and adapts exactly: validated prefix, result-count dispatch, one-limb typed producer, and allocation/writer typed producer. `CheckedNatAddPrefixExecution` factors the seven local updates and five ordered helper calls, proves preservation of operand/flavor/count/carry/scratch locals, and composes both result cases. Admission-driven multi-limb and concrete-allocation one-limb theorems now conclude typed WPs for this exact fallback.
files: Fir/Wasm/Concrete/NaturalAllocationCorrectness.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, semantic ABI, concrete runtime operation, helper signature, symbolic Wasm surface, emitter, ownership behavior, or layout changed. The proof now targets W7's exact checked fallback rather than existential source/target fragments. The reusable prefix execution record is proof-side only.
checks: Rebased the ten-commit W6 stack without conflict from 837e7601 onto current main 63204d2e. `git diff --check main...HEAD` passed. Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentNat.lean (latest pre-rebase source hash a2b6c46cdd3ef96f). Forced `lake build FirTalos.ConcreteResidentNat` passed all 3,122 jobs. Post-rebase `make check` passed with 713 unique cases, 2,121/2,121 comparisons equal, zero findings, 193 active bug cards, and 25 mailbox tests. `make talos-setup` selected Talos 0e05edbc and post-rebase `make talos-check` passed all 3,172 jobs.
bug-cards: none
blockers: none; the remaining public theorem boundary is explicit below
handoff: W7 may consume `instructions_natAddFunctionBody_exact`, `adaptedNatAddFunction_body_exact`, `NaturalSumWriterInstallation.wp_checkedNatAddFallbackProgram_multi_of_admissions`, and `wp_checkedNatAddFallbackProgram_one_of_concreteAllocation` at functional head cd4f6689. This is an in-progress proof checkpoint, not yet a claim that every checked-input representation is covered by one function-level theorem.
next: Construct `CheckedNatAddPrefixExecution` from the actual installed `validateNatural`, `magnitudeCountNatural`, and `sumCarryFrom` executions plus the adapted function entry locals. For the heap/heap arm, derive exact counts and carry from `LiveHeapRel` validator admissions and discharge the remaining scalar result-count equality. Then lift the exact fallback WP through the outer representation dispatcher and actual adapted function call. Treat immediate/heap and promoted-tag combinations as their separate admission arms rather than weakening the heap theorem.
```
