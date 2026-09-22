# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 17510a05343344a778532a907b75f80d1f027756
functional-head: 3a3fd0c4fae91e897708e18ee0ac852f05bc33cd
contract-base: 17510a05343344a778532a907b75f80d1f027756
clean-at-update: true
slice: Preserve a fixed suspended caller's retained-token facts through callee prefixes, heap-cache publication and result binding, without all-location ordinaryness.
files: integration/talos/FirTalos/ConcreteLazyPublication.lean; integration/talos/FirTalos/ConcreteLazyPublicationTests.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: No shared contract changed. New proof-local ReuseTokenOrdinaryTransport fixes caller facts/environment; ordinary-prefix compatibility and publication from existing graph disjointness feed trans/eraseBind/precomposeRetained. The earlier precompose delegates to this boundary. Central declaration/stack relations, admission exclusions, runtime, ABI and checker unchanged.
checks: Actual-module Beam update/sync/save passes; one stale-import barrier recovered by refresh. Beam stopped; clean FirTalos library plus focused proof/test/TrustAudit build passes (3181 jobs). Fresh direct Lean on both modules and exact printed axioms pass. make check and make talos-check including compiled/source trust audit pass. git diff --check passes. Exact containing-checkpoint gate refresh is recorded in canonical handoff.
trust: 209 maintained endpoints. Four new composition/compatibility laws are axiom-free; publication and three regressions use standard3; eraseBind uses propext/Quot.sound. No new generated dependency or semantic axiom.
regressions: A real heap publication refutes all-location transport but preserves a nonempty distinct caller token frame. Two caches publish the same heap root; precomposeRetained and trans/eraseBind preserve that frame and establish its postcondition from a concrete ordinary initial state. Existing alias rejection remains.
bug-cards: none new. FIR-BUG-wasm-none-reuse-retained-token-ordinary and FIR-BUG-wasm-none-endpoint-native-axiom-audit remain separate open debt.
blockers: None for this helper slice. Arbitrary-caller publication disjointness and facts-aware structured-stack wiring remain required before object/tobject miss admission. This is not PA3, a lean-zip application theorem, resident linking or encoded bytes.
handoff: Standing fir/root claimed bounded review on W6-ROOT-20260922-031. Exact immutable containing checkpoint, clean state and authorized ejgallego publication are recorded in canonical handoff. No main/board/W7 edit.
next: Connect fixed-caller transport to suspended frames without weakening existing ownership obligations. Separately ROOT-W6-20260922-021 awaits root-coordinated structural reification/same-input lowering boundary for exact retained Stored.olean; import succeeds but no kernel program constant is exposed. No substitute capture, historical LCNF or new native axiom.
```
