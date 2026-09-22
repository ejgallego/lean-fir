# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 6207996f3db181b3f1b53467efd8e63f587c25e2
functional-head: c9bb8add957e1c4abcfdb5dee8e25b22458ca3ed
contract-base: 6207996f3db181b3f1b53467efd8e63f587c25e2
clean-at-update: true
slice: Factor complete suspended caller cache-frame restoration through facts-aware binding transport, and reuse it in the existing structured direct-call restoration proof.
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteLazyPublicationTests.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: No shared contract changed. ConcreteReuseCapacityCacheFrame.restoreCaller_of_retainedTransport needs only the exact caller's ordinary binding transport, while retaining checked representation/local-update and witness/capacity premises plus the callee's budget, implementation laws, descriptors, cache globals and closure tables. restoreDirectCaller delegates its base-frame construction; its signature and historical all-location entry premise remain unchanged.
checks: Actual-module Beam update/sync/save passes. Beam stopped; clean FirTalos library plus focused proof/test/TrustAudit build passes (3181 jobs). Fresh direct Lean on cache correctness, structured simulation and regression modules passes. make check and make talos-check including compiled/source trust audit pass. git diff --check passes. Exact containing-checkpoint refresh is recorded in canonical handoff.
trust: 212 maintained endpoints. New full-frame restoration and refactored restoreDirectCaller depend exactly on propext/Quot.sound; twoPublications_restoreCallerFrame uses standard3. No new generated dependency or semantic axiom; existing executable endpoint native debt is unchanged.
regressions: Concrete two-publication source transport discharges ordinary binding at the complete cache-frame consumer using the nonempty distinct caller-token map. Physical frames, witness/capacity and checked destination premises remain explicit: this is conditional frame evidence, not nested compiled-call execution. Existing non-vacuous ordinary-token witness and alias rejection remain.
bug-cards: none new. FIR-BUG-wasm-none-reuse-retained-token-ordinary and FIR-BUG-wasm-none-endpoint-native-axiom-audit remain separate open debt.
blockers: None for this consumer-factoring slice. It does not close the strategy review's W1 gate: actual historical stack pops still require blanket ordinaryness. Ownership-derived disjointness and a facts-aware historical stack remain required before object/tobject miss admission. This is not PA3, a lean-zip application theorem, resident linking or encoded bytes.
handoff: Standing fir/root claimed bounded review on W6-ROOT-20260922-037 via ROOT-W6-20260922-038; clean local-only checkpoint requested. Exact containing checkpoint is recorded in canonical handoff. No main/board/W7 edit.
next: Coordinate the minimal historical-stack boundary retaining each suspended caller's own facts/environment and derive publication disjointness from ownership; use the factored restoration lemma at pop, not another equivalent wrapper. Separately ROOT-W6-20260922-021 awaits structural reification/same-input lowering evidence for the exact retained Stored.olean. No substitute capture, historical LCNF, new native axiom or frontend framework is folded into this slice.
```
