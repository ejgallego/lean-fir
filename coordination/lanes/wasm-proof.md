# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7fa9097125999ad40f236779b8883a1059fbe5c2
functional-head: 83d7950eb1c00be94593c108855fb41ef7faf3f5
contract-base: 7fa9097125999ad40f236779b8883a1059fbe5c2
clean-at-update: true
slice: Compose compiler-selected initializer ordinaryness and facts-aware cache publication into complete lazy-miss retained-token transport, without non-heap result exclusions.
files: integration/talos/FirTalos/ConcreteLazyPublication.lean; integration/talos/FirTalos/ConcreteLazyPublicationTests.lean; integration/talos/FirTalos/TrustAudit.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: none changed. Compiler inversion selects the exact recursive callee. Its ordinary transport is precomposed with existing facts-aware publication at the exact semantic setGlobal post-state. Preferred theorem consumes existing publication-disjoint induction. No checker/runtime/ABI change, new source invariant, caller-chosen target path, or central relation redesign.
checks: Beam sync/save and exact print-axioms pass. Refreshed 200-endpoint audit passes. Beam stopped; lake -d integration/talos clean FirTalos and focused proof/test/TrustAudit batch build pass. Forced direct Lean on both new modules passes. make check and make talos-check, including forced compiled/source trust audit, pass. git diff --check passes. Containing-checkpoint rebase/checks are recorded in canonical handoff.
trust: precompose is axiom-free. Both complete-miss endpoints and three regressions use standard3; alias rejection uses propext and Quot.sound. Existing native-dependency inventories unchanged. No new axiom or trust approval.
regressions: Actual heap publication falsifies all-location ordinaryness. A nonempty distinct retained-token relation is established before publication and preserved through precompose/binding. An alias into the published root fails disjointness. These are source-semantic boundary tests, not an admitted application fixture.
bug-cards: none new. FIR-BUG-wasm-none-reuse-retained-token-ordinary and FIR-BUG-wasm-none-endpoint-native-axiom-audit remain open.
blockers: none for this bounded composition. Publication disjointness still needs ownership derivation; the structured all-location entry transport and object/tobject miss exclusion remain unchanged. Not PA3, resident linking, fault preservation, or encoded bytes.
handoff: Ready for standing fir/root under W6-ROOT-20260922-021. Clean immutable containing checkpoint and authorized ejgallego publication are recorded in its canonical handoff. No main/board/W7 edit.
next: ROOT-W6-20260922-021 nominates retained Zip.Wasm.compressStored olean and exact inventories, superseding the orphaned ROOT-LZ request. Inspect this input only after the current clean checkpoint; select one separate reusable W6 obligation or report the exact proof-boundary blocker. Olean/printed LCNF identity is not itself a kernel-referable program proof. Facts-aware suspended-stack transport and ByteArray/shared-runtime work remain separate.
```
