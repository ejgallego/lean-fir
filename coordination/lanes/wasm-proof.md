# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 1121f917
functional-head: b91cf8d1
contract-base: 1121f917
clean-at-update: true
slice: Five terminal-extraction lemmas identify successful source completion, invert the existing validated global relation, and recover its yielded-value and checked-frame evidence automatically. Function/export corollaries connect that evidence to actual Wasm.run return refinement. The represented kind is existential; precise root-result provenance and finite-prefix assembly are explicitly separate. This is a successor to immutable reviewed checkpoint 3fc74692, not part of that pending integration.
files: integration/talos/FirTalos/ConcreteTerminalExtraction.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/FirTalos/TrustAudit.lean; integration/talos/FirTalos.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: none changed. No source/target relation, compiler-admission predicate, runtime behavior, ABI, W7 file, root gate, or resource contract changed. Successful final observations are derived from unframed yields; a staged external result is excluded by its pending bind frame. All five new lemmas have exactly propext, Classical.choice, and Quot.sound, with no generated dependencies. Existing trust debt is unchanged.
checks: Lean Beam update/sync/save of ConcreteTerminalExtraction and TrustInventory pass; extraction has zero diagnostics. TrustAudit hit a stale-import barrier, then refresh passed with 29 inventory messages and zero errors; the incomplete barrier was not counted as success. Beam stopped; lake -d integration/talos clean FirTalos followed by make talos-check passed (3201 jobs, 238 maintained source files, 3163-job audit cone, forced 29-endpoint audit). Forced direct lake env lean FirTalos/ConcreteTerminalExtraction.lean from integration/talos passed; an initial invocation from the root had a path-resolution error and is not counted. make check passed: 730 cases, 2172/2172 comparisons, expanded source/hash/trust gates, six negative trust tests, bug-card checks and 38 mailbox tests. git diff --check passed. git rebase main reports up to date at accepted main 1121f917. Setup, manifests and toolchain retained unchanged from the validated predecessor. Exact containing-head Talos receipt is published in the canonical handoff after final verification, avoiding receipt/commit self-reference.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains confirmed with unchanged existing debt
blockers: none for this slice. Precise root result-kind provenance, finite-prefix assembly, compiler-derived admission closure, and trap-aware structured semantics remain open; no closed compiler theorem is claimed.
handoff: ready independent successor based on reviewed 3fc74692, itself based on accepted main 1121f917. Prior immutable checkpoint remains separately consumed by W6-ROOT-20260909-004; the new canonical handoff pins this containing ready commit. No cleanup or later proof work is included. Local-only; no main update or remote push by W6.
next: Recover or retain the root export's selected result ABI and compose the simulation-produced finite target prefix with terminatesWith_of_validatedReturn. Preserve common finite-prefix composition and explicit runtime/resource contracts. Do not turn the existential kind or internal target prefix into a client provenance/certificate premise. Coordinate trap semantics separately.
```
