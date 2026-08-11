# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2d24f623 on main
functional-head: 56a3e15d (source-only pointwise admission, direct-let preservation, and return classification)
contract-base: 2d24f623; accepted pointwise control/resource stack and current compiler/runtime contracts
clean-at-update: true
slice: Added `ConcreteStructuredCodeAdmission`, a source-only structural coverage judgment containing supported direct operations, deterministic fact/budget transfer, continuation coverage, and return ABI compatibility, but no runtime step, endpoint, target path, or evaluation derivation. Added `ConcreteStructuredCodePointwiseRel` combining the actual compiler focus, hereditary resource stack, and that admission under the generated-function spec. Proved canonical root construction, complete direct-value successor preservation through the production runtime law, and return classification into terminal/direct-bind/saturated-bind control from a supplied successful source step.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: post-rebase `lean-beam update/sync/save FirTalos/ConcreteStructuredSimulation.lean` (0 errors, 1 existing warning); `lake -d integration/talos build FirTalos.ConcreteStructuredSimulation` (3110 jobs); `git diff --check`; `make check` (122 unit tests plus native/LCNF validation and Wasm validation checks); `make talos-setup` (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); `make talos-check` (3133 jobs); all passed
bug-cards: none
blockers: none
handoff: ready for integration; branch rebased on 2d24f623 and clean before this mailbox update
next: Carry source-only continuation admission through direct/saturated call push and bind pop, then widen the pointwise `advance` dispatcher to the already proved external, lazy, case, persistent/ordinary effect, and ranked zero-target-step families.
```
