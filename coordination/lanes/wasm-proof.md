# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8d97e6bd on main; includes the accepted validation argument-alias contract and all prior W6 pointwise slices
functional-head: 5bcc92bd
contract-base: 8d97e6bd; consumes the accepted structured-Wasm/compiler, source-semantics, concrete runtime, generated-call, resident-runtime, and validation contracts without changing a shared semantic or executable ABI contract
clean-at-update: true
slice: W6.7e arbitrary normalized case-table pointwise closure. ConcreteStructuredCodeStepAdmission replaces the singleton-only branch with source/compiler-only ObjectConstructorCasesSupported and ScalarUInt8CasesSupported branches. A successful current source step determines the actual selected arm; admission retains no branch choice, source execution, target path, or future certificate. The existing arbitrary chain theorems now expose both the exact selected prefix and the only zero-test shape. Object tables execute 5 * testCount structured steps through getTag/tag comparisons; scalar UInt8 tables execute 4 * testCount resident local/constant comparisons. Each test adds one target-only case-label layer to the suspended resource and supported-frame stacks. Both local and strong supported-global dispatchers preserve the module-stable relation for arbitrary first hits, later hits, and defaults, including nested calls and return-pop through all retained labels. If testCount is zero, the compiler-derived chain is proved default-only and the established compiler-silence rank decreases, closing the weak-simulation side condition constructively. The roadmap now identifies lazy/cache control as the next pointwise family.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, coordination/lanes/wasm-proof.md
contracts: none; proof-side arbitrary case admission, selected-arm recovery, exact variable-length prefixes, zero-test rank evidence, dispatcher coverage, and roadmap clarification only
checks: coherent proof checkpoint rebased cleanly from bb3172e5 onto main 8d97e6bd after the validation-only argument-alias integration; Lean Beam update/sync/save PASS before and after rebase with zero errors and save-ready module, source hash cbf737c76a3fc6c3; direct lake build FirTalos.ConcreteResumableWasm PASS before and after rebase (3120 jobs); git diff --check PASS before and after rebase; make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make check PASS on 8d97e6bd (123 harness tests, 661/661 native-LCNF, 9/9 direct-machine, 661-case native/LCNF/V8 triangle, 670 unique cases, 1992/1992 comparisons, 7176 machine steps, zero findings, 162 active bug cards, Lean 4.33 trusted-assumption gate); make talos-check PASS on 8d97e6bd (3143 jobs, including modified proof and ConcreteResumableWasm import cone)
bug-cards: none
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main 8d97e6bd through functional head 5bcc92bd and this mailbox commit; no shared contract changed
next: add generated lazy-cache hit and non-heap miss protocols to the pointwise relation, then close remaining production current-step coverage and canonical root construction
```
