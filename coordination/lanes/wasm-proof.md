# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 207e4c1eba3db52747fc0b2f70a4f0ca15a3c432, accepted UInt64 generation stack on top of the checked resident-decrement contract
functional-head: eacfc3aa
contract-base: e8ca658b9228e5ea99768663a3eb949e192deafa, public ResidentRelease.checkedDecrementLocal and its production resident call sites
clean-at-update: true
slice: Proved exact production Array and opaque-release adaptation, replaced the installed decrement body's existential opaque branch with one exact constructor/closure/Array body theorem, and lifted the resident Array loop through DecrementOnceSuccess to a public installed-call refinement. Proved the W7 caller-local checked-decrement gate exactly: tagged and erased-zero no-op branches, the single heap-helper branch, heap classification arithmetic, complete well-formed tobject classification including promoted tags, exact erased admission, and preservation of the existing direct object path.
files: integration/talos/FirTalos/ConcreteResidentRelease.lean; coordination/lanes/wasm-proof.md
contracts: No shared semantic definition, ABI, layout constant, helper signature, emitter, symbolic Wasm instruction, or production artifact changed. The proof consumes W7 checkedDecrementLocal at e8ca658b. Heap branches are parameterized by and reuse the installed fir_dec_once TerminatesWith theorem; zero is admitted semantically only through ValueRel.erased, while well-formed ValueRel.tobject contains mapped heap references or tagged references and sends promoted tags through the heap helper.
checks: Lean Beam update/sync reported zero errors, zero warnings, and save-ready status for integration/talos/FirTalos/ConcreteResidentRelease.lean; targeted lake build FirTalos.ConcreteResidentRelease passed 3,080 jobs; git diff --check passed; make check passed with 719/719 native-LCNF-V8 cases, 9/9 direct-machine cases, 2,166/2,166 indexed comparisons equal, zero findings, 203 active bug cards, and 26 mailbox tests; make talos-setup fixed Talos at 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check passed all 3,172 jobs.
bug-cards: none
blockers: none; W7 may integrate both proof commits immediately
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and integrate the stack based at 207e4c1e through functional head eacfc3aa. The branch is clean, rebased on current main, and changes only the W6-owned proof consumer plus this single-writer mailbox.
next: After landing, rebase W6 on main and continue the unified installed-decrement/finite-trace proof. Per-function resident body proofs instantiate instructions_checkedDecrementLocal and ValueRel.wp_checkedDecrementLocalProgram_tobject; exact object lanes retain their already-proved direct heap path.
```
