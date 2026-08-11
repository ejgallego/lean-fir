# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3e362ba0 on main
functional-head: dd375d94
contract-base: 3e362ba0; consumes accepted W6.7d terminal adequacy and the accepted W6.7e compiler-focus, silent-ownership, and positive return-path slices over the generated structured machine and concrete runtime refinements
clean-at-update: true
slice: Added a precise structured bind/call-frame relation. A yielded source bind frame now corresponds to a returning structured target with a one-result call frame whose residual code writes the result local. The restoration theorem matches the source bind-resume step by exactly two target steps (returnCall, then localSet), restores the caller operand tail, and re-establishes ConcreteStructuredCodeFocus for the continuation. Strengthened code/yield focus with ConcreteLocalFrameAligned so the proof records that compiler-assigned destination locals are writable rather than assuming it. Added the deterministic wrapper from a generic successful source-step premise.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: Lean Beam update/sync/save (0 errors, 0 warnings); lake build FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteResumableWasm (3107 jobs, pass); git diff --check (pass); no sorry/admit in changed proof files; make check (pass: 642 cases, 1844/1844 comparisons, 124 active bug cards); make talos-setup (pass, Talos a01d01c); make talos-check (pass, 3133 jobs)
bug-cards: none
blockers: none
handoff: ready for integration; base 3e362ba0, active mailbox commit 6cbe5ec2, functional head dd375d94; worktree clean before this mailbox update
next: Prove that the compiled direct-call entry path establishes ConcreteStructuredBindFrameFocus, closing the call/return round trip. Then incorporate target-only label/loop administrative unwinding into the finite target path and proceed to apply/cache frames.
```
