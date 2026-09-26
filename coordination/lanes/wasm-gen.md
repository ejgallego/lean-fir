# wasm-gen lane

Checked structural final-LCNF source boundary for `ROOT-W7-20260925-001`.
Root remains integration owner; W6 owns the initializer proof downstream.

```text
lane: wasm-gen
owner: fir/wasm-gen
branch: wasm/lcnf-reification-434
worktree: .worktrees/wasm-lcnf-reification-434
state: ready
base: 97c257cc4e0ed815daedf47a5161bd0c958f63a0
functional-head: 249f476d5c4b9f3bc08781a0fc9542d87f4f8b4d
contract-base: 97c257cc4e0ed815daedf47a5161bd0c958f63a0
clean-at-update: true
slice: Kernel-checked ImpureProgram definition, exact structural readback, initializer equations, and production lowering of that same checked program.
files: Fir/Compiler/LCNF/{Structural,Reify,ReifyExamples}.lean; README and retained-example templates; this snapshot
contracts: none; production capture-interface addition only, under root's narrow lease
checks: On functional head 249f476d5, Beam and fresh batch codec/corpus checks pass; focused 7-job cone passes; retained source 65-job build and fresh-process import pass; git diff --check, make check, make talos-setup, make talos-check and bash integration/talos/artifact/check.sh pass. This snapshot is documentation-only. No fresh browser campaign claimed.
bug-cards: none
blockers: none for the nominated Stored entry. Original diagnostic's unrelated Level1/Entry imports hit RC2 kernel recursion in Zip.Native.DeflateParse:361,367; unchanged real Stored owning-module capture passes.
handoff: Exact clean containing checkpoint is pinned by the canonical completion. Root reviews/lands; no main advance, push, package publication or W6 implementation by W7.
next: W6 consumes RetainedRC2.program and initializer.findDecl/body; root serializes integration against newer main.
```

The authenticated source commits remain lean-zip `273d0d6c` and zip-common
`4425bab1`; no source file was ported or patched. Official Lean is 4.34.0-rc2,
commit `6a10ac8c`. The historical 4.33 olean remains evidence only.

The new source artifact is under `.deps/retained-rc2/` in this worktree.
`RetainedRC2.program` contains 21 declarations/14 externals. Its generated
lookup equation inherits only standard `propext`; its concrete definition and
initializer-body equation use no axioms. Fresh-process structural readback is
checked without recapture. Production lowering uses that readback, not the
transient capture or a printed/copied initializer.

Ordinary/closed Wasm: 1,983 bytes each. Resident: 13,236 bytes, zero imports,
zero remaining runtime operations; V8 validates its module-owned memory.
All three byte sequences match the historical diagnostic, without claiming
cross-version AST/proof identity or a new runtime-refinement theorem.

Reproduction, exact source/setup/output digests and limitations are in
`Fir/Compiler/LCNF/README.md` (SHA-256
`505d488f624a112805d04efba1cce95a05bc5af65c0eb4ccbc6a0be470f9ada1`).
