# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: fb18c01fca80a6068f159e9387fecfcef5eb7cde on main
functional-head: f215c995c0f06ef6097d12cd642c342da51b80b7
contract-base: b6030300 on this branch retains the existing phase-level Program.NamesUnique fact in the proof-owned ConcreteSupportedExport boundary; otherwise consumes main at fb18c01f plus the accepted source interpreter, adapter, concrete-runtime, cache, closure-table, and declaration-correctness contracts
clean-at-update: true
slice: Retain source declaration-name uniqueness at the concrete compiler-correctness boundary; derive exact generated named-call indices from the executable lower/adapt pipeline; and make the production call implementation consume correctness of its nested finite hereditary source derivation rather than an opaque module theorem or target certificate
files: integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-supported-export-declaration-name-uniqueness.md; this mailbox
contracts: proof-only static boundary ConcreteSupportedExport now retains the phase's existing Program.NamesUnique fact; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed; the preferred call law contains no target program, store, witness, execution, numeric-index premise, or translation certificate
checks: PASS Lean Beam update/sync/save/refresh for FirTalos/ConcreteReuseCapacityCacheCorrectness.lean (zero errors; 10 pre-existing/style warnings) and FirTalos/ConcreteCompilerCorrectnessContract.lean (zero errors, zero warnings); PASS make talos-setup after rebase (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); PASS git diff --check before and after rebase; PASS make check after rebase (122 interpreter-validator tests; 642 unique validation cases; 1844/1844 comparisons equal; zero findings; 109 bug cards and trusted assumptions valid); PASS make talos-check after rebase (3125 jobs)
bug-cards: FIR-BUG-wasm-none-supported-export-declaration-name-uniqueness fixed at the compiler-correctness boundary
blockers: none
handoff: f215c995c0f06ef6097d12cd642c342da51b80b7 is the clean green W6 functional head based directly on current main at fb18c01f; direct named calls now reconstruct their exact generated callee, numeric target, entry frame, and caller ABI refinement from production equations plus the nested finite source theorem
next: integration owner lands this ready slice; W6 then proves DirectHereditaryGeneratedDeclarationInduction by structural induction from uniform generated-row operation laws, replaces the remaining compatibility DirectInternalCallDeclarationInduction in the root theorem, and only afterward adds saturated-closure and lazy-miss constructors
```
