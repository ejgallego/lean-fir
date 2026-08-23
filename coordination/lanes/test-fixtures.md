# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 837e760135e1ba3952177c2e4b7107e561b4df7c on main
functional-head: a9ced6ff0686f1f2da157c25ff789dd91cb45ff2, validate cached repeated-child String DAG ownership against native Lean, LCNF, and V8
contract-base: 837e760135e1ba3952177c2e4b7107e561b4df7c on main; consumes the accepted cache/persistence semantics, deterministic semantic-Wasm product publication, real-V8 surface, and direct ByteArray-size closure; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S13/E3b cached shared-DAG alias fidelity: add taken/skipped native-oracle cases for one cached owner whose two fields share the same String child, retain an independent alias outside the owner, optionally append through the sibling, call the nullary cache again, and observe both original fields, the outside alias, the result, and the second cached owner. Pin exact ordered LCNF form traces and counts: both paths execute two projections, six increments, four constructors, the cache miss/hit sequence, and the taken path alone executes one append
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; coordination/lanes/test-fixtures.md
contracts: none. The fixture lane changes only corpus cases, observations, exact telemetry, and coverage requirements; no interpreter, semantic-Wasm, concrete-runtime, proof, generator, or artifact contract changed
checks: PASS lean-beam update/sync/save Fir/Validation/Corpus.lean (zero diagnostics); PASS focused native-lcnf.json for cached-shared-string-dag-reuse-{skipped,taken} (2/2 equal); PASS focused native-lcnf-v8-scalars.json (6/6 directed comparisons equal, four semantic-Wasm products opened with strace); PASS git diff --check; PASS TMPDIR=.deps/tmp make check after rebase (706/706 native->LCNF, 1412/1412 native/LCNF->V8, 2127/2127 aggregate comparisons, 265/265 semantic domains, zero findings); PASS TMPDIR=.deps/tmp make talos-check (3171 jobs)
bug-cards: FIR-BUG-impure-none-cached-heap-persistence and FIR-BUG-wasm-none-validation-product-cold-publication are accepted fixed history; none new
blockers: none
handoff: integration may land the clean validation/closure-ownership-fixtures branch through functional-head a9ced6ff; the containing branch head also publishes this ready mailbox. The slice is fixture-only and dependency-independent of active W6/W7 work
next: after integration, assess E3c as a cached repeated-child ByteArray taken/skipped mutation pair; if its protocol cone is no longer small, prefer cache reuse across one already-controlled effect boundary
```
