# Consumer recipe cleanup audit

First slice, 2026-09-16, FIR main `9a050b8eb`. **No deletion is justified by
this inspection.** Absence from VIR's catalog is not absence of client use;
an older backend or source pin can still be a unique oracle/regression boundary.
This is a cleanup decision aid, not a package acceptance or run registry.

## Evidence boundary

Read-only inspection covered FIR recipes, package policies, smokes and history;
VIR `benchmarks/browser/artifact-builds.json`, example controllers/test plans and
`tests/browser/benchmark-pages.mjs`; and the named owning client views:

- VIR root `151538c6`; catalog last changed at `57c95a21` (2026-09-07).
  The checkout has unrelated local edits; its catalog is tracked and unchanged.
  Inspected catalog SHA256:
  `8fb571d4f8aabe2f808e888318647019f7213eba05f451c9f79c862cce21bb07`.
- Illuminate `.worktrees/vir-hit-scene`, `060d7103`, and its `scripts/` staging,
  acceptance and trace tests. FIR's player source pin is separately `6f16cdc3`.
- lean-zip `.worktrees/vir-fir-wasm-port`, clean `e43a0dec`; `bench/catalog`,
  `bench/web`, `bench/fir-native` and `bench/fir-c`.
- VersoSlides source-owner files at pinned `eb8d2b8f`, inspected with `git show`,
  including `demos/vir-pretty/scripts/stage-artifacts.sh` and
  `browser-tests/test_pretty_artifact_contract.py`. The old local path
  `.worktrees/vir-pretty-prototype` no longer exists; that is not retirement
  evidence for the recipes retained in Git.
- VBP `.worktrees/browser-pr188`, `bb25d035`; its component campaign scripts
  have local edits. Historical/current distinctions come from tracked
  `doc/performance/FIR_PREVIEW_BASELINE.md`, not an inferred live adoption.
  Inspected `component_campaign_smoke.mjs` SHA256:
  `6ca5d14e05ede5b6ab2206dfc1b40a3d469a03e7e69bd4d6d0cc608948fd9ba9`.
- Verso `.worktrees/vir-search-full-lean`, `c52c55ee`, plus FIR search worktrees
  identified by `git worktree list`. Directory parent names do not identify
  the producer repository.

Paths below are FIR-relative unless prefixed by VIR/client. Revisions identify
reviewed recipes/source pins, **not** fresh acceptance replays. Last-change
dates are `git log -1` for each recipe directory (PrettyTrace includes its
producer entry/gate); shared fixes can touch several
recipes without establishing a new consumer campaign.

## Classification and action

**A**: referenced campaign/client consumer, keep (branch-only is labeled).
**U**: unique semantic/oracle/regression boundary, keep even without catalog use.
**P**: provisional/branch-only experiment without a confirmed current external
consumer, park with an owner question. **O** requires no remaining scripts,
pins, tests, docs or owner dependency; no inspected recipe meets that threshold.

| Recipe | Class / evidence | Pin and last relevant change | Action / owner |
| --- | --- | --- | --- |
| Native PrettyTrace | A: VIR catalog `prettyM.components.native`, `examples/prettyM/tests.json`, `backends/pretty-native.js`; FIR artifact gate | Catalog FIR `298682a7`; producer/gate `422caea96`, 2026-09-15 | Keep; wasm-gen + VIR benchmark owner |
| PrettyTrace C/LLVM/Emscripten | A/U: catalog `prettyM.components.llvm`, `pretty-llvm.js`; full Lean runtime backend, not resident Wasm | Catalog same FIR pin; `integration/lcnf-c-wasm` `1155ba6db`, 2026-08-22 | Keep alternative oracle; root/backend owner |
| Verso Flat | A/U: source-owner `stage-artifacts.sh`, Flat contract validator and browser contract tests; FIR `check-flat.mjs` tagged UTF-8/native differentials; no VIR catalog entry | `verso-source.json` `eb8d2b8f`; recipe `8199b6d74`, 2026-08-14 | Keep text/event boundary; VersoSlides + wasm-gen |
| Verso complete HTML | A/U: same source-owner staging, separate HTML validator; tests reject Flat/PrettyTrace semantics; FIR `check-html.mjs` | Source `eb8d2b8f`; recipe `894aff627`, 2026-09-02 | Keep escaping/tag/HTML oracle; VersoSlides + wasm-gen |
| Illuminate full-action native player | A/U: client `stage-native-player.sh`, `test-player-traces.mjs`; FIR `export-v3-package.sh` and full-action/selection comparison; absent from current VIR catalog | Source `6f16cdc3`; recipe `daadd67de`, 2026-08-22 | Keep full FrameAction oracle; Illuminate + wasm-gen |
| Illuminate native selection player | A: catalog `illuminate.components.selection`, controller/app and quick-parity plan; client `stage-fir-live-player.sh` | Catalog FIR `1b1668f1`, source `6f16cdc3`; same recipe history | Keep compact production/diagnostic paths; Illuminate + VIR benchmark owner |
| Illuminate selection LLVM | A/U: client `stage-llvm-player.sh`, optional LLVM branch in trace tests; FIR `integration/illuminate-player-llvm/check.sh`; no catalog component | Source `6f16cdc3`; recipe `66c325df2`, 2026-08-26 | Keep full Lean runtime control; Illuminate + backend owner |
| Illuminate linear HitScene | A/U: client `stage-fir-hit-scene.sh`, `accept-fir-hit-scene.sh`; prepared-query native differentials; no VIR catalog entry | Source `88dcfee8`, v2 layout; recipe `daadd67de`, 2026-08-22 | Keep linear/reference query boundary; Illuminate + wasm-gen |
| Illuminate SpatialHitScene | A/U: client `stage-fir-spatial-hit-scene.sh`, `test-fir-spatial-hit-scene-package.mjs`, performance staging; separate spatial representation | Source `3b912826`; recipe `3ba58f873`, 2026-08-20 | Keep spatial/linear comparison; Illuminate + wasm-gen |
| lean-zip stored | U: `integration/lean-zip/package.mjs`, `smoke.mjs`, `package-smoke.mjs`; minimal packed ByteArray/stored-block oracle; not the catalog's raw dispatcher | Client `273d0d6c`, common `4425bab1`; recipe `ebd91d020`, 2026-08-31 | Keep minimal control; lean-zip + wasm-gen |
| lean-zip Level-1 | U: same publisher, `level1-smoke.mjs`, `level1-package-smoke.mjs`, reviewed closure contract; first matcher/emitter boundary | Same source pins/history | Keep focused matcher control; lean-zip + wasm-gen |
| lean-zip raw resident | A: catalog `lean-zip.components.fir-native`, browser-parity plan; client catalog controller/profile workload; `export-raw-package.mjs` | Catalog FIR `b9f6adb4`; source pins above; same recipe history | Keep production levels 1–10; lean-zip + VIR benchmark owner |
| lean-zip C/Emscripten and VIR | A/U: catalog `fir-emscripten` and `vir`, client `bench/fir-c/package.mjs` and catalog smoke; distinct compiler/runtime routes | Catalog VIR `6259590a`, FIR `b9f6adb4`; client `273d0d6c` | Keep independent full-runtime oracles; lean-zip + VIR/backend owners |
| VBP old mount/unmount viewer | U: exact 41-host-operation `package-policy.mjs`, `check.sh`, callback borrow/erased-dispatch bug regressions; VBP baseline doc explicitly preserves it as historical, not current parity | VBP `cad90a2f`, VIR `90aa3f49`; recipe `a9a0c56d9`, 2026-09-09; accepted producer `8848d822` | Keep frozen gate/output; ask VBP performance + wasm-gen whether any current client still invokes mount/unmount |
| VBP current renderer / none factory | A, branch-only: VBP `json_renderer_smoke.mjs`, `component_campaign_smoke.mjs` and SSR/Chromium entry; real factory is not old imperative widget | Qualified baseline `c560f6a4`, source closure `2c1ef0f6`; adapter successor `15fae0eb` / `59ccf4f98`, 2026-09-16 | Keep baseline and candidate distinct; VBP + wasm-gen; no full 4.34 migration/live adoption claim |
| VBP manifest resolver | U: separate zero-import String→String policy, `check.sh`, malformed/Unicode/rewind smokes; owner acceptance `VBP-FIR-20260909-001`; no catalog/live staging found in inspected VBP view | VBP `1af64db2`; recipe `3c2b6e6c7`, 2026-09-01; accepted producer `0eeacb2c` | Keep portable resolver gate; ask VBP performance where the accepted provider is currently staged |
| Verso search scalar factor | A, branch-only: client `experiments/vir-search/stage-fir-assets.mjs`, `benchmark.mjs`, `static-web/search/fir-search.js` and provider; client `FIR.md` explicitly selects scalar cache boundary | Verso `88f71dc9`; FIR `834aa522e`, 2026-08-12, branch `perf/verso-search-qsort` | Keep consumed experimental package; Verso search owner + wasm-gen; not on FIR main/catalog |
| Verso search earlier full/bulk/packed | P, with historical/control value: branch smokes/policies and client `FIR.md` comparison remain; no confirmed current client selects these older ABIs | FIR `d5648cf84` (2026-08-11), `2ffc5c219` / `5db70cf6a` (2026-08-12); Verso `e465741e` / `adc0368f` / `0f46ae0b` | Park, preserve evidence; ask Verso search owner which are still differential controls before proposing recipe removal |

## Generated pointer and policy check

Read-only `readlink`/existence inspection in `.worktrees/wasm-generation` found
resolving pointers for PrettyTrace, Flat/HTML, both native players, both
HitScenes, stored/Level-1/raw zip, old viewer and resolver. The Emscripten
PrettyTrace pointer was absent in that worktree despite its explicit catalog
consumer: absence of build state does not retire its recipe.

The old viewer pointer still selects producer `8848d822` and resolver `0eeacb2c`;
owner closures explicitly accepted/preserved these identities. Flat's generated
pointer selects source `3dbc9ef4`, while the tracked recipe now pins `eb8d2b8f`;
HTML's pointer selects `eb8d2b8f`. Both BUILD files say `provisional: false`.
That is **identity drift to resolve with the selected consumer**, not permission
to advance/remove a pointer or claim the old Flat package matches today's pin.

FIR search full/bulk/scalar pointers resolve in their respective feature
worktrees; packed has no pointer. The scalar client selects package
`e3f914cf…` / Wasm `081a930a…`, not the full ranker's `rankCandidates` ABI.
Policies/setup pins and package-local BUILD remain authoritative. Current VBP
none-factory packages intentionally have no canonical pointer; the immutable
baseline and v2 candidate are retained separately. Root cancelled their
exact-main rebase because main lacks the official-4.34 baseline; a package-only
candidate is not a main-based producer recipe or acceptance of the whole stack.

## Removal list for root review

**Proposed recipe/file/pointer removals: none in this slice.** In particular,
do not remove `integration/vbp-verso-viewer/`, `integration/vbp-manifest-resolver/`,
stored/Level-1 zip recipes, formatting controls, or their `_build/*-current`
outputs. Remaining tests, accepted owner contracts or historical comparisons
prevent an “obsolete” classification.

Next bounded decisions, without deleting anything:

1. Verso search owner: identify the earlier full/bulk/packed controls still
   needed; only owner-confirmed unused recipes, after tracing their docs/tests,
   can become an explicit file/pointer removal proposal for root.
2. VBP performance owner: confirm old viewer live-use status and resolver
   staging location. Historical/unique gates remain keep items regardless.
3. VersoSlides owner: name the immutable Flat package actually used by the
   current campaign before resolving generated-pointer/source-pin drift.

No current consumer was executed or repinned, no ABI/runtime changed, and no
outputs, worktrees, branches, ignored evidence or cross-project files were
removed. This report narrows the questions; it does not authorize removal.
