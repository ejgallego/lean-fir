# wasm-gen lane

Current slice: `ROOT-W7-20260915-020`, clarified by root event `-021`.
Five installed-module inputs and seven renderer-frontier entry captures are
ready. Root owns integration; no recursive assembly or Wasm claim is made.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 854f8d1505d96721ae5252f94493b7b11e199e56
functional-head: 6afe2ef860091e8c9706fc671da4f66c0e363835
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Pinned-bootstrap-derived capture inputs for five installed Lean modules; verify source/options/artifact/import provenance, capture seven actual renderer-frontier entries twice, refresh the original frontier taxonomy.
files: integration/vbp-native-session-probe/{InstalledModuleCapture.lean,installed-module-inputs.mjs,installed-module-check.mjs,installed-module-check.sh,INSTALLED_INPUTS.md,README.md}; coordination/lanes/wasm-gen.md
contracts: none; production ModuleSource, importer/reset/source-unit policy, selected toolchains, runtime/W6/ABI, consumer code and packages unchanged
checks: Beam zero blocking diagnostics; focused production 4.33 ModuleSource build (5 jobs) and fixture Lean typecheck pass; isolated 4.34 direct Lean and 629-job real-source dependency cone pass; fresh renderer assembly and five-owner/seven-entry deterministic capture gate pass; negative provenance controls pass; make check passes 730 cases/2172 comparisons; make talos-check passes 3205 jobs plus 3166-job trust stage after existing setup; FIR_CHECK_JOBS=2 bash integration/talos/artifact/check.sh passes, including deterministic repeats; diff and mailbox checks pass. No browser run or package retarget was requested. Containing status successor changes documentation only.
bug-cards: none new; no target compiler diagnostic or semantic discrepancy. Existing legacy reset defect remains separate.
blockers: none for this bounded slice; full renderer closure/assembly/lowering/linking/host profile/execution remain unproven
handoff: Clean local-only immutable checkpoint in canonical completion; root may review and land this bounded provider. No main advance or push by W7.
next: Stop. Root scopes the next dependency assembly/capture request; do not start recursive capture or runtime work implicitly.
```

## Results and provenance

The original 41-signature frontier is now **31 capture-resolvable owning-module
inputs, six runtime/primitive boundaries and four VIR boundaries**. All seven
former setup gaps were captured after compiling their real owning modules:

- `Init.Data.Repr`: 121 groups / 268 declarations; `Nat.reprFast`.
- `Init.Data.Array.Basic`: 351 / 673; `Array.append._redArg`.
- `Init.Prelude`: 747 / 1177; `Lean.Name.mkStr3`, `Lean.Name.mkStr4`.
- `Init.Data.ToString.Name`: 23 / 74; `Lean.Name.toString` and the observed
  `toStringWithToken` specialization.
- `Lean.DocString.Types`: 141 / 314; `Lean.Doc.instBEqMathMode.beq`.

These are **derived capture inputs**, not recovered release setup metadata.
They use pinned 4.34.0-rc2 revision `6a10ac8c22beadecabdbb0919c2b50214762f91d`,
exact bootstrap template and stage options, matching installed sources/imports,
and hashes of all six artifact parts for the selected owners and 325 installed
import-DAG modules. The DAG is inventoried, not recursively captured. No synthetic
Lake setup JSON is written. See `integration/vbp-native-session-probe/INSTALLED_INPUTS.md`
for the precise provider boundary, configuration and reproducer.

The previous one-dependency assembly remains 512 locals / 103 signatures, with
LCNF SHA-256 `7e09d684407485b58ba2dbbe25d8e20605b5e9b76dbdff42639c83c4ce019c7a`.
The five new captures have not been merged into it.

Reproduce: `bash integration/vbp-native-session-probe/installed-module-check.sh`.
Disposable evidence: `.deps/native-session-probe/installed-inputs/`.
Current derived-input manifest SHA-256:
`09f5950ffc9b292af6ff665297c8b949d825ecc797149022729e2a4858bf8f92`.
Gate logs are `.deps/native-session-probe/control/installed-module-final.log`
and `installed-inputs-{433-cone,make-check,talos-check,artifact-check}.log`.
