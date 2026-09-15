# wasm-gen lane

Current slice: `ROOT-W7-20260915-023`. The bounded source-only module-product
experiment is ready for review at its requested first-diagnostic stop.
**The renderer source closure remains incomplete; no Wasm claim is made.**
Root retains integration ownership.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: d127851315d98564b4cbb007799ead90c99174b7
functional-head: 31067950a6176fbc14d82101831dbde3749da652
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Deterministic source-only renderer module-product worklist; actual owner capture once, exact signature/provenance admission, explicit native/VIR boundaries, first-diagnostic stop and exact partial inventory.
files: integration/vbp-native-session-probe/{ModuleProduct.lean,Probe/InstalledInputs.lean,InstalledModuleCapture.lean,module-product-inputs.mjs,module-product-check.mjs,module-product-check.sh,installed-module-inputs.mjs,installed-module-check.sh,MODULE_PRODUCT.md,README.md}; bugs/FIR-BUG-wasm-none-module-product-extension-registration.md; coordination/lanes/wasm-gen.md
contracts: none; production capture/importer/reset/source-unit policy, root toolchain, runtime/W6/ABI, consumer sources and packages unchanged
checks: Lean Beam fixture checks zero blocking diagnostics (InstalledModuleCapture refresh resolved stale-direct-dependency barrier); exact functional-head module-product-check.sh passes direct Lean, 630-job source cone, signature/owner negative controls, two identical root/product text+JSON repeats and exact expected diagnostic/census; installed-module-check.sh passes one-module assembly, 629-job source cone plus 7-job helper build, five-owner/seven-entry repeats and negative provenance controls; exact functional-head make check passes 730 cases/2172 comparisons, 232 bug cards; diff and mailbox checks pass. Talos/artifact/browser gates not rerun: root explicitly permits fixture/report-only checks and no production or Wasm artifact changed. Containing status successor changes this document only.
bug-cards: FIR-BUG-wasm-none-module-product-extension-registration
blockers: source closure stops at duplicate Verso.Genre.Manual.inlineExtensionExt registration while capturing VersoManual.Basic; exact loader/initializer cause not yet isolated
handoff: Clean local-only immutable checkpoint in canonical completion. Root may review this diagnostic milestone; no main advance, push, runtime workaround or package publication by W7.
next: Stop for root review. Separately scope faithful module-initialization/plugin lifecycle isolation before continuing source closure; no suppression/reset or inferred host fallback.
```

## Exact result

Real root: `VersoBlueprint.Experimental.VirPreview.Renderer.render`.
Lean remains the isolated `4.34.0-rc2` revision
`6a10ac8c22beadecabdbb0919c2b50214762f91d`; production FIR remains 4.33.
Frozen source identities and production compiler overlays are unchanged.

The worklist captures **26 modules**, completes **74 source-entry selections**,
and admits **1,201 bodies**. Its **111 remaining signatures** are classified as
74 native/primitive, 12 VIR and 25 source pending. These counts are not a final
Wasm import inventory. The first new diagnostic, selecting
`Verso.Genre.Manual.instToJsonInline.toJson` from `VersoManual.Basic`, is:

```text
invalid environment extension, 'Verso.Genre.Manual.inlineExtensionExt' has already been used
```

The actual module setup includes `verso_VersoManual_Ext.so`. A process-global
initializer/plugin interaction is a hypothesis, not an isolated upstream bug.
No continuation or workaround was attempted beyond this requested stop.

Both independent committed-head runs match:

- root LCNF: `819fed859b7d21f3988072f7be53969705614de8d047f41b6c8b8bc488704073`
- partial-product LCNF: `fdb34c2cb7a5366c6d60258d17a46e15413416ba91e43a9e38e66a1dd1a7d1f3`
- product JSON: `3992287d8672a82573605c0732e7f2a9b44020967abd7095978718fc1ec1372e`

The existing installed-input verifier is extracted without semantic changes
into a fixture module. Its JS driver now accepts the actual worklist owner;
the default five-owner test and all provenance checks are retained.

Report/reproducer: `integration/vbp-native-session-probe/MODULE_PRODUCT.md`.
Disposable exact inventories: `.deps/native-session-probe/module-product/`.
Final logs: `.deps/native-session-probe/control/module-product-committed-final.log`,
`module-product-installed-regression.log`, `module-product-committed-make-check.log`.
The experiment's PASS certifies the expected deterministic partial stop, not
successful complete capture. No changed proof or generation-readiness claim.
