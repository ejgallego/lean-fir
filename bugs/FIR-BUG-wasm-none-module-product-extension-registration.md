---
id: FIR-BUG-wasm-none-module-product-extension-registration
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-09-15
reproduction: integration/vbp-native-session-probe/ModuleProduct.lean
regression: integration/vbp-native-session-probe/module-product-check.sh
---

# Summary

Serial owning-module source capture stops when importing the actual Lake setup
for `VersoManual.Basic`: the persistent environment extension
`Verso.Genre.Manual.inlineExtensionExt` is registered more than once.

## Minimal reproduction

The bounded renderer worklist captures each defining module once and caches its
environment. After 26 successful module captures and 74 entry selections, the
next source signature is `Verso.Genre.Manual.instToJsonInline.toJson`, owned by
`VersoManual.Basic`. Loading its real module setup reports the duplicate
extension before returning a captured module. This is currently a real-source
reproducer, not a minimized upstream case.

## Exact commands

From the W7 worktree, with the pinned consumer/source prerequisites documented
in the fixture README:

```sh
bash integration/vbp-native-session-probe/module-product-check.sh
```

All scratch uses `.deps/native-session-probe/`; no consumer build products or
system temporary paths are consumed. `product.json` explicitly reports
`complete: false`; a passing experiment check means the diagnostic/partial
product reproduces deterministically, not that source closure is complete.

## Expected semantics

A faithful module-product provider must preserve each owning frontend's imports
and initializer context. It must either isolate incompatible initialization
contexts or report that it cannot capture the requested module; it must not
silently reset or reuse a conflicting global extension registry.

## Actual behavior

Both runs stop at source header line 6 of `VersoManual/Basic.lean`:

```text
invalid environment extension, 'Verso.Genre.Manual.inlineExtensionExt' has already been used
```

The actual setup names 16 plugins, including `verso_VersoManual_Ext.so`.
`VersoManual.Ext` defines `inlineExtensionExt` with `initialize` and
`registerPersistentEnvExtension`. Upstream `Lean.Environment` rejects an already
registered extension name. The lifecycle successor isolates a collision between
the renderer setup's aggregate `libverso_VersoManual.so` and the Basic setup's
standalone `verso_VersoManual_Ext.so`. Both define the same native initializer
and extension storage symbols. A plugin-only load sequence reproduces the error;
fresh Basic, Basic twice, and the same renderer plugin list twice all pass.
This is not an interpreted-replay diagnosis or a claimed upstream defect.
The target source module is not self-imported.

## Proof or differential evidence

Two independent whole-worklist processes produce identical root/product LCNF
and product JSON. The partial result has 1,201 bodies and 111 signatures:
74 native/primitive, 12 VIR and 25 unresolved source signatures. Each successful
owner is captured once; type/borrow/safety/universe and duplicate-provider
negative controls reject before worklist execution.

## Semantic impact

Source capture failure before lowering or Wasm generation. No incorrect emitted
program or W6 contract violation is claimed. Existing native/host boundaries
remain unadmitted at the Wasm ABI level.

## Classification and triage

W7 module-capture process/initializer lifecycle boundary. It is distinct from the
older root-reset/shared-specialization defect. Preserve unchanged owning source
and actual plugin setup while isolating the cause in a separately scoped task.

## Workaround

None. Worklist stops at the first diagnostic and retains the partial inventory.
No registry reset, initializer suppression, name seeding or prebuilt closure
injection is added.

## Upstream tracking

None; no standalone upstream reproducer or upstream bug claim yet.

## Resolution and regression

Open. The diagnostic regression records the current stop; it does not certify
complete renderer capture or permit continuation past this module.

The causal lifecycle regression is
`bash integration/vbp-native-session-probe/extension-lifecycle-check.sh`.
It compares five fresh/serial/plugin-only controls, repeated in independent
processes, without changing the registry, sources or plugin inputs. See
`integration/vbp-native-session-probe/EXTENSION_LIFECYCLE.md` for exact inputs and
the reduced native-plugin reproducer. Repair/design remains separately scoped.
