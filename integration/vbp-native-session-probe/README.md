# Renderer-core capture/link probe

This local-only fixture targets the real
`VersoBlueprint.Experimental.VirPreview.Renderer.render` root, as revised by
`ROOT-W7-20260913-002..003`. The directory retains the original request name;
NativeSession component/session roots are no longer selected.
It does not implement a browser adapter or exercise React/callback lifetimes.
The historical `integration/vbp-verso-viewer/` package is untouched.

Current state: **the new owning-module production adapter captures the real
renderer successfully**: 151 local entry declarations and 41 explicit external
signatures. These are not final Wasm host imports. See
[MODULE_RESULT.md](MODULE_RESULT.md) for the repaired boundary, regression and
remaining transitive-dependency work. Run the bounded current acceptance with:

```sh
bash integration/vbp-native-session-probe/module-capture-check.sh
```

[FEASIBILITY.md](FEASIBILITY.md) records the next one-module dependency
experiment, successful deterministic assembly (512 locals / 103 remaining source
signatures), and the provenance-based taxonomy of all 41 original externals.
Run `bash integration/vbp-native-session-probe/module-assembly-check.sh` for that
capture-only gate. A complete renderer closure and Wasm package remain unclaimed.

[INSTALLED_INPUTS.md](INSTALLED_INPUTS.md) records the next bounded provider:
verified bootstrap-derived capture inputs for the five installed Lean modules
behind the seven former setup gaps. These are not recovered release setup files.
Run `bash integration/vbp-native-session-probe/installed-module-check.sh` to
refresh the frontier, capture those owners and check deterministic repeats and
negative provenance controls. No recursive assembly or Wasm linking is performed.

[MODULE_PRODUCT.md](MODULE_PRODUCT.md) records the subsequent source-only
worklist: 26 owning-module captures, 1,201 bodies and 111 remaining signatures.
It stops deterministically at duplicate extension registration in
`VersoManual.Basic`; the closure remains incomplete. Run
`bash integration/vbp-native-session-probe/module-product-check.sh` to reproduce
the checked partial product and exact diagnostic boundary, not a Wasm acceptance.

[EXTENSION_LIFECYCLE.md](EXTENSION_LIFECYCLE.md) isolates that stop to overlapping
aggregate/per-module native plugins. Fresh and same-context repeated captures
pass; a plugin-only aggregate-then-`Ext` reproducer fails. Run
`bash integration/vbp-native-session-probe/extension-lifecycle-check.sh` for the
bounded five-case repeated diagnostic. No lifecycle workaround or continued
module-product assembly is implemented.

[PRODUCT_TRANSPORT.md](PRODUCT_TRANSPORT.md) demonstrates the next isolated
experiment: two fresh Basic captures transport identical final-LCNF products
through Lean's existing object compactor into two fresh renderer contexts.
Source/setup/plugin and compiler-data verification pass without overlapping
native images. Run `bash integration/vbp-native-session-probe/product-transport-check.sh`.
This is trusted-local feasibility, not a durable format, production driver,
continued module worklist or Wasm artifact.

[TWO_MODULE_WORKER.md](TWO_MODULE_WORKER.md) records the bounded successor:
`product-transport-check.sh --assemble` constructs the renderer and selected
Basic source product (158 bodies / 45 signatures) with unchanged renderer
capture and isolated native images. It stops after those two entry closures.

The historical reset-based source provider is unchanged and still stops at the
same unknown specialization. Constructor metadata and executable-body discovery
regressions pass.
[REBUILD_BOUNDARY.md](REBUILD_BOUNDARY.md) locates it at the mandatory post-saveBase
check and records a shared-specialization reader left visible by root-local reset.
[PROVENANCE_RESULT.md](PROVENANCE_RESULT.md) explains the repaired discovery
omission and remaining compiler-rebuild failure. See
[REPAIR_RESULT.md](REPAIR_RESULT.md) for that earlier result and its ordinary
capture commands. [CAPTURE_RESULT.md](CAPTURE_RESULT.md) records the earlier
constructor failure. [CONTROL.md](CONTROL.md) isolates the
earlier postponement failure, and [RESULT.md](RESULT.md) preserves that original
negative checkpoint. The historical `Probe.lean` and `Capture.lean` compile in
ordinary mode, but their reset-based capture throws before returning a complete closure.
`Emit.lean` and actual lower/link execution remain unvalidated. The structural validator cannot
accept the new binding profile: it explicitly stops pending actual captured
frontier classification and conformance. No guessed profile is emitted.

[METADATA_RESULT.md](METADATA_RESULT.md) narrows the failure: all required
`Int`/`Int.ofNat` metadata is intact immediately before the final dependency
rebuild. The repair preserves constructor/type module mappings during that
stage; it does not seed metadata or merge source units.

## Historical reset-based reproducer (still failing)

From the W7 worktree, with Lean `leanprover/lean4:v4.34.0-rc2` installed:

```sh
bash integration/vbp-native-session-probe/check.sh
```

`prepare.mjs` checks the frozen consumer identity, archives the accepted FIR
base and every manifest-pinned dependency from local Git objects, and overlays
the exact hash-checked dirty RPC file and the hash-checked FIR
`CompilerPrivate.lean` metadata, `Source.lean` body-selection repairs and the
new `ModuleSource.lean` provider. No consumer `.lake` is read as
compiler input. Archives and private build trees live in
`.deps/native-session-probe/`; the fixture has its own `.lake`, Beam session
and exact 4.34 toolchain. Ordinary FIR remains on 4.33. The cache is explicitly
4.34-scoped, and all temporary files stay under the worktree, never `/tmp`.

Default source repositories are the fixed consumer and matched read-only
source trees from `VBP-FIR-20260913-003`; `VBP_ROOT`, `VBP_MATCHED_ROOT`, and
`VIR_ROOT` can supply equivalent local repositories. Source revisions, the
consumer's dirty state, archive hashes, renderer/RPC/manifest hashes and
fixture head and all three compiler overlay hashes are recorded in
`.deps/native-session-probe/SOURCE.json`.
The RPC overlay identifies the requested consumer snapshot; it does not add
RPC, StringPreview or component roots to this renderer-only probe.

## Historical compilation boundary

By default the fixture builds VBP source modules with postponed final LCNF, then uses
FIR's existing individual-source-unit capture and boxed-adapter recovery.
The bounded control exposes `-KpostponeCompile=false` without changing that
default. Ordinary module metadata satisfies the existing source-unit lookup
criteria and contains no postponed groups. Actual capture through the existing
historical fixture reaches its final dependency rebuilding stage. With the generic
metadata repair it passes the missing compiled `Int.ofNat` boundary and fails
on an unknown generated `Array.mapMUnsafe` specialization owned by
`Verso.Doc.ListItem.toJson`. Executable-body discovery now includes that caller,
but the rebuild still fails on the same helper. It does not synthesize a replacement root.
VIR's own extern-symbol decoder identifies candidate host boundaries; the
captured reachable externals select the actual host frontier. Historical
41/46-import lists are not used as either inputs or assertions.

The emitter records captured declarations before lowering, emits a base
module, applies the ordinary closed-application resident linker with the actual
VIR host declarations explicitly allowed, and writes the linked module.
`validate.mjs` checks Wasm structure, module-owned exported memory, the requested
function export, no unresolved runtime operations, and the exact remaining
import names against the emitted signature inventory. It then fails closed
pending the requested `fir.wasm-host-binding/render-core/v0` classification;
that classification cannot be performed before capture. No instance is
created and no host fallback is installed.

Output, when the corresponding phase succeeds:

- `captured.lcnf` and `capture.json`: final source closure and selected hosts.
- `native-session-base.wasm` and its manifest: before resident linking.
- `native-session.wasm`, its manifest, and `linked.json`: resident module and
  exact remaining import signatures/helper names.
- `validation.json`: Wasm hash/size, import/export inventory and structural
  validation verdict, explicitly distinguished from browser execution.

All outputs are under `.deps/native-session-probe/output/`; no accepted package
or canonical pointer is replaced. Stop at the first concrete compatibility,
capture, lowering or link error and report it to root. General runtime fixes,
semantic changes, host adapters, and performance measurements need a separate
request. Local scratch is working state, not a permanent acceptance registry.
