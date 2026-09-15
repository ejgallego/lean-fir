# Renderer source-only module product

Request: `ROOT-W7-20260915-023`; base:
`d127851315d98564b4cbb007799ead90c99174b7`.

The deterministic worklist captures **26 owning modules**, selects **74 source
entries**, and admits **1,201 bodies** before stopping at the first new frontend
diagnostic. The source closure is **incomplete**. No lowering, linking, Wasm
execution, host-profile admission, or package publication was attempted.

## Compilation boundary

The real entry remains
`VersoBlueprint.Experimental.VirPreview.Renderer.render`, owned by
`VersoBlueprintVir.Preview.Renderer`. Source pins and source views are unchanged
from [INSTALLED_INPUTS.md](INSTALLED_INPUTS.md) and [FEASIBILITY.md](FEASIBILITY.md).
The isolated compiler is Lean `4.34.0-rc2`, revision
`6a10ac8c22beadecabdbb0919c2b50214762f91d`; production FIR stays on 4.33.

`ModuleProduct.lean` walks source-pending signatures in stable encounter order.
It obtains defining owners from the captured environment, compiles each owner
once, and retains that exact captured module for subsequent entry selections.
Each owner uses either its actual Lake `ModuleSetup` or the accepted
pinned-bootstrap-derived installed-Lean input provider. The latter is selected
by the actual pending declaration and retains its existing source, import-DAG,
artifact, compiler-revision and option verification policy.

An admitted body must occur in that owner's recorded final-LCNF groups. A
signature is replaced only when owner, result type, parameter types, borrow
flags, safety and universe parameters agree. Duplicate ownership and conflicting
native declarations reject. The original root capture is compared after every
successful selection. Native/primitive and VIR externs remain signatures; they
are not copied implementations or an inferred final Wasm import inventory.

The installed-input verifier moved unchanged into the fixture-only
`Probe/InstalledInputs.lean`, so both probes use the same checks. The default
five-owner/seven-entry regression remains separate. No production capture,
importer/reset policy, runtime, W6 contract, ABI, toolchain manifest or consumer
source changed.

## First diagnostic

While selecting `Verso.Genre.Manual.instToJsonInline.toJson` from
`VersoManual.Basic`, both runs report at that source's module header, line 6:

```text
invalid environment extension, 'Verso.Genre.Manual.inlineExtensionExt' has already been used
```

The actual Lake setup has 16 plugins, including `verso_VersoManual_Ext.so`.
`VersoManual.Ext` defines the extension using `initialize` and
`registerPersistentEnvExtension`; Lean rejects a duplicate name in its
process-global extension registry. The failed owner is not included in the 26
successful captures. `VersoManual.Ext` was not separately source-captured.

These observations suggest an initialization/plugin loading interaction in the
serial multi-frontend process. They do **not** isolate the exact loading path or
establish an upstream compiler defect. No reset, suppression, process-isolation
workaround or continuation past the diagnostic was added. The next bounded
investigation should isolate that lifecycle before changing the capture driver.

Bug card: `FIR-BUG-wasm-none-module-product-extension-registration`.

## Exact partial inventory

The remaining 111 signatures are:

| Class | Count |
| --- | ---: |
| Native/primitive boundary | 74 |
| VIR boundary | 12 |
| Source pending | 25 |

Capture order:

```text
VersoBlueprintVir.Preview.Renderer
Init.Data.Repr
Vir.React.Builders
Init.Data.Array.Basic
Init.Prelude
VersoBlueprint.Informal.Code.Data
VersoBlueprint.Data
VersoBlueprint.Informal.Block.Model
Init.Data.ToString.Name
VersoReact.Renderer
VersoBlueprint.Informal.ExternalMarkupView
VersoBlueprint.Math.Data
Lean.DocString.Types
Init.Data.List.Basic
Lean.Data.Json.Basic
Lean.Data.Json.FromToJson.Basic
VersoBlueprint.Source.Data
Init.Meta.Defs
Init.Util
Init.Data.String.Defs
Init.Data.String.Substring
Init.Data.String.Basic
Init.Data.OfScientific
Vir.Js
Verso.Doc
VersoReact.RenderPath
```

Each run writes `product.json`: all module group names, every admitted body and
owner, all 74 selection records, and every remaining signature with its defining
module, source candidates, extern symbols and VIR target classification.
Per-owner `inputs/*.json` record the exact source/setup hashes or complete
derived-input manifest. `product.lcnf` contains the actual admitted bodies and
remaining signatures. These files are reproducible local evidence, not a new
published compiler format or an acceptance receipt archive.

Both independent runs agree byte-for-byte:

| File | SHA-256 |
| --- | --- |
| `root.lcnf` | `819fed859b7d21f3988072f7be53969705614de8d047f41b6c8b8bc488704073` |
| `product.lcnf` | `fdb34c2cb7a5366c6d60258d17a46e15413416ba91e43a9e38e66a1dd1a7d1f3` |
| `product.json` | `3992287d8672a82573605c0732e7f2a9b44020967abd7095978718fc1ec1372e` |

JSON includes absolute source paths, so its hash describes this exact worktree;
it is not a promise of path-independent serialization.

## Reproduce and interpret the checks

From the W7 worktree:

```sh
bash integration/vbp-native-session-probe/module-product-check.sh
bash integration/vbp-native-session-probe/installed-module-check.sh
git diff --check
make check
```

The module-product gate builds the real source dependency cone, directly checks
the Lean fixture, then runs two complete worklists in independent processes.
Negative controls reject changed borrow/safety/universe/result/parameter
signatures, a second body provider, an unknown owner and a missing entry. Output
checks enforce one capture per owner, unique bodies/signatures, selected-entry
ownership, unchanged root capture, exact partial census and the recorded stop.
A different repeatable failure does not pass this checkpoint.

Its `PASS` means **the expected deterministic fail-closed experiment passed**,
not that the source closure or renderer compilation succeeded. The unresolved
25 source entries are not waived or converted to host fallbacks.

Working evidence is under `.deps/native-session-probe/module-product/`:
`first/`, `repeat/`, and `summary.json`. Logs are under
`.deps/native-session-probe/control/module-product-*.log`. No temporary state
uses the system `/tmp` directory. Root owns review and any subsequent landing;
the fixture/report-only lease does not require rerunning unrelated Talos or
Wasm artifact gates and makes no new claims about them.
