# FIR renderer feasibility

Date: 2026-09-15. Source boundary: the real
`VersoBlueprint.Experimental.VirPreview.Renderer.render`, not NativeSession,
component factories or a substitute renderer. Investigation base:
`794b64fecec47d068c4400abe6213808081ba583`.

## Assessment

**The owning-module final-LCNF capture and one-module composition approach works
for the two real renderer modules tested. An executable FIR Wasm renderer is not
yet demonstrated.**
We can retain Lean's module compiler and final LCNF; there is no evidence from
this experiment requiring an IR-backend migration or a copied renderer.

The important change is architectural: compile each real module in its own
frontend context, then compose its captured products. Do not recover imported
code by selectively erasing compiler mappings and reconstructing root groups.
The latter path remains known-broken for shared specializations.

This is a synchronous **host-backed renderer**, not a self-contained pure trace
kernel like Illuminate's animation package. Its source type is
`Document → VersoReact.Renderer.Options → ReactM (Js Node)`. The existing draft
`render-core/v0` contract allows synchronous host-value construction. It does not
admit mounting, hooks, effects, retained callbacks or lifecycle ownership.
Zero function imports is consequently not the acceptance criterion for this
renderer. The exact permitted frontier must still be established from a complete
linked artifact; no signature in this report is classified as an accepted host import.

## Evidence obtained

| Actual module / selected entry | Original groups | Captured module declarations | Entry-local declarations | External source signatures |
| --- | ---: | ---: | ---: | ---: |
| Verso.Doc / private DescItem.toJson | 317 | 621 | 7 | 6 |
| VBP Renderer / Renderer.render | 28 | 164 | 151 | 41 |
| VersoReact.Renderer / render | 141 | 565 | 361 | 91 |

The first two rows are accepted on main through `c57742d0`. The third was
captured with the same accepted production provider in this investigation.
Counts include generated companions; they are neither Wasm function counts nor
package size measurements. The 41 and 91 frontiers overlap and must not be added
to infer a final import count.

The real DescItem final-LCNF body includes both calls to the ListItem-owned
shared specialization and its actual body. Root-local reset previously hid that
helper while retaining a reader. Ordinary module capture preserves the coherent
compiler context and passes all normal compiler checks. This is evidence against
a fundamental inability to compile the source, not a repair of the old reset API.

## One-module assembly experiment

The current bounded experiment selects only the actual external
`VersoReact.Renderer.render`. Its defining-module name comes from the renderer's
compiler environment. Lake's source search path resolves that module's unchanged
source; its actual setup must name the same owner. Both modules are compiled
through the accepted `ModuleSource` provider, not imported final-LCNF bodies.

The fixture checks parameter/result types, borrowing, safety and universe
parameters before replacing a signature. It rejects duplicate local definitions
and inconsistent duplicate externals. The root's full captured groups and entry
text must remain unchanged; remaining dependencies stay typed external signatures.
A negative control corrupts the selected signature's borrow bit and is rejected.
Assembly succeeds with **512 local declarations and 103 external signatures**.
The selected body is present; all 28 root groups (164 declarations) are unchanged.
Two complete runs produce identical inventories and LCNF text. The actual input
selector also rejects missing and ambiguous setup candidates before use.

Initial same-process run stopped before assembly: the second import lacked Lean's
initializer-execution precondition. Upstream `withImporting` resets that flag in
its `finally` block. Upstream `Elab/Frontend.lean` restores it before another
import in the incremental frontend. A single enable call in CLI `main` is therefore
insufficient for two serial frontend invocations. This was a driver lifecycle
obligation, not a failing LCNF transformation. Root approved per-invocation
restoration in `ROOT-W7-20260915-017`; the fixture now does so, preserving exact
native/imported versions, serial imports and loaded environments. Production
ModuleSource's caller-duty contract is unchanged. No compiler mapping reset is involved.

This is a partial capture product, not a closed renderer: the larger frontier
reflects the newly exposed dependencies and is not a regression or an import
count to optimize yet. No emitted Wasm, import-profile conformance or browser
result is claimed. The experiment is intentionally not recursive; root's lease
covers one immediate defining module.

## Taxonomy of the original 41 signatures

Classification uses actual final-LCNF extern attributes, VIR's own symbol
decoder, defining-module provenance, Lean's Lake-provided source search path,
and actual Lake-produced setup files. No historical host list is used.

| Category | Count | What the evidence establishes |
| --- | ---: | --- |
| Capture-resolvable owning module | 24 | One source and one matching Lake setup exist; only the selected owning module was compiled here. |
| Runtime/primitive boundary | 6 | Actual native extern symbol; resident availability/signature acceptance is not tested here. |
| VIR boundary | 4 | Actual encoded extern decoded by VIR metadata; no physical ABI or v0 conformance claim. |
| Unavailable/ambiguous input | 7 | All seven have source, but no owning setup in this fixture; none is ambiguous. |

Capture-resolvable signatures (24, in seven owning modules):

- `Vir.React.Builders` (10): `Lean.Vir.React.Props.{string,fromEntries,stylePairs,className}`;
  `Lean.Vir.React.Node.{codeText,divWith,pWith,elementWith,preWith,strongWith}`.
- `VersoReact.Renderer` (8): `VersoReact.Renderer.Style.{inlineCode,unsupported,codeBackground,borderColor,background,muted}`;
  `VersoReact.Renderer.{renderMath,render}`.
- `VersoBlueprint.Data` (2): `Informal.Data.instToStringLabel._lam_0`,
  `Informal.Data.ExternalMarkupLanguage.key`.
- `VersoBlueprint.Informal.Code.Data` (1):
  `Informal.instFromJsonExternalMarkupBlockData.fromJson`.
- `VersoBlueprint.Informal.Block.Model` (1): `Informal.instFromJsonBlockOccurrence.fromJson`.
- `VersoBlueprint.Informal.ExternalMarkupView` (1): `Informal.ExternalMarkupView.displaySummary`.
- `VersoBlueprint.Math.Data` (1): `Informal.Math.instFromJsonBpMathData.fromJson`.

Runtime/primitive signatures (6):

| Declaration | Actual native symbol |
| --- | --- |
| `Array.mkEmpty` | `lean_mk_empty_array_with_capacity` |
| `Array.push` | `lean_array_push` |
| `Lean.Name.beq` | `lean_name_eq` |
| `String.append` | `lean_string_append` |
| `String.utf8ByteSize` | `lean_string_utf8_byte_size` |
| `Nat.decEq` | `lean_nat_dec_eq` |

VIR signatures (4):

| Declaration | Decoded logical target |
| --- | --- |
| `Lean.Vir.Js.Array.empty` | `js.array.empty` |
| `Lean.Vir.React.Node.fragment` | `react.node.fragment` |
| `Lean.Vir.JsValue.ofString` | `js.string` |
| `Lean.Vir.React.Node.text` | `react.node.text` |

Missing setup inputs (7):

| Declaration | Recorded owning module |
| --- | --- |
| `Nat.reprFast` | `Init.Data.Repr` |
| `Array.append._redArg` | `Init.Data.Array.Basic` |
| `Lean.Name.mkStr3` | `Init.Prelude` |
| `Lean.Name.mkStr4` | `Init.Prelude` |
| `Lean.Name.toString` | `Init.Data.ToString.Name` |
| `Lean.Name.toStringWithToken._at_.Lean.Name.toString.spec_0` | `Init.Data.ToString.Name` |
| `Lean.Doc.instBEqMathMode.beq` | `Lean.DocString.Types` |

These last seven expose a **toolchain-module input gap**, not absent Lean source
or proved missing Wasm primitives. Installed Lean provides their source and
compiled imports, but this Lake project has no corresponding module setups.
A faithful toolchain-module provider needs its own reviewed source/options/import
provenance; inventing default setup JSON or rebuilding individual generated names
would evade that requirement. This is the clearest remaining capture prerequisite.

Full expanded rows, source/setup hashes, and all 103 remaining signatures are
reproducible in `assembly/feasibility.json` and `assembly/first/assembly.json`
under `.deps/native-session-probe/`. This taxonomy is of the original 41 only;
it must not be mistaken for classification of the complete dependency graph.

## Remaining work and acceptance

1. **Toolchain module inputs.** Decide the faithful owning-module provider for
   the seven observed signatures in five installed Lean modules. Reuse real
   compiler/build provenance; do not synthesize named adapters.
2. **Reachable dependency closure.** Generalize the now-passing composition control:
   resolve real source/setup identities, capture each owning unit once, preserve
   generated-name provenance, and resolve the remaining graph. Missing inputs,
   incompatible signatures or duplicate bodies are explicit blockers—not reasons
   to fall back to root-local reset or name-based shims.
3. **Actual Wasm lowering and resident linking.** Run the existing pipeline on
   that complete capture product. Record unsupported lowering, runtime operations,
   unresolved signatures, bytes and exact exports/imports. These stages are still
   untested for this renderer snapshot.
4. **Host-profile feasibility.** Crosswalk the actual remaining calls against
   VIR's logical metadata and the accepted draft profile. A callback, async or
   lifecycle requirement outside v0 is a separately reviewed contract question.
   Do not infer conformance from namespace prefixes or older viewer packages.
5. **Execution and consumer acceptance.** Only after structural/profile checks,
   test the real typed input and synchronous output, resource ownership/disposal
   and negative cases; then run VBP's browser comparison. No performance claim
   precedes equivalent workload and timing boundaries.

The next useful engineering investment is module-product composition and source
resolution, not a new renderer implementation or a new Wasm backend. The runtime
and host work cannot yet be estimated reliably: the complete closure is the gate
that reveals its actual size. Full allocation/refinement theorem coverage is a
separate W6 question and is not established by successful code generation.

## Reproduction and provenance

Accepted module controls:

```sh
bash integration/vbp-native-session-probe/module-capture-check.sh
```

The complete one-module repeat/negative-control and taxonomy gate is:

```sh
bash integration/vbp-native-session-probe/module-assembly-check.sh
```

The underlying same-process driver, after source preparation/cache setup, is:

```sh
cd integration/vbp-native-session-probe
lake --keep-toolchain -KpostponeCompile=false env lean --run ModuleAssembly.lean \
  ../../.deps/native-session-probe/sources/vbp/src/VersoBlueprintVir/Preview/Renderer.lean \
  .lake/build/ir/VersoBlueprintVir/Preview/Renderer.setup.json \
  ../../.deps/native-session-probe/sources/vbp/packages/verso-react/.lake/build/ir/VersoReact/Renderer.setup.json \
  ../../.deps/native-session-probe/assembly/first
```

This now exits 0 and writes a partial capture product. Beam and direct Lean are
green; the final source dependency cone is 629 jobs. The repeat gate confirms
the signature, source/setup, root-preservation and determinism controls above.
At functional head `7b60a8dadd848e523fa4efc1d7bdb173c0793d5e`, the focused
repeat/direct gate passes, `make check` passes 730 cases / 2172 comparisons, and
Talos passes 3205 jobs plus its 3166-job trust stage. Root checks were repeated
with the explicit production-toolchain cache scope; the fixture uses its separate
4.34 scope. No production adapter or runtime was edited, so no new artifact or
browser gate is claimed. Final diff and mailbox checks pass.

Exact source pins and hash-checked compiler overlays are in `prepare.mjs` and
`MODULE_RESULT.md`, with generated `SOURCE.json` in the ignored source view.
FIR production remains Lean 4.33; this isolated consumer probe uses exact Lean
4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
VBP is `c4430bfe2c898c0312903ae46c45b410d253ebf4` with only the recorded RPC
delta, VIR `9fafe9cfd594213ee39dc8205b08084c31101816`, and Verso
`52c8c9557bcb5cc8c0edc0ee37e74311a3d53ee9`. Consumer build products are not inputs.

The independent VersoReact entry LCNF SHA-256 is
`210232420f95470371ff1234b0b1097788b863815ef2120aa715842904a9f138`.
The assembled partial LCNF SHA-256 is
`7e09d684407485b58ba2dbbe25d8e20605b5e9b76dbdff42639c83c4ce019c7a`.
The initial assembly diagnostic log SHA-256 is
`81e59c77136cebc0fea7cf58e14593625e3fe03a3a99af5fa33b1e401b11e4f1`.
Ignored outputs are disposable; immutable sources and tracked drivers are the
reproduction record. No consumer source, W6/runtime/ABI, package pointer or
remote publication changes are part of this investigation.
