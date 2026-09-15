# FIR renderer feasibility

Date: 2026-09-15. Source boundary: the real
`VersoBlueprint.Experimental.VirPreview.Renderer.render`, not NativeSession,
component factories or a substitute renderer. Investigation base:
`e9040629423305c81f6e924b0761c66113dfa209`.

## Assessment

**The owning-module final-LCNF capture approach is viable for the two real
renderer modules tested. An executable FIR Wasm renderer is not yet demonstrated.**
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

The drafted fixture checks parameter/result types, borrowing, safety and universe
parameters before replacing a signature. It rejects duplicate local definitions
and inconsistent duplicate externals. The root's full captured groups and entry
text must remain unchanged; remaining dependencies stay typed external signatures.
A negative control corrupts the selected signature's borrow bit. These assembly
checks have not executed: the second frontend currently fails first.

Initial same-process run stopped before assembly: the second import lacked Lean's
initializer-execution precondition. Upstream `withImporting` resets that flag in
its `finally` block. Upstream `Elab/Frontend.lean` restores it before another
import in the incremental frontend. A single enable call in CLI `main` is therefore
insufficient for two serial frontend invocations. This is a driver lifecycle
obligation, not a failing LCNF transformation. A per-invocation restoration is
proposed to root; it must preserve exact native/imported versions, serial imports
and loaded compacted regions. No compiler mapping reset is involved.

No assembled closure, emitted Wasm, import-profile conformance or browser result
is claimed at this initial checkpoint. The assembly experiment is intentionally
not recursive; root's lease covers one immediate defining module.

## Remaining work and acceptance

1. **Checked module composition.** Complete the bounded assembly control,
   validate signature rejection and unchanged root groups, and repeat it exactly.
2. **Reachable dependency closure.** Generalize only after the control passes:
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

The same-process diagnostic, after the source preparation/cache setup documented
in `MODULE_RESULT.md`, is:

```sh
cd integration/vbp-native-session-probe
lake --keep-toolchain -KpostponeCompile=false env lean --run ModuleAssembly.lean \
  ../../.deps/native-session-probe/sources/vbp/src/VersoBlueprintVir/Preview/Renderer.lean \
  .lake/build/ir/VersoBlueprintVir/Preview/Renderer.setup.json \
  ../../.deps/native-session-probe/sources/vbp/packages/verso-react/.lake/build/ir/VersoReact/Renderer.setup.json \
  ../../.deps/native-session-probe/assembly/first
```

This currently exits 1 at the second import's initializer precondition; no
assembly files are published. `ModuleAssembly.lean` itself is Beam-clean.

Exact source pins and hash-checked compiler overlays are in `prepare.mjs` and
`MODULE_RESULT.md`, with generated `SOURCE.json` in the ignored source view.
FIR production remains Lean 4.33; this isolated consumer probe uses exact Lean
4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
VBP is `c4430bfe2c898c0312903ae46c45b410d253ebf4` with only the recorded RPC
delta, VIR `9fafe9cfd594213ee39dc8205b08084c31101816`, and Verso
`52c8c9557bcb5cc8c0edc0ee37e74311a3d53ee9`. Consumer build products are not inputs.

The independent VersoReact entry LCNF SHA-256 is
`210232420f95470371ff1234b0b1097788b863815ef2120aa715842904a9f138`.
The initial assembly diagnostic log SHA-256 is
`81e59c77136cebc0fea7cf58e14593625e3fe03a3a99af5fa33b1e401b11e4f1`.
Ignored outputs are disposable; immutable sources and tracked drivers are the
reproduction record. No consumer source, W6/runtime/ABI, package pointer or
remote publication changes are part of this investigation.
