# Checked final-LCNF definitions

`Reify.defineArtifact name captured` installs a safe, closed `ImpureProgram`
definition through Lean's kernel and returns an artifact whose program is read
from that definition. Pass this returned artifact to the ordinary production
lowerer. `Reify.defineDeclEquations` reads the same definition and adds the
selected declaration plus exact `findDecl?` and declaration-value equations.
These equations are checked by reflexivity; the lookup theorem type inherits
standard `propext` through `Array.find?`, not a generated axiom. The program,
concrete declaration and body equation have no axiom dependencies.

The bridge quotes constructors, not printed syntax or persistent-extension
payloads. Readback accepts only the canonical constructor grammar and requires
exact re-quotation equality. Embedded `Lean.Expr` fields are data: binder names,
universe parameters, literals and all supported constructor fields survive.
Metadata is explicitly unsupported, not erased. Other malformed input fails
closed. The regression corpus covers all impure LCNF constructors and all
supported expression constructors. This establishes concrete capture identity,
not a well-formedness or semantic correctness theorem for arbitrary LCNF.

Kernel checking is synchronous with `debug.skipKernelTC=false`, and exposes
generated bodies under Lean's module system. No native
evaluation, unsafe quotation or deserializer is involved. Production semantics,
runtime contracts, ABI and lowering policy are unchanged.

## Retained lean-zip RC2 nomination

The fixture templates in `retained-example/` reproduce the source boundary for
`Zip.Spec.DeflateStoredCorrect.deflateStoredPure._closed_0`, captured from the
real `Zip.Wasm.compressStored` entry. The new harness imports its owning
`Zip.Wasm.Stored` module and transitive dependencies; the old diagnostic's
unrelated Level1/Entry imports are not required to compile this entry. Those
extra imports exposed RC2 kernel recursion failures in
`Zip.Native.DeflateParse:361,367`, also with the private limit raised to 8192.
No source file was patched or substituted. Do not import old oleans under RC2.

Required immutable source trees:

- lean-zip: `273d0d6cd9cab77c7f3489b0b0b1f6e543315d21`.
- zip-common: `4425bab1f9522307d77e8d485bc536149ba31c36`.
- FIR: the checkpoint containing this bridge, official `leanprover/lean4:v4.34.0-rc2`.

Use `git archive` of those exact source commits, not mutable checkout copies or
old build products, into `.deps/retained-rc2/{lean-zip,zip-common}`. Do not fetch
replacement revisions if either object is unavailable. Relevant SHA-256 checks:

| File (inside its source tree) | SHA-256 |
| --- | --- |
| `Zip/Wasm/Stored.lean` | `04a45db8d39525f9fbf2eb1741a343f88f2cfdc0dc0bd6cfb44e9e433160badf` |
| `Zip/Spec/DeflateStoredCorrect.lean` | `7402afafeddc89b1f812404b84f03d0b6f7e6e1b076cc7eccdc11e51c670ace3` |
| `ZipForStd/ByteArray.lean` | `efb6d06b5fd2cef634ab79ecf454ee8ab00029ebe112c34af445d69e4eecc9ae` |

Copy the three templates to that private project without their `.in` suffix;
copy FIR's `lean-toolchain` there. Then, from the private project:

```sh
export LAKE_CACHE_DIR="$(bash ../../scripts/fir-lake-cache-path.sh)"
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
mkdir -p ../tmp
export TMPDIR="$(cd ../tmp && pwd)"
lake build RetainedRC2
lake env lean Readback.lean
sha256sum lean-toolchain lakefile.lean lake-manifest.json \
  RetainedRC2.lean .lake/build/lib/lean/RetainedRC2.olean \
  checked-lowering.json ordinary.wasm closed.wasm resident.wasm
```

The explicit private `maxRecDepth=8192` is a compilation resource limit for old
lean-zip proof imports under RC2, not a source change. Preserve this setup
identity separately from the historical 4.33 setup. No toolchain overrides,
source ports, copied state-machine/initializer bodies or old oleans are used.

`RetainedRC2` captures once, checks the definition, emits lookup/body equations,
and lowers only the readback through ordinary, closed-closure and resident
routes. `Readback` imports the resulting olean in another process without
recapture and independently emits the equations again. Wasm output here is
lowering evidence, not a new runtime execution or refinement acceptance.

Run the generic corpus with `lake build Fir.Compiler.LCNF.ReifyExamples`.
It rejects malformed root/array data, wrong phases and metadata, distinguishes
binder names, and checks the exact expected axiom sets. Batch-check generated
definitions in addition to Beam, since this boundary invokes the kernel.

## RC2 result (2026-09-26)

The owning-module capture yields 21 declarations and 14 externals, with the
nominated initializer present and whole-program closure-flow checks true.
Its checked definition is `RetainedRC2.program`; W6 can use
`RetainedRC2.initializer.findDecl` and `RetainedRC2.initializer.body` directly.
Fresh-process import/readback also succeeds. Exact embedded local IDs, names,
types and instructions are in the checked body, not a separately copied AST.

Ordinary and closed lowering each emit 1,983 bytes, SHA-256
`547a6b6e915708a5c2a491a73983f268bbb3819d13ce639f3e538b62829db4eb`.
Resident lowering emits 13,236 bytes, SHA-256
`62d0a0683b8aeaa696b592a20b3caf950b19ed59675131ae491c7dbff3cf34e4`,
with zero imports and zero remaining runtime operations. These bytes happen
to match the historical 4.33 diagnostic; that is not a claim of cross-version
AST or proof identity. The new checked definition is a distinct RC2 input.

The new toolchain is Lean `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. Local identity inventory:

| File | SHA-256 |
| --- | --- |
| `lean-toolchain` | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |
| `lakefile.lean` | `0dffafc0bf1abef84b45056db13e3b0d3a60c851a98c0fe3cc6868121687c9b7` |
| `lake-manifest.json` | `2f45a3d240c026eb60fcec7b9cf52da2e12adc908d52bfdcf40682faaafe7b0d` |
| `RetainedRC2.lean` | `257cec0900a86766b60376f9149d1996947ad12e2e6b0b996d38ee98f7687238` |
| `RetainedRC2.olean` | `7eb6d2adaf1f60e31cb7d53d5f1149593a3778084a3faaffc25ee3776efe2b0b` |
| `checked-lowering.json` | `6650403b2e5f9c7c9472ea07c0d7e30b287e2dd4dc173f6612bee4b38ab150bf` |

Outputs live in the producing worktree's ignored `.deps/retained-rc2/`.
The olean/setup identity is local and tied to that source/build environment;
the recipe, not an old binary imported under another toolchain, reproduces it.
