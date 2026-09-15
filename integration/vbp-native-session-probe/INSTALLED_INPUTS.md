# Installed Lean module capture inputs

Scope: `ROOT-W7-20260915-020`, clarified by root event `-021`, on base
`854f8d1505d96721ae5252f94493b7b11e199e56`. The provider is deliberately bounded
to five installed modules and seven observed renderer-frontier declarations.
It does not assemble these captures into the renderer or recursively capture
their dependencies. Production `ModuleSource.compile` is unchanged.

## Provenance boundary

The Lean release contains source and compiler artifacts but does not ship the
generated bootstrap Lake setup files or CMake cache. Lake's external-file setup
fallback uses `_unknown` for sources outside its workspace. Neither this fallback
nor invented `.setup.json` metadata is used here.

Instead these are **pinned-bootstrap-derived capture inputs**, explicitly *not*
recovered release setup metadata. The provider reads the exact Git objects
`src/lakefile.toml.in` and `src/CMakeLists.txt` at
`6a10ac8c22beadecabdbb0919c2b50214762f91d` (Lean 4.34.0-rc2). It checks and derives:

- bootstrap package identity: none;
- `interpreter.prefer_native=false` and `pp.rawOnError=true` from CMake's stage
  arguments, starting with empty additional options on Linux;
- `linter.coreInternal=true` from the bootstrap template;
- the existing capture overrides `compiler.postponeCompile=false` and
  `Elab.async=false` from `ModuleSource.compile`.

This is a new, explicit capture configuration. Unknown command-line overrides
from the original release build are not inferred. Native compilation/linker
options do not enter this source-capture request; no native compiler is rebuilt.
The Lake `--wfail` build policy is not a Lean frontend option and is not supplied
as one. All new compiler errors stop the harness.

The installed compiler must report the exact revision. Each source must match
the corresponding pinned Git blob byte-for-byte, have exactly one source in the
actual renderer frontier, and resolve beneath that compiler's own prefix.
The provider records SHA-256 identities of all six installed artifact parts for
each owner and its installed import DAG. This DAG walk is provenance collection,
not recursive source capture. Digests are checked again before each invocation.

The Lean frontend checks the active prefix, unshadowed import-resolution paths,
source module header, exact `.olean` import array and recorded import array,
and the derived option set. The owning source is then compiled unchanged through
the existing `ModuleSource.compile`; generated entries are selected only *after*
that complete owning-module capture.

The Node driver is the verified entry point; invoking the private Lean fixture
with an arbitrary manifest bypasses the pinned-Git/digest checks and is not an
accepted provider invocation. No accepted application package or pointer changes.

## Results

All five modules compile successfully, twice, and all seven requested entries
are captured. Exact text/group repeats are checked.

| Owning module | Groups | Module declarations | Requested entry: local / external declarations |
| --- | ---: | ---: | --- |
| `Init.Data.Repr` | 121 | 268 | `Nat.reprFast`: 12 / 16 |
| `Init.Data.Array.Basic` | 351 | 673 | `Array.append._redArg`: 3 / 7 |
| `Init.Prelude` | 747 | 1177 | `Lean.Name.mkStr3`, `mkStr4`: each 4 / 0 |
| `Init.Data.ToString.Name` | 23 | 74 | `Lean.Name.toString`: 35 / 33; its observed `toStringWithToken` specialization: 34 / 33 |
| `Lean.DocString.Types` | 141 | 314 | `Lean.Doc.instBEqMathMode.beq`: 2 / 1 |

The original 41-signature renderer frontier becomes **31 capture-resolvable
owning-module inputs, six runtime/primitive boundaries, and four VIR boundaries**.
The earlier one-dependency assembly remains 512 locals / 103 signatures: these
five new captures have not been merged into it. Runtime/host admission and full
renderer Wasm feasibility remain separate.

## Reproduce

```sh
bash integration/vbp-native-session-probe/installed-module-check.sh
```

Requires the same pinned consumer inputs as `module-assembly-check.sh`, the exact
installed toolchain, and local Lean Git objects (`LEAN_SOURCE_REPO` may select
an equivalent repository). No consumer `.lake` is used. The script first reruns
the real renderer/one-module assembly to refresh its frontier. It then derives
and verifies inputs, runs negative provenance controls, captures each owner twice,
and writes the revised taxonomy under `.deps/native-session-probe/installed-inputs/`.

`derived-inputs.json` records contributing upstream hashes, options, source and
artifact identities. `status.json` records every capture/group/entry inventory,
LCNF hashes and the revised frontier. Neither is Lake setup JSON. Scratch remains
worktree-local and disposable.

Negative controls cover stale revision, source, own/dependency artifacts, changed
options, missing source, ambiguous module/input selection, and recorded import
provenance mismatch. Successful capture does not weaken any existing source-unit,
importer, reset, runtime, W6, ABI or host-profile policy.
