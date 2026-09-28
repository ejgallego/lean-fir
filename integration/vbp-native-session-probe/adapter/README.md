# Frozen renderer UTF-8 adapter producer

This is a narrow, local package producer, not a public FIR runtime API. It
promotes the consumer-accepted JavaScript depth-scratch implementation from
package `b5b3a053e4135f913504a376` to tracked sources. The host and focused smoke
remain byte-identical to that package. No Lean program is recaptured or rebuilt.

The explicit input is frozen package `1c3b87b3f270114a3a56eeb7`. `inputs.json`
authenticates its full checksum inventory, BUILD identity and Wasm before any
output is created. Support modules, compiled Wasm, layouts and provider code
are copied only from that verified input, never from mutable VBP/VIR sources.
The tracked host, smoke and verifier replace only their designated files.
BUILD and README record the new producer boundary; all other baseline files
must remain identical. The existing immutable-package utility handles atomic
local output and complete checksums. There is no current-pointer update.

`BUILD.fir`, `BUILD.lean` and `BUILD.frozenInputs` remain the original compiled
Wasm provenance (Lean 4.34.0-rc2). `BUILD.producer` separately identifies this
packaging checkout, its 4.34.1 toolchain, dirty state and exact source hashes.
Repackaging does **not** turn those frozen bytes into a 4.34.1 compilation.

## Reproduce

From the FIR worktree, set `BASELINE` to the immutable input directory. For the
current local archive it is:

```sh
BASELINE=/home/egallego/lean/fir/.worktrees/wasm-generation-4.34/.deps/native-session-probe/cached-prelude-fbaa6efc/direct-construction-packages/1c3b87b3f270114a3a56eeb7
mkdir -p .deps/utf8-adapter .deps/tmp
cp integration/vbp-native-session-probe/adapter/package.json integration/vbp-native-session-probe/adapter/package-lock.json .deps/utf8-adapter/
TMPDIR="$PWD/.deps/tmp" npm ci --prefix .deps/utf8-adapter --cache .deps/npm-cache --ignore-scripts
node integration/vbp-native-session-probe/adapter/check.mjs "$BASELINE"
```

The locked React packages are Node test dependencies only. They do not replace
the frozen VIR providers or become bundled consumer/runtime dependencies.
The check produces the package twice and requires identical identity, checksums
and bytes, then runs its copied smoke against actual Wasm and React SSR.
Final handoff packages must be made from a clean checkout; dirty development
outputs are explicitly identified as such. A package-only invocation is:

```sh
node integration/vbp-native-session-probe/adapter/package.mjs "$BASELINE" "$PWD/.deps/utf8-adapter/packages"
```

## Preserved invariants and controls

Scratch slots are JavaScript-owned and per-session, indexed by active conversion
depth. A slot stays leased through allocation: nested allocator reentry takes
another slot. A `finally` restores depth, and disposal clears retained scratch.
Header and destination views are acquired after allocation, preserving safety
under memory growth. Typed ABI, Boolean/string conversions, provider errors,
callbacks, retained sessions and fail-closed conversion semantics are unchanged.

The inherited smoke covers Unicode/NUL, checked/direct equivalence and SSR,
growth including grow(0), forced growth during allocation, nested allocator
conversion/distinct slots and later slot reuse, provider/callback reentry,
provider error identity, controlled encoding failure, session independence,
retention and disposal. Negative controls reject wrong frozen bytes, counterfeit
checksum inventories, and removal of depth leasing/reset/disposal clearing.
Client-owned Chromium and performance acceptance remain separate.
