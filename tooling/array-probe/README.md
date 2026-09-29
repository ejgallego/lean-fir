# Ordinary compiled Array mechanism probe

This tooling-owned microprobe isolates four mechanisms without copying an
application benchmark into FIR: repeated reads from one persistent
`Array UInt32`, allocation-only construction, exclusive mutation, and mutation
while a pre-update alias remains live. All four entries are ordinary Lean
compiled through the generic final-LCNF and closed-application runtime paths.

Run the complete probe gate from the FIR root:

```text
make tooling-check
```

The target builds the ordinary Lean source with FIR's artifact-cache settings
and the same Lean toolchain as the FIR root (currently 4.34.1). A mismatched
nested pin fails rather than producing misleading evidence. The package records
a toolchain-specific input layout in `BUILD.json`. The target checks the raw
module, creates the optimized and stripped diagnostic artifact,
verifies identity capture against an unnamed control build, checks the final
module, and validates its final-function sidecar. All Lake, Binaryen, and
adapter scratch remains in this worktree's `.lake`, `.deps`, or `_build`
directories.

The equivalent focused command is:

```text
make -C tooling array-probe-check
```

`build.mjs` also compiles the unnamed control and requires it to be byte-for-
byte identical to the identity-captured release. `BUILD.json` binds source,
optimizer, Wasm, sidecar, import/export, layout, and ownership identities.

Run the optional local scaling diagnostic with stdout redirected to a JSONL
evidence file:

```text
node benchmark.mjs _build/package/array-probe.wasm
```

The correctness gate requires read calls to allocate nothing, exclusive
updates to have the same frontier growth as allocation alone regardless of
round count, shared mutation to preserve the pre-update value with the exact
toolchain-specific copy count, and every success or trap to rewind to the
persistent checkpoint. Under 4.34.1, a 16-element `Array UInt32` uses the same
`lean-4.34-Array-UInt32/v1` input layout as 4.34.0-rc2: a 32-byte resident
header, eight-byte element slots, and tagged immediate UInt32 values. The
raw 4.34.1 probe measured 160 bytes for allocation-only construction and for
unique mutation at 0, 1, and 64 rounds. Shared mutation measured 160 bytes
at 0 rounds and 320 bytes at 1, 4, and 16 rounds: the first shared update
copies, and later updates reuse the new Array. Reads allocated zero bytes;
trapped calls rewound and the next call succeeded. The packaged module must
pass the same ratchets. Timings remain raw diagnostics with entry
execution, rewind, and total kept separate. Each configuration uses a fresh
instance while sharing one compiled module. The client-owned lean-zip workload
and VIR browser catalog own comparative schedules, summaries, and performance
conclusions.
