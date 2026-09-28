# wasm-gen lane

Generic resident limb multiplication, ROOT-W7-20260928-002.
Root owns integration; math-browser owns matched consumer timings/full-suite acceptance.

```text
lane: wasm-gen
owner: fir/wasm-gen
branch: wasm/nat-mul-4341
worktree: .worktrees/wasm-nat-mul-4341
state: ready
base: a30ae0e173fccb2b5a94245bf72f5011ea8b5322
functional-head: f6c43d07e98a15eee870fe53235dcdf5cf31aeb5
contract-base: c32fdb8d3e9b89ab99643deaf456f5452f6217d6
clean-at-update: true
slice: General base-2^32 schoolbook Nat multiplication within the unchanged 64-bit limb representation.
files: Fir/Wasm/Emit/ResidentNatMultiplication.lean; ResidentNatArithmetic.lean; Tests/; this snapshot
contracts: none; existing signature, canonical layout, borrowed inputs and exact-extent recycler retained
checks: Runtime head eaa1a5e6 passes make check, make talos-setup/check, full deterministic artifact gate, focused build, raw/O3 Node differentials. Packaging d282b668 and full/trimmed-reuse fixture f6c43d07 leave runtime source/bytes unchanged; package checksum/smoke and focused tests pass. Serial make check passes again at f6c43d07; Talos and artifact gates also rerun green on unchanged runtime. Beam helper/test/arithmetic sync+save pass after refresh resolved an initial umbrella timeout.
bug-cards: none
blockers: none for generation-ready candidate
handoff: Clean exact containing checkpoint is pinned in the canonical completion; root alone reviews/lands. No consumer release/pointer, pin, ABI, W6 source, or push changes.
next: Root review/integration and client-owned matched stable-4.34.1 timing/full suite; no multiplication-refinement claim.
```

The generic helper no longer repeatedly doubles/adds whole Nats. Each digit
accumulation fits unsigned i64 exactly; the high 32 bits are its carry.
One upper-bound result extent is allocated, with a second exact allocation only
when canonicalization requires trimming. One-limb results use existing
`makeNatural`. A result equal to an input receives its owned reference via the
existing increment helper. Under-construction buffers never reach Nat consumers.

The unchanged production arithmetic fixture grows from 22,142 to 22,613 bytes
raw (+471), and from 15,837 to 16,064 bytes under the same Binaryen `-O3` (+227).
These are same-toolchain fixture sizes, not consumer speed measurements.

Focused raw and O3 tests pass 1,828 products each, including aliased/shared values,
maximal carries, uneven lengths, canonical boundaries and malformed inputs.
Both also pass 2,000 poisoned-payload reuse rounds with flat warm frontiers.
Final diagnostic frontier is 118,776 bytes; arena capacity is 131,072 bytes.
Persistent promoted outputs retain the existing non-reclaiming convention.

The immutable local package is
`.deps/packages/nat-mul-d282b6681129620b0f8052fab38fd4d7ee045f24-c02d47a8aa15/`.
Its standalone smoke verifies every checksum and 80 oracle products for each
binary. Raw diagnostic: 22,650 bytes,
`c02d47a8aa15fab69e29f612e634ad7d235f45a54806efbb20da3b184f8b26ee`.
O3 diagnostic: 16,239 bytes,
`0be3dbe599216e6f3d5bda2d894210fc3b73a75b403c1cb233596a0c732023f0`.
Both define memory and have zero imports. Diagnostic helper exports are not a
consumer ABI. Reproduction is in `Fir/Wasm/Emit/Tests/README.md`.

The former checked final-LCNF handoff remains immutable on
`wasm/lcnf-reification-434`; the UTF-8 producer remains preserved at `05671f39`.
Neither branch nor its packages were changed by this task.
