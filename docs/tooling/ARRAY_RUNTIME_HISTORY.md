# Resident Array hot-path history

This note records the Git evidence behind FIR's resident `Array` performance
work. It distinguishes three costs that were easy to conflate:

1. element-address calculation;
2. validation of the Array object at each helper call; and
3. validation and decoding of proof-indexed indices.

## Finding

There was no earlier FIR-resident implementation that was both O(1) in the
index and free of repeated structural validation. The first resident Array
implementation already contained both the full call-local validator of its
time and an O(index) element-address loop. The history therefore does not show
a fast FIR helper becoming slow. It shows an initially defensive prototype
being generalized before its two independent hot-path costs were removed.

The last non-resident C or host route may be a useful performance baseline, but
it is not a previous implementation of `ResidentArray` and should not be
described as one.

## Source timeline

| Commit | Change | Hot-path consequence |
|---|---|---|
| `1e49136a` | Introduced `ResidentArray` for Illuminate. | `requireArray` checked heap range, alignment, flags, object kind, and marker on each supported call. `elementAddress` advanced one slot per loop iteration, so lookup was O(index). |
| `10a71ee8` | Added closure-selected `internalizeAvailable`. | The same checked helpers could be selected for a narrower source closure; neither cost changed. |
| `1ab73d0e` and `57ae699e` | Generalized closed-application linking and the Array/String helper frontier. | The defensive helper implementation became a generic compiler path. These commits broadened exposure but did not introduce its validator or address loop. |
| `6592e2cb` | Added upstream-faithful ownership and unique-update behavior. | `requireArray` was strengthened with live/persistent refcount checks, reserved-header checks, and `size <= capacity`. Correct copy-on-write semantics were restored, while validation and O(index) addressing remained. |
| `696dac3e` | Extended the mutation frontier. | More operations reused the same validator and loop-based `elementAddressFor`. |
| `1d79658d` | Replaced the address loop by `array + headerBytes + index * 8`. | Element addressing became O(1). A source guard fixes the slot width at eight bytes; later code also guards that the address sequence contains no symbolic Wasm loop. Structural validation still ran on compiled calls. |
| `da721bc3` | Split checked/public helpers from trusted typed closed-application helpers. | Closed compiled applications stopped repeating `requireArray`. Raw and public helpers retained malformed-address traps. Lean guards establish that trusted bodies are exactly checked bodies with the common validator prefix removed. Bounds, ownership, uniqueness, copy-on-write, allocation, and recursive release stayed in place. |
| `e9629e37` | Trusted erased proof premises for proof-indexed Array operations. | Typed `get`, `uget`, `set`, `uset`, and `swap` no longer reconstruct bounds proofs or route canonical immediate indices through the general Nat validator. Checked/public variants retain those checks. |

The first FIR state that combines O(1) addressing with the upstream-style
trusted compiled boundary is therefore `da721bc3`. For proof-indexed calls, the
complete trusted hot path is `e9629e37`.

## Current invariant boundary

The optimized path is not an unchecked public ABI:

- raw, standalone, and public helper selection uses checked Array functions;
- typed closed-application linking alone selects the trusted family;
- the linker rejects mixed checked/trusted Array policy;
- checked and trusted function bodies are compared by source guards;
- trusted proof-indexed bodies are guarded against general Nat decoding and
  redundant bounds-check sequences; and
- address generation is guarded against reintroducing a loop.

This follows Lean's native split: well-typed compiled calls consume the
representation and erased-proof invariants, while an exposed raw boundary
validates before reading memory. Removing checks from the raw boundary would be
a different contract change and is not justified by this history.

## Performance interpretation

The accepted `da721bc3` lean-zip experiment kept exact output and ownership
behavior. Its paired raw-entry medians improved about 2.6% at 64 KiB and 1.9%
at 256 KiB; 4 KiB was neutral. That result established a real but non-dominant
Array validation cost, not a broad explanation of the native gap.

The later checked 256-KiB level-6 CPU profile attributes 4.29% of Wasm self
time to resident Array helpers and 68.93% to resident numeric helpers. Array is
therefore no longer the leading optimization target for that workload. The
compiled Array microprobe remains useful as a semantic and mechanism ratchet,
especially for index independence and unique-versus-shared updates.

## Reproducing the archaeology

The relevant source history can be inspected without building artifacts:

```text
git log --first-parent --oneline -- Fir/Wasm/Emit/ResidentArray.lean
git show 1e49136a:Fir/Wasm/Emit/ResidentArray.lean
git show 6592e2cb:Fir/Wasm/Emit/ResidentArray.lean
git show 1d79658d:Fir/Wasm/Emit/ResidentArray.lean
git show da721bc3:Fir/Wasm/Emit/ResidentArray.lean
git show e9629e37:Fir/Wasm/Emit/ResidentArray.lean
```

No semantic bug card is associated with this note: the historical issue was a
performance architecture problem, and the checked public semantics remained
intentional.
