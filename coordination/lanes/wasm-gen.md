# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 7637dd95 on main
functional-head: c12dba9c, decode tagged Nat inputs directly in USize conversions while repairing the arbitrary-limb fallback
contract-base: 7637dd95. No Lean semantic, semantic Wasm ABI, resident-helper signature, symbolic-module, source entry, adapter API, ownership contract, or arena contract changed. The USize helper implementation now consumes the already-linked ResidentBigNumeric validation/accessor contract instead of the older one-limb-only ResidentNumeric accessors
clean-at-update: true
slice: USize.ofNat and USize.ofNatLT dispatch canonical tagged Nats through direct payload decode and i64 extension. Promoted and arbitrary-limb inputs use checked ResidentBigNumeric limb-zero access, so values wider than 64 bits now reduce modulo 2^64 instead of trapping. Exact release profiles lower lean-zip 256-KiB seeded-random level-6 medians from 270.49/284.03 ms to 219.84/220.72 ms, about 19%/22%; USize.ofNat combined self samples fall about 61%, with identical compressed bytes and a flat frontier
files: Fir/Wasm/Emit/ResidentUSize.lean; integration/talos/artifact/resident-fixed-width-client.mjs; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/README.md; bugs/FIR-BUG-wasm-none-usize-ofnat-arbitrary-natural.md; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. The package has zero function and memory imports, module-owned memory, and the existing five function exports plus memory. Reviewed artifact-only ratchets are frontier bytes 1619270 to 1619354, complete bytes 936061 to 936077, final function-index digest 3c9ca42902c9dc5afec95117719ee278da5d358ed15d550617622511d178efe9, and sidecar digest f1ac6dd38b8b068ddd85b1cdc52ba561c04a4524c9f2dde1e93647dc059d11b5
artifacts: clean FIR producer c12dba9c619743b8477f129a69c29d01b8d9581b, lean-zip source 273d0d6cd9cab77c7f3489b0b0b1f6e543315d21, and zipCommon 4425bab1f9522307d77e8d485bc536149ba31c36. Immutable local preview .deps/evidence/lean-zip-numeric/usize-clean-package has package ID c12dba9c6197-273d0d6cd9ca-a2e10ca4130c28c1ac4b. Its 936077-byte Wasm SHA-256 is ba9eb0be837382a3586310ac40e4a9e6a1868605ac87db40986923ff3a247637; its 999568-byte sidecar SHA-256 is f1ac6dd38b8b068ddd85b1cdc52ba561c04a4524c9f2dde1e93647dc059d11b5
checks: All accepted temporary state, profiles, source views, and packages are persistent under the W7 worktree; active commands fixed TMPDIR to .deps/tmp. Lean Beam sync/save PASS with zero diagnostics. Focused ResidentUSize and ResidentFixedWidth builds plus the real-Wasm fixed-width fixture PASS for immediate boundaries, promoted one-limb values, and arbitrary limbs. Deterministic package generation, exact sidecar verification, five inputs x levels 1--10 native/Wasm byte comparison, independent inflate, zero imports, rewind, and flat warm frontier PASS. git diff --check PASS. make check PASS: 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 190 active bug cards. make talos-check PASS 3162 jobs. bash integration/talos/artifact/check.sh PASS, including all 44 concrete artifacts and all 15 source probes
bug-cards: FIR-BUG-wasm-none-usize-ofnat-arbitrary-natural, fixed with a permanent resident-helper regression
blockers: none. The lean-zip lane retains the independent Chrome and order-balanced FIR-native/FIR-C acceptance campaign
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head c12dba9c is based directly on 7637dd95. No W6-owned file or shared signature changed, and no push, canonical-pointer advance, or external package publication is authorized
follow-up: request W6 adaptation for the stable USize conversion bodies. The next profile-selected W7 candidate is immediate-immediate Nat.mul; its generic checked arbitrary-precision fallback must remain unchanged
```
