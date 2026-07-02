# pool-prover — Sepolia milestone 2: prove and verify spends as a tool

The spend circuit, graduated from a test patch into a first-class crate.
leanVM is a git dependency pinned to the same commit the numbers were measured
on (`12e6151`), and the circuit source is not duplicated: it is extracted at
compile time from [`../circuits/spend.py`](../circuits/spend.py), whose own
drift guard ties it to `pool_circuits.patch`. A crate test closes the loop by
checking the extraction against the patch, so all three copies are one.

## Binaries

```
# prove a spend from a wallet witness (JSON in, publics + proof out):
cargo run --release --bin prove-spend -- --in witness.json \
    --out publics.json --proof-out proof.json

# or from a deterministic demo witness (depth 20 transfer; --withdraw for the other op):
cargo run --release --bin prove-spend -- --demo 20 --out publics.json

# verify: recompute the claim from the publics (the contract's
# recompute-and-compare), then check the STARK against it:
cargo run --release --bin verify-spend -- --proof proof.json --publics publics.json

# regenerate ../contracts/vectors/poseidon16_vectors.json from leanVM itself:
cargo run --release --bin export-vectors > ../contracts/vectors/poseidon16_vectors.json
```

Witness JSON (all digests are 8 canonical u32 field elements; `bits[i] = 0`
means the current node is the left child; depth = `len(siblings)`):

```json
{"spend_key": [8 x u32], "rho": [8 x u32],
 "siblings": [[8 x u32], ...], "bits": [0 or 1, ...],
 "out_cm": [8 x u32], "ctx": [8 x u32]}
```

`prove-spend` derives the publics (owner_pk, cm, root, nf, claim), proves at
WHIR rate 1/2, self-verifies, and emits both array and packed-`bytes32` forms
(the canonical 8-big-endian-words encoding from
[../devnet/README.md](../devnet/README.md#encodings)), ready for the M3
contracts. The proof file is the `ExecutionProof` as JSON; `verify-spend`
exits 0 iff the claim binds the publics and the proof verifies.

## Tests

```
cargo test --release
```

runs the drift guards, the depth-20/32 transfer+withdraw prove/verify matrix
with tampered-claim rejection (the old `pool_circuits.patch` harness, now a
crate test that prints the measured numbers), and a proof serde roundtrip.

## Relation to circuits/

`circuits/pool_circuits.patch` remains the in-leanVM form of the same harness
(apply it inside a leanVM checkout); this crate is the primary workflow. The
`export-vectors` binary replaces the earlier vector-export patch: the
Solidity/Python differential vectors now come from the same pinned dependency
the prover uses.
