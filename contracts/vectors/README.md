# Differential vectors

`poseidon16_vectors.json` is exported from leanVM at the pinned commit
`12e6151` by the `export-vectors` binary in [`../../prover/`](../../prover/):
32 permutation vectors and
32 compression vectors (zero state, unit state, counter state, and 29
LCG-seeded states), plus one pool chain (seeded `spend_key`/`rho`/`root`/
`out_cm`/`ctx` with the resulting `owner_pk`, `cm`, `nf`, `claim`).

To regenerate (leanVM is fetched automatically as a pinned git dependency):

```
cd ../../prover && cargo run --release --bin export-vectors > ../contracts/vectors/poseidon16_vectors.json
```

Consumed by `../test/Poseidon16Vectors.t.sol` (forge) and
`../reference/poseidon16.py` (python3). All values are canonical (< p) decimal
field elements.
