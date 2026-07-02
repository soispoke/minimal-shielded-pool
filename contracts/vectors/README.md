# Differential vectors

`poseidon16_vectors.json` is exported from leanVM at the pinned commit
`12e6151` by `../reference/export_vectors.patch`: 32 permutation vectors and
32 compression vectors (zero state, unit state, counter state, and 29
LCG-seeded states), plus one pool chain (seeded `spend_key`/`rho`/`root`/
`out_cm`/`ctx` with the resulting `owner_pk`, `cm`, `nf`, `claim`).

To regenerate:

```
git clone https://github.com/leanEthereum/leanVM && cd leanVM && git checkout 12e6151
git apply /path/to/reference/export_vectors.patch
cargo test -p koala-bear --release export_poseidon16_vectors -- --nocapture
# copy the JSON between VECTORS_BEGIN/VECTORS_END here
```

Consumed by `../test/Poseidon16Vectors.t.sol` (forge) and
`../reference/poseidon16.py` (python3). All values are canonical (< p) decimal
field elements.
