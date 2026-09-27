# Concrete Ethereum Keccak-256

`Hash.lean` defines Keccak-f[1600] with 24 rounds and a 1088-bit rate. Byte
inputs use the legacy Keccak delimited suffix `0x01` and `pad10*1`; SHA3-256's
`0x06` suffix is absent. State lane `x + 5*y` absorbs eight little-endian bytes.
The first 32 squeezed bytes form the digest, which `hash` reads as a big-endian
natural, as canonical SPEC D2 requires. `word` exposes the same value as
`BitVec 256`; `hash_lt` proves the bound without a cryptographic premise.

The definition follows the [Keccak reference v3.0, §1](https://keccak.team/files/Keccak-reference-3.0.pdf),
the team's [round and sponge summary](https://keccak.team/keccak_specs_summary.html),
and its [byte conventions](https://keccak.team/keccak_bits_and_bytes.html).
`rhoPi` uses the inverse of `B[y,2*x+3*y] = rot(A[x,y],r[x,y])`.
Every operation is a kernel-computable Lean `BitVec`/natural operation.

`vector_generator.py` constructs explicit round witnesses using a different
indexing method: the triangular-number rotation walk and an LFSR for round
constants. Every round witness is checked by ordinary Lean `decide`; proofs
then compose those equalities through padding, absorption, squeezing and the
big-endian conversion. The generator is not trusted by these proofs.

The fixtures cover empty input, ASCII `abc`, `addr20(1) ++ u256(0)`, ascending byte messages of lengths 135, 136 and 137, the three fixed domain
labels, and the occurrence domain for chain/address 1 and epoch 0. Python tests also cover arbitrary
byte messages across multiple rate blocks. Their expected digests are checked
independently with PyCryptodome Keccak and, when supplied, the pinned local
`js-sha3` 0.8.0 (`src/sha3.js` SHA-256
`13590a201b2199f00b74ee711edc1bdf744705dca12f43cc6ef64c32b5767fa9`).
A comparison explicitly rejects substitution of SHA3-256.

`Encoding.lean` proves `byteArray_toList` and `utf8_ofList` for conversion through Lean’s
standard UTF-8 API, whose well-founded byte loop is not directly reducible by
`decide`. `Labels.lean` connects the literal strings in the specification to
the checked byte fixtures. `Vectors.lean` exports `source_one_zero_eq` and
`source_one_zero_nondegenerate` (the result is at least `2^64`).
`Labels.domain_one_one_zero_eq` includes the domain-tag hash inside its exact
encoded preimage. These fixtures add no nondegeneracy assumption.

From `formal/`:

```sh
python3 Keccak/vector_generator.py --node-modules /path/to/tooling/node_modules
python3 -m unittest discover -s Keccak -p test_vectors.py -v
lake build Keccak
```

Pass `--write` only to regenerate the Lean witnesses. These checks establish
concrete reference computation and fixtures. They do not establish collision
resistance, nondegeneracy for arbitrary inputs, or equivalence to an EVM/client
Keccak implementation; the cryptographic assumptions and client semantics
remain separately scoped by the canonical specification.
