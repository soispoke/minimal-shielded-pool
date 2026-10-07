# Design

This note explains why the pool is built the way it is, so that a change does
not break a rule something else depends on. [README.md](../README.md) says what
the pool does, and [SECURITY.md](../SECURITY.md) lists its trust and failure
boundaries.

## The rule behind most others

A spend has a validation frame, which checks the proof and approves the
transaction, and a later frame that settles it. Approval consumes the spent
notes' nullifiers, the tags that mark a note as spent. Anything that makes
settlement fail after approval therefore burns the notes. That is why
validation re-checks everything settlement could refuse, and why settlement's
gas limits are pinned.

## The pool is the sender

EIP-8250 nonce keys belong to a transaction's sender. With the pool as the
sender of every spend, a spend's two nullifiers are its nonce keys at sequence
zero, and the dispatcher requires exactly those keys. The protocol then rejects
a second spend of either note without the pool keeping its own record of spent
notes. The pool also pays the gas, out of note value, through the proof's
`fee`.

Validation needs EIP-8141's new opcodes, which Solidity cannot emit, so the
dispatcher (`core/dispatcher/ShieldedPoolDispatcher.yul`) is written in Yul
with `verbatim`. It checks the frame layout, the nonce keys, the recent-root
tuple, and that the transaction's one signature comes from the proof's one-time
`authorizer`. It calls the verifier directly, because ethrex forbids a
delegatecall inside a VERIFY frame, and then approves. Every other call is
delegatecalled to `ShieldedPoolLogic`, which shares the dispatcher's storage
and refuses direct state-changing calls.

## Notes are occurrences

The nullifier binds a note's epoch and leaf index, not only its commitment:

```text
nf = Poseidon3(4, Poseidon2(D, spend_key), Poseidon2(cm, leaf_index))
```

Here `D` hashes the chain ID, the pool and the epoch of the root the spend
proves against. Two deposits of the same commitment are therefore two notes,
spent independently, with no uniqueness registry and no storage read during
validation. PR 14 made this change because a duplicate output could otherwise
revert settlement after approval. The commitment stays in the formula so that a
zero-value dummy input, whose tree membership is not checked, cannot copy a
funded note's nullifier.

Any replacement tree must keep this property. Each insertion gets one position
that the circuit authenticates, and no root the pool accepts may authenticate
the same insertion at another position, or one note gets two nullifiers. A new
nullifier formula needs a fresh deployment.

## The statement is compressed

A spend's statement is ten values (`nf1, nf2, outCm1, outCm2, root, domain,
publicAmount, fee, recipient, authorizer`), all in the settlement calldata.
Groth16 verification costs gas per public input, so the proof exposes only
three, using the hybrid compression of
[eprint 2025/1500](https://eprint.iacr.org/2025/1500). With `r` the BN254
scalar field order, the pool computes `alpha = keccak256(statement) mod r`, the
circuit computes `beta = Poseidon(statement)`, and both evaluate `gamma`, the
statement as a polynomial at `alpha + beta`. This saved about 44,100 gas per
spend (PR 19).

The verifier no longer sees the ten values, so the dispatcher range-checks each
one. Without that, a note owner could re-prove a spend with a value plus `r`.
The proof would still verify, so the pool would approve and pay the gas, and
settlement, which re-checks the values, would then revert. An aliased
nullifier gives fresh nonce keys, so the pool would pay each time, and an
aliased output, amount or fee spends the owner's notes without creating
anything. The wallet, the dispatcher and the circuit must agree on the order and
encoding of the values, and a mismatch shows up only as an invalid proof.

## Roots come from EIP-8272

The first frame runs EIP-8272's recent-root check on a `(source_id, slot,
root)` tuple, and the dispatcher requires that tuple to name the spend's root
and `source_id = keccak256(pool || epoch)`. Validation therefore never reads
pool storage. This matters because every spend has the same sender, and ethrex
lets several of one sender's frame transactions wait in the mempool only when
their nonce keys are disjoint and their validation reads no sender storage. The
tuple also keeps a proof valid for EIP-8272's window while new deposits change
the tree. Anyone can publish a root with `publishEpochRoot`, outside
settlement, so a failed publication never consumes note keys. When the
depth-20 tree lacks room for the notes being inserted, the pool starts a new
epoch first, so settlement never fails for lack of room.

## Settlement gas is pinned

The dispatcher pins the settlement frame at 2,000,000 execution gas and 550,000
state gas, because running out after approval burns the notes. The highest
settlement the native suite measures, carrying a first payment's notes, is
1,435,539 gas, so the limit is a measurement with margin, not a proof. The
validation limits are wallet defaults in `sdk/gas_profile.py`, because a
validation limit that is too low only makes the transaction invalid before any
key is consumed. A repricing that makes settlement more expensive needs a new
pool. A repricing of validation needs only new defaults and a regenerated
manifest, as long as the proof check still fits the 500,000 gas the dispatcher
forwards to the verifier.

## The client and its cross-checks

The client in `sdk/` is Python. It calls snarkjs to prove, Foundry's `cast` to
encode calls and `cryptography` (OpenSSL) to encrypt notes, and JavaScript
appears only in the pinned circuit toolchain in `tools/`. Because the client
reimplements Poseidon, the tree, the statement and the transaction encoding,
the tests check it against independent sources: Poseidon against circomlibjs
vectors, witnesses and statements against the committed R1CS and a real proof
(`test/test_occurrence.py`), the smoke fixture's proof against the Solidity
verifier in Forge, and the whole pool with real proofs and signed transactions
in the pinned ethrex VM (`test/native/`).

## Changing the tree or the statement

A change to the tree or the statement touches all of these:

- the circuit, then the artifacts and the verifier (`tools/setup.sh` runs a
  test setup, not a ceremony);
- the dispatcher's statement handling, its frame data length pins (288 bytes
  for the proof, 484 or 1,572 for settlement with its notes), the `settle`
  selector and the constructor's empty root;
- `ShieldedPoolLogic`'s tree constants, `Spend` struct, storage layout,
  insertion and epoch roll, the Forge tests and the Python tests in `test/`;
- the client: `sdk/wallet.py`, `sdk/pool_frametx.py`, `sdk/notes.py`, whose
  scanner rebuilds positions from `LeafAppended` and tracks spends by
  nullifier, and `sdk/disclosure.py`, which repeats the nullifier formula and
  the `Spend` fields;
- `sdk/poseidon_bn254.py`, `tools/export_vectors.js` and `test/vectors/`, if
  the change needs a new hash arity, and a new Poseidon library from
  `tools/gen_poseidon_sol.py` and `tools/split_poseidon.py` if the contracts
  need it too;
- the fixture generators: `sdk/gen_smoke.py`, `sdk/gen_nonce_race.py` and
  `test/native/scripts/generate_fixtures.py`;
- gas: re-measure the worst settlement in the native suite, then update the
  pins, `sdk/gas_profile.py` and the gas checks;
- the activation manifest, the activation check's profiles, a new pool profile
  and a fresh deployment. The formal proofs stop covering the changed files
  until their pins are updated.
