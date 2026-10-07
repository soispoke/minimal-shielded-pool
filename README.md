# Minimal shielded pool

An immutable shielded pool for native ETH on the ethrex Hegotá testnet. It uses
EIP-8141 frame transactions, EIP-8250 keyed nonces and EIP-8272 recent roots.
It has no ERC-20 support, admin, governance or external paymaster.

> [!CAUTION]
> **For research and prototyping only.** This is not production software. Do
> not deploy it on mainnet or use it with real funds. See
> [SECURITY.md](SECURITY.md).

## How it works

A note commits to its owner, a random `rho` and its value:

```text
owner_pk = Poseidon3(1, spend_key, 0)
cm       = Poseidon3(2, Poseidon2(owner_pk, rho), value)
```

`PoseidonN` is circomlib's Poseidon over BN254 with N inputs, not the separate
Poseidon2 hash.

A spend proves a join-split with two inputs and two outputs. Its statement is
ten values: `[nf1, nf2, outCm1, outCm2, root, domain, publicAmount, fee,
recipient, authorizer]`. To save verification gas, the proof exposes three
public signals instead, using the hybrid compression of
[eprint 2025/1500](https://eprint.iacr.org/2025/1500): the pool computes
`alpha = keccak256(statement) mod r`, the circuit computes
`beta = Poseidon(statement)`, and both evaluate `gamma`, the statement as a
polynomial at `alpha + beta`. The ten values stay public in the settlement
data. The pool recomputes `alpha` and `gamma` from them and range-checks each
value itself, since the verifier no longer sees them. The circuit derives each nullifier from its input note and checks that
every positive input is in the tree, that value is conserved over 128-bit
amounts, and that at least one input carries value. It also requires distinct
nullifiers and outputs, a nonzero authorizer address, and a recipient exactly
when `publicAmount` is positive. A zero-value output must use a fixed "sink"
commitment for its position, which the pool never inserts.

Every note is identified by its tree epoch and leaf index. The nullifier binds
that position, so two notes with the same commitment are spent independently and no uniqueness registry is needed:

```text
D  = keccak256(domain_tag || chain_id || pool || epoch) mod r
nf = Poseidon3(4, Poseidon2(D, spend_key), Poseidon2(cm, leaf_index))
```

Here `domain_tag = keccak256("minimal-shielded-pool:occurrence-domain:v1")`,
each field is 32 bytes and `r` is the BN254 scalar field order. The pool
checks that `D` uses the epoch of the root the spend proves against, so each
note has exactly one nullifier. Wallets must track notes
by position and rebuild positions after a reorg.

## Transactions

The pool is the sender and payer of every spend. The two nullifiers are the
transaction's EIP-8250 nonce keys at sequence zero, so the protocol rejects a
second spend of either note. A spend has three frames and an optional fourth:

1. `VERIFY(0x…8272, tuple)`: EIP-8272's recent-root check of the
   `(source_id, slot, root)` tuple for the root the proof uses. The slot is the
   EIP-7843 `slotNumber` of the block that published the root.
2. `VERIFY(pool, proof)`: the pool checks the proof, binds it to that tuple,
   and checks the frame layout and the settlement frame's gas limits. It then
   approves execution and payment.
3. `SENDER(pool, settle(Spend) || notes)`: settlement inserts the outputs,
   records any withdrawal as a credit for `recipient` and emits the notes (see
   [Note delivery](#note-delivery)). It never publishes a root or
   calls the recipient, and the pool's `VERIFY` rejects anything settlement
   would refuse. Its gas limits must cover the worst tree shape, because running
   out after approval burns the notes. The pinned limits come from
   measurement, not a proof.
4. Optional `DEFAULT` call: any nonzero target, including the pool, and any
   calldata, with zero value and flags. A withdrawal usually calls
   `claimWithdrawal(recipient)`. A transfer can call `publishEpochRoot` so the
   notes it creates can be spent from the next slot, though a spend against
   that root is then easy to link to the transfer. It must name the epoch its
   outputs land in, which is a new epoch if settlement starts a new tree.
   Naming the old epoch succeeds but leaves them unpublished.

The dispatcher pins the data length of the first three frames and the
settlement frame's gas limits. The validation frames' gas limits are wallet
defaults, except the recent-root frame's state limit, which EIP-8272 requires
to be zero. A limit that is too low only makes the transaction invalid, and
the proof's fee covers whatever is declared. Wallets can therefore raise these
limits after a gas repricing without a new pool, as long as the proof check
still fits the 500,000 gas the pool forwards to the verifier. Settlement's
limits are pinned, so a repricing that makes settlement more expensive needs a
new pool. Wallets should keep the defaults, since a spend with different limits
stands out.

| Frame | Execution gas | State gas | Data |
|---|---:|---:|---:|
| Recent root | 8,000 default (uses 5,579) | 0 pinned | 72 bytes |
| Proof | 225,000 default (uses about 210,000) | 195,840 default | 288 bytes |
| Settlement | 2,000,000 pinned | 550,000 pinned | 484 or 1,572 bytes |

The settlement frame's data is the 388-byte `settle(Spend)` call followed by
96 note bytes, or 1,184 on a sender's first payment to a public address.
The proof frame's data is the 256-byte proof followed by `beta`. It needs a
limit of about 216,000, although it uses about 210,000, because each nested
call keeps back 1/64 of its gas (EIP-150). Below
that, the verifier runs out of gas and the pool reports an invalid proof. The
proof frame's state gas pays for creating the two nullifier keys.

The proof names a secp256k1 authorizer, which the wallet makes fresh for each
spend. Its signature covers the
whole transaction, including the proof, the recent-root tuple and the fourth
frame. The proof's `fee` must cover the transaction's maximum cost; any unused
part stays in the pool.

The wallet chooses the fourth frame's limits. Intrinsic gas plus every frame's
execution limit, or the calldata floor when larger, must fit EIP-7825's `2^24`
cap, of which the pool's own frames use 2.23M by default; state gas is
budgeted separately. The encoded transaction must also fit ethrex's 128 KiB
mempool limit.

If the fourth frame fails or is left out, settlement still stands, and a
withdrawal remains as a credit that anyone can pay out later with
`claimWithdrawal(recipient)`. A failed fourth frame makes the receipt's overall
status 0 even though settlement succeeded, so check each frame's status. The
claim pays `recipient` with a plain ETH transfer and cannot redirect it, so a
recipient that rejects plain ETH transfers strands the credit.

An account called by the fourth frame sees EIP-8141's entry point as its caller, so it must
authenticate its own owner. This is a direct account call, not an ERC-4337
adapter. See [SECURITY.md](SECURITY.md#generic-default-tail).

When the current tree lacks room for the notes being inserted, the pool starts
a new epoch first, for shields and settlements alike. Sinks take no space, so a
full tree never blocks a full withdrawal. Anyone may publish the pool's current or final
epoch root to EIP-8272.

## Note delivery

A recipient needs each note's amount and `rho` to spend it. Notes carry them on
chain, encrypted under a 32-byte secret `K` that the sender and recipient share,
so a payment can go to a reusable address and the recipient can recover
everything from its seed. `sdk/notes.py` implements the format with
ML-KEM-768 and ChaCha20-Poly1305 from `cryptography` (OpenSSL):

```text
note = tag (16) || ChaCha20-Poly1305(value) (16 + 16)
tag  = PRF(K, "tag", i)[:16]    rho = PRF(K, "rho", i) mod r
```

`i` counts the notes a sender has sent with `K`. A sender sets up `K` in one of
two ways, and later payments look the same whichever it used:

- **Public address** (a version byte, `owner_pk` and an ML-KEM-768 key,
  1,217 bytes, shared by ENS or QR): no prior contact. The payment that opens
  the channel carries the 1,088-byte ML-KEM ciphertext, which the recipient
  decapsulates. Two transactions carrying the same ciphertext would be linked,
  so until that payment is final, another payment to the same recipient opens
  a new channel.
- **Out of band:** the recipient issues the next numbered secret from its seed
  with `direct-secret` and sends it to the sender over Signal or another
  post-quantum channel. The wallet state records each number, so that it goes
  to one sender. Nothing extra goes on chain.

Every spend carries two notes, one for the payee and one for the change (a
withdrawal's payee note is random). A shield carries one. The pool only
checks their length and emits them in a `Notes` event; the one-time
authorizer's signature covers them. The CLI refuses a spend or shield whose
fixture lacks the wallet's notes.

Wallets download every event and look for the tags they expect, so no server
learns which notes are theirs. From its seed alone a wallet rebuilds its
incoming and change notes: it re-derives its secrets, decapsulates every
ciphertext and matches tags, and it tracks their spends by nullifier. A sender
cannot recompute an outgoing secret, so after a restore it opens a new channel
with each recipient. The change channel cannot be reopened, so a restored
wallet, or a device taking over sending from the account, rebuilds it with
`notes.self_channel`, past the indices it may have used. A sender reserves an
index in its saved state before broadcasting a new payment, because a repeated
index repeats the tag, key and `rho`, and retries a payment that did not land
with the same note. It also keeps fewer than 20 payments per channel past the
last one it has seen final, since the recipient watches 20 indices ahead.

```sh
python3 sdk/notes.py address --seed-file SEED
python3 sdk/notes.py scan --config CONFIG --state STATE --seed-file SEED
python3 sdk/notes.py direct-secret --config CONFIG --state STATE --seed-file SEED
```

`scan` and `direct-secret` need the config of a `position-notes-v3` pool. No
such deployment exists yet, and `core/deploy_config.json` records the v2 pool,
which publishes no notes.

The seed file must be readable by its owner only; without `--seed-file` the
seed is read from the terminal. `scan` reads finalized blocks only and keeps
its state in an owner-only file. It reads every shield and settlement apart,
even several in one transaction. A node may leave a call's logs out of
`eth_getLogs`, as ethrex does for every log of a frame transaction whose
fourth frame failed. Once a later leaf shows the gap, `scan` rebuilds the call
from block receipts, and it stops if leaves are still missing rather than hide
notes. `direct-secret` needs a state
that has been scanned, and hands out numbers only within 20 of the highest one
paid, which is how far a scan from the seed looks. History older than
Ethereum's retention window (EIP-4444) comes from archives, as it already does
for the tree leaves.

A normal spend grows by 96 bytes and about 4,000 gas, and an inclusion list
still holds four spends. A first payment to a public address grows by
1,184 bytes and is visibly larger. See [SECURITY.md](SECURITY.md#note-delivery).

## Layout

```text
core/          what is deployed and what the formal proofs cover, with the
               activation manifest and the deployment record
  circuits/    the spend circuit
  contracts/   the Foundry project: settlement logic, verifier, Poseidon, tests
  dispatcher/  the Yul dispatcher, the pool's own account code
  artifacts/   R1CS, WASM, proving key, verification key, dispatcher initcode
sdk/           Python client: wallet, note delivery, transaction builder and
               CLI, disclosure receipts, fixture generators
test/          Python tests, fixtures, vectors and the native ethrex suite
tools/         setup, deployment, generators, activation and formal-pin
               checks, and the pinned npm toolchain
evidence/      dated records of earlier devnet runs and reviews
docs/          design notes
```

[docs/design.md](docs/design.md) explains why the pool is built this way and
what a change to the tree or the statement has to touch.

## Disclosure receipts

`sdk/disclosure.py` lets a user show, after the fact, where funds in the
pool came from and where they went, like Tornado Cash's compliance tool but
without giving anyone the power to spend. For each note you spent, a receipt
gives its nullifier key `K = Poseidon2(D, spend_key)`. With `K` and the
note's position, anyone can confirm on chain which spend used up the note,
but `K` cannot spend anything. A receipt can follow notes from a public
deposit through private transfers to a withdrawal, and fully explains a
spend when both of its inputs are disclosed.

```sh
python3 sdk/disclosure.py export --rpc URL --config core/deploy_config.json \
  --fixture FIXTURE --only CM[,CM...] --output receipt.json
python3 sdk/disclosure.py verify --rpc URL --config core/deploy_config.json \
  --receipt receipt.json
```

Export discloses only the notes you name, and gives a nullifier key only for
notes you spent. Notes paid to one address share its spend key, so their
nullifier key shows when any of that address's notes in the epoch is spent;
export refuses such a key unless you pass `--address-wide`. Verify checks the receipt against finalized blocks and the
pool's deployed code. It trusts its config and its node, so use your own copy
of the config and a node you control; a public node also learns which
transactions you look up. A receipt proves links and amounts, not who
presents it or where the funds came from before the deposit. See
[SECURITY.md](SECURITY.md#privacy-limits) for what a receipt reveals.

## Deployment

This is pool profile `position-notes-v3`. It follows EIP-8141 at
`7d1c8bfb94`, EIP-8250 at `f3079a09e8` and EIP-8272 at `824cbc0b0e`: an eight-field envelope
with separate execution and state gas limits for each frame. Because the EIPs
are drafts, each supported combination is a separate profile, and profiles are
not wire compatible. The format chain 8141 used before its relaunch is archived byte for byte
under `evidence/vectors/2026-09-01-hegota-final-profile/`.

Each profile needs its own deployment, because a deployed pool cannot be
upgraded. A `position-notes-v2` pool rejects this profile's settlement and
shield calldata, which carry notes. This profile has no deployment yet:
`core/deploy_config.json` still records the `position-notes-v2` testnet
deployment on chain 8141 (pool `0xcb83…0e86`, commit `08bb034`), which
completed shield, transfer, withdrawal and claim calls on September 25, 2026,
and the CLI refuses to shield into or spend from it. The earlier
`position-notes-v1` pool (`0xac01…b100`, commit `c26b8e4`) stays on chain too.

Before shielding or spending, the CLI requires the config to name this profile
and checks the pool itself: the RPC must be on the configured chain, the pool's
code must be exactly what this profile's dispatcher deploys when linked to the
logic and verifier the config records, and its `domain(uint64)` must match the
profile's formula. The code check matters because both profiles share the
domain formula. The linked verifier must also accept a reference proof and
reject it with `gamma` changed. These checks catch a stale or mislabeled config,
not a malicious deployer: they trust the config's logic and verifier, which the
deployment script verified, and cannot see what a pool's constructor wrote to
storage. Before depositing into a pool someone else deployed, check its
deployment transactions.

A shield also refuses a fixture made for another chain, pool or epoch, or one
whose note would not land at the leaf and on the tree its proofs expect.
Before sending, and with `--dry-run`, the CLI gives the RPC the fully signed
transaction for simulation, and the RPC could broadcast it. Use an RPC you
trust.

The public mempool counts the two validation frames' declared limits plus
2,800 gas for the signature: 235,800 by default, while a spend uses about
218,500. That is well above EIP-8141's published default of 100,000. The chain
8141 testnet admits it; other networks need a policy that does.
[EIP-8369](https://eips.ethereum.org/EIPS/eip-8369) has not settled a
per-transaction budget.

## Test

With [just](https://just.systems) installed:

```sh
just install   # the pinned npm toolchain and the Python dependencies
just test      # what CI's test job runs
```

`just --list` shows the other recipes: the native suite, the formal-pin report,
Poseidon regeneration and deployment. The [justfile](justfile) lists every
command they run.

The tests rebuild the circuit and require byte-identical R1CS and WASM. The
committed artifacts come from circom2 0.2.8; 0.2.23 does not reproduce them
byte for byte, so a compiler upgrade means a new reviewed artifact set. 
`tools/setup.sh` runs a new single-party test setup, not a ceremony. Run it
only to replace the test setup on purpose, then rebuild the activation manifest
and proof fixtures. The activation gate checks that the proving key's A and B
terms come from the committed R1CS and that the verifier holds the key's
verification key; the rest of the key needs the phase-1 file (`--ptau`, see
[SECURITY.md](SECURITY.md)).

The native tests in [`test/native/`](test/native/README.md)
run real proofs through the pinned ethrex VM. They cover duplicate notes,
replay, a reorg simulated by database rollback, settlement gas and the fourth-frame rules, but not networking,
other clients or FOCIL.

A Lean formal verification of this pool at `8835be7` lives in
[verified-shielded-pool](https://github.com/soispoke/verified-shielded-pool),
with its own CI. It is checked out as `formal/` inside a pool checkout, which
git ignores here. CI's `formal-pins` job warns, without failing, when a change
touches a file those proofs pin (`python3 tools/check_formal_pins.py`).

See [SECURITY.md](SECURITY.md) for trust and failure boundaries.
