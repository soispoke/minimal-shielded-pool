# Formal specification of the minimal shielded pool

This file states what the formal verification must prove about the pool. It is
the reviewed source of truth for the Lean statements in `formal/Spec/`, which
typecheck against Lean 4.35 and Mathlib and depend only on Lean's standard
axioms. Proofs come in later steps. Changing a claim or premise, here or in
Lean, needs the same review as changing the pool.

## 1. Scope

The subject is `main` at `8835be7`, pool profile `position-notes-v2`, fixed by
these artifacts (SHA-256, first 16 hex digits):

| Artifact | Hash |
|---|---|
| `build/spend.r1cs` | `e2f6fc89bc0e4782` |
| `build/spend_final.zkey` | `587c048b06d68c61` |
| `circuits/spend.circom` | `97c24b754549fd57` |
| `devnet/build/shielded_pool_dispatcher_init.hex` | `8339dab370f7fc24` |
| `devnet/ShieldedPoolDispatcher.yul` | `32e4701834435d21` |
| `contracts/src/ShieldedPoolLogic.sol` | `fa9d7b1fc5fdca83` |
| `contracts/src/Groth16Verifier.sol` | `5bcda629ac9fa431` |
| `contracts/src/PoseidonT3.sol`, `PoseidonT4.sol` | `f353af63ac124e51`, `2384b8f71a2ed09f` |

In scope: the circuit, the dispatcher, the settlement logic and the Poseidon
libraries, deployed together, and the safety of the funds they hold, including
that honest holders can always spend and be paid. Not in scope: privacy,
inclusion and mempool policy, the wallet, CLI and disclosure tooling, client
correctness, fee economics, and the honesty of the trusted setup, which is a
premise.

## 2. Definitions

**D1. Fields.** `p` is the BN254 scalar field order
`21888242871839275222246405745257275088548364400416034343698204186575808495617`
and `F = ZMod p`. For `x : F`, `val x` is its integer in `[0, p)`. `q` is the
BN254 base field order
`21888242871839275222246405745257275088696311157297823662689037894645226208583`.
A 256-bit word `w` is *canonical* when `w < p`.

**D2. Hashes.** `H2`, `H3`, `H10` are circomlib's Poseidon over BN254 with 2, 3
and 10 inputs, with the constants in `reference/poseidon_bn254.py`. `K(bytes)` is
Keccak-256 read as a big-endian integer. `u256(n)` and `uint64_be(n)` are the
32-byte and 8-byte big-endian encodings of `n` modulo `2^256` and `2^64`, and
`addr20(a)` is the 20-byte address.

**D3. Notes.** `pk(sk) = H3(1, sk, 0)`, `inner(sk, ρ) = H2(pk(sk), ρ)` and
`cm(inner, v) = H3(2, inner, v)`.

**D4. Domain.** `DOMAIN_TAG = K("minimal-shielded-pool:occurrence-domain:v1")`
and `D(c, a, e) = K(u256(DOMAIN_TAG) ‖ u256(c) ‖ u256(a) ‖ u256(e)) mod p`.

**D5. Nullifier.** `nf(d, sk, cm, i) = H3(4, H2(d, sk), H2(cm, i))`; `H2(d, sk)`
is the nullifier key.

**D6. Sinks.** `SINK_k = cm(k + 1, 0)` for `k ∈ {0, 1}`.

**D7. Merkle tree.** Depth 20. `Z_0 = 0`, `Z_{l+1} = H2(Z_l, Z_l)`,
`EMPTY_ROOT = Z_20`. `MR(leaf, i, s)` is the root reached from `leaf` at index
`i < 2^20` with siblings `s`, where bit `l` of `i` set puts the running node on
the right. `TR(L)` is the root of the complete depth-20 tree whose leaves are
`L` followed by zeros.

**D8. Statement.** `x = (nf1, nf2, o1, o2, r, d, pub, fee, rcp, auth)`.

**D9. Compression.** `α(x) = K(u256(x_0) ‖ … ‖ u256(x_9)) mod p`,
`β(x) = H10(x)`, `γ(x, s) = Σ_{j<10} x_j · s^j`.

**D10. Valid spend.** `R(x; w)`, for `w = (sk_k, ρ_k, v_k, i_k, sib_k, oi_k, ov_k)`
with `k ∈ {0, 1}`, holds when:

- **R1** `i_k < 2^20`;
- **R2** with `c_k = cm(inner(sk_k, ρ_k), v_k)`: `nf1 = nf(d, sk_0, c_0, i_0)` and `nf2 = nf(d, sk_1, c_1, i_1)`;
- **R3** if `v_k ≠ 0` then `MR(c_k, i_k, sib_k) = r`;
- **R4** `o1 = cm(oi_0, ov_0)` and `o2 = cm(oi_1, ov_1)`;
- **R5** `v_0, v_1, ov_0, ov_1, pub, fee` are below `2^128`, and `v_0 + v_1 = ov_0 + ov_1 + pub + fee` over the integers;
- **R6** `v_0 + v_1 > 0`;
- **R7** if `ov_k = 0` then `oi_k = k + 1`, else `oi_k ∉ {1, 2}`;
- **R8** `nf1 ≠ nf2` and `o1 ≠ o2`;
- **R9** `rcp < 2^160`, `0 < auth < 2^160`, and `pub = 0 ↔ rcp = 0`.

**D11. Frame transactions.** EIP-8141 at `7d1c8bfb94` with EIP-8250 at
`f3079a09e8` and EIP-8272 at `824cbc0b0e`: sender, `nonce_keys`, `nonce_seq`,
frames (resolved target, mode, flags, value, execution and state limits, data,
status), signatures (scheme, resolved signer, `msg`), blob hashes and
`max_cost`. Mode 0 is DEFAULT, 1 VERIFY, 2 SENDER.

**D12. Deployment.** A pool at `A` on chain `c`, whose runtime code is the
committed dispatcher initcode's output linked to a logic contract `L` and a
verifier `V`; `L` is `ShieldedPoolLogic` built with the pinned settings, linked
to the committed Poseidon libraries; after construction the pool's storage is
zero except slot 22, which holds `EMPTY_ROOT`.

**D13. Pool state** (the model). Per epoch `e` an append-only leaf list
`Leaves[e]`; the current epoch `E`; `finalRoot[e]` for `e < E`; credits; the
pool's balance; every EIP-8272 write as `(source_id, slot, root)`; the nonce
keys consumed for sender `A`; the current slot. Ghost fields, not on chain:
each leaf's value from its opening, the occurrences consumed, and the total
credited to and paid out to each recipient.

**D14. Occurrence.** A pair `(e, i)` with `i < |Leaves[e]|`.

**D15. Acceptance.** `Acc(A, c, tx)`, reading the settlement words of frame 2
(`root, rootSlot, epoch, domain, nf1, nf2, o1, o2, pub, fee, rcp, auth`):

- **A1 shape.** `sender = A`; 3 or 4 frames; one signature; no blob hashes; the executing frame is 1. Frame 0: target `0x…8272`, VERIFY, flags 0, 72 data bytes, succeeded, value 0, state limit 0. Frame 1: target `A`, VERIFY, flags 3, 288 data bytes, value 0. Frame 2: target `A`, SENDER, flags 0, 388 data bytes beginning `0x921fcac7`, value 0, limits 2,000,000 and 550,000. A fourth frame: nonzero target, DEFAULT, flags 0, value 0.
- **A2 keys.** `nonce_seq = 0`, two keys, and `TXPARAM(0x0F) = K(u256(2) ‖ u256(min(nf1, nf2)) ‖ u256(max(nf1, nf2)))`.
- **A3 root.** Frame 0's data is `u256(K(addr20(A) ‖ u256(epoch))) ‖ uint64_be(rootSlot) ‖ u256(root)`, with `epoch, rootSlot < 2^64`.
- **A4 signature.** Signature 0 has scheme 1, empty `msg` and resolved signer `auth`.
- **A5 statement.** `nf1, nf2 ≠ 0`; `root, domain, nf1, nf2, o1, o2 < p`; `pub, fee < 2^128`; `rcp < 2^160`; `0 < auth < 2^160`; `pub = 0 ↔ rcp = 0`; `domain = D(c, A, epoch)`.
- **A6 proof.** Frame 1's data is eight proof words below `q`, with none of `A`, `B`, `C` encoded as the point at infinity, then `β < p`; and the verifier's return value for `(π, [β, γ(x, α(x) + β), α(x)])` is 1.
- **A7 fee.** `max_cost ≤ fee`.

## 3. Premises

Every premise can be satisfied, and no premise assumes a hash function is
injective: a hash from `F^3` to `F` cannot be, and assuming it would make every
claim trivially true. Claims that rely on binding end in "or the run has a bad
event". A *bad event* counts only among what the run itself hashed: the sink
commitments the code hardcodes, the inputs of every approved spend's extracted
witness, every shield's commitment, every tree node of every root of every
prefix, every domain, root source and key-set hash, every foreign root write's
source, and any inputs a claim names explicitly. It is two distinct inputs with
equal outputs, an `H3` input whose output is 0 (the empty leaf), or a
compression break. Collisions that merely exist do not count. Every witness a
claim ranges over is fixed by an extractor quantified universally, never chosen
by the proof.

- **P1 Poseidon.** `H2`, `H3`, `H10` are the concrete functions of D2. Finding a Poseidon collision, or an `H3` input with output 0, among a run's queries is assumed infeasible.
- **P2 Keccak.** The same for Keccak collisions, and for distinct `(c, a, e)` with equal `D`.
- **P3 Groth16.** For the committed verification key and an honest setup, an extractor maps every accepted proof and public signals to a satisfying assignment with those public signals; every claim holds for every such extractor. Spend authority against mempool attackers, who see proofs before inclusion, needs Groth16's weak simulation extractability instead; that is a paper-level claim (§8). The current single-party setup does not meet P3.
- **P4 Hybrid compression** (eprint 2025/1500). A compression break is an approved spend whose extracted assignment proves a statement other than the settlement's. Its negligible probability is the paper's claim.
- **P5 EIP-8141.** A transaction is valid only if its `chain_id` is the chain's. Frames run in order. A VERIFY frame changes nothing but through `APPROVE`; if it fails, the transaction is invalid. `APPROVE` outside a VERIFY frame, or beyond its frame's allowed scope, halts; `APPROVE` with payment fails if the payer's balance is below `max_cost`. `APPROVE(3)` from frame 1 makes `A` sender and payer. A SENDER frame's caller is `sender`, a DEFAULT frame's the entry point. A failed non-VERIFY frame reverts only its own effects. `TXPARAM`, `FRAMEPARAM` and `SIGPARAM` return the EIP's table values, with EIP-8250's `TXPARAM(0x01) = nonce_seq`, `0x0E` = key count, `0x0F = K(u256(n) ‖ u256(k_1) ‖ … ‖ u256(k_n))`. Frame data read with `FRAMEDATALOAD` or, in the running frame, `CALLDATALOAD` is the frame's data. A `msg` is empty, signing the canonical hash, or a nonzero 32-byte digest, so `SIGPARAM(i, 0x02) = 0` exactly when signature `i` signs the canonical hash, which covers every field except the raw bytes of such signatures. The payer pays at most `max_cost`.
- **P6 EIP-8250.** Keys are 1 to 16 strictly increasing integers below `2^256`. A transaction is valid only if each key's sequence for `sender` equals `nonce_seq`; approval consumes every key atomically; an invalid transaction consumes nothing; consuming a key for the first time costs 97,920 state gas.
- **P7 EIP-8272.** A call from address `a` with data `salt ‖ root` writes the entry `(K(addr20(a) ‖ salt), slot) → root` for the current slot, replacing any earlier write for that pair; nothing else writes. The canonical frame 0 succeeds only if its tuple is the entry for its source and slot, with the slot strictly before the current slot and within 8,191 slots of it. Entries change otherwise only through a reorg; the model follows the canonical chain.
- **P8 Gas schedule and fork.** A pinned gas schedule `G`, with EIP-8037 state gas, EIP-2929 access costs and EIP-150's 63/64 rule. The claims hold while the chain keeps `G` and the pinned EIP revisions; a fork that changes them ends them.
- **P9 Deployment.** The pool is deployed as in D12 with the committed artifacts. The deployment script checks this; no proof does.
- **P10 EVM model.** The Lean EVM and Yul semantics, extended with EIP-8141 frames, EIP-8250 and EIP-8272, match the client, and every chain-level declaration in `Spec/Evm.lean` is defined from it.
- **P11 Chain identity.** The chain ID never changes on a chain that carries the pool's state.
- **P12 Signatures.** secp256k1 low-s ECDSA is existentially unforgeable, and the canonical signature hash is collision resistant. Used only to read C3's signature conclusion as "only the holder of `auth`'s key authorized this transaction".
- **P13 Bounded history.** Fewer than `2^64 − 1` epochs ever roll over. Credit totals stay below `2^256` by C5c.

## 4. Claims

**C1 Circuit soundness.** Every satisfying assignment of the pinned
`spend.r1cs`, whose wire 0 is 1, with statement `x`, private inputs `w` and
public signals `(β, γ, α)`, has `R(x; w)`, `β = H10(x)` and `γ = γ(x, α + β)`.
*Prevents* mints, overflows, fake membership, bad sinks and duplicate
nullifiers inside a proof.

**C1c Circuit completeness.** For every `x`, `w` with `R(x; w)` and every `α`,
some satisfying assignment has statement `x`, inputs `w` and public signals
`(H10(x), γ(x, α + H10(x)), α)`. *Ensures* every valid spend can be proven.

**C2 Approval.** Whenever code running at `A` executes `APPROVE` during a valid
transaction in a reachable state, it is frame 1 of a transaction whose sender
is `A`, the scope is 3, and `Acc(A, c, tx)` holds. *Prevents* approving a wrong
shape, keys, root, signer, statement, proof or fee, and paying for anyone
else's transaction.

**C2c Approval completeness.** The pool approves every valid transaction with
`Acc(A, c, tx)`, frame 1 limits of at least 216,141 execution gas (the measured
minimum under `G`) and 195,840 state gas (two first-use keys), and
`max_cost ≤ balance(A)`. *Ensures* honest spends are not rejected.

**C3 Approved spends are valid** (P3, P4, P5, P7). An approved spend's
extracted witness satisfies `R` for the settlement's own statement; the
transaction's keys are exactly `[min(nf1, nf2), max(nf1, nf2)]`; its root is
`TR` of a prefix of its epoch's leaves; and it carries `auth`'s signature over
the canonical hash, which with P12 means only `auth`'s key holder authorized
every field, including the fourth frame, the gas limits and the recipient.
All this, or the run has a bad event.

**C4 No burn.** An approved spend's settlement passes every revert condition
of `settle`, including the ABI decoder's, or the run has a bad event; with C7
it does not run out of gas, and with P13 and C5c no counter overflows.
*Prevents* burning notes whose keys approval has consumed.

**C5 System safety.** In every run of the model, unless it has a bad event:

- **C5a Leaves.** Every leaf opens to a value `0 < v < 2^128` and is no sink.
- **C5b Single spend.** Each nonzero-value input of an approved spend is an existing occurrence of the spend's epoch, holding the witness's leaf and value, not consumed before; a spend's two inputs differ.
- **C5c Solvency.** The pool's balance covers every unspent occurrence's value plus every credit.
- **C5d Credits.** Each recipient's credit is what it was credited minus what it was paid (holds with no bad event).
- **C5e Roots.** Every root written under one of the pool's sources, `K(addr20(A) ‖ u256(e))`, is `TR` of a prefix of `Leaves[e]`, with `e ≤ E`.
- **C5g No griefing.** A key an approved spend consumes that is some occurrence's nullifier, under any opening of its leaf, consumes that occurrence as one of the spend's inputs; the bad event may use that opening's hash inputs.
- **C5h Freshness.** An unspent occurrence's nullifier, under any opening, is not a consumed key; the bad event may use that opening's hash inputs.

**Spendability.** For every unspent occurrence with opening `(sk, ρ)`, every
root of a prefix of its epoch that contains it, every fee below its value,
every recipient and authorizer, and every dummy second input whose nullifier
key the run never hashed, the canonical full withdrawal of it satisfies `R` and
its keys are unconsumed, or the run has a bad event among its hashes and the
spend's. With C1c, C2c and C10, the holder can be paid.

**C6 Tree.** The contract's zero constants are `Z_l`, its `EMPTY_ROOT` is
`Z_20`, and its insertion and root computation from empty yield `TR` of the
inserted leaves.

**C7 Gas.** In every reachable state, an approved spend's frame 2 does not run
out of gas.

**C8 Libraries.** `hash2` and `hash3` return `H2` and `H3` within 200,000 gas.

**C10 Publication and claims.** In every reachable state anyone can call
`publishEpochRoot(e)` for every `e ≤ E` whose root is nonzero, and
`claimWithdrawal(r)` for every credited `r` that accepts a plain ETH call, and
the call succeeds. *Prevents* permanently locking notes or credits.

**Refinement.** Along every run of the chain from an honest deployment, for
every extractor that P3 admits, the model events its steps denote form a run
of the model; the chain shows that run's state (balance, credits, consumed
keys, epoch, leaf count, current and final roots, the logs of appended leaves,
the recent-root entries, the ETH paid to each address, the slot); ETH arrives
without a model event only in steps where no pool code ran; or the run has a
bad event. This gives C5f: nothing else changes the pool's state.

## 5. Main theorem

`MainTheorem` is C1, C1c, the model half (C3 to C5 and spendability, for every
extractor, from C1 and P3) and the chain half (C2, C2c, C6 to C8, C10 and
refinement). `Composes` states its meaning on the chain: along every run of an
honest deployment the pool is solvent, no occurrence is consumed twice, and
every root it wrote is a real root of its tree, or the run has a bad event.

## 6. Validating this specification

**Past bugs.** Every safety bug found earlier must violate some claim:

| Past bug or fix | Claim that catches it |
|---|---|
| Signature not covering every frame | C3 with P5, P12 |
| Zero outputs without position-specific sinks; duplicate outputs | C1 (R7, R8), C4 |
| Rollover after insertion, so settlement could fail on a full tree | C4, C6 |
| Root publication inside settlement, so its failure burned notes | C4 |
| Non-canonical Groth16 encodings | C2 (A6) |
| A statement value at or above `p` aliasing a nullifier | C2 (A5), C5b |
| Calling the logic contract directly | refinement (C5f) |
| Frame shapes other than exact three or four frames with self-payment | C2 (A1) |
| A SENDER fourth frame that credited a withdrawal twice | C2 (A1), C5c |
| Deleting settlement's pool-sender check | refinement (C5f), C5c |
| Slot taken from the timestamp instead of EIP-7843 | C3 with P7 |
| A spent key set replayed at `nonce_seq` 1 | C2 (A2), C5b |
| Duplicate commitments not independently spendable | C5b, spendability |
| Notes from different epochs mixed, or a nullifier from another epoch | C2 (A3, A5), C5b |
| A dummy input reproducing a funded note's nullifier | C1 (R2), C5g |
| Membership not gated by value | C1 (R3) |
| The same note in both inputs | C1 (R8), P6 |
| Fee below the maximum cost | C2 (A7), C5c |
| A fourth frame draining the pool | C5c, refinement |
| Settlement out of gas on a long carry at 262,143 leaves | C7 |
| EIP-8250 first-use state gas not budgeted | C2c |
| A deployment check accepting wrong logic bytecode | P9, checked by tooling |
| A chain ID change making spent notes spendable | P11 |

A recipient that rejects plain ETH strands its own credit (C5d keeps it, C10
requires acceptance); that is a limit, not a bug.

**Non-vacuity.** `W1` states that some model run has an approved spend whose
settlement passes every check, with a verifier that accepts exactly the public
signals of satisfying assignments; `W2` states that an honest deployment
approves some valid transaction in a reachable state. The live testnet
transactions of the `position-notes-v2` deployment are informal evidence:
deposit `0x9c8c1e19…399a`, transfer `0x21b51a52…ec4f`, tailless withdrawal
`0x93d07a20…978e` and swap withdrawal `0x8a551c3f…2f01`.

**Mutations.** Each change must make some claim false:

| Mutation | Claim that must fail |
|---|---|
| Remove `(cur[20] - root) * value === 0` | C1 (R3) |
| Remove one 128-bit range check | C1 (R5) |
| Remove `nf1 != nf2` | C1 (R8) |
| Remove the sink rules | C1 (R7) |
| Dispatcher: drop the `nonce_seq` check | C2 (A2) |
| Dispatcher: drop the fee check | C2 (A7), C5c |
| Dispatcher: drop the domain check | C2 (A5), C5b |
| Dispatcher: allow flags on frame 2, or a SENDER fourth frame | C2 (A1) |
| Logic: skip rollover before insertion | C4, C6 |
| Logic: pay a claim to `msg.sender`, or less than the credit | refinement |
| Logic: shield without inserting the leaf | refinement |
| Logic: make `claimWithdrawal` or `publishEpochRoot` always revert | C10 |

## 7. Lean statements

| Claim | Lean name | File |
|---|---|---|
| D1 to D10 | definitions, `R` | `Basic`, `Hash`, `Relation` |
| D11, D15 | `FrameTx`, `Acc`, `SignsCanonicalHash` | `FrameTx` |
| C1, C1c | `C1`, `C1c` | `Circuit` |
| C2, C2c, C7, C8, C10 | same names | `Evm` |
| C3, C4, C5a to C5h, spendability | same names, `Spendable` | `System` |
| C6 | `C6` | `Tree` |
| Refinement | `Refines`, `Obs` | `Evm` |
| Main theorem | `MainTheorem`, `Composes` | `Main` |
| Non-vacuity | `W1`, `W2` | `Main` |

The model is `Step` over `PoolState`, with P5 to P7 built into the spend step.
`Refines` ties it to the chain through `Obs`. Bad events are `BadEventWith`,
over `traceQueries`. Declarations marked `opaque` are bound to the artifacts in
later steps: the hashes and constraint system in step 3, and the EVM semantics
in step 5, where their definitions must come from one semantics applied to the
pinned bytecode.

## 8. Limits

A proof shows the code meets this specification under the premises. It does
not show the premises hold: that the cryptography is secure, that the setup
was honest, that clients implement the EIPs as modeled, or that the gas
schedule stays. Spend authority against mempool attackers rests on Groth16's
weak simulation extractability, argued on paper. Privacy and inclusion are
outside this specification.
