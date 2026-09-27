# Formal specification of the minimal shielded pool

This file states what the formal verification must prove about the pool. It is
the reviewed source of truth for the Lean statements in `formal/Spec/`, which
typecheck against Lean 4.35.0-rc3 and Mathlib and depend only on Lean's standard
axioms. Proofs of the claims are in progress (§7). Changing a claim or premise, here or in
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
| `contracts/vectors/spend_vkey.json` | `2b37d2e021ef759d` |
| `contracts/foundry.toml` (the pinned settings) | `af279592ce45b3be` |
| `activation_manifest.testbed.json` (whole file; its `compiler` entry pins the settings) | `b85d5808c6b71748` |
| `contracts/src/PoseidonT3.sol`, `PoseidonT4.sol` | `f353af63ac124e51`, `2384b8f71a2ed09f` |

In scope: the circuit, the dispatcher, the settlement logic, the verifier and
the Poseidon libraries, deployed together, and the safety of the funds they
hold, including that honest holders of notes worth more than a spend's maximum
cost can spend and be paid, given inclusion, a recipient that accepts a plain
payment and returns less than 64 KiB, and that no other party consumes the
note or its keys first, which §8 argues on paper (§5). Solvency, single consumption, real roots and
that a spend's extracted witness carries its note's key are claimed under §3
(proofs in progress, §7); that only a note's holder can spend it is argued on
paper under §8. Not in scope: privacy,
inclusion and mempool policy, the wallet, CLI and disclosure tooling, client
correctness, fee economics, and the trusted setup: its honesty (P3) and that
the committed zkey and `spend_vkey.json` are a setup of `spend.r1cs` (P9) are
premises, and the pinned zkey is not known to meet P3 (§8).

## 2. Definitions

**D1. Fields.** `p` is the BN254 scalar field order
`21888242871839275222246405745257275088548364400416034343698204186575808495617`
and `F = ZMod p`. For `x : F`, `val x` is its integer in `[0, p)`. `q` is the
BN254 base field order
`21888242871839275222246405745257275088696311157297823662689037894645226208583`.

**D2. Hashes.** `H2`, `H3`, `H10` are circomlib's Poseidon over BN254 with 2, 3
and 10 inputs, with the constants in `reference/poseidon_bn254_constants.json`,
which `reference/poseidon_bn254.py` loads. `K(bytes)` is
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
frames (resolved target, mode, flags, value, execution and state limits, data),
signatures (scheme, resolved signer, `msg`), blob hashes and `max_cost`
(`TXPARAM(0x06)`), as projected from a concrete signed transaction. Mode 0 is DEFAULT, 1 VERIFY, 2 SENDER.

**D12. Deployment.** A pool at `A` on chain `c`, whose runtime code is the
committed dispatcher initcode's output linked to a logic contract `L` and a
verifier `V`; `L` is `ShieldedPoolLogic` built with the pinned default
profile, linked to `PoseidonT3` and `PoseidonT4` built with the pinned
`libsmall` profile, and `V` is `Groth16Verifier` built with the pinned default
profile; after construction the pool's storage is
zero except slot 22, which holds `EMPTY_ROOT`. It is deployed once the pinned
EIPs are active, and `A` is created by a contract-creation transaction (empty
`to`) sent by an externally owned account, so the committed initcode is the
only code that runs in that transaction. Before deployment no code ran at `A`
and no frame transaction had sender `A` (§8). Neither follows from the
creation: code created at `A` through an address collision can destroy itself
in its creation transaction (EIP-6780), and EIP-8250's keyed nonces let a frame
transaction from `A` leave `A`'s nonce, code and storage unchanged. Either
could write roots under `A`'s sources, emit logs or send ETH from `A`. Its
balance at deployment may be nonzero, since anyone can fund the address in
advance.

**D13. Pool state** (the model). Per epoch `e` an append-only leaf list
`Leaves[e]`; the current epoch `E`; `finalRoot[e]` for `e < E`; credits; the
pool's balance; every EIP-8272 write as `(source_id, slot, root word)`, where
the latest write for a source and slot replaces earlier ones; the nonce keys
consumed for sender `A`; the current slot. The model starts from the
deployment: the chain's history before it, as slots and foreign root writes,
then the pool's balance at deployment. Ghost fields, not on chain:
each leaf's value from its opening, the occurrences consumed, and the total
credited to and paid out to each recipient.

**D14. Occurrence.** A pair `(e, i)` with `i < |Leaves[e]|`.

**D15. Acceptance.** `Acc(A, c, tx)`, reading the settlement words of frame 2
(`root, rootSlot, epoch, domain, nf1, nf2, o1, o2, pub, fee, rcp, auth`):

- **A1 shape.** `sender = A`; 3 or 4 frames; one signature; no blob hashes; the executing frame is 1. Frame 0: target `0x…8272`, VERIFY, flags 0, 72 data bytes, value 0, state limit 0; it succeeded, which P5 implies once frame 1 runs. Frame 1: target `A`, VERIFY, flags 3, 288 data bytes, value 0. Frame 2: target `A`, SENDER, flags 0, 388 data bytes beginning `0x921fcac7`, value 0, limits 2,000,000 and 550,000. A fourth frame: nonzero target, DEFAULT, flags 0, value 0.
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
event". A bad event anywhere in the run, even one among queries only the
adversary chose, voids the claims for every user from then on, since it
persists as the run grows; the guarantee is that an efficient algebraic machine
makes the run contain one only by exhibiting an object P1, P2 or P4 assumes no
one exhibits, or with the probability P3 bounds. A *bad event* counts only among what the run itself hashed: the sink
commitments the code hardcodes, the inputs of every approved spend's extracted
witness, every shield's commitment, every tree node of every root of every
prefix, every domain, root source and key-set hash, the entry and storage key
of every EIP-8272 write and of every spend's frame 0 tuple, the storage slot of
every credited or claimed recipient and of every closed epoch, every foreign
root write's source, and any inputs a claim names explicitly. It is two
distinct inputs with equal outputs; a degenerate output, meaning a Poseidon
output of 0 (the empty leaf) or a Keccak output below `2^64` (where empty
storage and fixed slots live); an approved spend whose extraction fails; or a
compression break. Collisions that merely exist do not count. Every witness a
claim ranges over is fixed by an extractor quantified universally, never chosen
by the proof. Because `H2`, `H3`, `H10` and `K` are fixed and unkeyed, P1, P2
and P4 are not probability bounds: collisions exist, and a machine could
hardcode one. Each such bad event instead exhibits, computably from the run and
its extracted witnesses, an explicit Poseidon or Keccak collision, a Poseidon
output of 0, a Keccak output below `2^64`, a run query other than
`addr20(A) ‖ u256(e)` that hashes to `K(addr20(A) ‖ u256(e))`, distinct
`(c, a, e)` with equal `D`, or `x ≠ x′` with `γ(x − x′, α(x) + H10(x′)) = 0`.
Openings and dummies a claim names are treated alike: for one that merely
exists, the claim holds through a collision with the query that created the
leaf, and the object is exhibited only for openings some party outputs.
P1, P2 and P4 assume that no one exhibits such an object. The guarantee is
constructive: from any algebraic machine that makes the run contain one of
these bad events, running it with P3's extractor and scanning the run's queries
yields the object at about the same cost. Only P3 bounds a probability, over
the setup's randomness, for algebraic machines with `ext` taken to be P3's
extractor.

- **P1 Poseidon.** `H2`, `H3`, `H10` are the concrete functions of D2. No one is assumed to exhibit a Poseidon collision, or an input with output 0, among a run's queries or the openings and dummies a claim names.
- **P2 Keccak.** No one is assumed to exhibit Keccak collisions and outputs below `2^64`, for distinct `(c, a, e)` with equal `D`, and for a run query other than `addr20(A) ‖ u256(e)` whose output is `K(addr20(A) ‖ u256(e))` for some `e < 2^64`, or an output `K(addr20(A) ‖ u256(e))` below `2^64`; and, used only for liveness, for a Keccak collision between the `NONCE_MANAGER` storage key of a key a spend selects and that of any key consumed on the chain, by any sender.
- **P3 Groth16.** For the committed verification key, from snarkjs's two-phase setup (`γ = [1]₂`, `δ` from phase 2) run honestly, knowledge soundness: for every efficient algebraic machine that produces the run's transactions, honest provers included, whose group inputs include the whole setup transcript (the phase-1 powers of tau and the phase-2 contributions) and every other group element it sees, including other setups built on the same phase 1, an efficient, explicit extractor (the algebraic group model argument's, which computes the witness from the machine's representations of its group outputs over those inputs, without rewinding) maps, except with negligible probability, each proof that Groth16's verification for the committed key accepts (`Groth16Accepts`) to a satisfying assignment of the pinned `spend.r1cs` with the verified public signals. Bowe, Gabizon and Miers (2017) argue this in the generic group model, and Kohlweiss, Maller, Siim and Volkhov (2021) prove knowledge soundness for that ceremony, including the beacon version used in practice, against algebraic adversaries in the random oracle model with one honest party per phase, though their update proofs put the random-oracle element in G1 rather than snarkjs's G2 and their model excludes honest setups of other relations on the same phase 1 (their §3), so P3's extension to snarkjs's transcript and to such setups is an assumption; Fuchsbauer, Kiltz and Loss (2018) cover Groth's original reference string, not this one. Every claim holds for every extractor, and an approved spend whose extraction fails is a bad event. An approved spend's proof is 256 bytes the linked verifier accepts, so with C9 it is one that `Groth16Accepts`, and P3 bounds its extraction failure. No claim assumes extraction for every accepted proof: a Groth16 verifier accepts some proof for every public input. Knowledge soundness over a machine that includes honest provers says nothing about who knew a witness, so it gives no spend authority against any party that sees honest proofs, on chain or before inclusion. Beyond C5i, spend authority needs weak simulation extractability, so that a spend of new public signals yields a witness from its sender's view alone, and zero knowledge with Poseidon one-wayness, so that no other party learns a holder's key (§8). The pinned zkey comes from a local test setup with one phase-2 contribution and an unrecorded phase 1, so it is not known to meet P3.
- **P3c Groth16 completeness.** For every satisfying assignment there are eight proof words that Groth16's verification for the committed key accepts for its public signals; with C9 the linked verifier accepts them. Used only for liveness (§5).
- **P4 Hybrid compression** (eprint 2025/1500). A compression break is an approved spend whose extraction succeeds with a statement `x′` other than the settlement's `x`. It gives `x ≠ x′` with `γ(x, α(x) + β(x′)) = γ(x′, α(x) + β(x′))`. No one is assumed to exhibit one. For these fixed, unkeyed functions that is an assumption about what anyone exhibits, like P1 and P2; with `K` and `H10` as random oracles the paper's Lemma 4 bounds it by about `1.14 · 9q²/p` for `q` queries, the factor covering the bias of `K mod p`.
- **P5 EIP-8141.** A transaction is valid only if its `chain_id` is the chain's. Frames run in order. A VERIFY frame changes nothing but through `APPROVE`; if it fails, the transaction is invalid. `APPROVE` reverts the current frame unless `ADDRESS` is the frame's resolved target and the scope is among the frame's flags; `APPROVE` with payment reverts if the payer's balance is below `max_cost`. Approval flags are excluded from atomic batches. `APPROVE(3)` from frame 1 makes `A` sender and payer. A SENDER frame's caller is `sender`, a DEFAULT frame's the entry point. A failed non-VERIFY frame reverts its own effects, or its whole atomic batch's. `TXPARAM`, `FRAMEPARAM` and `SIGPARAM` return the EIP's table values, with EIP-8250's `TXPARAM(0x01) = nonce_seq`, `0x0E` = key count, `0x0F = K(u256(n) ‖ u256(k_1) ‖ … ‖ u256(k_n))`. Frame data read with `FRAMEDATALOAD` or, in the running frame, `CALLDATALOAD` is the frame's data. A `msg` is empty, signing the canonical hash, or a nonzero 32-byte digest, so `SIGPARAM(i, 0x02) = 0` exactly when signature `i` signs the canonical hash, which covers every field except the raw bytes of such signatures. The payer pays at most `max_cost`.
- **P6 EIP-8250.** Keys are 1 to 16 strictly increasing integers below `2^256`. A nonzero key's sequence for `sender` is the `NONCE_MANAGER` storage word at `K(u256(sender) ‖ u256(key))`. A transaction is valid only if each key's sequence equals `nonce_seq`; approval consumes every key atomically; an invalid transaction consumes nothing; nothing else changes a sequence, since ordinary calls to `NONCE_MANAGER` revert; consuming a key for the first time costs 97,920 state gas.
- **P7 EIP-8272.** A call from address `a` with data `salt ‖ root` during slot `S` stores the entry hash of `(K(addr20(a) ‖ salt), S, root)` at the storage key of that source and ring index `S mod 8192`; nothing else writes. Frame 0, with the target, mode, flags, value, state limit and data length A1 gives it, A3's data and enough execution gas, succeeds exactly when, for its tuple, the slot is strictly before the current slot and within 8,191 slots of it and the stored word at the tuple's storage key is the tuple's entry hash. Entries change otherwise only through a reorg; the model follows the canonical chain.
- **P8 Gas schedule and fork.** A pinned gas schedule `G`: the schedule ethrex 247e2dd2 applies at the pinned fork, with EIP-8037 state gas, EIP-2929's warm and cold access sets priced as EIP-8038 sets them (EIP-8037 requires EIP-8038; how EIP-8038 applies at EIP-8141's frame entry is not settled in the EIPs, and the measured constants follow ethrex), and EIP-150's 63/64 rule. The claims hold while the chain keeps `G` and the pinned EIP revisions; a fork that changes them ends them.
- **P9 Deployment.** The pool is deployed as in D12 with the committed artifacts, by a plain contract-creation transaction from an externally owned account; the committed zkey is snarkjs's Groth16 setup of the committed `spend.r1cs`, and `spend_vkey.json` is that zkey's verification key. No Lean proof checks the setup. The deployment script checks the deployment and the artifact hashes the activation manifest pins (`spend_vkey.json` is bound field by field, not by hash). The activation gate on this branch (added in `6735e3e` and `870dd58`; at `8835be7` it compares only the manifest's hashes, profile and contribution count) additionally checks the zkey's sizes and A/B coefficient metadata against `spend.r1cs`, and binds both the Solidity constants and every verifier-used field of `spend_vkey.json` to that key. C/IC/L and key-point consistency with the complete constraint system remain unchecked without the original phase-1 powers of tau (§8). No tool checks D12's conditions that no code ran at `A` and no frame transaction had sender `A` before deployment.
- **P10 EVM model.** The Lean EVM and Yul semantics, extended with EIP-8141 frames, EIP-8250 and EIP-8272, match the client, and every chain-level declaration in `Spec/Evm.lean` is defined from it.
- **P11 Chain identity.** The chain ID never changes on a chain that carries the pool's state.
- **P12 Signatures.** secp256k1 low-s ECDSA applied to EIP-8141's canonical signature hash is unforgeable as a scheme on transactions: no efficient party without the key outputs a valid transaction whose scheme-1 signature resolves to that key's address, other than one the holder signed or one that differs from it only in that signature's bytes. ECDSA on bare digests is forgeable, so collision resistance of the hash alone does not give this; Brown (2005) argues it in the generic group model from collision resistance and uniformity of the hash, pseudorandom signing nonces, and a condition on the conversion from `R` to `r`. Used only to read C3's signature conclusion as "only the holder of `auth`'s key authorized this transaction".
- **P13 Bounded history.** Fewer than `2^64 − 1` epochs ever roll over, and the pool's balance stays below `2^256`, as it always does on chain. With C5c, no credit overflows.

## 4. Claims

**C1 Circuit soundness.** Every satisfying assignment of the pinned
`spend.r1cs`, whose wire 0 is 1, with statement `x`, private inputs `w` and
public signals `(β, γ, α)`, has `R(x; w)`, `β = H10(x)` and `γ = γ(x, α + β)`.
*Prevents* mints, overflows, fake membership, bad sinks and duplicate
nullifiers inside a proof.

**C1c Circuit completeness.** For every `x`, `w` with `R(x; w)` and every `α`,
some satisfying assignment has statement `x`, inputs `w` and public signals
`(H10(x), γ(x, α + H10(x)), α)`. *Ensures* every valid spend can be proven.

**C2 Approval.** Whenever code running at `A` executes an `APPROVE` that does
not revert its frame, during a valid transaction in a reachable state, it is
frame 1 of a transaction whose sender
is `A`, the scope is 3, and `Acc(A, c, tx)` holds. *Prevents* approving a wrong
shape, keys, root, signer, statement, proof or fee, and paying for anyone
else's transaction.

**C2c Approval completeness.** In every reachable state, the pool approves every transaction with
`Acc(A, c, tx)` that is valid up to frame 1 (EIP-8141's static rules and gas
caps, EIP-8250's decoding rules, EIP-1559's fee-field checks, the fee caps
against the base fee, each gas dimension's reservation
against the block's remaining gas, the chain ID, the nonce sequences,
signature validation and frame 0),
with frame 1 limits of at least 216,141 execution gas (the measured minimum
under `G`) and 195,840 state gas (two first-use keys) and
`max_cost ≤ balance(A)`; the transaction is then valid. *Ensures* honest spends
are not rejected.

**C3 Approved spends are valid** (P3, P4, P5, P7). An approved spend's
extracted witness satisfies `R` for the settlement's own statement; the
transaction's keys are exactly `[min(nf1, nf2), max(nf1, nf2)]`; its root is
`TR` of a prefix of its epoch's leaves; and it carries `auth`'s signature over
the canonical hash, which with P12 means only `auth`'s key holder authorized
every field except that signature's own bytes, including the fourth frame, the gas limits and the recipient.
All this, or the run has a bad event.

**C4 No burn.** An approved spend's settlement passes every revert condition
of `settle`, including the ABI decoder's and checked arithmetic on the epoch
counter and the credit, unless the run has a bad event or P13's bound fails;
with refinement it succeeds on chain. *Prevents* burning notes whose keys
approval has consumed.

**C5 System safety.** In every run of the model, unless it has a bad event:

- **C5a Leaves.** Every leaf opens to a value `0 < v < 2^128` and is no sink.
- **C5b Single spend.** Each nonzero-value input of an approved spend is an existing occurrence of the spend's epoch, holding the witness's leaf and value, not consumed before; when both inputs have nonzero value, they are different occurrences.
- **C5c Solvency.** The pool's balance covers every unspent occurrence's value plus every credit.
- **C5d Credits.** Each recipient's credit is what it was credited minus what it was paid (holds with no bad event).
- **C5e Roots.** Every root written under the source `K(addr20(A) ‖ u256(e))` of an epoch `e < 2^64` is `TR` of a prefix of `Leaves[e]`, with `e ≤ E`; the bad event may use that source's Keccak input.
- **C5f Exclusive access.** Only the events refinement lists change the pool's state. It is part of refinement, not a model claim.
- **C5g No griefing.** A key an approved spend consumes that is some occurrence's nullifier, under any opening of its leaf, consumes that occurrence as one of the spend's inputs; the bad event may use that opening's hash inputs.
- **C5h Freshness.** An unspent occurrence's nullifier, under any opening, is not a consumed key; the bad event may use that opening's hash inputs.
- **C5i Key binding.** A spend that consumes an occurrence as a nonzero-value input, under any opening `(sk, ρ, v)` of its leaf, extracts that `sk` and `ρ`; the bad event may use that opening's hash inputs. With §8's premises, taking a note therefore needs its holder's key; C5i alone does not give that, since P3's extractor may read the key from an honest prover.
- **C5j Insertions.** A shield inserts its commitment, and a settlement that passes its checks inserts each nonzero-value output, as a new unspent occurrence holding that commitment and value.
- **C5k Publication.** Only an existing epoch `e < 2^64` can be published; anyone can publish one, and publishing writes exactly `TR` of all of `Leaves[e]`, the current tree for the current epoch and the full final tree for a closed one, changing nothing else.
- **C5l Value accounting.** For every event, the balance, credits, payouts and what the pool owes change as follows: only a shield or a receive adds value; value leaves the balance only as a claim's payout (its credit, to its recipient) or a spend's gas, and leaves what the pool owes only as a claim's payout, a settled spend's fee or a failing settlement's inputs; a settlement credits `pub` to its recipient. A failing settlement, which C4 excludes in bounded runs without a bad event, burns its inputs. With C4, in bounded runs value is therefore not burned, misdirected or swept, not only not minted.
- **C5m Root writes.** Only a publish or another address's write adds an EIP-8272 write, the latter one write under its own source at the current slot; a shield, claim, spend, receive or slot leaves the root writes unchanged. So a published root is replaced only by a publication in the same slot, or by a foreign write whose source collides with the pool's (a bad event).
- **C5n Epochs.** The epoch counter moves only by a rollover: by one, on a shield or a settled spend whose new leaves do not fit in the current epoch.
- **Determinism.** A state and an event allow at most one next state (`StepFunctional`), so the publish step C5k exhibits is the only step from that state on that event.

**Spendability.** For every unspent occurrence with opening `(sk, ρ, v)`, every
root of a prefix of its epoch that contains it, every fee below its value,
every recipient and authorizer, and every dummy second input whose nullifier
key the run never hashed, the canonical full withdrawal of it satisfies `R` and
its keys are nonzero and unconsumed, or the run has a bad event among its
hashes and the spend's.

**C6 Tree.** The contract's zero constants are `Z_l`, its `EMPTY_ROOT` is
`Z_20`, and inserting up to `2^20` leaves from empty, then computing the root,
yields `TR` of the inserted leaves.

**C7 Gas** is part of refinement: whenever the model's settlement passes
`SettlePre`, the chain's succeeds, so it never runs out of gas. The exception is
a settlement that inserts no leaf and credits nothing, whose failure changes
nothing the chain shows, so refinement cannot tell it from success.

**C8 Libraries.** `hash2` and `hash3` return `H2` and `H3` within 200,000 gas.

**C9 Verifier.** The linked verifier, when its call frame starts with 500,000
gas (the dispatcher's gas operand; frame 1's limit may leave less, which C2c
covers), returns 1 for 256 proof bytes and public signals exactly when
Groth16's verification for the committed key accepts them: the eight words are
the coordinates of `A`, `B` and `C` in EIP-197's encoding (each G2 coordinate
imaginary part first), below `q`, of points on the curves, in the prime-order
subgroups and none at infinity, satisfying the pairing equation.

**C10 Publication and claims.** In every reachable state anyone other than the
pool, sending a valid transaction in any block environment the consensus rules
allow, can call
`publishEpochRoot(e)` for every `e ≤ E` whose root is nonzero, and the call
succeeds; and they can call `claimWithdrawal(r)` for every credit the balance
covers, and the call succeeds unless the first `CALL`, `CALLCODE` or
`STATICCALL` made by code running at `A` (the dispatcher's `DELEGATECALL` into
`L` does not count) is a plain `CALL` paying the credit to `r` with at least
15,000,000 gas and the recipient (its code, its
EIP-7702 delegate or a precompile) rejects it or returns at least 64 KiB. Each
call is the only call of a plain EIP-1559 transaction (no access list,
authorizations or blobs) with a 16,000,000 gas limit, and carries no value. *Prevents* permanently locking notes or credits.

**Refinement.** Along every run of the chain from an honest deployment, for
every extractor, the model events of the deployment and of the run's steps form
a run of the model, and
the chain shows that run's state: balance, credits, consumed keys, epoch, leaf
count, current and final roots, the logs of appended leaves, the latest
recent-root entry of each of the pool's sources in the usable window, the ETH
paid to each address, and the slot. Otherwise the run has a bad event, or, if
the model cannot follow some event, the run up to and including that event has
one. What the
chain shows about hash-indexed storage names only keys the model holds, so a
collision with a key nobody hashed cannot falsify it. The deployment's events
are the chain's EIP-8272 writes and slots up to deployment, then the pool's
balance. A step's events are the calls into the pool (a transaction whose `to`
is `A`, a `CALL` to `A`, or a non-VERIFY frame whose resolved target is `A`, not
the dispatcher's `DELEGATECALL` into `L`)
whose calldata begins with the selector of `shield`, `publishEpochRoot` or
`claimWithdrawal` and that return successfully and whose effects persist,
whether or not they change state, decoded from that outer call's own calldata
and `CALLVALUE` (a shield's `inner` is its calldata word and its value the
`CALLVALUE`), so a dispatcher that rewrites calldata before delegating is
caught; each spend, meaning a transaction whose
frame 1 the pool approved, with the gas the pool paid, whether or not its
settlement succeeds; each foreign EIP-8272 write; and the slots. A chain step is any valid transaction, the end of a block with its
withdrawals, or the next slot, empty or opening a block with any header the
consensus rules allow, so refinement covers every block environment. A step's
events are in execution order, with a spend at its settlement, before the
events of its later frames. `receive`
events account for the balance at deployment and for exactly the ETH that later
reaches the pool other than by a call into it (as `eventsOf` defines one) or as a gas refund. Any other
successful call leaves what the chain shows unchanged. This gives C5f and C7.

## 5. Main theorem

`MainTheorem` is C1, C1c, the model half (C3 to C5 and spendability, for every
verifier and extractor, from C1) and the chain half (C2, C2c, C6, C8, C9, C10
and refinement). `Composes` states that the main theorem implies `ChainCorollary`:
for every extractor, along every run of an honest deployment, the chain shows a
model state in which the pool is solvent, no occurrence is consumed twice, and
every root under one of its sources is a real root of its tree, or some prefix
of the run has a bad event (for a root, one that may use that source's Keccak
input, as in C5e). Such a bad event, including one among queries only the
adversary chose or a failed extraction of its own spend, voids these
conclusions for every user from then on. The guarantee is that an efficient
algebraic adversary, with `ext` taken to be P3's extractor, makes the run
contain a bad event only by exhibiting an object P1, P2 or P4 assumes no one
exhibits, or with the probability P3 bounds; it does not shrink to the notes
involved.

Liveness composes from the same claims and is argued, not stated in Lean. The
holder of an unspent note worth more than the spend's maximum cost builds the
canonical spend, which spendability makes valid with fresh, nonzero keys. C1c
and P3c give an accepted proof. C5k, C5m, C10 and refinement put a root
containing the note on chain, which no event replaces once its slot has passed,
unless the run has a bad event, so P7 makes frame 0 succeed for a spend 1 to
8,191 slots after the root's slot; and P6 makes its keys' sequences 0 unless an EIP-8250 slot
collides with a consumed one. C5c gives `max_cost ≤ fee < v ≤ balance`, so C2c
approves the spend; C4 and refinement settle it, C5l credits `pub` to the
chosen recipient, and C10 pays the credit, which C5c covers, to any recipient that accepts a plain payment and returns less
than 64 KiB. This assumes the
publication and the spend are included, with the spend 1 to 8,191 slots after
the root's slot. It also assumes no other party consumes the note or its keys
first, which rests on §8's argument, applied to the note's key through C5g and
C5i and to the dummy's key directly.

## 6. Validating this specification

**Past bugs.** Every safety bug found earlier must violate some claim:

| Past bug or fix | Claim that catches it |
|---|---|
| Signature not covering every frame | C2 (A4); C3 with P5 and P12 gives its meaning |
| Zero outputs without position-specific sinks; duplicate outputs | C1 (R7, R8), C4, refinement |
| Rollover after insertion, so settlement could fail on a full tree | refinement, C4 |
| Root publication inside settlement, so its failure burned notes | refinement, C4 |
| Non-canonical Groth16 encodings | C2 (A6) |
| A statement value at or above `p` aliasing a nullifier | C2 (A5), C5b |
| Calling the logic contract directly | none: it touches only the logic's own state (defense in depth) |
| Frame shapes other than exact three or four frames with self-payment | C2 (A1) |
| A SENDER fourth frame that credited a withdrawal twice | C2 (A1), C5c |
| Deleting settlement's pool-sender check | refinement (C5f), C5c |
| Slot taken from the timestamp instead of EIP-7843 | none: client tooling, out of scope (§1); a wrong slot only makes frame 0 fail |
| A spent key set replayed at `nonce_seq` 1 | C2 (A2), C5b |
| Duplicate commitments not independently spendable | C1 (R2), C1c, refinement; spendability shows why R2 needs the index |
| Notes from different epochs mixed, or a nullifier from another epoch | C2 (A3, A5), C5b |
| A dummy input reproducing a funded note's nullifier | C1 (R2), C5g |
| Membership not gated by value | C1c if it bound dummies too; C1 (R3) if it keyed on another signal |
| The same note in both inputs | C1 (R8), P6 |
| Fee below the maximum cost | C2 (A7), C5c |
| A fourth frame draining the pool | C5c, refinement |
| Settlement out of gas on a long carry at 262,143 leaves | refinement (C7) |
| EIP-8250 first-use state gas not budgeted | C2c |
| A deployment check accepting wrong logic bytecode | P9, checked by tooling |
| A chain ID change making spent notes spendable | P11 |

A recipient that rejects a plain payment, such as some precompiles, or returns
so much data that copying it exhausts the pool's gas, strands its own credit
(C5d keeps it; C10 excuses a rejection or at least 64 KiB of returned data); so
may a recipient that calls back into the pool while being paid, if the pool
guards against reentry. These are limits, not bugs.

C3 to C5 and spendability depend on the code only through the circuit; beside
a dispatcher or logic change in these tables they name the property the
failing chain claim protects.

**Non-vacuity.** `W1` states that some model run has an approved spend whose
settlement passes every check and no bad event, with a verifier that accepts
exactly the public signals of satisfying assignments and an extractor that maps
every accepted proof to such an assignment (`IdealVerifier`); `W2` states that some
reachable state of an honest deployment shows a leaf and a payout, the pool
approves there a transaction valid up to frame 1 and then valid, and some
caller other than the pool has a valid environment there. The 2026-09-25 run
of the `position-notes-v2` deployment recorded in `SECURITY.md` (pool and block
in `devnet/deploy_config.json`) is informal evidence.

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
| Dispatcher: reject every withdrawal | C2c |
| Logic: skip rollover before insertion | refinement |
| Logic: pay a claim to `msg.sender`, or less than the credit | refinement (C5l) |
| Logic: shield without inserting the leaf, or hashing a different `inner` | refinement (C5j, C5l) |
| Logic: `publishEpochRoot` returns without writing the root | refinement (C5k) |
| Dispatcher: rewrite `shield`'s `inner` or `publishEpochRoot`'s epoch before delegating | refinement (C5j, C5k) |
| Logic: make `claimWithdrawal` or `publishEpochRoot` always revert | C10 |
| Verifier: generated from another zkey | C9 |
| Verifier: skip the canonical-coordinate or infinity checks | C9 |
| Set up the zkey from `spend.r1cs` minus one constraint | none: violates P9; this branch's gate checks A/B terms and counts (the gate at `8835be7` does not), while full setup remains assumed (§8) |

**Model mutants.** Refinement certifies any code that matches `Step`, so the
model claims must also reject a wrong `Step`. Each variant below makes the named
claim force a bad event at every step of the stated shape, which ordinary
hashes do not produce (argued during review):

| `Step` variant | Claim that fails |
|---|---|
| Credit `auth` instead of `rcp`, or credit nothing | C5l |
| Drop a settlement's outputs | C5j |
| Shield inserts nothing, another commitment, or skips a duplicate | C5j (and C5l for the duplicate) |
| Claim pays half and records the full credit as paid | C5l |
| Publish or roll over with a partial, stale or zero root | C5k |
| Publish under another epoch's source or the raw epoch | C5k |
| Shield, claim or spend also writes a root | C5m |
| Publish an epoch that does not exist yet | C5k |
| Move the epoch counter other than by a rollover | C5n |
| Credit twice | C5l (and C5d unless `credited` also doubles) |
| Skip consuming inputs | C5h, and C5l when the settlement passes |
| Accept a used key as a nonzero-value input's nullifier | C5b |
| Accept a foreign root | C3, C5b |
| No rollover | spendability (R1) |

## 7. Lean statements

| Claim | Lean name | File |
|---|---|---|
| D1 to D10 | definitions, `R` | `Basic`, `Hash`, `Relation` |
| D11, D15 | `Mode`, `Frame`, `Signature`, `FrameTx`, `RawTx`, `RawTx.view`, `Acc`, `PointsNotInfinity`, `SettleData`, `SettleData.decode`, `SettleData.stmt`, `settleData`, `RECENT_ROOT`, `SETTLE_SELECTOR`, `RR_ENTRY_DOMAIN`, `RR_STORAGE_DOMAIN`, `keysHash`, `sourceId`, `SignsCanonicalHash` | `FrameTx`, `Evm`, `System` |
| D12 | `Deployment`, `Honest`, `addrOf`, `chainOf`, `verifierOf`, `poolOf`, `NONCE_MANAGER` | `Evm` |
| D13, D14 | `Pool`, `PoolState`, `PoolState.init`, `PoolState.append`, `rollsOver`, `CAPACITY`, `Event`, `Step`, `Run`, `Occ` | `System`, `Tree` |
| P3, P4, P13, C4's checks, bad events | `Pool.ext`, `extOf`, `proofOf`, `verifiedPublics`, `Query.collide`, `Query.degenerate`, `BadEvent`, `pathQueries`, `newCount`, `ExtractionFailure`, `CompressionBreak`, `Bounded`, `SettlePre` | `System` |
| C1, C1c, C9's key | `C1`, `C1c`, `Assignment`, `Satisfied`, `stmtOf`, `witOf`, `publicOf`, `Groth16Accepts` | `Circuit` |
| C2, C2c, C8, C9, C10 | same names, `Outcome`, `ValidTx`, `PreValid`, `approvalsIn`, `libHash2`, `libHash3`, `Env`, `EnvValid`, `callPool`, `publishCalldata`, `claimCalldata`, `firstPayout`, `Payout`, `RecipientRejected` | `Evm` |
| C3, C4, C5a to C5e, C5g to C5n, determinism, spendability | same names, `StepFunctional`, `stmtOfTx`, `Spendable`, `owed`, `inputsOf`, `newLeaves`, `lastWrite`, `openingQueries`, `mkSpend`, `siblingsOf` | `System` |
| C6 | `C6`, `LogicTree`, `LogicTree.empty`, `ZEROS`, `EMPTY_ROOT_CONST`, `zeroConst`, `insertLoop`, `LogicTree.insert`, `LogicTree.root` | `Tree` |
| Refinement, C5f, C7 | `Refines`, `Obs`, `ChainState`, `ChainStep`, `eventsOf`, `passiveInflow`, `receivedIn`, `eventsAlong`, `chainInit`, `historyEvents`, `initEvents`, `modelEvents`, `ChainRun`, `ReachableChain` | `Evm` |
| Main theorem | `MainTheorem`, `ModelTheorem`, `ChainTheorem`, `ChainCorollary`, `Composes` | `Main` |
| Non-vacuity | `W1`, `W2`, `IdealVerifier` | `Main`, `System` |

The model is `Step` over `PoolState`, with P5 to P7 built into the spend step.
`Refines` ties it to the chain through `Obs`, whose chain side reads concrete
fields of `ChainState`, over `modelEvents`: the deployment's `initEvents`, then
each step's `eventsOf`. `Obs`, `creditMsg` and `finalRootMsg` fix the logic's
storage layout: slot 21 is the leaf count, 22 the current root, 23 the credits,
24 the epoch and 25 the final roots. `traceQueries` collects `witnessQueries`,
`treeQueries`, `eventQueries` and the Keccak inputs `rrEntryMsg`, `rrKeyMsg`,
`creditMsg` and `finalRootMsg`. Bad events are `BadEventWith`, over `traceQueries`,
with `Query.degenerate`, `ExtractionFailure` and `CompressionBreak`.
Declarations still marked `opaque` are bound to the artifacts in step 5:
`Groth16Accepts` (textbook Groth16 verification with the key in
`spend_vkey.json`, not the verifier's code), which only C9 uses, and the EVM
semantics, where
`ChainStep`, `eventsOf`, `approvalsIn`, `firstPayout` and the
other chain declarations must
come from one semantics applied to the pinned bytecode, and where step 5 proves
the bytecode's `_zeros`, `EMPTY_ROOT`, `_insert` and `_computeRoot` equal
`ZEROS`, `EMPTY_ROOT_CONST`, `LogicTree.insert` and `LogicTree.root`. `formal/Sanity/` holds
proofs, written during review, that parts of the specification mean what they
should. `Spec.Hash` uses concrete reference Poseidon functions generated from
the pinned D2 constants. Universal optimized/reference equivalence is now
proved for all three widths. `Spec.Circuit` uses the complete pinned R1CS and
concrete projections; `Artifacts.CircuitSoundness` proves C1, including every
note/path hash and both compression outputs. `Artifacts.CircuitCompleteness`
proves C1c by constructing and checking the complete assignment, including
exact statement, private witness and public projections for every alpha.
Both rest on an external binding: `formal/tools/r1cs_artifact.py` decodes
`build/spend.r1cs` into `Artifacts/Spend.lean` and maps signals to wires
through the reproduced symbol file, cross-checked by `crosscheck_r1cs.cjs`.
Lean does not parse the binary.
`formal/Proofs/` proves `ModelTheorem`, every model claim from C1, and `Composes`.
It also proves C6 for the specified tree algorithm, including kernel-checked
zero constants. `K` is concrete Ethereum Keccak-256, with kernel-checked
source/domain fixtures. `Proofs.NonVacuityFixtureVerified` proves W1 using
an actual satisfying circuit assignment, the specified ideal verifier, an
encoded accepted spend and the complete finite bad-event query support.
W2 and the chain half of `MainTheorem` remain open: C2, C2c, C8, C9, C10 and
refinement, which need step 5's semantics. `Proofs.CircuitModel` derives
`MainTheorem` and `ChainCorollary` from exactly those obligations.

CI's `formal` job checks this project on every push: `lake build`, with
`Proofs/AxiomAudit.lean` rejecting any axiom beyond Lean's standard three for
the principal results; `tools/check_formal.py`, which rejects `sorry`, `admit`,
`native_decide`, new axioms and unsafe code in any Lean file, checks the
artifact hashes of §1, and checks the statement files (this file, `Spec.lean`
and `Spec/`) against `STATEMENTS.lock`; and the R1CS import check above, with
the circuit recompiled. `.github/CODEOWNERS` assigns the statement files and
the lock to the owner, which binds only if branch protection requires code
owner review.

## 8. Limits

A proof shows the code meets this specification under the premises. It does
not show the premises hold: that the cryptography is secure, that the setup
was honest, that clients implement the EIPs as modeled, or that the gas
schedule stays. Spend authority against every party other than the holder,
and hence liveness, rest on
Groth16's weak simulation extractability over P3's group inputs (proven in
the algebraic group model for Groth's original reference string by Baghery,
Kohlweiss, Siim and Volkhov 2021, not known for this setup) and zero
knowledge, on P4 for replayed
proofs, on P12, and on no efficient party computing `sk` from `inner`, `cm` and
`nf` (Poseidon one-wayness), argued on paper. Liveness is argued from the
claims (§5), not proven as one theorem.

On this branch, tooling checks the zkey's sizes and A/B terms against `spend.r1cs`, and both
verification-key representations against the zkey. Those comparisons catch a
key whose sizes or A/B terms differ from `spend.r1cs`, and a Solidity or JSON
key that differs from the zkey's. They miss a key set up from an R1CS that
differs only in C terms, and they do not prove that any of the zkey's points
were derived from the complete R1CS. The original phase-1 powers of tau
is not recorded. Full setup consistency therefore remains part of P9. The gate
reports `setup: partial`; its `--ptau` path requires a manifest-pinned file and
runs snarkjs's full check. The unused JSON pairing cache is outside the native
gate, although snarkjs 0.7.5's `zkey export verificationkey` on the pinned zkey
reproduces every field of the JSON, including that cache
(`formal/evidence/2026-09-27-claude/vkey-export.log`). Until a ceremony
replaces the zkey, the claims that allow a bad event give no guarantee for the
pinned artifacts.

D12's conditions that no code ran at `A` and no frame transaction had sender
`A` before deployment are not checked. They fail only if someone holds a key for `A` or
created a contract at `A` earlier (which EIP-6780 lets it destroy in the same
transaction): a 2^160 search against an honest deployer, but about 2^80 for a
deployer who searches for a creation address that is also a key's address or
an earlier `CREATE2` address. Such a deployer could plant roots under the
pool's sources and drain it. A tool checking these conditions must look for
any execution at `A` before deployment, not only transactions with sender `A`;
only executions since EIP-8272's activation can plant roots. Recording the
deployment slot and rejecting root slots at or before it would remove the risk
that planted roots drain the pool, at the cost of changing the pinned code;
refinement would still need these conditions unless `Obs` counted only logs
and transfers after deployment and the model accepted the pool's own earlier
root writes, which `historyEvents` replays as `rootWrite` events that `Step`
rejects.

Step 5's definitions of `chainInit`, `ChainStep`, `eventsOf`, `passiveInflow`,
`ValidTx`, `PreValid`, `approvalsIn`, `EnvValid`, `callPool`, `firstPayout`,
`verifierOf`, `libHash2`, `libHash3`, `addrOf`, `chainOf`, `NONCE_MANAGER`,
`RawTx.view`, `Groth16Accepts` and `Honest` are checked against their docstrings by review only.
A narrower `ChainStep`, `EnvValid` or `Honest`, or a wrong `chainInit`, leaves
states uncovered by refinement, C2, C2c and C10. A looser `eventsOf` or
`passiveInflow` weakens refinement, a narrower `ValidTx` or `approvalsIn`
weakens C2 and a looser one weakens C2c and W2, a stronger `PreValid` weakens
C2c, a looser `callPool` or `firstPayout` weakens C10, and a `verifierOf`,
`libHash2` or `libHash3` not defined by running the linked bytecode makes C9 or
C8 vacuous and weakens C2 and C2c. A `Groth16Accepts` other than textbook
verification for the committed key makes C9 and P3 refer to the wrong
predicate.

Privacy and inclusion are outside this specification.
