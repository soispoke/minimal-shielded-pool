pragma circom 2.0.8;

// The spend relation of the minimal shielded pool: a join-split over native ETH
// with two input notes, two output notes, a public withdrawal amount and a fee,
// all in wei. There are no tokens. The pool is the sender and payer of every
// spend: the fee leaves the notes and stays in the pool, which pays the gas.
//
// Notes. The first input of each three-input hash is a tag (1 owner key,
// 2 commitment, 4 nullifier) that keeps the three hashes apart:
//     owner_pk = Poseidon(1, spend_key, 0)
//     inner    = Poseidon(owner_pk, rho)     what a recipient gives a sender
//     cm       = Poseidon(2, inner, value)   shield hashes msg.value in on chain
//     index    = sum(bits[i] * 2^i)          the note's leaf in its epoch's tree
//     nf       = Poseidon(4, Poseidon(domain, spend_key), Poseidon(cm, index))
// The spender proves it knows each input's spend_key, rho, value and Merkle
// path (siblings, and the index bits, low bit first). The domain is
// keccak256(DOMAIN_TAG || chain_id || pool || epoch) mod p, and the pool
// requires the epoch whose root the spend proves against. Each epoch has its
// own depth-20 tree, and the pool starts the next epoch when a tree lacks
// room. Each leaf is therefore a separate note with exactly one nullifier,
// even when two leaves hold the same commitment. A circuit with another
// nullifier formula needs a fresh pool: under an existing one, its spent notes
// would get new nullifiers and could be spent again.
//
// Statement. Ten values, in this order:
//     [nf1, nf2, out_cm1, out_cm2, root, domain, public_amount, fee,
//      recipient, authorizer]
// They are private signals here and public in the settlement calldata. Hybrid
// compression (eprint 2025/1500) exposes three public signals instead of ten,
// which saves the verifier seven scalar multiplications:
//     alpha = keccak256(the ten values as 32-byte words) mod p, computed by
//             the pool and passed in as the one public input;
//     beta  = Poseidon(the ten values), an output;
//     gamma = x[0] + x[1]*s + ... + x[9]*s^9 at s = alpha + beta, an output
//             that the pool recomputes from its own copy of the values.
// circom puts outputs first, so the verifier's order is [beta, gamma, alpha].
// The verifier never sees the ten values, so the pool range-checks each one
// itself (see verifyProof in the dispatcher). The client (src/protocol.ts),
// the dispatcher and this circuit must agree on the order and encoding of the
// values, and a mismatch shows up only as an invalid proof.
//
// The rules, beyond each nullifier following from its note:
//   - An input with value must open at root. A zero-value input is not
//     checked, so a single note can be spent beside a fabricated dummy, which
//     adds no value.
//   - Every amount is below 2^128, and value is conserved.
//   - At least one input carries value.
//   - nf1 != nf2, so one note cannot be both inputs. EIP-8250 refuses a
//     repeated nonce key too, as defense in depth.
//   - A zero-value output k must use inner k + 1, which makes its commitment
//     Poseidon(2, k + 1, 0), ShieldedPoolLogic's SINK_k. Settlement does not
//     insert sinks, so a spend can leave an output empty without using tree
//     capacity, and a full tree never blocks a full withdrawal. A positive
//     output may use neither sink inner, so sink inners only ever carry zero.
//   - out_cm1 != out_cm2. Settlement refuses two equal outputs, and a sink
//     in the other position. The dispatcher checks neither before approving,
//     so the proof must, or an approved spend would fail in settlement and
//     burn its inputs.
//   - recipient and authorizer are addresses, the authorizer is nonzero, and
//     a recipient is named exactly when public_amount is positive. The
//     dispatcher and settlement require the same.
//
// The proof does not cover the rest of the transaction. Instead it names a
// fresh one-time secp256k1 authorizer, and the dispatcher
// (core/dispatcher/ShieldedPoolDispatcher.yul) requires the transaction's only
// signature to come from it. That signature covers the whole frame
// transaction, including the recent-root tuple, the gas and fee fields and any
// fourth frame. The dispatcher also binds the domain and the root to that
// tuple, checks the fee against the transaction's maximum cost, and requires
// the transaction's EIP-8250 nonce keys to be exactly {nf1, nf2} at sequence
// zero, so the protocol refuses a second spend of either note.
//
// A change to the relation needs new artifacts, a new verifier and a fresh
// pool; docs/design.md lists everything else it touches. A change to comments
// alone must keep every line of code on its line: circom builds line numbers
// into spend.wasm, which check-artifacts in the justfile rebuilds and compares
// byte for byte with core/artifacts/.

// circomlib, found through circom2's -l node_modules.
include "circomlib/circuits/poseidon.circom";
include "circomlib/circuits/bitify.circom";
include "circomlib/circuits/comparators.circom";

// One input note: its nullifier, and its membership at root when it has value.
template InputNote(DEPTH) {
    signal input root;
    signal input domain;
    signal input spend_key;
    signal input rho;
    signal input value;
    signal input siblings[DEPTH];
    signal input bits[DEPTH];
    signal output nf;

    var index = 0;
    for (var i = 0; i < DEPTH; i++) {
        bits[i] * (bits[i] - 1) === 0;
        index += bits[i] * (2 ** i);
    }

    component pk = Poseidon(3);
    pk.inputs[0] <== 1;
    pk.inputs[1] <== spend_key;
    pk.inputs[2] <== 0;
    component inner = Poseidon(2);
    inner.inputs[0] <== pk.out;
    inner.inputs[1] <== rho;
    component leaf = Poseidon(3);
    leaf.inputs[0] <== 2;
    leaf.inputs[1] <== inner.out;
    leaf.inputs[2] <== value;

    component node[DEPTH];
    signal left[DEPTH];
    signal right[DEPTH];
    signal cur[DEPTH + 1];
    cur[0] <== leaf.out;
    for (var i = 0; i < DEPTH; i++) {
        left[i] <== cur[i] + bits[i] * (siblings[i] - cur[i]);  // bits[i] = 1: sibling on the left
        right[i] <== siblings[i] + bits[i] * (cur[i] - siblings[i]);
        node[i] = Poseidon(2);
        node[i].inputs[0] <== left[i];
        node[i].inputs[1] <== right[i];
        cur[i + 1] <== node[i].out;
    }
    // Membership only for a note with value: a zero-value input may be a dummy.
    (cur[DEPTH] - root) * value === 0;

    // The domain carries the input's epoch and the index its leaf, so each funded
    // leaf has one nullifier. cm stays in so that a zero-value dummy, whose path is
    // not checked, cannot copy a funded note's nullifier with its key and index.
    component domainKey = Poseidon(2);
    domainKey.inputs[0] <== domain;
    domainKey.inputs[1] <== spend_key;
    component occurrence = Poseidon(2);
    occurrence.inputs[0] <== leaf.out;
    occurrence.inputs[1] <== index;
    component null = Poseidon(3);
    null.inputs[0] <== 4;
    null.inputs[1] <== domainKey.out;
    null.inputs[2] <== occurrence.out;
    nf <== null.out;
}

template Spend(DEPTH) {
    signal input root;
    signal input domain;
    signal input in_spend_key[2];
    signal input in_rho[2];
    signal input in_value[2];
    signal input in_siblings[2][DEPTH];
    signal input in_bits[2][DEPTH];
    signal input out_inner[2];   // a recipient reveals inner, never its secrets
    signal input out_value[2];
    signal input public_amount;  // credited to recipient as a withdrawal
    signal input fee;            // kept by the pool, which pays the gas
    signal input recipient;      // zero for a transfer, the withdrawal address otherwise
    signal input authorizer;     // the fresh secp256k1 address that signs this spend
    signal output nf1;
    signal output nf2;
    signal output out_cm1;
    signal output out_cm2;

    // inputs
    component note[2];
    for (var k = 0; k < 2; k++) {
        note[k] = InputNote(DEPTH);
        note[k].root <== root;
        note[k].domain <== domain;
        note[k].spend_key <== in_spend_key[k];
        note[k].rho <== in_rho[k];
        note[k].value <== in_value[k];
        for (var i = 0; i < DEPTH; i++) {
            note[k].siblings[i] <== in_siblings[k][i];
            note[k].bits[i] <== in_bits[k][i];
        }
    }

    // outputs: cm = Poseidon(2, inner, value), as shield computes it. A zero-value
    // output k is SINK_k (inner k + 1), a positive output uses neither sink inner, and
    // the two commitments differ (the header says why).
    var SINK_INNER_0 = 1;
    var SINK_INNER_1 = 2;
    component outCm[2];
    component outIsZero[2];
    component outEqSink0[2];
    component outEqSink1[2];
    for (var k = 0; k < 2; k++) {
        outCm[k] = Poseidon(3);
        outCm[k].inputs[0] <== 2;
        outCm[k].inputs[1] <== out_inner[k];
        outCm[k].inputs[2] <== out_value[k];

        outIsZero[k] = IsZero();
        outIsZero[k].in <== out_value[k];
        if (k == 0) {
            (out_inner[k] - SINK_INNER_0) * outIsZero[k].out === 0;
        } else {
            (out_inner[k] - SINK_INNER_1) * outIsZero[k].out === 0;
        }
        outEqSink0[k] = IsEqual();
        outEqSink0[k].in[0] <== out_inner[k];
        outEqSink0[k].in[1] <== SINK_INNER_0;
        outEqSink0[k].out * (1 - outIsZero[k].out) === 0;
        outEqSink1[k] = IsEqual();
        outEqSink1[k].in[0] <== out_inner[k];
        outEqSink1[k].in[1] <== SINK_INNER_1;
        outEqSink1[k].out * (1 - outIsZero[k].out) === 0;
    }

    // Amounts below 2^128 keep both sides below 2^130, so the sum cannot wrap mod p.
    component rc[6];
    var vals[6] = [in_value[0], in_value[1], out_value[0], out_value[1], public_amount, fee];
    for (var k = 0; k < 6; k++) {
        rc[k] = Num2Bits(128);
        rc[k].in <== vals[k];
    }
    in_value[0] + in_value[1] === out_value[0] + out_value[1] + public_amount + fee;

    // A spend must consume value. Two fabricated zero-value inputs would otherwise make
    // a valid spend that stores two new nonce keys, free on a chain with zero base fee.
    component noRealInput = IsZero();
    noRealInput.in <== in_value[0] + in_value[1];
    noRealInput.out === 0;

    // recipient and authorizer are addresses and the authorizer is nonzero. A
    // recipient is named exactly when public_amount is positive, as the dispatcher
    // and settlement also require.
    component recipientBits = Num2Bits(160);
    recipientBits.in <== recipient;
    component authorizerBits = Num2Bits(160);
    authorizerBits.in <== authorizer;
    component authorizerIsZero = IsZero();
    authorizerIsZero.in <== authorizer;
    authorizerIsZero.out === 0;
    component publicIsZero = IsZero();
    publicIsZero.in <== public_amount;
    component recipientIsZero = IsZero();
    recipientIsZero.in <== recipient;
    publicIsZero.out === recipientIsZero.out;

    nf1 <== note[0].nf;
    nf2 <== note[1].nf;
    component sameNullifier = IsEqual();  // one note cannot be both inputs
    sameNullifier.in[0] <== nf1;
    sameNullifier.in[1] <== nf2;
    sameNullifier.out === 0;
    out_cm1 <== outCm[0].out;
    out_cm2 <== outCm[1].out;
    component sameOutput = IsEqual();  // settlement refuses equal outputs
    sameOutput.in[0] <== out_cm1;
    sameOutput.in[1] <== out_cm2;
    sameOutput.out === 0;
}

// The spend with its ten-value statement compressed to (beta, gamma, alpha).
template CompressedSpend(DEPTH) {
    signal input alpha;
    signal input root;
    signal input domain;
    signal input in_spend_key[2];
    signal input in_rho[2];
    signal input in_value[2];
    signal input in_siblings[2][DEPTH];
    signal input in_bits[2][DEPTH];
    signal input out_inner[2];
    signal input out_value[2];
    signal input public_amount;
    signal input fee;
    signal input recipient;
    signal input authorizer;
    signal output beta;
    signal output gamma;

    component spend = Spend(DEPTH);
    spend.root <== root;
    spend.domain <== domain;
    for (var k = 0; k < 2; k++) {
        spend.in_spend_key[k] <== in_spend_key[k];
        spend.in_rho[k] <== in_rho[k];
        spend.in_value[k] <== in_value[k];
        for (var i = 0; i < DEPTH; i++) {
            spend.in_siblings[k][i] <== in_siblings[k][i];
            spend.in_bits[k][i] <== in_bits[k][i];
        }
        spend.out_inner[k] <== out_inner[k];
        spend.out_value[k] <== out_value[k];
    }
    spend.public_amount <== public_amount;
    spend.fee <== fee;
    spend.recipient <== recipient;
    spend.authorizer <== authorizer;

    signal stmt[10];
    stmt[0] <== spend.nf1;
    stmt[1] <== spend.nf2;
    stmt[2] <== spend.out_cm1;
    stmt[3] <== spend.out_cm2;
    stmt[4] <== root;
    stmt[5] <== domain;
    stmt[6] <== public_amount;
    stmt[7] <== fee;
    stmt[8] <== recipient;
    stmt[9] <== authorizer;

    component digest = Poseidon(10);
    for (var i = 0; i < 10; i++) {
        digest.inputs[i] <== stmt[i];
    }
    beta <== digest.out;

    // Horner's rule, highest coefficient first.
    signal sigma;
    sigma <== alpha + beta;
    signal acc[10];
    acc[9] <== stmt[9];
    for (var i = 9; i > 0; i--) {
        acc[i - 1] <== acc[i] * sigma + stmt[i - 1];
    }
    gamma <== acc[0];
}

component main {public [alpha]} = CompressedSpend(20);
