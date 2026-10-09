/**
 * The EIP-8141 frame transaction encoder (src/frametx.ts): its envelope shape, its gas, and its
 * break from the dialect the pre-relaunch chain-8141 deployment uses. Runs in about 0.1 s. The
 * live-node group offers the bytes to a live ethrex, the authoritative check (an encoder that
 * only agrees with itself proves nothing); it is manual, in neither the justfile nor CI:
 *   FRAMETX_NODE_RPC=http://127.0.0.1:8545 node --test test/frametx.test.ts
 */
import assert from "node:assert/strict";
import { describe, test } from "node:test";

import { concat, keccak, toBytes, toHex } from "../src/bytes.ts";
import {
  calldataFloorGas,
  encodeTx,
  executionCapUsage,
  mandatoryGas,
  maxCost,
  rawTx,
  recoverSigner,
  rlpBytes,
  rlpInt,
  rlpItems,
  rlpList,
  SCHEME,
  sigHash,
  signHash,
  standardGasLimit,
  totalGasLimit,
  type Frame,
  type FrameTx,
} from "../src/frametx.ts";

const hex = (bytes: Uint8Array) => toHex(bytes).slice(2);
const ones = (n: number) => new Uint8Array(n).fill(0x01);
const EMPTY = new Uint8Array(0);

function frame(mode: bigint, flags: bigint, to: bigint | null, gas: bigint, more?: Partial<Frame>) {
  const rest = { stateLimit: 0n, value: 0n, data: EMPTY, ...more };
  return { mode, flags, target: to, gasLimit: gas, ...rest };
}

/**
 * The transaction the archived evidence pins (evidence/vectors/2026-09-01-hegota-final-profile/
 * frametx.py): a targetless VERIFY frame approving execution and payment, then a SENDER call.
 */
function build(): FrameTx {
  return {
    chainId: 1n,
    nonceKeys: [0n],
    nonceSeq: 7n,
    sender: 0xabcdn,
    frames: [
      frame(1n, 3n, null, 0x5208n, { data: Uint8Array.of(0x11, 0x22) }),
      frame(2n, 0n, 0x1234n, 0x9c40n),
    ],
    signatures: [{ scheme: SCHEME.SECP256K1, signer: 0xabcdn, msg: EMPTY, signature: ones(65) }],
    maxPriorityFee: 0x3b9aca00n,
    maxFee: 0x6fc23ac00n,
    maxBlobFee: 0n,
    blobHashes: [],
  };
}

/** build() with frame i's fields replaced. */
function edited(i: number, fields: Partial<Frame>): FrameTx {
  const tx = build();
  Object.assign(tx.frames[i], fields);
  return tx;
}

/**
 * The archived pre-relaunch envelope: 11 fields (three fee scalars, blob fields and an EIP-8272
 * reference list) and one gas limit per frame. The archive is Python and never edited, so it is
 * copied here, and a test below pins the copy to the archive's own golden. With `elide`, a
 * signature with an empty msg is written as empty bytes, the form the signature hash covers.
 */
function frozenEnvelope(tx: FrameTx, elide: boolean): Uint8Array {
  const address = (a: bigint | null) => rlpBytes(a === null ? EMPTY : toBytes(a, 20));
  const frames = tx.frames.map((f) => {
    const [mode, flags, gas, value] = [f.mode, f.flags, f.gasLimit, f.value].map(rlpInt);
    return rlpList([mode, flags, address(f.target), gas, value, rlpBytes(f.data)]);
  });
  const signatures = tx.signatures.map((s) => {
    const signature = elide && s.msg.length === 0 ? EMPTY : s.signature;
    return rlpList([rlpInt(s.scheme), address(s.signer), rlpBytes(s.msg), rlpBytes(signature)]);
  });
  return rlpList([
    rlpInt(tx.chainId),
    rlpList(tx.nonceKeys.map(rlpInt)),
    rlpInt(tx.nonceSeq),
    address(tx.sender),
    rlpList(frames),
    rlpList(signatures),
    ...[tx.maxPriorityFee, tx.maxFee, tx.maxBlobFee].map(rlpInt),
    rlpList(tx.blobHashes.map(rlpBytes)),
    rlpList([]),
  ]);
}
const frozenRaw = (tx: FrameTx) => concat(Uint8Array.of(0x06), frozenEnvelope(tx, false));

const SIGNATURE_HEX = "01".repeat(65);

// The archive's own golden for build(): EXPECT_RLP and EXPECT_SIGHASH. Its EXPECT_TOTAL_GAS,
// 80,974, is 3,000 above the spec's (the intrinsic fell from 15,000 to 12,000).
const FROZEN_RLP =
  "f8ae01c1800794000000000000000000000000000000000000abcde8ca01038082520880821122dc" +
  "0280940000000000000000000000000000000000001234829c408080f85cf85a0194000000000000" +
  "000000000000000000000000abcd80b841" +
  SIGNATURE_HEX +
  "843b9aca008506fc23ac0080c0c0";
const FROZEN_SIGHASH = "989e6ce4dc87b2afd5cfa6c780ff60f01fc3b40c77057cf872410145d69f715c";

describe("the frame transaction envelope", () => {
  // Not 11: the three fee scalars became one list, EIP-8272's reference list left the envelope
  // for a canonical VERIFY frame, and each frame's one gas limit became [execution, state].
  test("has 8 top-level fields, nested fees and [execution, state] limits per frame", () => {
    const fields = rlpItems(encodeTx(build()));
    assert.equal(fields.length, 8);
    assert.equal(rlpItems(fields[6]).length, 3, "field 6 is the nested fees list");
    const frame0 = rlpItems(rlpItems(fields[4])[0]);
    assert.equal(frame0.length, 6);
    assert.equal(rlpItems(frame0[3]).length, 2, "the limits field is a 2-element list");
  });

  test("the frozen copy reproduces the archive's golden; the spec envelope differs", () => {
    const frozenHash = keccak(concat(Uint8Array.of(0x06), frozenEnvelope(build(), true)));
    assert.equal(hex(frozenEnvelope(build(), false)), FROZEN_RLP);
    assert.equal(hex(frozenHash), FROZEN_SIGHASH);
    assert.notEqual(hex(encodeTx(build())), FROZEN_RLP);
    assert.notEqual(hex(sigHash(build())), FROZEN_SIGHASH);
  });
});

describe("gas", () => {
  test("a frame moving value to another account adds TX_VALUE_COST, and only then", () => {
    const base = build();
    assert.equal(totalGasLimit(edited(1, { value: 1n })) - totalGasLimit(base), 6_000n);
    assert.equal(mandatoryGas(edited(0, { value: 1n })), mandatoryGas(base), "targetless frame");
    const selfPay = edited(1, { value: 1n, target: base.sender });
    assert.equal(mandatoryGas(selfPay), mandatoryGas(base), "value to the sender itself");
  });

  test("the calldata floor prices zero and nonzero bytes alike; the standard charge does not", () => {
    const zeros = edited(0, { data: new Uint8Array(64) });
    const nonzero = edited(0, { data: ones(64) });
    assert.equal(calldataFloorGas(zeros), calldataFloorGas(nonzero));
    assert.equal(standardGasLimit(nonzero) - standardGasLimit(zeros), 64n * 12n);
  });
});

/** The spec encoding and signature hash of `tx`. */
const encoded = (tx: FrameTx) => [hex(encodeTx(tx)), hex(sigHash(tx))];
/** The raw length, then mandatory, standard, calldata floor, execution cap and total gas. */
const GAS = [mandatoryGas, standardGasLimit, calldataFloorGas, executionCapUsage, totalGasLimit];
const costs = (tx: FrameTx) => [BigInt(rawTx(tx).length), ...GAS.map((f) => f(tx))];

// Computed by the Python client (sdk/frametx.py at commit 2386147), so these bytes and gas are
// pinned to the implementation this encoder replaced, not only to themselves.
describe("parity with the Python encoder", () => {
  // limits.state adds exactly its amount to max_gas, and nothing to the execution cap.
  test("the evidence transaction, and with limits.state 97920 on frame 0", () => {
    const tx = build();
    assert.deepEqual(encoded(tx), [
      "f8b201c1800794000000000000000000000000000000000000abcdeccc010380c482520880808211" +
        "22de0280940000000000000000000000000000000000001234c4829c40808080f85cf85a01940000" +
        "00000000000000000000000000000000abcd80b841" +
        SIGNATURE_HEX +
        "cc843b9aca008506fc23ac0080c0",
      "73827d510b0029220c237a46b27f6b6b8e7a3fd3b52c42a55c6c6e343fc45951",
    ]);
    assert.deepEqual(costs(tx), [181n, 15_750n, 77_974n, 21_510n, 77_974n, 77_974n]);
    assert.equal(maxCost(tx), 2_339_220_000_000_000n);

    const stated = edited(0, { stateLimit: 97_920n });
    assert.deepEqual(encoded(stated), [
      "f8b501c1800794000000000000000000000000000000000000abcdefcf010380c782520883017e80" +
        "80821122de0280940000000000000000000000000000000000001234c4829c40808080f85cf85a01" +
        "94000000000000000000000000000000000000abcd80b841" +
        SIGNATURE_HEX +
        "cc843b9aca008506fc23ac0080c0",
      "1cc58f7cffff92a6bc5ef6f5de7a30f75f337a5e0252d3fda1c987cbe9d94497",
    ]);
    assert.equal(totalGasLimit(stated), 175_894n);
    assert.equal(executionCapUsage(stated), 77_974n, "state is not execution");
  });

  test("a signature with a message (no elision), a state limit and blob fields", () => {
    const tx: FrameTx = {
      ...build(),
      frames: edited(0, { stateLimit: 97_920n }).frames.slice(0, 1),
      signatures: [{ ...build().signatures[0], msg: ones(32) }],
      maxBlobFee: 5n,
      blobHashes: [new Uint8Array(32).fill(0x02)],
    };
    assert.deepEqual(encoded(tx), [
      "f8d701c1800794000000000000000000000000000000000000abcdd0cf010380c782520883017e80" +
        "80821122f87cf87a0194000000000000000000000000000000000000abcda0" +
        "01".repeat(32) +
        "b841" +
        SIGNATURE_HEX +
        "cc843b9aca008506fc23ac0005e1a0" +
        "02".repeat(32),
      "3f8a959889402765838595c5fb5171a4474946898594e09d37a9738ddbd57a78",
    ]);
    assert.equal(totalGasLimit(tx), 135_931n);
    assert.equal(maxCost(tx, 3n), 4_077_930_000_393_216n);
  });

  // The branches the evidence transaction does not reach: the first long RLP header (a 56-byte
  // string) beside the last short one (55 bytes), the single byte 0x80 and the integer 128 (both
  // need a header, unlike 0x7f), P256 and ARBITRARY signature costs, and value moved to another
  // account and to the sender itself.
  test("RLP header boundaries, P256 and ARBITRARY signatures, and value of 128", () => {
    const b80 = Uint8Array.of(0x80);
    const tx: FrameTx = {
      ...build(),
      nonceKeys: [0n, 128n],
      nonceSeq: 128n,
      frames: [
        frame(1n, 3n, null, 0x5208n, { data: b80 }),
        frame(2n, 0n, 0x1234n, 0x9c40n, { stateLimit: 128n, value: 128n, data: ones(56) }),
        frame(2n, 0n, 0xabcdn, 0x9c40n, { value: 1n, data: new Uint8Array(55).fill(0x7f) }),
      ],
      signatures: [
        { scheme: SCHEME.P256, signer: 0xabcdn, msg: EMPTY, signature: ones(64) },
        { scheme: SCHEME.ARBITRARY, signer: 0x1234n, msg: b80, signature: Uint8Array.of(2, 2, 2) },
      ],
      maxPriorityFee: 128n,
    };
    assert.deepEqual(encoded(tx), [
      "f9016101c3808180818094000000000000000000000000000000000000abcdf8becb010380c482520880" +
        "808180f8590280940000000000000000000000000000000000001234c5829c4081808180b838" +
        "01".repeat(56) +
        "f855028094000000000000000000000000000000000000abcdc4829c408001b7" +
        "7f".repeat(55) +
        "f878f8590294000000000000000000000000000000000000abcd80b840" +
        "01".repeat(64) +
        "dc80940000000000000000000000000000000000001234818083020202c981808506fc23ac0080c0",
      "c790652d8e860a5a7e492597662f7420cab6cfbae54828181d4dbe0699b56395",
    ]);
    // Mandatory: 12000 + 3 frames at 475 + P256 6700 + ARBITRARY 100 + one TX_VALUE_COST 6000.
    assert.deepEqual(costs(tx), [357n, 26_225n, 130_537n, 40_689n, 130_409n, 130_537n]);
    assert.equal(maxCost(tx), 3_916_110_000_000_000n);
  });
});

const NODE = process.env.FRAMETX_NODE_RPC;
const SENDER = 0xd277b144f4c62839ef04bd4282d1d852d4a956e3n;

async function call(method: string, params: unknown[]): Promise<Record<string, unknown>> {
  const response = await fetch(NODE as string, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ jsonrpc: "2.0", id: 1, method, params }),
    signal: AbortSignal.timeout(25_000),
  });
  return (await response.json()) as Record<string, unknown>;
}

/** A self-verify shape: one VERIFY frame approving execution and payment, then a call. */
function selfVerify(chainId: bigint, stateLimit = 0n): FrameTx {
  return {
    ...build(),
    chainId,
    nonceSeq: 0n,
    sender: SENDER,
    frames: [frame(1n, 3n, SENDER, 80_000n, { stateLimit }), frame(2n, 0n, 0xc0den, 30_000n)],
    signatures: [{ ...build().signatures[0], signer: SENDER }],
    maxPriorityFee: 10n ** 9n,
    maxFee: 10n ** 10n,
  };
}

// ethrex_simulateFrameTransaction decodes canonically before judging anything, so a business
// verdict (valid true or false) under `result` means the envelope parsed, and an error means the
// bytes did not decode. The frozen envelope is the control: if the node accepts both encodings,
// it is not enforcing the format either encoder targets, and neither result means anything.
describe(
  "against a live ethrex (FRAMETX_NODE_RPC)",
  { skip: NODE ? false : "FRAMETX_NODE_RPC is not set" },
  () => {
    const cases: [label: string, raw: (chainId: bigint) => Uint8Array, decodes: boolean][] = [
      ["decodes the spec envelope", (id) => rawTx(selfVerify(id)), true],
      ["rejects the frozen envelope on a spec chain", (id) => frozenRaw(selfVerify(id)), false],
      ["decodes a frame that declares limits.state", (id) => rawTx(selfVerify(id, 97_920n)), true],
    ];
    for (const [label, raw, decodes] of cases) {
      test(`the node ${label}`, async () => {
        const chainId = BigInt((await call("eth_chainId", [])).result as string);
        const out = await call("ethrex_simulateFrameTransaction", [toHex(raw(chainId))]);
        assert.equal("result" in out, decodes, JSON.stringify(out));
      });
    }
  },
);

// A frame signature covers the 32-byte signature hash itself; any other length is a caller bug,
// refused rather than signed.
test("signing and recovery take exactly a 32-byte hash", () => {
  const key = toBytes(1n, 32);
  const signature = signHash(new Uint8Array(32), key);
  for (const length of [0, 31, 33]) {
    assert.throws(() => signHash(new Uint8Array(length), key), RangeError);
    assert.throws(() => recoverSigner(new Uint8Array(length), signature), RangeError);
  }
});
