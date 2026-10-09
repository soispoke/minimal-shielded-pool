/**
 * The EIP-8272 recent-root window, checked at both boundaries and on the spend path. Runs in
 * about 0.1 s.
 *
 *   node --test test/pool-recent-root-window.test.ts
 *
 * The wallet must refuse exactly the publication slots the node refuses. Admission judges a
 * transaction against the earliest block that could carry it, so the node's current slot is the
 * head slot plus one. A wallet that compares against the head slot is one slot too generous at
 * the old end: it signs a transaction the node rejects, and the operator sees only a mempool
 * refusal for a proof already spent.
 */
import assert from "node:assert/strict";
import { test } from "node:test";

import { concat, hex32, keccak, toBytes, toHex, word } from "../src/bytes.ts";
import { PoolError } from "../src/errors.ts";
import { RECENT_ROOT_TUPLE_BYTES } from "../src/gas.ts";
import { recentRootReference, recentRootWindowError } from "../src/deployment.ts";
import { RECENT_ROOT_LENGTH, recentRootTuple, sourceId } from "../src/protocol.ts";
import type { PoolNode } from "../src/rpc.ts";
import { waitPublishedSlot } from "../src/send.ts";

// Mirrors ethrex's FRAME_TX_RECENT_ROOT_USABLE_WINDOW: the node rejects when
// `current_slot - slot` exceeds it.
const USABLE_WINDOW = RECENT_ROOT_LENGTH - 1n;
const HEAD = 100_000n;

test("the window constants", () => {
  assert.equal(RECENT_ROOT_LENGTH, 8192n);
  assert.equal(USABLE_WINDOW, 8191n);
  assert.equal(RECENT_ROOT_TUPLE_BYTES, 72);
  assert.equal(recentRootTuple(sourceId(1n, 0n), 1n, 1n).length, RECENT_ROOT_TUPLE_BYTES);
});

// Stated as outcomes rather than as agreement, so the test still means something if the wallet
// and the restated node rule below are changed together by mistake. Ages count from the head
// slot, which is what an operator reads off the chain.
test("the boundaries, and which end of the window a refusal crossed", () => {
  const expired = ["expired", "publishEpochRoot(7)"];
  for (const [slot, texts] of [
    [HEAD - 8190n, []],
    [HEAD - 8191n, expired], // it used to pass here and fail on chain
    [HEAD - 8192n, expired],
    [HEAD, []], // a head-slot root is usable from the next slot
    [HEAD + 1n, ["not yet referenceable", `current slot ${HEAD + 1n}`]],
  ] as const) {
    const error = recentRootWindowError(slot, HEAD, 7n);
    if (texts.length === 0) assert.equal(error, null, `slot ${slot}`);
    for (const text of texts) assert.ok(error?.includes(text), `${text} not in ${error}`);
  }
});

test("the wallet agrees with the node over the whole window", () => {
  // What ethrex's `check_recent_root_frame_at_root` decides, restated here.
  const current = HEAD + 1n;
  const nodeRejects = (slot: bigint) => slot >= current || current - slot > USABLE_WINDOW;
  for (let age = 0n; age < USABLE_WINDOW + 3n; age++) {
    const slot = HEAD - age;
    const walletRejects = recentRootWindowError(slot, HEAD) !== null;
    assert.equal(walletRejects, nodeRejects(slot), `disagreement at age ${age}`);
  }
});

// The spend path applies the same window before it reads the recent-root contract, so a root
// that has left the window is refused before anything is signed. Inside the window, the slot
// must hold this root's entry; an empty slot does not. The contract's entry and storage key are
// written out here from EIP-8272's definitions, not read from the client.
test("the spend path refuses a root outside the window or not held at its slot", async () => {
  const [pool, epoch, root] = [0xbeefn, 2n, 0x1234n];
  const source = keccak(concat(toBytes(pool, 20), word(epoch)));
  const at = (tag: string, slot: bigint, ...rest: Uint8Array[]) =>
    toHex(keccak(concat(keccak(new TextEncoder().encode(tag)), source, toBytes(slot, 8), ...rest)));

  async function reference(
    slot: bigint,
    stored = at("RECENT_ROOT_ENTRY", slot, word(root)),
  ): Promise<{ result: unknown; reads: number }> {
    let reads = 0;
    const node: PoolNode = {
      async call(method, params) {
        if (method === "eth_getBlockByNumber") return { slotNumber: "0x" + HEAD.toString(16) };
        assert.equal(method, "eth_getStorageAt");
        reads++;
        assert.equal(BigInt(params[0] as string), 0x8272n, "the recent-root contract");
        assert.equal(params[1], at("RECENT_ROOT_STORAGE", slot % RECENT_ROOT_LENGTH));
        return stored;
      },
      simulate: async () => assert.fail("simulated"),
    };
    const recent = { rootSlot: slot, epoch, root };
    const result = await recentRootReference(node, pool, recent).catch((error: unknown) => error);
    return { result, reads };
  }

  const inside = await reference(HEAD - 8190n);
  assert.deepEqual(inside.result, concat(source, toBytes(HEAD - 8190n, 8), word(root)));
  assert.equal(inside.reads, 1);
  const empty = await reference(HEAD - 8190n, hex32(0n));
  assert.ok(empty.result instanceof PoolError, String(empty.result));
  assert.ok(empty.result.message.includes("self-check failed"), empty.result.message);
  for (const [slot, text] of [
    [HEAD - 8191n, "expired"],
    [HEAD + 1n, "not yet referenceable"],
  ] as const) {
    const { result, reads } = await reference(slot);
    assert.ok(result instanceof PoolError, String(result));
    assert.ok(result.message.includes(text), result.message);
    assert.equal(reads, 0, `slot ${slot} was read`);
  }
});

// The slot a spend references is read from the publication block once two blocks follow it, so a
// head one block past publication is still waiting.
test("the publication slot is not read one block after publication", async () => {
  const node: PoolNode = { call: async () => "0xb", simulate: async () => assert.fail() };
  const receipt = { blockNumber: "0xa", blockHash: hex32(1n) };
  const waiting = waitPublishedSlot(node, { log: () => {}, now: () => 0 }, receipt, 0);
  await assert.rejects(waiting, /timed out waiting for 2 blocks after publish at 10 \(head 11\)/);
});
