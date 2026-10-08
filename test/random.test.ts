/**
 * The seeded stream's definition, recomputed here from keccak alone: committed fixtures depend
 * on it, so a change to random.ts must show up as a failure, not as new fixtures. secureRng,
 * which every real secret comes from, draws fresh bytes on each call.
 */
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { test } from "node:test";

import { concat, keccak, toBigint, word } from "../src/bytes.ts";
import { secureRng, seededRng } from "../src/random.ts";

/** The stream's first three blocks, keccak(seed || i). */
const stream = (seed: bigint) =>
  concat(...[0n, 1n, 2n].map((i) => keccak(concat(word(seed), word(i)))));

test("bytes follow keccak(seed || i) across block boundaries", () => {
  const rng = seededRng(7n);
  assert.deepEqual(concat(rng.bytes(5), rng.bytes(40), rng.bytes(25)), stream(7n).subarray(0, 70));
});

test("bits takes whole bytes, big-endian, and keeps the low bits", () => {
  const rng = seededRng(9n);
  assert.equal(rng.bits(12), toBigint(stream(9n).subarray(0, 2)) & 0xfffn);
  assert.equal(rng.bits(256), toBigint(stream(9n).subarray(2, 34)));
});

test("below rejects a draw at or above n instead of reducing it", () => {
  // Find a seed whose first draw is at least n and second below it: below must skip the first.
  const n = (1n << 255n) + 1n;
  for (let seed = 0n; ; seed++) {
    const [first, second] = [0, 32].map((at) => toBigint(stream(seed).subarray(at, at + 32)));
    if (first >= n && second < n) return assert.equal(seededRng(seed).below(n), second);
  }
});

test("secureRng draws fresh bytes on each call and in each process", () => {
  assert.notDeepEqual(secureRng.bytes(32), secureRng.bytes(32));
  // A stream with a fixed seed passes the check above, but repeats itself in the next run.
  const module = JSON.stringify(new URL("../src/random.ts", import.meta.url).href);
  const script = `import { secureRng } from ${module};
    process.stdout.write(Buffer.from(secureRng.bytes(32)).toString("hex"));`;
  const draw = () => execFileSync(process.execPath, ["--input-type=module", "-e", script]);
  assert.notDeepEqual(draw(), draw());
});
