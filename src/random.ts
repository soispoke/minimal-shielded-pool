/**
 * Randomness for secrets. Every function that draws takes an Rng, so a fixture generator
 * can pass a seeded stream and get the same notes, keys and witnesses on every run, while
 * the wallet passes secureRng. Nothing reads a global generator.
 */
import { randomFillSync } from "node:crypto";

import { concat, keccak, toBigint, word } from "./bytes.ts";

export interface Rng {
  /** A uniform integer in [0, 2^k). */
  bits(k: number): bigint;
  /** A uniform integer in [0, n), for n > 0. */
  below(n: bigint): bigint;
  /** n uniform bytes. */
  bytes(n: number): Uint8Array;
}

/** Builds bits and below on a source of uniform bytes, drawing whole bytes per call. */
function rngFrom(next: (n: number) => Uint8Array): Rng {
  const bits = (k: number): bigint => {
    if (!Number.isSafeInteger(k) || k < 0) throw new RangeError(`cannot draw ${k} bits`);
    return toBigint(next(Math.ceil(k / 8))) & ((1n << BigInt(k)) - 1n);
  };
  return {
    bits,
    // Rejection sampling keeps the result uniform: a draw of n's bit length is below n
    // with probability at least one half, and a draw at or above n is discarded, not reduced.
    below(n) {
      if (n <= 0n) throw new RangeError(`cannot draw below ${n}`);
      const k = n.toString(2).length;
      for (;;) {
        const r = bits(k);
        if (r < n) return r;
      }
    },
    bytes(n) {
      if (!Number.isSafeInteger(n) || n < 0) throw new RangeError(`cannot draw ${n} bytes`);
      return next(n);
    },
  };
}

/** Cryptographic randomness from the operating system, for real notes and keys. */
export const secureRng: Rng = rngFrom((n) => randomFillSync(new Uint8Array(n)));

/**
 * A reproducible stream for test fixtures, never for real funds: anyone who knows the seed
 * knows every secret drawn from it. The stream is block i = keccak256(seed || i), with seed
 * and i as 32-byte big-endian words and i counting from 0, read as one byte string. Each
 * call takes the next bytes it needs (bits(k) takes ceil(k/8) bytes, big-endian, and keeps
 * the low k bits), so outputs depend on the exact order and size of every call. Committed
 * fixtures depend on this definition.
 */
export function seededRng(seed: bigint): Rng {
  const key = word(seed);
  let counter = 0n;
  let block: Uint8Array = new Uint8Array(0);
  return rngFrom((n) => {
    const out = new Uint8Array(n);
    for (let filled = 0; filled < n;) {
      if (block.length === 0) block = keccak(concat(key, word(counter++)));
      const take = Math.min(n - filled, block.length);
      out.set(block.subarray(0, take), filled);
      block = block.subarray(take);
      filled += take;
    }
    return out;
  });
}
