/**
 * Bytes, hex and integers. Protocol integers are bigint everywhere. Parsing is
 * strict on purpose: BigInt("") is 0 and BigInt("0b11") is 3, so every value
 * read from a file, the command line or a node goes through these helpers.
 */
import { keccak_256 } from "@noble/hashes/sha3.js";
import { bytesToHex, concatBytes, hexToBytes } from "@noble/hashes/utils.js";

import { InputError } from "./errors.ts";

export { concatBytes as concat };

export function keccak(data: Uint8Array): Uint8Array {
  return keccak_256(data);
}

/** "0x" followed by two lowercase hex digits per byte. */
export function toHex(bytes: Uint8Array): string {
  return "0x" + bytesToHex(bytes);
}

/** Decodes "0x"-prefixed hex, optionally of an exact byte length. */
export function fromHex(text: unknown, what: string, length?: number): Uint8Array {
  if (typeof text !== "string" || !/^0x([0-9a-fA-F]{2})*$/.test(text)) {
    throw new InputError(`${what} must be 0x-prefixed hex with whole bytes`);
  }
  const bytes = hexToBytes(text.slice(2));
  if (length !== undefined && bytes.length !== length) {
    throw new InputError(`${what} must be ${length} bytes, got ${bytes.length}`);
  }
  return bytes;
}

export function toBigint(bytes: Uint8Array): bigint {
  return bytes.length === 0 ? 0n : BigInt(toHex(bytes));
}

/** Big-endian encoding in exactly `length` bytes; never truncates. */
export function toBytes(value: bigint, length: number): Uint8Array {
  if (value < 0n || value >= 1n << BigInt(8 * length)) {
    throw new RangeError(`${value} does not fit in ${length} bytes`);
  }
  return hexToBytes(value.toString(16).padStart(2 * length, "0"));
}

/** One 32-byte big-endian word, the encoding of a field element or uint256. */
export function word(value: bigint): Uint8Array {
  return toBytes(value, 32);
}

/** The canonical bytes32 hex of a field element: "0x" and 64 lowercase digits. */
export function hex32(value: bigint): string {
  return toHex(word(value));
}

/** "0x" and at least `digits` lowercase hex digits, never truncated. */
export function hexPadded(value: bigint, digits: number): string {
  if (value < 0n) throw new RangeError(`${value} is negative`);
  return "0x" + value.toString(16).padStart(digits, "0");
}

/** "0x"-prefixed hex of any length, as nodes write integers; null for any other form. */
export function hexFromText(text: unknown): bigint | null {
  return typeof text === "string" && /^0x[0-9a-fA-F]+$/.test(text) ? BigInt(text) : null;
}

/** hexFromText, refusing any other form. */
export function parseHex(text: unknown, what: string): bigint {
  const value = hexFromText(text);
  if (value === null) throw new InputError(`${what} must be 0x-prefixed hex`);
  return value;
}

/** A non-negative decimal integer, as a JSON number or a string of digits. */
export function parseDec(value: unknown, what: string): bigint {
  if (typeof value === "number" && Number.isSafeInteger(value) && value >= 0) {
    return BigInt(value);
  }
  if (typeof value === "bigint" && value >= 0n) return value;
  if (typeof value === "string" && /^[0-9]+$/.test(value)) return BigInt(value);
  throw new InputError(`${what} must be a non-negative decimal integer`);
}

/** A non-negative integer written as decimal digits or "0x" hex, nothing else. */
export function parseUint(text: unknown, what: string): bigint {
  if (typeof text === "string" && /^0x[0-9a-fA-F]+$/.test(text)) return BigInt(text);
  if (typeof text === "string" && /^[0-9]+$/.test(text)) return BigInt(text);
  throw new InputError(`${what} must be a non-negative integer, in decimal or 0x hex`);
}

/**
 * A non-negative integer as a person or a node types it: "0x" hex, or decimal without leading
 * zeros, since 010 could mean ten or eight. Null for any other form, so that each caller names
 * its own refusal.
 */
export function uintFromText(text: string): bigint | null {
  return /^(0x[0-9a-fA-F]+|0+|[1-9][0-9]*)$/.test(text) ? BigInt(text) : null;
}

/**
 * An address as fixtures, receipts and nodes write it, and as the generators' --pool-address
 * takes it for the fixture: "0x" and exactly 40 hex digits, in any case. Null for any other form.
 */
export function addressFromText(text: unknown): bigint | null {
  return typeof text === "string" && /^0x[0-9a-fA-F]{40}$/.test(text) ? BigInt(text) : null;
}

/** addressFromText, refusing any other form without repeating it, in case a key was pasted. */
export function parseAddress(text: unknown, what: string): bigint {
  const value = addressFromText(text);
  if (value === null) throw new InputError(`${what} must be 0x and 40 hex digits`);
  return value;
}

/**
 * An address as a person writes it in a deployment config: "0x" and 1 to 40 hex digits in any
 * case, so EIP-55 checksummed addresses and short ones such as 0x01 read (critic G10).
 */
export function parseConfigAddress(text: unknown, what: string): bigint {
  if (typeof text !== "string" || !/^0x[0-9a-fA-F]{1,40}$/.test(text)) {
    throw new InputError(`${what} must be 0x and 1 to 40 hex digits`);
  }
  return BigInt(text);
}

/** Orders bigints for sort(): negative, zero or positive as a is below, equal to or above b. */
export function compareBigint(a: bigint, b: bigint): number {
  return a < b ? -1 : a > b ? 1 : 0;
}

export function maxBigint(a: bigint, b: bigint): bigint {
  return a > b ? a : b;
}

/** Floor modulo: the result is in [0, m) even for negative x, unlike JavaScript's %. */
export function mod(x: bigint, m: bigint): bigint {
  const r = x % m;
  return r < 0n ? r + m : r;
}

export function equalBytes(a: Uint8Array, b: Uint8Array): boolean {
  return a.length === b.length && a.every((byte, i) => byte === b[i]);
}
