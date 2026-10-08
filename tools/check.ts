/**
 * What the repository checks share: the repository root, strict UTF-8, refusals as CheckError,
 * and JSON read with its objects in file order. It imports no packages, so check-formal-pins.ts
 * still runs where nothing is installed.
 */
import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { CheckError } from "../src/errors.ts";

export const ROOT = resolve(import.meta.dirname, "..");

/** Strict UTF-8 that keeps a leading byte order mark: the text is exactly the file's bytes. */
export const utf8 = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });

/** The text of a file, decoded as strict UTF-8. */
export function readText(path: string | URL): string {
  return utf8.decode(readFileSync(path));
}

/** Refuses with message unless condition holds. */
export function check(condition: boolean, message: string): asserts condition {
  if (!condition) throw new CheckError(message);
}

// Reads from parseInOrder's objects refuse a missing key or a value of the wrong type, where
// JavaScript would quietly answer (undefined >= n is false).

/** A JSON object from parseInOrder, or a refusal naming it. */
export function object(value: unknown, what: string): Map<string, unknown> {
  if (!(value instanceof Map)) throw new CheckError(`${what} must be a JSON object`);
  return value;
}

/** The key's value, or null when the object lacks the key. */
export function get(value: unknown, key: string, where: string): unknown {
  return object(value, where).get(key) ?? null;
}

/** The key's value; the object must have the key. */
export function field(value: unknown, key: string, where: string): unknown {
  if (!object(value, where).has(key)) throw new CheckError(`${where} has no ${key}`);
  return get(value, key, where);
}

/**
 * JSON.parse, except every object is a Map in file order, so entries are checked and reported
 * in the order written (a plain object lists integer-like keys such as "7" first), and every
 * number is replaced by number(value, its source text).
 */
export function parseInOrder(
  text: string,
  number: (value: number, source: string) => unknown,
): unknown {
  JSON.parse(text); // valid JSON, so the scan below meets each string at its opening quote
  // Mark every key so that none is integer-like; the Map drops the mark.
  const marked = text.replace(/"(?:[^"\\]|\\.)*"([ \t\n\r]*:)?/gs, (token, colon) =>
    colon === undefined ? token : `"#${token.slice(1)}`,
  );
  return JSON.parse(marked, (_key, value, context?: { source?: string }) => {
    if (typeof value === "number") return number(value, context!.source!);
    if (typeof value !== "object" || value === null || Array.isArray(value)) return value;
    return new Map(Object.entries(value).map(([key, item]) => [key.slice(1), item]));
  });
}
