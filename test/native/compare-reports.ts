/**
 * Checks that a fresh native run reproduces the committed reports, so the case list, results,
 * frame outcomes and per-frame gas that the READMEs quote are what CI measured.
 *
 *   node test/native/compare-reports.ts COMMITTED_DIR FRESH_DIR
 *
 * Each directory holds native-report.json and policy-report.json. Groth16 proving is
 * randomized, so a fresh run without the local proof cache signs other proof bytes. Only what
 * follows from those bytes may differ: a transaction's hash, the policy fixtures' hashes, and its
 * total gas and fee, which move by the calldata price of the bytes that changed between zero and
 * nonzero (12 gas each under EIP-2028, at most the proof's 288 bytes). Everything else must match
 * exactly, and every fee must be the total gas times the effective gas price.
 */
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { parseArgs, runCli } from "../../src/cli/args.ts";
import { CheckError } from "../../src/errors.ts";

const PROOF_BYTES = 288;
const ZERO_BYTE_DISCOUNT = 12;

type Json = unknown;
const read = (dir: string, name: string): Json =>
  JSON.parse(readFileSync(join(dir, name), "utf8")) as Json;
const isObject = (value: Json): value is Record<string, Json> =>
  typeof value === "object" && value !== null && !Array.isArray(value);

/** Every path at which `a` and `b` differ, as "a.b[3].c". */
function differences(a: Json, b: Json, path = ""): string[] {
  if (Array.isArray(a) && Array.isArray(b)) {
    if (a.length !== b.length) return [`${path}: ${a.length} entries, now ${b.length}`];
    return a.flatMap((x, i) => differences(x, b[i], `${path}[${i}]`));
  }
  if (isObject(a) && isObject(b)) {
    const keys = [...new Set([...Object.keys(a), ...Object.keys(b)])];
    return keys.flatMap((k) => differences(a[k], b[k], path ? `${path}.${k}` : k));
  }
  return a === b ? [] : [`${path}: ${JSON.stringify(a)}, now ${JSON.stringify(b)}`];
}

/** A step's total gas and fee, which the fee rule ties together. */
function costs(step: Record<string, Json>, where: string) {
  const execution = step.execution;
  const fee = step.paid_fee;
  if (!isObject(execution) || !isObject(fee)) return null;
  const gas = BigInt(execution.gas_spent as number);
  const paid = BigInt(fee.amount as string);
  const price = BigInt(step.effective_gas_price as string);
  if (paid !== gas * price) throw new CheckError(`${where}: fee ${paid} is not ${gas} x ${price}`);
  return gas;
}

export function compareNative(committed: Json, fresh: Json): string[] {
  const problems: string[] = [];
  const cases = (report: Json) =>
    isObject(report) && Array.isArray(report.cases) ? report.cases : [];
  const [before, after] = [cases(committed), cases(fresh)];
  // Compare with the proof-dependent fields of re-proved transactions taken out.
  const strip = (report: Json, other: Json): Json => {
    const copy = structuredClone(report) as Record<string, Json>;
    const theirs = cases(other);
    cases(copy).forEach((c, i) => {
      if (!isObject(c) || !Array.isArray(c.steps)) return;
      c.steps.forEach((step, j) => {
        const twin = (theirs[i] as { steps?: Json[] } | undefined)?.steps?.[j];
        if (!isObject(step) || !isObject(twin) || step.raw_hash === twin.raw_hash) return;
        delete step.raw_hash;
        delete step.paid_fee;
        if (isObject(step.execution)) delete step.execution.gas_spent;
      });
    });
    return copy;
  };
  problems.push(...differences(strip(committed, fresh), strip(fresh, committed)));
  before.forEach((c, i) => {
    const name = isObject(c) ? String(c.name) : `case ${i}`;
    const steps = isObject(c) && Array.isArray(c.steps) ? c.steps : [];
    const twins = (after[i] as { steps?: Json[] } | undefined)?.steps ?? [];
    steps.forEach((step, j) => {
      const twin = twins[j];
      if (!isObject(step) || !isObject(twin)) return;
      const where = `${name} step ${j}`;
      const [a, b] = [costs(step, `${where} (committed)`), costs(twin, `${where} (fresh)`)];
      if (a === null || b === null || step.raw_hash === twin.raw_hash) return;
      const moved = b > a ? b - a : a - b;
      const bound = BigInt(PROOF_BYTES * ZERO_BYTE_DISCOUNT);
      if (moved % BigInt(ZERO_BYTE_DISCOUNT) !== 0n || moved > bound) {
        problems.push(`${where}: gas ${a}, now ${b}, more than re-proving can change`);
      }
    });
  });
  return problems;
}

export function comparePolicy(committed: Json, fresh: Json): string[] {
  // The two policy fixtures carry proofs, so their hashes change with every proving run.
  const strip = (report: Json): Json => {
    const copy = structuredClone(report) as Record<string, Json>;
    if (isObject(copy.fixture_keccak256)) {
      delete copy.fixture_keccak256["policy-first.hex"];
      delete copy.fixture_keccak256["policy-second.hex"];
    }
    return copy;
  };
  return differences(strip(committed), strip(fresh));
}

const SPEC = {
  prog: "compare-reports.ts",
  description: "Check a fresh native run against the committed reports.",
  positionals: [
    { name: "committed", help: "directory holding the committed reports" },
    { name: "fresh", help: "directory holding the fresh run's reports" },
  ],
  options: {},
} as const;

if (import.meta.main) {
  await runCli(() => {
    const { positionals } = parseArgs(SPEC, process.argv.slice(2));
    const problems = [
      ...compareNative(
        read(positionals.committed, "native-report.json"),
        read(positionals.fresh, "native-report.json"),
      ),
      ...comparePolicy(
        read(positionals.committed, "policy-report.json"),
        read(positionals.fresh, "policy-report.json"),
      ),
    ];
    if (problems.length > 0) {
      throw new CheckError(
        `the fresh native run differs from the committed reports:\n  ${problems.join("\n  ")}`,
      );
    }
    process.stdout.write("the fresh native run reproduces the committed reports\n");
  });
}
