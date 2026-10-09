/**
 * Checks that a fresh native run reproduces the committed reports exactly, so the case list,
 * results, transaction hashes, fees and per-frame gas that the READMEs quote are what CI
 * measured.
 *
 *   node test/native/compare-reports.ts COMMITTED_DIR FRESH_DIR
 *
 * Each directory holds native-report.json and policy-report.json. Groth16 proving is
 * randomized, so the fixtures reproduce byte for byte only from the committed proofs; CI
 * generates them with run.ts --cache-only, and no difference is tolerated.
 */
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { parseArgs, runCli } from "../../src/cli/args.ts";
import { CheckError } from "../../src/errors.ts";
import { isObject } from "../../src/json.ts";

type Json = unknown;
const read = (dir: string, name: string): Json => JSON.parse(readFileSync(join(dir, name), "utf8"));

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

const SPEC = {
  prog: "compare-reports.ts",
  description: "Check a fresh native run against the committed reports.",
  positionals: [
    { name: "committed", help: "directory holding the committed reports" },
    { name: "fresh", help: "directory holding the fresh run's reports" },
  ],
} as const;

if (import.meta.main) {
  await runCli(() => {
    const { positionals } = parseArgs(SPEC, process.argv.slice(2));
    const problems = ["native-report.json", "policy-report.json"].flatMap((name) =>
      differences(read(positionals.committed, name), read(positionals.fresh, name)),
    );
    if (problems.length > 0) {
      throw new CheckError(
        `the fresh native run differs from the committed reports:\n  ${problems.join("\n  ")}`,
      );
    }
    process.stdout.write("the fresh native run reproduces the committed reports\n");
  });
}
