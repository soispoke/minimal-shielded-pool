/**
 * CI's native job builds every fixture from the proofs committed in test/native/fixtures/ and
 * never proves, so the fixture generator must check each cached proof against the committed
 * verification key: a case that expects a rejection would otherwise pass on an invalid proof.
 * No ethrex runs. Runtime: about 1 s.
 */
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { after, test } from "node:test";

import { GeneratorError } from "../src/errors.ts";
import { isObject, parse, stringify } from "../src/json.ts";
import { terminate, verify, type ProofWords } from "../src/prover.ts";
import { readCachedProof } from "./native/scripts/generate-fixtures.ts";

const FIXTURES = resolve(import.meta.dirname, "native", "fixtures");
const SUFFIX = "-proof.json";
const NAMES = readdirSync(FIXTURES)
  .filter((file) => file.endsWith(SUFFIX))
  .map((file) => file.slice(0, -SUFFIX.length));
type Cached = { witness_hash: string; publics: bigint[]; proof: ProofWords };
function cached(name: string): Cached {
  const record = parse(readFileSync(join(FIXTURES, name + SUFFIX), "utf8"));
  assert.ok(isObject(record), `${name}${SUFFIX} is not a JSON object`);
  return record as Cached;
}
const tmp = mkdtempSync(join(tmpdir(), "msp-native-proofs-"));
after(() => rmSync(tmp, { recursive: true, force: true }));
after(terminate);

test("every committed native proof verifies, and the generator accepts it", async () => {
  assert.ok(NAMES.length > 0, `no committed proofs in ${FIXTURES}`);
  for (const name of NAMES) {
    const record = cached(name);
    assert.ok(await verify(record.publics, record.proof), `${name} does not verify`);
    const hit = await readCachedProof(FIXTURES, name, record.witness_hash);
    assert.deepEqual(hit, { publics: record.publics, proof: record.proof }, name);
  }
});

// alias-nf1 feeds only a step the harness expects to be rejected, so an invalid proof there
// would leave every native case passing.
const tampered: [name: string, change: (record: Cached) => void][] = [
  ["another spend's proof", (record) => (record.proof = cached("rollover").proof)],
  ["a changed public signal", (record) => (record.publics[2] += 1n)],
];

for (const [name, change] of tampered) {
  test(`the generator refuses a cached proof that does not verify: ${name}`, async () => {
    const record = cached("alias-nf1");
    change(record);
    writeFileSync(join(tmp, "alias-nf1" + SUFFIX), stringify(record, 2) + "\n");
    await assert.rejects(
      readCachedProof(tmp, "alias-nf1", record.witness_hash),
      (e: unknown) =>
        e instanceof GeneratorError &&
        e.message === "the cached proof of alias-nf1 does not verify",
    );
  });
}
