#!/usr/bin/env node
// Independent decoding with the lockfile-pinned r1csfile dependency. This is a
// parser cross-check, not a formal verification of the decoder or the circuit.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const { createRequire } = require('node:module');
const assert = require('node:assert/strict');

async function main() {
  const [modules, artifact, manifestPath] = process.argv.slice(2);
  if (!manifestPath) throw new Error('Usage: crosscheck_r1cs.cjs NODE_MODULES R1CS MANIFEST');
  const load = createRequire(path.join(path.resolve(modules), '../package.json'));
  const { readR1cs } = load('r1csfile');
  const { F1Field } = load('ffjavascript');
  assert.equal(JSON.parse(fs.readFileSync(path.join(modules, 'r1csfile/package.json'))).version, '0.0.48');
  const manifest = JSON.parse(fs.readFileSync(manifestPath));
  assert.equal(crypto.createHash('sha256').update(fs.readFileSync(artifact)).digest('hex'), manifest.sha256);
  const system = await readR1cs(artifact, {
    loadConstraints: true, loadMap: true, F: new F1Field(BigInt(manifest.field_order)),
  });
  assert.deepEqual([system.nVars, system.nOutputs, system.nPubInputs, system.nPrvInputs,
                   system.nLabels, system.nConstraints],
                  ['wires', 'public_outputs', 'public_inputs', 'private_inputs', 'labels', 'constraints']
                    .map(key => manifest.header[key]));
  const digest = crypto.createHash('sha256');
  let terms = 0;
  for (const constraint of system.constraints) {
    digest.update(constraint.map(side => {
      const keys = Object.keys(side).sort((a, b) => Number(a) - Number(b));
      terms += keys.length;
      return keys.map(wire => `${wire}:${side[wire].toString()}`).join(',');
    }).join(';') + '\n');
  }
  assert.equal(digest.digest('hex'), manifest.constraints_sha256);
  assert.equal(terms, manifest.terms);
  const map = Buffer.alloc(8 * system.map.length);
  system.map.forEach((label, wire) => map.writeBigUInt64LE(BigInt(label), 8 * wire));
  assert.equal(crypto.createHash('sha256').update(map).digest('hex'),
               manifest.sections.find(section => section.type === 3).sha256);
  console.log(`Independent r1csfile decode matches all ${system.nConstraints} constraints, ${terms} terms and ${system.nVars} labels.`);
}
main().catch(error => { console.error(error); process.exitCode = 1; });
