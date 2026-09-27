#!/usr/bin/env node
// Decode with the lockfile-pinned r1csfile, and independently ask snarkjs to
// check the complete witness. The Python driver separately evaluates all LCs.
const fs = require('node:fs');
const path = require('node:path');
const {createRequire} = require('node:module');
const assert = require('node:assert/strict');

async function main() {
  const [modules, r1cs, witness, decoded] = process.argv.slice(2);
  assert(decoded, 'Usage: circuit_mutations.cjs NODE_MODULES R1CS WTNS DECODED_JSON');
  const load = createRequire(path.join(path.resolve(modules), '../package.json'));
  for (const [pkg, version] of [['r1csfile', '0.0.48'], ['snarkjs', '0.7.5'], ['ffjavascript', '0.2.63']]) {
    assert.equal(JSON.parse(fs.readFileSync(path.join(modules, pkg, 'package.json'))).version, version);
  }
  const {readR1cs} = load('r1csfile');
  const {F1Field} = load('ffjavascript');
  const snarkjs = load('snarkjs');
  const prime = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
  const system = await readR1cs(r1cs, {loadConstraints: true, loadMap: true, F: new F1Field(prime)});
  assert.equal(system.prime.toString(), prime.toString());
  assert.equal(system.constraints.length, system.nConstraints);
  const constraints = system.constraints.map(c => c.map(side => Object.keys(side)
    .sort((a, b) => Number(a) - Number(b)).map(wire => [Number(wire), side[wire].toString()])));
  const values = (await snarkjs.wtns.exportJson(witness)).map(v => v.toString());
  assert.equal(values.length, system.nVars);
  const checked = await snarkjs.wtns.check(r1cs, witness, console);
  assert.equal(checked, true, 'snarkjs rejected the witness');
  fs.writeFileSync(decoded, JSON.stringify({
    prime: prime.toString(), wires: system.nVars, public_outputs: system.nOutputs,
    public_inputs: system.nPubInputs, private_inputs: system.nPrvInputs,
    labels: system.nLabels, constraint_count: system.nConstraints,
    constraints, witness: values, snarkjs_check: checked,
  }));
  console.log(JSON.stringify({snarkjs_check: checked, constraints: system.nConstraints, wires: system.nVars}));
}
main().then(() => process.exit(0)).catch(error => { console.error(error); process.exit(1); });
