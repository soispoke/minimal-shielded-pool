/**
 * Groth16 proofs of the spend circuit through snarkjs 0.7.5 as a library: its fullprove, verify
 * and soliditycalldata steps, run in memory rather than as `npx snarkjs` commands.
 * Proving draws its blinding from the operating system, so proofs are never reproducible;
 * their public signals are.
 *
 * snarkjs keeps a worker-threaded bn128 curve alive after its first use, so a process that
 * proves or verifies calls terminate() once at the end in order to exit.
 */
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

// @ts-expect-error snarkjs 0.7.5 ships no type declarations; SnarkJs below types what is used.
import * as untyped from "snarkjs";

import { parseHex } from "./bytes.ts";
import { GeneratorError } from "./errors.ts";
import { P } from "./protocol.ts";
import type { Witness } from "./wallet.ts";

interface SnarkJs {
  curves: { getCurveFromName(name: "bn128"): Promise<unknown> };
  groth16: {
    fullProve(
      input: Witness,
      wasm: string,
      zkey: string,
    ): Promise<{ proof: object; publicSignals: string[] }>;
    verify(vkey: unknown, publics: readonly bigint[], proof: object): Promise<boolean>;
    exportSolidityCallData(proof: object, publics: string[]): Promise<string>;
  };
  wtns: { calculate(input: Witness, wasm: string, output: { type: "mem" }): Promise<void> };
}

const snarkjs: SnarkJs = untyped;

const artifact = (name: string) =>
  fileURLToPath(new URL(`../core/artifacts/${name}`, import.meta.url));
export const WASM = artifact("spend_js/spend.wasm");
export const ZKEY = artifact("spend_final.zkey");
const VKEY = artifact("spend_vkey.json");

/** The BN254 base field modulus: proof coordinates live in [0, Q). */
const Q = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47n;

/** The circuit's public signals, in its order: [beta, gamma, alpha]. */
export type Publics = [beta: bigint, gamma: bigint, alpha: bigint];

/**
 * A proof as the verifier's calldata takes it and fixtures store it: each word "0x" and 64
 * lowercase hex digits. Each pB coordinate's two halves are swapped from snarkjs's order,
 * because the EIP-197 pairing precompile reads an Fp2 element imaginary part first.
 */
export interface ProofWords {
  pA: [string, string];
  pB: [[string, string], [string, string]];
  pC: [string, string];
}

/**
 * Proves a witness and checks the proof against the committed verification key before
 * returning it, so a zkey from another setup never reaches a fixture. `tag` names the proof
 * in errors.
 */
export async function prove(
  witness: Witness,
  tag: string,
): Promise<{ publics: Publics; proof: ProofWords }> {
  await sharedCurve();
  const { proof, publicSignals } = await snarkjs.groth16
    .fullProve(witness, WASM, ZKEY)
    .catch((error: Error) => {
      throw new GeneratorError(`snarkjs could not prove ${tag}: ${error.message}`);
    });
  const publics = publicSignals.map(BigInt) as Publics;
  if (!(await verifySnark(publics, proof))) {
    throw new GeneratorError(`the proof of ${tag} does not verify against ${VKEY}`);
  }
  const calldata = await snarkjs.groth16.exportSolidityCallData(proof, publicSignals);
  const [pA, pB, pC] = JSON.parse(`[${calldata}]`);
  return { publics, proof: { pA, pB, pC } };
}

/**
 * Whether a proof in calldata form verifies for these public signals against VKEY, under the
 * deployed Groth16Verifier's input checks: three public signals in [0, r) and every proof
 * word in [0, q). snarkjs reduces coordinates modulo q and writes a negative signal -x as x
 * when x has 64 hex digits, so without these checks it would accept inputs the contract
 * refuses. A word that is not 0x-prefixed hex throws an InputError, as the pool's fixture
 * reader refuses it.
 */
export async function verify(
  publics: readonly bigint[],
  { pA, pB, pC }: ProofWords,
): Promise<boolean> {
  const words = [...pA, ...pB.flat(), ...pC].map((word) => parseHex(word, "a proof word"));
  if (publics.length !== 3 || !publics.every((x) => 0n <= x && x < P)) return false;
  if (!words.every((w) => w < Q)) return false;
  return verifySnark(publics, {
    pi_a: [pA[0], pA[1], "1"],
    pi_b: [
      [pB[0][1], pB[0][0]],
      [pB[1][1], pB[1][0]],
      ["1", "0"],
    ],
    pi_c: [pC[0], pC[1], "1"],
    protocol: "groth16",
    curve: "bn128",
  });
}

let vkey: unknown;

async function verifySnark(publics: readonly bigint[], proof: object): Promise<boolean> {
  vkey ??= JSON.parse(readFileSync(VKEY, "utf8"));
  await sharedCurve();
  return snarkjs.groth16.verify(vkey, publics, proof);
}

// ffjavascript publishes the curve in globalThis.curve_bn128 only once it is built, so two
// first calls in flight would each build one and terminate() would stop only the last.
// Every snarkjs call here that needs the curve first awaits this one build.
let curve: Promise<unknown> | undefined;
const sharedCurve = () => (curve ??= snarkjs.curves.getCurveFromName("bn128"));

// circom_runtime prints each failed assertion to stderr before throwing it. In
// assertUnprovable the failure is the expected outcome and its text is in the error, so
// console.error is silenced while any call runs; the count restores it once if calls overlap.
let quietCalls = 0;
let printError = console.error;

/**
 * Checks that the circuit itself refuses a witness built to break one of its rules. Only a
 * failed in-circuit assertion counts as the refusal: any other error, such as a missing
 * signal or artifact, is rethrown, so a broken run can never pass as a sound circuit.
 */
export async function assertUnprovable(witness: Witness, tag: string): Promise<void> {
  if (quietCalls++ === 0) {
    printError = console.error;
    console.error = () => {};
  }
  try {
    await snarkjs.wtns.calculate(witness, WASM, { type: "mem" });
  } catch (error) {
    if (error instanceof Error && error.message.includes("Assert Failed")) return;
    throw error;
  } finally {
    if (--quietCalls === 0) console.error = printError;
  }
  throw new GeneratorError(`UNSOUND: circuit accepted ${tag}`);
}

/**
 * Stops the curve's worker threads. snarkjs shares one curve through globalThis.curve_bn128,
 * so this also stops one that a direct snarkjs call built. A later call builds a new curve.
 */
export async function terminate(): Promise<void> {
  curve = undefined;
  const shared = globalThis as { curve_bn128?: { terminate(): Promise<void> } | null };
  await shared.curve_bn128?.terminate();
}
