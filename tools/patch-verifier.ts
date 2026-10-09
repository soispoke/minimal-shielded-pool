/**
 * Hardens snarkjs's generated verifier for the restricted VERIFY prefix.
 *
 *   node tools/patch-verifier.ts
 *
 * The Hegotá validation observer bans the GAS opcode. snarkjs emits
 * `staticcall(sub(gas(), 2000), ...)` for ECADD, ECMUL, and pairing. Replace all three with a
 * fixed request; EIP-150 still caps it to 63/64 of remaining gas. It also rejects
 * noncanonical BN254 point-coordinate aliases and infinity encodings before the pairing
 * precompile. Fail closed if a future snarkjs output changes shape.
 */
import { writeFileSync } from "node:fs";

import { runCli } from "../src/cli/args.ts";
import { CheckError } from "../src/errors.ts";
import { readText } from "./check.ts";

export const VERIFIER = new URL("../core/contracts/src/Groth16Verifier.sol", import.meta.url);
const NEEDLE = "staticcall(sub(gas(), 2000),";
const REPLACEMENT = "staticcall(500000,";
const MARKER = "// CANONICAL_PROOF_COORDINATES";
// The memory prologue snarkjs emits; the guard goes right before it.
const PROLOGUE = `            let pMem := mload(0x40)
            mstore(0x40, add(pMem, pLastMem))
`;
const GUARD = `            // CANONICAL_PROOF_COORDINATES: the pairing precompile accepts
            // field elements, but a proof has one canonical uint256 encoding.
            // Reject aliases such as pA.y + q and reject infinity points.
            function checkCoordinate(v) {
                if iszero(lt(v, q)) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }
            let ax := calldataload(_pA)
            let ay := calldataload(add(_pA, 32))
            let bx0 := calldataload(_pB)
            let bx1 := calldataload(add(_pB, 32))
            let by0 := calldataload(add(_pB, 64))
            let by1 := calldataload(add(_pB, 96))
            let cx := calldataload(_pC)
            let cy := calldataload(add(_pC, 32))
            checkCoordinate(ax)
            checkCoordinate(ay)
            checkCoordinate(bx0)
            checkCoordinate(bx1)
            checkCoordinate(by0)
            checkCoordinate(by1)
            checkCoordinate(cx)
            checkCoordinate(cy)
            if iszero(or(ax, ay)) { mstore(0, 0) return(0, 0x20) }
            if iszero(or(or(bx0, bx1), or(by0, by1))) { mstore(0, 0) return(0, 0x20) }
            if iszero(or(cx, cy)) { mstore(0, 0) return(0, 0x20) }

`;

const count = (text: string, part: string) => text.split(part).length - 1;

/**
 * The hardened verifier source. Applying it to its own output changes nothing, so a rerun is
 * safe. log receives each step as it is taken.
 */
export function patchVerifier(source: string, log: (line: string) => void): string {
  const calls = count(source, NEEDLE);
  if (calls === 3) {
    source = source.replaceAll(NEEDLE, REPLACEMENT);
    log("patched 3 verifier precompile calls to fixed gas");
  } else if (calls === 0 && count(source, REPLACEMENT) === 3) {
    log("verifier already uses 3 fixed-gas precompile calls");
  } else {
    throw new CheckError(
      `expected 3 snarkjs GAS calls, found ${calls}; inspect generated verifier`,
    );
  }
  if (!source.includes(MARKER)) {
    if (count(source, PROLOGUE) !== 1) {
      throw new CheckError("generated verifier memory prologue changed; inspect before hardening");
    }
    source = source.replace(PROLOGUE, GUARD + PROLOGUE);
    log("added canonical BN254 coordinate and infinity checks");
  } else {
    log("verifier already has canonical proof-coordinate checks");
  }
  return source;
}

if (import.meta.main) {
  await runCli(() => {
    // Strict UTF-8 keeps any byte order mark, so the file is rewritten byte for byte.
    const source = readText(VERIFIER);
    // Written once, at the end, so a refusal leaves the file untouched.
    writeFileSync(VERIFIER, patchVerifier(source, console.log));
  });
}
