/**
 * Generates the shared-sender nonce-race fixture (src/nonce-race.ts) with real Groth16 proofs.
 *
 *   node src/cli/nonce-race.ts --pool-address=0x... [--chain-id=N] [--epoch=N]
 *                              [--note-wei=N] [--random] [--rpc=URL] [--output=PATH]
 *
 * --rpc seeds the tree from the live pool at --pool-address. The fixed seed is public, so it
 * is refused off the test chain and with --rpc: pass --random there. The fixture holds the
 * only openings of its notes, so it goes under the ignored artifacts/ by default.
 */
import { TEST_CHAIN_ID } from "../fixtures.ts";
import { generateNonceRace } from "../nonce-race.ts";
import * as prover from "../prover.ts";
import { parseArgs, runCli } from "./args.ts";

// Every flag must be one this script knows, so a mistyped flag stops the run instead of being
// dropped.
const SPEC = {
  prog: "nonce-race.ts",
  description: "Generate the shared-sender nonce-race fixture.",
  options: {
    "--random": {
      kind: "flag",
      help: "fresh seeds and witnesses (required off the test chain or with --rpc)",
    },
    "--chain-id": { kind: "int" },
    "--pool-address": { kind: "string" },
    "--epoch": { kind: "int" },
    "--note-wei": { kind: "int" },
    "--rpc": { kind: "string", help: "seed the tree from this node's pool at --pool-address" },
    "--output": { kind: "string" },
  },
} as const;

/** The command line `argv` (without node and the script). */
async function main(argv: readonly string[]): Promise<void> {
  const { options } = parseArgs(SPEC, argv);
  try {
    await generateNonceRace(
      {
        random: options["--random"],
        chainId: options["--chain-id"] ?? TEST_CHAIN_ID,
        poolAddress: options["--pool-address"],
        epoch: options["--epoch"] ?? 0n,
        noteWei: options["--note-wei"] ?? 10n ** 18n,
        rpc: options["--rpc"],
        output: options["--output"],
      },
      { prover, log: (line) => process.stdout.write(line + "\n") },
    );
  } finally {
    await prover.terminate();
  }
}

// Redacted like smoke: a key pasted as --output would come back in a refusal naming that path.
// A tree mismatch's two roots are redacted with it.
if (import.meta.main) await runCli(() => main(process.argv.slice(2)), { redactErrors: true });
