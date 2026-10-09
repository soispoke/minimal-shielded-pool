/**
 * Generates the smoke fixture (src/smoke.ts) with real Groth16 proofs.
 *
 *   node src/cli/smoke.ts [--random] [--chain-id=N] [--pool-address=0x...]
 *                         [--recipient=0x...] [--output=PATH]
 *
 * With no options it rewrites the committed test/fixtures/smoke_fixture.json from the fixed
 * seed. Any other chain or pool needs --random and a --recipient, and its fixture goes under
 * the ignored artifacts/ unless --output names another path.
 */
import { existsSync } from "node:fs";

import { GeneratorError } from "../errors.ts";
import { TEST_CHAIN_ID, TEST_POOL } from "../fixtures.ts";
import * as prover from "../prover.ts";
import { generateSmoke } from "../smoke.ts";
import { parseArgs, runCli } from "./args.ts";

// Every flag must be one this script knows, so a mistyped --chain-id stops the run instead of
// falling back to the test chain's fixture.
const SPEC = {
  prog: "smoke.ts",
  description: "Generate the smoke fixture with real Groth16 proofs.",
  options: {
    "--random": {
      kind: "flag",
      help: "fresh seeds and witnesses (required off the test chain and pool)",
    },
    "--chain-id": { kind: "int" },
    "--pool-address": { kind: "string" },
    "--recipient": { kind: "string" },
    "--output": { kind: "string" },
  },
} as const;

/** The command line `argv` (without node and the script). */
async function main(argv: readonly string[]): Promise<void> {
  const { options } = parseArgs(SPEC, argv);
  if (!existsSync(prover.ZKEY)) {
    throw new GeneratorError("run the setup first: (cd tools && ./setup.sh)");
  }
  try {
    await generateSmoke(
      {
        random: options["--random"],
        chainId: options["--chain-id"] ?? TEST_CHAIN_ID,
        poolAddress: options["--pool-address"] ?? TEST_POOL,
        recipient: options["--recipient"],
        output: options["--output"],
      },
      { prover, log: (line) => process.stdout.write(line + "\n") },
    );
  } finally {
    await prover.terminate();
  }
}

// Redacted: a key pasted as --recipient or --output would come back in a refusal naming it.
if (import.meta.main) await runCli(() => main(process.argv.slice(2)), { redactErrors: true });
