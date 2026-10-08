/**
 * Builds and submits the pool's frame transactions; src/pool.ts's poolCommand does the work.
 *
 *   node src/cli/pool.ts <rpc> <config> <fixture> shield|publish|transfer|withdraw [--dry-run]
 *
 * shield and publish read the funded key from standard input, since any local user can read a
 * command line; a spend is signed by the authorizer its proof selects. Flags and the config are
 * checked before any RPC.
 */
import { InputError } from "../errors.ts";
import { parsePrivateKeyLine } from "../frametx.ts";
import * as pool from "../pool.ts";
import { parseArgs, runCli } from "./args.ts";
import { readSecretLine } from "./secret.ts";

const TAIL = "custom DEFAULT tail (all four together)";
const SPEC = {
  prog: "pool.ts",
  description: "Build and submit the minimal pool's frame transactions.",
  positionals: [
    { name: "rpc" },
    { name: "config", help: "deployment config, such as core/deploy_config.json" },
    { name: "fixture", help: "fixture from src/cli/smoke.ts or src/cli/nonce-race.ts" },
    { name: "op", choices: ["shield", "publish", "transfer", "withdraw"] },
  ],
  options: {
    "--dry-run": { kind: "flag", help: "simulate without submitting" },
    "--epoch": { kind: "int", help: "epoch to publish" },
    "--note": { kind: "int", help: "index into the fixture's shields" },
    "--spend-key": { kind: "string", help: "fixture key of the spend entry (e.g. transfer_c)" },
    "--root-slot": { kind: "int", help: "consensus slot that published the root" },
    "--no-tail": { kind: "flag", help: "send a spend without a fourth frame" },
    "--allow-failed-claim": {
      kind: "flag",
      help: "send a withdrawal whose default claim is expected to revert",
    },
    "--action-target": { kind: "append", help: TAIL },
    "--action-call": { kind: "append", help: TAIL },
    "--action-gas": { kind: "append", help: TAIL },
    "--action-state-gas": { kind: "append", help: TAIL },
    "--max-fee-per-gas": {
      kind: "int",
      help: "a spend's fee cap in wei (default: twice the base fee plus the tip)",
    },
    "--max-priority-fee-per-gas": { kind: "int", help: "a spend's tip in wei (default: 1 gwei)" },
  },
  // The CLI once took the funded key here. Refused before parsing, whose errors repeat values.
  refuseBeforeParsing: {
    index: 4,
    message:
      "the CLI no longer takes a key argument, which other local users could read: shield " +
      "and publish read the funded key from standard input",
  },
} as const;

/** The shield or publish payer's key: a hidden prompt on a terminal, one line from a pipe. */
async function fundedKey(): Promise<Uint8Array> {
  const line = await readSecretLine("funded private key: ");
  try {
    // trim() would drop a byte order mark as whitespace; a key line holding one is refused.
    if (!line.includes("\uFEFF")) return parsePrivateKeyLine(line, "the funded key");
  } catch (error) {
    if (!(error instanceof InputError)) throw error;
  }
  throw new InputError("standard input did not hold a private key");
}

/** What in-process tests replace: the node, the deployed-code check, the sender, the key. */
export interface Deps {
  readonly node?: pool.PoolNode;
  readonly checkDeployedProfile?: typeof pool.checkDeployedProfile;
  readonly buildAndSend?: typeof pool.buildAndSend;
  readonly readFundedKey?: () => Promise<Uint8Array>;
}

/** The command line `argv` (without node and the script), run against the real node by default. */
export async function main(argv: readonly string[], deps: Deps = {}): Promise<void> {
  const { positionals, options } = parseArgs(SPEC, argv);
  // Flag-value pairs as the parser read them, so --flag=value forms obey the same tail rules.
  const given: Record<string, unknown> = options;
  const pairs = pool.ACTION_OPTION_FLAGS.flatMap((flag) =>
    (given[flag] as string[]).flatMap((value) => [flag, value]),
  );
  const command = {
    ...positionals,
    dryRun: options["--dry-run"],
    epoch: options["--epoch"],
    note: options["--note"],
    spendKey: options["--spend-key"],
    rootSlot: options["--root-slot"],
    maxFee: options["--max-fee-per-gas"],
    maxPriorityFee: options["--max-priority-fee-per-gas"],
    omitTail: options["--no-tail"],
    allowFailedClaim: options["--allow-failed-claim"],
    action: pool.actionOptions(pairs),
  };
  const log = (line: string) => process.stdout.write(line + "\n");
  await pool.poolCommand(command, { ...deps, log, readFundedKey: deps.readFundedKey ?? fundedKey });
}

if (import.meta.main) await runCli(() => main(process.argv.slice(2)), { redactErrors: true });
