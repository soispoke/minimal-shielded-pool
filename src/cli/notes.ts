/**
 * Note delivery from the command line; src/notes.ts does the work.
 *
 *   node src/cli/notes.ts address [--account N] [--seed-file PATH]
 *   node src/cli/notes.ts scan --config CONFIG --state PATH [--rpc URL] [--chunk N] [--account N]
 *                              [--seed-file PATH]
 *   node src/cli/notes.ts direct-secret --config CONFIG --state PATH [--number N] [--account N]
 *                                       [--seed-file PATH]
 *
 * direct-secret issues the next number and records it in the state; --number shows one already
 * issued again. Without --seed-file the seed is typed at a hidden prompt or read from standard
 * input, never taken from the command line, which other local users can read.
 */
import * as notes from "../notes.ts";
import { parseArgs, runCli } from "./args.ts";
import { readSecretLine } from "./secret.ts";

const SPEC = {
  prog: "notes.ts",
  description: "Note delivery: a secret per sender and recipient, and 48-byte notes on chain.",
  positionals: [{ name: "command", choices: ["address", "direct-secret", "scan"] }],
  options: {
    "--seed-file": { kind: "string", help: "owner-only file holding the wallet seed in hex" },
    "--account": { kind: "decimal", help: "address number derived from the seed" },
    "--number": { kind: "decimal", help: "direct-secret: show a number already handed out again" },
    "--config": { kind: "string", help: "scan, direct-secret: config naming the chain and pool" },
    "--state": { kind: "string", help: "scan, direct-secret: wallet state, created owner-only" },
    "--rpc": { kind: "string", help: "scan: RPC URL (default: the config's)" },
    "--chunk": { kind: "decimal", help: "scan: blocks per eth_getLogs call" },
  },
} as const;

/** What in-process tests replace: the prompt or pipe the seed is read from. */
export interface Deps {
  readonly readSecretLine?: (prompt: string) => Promise<string>;
}

/** The command line `argv` (without node and the script). */
export async function main(argv: readonly string[], deps: Deps = {}): Promise<void> {
  const { positionals, options } = parseArgs(SPEC, argv);
  const readLine = deps.readSecretLine ?? readSecretLine;
  // The seed is read and checked first, so a bad seed is reported before any other option.
  const seed = await notes.readSeed(options["--seed-file"], () => readLine("wallet seed (hex): "));
  const keys = new notes.WalletKeys(seed, options["--account"] ?? 0n);
  const chunk = options["--chunk"];
  const command = {
    keys,
    config: options["--config"],
    state: options["--state"],
    rpc: options["--rpc"],
    // A chunk of 2^53 blocks already covers any range in one call.
    chunk: chunk === undefined ? undefined : Math.min(Number(chunk), Number.MAX_SAFE_INTEGER),
    number: options["--number"],
  };
  process.stdout.write(
    positionals.command === "address"
      ? notes.addressCommand(keys)
      : positionals.command === "scan"
        ? await notes.scanCommand(command)
        : await notes.directSecretCommand(command),
  );
}

// Refusals and file errors begin with "notes: ", and are redacted like the pool CLI's: a seed
// pasted as a path, or a secret in a malformed state file, would come back in a refusal. No
// notes refusal needs a 64-digit hash.
if (import.meta.main) {
  await runCli(() => main(process.argv.slice(2)), { redactErrors: true, prefix: "notes: " });
}
