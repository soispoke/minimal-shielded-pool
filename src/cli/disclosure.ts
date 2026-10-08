/**
 * Disclosure receipts from the command line; src/disclosure.ts does the work.
 *
 *   node src/cli/disclosure.ts export --rpc URL --config CONFIG --fixture FIXTURE
 *                              (--only CM,... | --all) [--address-wide] --output PATH
 *   node src/cli/disclosure.ts verify --rpc URL --config CONFIG --receipt PATH
 */
import { exportCommand, verifyCommand } from "../disclosure.ts";
import { parseArgs, runCli } from "./args.ts";

const SPEC = {
  prog: "disclosure.ts",
  description:
    "Disclosure receipts: show which notes a spend consumed and created, without giving away " +
    "the spending key.",
  positionals: [{ name: "command", choices: ["export", "verify"] }],
  options: {
    "--rpc": { kind: "string", required: true },
    "--config": { kind: "string", required: true, help: "deployment config naming the pool" },
    "--fixture": { kind: "string", help: "export: the wallet fixture holding the openings" },
    "--only": {
      kind: "string",
      help: "export: comma-separated commitments of the notes to disclose",
    },
    "--all": { kind: "flag", help: "export: disclose every note the fixture opens" },
    "--address-wide": {
      kind: "flag",
      help: "export: allow nullifier keys shared by every note of an address in the epoch",
    },
    "--output": { kind: "string", help: "export: where to write the receipt" },
    "--receipt": { kind: "string", help: "verify: the receipt to check" },
  },
} as const;

/** The command line `argv` (without node and the script). */
export async function main(argv: readonly string[]): Promise<void> {
  const { positionals, options } = parseArgs(SPEC, argv);
  const [rpc, config] = [options["--rpc"], options["--config"]];
  process.stdout.write(
    positionals.command === "export"
      ? await exportCommand({
          rpc,
          config,
          fixture: options["--fixture"],
          only: options["--only"],
          all: options["--all"],
          addressWide: options["--address-wide"],
          output: options["--output"],
        })
      : await verifyCommand({ rpc, config, receipt: options["--receipt"] }),
  );
}

// Refusals keep the commitments and hashes they name; runCli still redacts file errors.
if (import.meta.main) await runCli(() => main(process.argv.slice(2)));
