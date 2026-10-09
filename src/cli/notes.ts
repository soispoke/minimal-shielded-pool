/**
 * Note delivery from the command line; src/notes.ts and src/scan.ts do the work. This module reads
 * the wallet seed, keeps the wallet's state file under a lock, and saves each direct number it
 * issues before returning its secret.
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
import { fromHex, hex32, parseConfigAddress, parseDec, toHex } from "../bytes.ts";
import { NotesError } from "../errors.ts";
import {
  FileChangedError,
  fileIdentity,
  readJson,
  readPrivate,
  withLock,
  writePrivate,
} from "../files.ts";
import { POOL_PROFILE } from "../gas.ts";
import { asObject, stringify, type JsonObject } from "../json.ts";
import { MIN_SEED_BYTES, WalletKeys } from "../notes.ts";
import { RpcChain } from "../rpc.ts";
import { Scanner, scanToFinalized } from "../scan.ts";
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
  const seed = await readSeed(options["--seed-file"], () => readLine("wallet seed (hex): "));
  const keys = new WalletKeys(seed, options["--account"] ?? 0n);
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
      ? addressCommand(keys)
      : positionals.command === "scan"
        ? await scanCommand(command)
        : await directSecretCommand(command),
  );
}

// ---- commands (main parses the arguments and prints what these return) ----

/** A wallet seed written as hex ("0x" optional), at least 32 bytes. */
export function parseSeed(text: string): Uint8Array {
  const digits = text.trim().replace(/^0x/, "");
  if (!/^([0-9a-fA-F]{2})*$/.test(digits)) throw new NotesError("a seed is hex");
  const seed = fromHex("0x" + digits, "a seed");
  if (seed.length < MIN_SEED_BYTES) {
    throw new NotesError(`a seed has at least ${MIN_SEED_BYTES} bytes`);
  }
  return seed;
}

/**
 * The wallet seed from an owner-only file or, when none is named, from the line readLine gives;
 * never from the command line, which any local user can read.
 */
export async function readSeed(seedFile: string | undefined, readLine: () => Promise<string>) {
  return parseSeed(seedFile ? readPrivate(seedFile) : await readLine());
}

/** What `notes address` prints. */
export function addressCommand(keys: WalletKeys): string {
  return keys.address().hex() + "\n";
}

export interface CommandOptions {
  keys: WalletKeys;
  config?: string; // the deployment config, naming the chain, pool, profile and RPC
  state?: string; // the wallet state file, created owner-only
  rpc?: string; // scan: the RPC URL, instead of the config's
  chunk?: number; // scan: blocks per eth_getLogs call
  number?: bigint; // direct-secret: show a number already handed out again
}

/**
 * `notes scan`: brings the state up to the finalized head (scanToFinalized), saves it, and
 * returns the unspent notes.
 */
export async function scanCommand(options: CommandOptions): Promise<string> {
  return withState("scan", options, async (config, scanner, save) => {
    const { deploymentBlock = 0 } = config;
    const deployment = parseDec(deploymentBlock, "the config's deploymentBlock");
    const url = options.rpc || config.rpc;
    if (typeof url !== "string") throw new NotesError("the config names no rpc URL; pass --rpc");
    await scanToFinalized(scanner, new RpcChain(url), deployment, options.chunk);
    save();
    const unspent = scanner.unspent();
    const balance = String(unspent.reduce((sum, note) => sum + note.value, 0n));
    const notes = unspent.map(({ cm, epoch, index, value }) => {
      return { cm: hex32(cm), epoch, index, value: String(value) };
    });
    const result = { scanned_block: scanner.scannedBlock, unspent: unspent.length, balance, notes };
    return stringify(result, 1) + "\n";
  });
}

const DIRECT_NOTE = "give this to one sender only, over a post-quantum channel; never publish it";

/**
 * `notes direct-secret`: issues the next direct number, saved before its secret is returned, or
 * shows one already issued again. Two senders with one secret would link their payments.
 */
export async function directSecretCommand(options: CommandOptions): Promise<string> {
  return withState("direct-secret", options, async (_, scanner, save) => {
    if (scanner.scannedBlock < 0n) {
      throw new NotesError("scan first, so that the wallet knows which numbers have been paid");
    }
    let number = options.number;
    if (number === undefined) {
      number = scanner.issueDirect();
      save();
    } else if (!(number >= 0n && number <= scanner.directIssued)) {
      throw new NotesError(
        "--number shows a secret already handed out; leave it out to issue the next one",
      );
    }
    // The output format is fixed: one line, with ", " and ": " separators.
    const { keys } = options;
    const secret = toHex(keys.directSecret(number));
    return `{"number": ${number}, "owner_pk": "${hex32(keys.ownerPk)}", "secret": "${secret}", "note": "${DIRECT_NOTE}"}\n`;
  });
}

/**
 * Runs body under the state file's lock, which serializes runs on one wallet, with the config,
 * the wallet's scanner (from the state file if there is one) and a save that writes it back.
 */
async function withState<T>(
  command: string,
  { keys, config: configPath, state: statePath }: CommandOptions,
  body: (config: JsonObject, scanner: Scanner, save: () => void) => Promise<T>,
): Promise<T> {
  if (!configPath || !statePath) throw new NotesError(`${command} needs --config and --state`);
  return withLock(statePath, () => {
    const config = asObject(readJson(configPath), configPath);
    if (config.profile !== POOL_PROFILE) {
      throw new NotesError(
        `the config names profile ${config.profile ?? "none"}; scan and direct-secret need a ` +
          `${POOL_PROFILE} pool, which publishes notes`,
      );
    }
    const chainId = parseDec(config.chainId, "the config's chainId");
    const pool = parseConfigAddress(config.pool, "the config's pool");
    const seen = fileIdentity(statePath);
    const scanner =
      seen === null
        ? new Scanner(keys, chainId, pool)
        : Scanner.fromJson(keys, readJson(statePath, readPrivate));
    if (scanner.chainId !== chainId || scanner.pool !== pool) {
      throw new NotesError("the state file is for another chain or pool");
    }
    // Under the lock the file cannot change unless the lock was removed while held. Saving
    // would then undo the other run's changes and could reissue a direct number, so the save
    // requires the file seen at load, or no file if there was none.
    const save = () => {
      try {
        writePrivate(statePath, stringify(scanner.toJson(), 1), seen);
      } catch (error) {
        if (!(error instanceof FileChangedError)) throw error;
        throw new NotesError(
          `${statePath} changed during this run, so another run wrote it without the lock; ` +
            "nothing was saved",
        );
      }
    };
    return body(config, scanner, save);
  });
}

// Refusals and file errors begin with "notes: ", and are redacted like the pool CLI's: a seed
// pasted as a path, or a secret in a malformed state file, would come back in a refusal. No
// notes refusal needs a 64-digit hash.
if (import.meta.main) {
  await runCli(() => main(process.argv.slice(2)), { redactErrors: true, prefix: "notes: " });
}
