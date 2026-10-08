/**
 * Compiles and parameterizes the ShieldedPoolDispatcher Yul, the pool-as-sender shell that
 * DELEGATECALLs settlement to ShieldedPoolLogic.sol.
 *
 *   node tools/dispatcher.ts --initcode 0x<impl> 0x<verifier>   print the deploy initcode
 *   node tools/dispatcher.ts --artifact   rewrite core/artifacts/shielded_pool_dispatcher_init.hex
 *
 * The deployed runtime carries two appended 32-byte immutables: the implementation
 * (ShieldedPoolLogic) address, then the Groth16 verifier address. The verifier is a dispatcher
 * immutable because frame 0 verifies the proof inline, with a direct staticcall: ethrex's
 * validation observer rejects a delegatecall to the implementation during a VERIFY frame. The
 * artifact is the bare initcode, without the addresses, which the deployment script and the
 * pool client's deployed-code check read; rerun --artifact after any change to the Yul.
 *
 * There is deliberately no --runtime mode: the optimizer appends a data segment after the
 * runtime subobject, so splitting at 0xfe is unsound. Derive the expected deployed code by
 * simulating the deployment, as run_live_dispatcher.sh does:
 *
 *   cast call --rpc-url <rpc> --create "$(node tools/dispatcher.ts --initcode <impl> <verifier>)"
 */
import { spawnSync } from "node:child_process";
import { accessSync, constants, mkdirSync, statSync, writeFileSync } from "node:fs";
import { homedir } from "node:os";
import { basename, delimiter, dirname, join, resolve } from "node:path";

import { concat, fromHex, hexFromText, toHex, word } from "../src/bytes.ts";
import { parseArgs, runCli, UsageError } from "../src/cli/args.ts";
import { CheckError, InputError } from "../src/errors.ts";

const SOLC_VERSION = "0.8.30";
const CORE = resolve(import.meta.dirname, "../core");
const SOURCE = join(CORE, "dispatcher/ShieldedPoolDispatcher.yul");
const ARTIFACT = join(CORE, "artifacts/shielded_pool_dispatcher_init.hex");

/** A command's output; a command that cannot start or exits nonzero is refused. */
function capture(command: string, args: string[], cwd?: string) {
  const result = spawnSync(command, args, { cwd, encoding: "utf8" });
  if (result.error || result.status !== 0) {
    const reason =
      result.error?.message ?? (result.stderr.trim() || `exit status ${result.status}`);
    throw new CheckError(`${command} ${args.join(" ")} failed: ${reason}`);
  }
  return result;
}

/** The first executable `name` on PATH (/bin:/usr/bin when unset) that is not a directory. */
function which(name: string): string | undefined {
  const search = process.env.PATH ?? "/bin:/usr/bin";
  for (const dir of search ? search.split(delimiter) : []) {
    const path = join(dir, name);
    try {
      accessSync(path, constants.X_OK);
      if (!statSync(path).isDirectory()) return path;
    } catch {
      // not here
    }
  }
  return undefined;
}

/**
 * The pinned compiler. The list is a fallback chain, so a candidate of the wrong version is
 * skipped: otherwise any `solc` on PATH (the one a package manager or a shim happens to expose)
 * would hide the pinned install below it, and only the pinned compiler reproduces the committed
 * initcode. An explicit SOLC of the wrong version is refused, because naming a binary by hand
 * and getting a different compiler is a mistake worth reporting. CI has solc 0.8.30 only because
 * `forge build` installs it under ~/.svm first.
 */
function solcBinary(): string {
  const svm = (root: string) => join(root, SOLC_VERSION, `solc-${SOLC_VERSION}`);
  const candidates = [
    process.env.SOLC,
    which("solc"),
    svm(join(homedir(), "Library", "Application Support", "svm")),
    svm(join(homedir(), ".svm")),
  ];
  const rejected: string[] = [];
  for (const [index, candidate] of candidates.entries()) {
    if (!candidate || !statSync(candidate, { throwIfNoEntry: false })?.isFile()) continue;
    const version = capture(candidate, ["--version"]).stdout;
    if (version.includes(`Version: ${SOLC_VERSION}`)) return candidate;
    const summary = version.trim().split("\n").at(-1);
    if (index === 0) {
      throw new CheckError(`SOLC=${candidate} is not solc ${SOLC_VERSION}: ${summary}`);
    }
    rejected.push(`${candidate} (${summary})`);
  }
  const detail = rejected.length > 0 ? `; rejected ${rejected.join(", ")}` : "";
  throw new CheckError(`solc ${SOLC_VERSION} not found${detail}; set SOLC to the pinned binary`);
}

let compiled: Uint8Array | undefined;

/** The dispatcher's bare initcode, compiled once per process. */
function compiledInitcode(): Uint8Array {
  if (compiled) return compiled;
  const args = ["--strict-assembly", "--optimize", "--optimize-runs", "200", "--bin"];
  const { stdout, stderr } = capture(solcBinary(), [...args, basename(SOURCE)], dirname(SOURCE));
  const marker = "Binary representation:\n";
  const at = stdout.indexOf(marker);
  if (at < 0) throw new CheckError(`could not parse solc output: ${stdout}\n${stderr}`);
  const hex = stdout
    .slice(at + marker.length)
    .split("\n")[0]
    .trim();
  return (compiled = fromHex(`0x${hex}`, "solc's binary output"));
}

/** The deploy initcode: the compiled dispatcher, then word(impl) and word(verifier). */
export function initcode(impl: bigint, verifier: bigint): Uint8Array {
  return concat(compiledInitcode(), word(impl), word(verifier));
}

/** A nonzero address below 2^160 in hex, with or without 0x or 0X, as Python's int() read it. */
function address(value: string): bigint {
  const parsed = hexFromText(value.replace(/^(0[xX])?/, "0x")) ?? 0n;
  if (parsed === 0n || parsed >= 1n << 160n) throw new InputError(`invalid address: ${value}`);
  return parsed;
}

const SPEC = {
  prog: "dispatcher.ts",
  description:
    "Compile the dispatcher Yul with solc 0.8.30: print its deploy initcode, or rewrite the " +
    "committed initcode artifact.",
  options: {
    "--initcode": { kind: "flag", help: "print the initcode for IMPL and VERIFIER" },
    "--artifact": {
      kind: "flag",
      help: "rewrite core/artifacts/shielded_pool_dispatcher_init.hex",
    },
  },
} as const;

function main(argv: readonly string[]): void {
  // Only --initcode takes the two addresses, and the parser takes a fixed set of positionals.
  // After "--" every argument is positional, so "--initcode" there does not choose the mode.
  const end = argv.indexOf("--");
  if ((end < 0 ? argv : argv.slice(0, end)).includes("--initcode")) {
    const positionals = [
      { name: "impl", help: "ShieldedPoolLogic implementation address" },
      { name: "verifier", help: "Groth16 verifier address" },
    ] as const;
    const { options, positionals: args } = parseArgs({ ...SPEC, positionals }, argv);
    if (options["--artifact"]) {
      throw new UsageError(SPEC, "argument --artifact: not allowed with argument --initcode");
    }
    process.stdout.write(toHex(initcode(address(args.impl), address(args.verifier))) + "\n");
  } else if (parseArgs(SPEC, argv).options["--artifact"]) {
    mkdirSync(dirname(ARTIFACT), { recursive: true });
    // No trailing newline: the deploy script's vm.parseBytes reads the file whole.
    writeFileSync(ARTIFACT, toHex(compiledInitcode()));
    process.stdout.write(ARTIFACT + "\n");
  } else {
    throw new UsageError(SPEC, "one of the arguments --initcode --artifact is required");
  }
}

if (import.meta.main) await runCli(() => main(process.argv.slice(2)));
