/**
 * Rebuilds the native vectors and runs the native occurrence evidence suite against a pinned
 * ethrex source snapshot. Both cargo suites rewrite their tracked reports, native-report.json
 * and policy-report.json.
 */
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, readFileSync, realpathSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { parseArgs, runCli } from "../../src/cli/args.ts";
import { CheckError } from "../../src/errors.ts";

const HERE = import.meta.dirname;
const REPO = join(HERE, "..", "..");

type Env = NodeJS.ProcessEnv;
/** Runs a command and returns its exit status; tests pass a stub. */
export type Exec = (argv: string[], options: { cwd: string; env?: Env }) => number | null;

const spawnInherited: Exec = (argv, options) => {
  const result = spawnSync(argv[0], argv.slice(1), { ...options, stdio: "inherit" });
  if (result.error) throw new CheckError(`cannot run ${argv[0]}: ${result.error.message}`);
  return result.status;
};

/**
 * The absolute path as the kernel resolves it: each symlink is followed before the ".." after
 * it, and a missing part is kept as written. path.resolve would apply ".." first and could
 * pin-check and build against another directory.
 */
function resolveSource(given: string): string {
  let path = given.startsWith("/") ? "/" : process.cwd();
  for (const part of given.split("/").filter((p) => p !== "" && p !== ".")) {
    path = part === ".." ? dirname(path) : join(path, part);
    if (existsSync(path)) path = realpathSync(path);
  }
  return path;
}

/** Refuses a snapshot whose pinned files differ from the revision the harness was written for. */
function verifyEthrex(source: string): void {
  const pins = JSON.parse(readFileSync(join(HERE, "ethrex-source-sha256.json"), "utf8"));
  for (const [file, pin] of Object.entries<string>(pins)) {
    const bytes = readFileSync(join(source, file));
    const actual = createHash("sha256").update(bytes).digest("hex");
    if (actual !== pin) throw new CheckError(`pinned ethrex source mismatch: ${file}: ${actual}`);
  }
}

const SPEC = {
  prog: "run.ts",
  description: "Rebuild vectors and run the native occurrence evidence suite.",
  options: {
    "--ethrex-source": {
      kind: "string",
      help: "ethrex 247e2dd2 source snapshot (or set ETHREX_SOURCE)",
    },
    "--offline": { kind: "flag", help: "pass --offline to cargo" },
    "--skip-generate": { kind: "flag", help: "reuse locally generated vectors" },
  },
} as const;

export function main(argv: readonly string[], exec: Exec = spawnInherited): void {
  const { options } = parseArgs(SPEC, argv);
  const given = options["--ethrex-source"] ?? process.env.ETHREX_SOURCE;
  if (!given) throw new CheckError("--ethrex-source or ETHREX_SOURCE is required");
  const source = resolveSource(given);
  verifyEthrex(source);

  const run = (command: string[], env?: Env) => {
    process.stdout.write(`+ ${command.join(" ")}\n`);
    const status = exec(command, { cwd: REPO, env });
    if (status !== 0) throw new CheckError(`${command.join(" ")} exited with status ${status}`);
  };
  if (!options["--skip-generate"]) {
    const forge = ["forge", "build", "--root", "core/contracts", "--force"];
    run(forge);
    run(forge, { ...process.env, FOUNDRY_PROFILE: "libsmall" });
    run([process.execPath, join(HERE, "scripts", "generate-fixtures.ts")]);
  }
  // Each cargo suite runs with its Cargo.toml pointed at the snapshot.
  const offline = options["--offline"] ? ["--offline"] : [];
  const cargoTest = (dir: string, env: Env) => {
    const manifest = join(dir, "Cargo.toml");
    writeFileSync(manifest, readFileSync(`${manifest}.in`, "utf8").replaceAll("@ETHREX@", source));
    const args = ["test", ...offline, "--locked", "--manifest-path", manifest, "--", "--nocapture"];
    run(["cargo", ...args], env);
  };
  const env = { ...process.env, ETHREX_SOURCE: source };
  cargoTest(HERE, env);
  cargoTest(join(HERE, "policy"), { ...env, POLICY_REPORT: join(HERE, "policy-report.json") });
}

if (import.meta.main) await runCli(() => main(process.argv.slice(2)));
