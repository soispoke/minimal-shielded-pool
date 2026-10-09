/**
 * Rebuilds the native vectors and runs the native occurrence evidence suite against a pinned
 * ethrex source snapshot. Both cargo suites rewrite their tracked reports, native-report.json
 * and policy-report.json. CI passes --cache-only, so every proof comes from the committed
 * cache and a changed witness fails the run until its new proof is committed.
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
    "--cache-only": { kind: "flag", help: "pass --cache-only to the fixture generator" },
    "--skip-generate": { kind: "flag", help: "reuse locally generated vectors" },
  },
} as const;

function main(argv: readonly string[]): void {
  const { options } = parseArgs(SPEC, argv);
  const given = options["--ethrex-source"] ?? process.env.ETHREX_SOURCE;
  if (!given) throw new CheckError("--ethrex-source or ETHREX_SOURCE is required");
  const source = resolveSource(given);
  verifyEthrex(source);

  const run = ([program, ...args]: string[], env?: Env) => {
    const command = [program, ...args].join(" ");
    process.stdout.write(`+ ${command}\n`);
    const result = spawnSync(program, args, { cwd: REPO, env, stdio: "inherit" });
    if (result.error) throw new CheckError(`cannot run ${program}: ${result.error.message}`);
    if (result.status !== 0) throw new CheckError(`${command} exited with status ${result.status}`);
  };
  if (!options["--skip-generate"]) {
    const forge = ["forge", "build", "--root", "core/contracts", "--force"];
    run(forge);
    run(forge, { ...process.env, FOUNDRY_PROFILE: "libsmall" });
    const cacheOnly = options["--cache-only"] ? ["--cache-only"] : [];
    run([process.execPath, join(HERE, "scripts", "generate-fixtures.ts"), ...cacheOnly]);
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
