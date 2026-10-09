/**
 * Reports which formally verified files differ from their pinned hashes.
 *
 *   node tools/check-formal-pins.ts
 *
 * The Lean proofs in soispoke/verified-shielded-pool cover one pool commit, whose artifacts
 * SPEC.md section 1 pins by SHA-256. This script hashes the pinned files here and lists any
 * that changed, so a pull request shows when it moves the pool away from the verified commit.
 * It only reports: it exits 0 whether or not pins differ, and whether or not SPEC.md can be
 * read.
 *
 * It reads formal/SPEC.md when the formal repository is checked out as formal/, and otherwise
 * fetches SPEC.md from the formal repository's main branch. It imports no packages, so it runs
 * without installing any.
 */
import { createHash } from "node:crypto";
import { appendFileSync, existsSync, readFileSync } from "node:fs";
import { resolve } from "node:path";

import { readText, ROOT, utf8 } from "./check.ts";

export const SPEC_URL =
  "https://raw.githubusercontent.com/soispoke/verified-shielded-pool/main/SPEC.md";
// SPEC.md names the pinned files by their paths at the verified commit, before the repository
// was reorganized. Look each one up where it lives now; a path not listed here (for example
// one SPEC.md already gives in the new layout) is used as is.
export const MOVED: ReadonlyMap<string, string> = new Map([
  ["build/spend.r1cs", "core/artifacts/spend.r1cs"],
  ["build/spend_final.zkey", "core/artifacts/spend_final.zkey"],
  ["circuits/spend.circom", "core/circuits/spend.circom"],
  [
    "devnet/build/shielded_pool_dispatcher_init.hex",
    "core/artifacts/shielded_pool_dispatcher_init.hex",
  ],
  ["devnet/ShieldedPoolDispatcher.yul", "core/dispatcher/ShieldedPoolDispatcher.yul"],
  ["contracts/src/ShieldedPoolLogic.sol", "core/contracts/src/ShieldedPoolLogic.sol"],
  ["contracts/src/Groth16Verifier.sol", "core/contracts/src/Groth16Verifier.sol"],
  ["contracts/vectors/spend_vkey.json", "core/artifacts/spend_vkey.json"],
  ["contracts/foundry.toml", "core/contracts/foundry.toml"],
  ["activation_manifest.testbed.json", "core/activation_manifest.testbed.json"],
  ["contracts/src/PoseidonT3.sol", "core/contracts/src/PoseidonT3.sol"],
  ["contracts/src/PoseidonT4.sol", "core/contracts/src/PoseidonT4.sol"],
]);

/** SPEC.md's text and where it came from: formal/SPEC.md under root, or a fetch. */
export async function readSpec(root = ROOT): Promise<[text: string, source: string]> {
  const local = resolve(root, "formal", "SPEC.md");
  if (existsSync(local)) return [readText(local), "formal/SPEC.md"];
  const response = await fetch(SPEC_URL, { signal: AbortSignal.timeout(30_000) });
  if (!response.ok) throw new Error(`HTTP ${response.status} ${response.statusText}`.trim());
  return [utf8.decode(await response.arrayBuffer()), SPEC_URL];
}

const backticked = (text: string) => [...text.matchAll(/`([^`]+)`/g)].map((m) => m[1]);

/**
 * [path, sha256] for every row of SPEC.md's section 1 table, parsed as
 * formal/tools/check_formal.py parses it. A row's first cell may list several files of one
 * directory, the first with its path and the rest by name.
 */
export function pinned(spec: string): [name: string, sha256: string][] {
  const lines = spec.split("## 2.")[0].split(/\r\n|\n|\r/);
  const pins: [string, string][] = [];
  for (const line of lines.filter((l) => l.startsWith("|")).slice(2)) {
    const cells = line.replace(/^\|+|\|+$/g, "").split("|");
    if (cells.length < 2) throw new Error(`SPEC.md table row has one cell: ${line}`);
    const paths = backticked(cells[0]).filter((p) => p.includes("/") || p.includes("."));
    const hashes = backticked(cells[1]).filter((t) => /^[0-9a-f]{64}$/.test(t));
    const base = paths.length > 0 ? paths[0].slice(0, paths[0].lastIndexOf("/") + 1) : "";
    for (let i = 0; i < Math.min(paths.length, hashes.length); i++) {
      const name = paths[i];
      pins.push([i === 0 || name.includes("/") ? name : base + name, hashes[i]]);
    }
  }
  return pins;
}

/**
 * The lines to print for a SPEC.md text read from source, checking files under root, and the
 * summary for GitHub's step summary (null when nothing was checked).
 */
export function report(
  spec: string,
  source: string,
  root = ROOT,
): { lines: string[]; summary: string | null } {
  const pins = pinned(spec);
  if (pins.length === 0) {
    return {
      lines: [`::warning::no full SHA-256 pins found in ${source}; nothing checked`],
      summary: null,
    };
  }
  const changed: string[] = [];
  for (const [name, want] of pins) {
    const local = MOVED.get(name) ?? name;
    const path = resolve(root, local);
    if (
      !existsSync(path) ||
      createHash("sha256").update(readFileSync(path)).digest("hex") !== want
    ) {
      changed.push(local);
    }
  }
  const commit = /at `([0-9a-f]{7,40})`/.exec(spec)?.[1] ?? "the pinned commit";
  const lines = changed.map(
    (name) =>
      `::warning file=${name}::${name} differs from the formally verified version; ` +
      `the proofs cover pool commit ${commit}`,
  );
  const summary =
    changed.length > 0
      ? `${changed.length} of ${pins.length} formally verified files differ from ${commit}: ` +
        changed.map((n) => `\`${n}\``).join(", ") +
        ". The proofs in soispoke/verified-shielded-pool do not cover this change " +
        "until its pins are updated."
      : `All ${pins.length} formally verified files match ${commit} (${source}).`;
  return { lines: [...lines, summary], summary };
}

async function main(): Promise<void> {
  let spec: string, source: string;
  try {
    [spec, source] = await readSpec();
  } catch (error) {
    // fetch's own message is only "fetch failed"; the reason is its cause.
    const cause =
      error instanceof Error && error.cause instanceof Error ? `: ${error.cause.message}` : "";
    const reason = error instanceof Error ? error.message + cause : String(error);
    console.log(`::warning::could not read the formal pins (${reason}); nothing checked`);
    return;
  }
  const { lines, summary } = report(spec, source);
  for (const line of lines) console.log(line);
  const stepSummary = process.env.GITHUB_STEP_SUMMARY;
  if (summary !== null && stepSummary) appendFileSync(stepSummary, summary + "\n");
}

if (import.meta.main) await main();
