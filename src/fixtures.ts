/**
 * What the fixture generators share: the spend entry each proof becomes, and the rules that keep
 * a fixture's secrets. A fixture holds the only openings of its notes and the one-time
 * authorizer keys of its spends, so it is written readable by its owner only, a live one goes
 * under the ignored artifacts/ and never into a tracked file, and no run writes over a fixture
 * made for another chain, whose notes may still be unspent.
 */
import assert from "node:assert/strict";
import { mkdirSync, readlinkSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { hex32, hexPadded, toHex } from "./bytes.ts";
import { GeneratorError } from "./errors.ts";
import {
  FileChangedError,
  fileIdentity,
  readJson,
  writePrivate,
  type FileIdentity,
} from "./files.ts";
import { isObject, stringify } from "./json.ts";
import type { Encapsulate } from "./notes.ts";
import * as protocol from "./protocol.ts";
import type { ProofWords } from "./prover.ts";
import type { Rng } from "./random.ts";
import type { MerkleTree, SpendTerms, Witness } from "./wallet.ts";

export const TEST_CHAIN_ID = 31337n;
/** The pool address of the Forge tests' deployment, which the committed fixture is made for. */
export const TEST_POOL = "0xf62849f9a0b5bf2913b396098f7c7019b51a820a";
/** Where live fixtures go by default; .gitignore holds it, so move that line with it. */
export const ARTIFACTS = fileURLToPath(new URL("../artifacts", import.meta.url));
const COMMITTED_SMOKE = fileURLToPath(
  new URL("../test/fixtures/smoke_fixture.json", import.meta.url),
);

/** Proving as the generators use it: prover.ts, or a fake in tests. */
export interface Prover {
  prove(witness: Witness, tag: string): Promise<Proved>;
  assertUnprovable(witness: Witness, tag: string): Promise<void>;
}

/** A proof and its public signals [beta, gamma, alpha]. */
export interface Proved {
  publics: readonly bigint[];
  proof: ProofWords;
}

/** Everything a generator draws or prints, so tests can replay each source. */
export interface GeneratorDeps {
  prover: Prover;
  log(line: string): void;
  /** Seeds, dummy inputs and authorizers. By default the fixed seed, or secureRng with --random. */
  rng?: Rng;
  /** ML-KEM-768 encapsulation for a payment to a public address. */
  encapsulate?: Encapsulate;
  /** The random bytes standing in for a withdrawal's payee note. */
  dummyNote?: () => Uint8Array;
}

/**
 * A command-line path made absolute: a leading "~" is the home directory, and the rest is
 * resolved component by component, following links (dangling ones included) and applying ".."
 * to the path resolved so far, as the kernel does, so the overwrite check looks at the file the
 * user meant. A component that is not a readable link, or a link that loops, stays as written.
 */
export function resolvePath(text: string): string {
  const expanded = text === "~" || text.startsWith("~/") ? homedir() + text.slice(1) : text;
  // Parts still to resolve, next last. A marker records where a link led once its target's
  // parts are resolved; null marks a link being resolved, so a loop ends there.
  const rest: (string | { link: string })[] = expanded.split("/").reverse();
  const links = new Map<string, string | null>();
  let path = expanded.startsWith("/") ? "/" : process.cwd();
  while (rest.length > 0) {
    const part = rest.pop()!;
    if (typeof part !== "string") links.set(part.link, path);
    else if (part === "..") path = path.slice(0, path.lastIndexOf("/")) || "/";
    else if (part !== "" && part !== ".") {
      const next = path === "/" ? "/" + part : `${path}/${part}`;
      const target = links.has(next) ? undefined : readLink(next);
      if (target === undefined) {
        path = links.get(next) ?? next;
      } else {
        if (target.startsWith("/")) path = "/";
        links.set(next, null);
        rest.push({ link: next }, ...target.split("/").reverse());
      }
    }
  }
  return path;
}

/** Where a generator writes: the given --output, made absolute by resolvePath, or the default. */
export function outputPath(given: string | undefined, fallback: string): string {
  return given === undefined ? fallback : resolvePath(given);
}

function readLink(path: string): string | undefined {
  try {
    return readlinkSync(path);
  } catch {
    return undefined; // missing, unreadable or not a link
  }
}

/** The committed fixture for the test chain and pool, and anything else under artifacts/. */
export function defaultOutput(chainId: bigint, pool: bigint): string {
  if (chainId === TEST_CHAIN_ID && pool === BigInt(TEST_POOL)) return COMMITTED_SMOKE;
  return join(ARTIFACTS, `smoke_fixture.${chainId}.json`);
}

/**
 * Refuses to replace a fixture for any chain but the test chain, whatever mode the new run uses,
 * since it may hold the only openings of unspent notes. A file that is not a JSON object with
 * an integer chain_id counts as another chain's. Returns the identity of what is there, for
 * writeFixture to check again.
 */
export function refuseOverwrite(path: string): FileIdentity | null {
  const previous = fileIdentity(path);
  if (previous === null) return null;
  let chain = -1n;
  try {
    const data = readJson(path);
    const found = isObject(data) ? data.chain_id : undefined;
    if (typeof found === "bigint" || Number.isInteger(found)) chain = BigInt(found as number);
  } catch {
    // unreadable, not UTF-8 or not JSON
  }
  if (chain !== TEST_CHAIN_ID) {
    throw new GeneratorError(
      `${path} holds a fixture for chain ${chain} and may hold the only secrets of unspent ` +
        "notes; move it or pass another --output",
    );
  }
  return previous;
}

/** Refuses a recipient whose credit could never be claimed, before proving rather than later. */
export function refuseRecipient(recipient: bigint, pool: bigint): void {
  const { PRECOMPILES, UNCLAIMABLE_RECIPIENTS } = protocol;
  if (recipient === pool || PRECOMPILES.has(recipient) || UNCLAIMABLE_RECIPIENTS.has(recipient)) {
    const shown = hexPadded(recipient, 40);
    throw new GeneratorError(`--recipient ${shown} would strand the withdrawal credit`);
  }
}

/** Writes a fixture owner-only, refusing if what is at path changed since refuseOverwrite. */
export function writeFixture(path: string, fixture: object, previous: FileIdentity | null): void {
  mkdirSync(dirname(path), { recursive: true });
  try {
    writePrivate(path, stringify(fixture, 1), previous);
  } catch (error) {
    if (!(error instanceof FileChangedError)) throw error;
    const what = previous === null ? "appeared" : "changed";
    const message = `${path} ${what} while generating; move it and run again`;
    throw new GeneratorError(message, { cause: error });
  }
}

/** A spend's public terms, its epoch and its one-time authorizer's private key. */
export interface EntryTerms extends SpendTerms {
  epoch: bigint;
  authorizerKey: Uint8Array;
}

/**
 * A fixture's spend entry: the statement values, the authorizer key, the proof, and the openings
 * of both inputs, dummy included, followed by `extra`. If another deposit changes the tree
 * first, the notes must be proved again against a newer root, and nothing else keeps these
 * secrets.
 */
export function spendEntry(
  tree: MerkleTree,
  domain: bigint,
  inputs: readonly protocol.SpendInput[],
  outputs: readonly protocol.Output[],
  terms: EntryTerms,
  { publics, proof }: Proved,
  extra: Record<string, unknown> = {},
) {
  const { epoch, authorizer, publicAmount = 0n, fee = 0n, recipient = 0n } = terms;
  const root = tree.root();
  const [nf1, nf2] = protocol.inputNullifiers(domain, inputs);
  const [outCm1, outCm2] = protocol.outputCommitments(outputs);
  // The crux: the proof's public signals compress exactly the wallet's own ten statement
  // values, recomputed here as the pool recomputes them.
  const hashes = { nf1, nf2, outCm1, outCm2, root, domain };
  const stmt = protocol.statement({ ...hashes, publicAmount, fee, recipient, authorizer });
  const [beta, gamma, alpha] = publics;
  const { compressionAlpha, compressionBeta, fingerprint, P } = protocol;
  assert(alpha === compressionAlpha(stmt), "proof alpha does not hash the wallet's statement");
  assert(beta === compressionBeta(stmt), "proof beta is not Poseidon of the wallet's statement");
  const sigma = (alpha + beta) % P;
  assert(
    gamma === fingerprint(sigma, stmt),
    "proof gamma does not fingerprint the wallet's statement",
  );
  return {
    root: hex32(root),
    epoch: String(epoch),
    domain: hex32(domain),
    nf1: hex32(nf1),
    nf2: hex32(nf2),
    out_cm1: hex32(outCm1),
    out_cm2: hex32(outCm2),
    public_amount: String(publicAmount),
    fee: String(fee),
    recipient: hexPadded(recipient, 40),
    authorizer: hexPadded(authorizer, 40),
    authorizer_private_key: toHex(terms.authorizerKey),
    beta: hex32(beta),
    proof,
    inputs: inputs.map((i) => ({
      spend_key: hex32(i.sk),
      rho: hex32(i.rho),
      value: String(i.value),
      leaf: i.idx,
    })),
    ...extra,
  };
}
