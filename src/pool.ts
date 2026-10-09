/**
 * The pool client for chain 8141's EIP-8141/8250/8272 dialect. A spend is VERIFY(0x…8272,
 * recent-root tuple) -> VERIFY(pool, proof) -> SENDER(pool, settle(Spend) || notes), plus at
 * most one DEFAULT tail; the pool pays, its nonce keys are the nullifiers, and the authorizer
 * the proof selects signs the whole transaction. Shield and publish are calls from a funded
 * account: a self-verify frame, then a SENDER frame to the pool.
 */
import { readFileSync } from "node:fs";
import { setTimeout as delay } from "node:timers/promises";

import {
  concat,
  fromHex,
  hexPadded,
  maxBigint,
  parseAddress,
  parseConfigAddress,
  parseDec,
  parseHex,
  parseUint,
  toBigint,
  toHex,
  uintFromText,
  word,
} from "./bytes.ts";
import { InputError, PoolError } from "./errors.ts";
import { readJson } from "./files.ts";
import {
  addressOf,
  APPROVE,
  checksumAddress,
  executionCapUsage,
  maxCost,
  MODE,
  parsePrivateKey,
  rawTx,
  SCHEME,
  sigHash,
  signHash,
  totalGasLimit,
  type Frame,
  type FrameTx,
} from "./frametx.ts";
import * as gas from "./gas.ts";
import { asObject, isObject, parse, stringify, type JsonObject } from "./json.ts";
import * as protocol from "./protocol.ts";
import { rpc, RpcError } from "./rpc.ts";

// The self-verify frame of a shield or publish, and the floor when its SENDER frame is resized.
const CALL_VERIFY_FRAME_GAS = 80_000n;
const MAX_PRIORITY_FEE = 10n ** 9n;
const INITCODE = new URL("../core/artifacts/shielded_pool_dispatcher_init.hex", import.meta.url);
// A proof from the committed proving key, used to check the verifier a pool is linked to.
const REFERENCE_FIXTURE = new URL("../test/fixtures/smoke_fixture.json", import.meta.url);

/**
 * The node calls the pool client makes; tests pass a fake. `call` throws RpcError for an error
 * reply and RpcTransportError otherwise; `simulate` returns null when the node lacks the method.
 */
export interface PoolNode {
  call(method: string, params: readonly unknown[]): Promise<unknown>;
  simulate(raw: string): Promise<unknown>;
}

/**
 * The node at `url`, with the pool's 20-second timeout by default. simulate dry-runs a signed
 * frame transaction through ethrex_simulateFrameTransaction, the frame-native eth_estimateGas; a
 * transaction over the gas cap comes back as a result with valid=false, not as an error.
 */
export function poolNode(url: string, { timeoutMs = 20_000 } = {}): PoolNode {
  const call = (method: string, params: readonly unknown[]) =>
    rpc(url, method, params, { timeoutMs });
  return {
    call,
    async simulate(raw) {
      try {
        return await call("ethrex_simulateFrameTransaction", [raw]);
      } catch (error) {
        if (!(error instanceof RpcError)) throw error;
        if (error.code === -32601) return null;
        throw new PoolError(`  simulate RPC error: ${error.detail}`);
      }
    },
  };
}

const get = (value: unknown, key: string): unknown => (isObject(value) ? value[key] : undefined);

// ---- fixture entries ----

type Parser = (value: unknown, what: string) => bigint;
const word32: Parser = (value, what) => toBigint(fromHex(value, what, 32));
// A fixture's integers are decimal or 0x hex strings, or JSON numbers (root_slot may be one).
const uintField: Parser = (value, what) =>
  typeof value === "string" ? parseUint(value, what) : parseDec(value, what);

/** The note bytes a wallet stored in a fixture entry; the protocol encoders check the length. */
function notesField(entry: unknown, key: string, what: string): Uint8Array {
  const notes = get(entry, key);
  if (notes === undefined) {
    throw new PoolError(
      `the fixture's ${what} has no \`${key}\`: regenerate it with src/cli/smoke.ts or ` +
        "src/cli/nonce-race.ts so its recipients can find their notes",
    );
  }
  return fromHex(notes, `the ${what}'s ${key}`);
}

/** The Spend of a fixture spend entry with root_slot set. */
function entrySpend(entry: unknown): protocol.Spend {
  const at = (parse: Parser, key: string) => parse(get(entry, key), `the spend entry's ${key}`);
  return {
    root: at(word32, "root"),
    rootSlot: at(uintField, "root_slot"),
    epoch: at(uintField, "epoch"),
    domain: at(word32, "domain"),
    nf1: at(word32, "nf1"),
    nf2: at(word32, "nf2"),
    outCm1: at(word32, "out_cm1"),
    outCm2: at(word32, "out_cm2"),
    publicAmount: at(uintField, "public_amount"),
    fee: at(uintField, "fee"),
    recipient: at(parseAddress, "recipient"),
    authorizer: at(parseAddress, "authorizer"),
  };
}

/** settle(Spend) calldata followed by the notes, from a fixture spend entry with root_slot set. */
export function settleCalldata(entry: unknown): Uint8Array {
  return protocol.encodeSettle(entrySpend(entry), notesField(entry, "notes", "spend"));
}

/** shield(inner, note) calldata with the note the wallet made for the new leaf. */
export function shieldCalldata(inner: unknown, entry: unknown): Uint8Array {
  const note = notesField(entry, "note", "shield");
  return protocol.encodeShield(word32(inner, "the shield's inner"), note);
}

function entryProof(entry: unknown): [proof: protocol.Proof, beta: bigint] {
  // Rows must be arrays: an object keyed "0" and "1" is not read as one.
  const row = (value: unknown, i: number) => (Array.isArray(value) ? value[i] : undefined);
  const at = (key: string, ...path: number[]) =>
    parseHex(path.reduce(row, get(get(entry, "proof"), key)), `the spend entry's proof ${key}`);
  const proof: protocol.Proof = {
    pA: [at("pA", 0), at("pA", 1)],
    pB: [
      [at("pB", 0, 0), at("pB", 0, 1)],
      [at("pB", 1, 0), at("pB", 1, 1)],
    ],
    pC: [at("pC", 0), at("pC", 1)],
  };
  return [proof, parseHex(get(entry, "beta"), "the spend entry's beta")];
}

/** The proof frame's 288 bytes: the Groth16 proof in snarkjs calldata word order, then beta. */
export function entryProofBytes(entry: unknown): Uint8Array {
  return protocol.proofBytes(...entryProof(entry));
}

/** The entry's authorizer key, refused unless it is the key of the authorizer the proof binds. */
export function authorizerKey(entry: unknown): Uint8Array {
  const what = "the spend entry's authorizer_private_key";
  const key = parsePrivateKey(get(entry, "authorizer_private_key"), what);
  const authorizer = parseAddress(get(entry, "authorizer"), "the spend entry's authorizer");
  if (addressOf(key) !== authorizer) {
    throw new PoolError("fixture authorizer private key does not match the proof public");
  }
  return key;
}

// ---- the optional fourth frame ----

/** A custom DEFAULT tail. Its calldata already holds whatever authorization the target needs. */
export interface Action {
  readonly target: bigint;
  readonly data: Uint8Array;
  readonly gasLimit: bigint;
  readonly stateLimit: bigint;
}

export const ACTION_OPTION_FLAGS: readonly string[] = [
  "--action-target",
  "--action-call",
  "--action-gas",
  "--action-state-gas",
];
// Whole hex bytes after an optional "0x", then an optional "0X": the prefixes this option has
// always accepted, so "0x0X12" is 0x12.
const CALL_FORM = /^(?:0x)?(?:0X)?((?:[0-9a-fA-F]{2})*)$/;

/**
 * One all-or-none custom tail from [flag, value, ...] pairs, or null when no action flag is
 * present. The CLI passes --flag=value forms back as pairs, so they obey the same rules.
 */
export function actionOptions(argv: readonly string[]): Action | null {
  const flags = ACTION_OPTION_FLAGS;
  const unknown = new Set(argv.filter((a) => a.startsWith("--action-") && !flags.includes(a)));
  if (unknown.size > 0) {
    throw new InputError(`unknown action option: ${[...unknown].sort().join(", ")}`);
  }
  const missing = flags.filter((flag) => !argv.includes(flag));
  if (missing.length === flags.length) return null;
  if (missing.length > 0) throw new InputError(`action requires ${missing.sort().join(", ")}`);
  const value = <T>(flag: string, read: (raw: string) => T | null): T => {
    if (argv.filter((arg) => arg === flag).length !== 1) {
      throw new InputError(`${flag} must be supplied exactly once`);
    }
    const raw = argv[argv.indexOf(flag) + 1];
    if (raw === undefined || raw.startsWith("--")) throw new InputError(`${flag} requires a value`);
    const parsed = read(raw);
    if (parsed === null) throw new InputError(`invalid ${flag} value: ${raw}`);
    return parsed;
  };
  const calldata = (raw: string) => {
    const digits = CALL_FORM.exec(raw)?.[1];
    return digits === undefined ? null : fromHex("0x" + digits, "--action-call");
  };
  return {
    target: value("--action-target", uintFromText),
    data: value("--action-call", calldata),
    gasLimit: value("--action-gas", uintFromText),
    stateLimit: value("--action-state-gas", uintFromText),
  };
}

/**
 * DEFAULT(pool, claimWithdrawal(recipient)) at the claim frame's wallet limits, unchecked: the
 * native generator signs claims for deliberately invalid settlements.
 */
export function defaultClaimTail(pool: bigint, recipient: bigint): Frame {
  const data = concat(protocol.CLAIM_SELECTOR, word(recipient));
  return {
    mode: MODE.DEFAULT,
    flags: APPROVE.NONE,
    target: pool,
    gasLimit: gas.CLAIM_FRAME_GAS,
    stateLimit: gas.CLAIM_FRAME_STATE_GAS,
    value: 0n,
    data,
  };
}

/**
 * A spend's optional fourth DEFAULT frame: a withdrawal's claim by default, none when `omit`
 * leaves withdrawalCredit, or one custom action. Resource limits are checked on the whole tx.
 */
export function spendTailFrame(
  pool: bigint,
  settle: Uint8Array,
  action: Action | null = null,
  options: { omit?: boolean } = {},
): Frame | null {
  const decoded = protocol.decodeSettle(settle);
  if (decoded === null) {
    throw new InputError("tail frame requires settle(Spend) calldata followed by its notes");
  }
  const { publicAmount: amount, recipient } = decoded.spend;
  if (pool <= 0n || pool >= 1n << 160n || recipient >= 1n << 160n || amount >= 1n << 128n) {
    throw new InputError("invalid pool, recipient, or public amount");
  }
  if ((amount === 0n) !== (recipient === 0n)) {
    throw new InputError("public amount and recipient must both be zero or both nonzero");
  }
  // Checked before omit, so leaving out the tail cannot launder a credit nobody can claim.
  const unclaimable = protocol.PRECOMPILES.has(recipient)
    ? "a precompile, which no one controls"
    : protocol.UNCLAIMABLE_RECIPIENTS.get(recipient);
  if (amount !== 0n && (unclaimable || recipient === pool)) {
    const what = unclaimable ?? "the pool itself";
    throw new InputError(`withdrawal recipient would strand the credit: ${what}`);
  }
  if (options.omit) {
    if (action !== null) throw new InputError("omit cannot be combined with a custom action");
    return null;
  }
  if (action === null) return amount === 0n ? null : defaultClaimTail(pool, recipient);
  const { target, data, gasLimit, stateLimit } = action;
  if (target <= 0n || target >= 1n << 160n) {
    throw new InputError("action target must be a nonzero address");
  }
  // Both pinned ethrex revisions panic executing a top-level frame to a precompile after an
  // earlier frame emitted logs, as settlement does.
  if (protocol.PRECOMPILES.has(target)) {
    throw new InputError("action target must not be a precompile");
  }
  if (gasLimit <= 0n) throw new InputError("action execution gas must be positive");
  if (stateLimit < 0n) throw new InputError("action state gas must be nonnegative");
  return { mode: MODE.DEFAULT, flags: APPROVE.NONE, target, gasLimit, stateLimit, value: 0n, data };
}

// ---- building ----

/**
 * A spend's frames, unchecked, so the native generator can sign deliberately invalid spends.
 * The recent-root frame approves nothing. The proof frame reads the tuple back from frame 0,
 * and once the proof verifies the pool approves itself as sender and payer. The SENDER frame
 * starts at the limit the activation profile proves: an out-of-gas after payment approval
 * burns the notes.
 */
export function spendFrames(spend: {
  pool: bigint;
  recentRoot: Uint8Array;
  proof: Uint8Array;
  settle: Uint8Array;
  tail?: Frame | null;
  settleGas?: bigint;
}): Frame[] {
  const { pool, recentRoot, proof, settle, tail, settleGas = gas.SETTLE_FRAME_GAS } = spend;
  return [
    {
      mode: MODE.VERIFY,
      flags: APPROVE.NONE,
      target: protocol.RECENT_ROOT_ADDRESS,
      gasLimit: gas.RECENT_ROOT_FRAME_GAS,
      stateLimit: 0n,
      value: 0n,
      data: recentRoot,
    },
    {
      mode: MODE.VERIFY,
      flags: APPROVE.EXECUTION_AND_PAYMENT,
      target: pool,
      gasLimit: gas.VERIFY_FRAME_GAS,
      stateLimit: gas.VERIFY_FRAME_STATE_GAS,
      value: 0n,
      data: proof,
    },
    {
      mode: MODE.SENDER,
      flags: APPROVE.NONE,
      target: pool,
      gasLimit: settleGas,
      stateLimit: gas.SETTLE_FRAME_STATE_GAS,
      value: 0n,
      data: settle,
    },
    ...(tail ? [tail] : []),
  ];
}

/** A spend's EIP-8250 nonce keys: its two nullifiers in ascending numeric order. */
export function spendNonceKeys(settle: Uint8Array): bigint[] {
  const [a, b] = [4, 5].map((i) => toBigint(settle.subarray(4 + 32 * i, 36 + 32 * i)));
  return a <= b ? [a, b] : [b, a];
}

/** Gives the transaction its one secp256k1 signature, in place; the hash elides its bytes. */
export function signTransaction(tx: FrameTx, key: Uint8Array): FrameTx {
  const unsigned = { scheme: SCHEME.SECP256K1, signer: addressOf(key), msg: new Uint8Array(0) };
  tx.signatures = [{ ...unsigned, signature: new Uint8Array(0) }];
  tx.signatures = [{ ...unsigned, signature: signHash(sigHash(tx), key) }];
  return tx;
}

/**
 * Refuses a transaction over chain-wide limits: execution (intrinsic cost plus frame budgets,
 * against the EIP-7976 calldata floor; EIP-7825's cap does not count state gas) and size.
 */
export function checkTxResourceLimits(tx: FrameTx): void {
  const [used, cap] = [executionCapUsage(tx), gas.EIP7825_TX_GAS_CAP];
  if (used > cap) throw new InputError(`declared execution ${used} exceeds EIP-7825 cap ${cap}`);
  const [size, limit] = [rawTx(tx).length, gas.ETHREX_MEMPOOL_MAX_BYTES];
  if (size > limit) {
    throw new InputError(
      `encoded transaction ${size} bytes exceeds ethrex ${limit}-byte mempool limit`,
    );
  }
}

// ---- checks against the node ----

/**
 * Calldata for the reference transfer proof with its compressed signals [beta, gamma, alpha],
 * and the same call with gamma changed. A verifier for this circuit accepts only the first.
 */
export function referenceVerifierCalls(): [good: string, changed: string] {
  const e = (parse(readFileSync(REFERENCE_FIXTURE, "utf8")) as { transfer: JsonObject }).transfer;
  const stmt = protocol.statement(entrySpend({ ...e, root_slot: 0 }));
  const alpha = protocol.compressionAlpha(stmt);
  const [proof, beta] = entryProof(e);
  const gamma = protocol.fingerprint((alpha + beta) % protocol.P, stmt);
  const call = (g: bigint) => toHex(protocol.verifyProofCall(proof, [beta, g, alpha]));
  return [call(gamma), call((gamma + 1n) % protocol.P)];
}

/** An eth_call's one-word answer, or null for a JSON-RPC error or an answer of another length. */
async function callWord(node: PoolNode, to: string, data: string): Promise<bigint | null> {
  const result = await node.call("eth_call", [{ to, data }, "latest"]).catch((error) => {
    if (error instanceof RpcError) return null;
    throw error;
  });
  const isWord = typeof result === "string" && result.length === 66;
  return isWord ? parseHex(result, "eth_call's result") : null;
}

/**
 * Refuses a pool that is not this profile's dispatcher, linked to the configured logic and
 * verifier on the configured chain, so no deposit lands where VERIFY rejects every spend. This
 * catches a stale config, not a malicious deployer; only a JSON-RPC error reply is a verdict.
 */
export async function checkDeployedProfile(
  node: PoolNode,
  pool: bigint,
  configuredChain: bigint,
  logic: bigint,
  verifier: bigint,
): Promise<void> {
  const profile = gas.POOL_PROFILE;
  const chainId = parseHex(await node.call("eth_chainId", []), "eth_chainId's result");
  if (chainId !== configuredChain) {
    throw new PoolError(
      `RPC is on chain ${chainId}, but the config names chain ${configuredChain}`,
    );
  }
  // The previous profile shares this one's domain formula, so the code itself is compared.
  const links = toHex(concat(word(logic), word(verifier))).slice(2);
  const initcode = readFileSync(INITCODE, "utf8").trim() + links;
  const expected = await node.call("eth_call", [{ data: initcode }, "latest"]).catch((error) => {
    if (!(error instanceof RpcError)) throw error;
    throw new PoolError(
      `could not simulate the ${profile} dispatcher deployment: ${error.message}`,
    );
  });
  const [address, verifierAddress] = [hexPadded(pool, 40), hexPadded(verifier, 40)];
  const code = await node.call("eth_getCode", [address, "latest"]);
  const deployed = typeof expected === "string" && expected.length > 2 && typeof code === "string";
  if (!deployed || code.toLowerCase() !== expected.toLowerCase()) {
    throw new PoolError(
      `pool ${address} is not the ${profile} dispatcher linked to the configured logic ` +
        `${hexPadded(logic, 40)} and verifier ${verifierAddress}`,
    );
  }
  // The dispatcher's code does not cover the verifier it calls.
  const [good, changed] = referenceVerifierCalls();
  for (const [data, verdict] of [[good, 1n] as const, [changed, 0n] as const]) {
    if ((await callWord(node, verifierAddress, data)) !== verdict) {
      throw new PoolError(`verifier ${verifierAddress} does not verify ${profile} proofs`);
    }
  }
  const domain = await callWord(node, address, toHex(protocol.encodeDomainCall(0n)));
  if (domain === null) {
    throw new PoolError(
      `pool ${address} does not expose domain(uint64); it is not a ${profile} deployment`,
    );
  }
  if (domain !== protocol.domainScalar(chainId, pool)) {
    throw new PoolError(`pool ${address} domain(0) does not match ${profile} on chain ${chainId}`);
  }
}

/**
 * Refuses to fund a note this fixture's proofs cannot spend: their domain names a chain, pool
 * and epoch, and their paths assume the note lands at `leaf` of the tree with root `priorRoot`.
 * Another deposit can still take the leaf first, so callers also check shieldLeaf.
 */
export async function checkShieldFixture(
  node: PoolNode,
  pool: bigint,
  chainId: bigint,
  fixture: unknown,
  leaf: bigint,
  priorRoot: bigint,
): Promise<void> {
  const field = (key: string) => get(fixture, key);
  const recorded = ["chain_id", "pool_address", "epoch", "domain"];
  const missing = recorded.filter((key) => field(key) === undefined);
  if (missing.length > 0) {
    throw new PoolError(`shield requires the fixture to record ${missing.join(", ")}`);
  }
  const epoch = parseDec(field("epoch"), "the fixture's epoch");
  if (
    parseDec(field("chain_id"), "the fixture's chain_id") !== chainId ||
    parseAddress(field("pool_address"), "the fixture's pool_address") !== pool
  ) {
    throw new PoolError(
      `fixture was made for pool ${field("pool_address")} on chain ${field("chain_id")}, ` +
        `not ${hexPadded(pool, 40)} on chain ${chainId}`,
    );
  }
  const domain = parseHex(field("domain"), "the fixture's domain");
  if (domain !== protocol.domainScalar(chainId, pool, epoch)) {
    throw new PoolError("fixture domain does not match its chain, pool and epoch");
  }
  const state: bigint[] = [];
  for (const signature of ["currentEpoch()", "nextIndex()", "currentRoot()"]) {
    const call = { to: hexPadded(pool, 40), data: toHex(protocol.selector(signature)) };
    const answer = await node.call("eth_call", [call, "latest"]).catch((error) => {
      if (!(error instanceof RpcError)) throw error;
      throw new PoolError(`could not read the pool's next leaf: ${error.message}`);
    });
    state.push(parseHex(answer, `the pool's ${signature}`));
  }
  // A full tree rolls to a new, empty epoch before this deposit.
  const full = state[1] === protocol.TREE_CAPACITY;
  const [nowEpoch, nowIndex, nowRoot] = full ? [state[0] + 1n, 0n, protocol.EMPTY_ROOT] : state;
  if (nowEpoch !== epoch || nowIndex !== leaf) {
    throw new PoolError(
      `fixture expects the note at epoch ${epoch} leaf ${leaf}, but the pool's next leaf is ` +
        `epoch ${nowEpoch} leaf ${nowIndex}`,
    );
  }
  if (nowRoot !== priorRoot) {
    throw new PoolError(
      "the pool's tree is not the one this fixture's proofs assume: another deposit took an earlier leaf",
    );
  }
}

/**
 * (epoch, index) from the pool's LeafAppended log in a shield receipt, or null. Addresses are
 * checked before parsing, so another contract's malformed log is ignored; the node writes the
 * address, so one that is not an address is refused on any log.
 */
export function shieldLeaf(receipt: unknown, pool: bigint): [epoch: bigint, index: bigint] | null {
  const list = (value: unknown): unknown[] => (Array.isArray(value) ? value : []);
  const frames = list(get(receipt, "frameReceipts")).map((f) => get(f, "logs"));
  for (const log of [get(receipt, "logs"), ...frames].flatMap(list)) {
    const address = get(log, "address");
    if (address === undefined) continue;
    if (parseAddress(address, "a receipt log's address") !== pool) continue;
    const leaf = protocol.parseLeafAppended(log as JsonObject);
    if (leaf !== null) return [leaf.epoch, leaf.index];
  }
  return null;
}

/**
 * Why the node would refuse a root published in `slot`, or null. EIP-8272 judges a
 * transaction against the earliest block that could carry it, so the current slot is the
 * head's plus one; comparing against the head would sign a transaction one slot too late.
 */
export function recentRootWindowError(slot: bigint, latestSlot: bigint, epoch = 0n): string | null {
  const current = latestSlot + 1n;
  if (slot >= current) {
    return (
      `  recent-root ref is not yet referenceable: publication slot ${slot} is not earlier than ` +
      `current slot ${current}. A root written in slot S is only usable from S+1 on; wait one ` +
      "slot and re-sign."
    );
  }
  if (current - slot >= protocol.RECENT_ROOT_LENGTH) {
    return (
      `  recent-root ref expired: publication slot ${slot} is outside the ` +
      `${protocol.RECENT_ROOT_LENGTH}-slot window at current slot ${current}. If the tree has ` +
      `not changed since the proof's root, call publishEpochRoot(${epoch}), read that block's ` +
      "slotNumber, and re-sign with --root-slot set to that consensus slot."
    );
  }
  return null;
}

/**
 * Frame 0's tuple, source_id || uint64 slot || root, once the slot (EIP-7843's slotNumber, never
 * derived from timestamps) is in the window and the recent-root contract holds this root there.
 */
export async function recentRootReference(
  node: PoolNode,
  pool: bigint,
  entry: unknown,
): Promise<Uint8Array> {
  const slot = parseDec(get(entry, "root_slot"), "the spend entry's root_slot");
  const epoch = parseDec(get(entry, "epoch"), "the spend entry's epoch");
  const source = protocol.sourceId(pool, epoch);
  const root = word32(get(entry, "root"), "the spend entry's root");
  const latest = get(await node.call("eth_getBlockByNumber", ["latest", false]), "slotNumber");
  if (latest === undefined) {
    throw new PoolError("latest block has no EIP-7843 slotNumber; refusing timestamp derivation");
  }
  const what = "the latest block's slotNumber";
  const problem = recentRootWindowError(slot, parseHex(latest, what), epoch);
  if (problem) throw new PoolError(problem);
  const at = toHex(protocol.recentRootStorageKey(source, slot));
  const contract = hexPadded(protocol.RECENT_ROOT_ADDRESS, 40);
  const stored = await node.call("eth_getStorageAt", [contract, at, "latest"]);
  const entryHash = toBigint(protocol.recentRootEntry(source, slot, root));
  // A storage word has at most 64 digits; a longer answer is not this entry.
  const found = parseHex(stored, "eth_getStorageAt's result");
  if (found !== entryHash || (stored as string).length > 66) {
    throw new PoolError(
      `  recent-root ref self-check failed at consensus slot ${slot}. The fixture root differs ` +
        "from the root committed at that slot, or the wrong epoch/slot was supplied. Either " +
        "would be rejected as FrameTxRecentRootNotCommitted. If another deposit changed the " +
        "tree, the notes are safe but this proof is not: prove again against a published root, " +
        "at the leaves the notes occupy, from the openings in the fixture entries' `inputs`, " +
        "and keep this fixture: it holds the only copy of those secrets.",
    );
  }
  return protocol.recentRootTuple(source, slot, root);
}

// ---- sending ----

/** What to send: an ordinary call from the funded account, or a spend the pool pays for. */
export type Send =
  | { readonly kind: "call"; readonly value: bigint; readonly calldata: Uint8Array }
  | {
      readonly kind: "spend";
      readonly settle: Uint8Array;
      readonly proof: Uint8Array;
      readonly recentRoot: Uint8Array;
      readonly action?: Action | null;
      readonly omitTail?: boolean;
      readonly allowFailedClaim?: boolean;
    };

/** Where the sender reports progress, and how it waits; sleep and now default to real time. */
export interface SendIo {
  readonly log: (line: string) => void;
  readonly sleep?: (ms: number) => Promise<void>;
  readonly now?: () => number;
}

// A node value in a progress line: a string as it is, anything else as JSON.
const show = (value: unknown): string =>
  typeof value === "string" ? value : stringify(value ?? null);
const grouped = (value: bigint | null): string =>
  value === null ? "null" : value.toLocaleString("en-US");

/**
 * A simulation result as ethrex writes it, or null when the node lacks the method: an object
 * whose gas values are hex or null and whose frames are objects. Other fields stay raw, since
 * they only shape messages or are compared with "success".
 */
function simulation(result: unknown) {
  if (result === null) return null;
  if (!isObject(result)) {
    throw new PoolError(
      `  simulate: ethrex_simulateFrameTransaction returned ${show(result)}, not an object`,
    );
  }
  const gasOf = (value: unknown, what: string) =>
    value == null ? null : parseHex(value, `the simulation's ${what}`);
  const frames = result.frames ?? [];
  if (!Array.isArray(frames) || !frames.every(isObject)) {
    throw new PoolError(`  simulate: frames ${show(frames)} is not a list of objects; not sending`);
  }
  return {
    result,
    valid: result.valid === true,
    frames: frames.map((f, i) => ({
      gasUsed: gasOf(f.gasUsed, `frame ${i} gasUsed`),
      // Only the JSON boolean true: an aggregate status cannot tell a failed tail from a
      // failed settlement.
      succeeded: f.succeeded === true,
    })),
    gasUsed: gasOf(result.gasUsed, "gasUsed"),
  };
}

const ACTION_REBUILD =
  "Fix the account calldata or limits and rebuild. The RPC has seen this signed spend, so " +
  "check that its nonce keys are unused before sending another.";

/**
 * Builds, simulates and sends a call or a spend and returns its receipt, or null after a dry
 * run. A spend whose SENDER frame reverts still burns its notes, so it is sent only after a
 * simulation in which settlement (frame 2) succeeded, and keeps its SENDER limit: EIP-8037 state
 * accounting varies too much for measured gas plus 25% to be a safe margin. A call that reverts
 * loses nothing (a shield's deposit stays with the sender), so it may go on the default limits
 * when the node cannot simulate, and its SENDER frame is sized from the simulated gas.
 */
export async function buildAndSend(
  node: PoolNode,
  io: SendIo,
  key: Uint8Array,
  pool: bigint,
  send: Send,
  options: { dryRun?: boolean; maxFee?: bigint; maxPriorityFee?: bigint } = {},
): Promise<JsonObject | null> {
  const spend = send.kind === "spend" ? send : null;
  const value = send.kind === "call" ? send.value : 0n;
  const omit = spend?.omitTail;
  const tail = spend && spendTailFrame(pool, spend.settle, spend.action ?? null, { omit });
  const tailKind = spend?.action ? "action" : tail ? "claim" : null;
  const signer = addressOf(key);
  const account = hexPadded(spend ? pool : signer, 40);
  const chainId = parseHex(await node.call("eth_chainId", []), "eth_chainId's result");
  // A spend's sequence is always 0, but its nonce is still read, keeping the RPC order.
  const count = await node.call("eth_getTransactionCount", [account, "latest"]);
  const nonce = parseHex(count, "eth_getTransactionCount's result");
  const block = await node.call("eth_getBlockByNumber", ["latest", false]);
  if (!isObject(block)) throw new PoolError("eth_getBlockByNumber returned no latest block");
  const { baseFeePerGas = "0x0" } = block;
  const baseFee = parseHex(baseFeePerGas, "the latest block's baseFeePerGas");
  // By default the fee cap is twice the base fee plus a 1 gwei tip. A spend's proof fixes a fee
  // that must cover the transaction's maximum cost, so the overrides let an existing proof fit
  // when base fees rise.
  const maxPriorityFee = options.maxPriorityFee ?? MAX_PRIORITY_FEE;
  const maxFee = options.maxFee ?? 2n * baseFee + maxPriorityFee;
  if (maxFee < baseFee || maxPriorityFee > maxFee) {
    throw new PoolError("fee overrides require max_fee >= base_fee and max_priority <= max_fee");
  }
  if (value > 0n) {
    const answer = await node.call("eth_getBalance", [account, "latest"]);
    const balance = parseHex(answer, "eth_getBalance's result");
    if (balance < value) {
      throw new PoolError(
        `  sender ${account} has ${balance} wei; this frame moves ${value} wei plus gas ` +
          "(deployer balance after contract creates is a common cause)",
      );
    }
  }
  // The pool sends a spend at sequence 0 under its nullifier keys; a call goes from the key's
  // account under key 0.
  const build = (senderGas = gas.SETTLE_FRAME_GAS): FrameTx => {
    const tx: FrameTx = {
      chainId,
      nonceKeys: spend ? spendNonceKeys(spend.settle) : [0n],
      nonceSeq: spend ? 0n : nonce,
      sender: spend ? pool : signer,
      frames:
        send.kind === "spend"
          ? spendFrames({ ...send, pool, tail, settleGas: senderGas })
          : [
              // The account's default code checks the signature and approves both.
              {
                mode: MODE.VERIFY,
                flags: APPROVE.EXECUTION_AND_PAYMENT,
                target: signer,
                gasLimit: CALL_VERIFY_FRAME_GAS,
                stateLimit: 0n,
                value: 0n,
                data: new Uint8Array(0),
              },
              {
                mode: MODE.SENDER,
                flags: APPROVE.NONE,
                target: pool,
                gasLimit: senderGas,
                stateLimit: gas.SETTLE_FRAME_STATE_GAS,
                value,
                data: send.calldata,
              },
            ],
      signatures: [],
      maxPriorityFee,
      maxFee,
      maxBlobFee: 0n,
      blobHashes: [],
    };
    checkTxResourceLimits(signTransaction(tx, key));
    return tx;
  };
  let tx = build();
  let raw = toHex(rawTx(tx));
  const sim = simulation(await node.simulate(raw));
  const r = sim?.result ?? {};
  const { prefixShape: shape, payer, executionStatus: status } = r;
  const report = `shape=${show(shape)}  payer=${show(payer)}  status=${show(status)}`;
  if (options.dryRun) {
    if (sim === null) {
      io.log("  dry-run: ethrex_simulateFrameTransaction unavailable on this endpoint");
      return null;
    }
    io.log(`  dry-run: valid=${show(r.valid)}  ${report}`);
    io.log(`           violation=${show(r.violation)}`);
    io.log(`           max_cost=${maxCost(tx)}  total_gas_limit=${totalGasLimit(tx)}`);
    const per = sim.frames.map((f, i) => `f${i}=${grouped(f.gasUsed)}`).join(", ");
    if (sim.gasUsed !== null) io.log(`           gas=${grouped(sim.gasUsed)}  (${per})`);
    return null;
  }

  let effective = sim;
  if (sim === null) {
    if (spend) {
      throw new PoolError(
        "  simulate: ethrex_simulateFrameTransaction unavailable here; refusing to send a " +
          "nullifier-consuming spend without a pre-send simulation (a mined tx whose SENDER " +
          "frame reverts burns the spent notes)",
      );
    }
    io.log("  simulate: ethrex_simulateFrameTransaction unavailable here; default gas limits");
  } else if (sim.valid) {
    const per = sim.frames.map((f, i) => `f${i}=${show(f.gasUsed)}`).join(", ");
    io.log(`  simulate: valid  ${report}  gas=${show(sim.gasUsed)}  (${per})`);
    // A reverting SENDER still reports per-frame gas; only a successful one is a size.
    const used = sim.frames.at(-1)?.gasUsed ?? null;
    if (used !== null && !spend && status === "success") {
      const sized = maxBigint(used + used / 4n, CALL_VERIFY_FRAME_GAS);
      const resized = build(sized);
      const resizedRaw = toHex(rawTx(resized));
      const check = simulation(await node.simulate(resizedRaw));
      if (check?.valid && check.result.executionStatus === "success") {
        [tx, raw, effective] = [resized, resizedRaw, check];
        const measured = `measured ${grouped(used)} + 25%, floor 80k`;
        io.log(`  sized SENDER frame to ${grouped(sized)} gas (${measured})`);
      } else if (check?.valid) {
        const fallback = grouped(gas.SETTLE_FRAME_GAS);
        io.log(`  sized SENDER ${grouped(sized)} did not execute; keeping default ${fallback}`);
      }
    }
  } else {
    // A DEFAULT tail revert is not a prefix failure: an allowed claim failure may go ahead,
    // but an action that simulation shows failing is never broadcast.
    const settled = spend !== null && sim.frames[2]?.succeeded === true;
    if (settled && tailKind === "action") {
      throw new PoolError(
        "  simulate: settlement would succeed but the gas-only action frame would fail; not " +
          `sending. ${ACTION_REBUILD}`,
      );
    }
    if (!(settled && tailKind === "claim" && spend?.allowFailedClaim)) {
      let message = `  simulate: INVALID (${show(r.violation)}); not sending`;
      if (spend && show(r.violation).includes("Nonce mismatch")) {
        message +=
          "\n  a nullifier key is already consumed: this spend, or another spend of the" +
          "\n  same note or dummy, may already have settled. Check the notes before" +
          "\n  building another spend.";
      }
      throw new PoolError(message);
    }
    io.log(
      `  simulate: valid=${show(r.valid)} violation=${show(r.violation)}; settlement succeeded ` +
        "and failed claim is allowed",
    );
  }

  const outcome = effective?.result ?? {};
  if (spend) {
    const frames = effective?.frames ?? [];
    if (frames[2]?.succeeded !== true) {
      throw new PoolError("  simulate: settlement frame 2 did not explicitly succeed; not sending");
    }
    const tailFailed = tail !== null && frames[3]?.succeeded !== true;
    if (tailFailed && tailKind === "action") {
      throw new PoolError(
        "  simulate: settlement succeeded but the gas-only action frame failed; not sending. " +
          ACTION_REBUILD,
      );
    }
    if (tailFailed && !spend.allowFailedClaim) {
      throw new PoolError(
        "  simulate: settlement succeeded but the claim frame failed; not sending. The credit " +
          "would remain and can be claimed later.",
      );
    }
    if (frames.length !== tx.frames.length || frames.some((f, i) => i !== 3 && !f.succeeded)) {
      throw new PoolError("  simulate: settlement succeeded but another frame failed; not sending");
    }
    if (tailFailed) {
      io.log(
        "  simulate: settlement succeeded; claim frame failed (allowed); credit will remain for a later claim",
      );
    }
  } else if ((outcome.executionStatus ?? "success") !== "success") {
    const hint =
      value > 0n
        ? `; this frame moves ${value} wei — if the sender is short after contract creates, ` +
          "top up and redeploy from scratch"
        : " (if root-not-recent, retry one block later)";
    const error = outcome.executionError;
    const cause = show(typeof error === "string" && error !== "" ? error : outcome.executionStatus);
    throw new PoolError(`  simulate: execution did not succeed (${cause}); not sending${hint}`);
  }

  io.log(
    `  frame tx: sender=${account} signer=${checksumAddress(signer)} ` +
      `nonce_keys=[${tx.nonceKeys.join(", ")}] raw_len=${rawTx(tx).length} ` +
      `max_cost=${maxCost(tx)} sig_hash=${toHex(sigHash(tx)).slice(2, 20)}...`,
  );
  const hash = await node.call("eth_sendRawTransaction", [raw]);
  io.log(`  submitted: ${show(hash)}`);
  for (let poll = 0; poll < 30; poll++) {
    const receipt = await node.call("eth_getTransactionReceipt", [hash]);
    if (receipt !== null) return checkReceipt(io, receipt, spend, tailKind);
    await (io.sleep ?? delay)(2_000);
  }
  throw new PoolError("  not mined within timeout");
}

// Frame receipt statuses are compared as the literal strings, so "0x01" never passes for "0x1".
const FRAME_STATUSES: ReadonlySet<unknown> = new Set(["0x0", "0x1", "0x2"]);

/** Refuses a mined transaction whose settlement or tail did not do what was signed. */
function checkReceipt(
  io: SendIo,
  receipt: unknown,
  spend: { allowFailedClaim?: boolean } | null,
  tailKind: "action" | "claim" | null,
): JsonObject {
  if (!isObject(receipt)) {
    throw new PoolError(`  eth_getTransactionReceipt returned ${show(receipt)}, not a receipt`);
  }
  const { status = "0x0", gasUsed = "0x0" } = receipt;
  const reverted = parseHex(status, "the receipt's status") !== 1n;
  const block = parseHex(receipt.blockNumber, "the receipt's blockNumber");
  io.log(
    `  MINED block=${block} type=${show(receipt.type)} status=${show(receipt.status)} ` +
      `gasUsed=${parseHex(gasUsed, "the receipt's gasUsed")}`,
  );
  if (!spend) {
    if (reverted) throw new PoolError(`  tx reverted (status ${show(receipt.status)}); aborting`);
    return receipt;
  }
  const frames = Array.isArray(receipt.frameReceipts) ? receipt.frameReceipts : [];
  const [settlement, tailStatus] = [get(frames[2], "status"), get(frames[3], "status")];
  if (!FRAME_STATUSES.has(settlement)) {
    throw new PoolError("  settlement outcome unavailable; inspect frame receipts before retrying");
  }
  if (settlement !== "0x1") {
    throw new PoolError(
      "  settlement frame did not succeed; nullifiers may have been consumed without creating " +
        "outputs. Inspect frame receipts before retrying.",
    );
  }
  if (tailKind !== null && !FRAME_STATUSES.has(tailStatus)) {
    throw new PoolError(
      tailKind === "action"
        ? "  settlement succeeded, but the gas-only action outcome is unknown. The input notes " +
            "may already be consumed; inspect the nullifiers, outputs, and account state. Do not " +
            "retry or re-sign using those notes."
        : "  settlement succeeded, but the claim frame outcome is unknown. Inspect the pool " +
            "credit before taking any recovery action.",
    );
  }
  const tailReverted = tailKind !== null && tailStatus !== "0x1";
  if (tailReverted && tailKind === "action") {
    throw new PoolError(
      "  settlement succeeded, but the gas-only action frame failed. The input notes were " +
        "consumed and settlement outputs were created; inspect them and the account state. Do " +
        "not retry or re-sign using those notes.",
    );
  }
  const claimFailed = "  settlement succeeded, but the claim frame failed";
  if (tailReverted && !spend.allowFailedClaim) {
    throw new PoolError(`${claimFailed}. The settled credit remains recoverable.`);
  }
  if (tailReverted) io.log(`${claimFailed} (allowed). The settled credit remains recoverable.`);
  // Only an allowed claim revert may leave the whole transaction reverted.
  if (reverted && !tailReverted) {
    throw new PoolError(
      `  tx reverted (status ${show(receipt.status)}) after successful settlement; inspect frame receipts`,
    );
  }
  return receipt;
}

/** Waits for two blocks after the publication block, then returns its EIP-7843 slotNumber. */
export async function waitPublishedSlot(
  node: PoolNode,
  io: SendIo,
  receipt: unknown,
  timeoutMs = 180_000,
): Promise<bigint> {
  const published = parseHex(get(receipt, "blockNumber"), "the receipt's blockNumber");
  const hash = get(receipt, "blockHash");
  if (hash === undefined) throw new PoolError("  the publication receipt has no blockHash");
  const now = io.now ?? Date.now;
  const deadline = now() + timeoutMs;
  for (;;) {
    const head = parseHex(await node.call("eth_blockNumber", []), "eth_blockNumber's result");
    io.log(`  confirmations: head=${head} publish_block=${published} (need +2)`);
    if (head >= published + 2n) break;
    if (now() >= deadline) {
      throw new PoolError(
        `  timed out waiting for 2 blocks after publish at ${published} (head ${head})`,
      );
    }
    await (io.sleep ?? delay)(2_000);
  }
  const block = await node.call("eth_getBlockByHash", [hash, false]);
  if (!isObject(block)) throw new PoolError("  publication block is no longer on the chain");
  const slot = block.slotNumber;
  if ((slot ?? "") === "") throw new PoolError("  publication block has no slotNumber");
  const what = "the publication block's slotNumber";
  const value = typeof slot === "string" ? uintFromText(slot) : parseDec(slot, what);
  if (value === null)
    throw new InputError(`${what} must be 0x hex or decimal without leading zeros`);
  return value;
}

// ---- the pool CLI's operations (src/cli/pool.ts parses the command line) ----

/** One run of the pool CLI, as its command line names it. */
export interface PoolCommand {
  readonly rpc: string;
  readonly config: string;
  readonly fixture: string;
  readonly op: "shield" | "publish" | "transfer" | "withdraw";
  readonly dryRun: boolean;
  /** publish: the epoch to publish, 0 by default. */
  readonly epoch?: bigint;
  /** shield: the index into a nonce-race fixture's shields. */
  readonly note?: bigint;
  /** A spend: the fixture key of its entry, the operation's name by default. */
  readonly spendKey?: string;
  /** A spend: the slot that published its root, the config's _slot_<op> by default. */
  readonly rootSlot?: bigint;
  /** A spend: the fee cap and tip in wei, in place of the defaults buildAndSend computes. */
  readonly maxFee?: bigint;
  readonly maxPriorityFee?: bigint;
  readonly omitTail: boolean;
  readonly allowFailedClaim: boolean;
  readonly action: Action | null;
}

/** Where poolCommand reports and finds the funded key; tests replace the node and checks. */
export interface PoolCommandDeps {
  readonly log: (line: string) => void;
  readonly readFundedKey: () => Promise<Uint8Array>;
  readonly node?: PoolNode;
  readonly checkDeployedProfile?: typeof checkDeployedProfile;
  readonly buildAndSend?: typeof buildAndSend;
}

/**
 * The shield to fund: a smoke fixture's note A, proved as the first leaf of an empty tree, or
 * --note N of a nonce-race fixture, whose shields share one tree (the second completes the root
 * both race transfers reference) and so record their leaf and prior root.
 */
function fixtureShield(fix: JsonObject, note: bigint | undefined) {
  if (!Object.hasOwn(fix, "shields")) {
    const value = parseDec(fix.shield_value, "the fixture's shield_value");
    const entry = Object.hasOwn(fix, "shield_note") ? { note: fix.shield_note } : {};
    return { value, inner: fix.inner_a, leaf: 0n, priorRoot: protocol.EMPTY_ROOT, entry };
  }
  if (note === undefined) {
    throw new PoolError("this fixture has a 'shields' array; pass --note N (0-based)");
  }
  const s: unknown = Array.isArray(fix.shields) ? fix.shields[Number(note)] : undefined;
  if (!isObject(s)) throw new PoolError(`the fixture's shields have no note ${note}`);
  if (!Object.hasOwn(s, "prior_root")) {
    throw new PoolError("this fixture's shields do not record prior_root; regenerate it");
  }
  const value = parseDec(s.value, "the shield's value");
  const leaf = parseDec(s.leaf, "the shield's leaf");
  const priorRoot = parseHex(s.prior_root, "the shield's prior_root");
  return { value, inner: s.inner, leaf, priorRoot, entry: s };
}

/**
 * Runs one pool CLI operation. A config for another profile, and options that do not fit the
 * operation, are refused before any RPC; then the deployed pool is checked, except before a
 * publication, and the shield, publication or spend is built and sent.
 */
export async function poolCommand(command: PoolCommand, deps: PoolCommandDeps): Promise<void> {
  const { op, dryRun, action, omitTail, allowFailedClaim } = command;
  const sendTx = deps.buildAndSend ?? buildAndSend;
  const config = readJson(command.config);
  const fix = readJson(command.fixture) as JsonObject;
  // Both files are read before the config's shape is checked, as the oracle read them.
  const cfg = asObject(config, command.config);
  const poolAddress = parseConfigAddress(cfg.pool, "the config's pool");
  const spend = op === "transfer" || op === "withdraw";
  // A config for another profile names a pool this tooling cannot spend from. The label is a
  // first check before any RPC; checkDeployedProfile compares the deployed code.
  if (op !== "publish") {
    if (cfg.profile !== gas.POOL_PROFILE) {
      throw new PoolError(
        `${op} requires profile=${gas.POOL_PROFILE}; this config names ` +
          `${stringify(cfg.profile ?? null)}. Use a fresh deployment of this profile`,
      );
    }
    const missing = ["chainId", "logic", "verifier"].filter((key) => !Object.hasOwn(cfg, key));
    if (missing.length > 0) {
      throw new PoolError(`${op} requires the config to record ${missing.join(", ")}`);
    }
  }
  // JSON numbers, which readJson gives for integers this small: 100000.0 matches, "100000" not.
  const claimLimits = [Number(gas.CLAIM_FRAME_GAS), Number(gas.CLAIM_FRAME_STATE_GAS)];
  if (spend && (cfg.claimGas !== claimLimits[0] || cfg.claimStateGas !== claimLimits[1])) {
    throw new PoolError(`spends require claimGas/claimStateGas matching ${gas.POOL_PROFILE}`);
  }
  if (omitTail && action !== null) {
    throw new PoolError("--no-tail cannot be combined with action options");
  }
  if ((action !== null || omitTail) && !spend) {
    throw new PoolError("action options and --no-tail are valid only for transfer or withdraw");
  }
  if (allowFailedClaim && op !== "withdraw") {
    throw new PoolError("--allow-failed-claim is only valid on withdraw");
  }
  if (allowFailedClaim && omitTail) {
    throw new PoolError("--allow-failed-claim cannot be combined with --no-tail");
  }
  const { maxFee, maxPriorityFee } = command;
  if ((maxFee !== undefined || maxPriorityFee !== undefined) && !spend) {
    throw new PoolError("fee overrides are valid only for transfer or withdraw");
  }

  const node = deps.node ?? poolNode(command.rpc);
  const io: SendIo = { log: deps.log };
  const sendCall = async (value: bigint, calldata: Uint8Array) => {
    const call = { kind: "call", value, calldata } as const;
    return sendTx(node, io, await deps.readFundedKey(), poolAddress, call, { dryRun });
  };
  if (op === "publish") {
    const epoch = command.epoch ?? 0n;
    const calldata = protocol.encodePublish(epoch);
    io.log(`publishEpochRoot(${epoch}) via frame tx -> pool ${cfg.pool}`);
    const receipt = await sendCall(0n, calldata);
    if (receipt !== null) io.log(`ROOT_SLOT ${await waitPublishedSlot(node, io, receipt)}`);
    return;
  }

  const logic = parseConfigAddress(cfg.logic, "the config's logic");
  const verifier = parseConfigAddress(cfg.verifier, "the config's verifier");
  const chainId = parseDec(cfg.chainId, "the config's chainId");
  const checkDeployed = deps.checkDeployedProfile ?? checkDeployedProfile;
  await checkDeployed(node, poolAddress, chainId, logic, verifier);

  if (op === "shield") {
    const { value, inner, leaf, priorRoot, entry } = fixtureShield(fix, command.note);
    // A missing inner is refused before the pool's tree is read; shieldCalldata checks its form.
    if (inner === undefined) throw new PoolError("the fixture does not record the shield's inner");
    await checkShieldFixture(node, poolAddress, chainId, fix, leaf, priorRoot);
    const calldata = shieldCalldata(inner, entry);
    io.log(`shield ${value} wei via frame tx -> pool ${cfg.pool}`);
    const receipt = await sendCall(value, calldata);
    if (receipt === null) return;
    const landed = shieldLeaf(receipt, poolAddress);
    const shown = landed === null ? "None" : `(${landed.join(", ")})`;
    io.log(`SHIELD_LEAF ${shown}`);
    const epoch = parseDec(fix.epoch, "the fixture's epoch");
    if (landed === null || landed[0] !== epoch || landed[1] !== leaf) {
      throw new PoolError(
        `  the note landed at (epoch, leaf) ${shown}, not (${fix.epoch}, ${leaf}), so the ` +
          "fixture's proofs cannot spend it. Keep this fixture: its spend entries' inputs hold " +
          "the note's opening, from which it can be proved again at the leaf it occupies.",
      );
    }
    return;
  }

  // A nonce-race fixture holds two transfers against one root (--spend-key picks one), both
  // using the slot in which its second shield completed the tree (--root-slot).
  const name = command.spendKey ?? op;
  const source = Object.hasOwn(fix, name) ? fix[name] : undefined;
  if (!isObject(source)) throw new PoolError(`the fixture has no spend entry ${name}`);
  const configured = `_slot_${op}`;
  const slot = command.rootSlot ?? cfg[configured];
  if (slot === undefined) throw new PoolError(`the config has no ${configured}; pass --root-slot`);
  // recentRootReference reads the entry's root_slot as decimal text. A configured non-string
  // must be a non-negative integer here, since String() would also turn [100] into "100".
  const rootSlot = typeof slot === "string" ? slot : parseDec(slot, `the config's ${configured}`);
  const e = { ...source, root_slot: String(rootSlot) };
  const recentRoot = await recentRootReference(node, poolAddress, e);
  const key = authorizerKey(e);
  const settle = settleCalldata(e);
  io.log(`join-split ${op} via frame tx (pool ${cfg.pool} self-pays)`);
  const proof = entryProofBytes(e);
  const fields = { settle, proof, recentRoot, action, omitTail, allowFailedClaim };
  const sendOptions = { dryRun, maxFee, maxPriorityFee };
  await sendTx(node, io, key, poolAddress, { kind: "spend", ...fields }, sendOptions);
}
