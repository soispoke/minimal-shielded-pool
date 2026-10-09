/**
 * Note delivery: a secret per sender and recipient, and 48-byte notes on chain.
 *
 * A recipient needs each note's amount and rho to spend it. The pool publishes notes and never
 * reads them (core/contracts/src/ShieldedPoolLogic.sol): settlement carries two notes, one per
 * output, and a shield carries one. A sender's first payment to a public address puts its
 * ML-KEM-768 ciphertext before the notes.
 *
 *   note = tag (16) || ChaCha20-Poly1305(value as 16 bytes) (16 + 16 tag)
 *   tag  = PRF(K, "tag", i)[:16]
 *   key  = PRF(K, "key", i)              each key seals one note, so the nonce is zero
 *   rho  = PRF64(K, "rho", i) mod r       the recipient recomputes the commitment
 *   cm   = Poseidon(2, Poseidon2(owner_pk, rho), value)
 *
 * PRF is HMAC-SHA256 and PRF64 joins two outputs into 512 bits before reducing. `i` counts the
 * notes sent under K. Reusing an index repeats the tag, the key and rho, which links two
 * payments and reveals the XOR of their amounts, so a sender reserves each index in its saved
 * state before using it. The recipient watches LOOKAHEAD indices past the last one it found,
 * so a sender keeps fewer than LOOKAHEAD payments past the last one it has seen final.
 *
 * K, the secret a sender and recipient share, comes from the recipient's public address (a
 * version byte, owner_pk and an ML-KEM-768 encapsulation key): the payment that opens the channel
 * carries its 1,088-byte ciphertext, and no other transaction does, since two carrying it would
 * be linked. Or the recipient issues K = PRF(root, "direct", n), for the next number n, to one
 * sender over a post-quantum channel; n stays within GAP of the highest number paid, which is how
 * far a scan from the seed looks. Change and shields from one's own funds use K = PRF(root,
 * "self"), and a withdrawal puts a random dummy in the payee note.
 *
 * A recipient rebuilds every incoming note, and every change note, from its seed alone. A sender
 * cannot recompute a secret it encapsulated, so after a restore it opens a new channel with each
 * recipient, and resumes its self channel with selfChannel(). Direct secrets and the self channel
 * do not depend on the deployment, so a seed is used with one pool only.
 *
 * All notes paid to one address share its spend key. A disclosure receipt for one of them
 * reveals Poseidon2(D, spend_key), which identifies every spend of that address in epoch D, so
 * src/disclosure.ts refuses such a receipt unless asked for it explicitly.
 */
import * as crypto from "node:crypto";

import {
  compareBigint,
  concat,
  fromHex,
  hex32,
  hexPadded,
  maxBigint,
  parseAddress,
  parseConfigAddress,
  parseDec,
  parseHex,
  toBigint,
  toBytes,
  toHex,
  word,
} from "./bytes.ts";
import { NotesError } from "./errors.ts";
import {
  FileChangedError,
  fileIdentity,
  readJson,
  readPrivate,
  withLock,
  writePrivate,
} from "./files.ts";
import {
  KEM_CIPHERTEXT_BYTES,
  NOTE_BYTES,
  POOL_PROFILE,
  SHIELD_NOTE_BYTES,
  SPEND_NOTES_BYTES,
} from "./gas.ts";
import { asList, asObject, isObject, stringify, type JsonObject } from "./json.ts";
import * as protocol from "./protocol.ts";
import { LEAF_APPENDED, NOTES, NOTE_SPENT, P } from "./protocol.ts";
import type { Rng } from "./random.ts";
import { RpcChain } from "./rpc.ts";

const LABEL = "minimal-shielded-pool:note:v1:";
const TAG_BYTES = 16;
const VALUE_BYTES = 16;
const SECRET_BYTES = 32;
const EK_BYTES = 1184;
const ADDRESS_VERSION = 1;
export const ADDRESS_BYTES = 1 + 32 + EK_BYTES;
const MIN_SEED_BYTES = 32;
export const GAP = 20;
export const LOOKAHEAD = 20;
export const RESTORE_SKIP = LOOKAHEAD / 2;
const STATE_VERSION = 2;
export const POOL_TOPICS: readonly string[] = [LEAF_APPENDED, NOTE_SPENT, NOTES];
const EMPTY: Uint8Array = new Uint8Array();

// ---- primitives ----

/** HMAC-SHA256 under a domain-separated label; an integer part is one 32-byte word. */
export function prf(key: Uint8Array, label: string, ...parts: (bigint | Uint8Array)[]): Uint8Array {
  const hmac = crypto.createHmac("sha256", key).update(LABEL + label);
  for (const part of parts) hmac.update("|").update(typeof part === "bigint" ? word(part) : part);
  return new Uint8Array(hmac.digest());
}

/** A field element from 512 PRF bits, so the reduction mod P has no useful bias. */
export function prfField(key: Uint8Array, label: string, ...parts: (bigint | Uint8Array)[]) {
  return toBigint(concat(prf(key, `${label}:0`, ...parts), prf(key, `${label}:1`, ...parts))) % P;
}

export function noteTag(secret: Uint8Array, index: bigint): Uint8Array {
  return prf(secret, "tag", index).subarray(0, TAG_BYTES);
}

export function noteRho(secret: Uint8Array, index: bigint): bigint {
  return prfField(secret, "rho", index);
}

const NONCE = new Uint8Array(12);
const AAD = { plaintextLength: VALUE_BYTES };

/** The 48-byte note for the index-th payment under `secret`, and its rho. */
export function sealNote(secret: Uint8Array, index: bigint, value: bigint) {
  if (!(value > 0n && value < protocol.MAX_VALUE)) {
    throw new NotesError("a note's value must be positive and fit 128 bits");
  }
  const tag = noteTag(secret, index);
  const cipher = crypto.createCipheriv("chacha20-poly1305", prf(secret, "key", index), NONCE);
  cipher.setAAD(tag, AAD);
  const sealed = concat(cipher.update(toBytes(value, VALUE_BYTES)), cipher.final());
  return { note: concat(tag, sealed, cipher.getAuthTag()), rho: noteRho(secret, index) };
}

/** The note's value, or null if it was not sealed with (secret, index). */
export function openNote(secret: Uint8Array, index: bigint, note: Uint8Array): bigint | null {
  const tag = note.subarray(0, TAG_BYTES);
  if (note.length !== NOTE_BYTES || !crypto.timingSafeEqual(tag, noteTag(secret, index))) {
    return null;
  }
  const decipher = crypto.createDecipheriv("chacha20-poly1305", prf(secret, "key", index), NONCE);
  decipher.setAAD(tag, AAD).setAuthTag(note.subarray(TAG_BYTES + VALUE_BYTES));
  const value = toBigint(decipher.update(note.subarray(TAG_BYTES, TAG_BYTES + VALUE_BYTES)));
  try {
    decipher.final();
  } catch {
    return null;
  }
  return value > 0n ? value : null;
}

/** Random bytes in a note's place, for a withdrawal's payee: they open for no one. */
export function dummyNote(rng: Rng): Uint8Array {
  return rng.bytes(NOTE_BYTES);
}

/** Settlement's notes: an optional ciphertext, then the payee and change notes. */
export function spendNotes(payee: Uint8Array, change: Uint8Array, ciphertext = EMPTY) {
  const data = concat(ciphertext, payee, change);
  const notes = payee.length === NOTE_BYTES && change.length === NOTE_BYTES;
  if (!notes || !SPEND_NOTES_BYTES.includes(data.length)) {
    throw new NotesError(
      "a spend carries two 48-byte notes, optionally after a 1,088-byte ciphertext",
    );
  }
  return data;
}

/** A shield's note, optionally after a ciphertext. */
export function shieldNotes(note: Uint8Array, ciphertext = EMPTY): Uint8Array {
  const data = concat(ciphertext, note);
  if (note.length !== NOTE_BYTES || !SHIELD_NOTE_BYTES.includes(data.length)) {
    throw new NotesError(
      "a shield carries one 48-byte note, optionally after a 1,088-byte ciphertext",
    );
  }
  return data;
}

/** cm of an output paid to owner (protocol.commitment takes a spend key instead). */
export function outputCommitment(owner: bigint, rho: bigint, value: bigint): bigint {
  return protocol.tagged(protocol.TAG_LEAF, protocol.p2(owner, rho), value);
}

// ---- keys and addresses ----

// Node imports ML-KEM-768 keys (OID 2.16.840.1.101.3.4.4.2) only as DER: PKCS#8 holding the
// FIPS 203 seed d || z, and SPKI holding the 1,184-byte encapsulation key.
const PKCS8_SEED = Buffer.from("3054020100300b060960864801650304040204428040", "hex");
const SPKI = Buffer.from("308204b2300b0609608648016503040402038204a100", "hex");
const NO_MLKEM =
  "this Node cannot load ML-KEM-768 keys: note delivery needs Node 24.7 or later built with " +
  "OpenSSL 3.5 or later";

const spki = (ek: Uint8Array) =>
  crypto.createPublicKey({ key: Buffer.concat([SPKI, ek]), format: "der", type: "spki" });

function publicKey(ek: Uint8Array): crypto.KeyObject {
  try {
    return spki(ek);
  } catch {
    // An all-zero key passes FIPS 203's check that every 12-bit coefficient is below 3329, so if
    // it fails too, this Node has no ML-KEM.
    try {
      spki(new Uint8Array(EK_BYTES));
    } catch {
      throw new NotesError(NO_MLKEM);
    }
    throw new NotesError("the address's ML-KEM-768 key is invalid");
  }
}

/** A public address: owner_pk and an ML-KEM-768 encapsulation key. */
export class Address {
  readonly ownerPk: bigint;
  readonly ek: Uint8Array;

  constructor(ownerPk: bigint, ek: Uint8Array) {
    this.ownerPk = ownerPk;
    this.ek = ek;
  }

  encode(): Uint8Array {
    return concat(Uint8Array.of(ADDRESS_VERSION), word(this.ownerPk), this.ek);
  }

  hex(): string {
    return toHex(this.encode());
  }

  /** An address from its bytes or hex ("0x" optional), with its owner key and ek checked. */
  static decode(data: string | Uint8Array): Address {
    if (typeof data === "string") {
      if (!/^(0x)?([0-9a-fA-F]{2})*$/.test(data)) throw new NotesError("an address is hex");
      data = fromHex("0x" + data.replace(/^0x/, ""), "an address");
    }
    if (data.length !== ADDRESS_BYTES || data[0] !== ADDRESS_VERSION) {
      throw new NotesError(
        `an address is ${ADDRESS_BYTES} bytes starting with version ${ADDRESS_VERSION}`,
      );
    }
    const owner = toBigint(data.subarray(1, 33));
    if (!(owner > 0n && owner < P)) {
      throw new NotesError("the address's owner key is not a nonzero field element");
    }
    const ek = data.slice(33);
    publicKey(ek);
    return new Address(owner, ek);
  }
}

/** One address's keys, all derived from the wallet seed. */
export class WalletKeys {
  readonly account: bigint;
  readonly root: Uint8Array;
  readonly spendKey: bigint;
  readonly ownerPk: bigint;
  readonly selfSecret: Uint8Array;
  readonly #kem: crypto.KeyObject;

  constructor(seed: Uint8Array, account = 0n) {
    if (seed.length < MIN_SEED_BYTES) {
      throw new NotesError(`a seed has at least ${MIN_SEED_BYTES} bytes`);
    }
    if (account < 0n) throw new NotesError("an account number is nonnegative");
    this.account = account;
    this.root = prf(seed, "account", account);
    this.spendKey = prfField(this.root, "spend");
    if (this.spendKey === 0n) throw new NotesError("degenerate spend key");
    this.ownerPk = protocol.ownerPk(this.spendKey);
    // FIPS 203's 64-byte seed (d || z) regenerates the same key pair in any library.
    const key = Buffer.concat([PKCS8_SEED, prf(this.root, "kem-d"), prf(this.root, "kem-z")]);
    try {
      this.#kem = crypto.createPrivateKey({ key, format: "der", type: "pkcs8" });
    } catch {
      throw new NotesError(NO_MLKEM);
    }
    this.selfSecret = prf(this.root, "self");
  }

  address(): Address {
    const der = crypto.createPublicKey(this.#kem).export({ format: "der", type: "spki" });
    return new Address(this.ownerPk, new Uint8Array(der.subarray(SPKI.length)));
  }

  /** The secret this wallet hands its number-th out-of-band sender. */
  directSecret(number: bigint): Uint8Array {
    if (number < 0n) throw new NotesError("a direct secret number is nonnegative");
    return prf(this.root, "direct", number);
  }

  decapsulate(ciphertext: Uint8Array): Uint8Array {
    return new Uint8Array(crypto.decapsulate(this.#kem, ciphertext));
  }
}

// ---- sending ----

/** A sender's secret with one recipient, and the next index it may use. */
export interface Outgoing {
  ownerPk: bigint;
  secret: Uint8Array;
  nextIndex: bigint;
  ciphertext: Uint8Array; // the opening payment's, until that payment is final
  ciphertextSent: boolean; // the opening payment is reserved but not final
  confirmed: bigint; // one past the highest index seen final
}

function outgoing(ownerPk: bigint, secret: Uint8Array, rest: Partial<Outgoing> = {}): Outgoing {
  const fresh = { nextIndex: 0n, ciphertext: EMPTY, ciphertextSent: false, confirmed: 0n };
  return { ownerPk, secret, ...fresh, ...rest };
}

export function outgoingToJson(channel: Outgoing) {
  return {
    owner_pk: hex32(channel.ownerPk),
    secret: toHex(channel.secret),
    next_index: channel.nextIndex,
    ciphertext: toHex(channel.ciphertext),
    ciphertext_sent: channel.ciphertextSent,
    confirmed: channel.confirmed,
  };
}

export function outgoingFromJson(data: unknown): Outgoing {
  const d = asObject(data, "a channel");
  const ciphertextSent = bool(d.ciphertext_sent, "ciphertext_sent");
  return outgoing(parseHex(d.owner_pk, "owner_pk"), fromHex(d.secret, "secret"), {
    nextIndex: parseDec(d.next_index, "next_index"),
    ciphertext: fromHex(d.ciphertext, "ciphertext"),
    ciphertextSent,
    confirmed: parseDec(d.confirmed, "confirmed"),
  });
}

/** ML-KEM-768 encapsulation to an encapsulation key; tests replay recorded pairs instead. */
export type Encapsulate = (ek: Uint8Array) => { secret: Uint8Array; ciphertext: Uint8Array };

const encapsulateMlKem: Encapsulate = (ek) => {
  const { sharedKey, ciphertext } = crypto.encapsulate(publicKey(ek));
  return { secret: new Uint8Array(sharedKey), ciphertext: new Uint8Array(ciphertext) };
};

/** A new secret with the owner of a public address, and the ciphertext that carries it. */
export function openChannel(
  address: Address | string | Uint8Array,
  encapsulate: Encapsulate = encapsulateMlKem,
): Outgoing {
  const to = address instanceof Address ? address : Address.decode(address);
  const { secret, ciphertext } = encapsulate(to.ek);
  return outgoing(to.ownerPk, secret, { ciphertext });
}

/** The sender's side of a secret the recipient handed over out of band. */
export function directChannel(owner: bigint, secret: Uint8Array): Outgoing {
  if (secret.length !== SECRET_BYTES || !(owner > 0n && owner < P)) {
    throw new NotesError("a direct secret is 32 bytes for a nonzero owner key");
  }
  return outgoing(owner, secret.slice());
}

/**
 * The self channel of a wallet restored from its seed, or of a device taking over sending (one
 * device sends from an account at a time, and a saved channel is stale once another has sent),
 * after a scan to the finalized head. It resumes RESTORE_SKIP indices past the last self note
 * found, which is safe while at most RESTORE_SKIP self payments the previous device sent are
 * pending; with more, wait until they are final or can no longer land (a spend cannot once its
 * recent root has left the window).
 */
export function selfChannel(scanner: Scanner): Outgoing {
  const found = scanner.incoming.find((i) => i.kind === "self");
  if (found === undefined) throw new NotesError("the wallet state has no self channel");
  const nextIndex = found.nextIndex + BigInt(RESTORE_SKIP);
  const { ownerPk, selfSecret } = scanner.keys;
  return outgoing(ownerPk, selfSecret, { nextIndex, confirmed: found.nextIndex });
}

/** Records that the payment carrying `index` is final and succeeded, so the channel is open. */
export function finalized(channel: Outgoing, index: bigint): void {
  if (!(index >= 0n && index < channel.nextIndex)) {
    throw new NotesError("that index was never reserved on this channel");
  }
  channel.ciphertext = EMPTY;
  channel.ciphertextSent = false;
  channel.confirmed = maxBigint(channel.confirmed, index + 1n);
}

/**
 * Seals the channel's next note and advances its index. Save the state before broadcasting the
 * note: an index used twice repeats its tag, key and rho. Retry a payment that did not land with
 * its existing note, so that both attempts carry the same bytes and spend the same inputs, and at
 * most one lands; two transactions with one ciphertext would also be linked.
 */
export function reserve(channel: Outgoing, value: bigint) {
  if (channel.ciphertextSent) {
    throw new NotesError(
      "this channel's opening payment is not final yet: retry that payment with its note, or " +
        "open a new channel, since two transactions with one ciphertext are linked",
    );
  }
  if (channel.nextIndex >= channel.confirmed + BigInt(LOOKAHEAD)) {
    throw new NotesError(
      `${channel.nextIndex - channel.confirmed} payments on this channel are past the last ` +
        `final one, and the recipient watches only ${LOOKAHEAD} ahead: wait until one is ` +
        "final, or retry a payment with its existing note",
    );
  }
  const index = channel.nextIndex;
  const { note, rho } = sealNote(channel.secret, index, value);
  channel.nextIndex += 1n;
  channel.ciphertextSent = channel.ciphertext.length > 0;
  return { note, rho, index, ciphertext: channel.ciphertext };
}

// ---- receiving ----

export type Leaf = { cm: bigint; epoch: bigint; index: bigint };

/** What one shield or settlement published; (block, tx, call) orders events on chain. */
export interface PoolEvent {
  block: bigint;
  tx: bigint; // the transaction's index in its block
  call: number; // which shield or settlement of that transaction
  notes: Uint8Array;
  leaves: Leaf[];
  spent: bigint[]; // nullifiers
}

type Kind = "self" | "direct" | "kem";

/** A secret this wallet watches; `number` is a direct secret's number, -1 otherwise. */
export type Incoming = { secret: Uint8Array; kind: Kind; nextIndex: bigint; number: bigint };

/** A note this wallet owns. The state file writes `kind` under the key "secret". */
export interface NoteRecord extends Leaf {
  value: bigint;
  rho: bigint;
  nullifier: bigint;
  spent: boolean;
  kind: Kind;
}

export type ScannerOptions = { gap?: number; lookahead?: number };

// The 48-byte notes of an event's body after any ciphertext, and their tags as Map keys.
const notesOf = (body: Uint8Array) =>
  Array.from({ length: body.length / NOTE_BYTES }, (_, i) =>
    body.subarray(i * NOTE_BYTES, (i + 1) * NOTE_BYTES),
  );
const tagOf = (note: Uint8Array) => toHex(note.subarray(0, TAG_BYTES));
const placeOf = (leaf: Leaf) => `${leaf.epoch},${leaf.index}`;

/**
 * Finds a wallet's notes and their spends in the pool's finalized events, from its seed. Each
 * epoch's leaves must arrive without gaps, so a node that left a payment's logs out stops the
 * scan instead of hiding the payment.
 */
export class Scanner {
  readonly keys: WalletKeys;
  readonly chainId: bigint;
  readonly pool: bigint;
  readonly incoming: Incoming[] = [];
  readonly notes = new Map<string, NoteRecord>(); // by placeOf, in the order found
  directHighest = -1n; // the highest direct number paid
  directIssued = -1n; // the highest direct number handed out
  scannedBlock = -1n;
  leafBlock = -1n; // the block of the last leaf seen
  readonly #gap: bigint;
  readonly #lookahead: bigint;
  readonly #tags = new Map<string, [Incoming, bigint]>(); // tag hex -> secret, note index
  readonly #tree = new Map<bigint, bigint>(); // epoch -> next leaf index
  readonly #nullifiers = new Map<bigint, string>(); // nullifier -> placeOf its note

  constructor(keys: WalletKeys, chainId: bigint, pool: bigint, options: ScannerOptions = {}) {
    this.keys = keys;
    this.chainId = chainId;
    this.pool = pool;
    this.#gap = BigInt(options.gap ?? GAP);
    this.#lookahead = BigInt(options.lookahead ?? LOOKAHEAD);
    this.#add(keys.selfSecret, "self");
    for (let n = 0n; n < this.#gap; n++) this.#add(keys.directSecret(n), "direct", 0n, n);
  }

  #add(secret: Uint8Array, kind: Kind, nextIndex = 0n, number = -1n): void {
    const incoming = { secret, kind, nextIndex, number };
    this.incoming.push(incoming);
    this.#watch(incoming);
  }

  // From index 0: a payment with an earlier index can land after a later one, including after
  // the state was saved and loaded again.
  #watch(incoming: Incoming): void {
    for (let index = 0n; index < incoming.nextIndex + this.#lookahead; index++) {
      this.#tags.set(tagOf(noteTag(incoming.secret, index)), [incoming, index]);
    }
  }

  /** Whether this event's leaves skip some that were never seen. */
  skipsLeaves(event: PoolEvent): boolean {
    const expected = new Map(this.#tree);
    for (const { epoch, index } of event.leaves) {
      if (index !== (expected.get(epoch) ?? 0n)) return true;
      expected.set(epoch, index + 1n);
    }
    return false;
  }

  /** Whether this event's leaves are already in the tree. */
  applied(event: PoolEvent): boolean {
    const first = event.leaves[0];
    return first !== undefined && first.index < (this.#tree.get(first.epoch) ?? 0n);
  }

  /**
   * Applies one event and returns the notes it paid to this wallet. inOrder=false applies a
   * call whose logs the node left out, rebuilt from receipts once a later leaf showed the gap.
   */
  scan(event: PoolEvent, inOrder = true): NoteRecord[] {
    if (inOrder && event.block < this.scannedBlock) {
      throw new NotesError("events must arrive in chain order");
    }
    for (const { epoch, index } of event.leaves) {
      const expected = this.#tree.get(epoch) ?? 0n;
      if (index !== expected) {
        throw new NotesError(
          `leaf ${index} of epoch ${epoch} arrived where ${expected} was expected; this node ` +
            "is missing pool logs, so notes may be hidden",
        );
      }
      this.#tree.set(epoch, index + 1n);
      this.leafBlock = maxBigint(this.leafBlock, event.block);
    }
    for (const nf of event.spent) {
      const place = this.#nullifiers.get(nf);
      if (place !== undefined) this.notes.get(place)!.spent = true;
    }
    let body = event.notes;
    if ([NOTE_BYTES, 2 * NOTE_BYTES].includes(body.length - KEM_CIPHERTEXT_BYTES)) {
      const secret = this.keys.decapsulate(body.subarray(0, KEM_CIPHERTEXT_BYTES));
      body = body.subarray(KEM_CIPHERTEXT_BYTES);
      // A foreign ciphertext decapsulates to a pseudorandom key, so a secret is adopted only if
      // a note carries a tag at an index a fresh channel would watch.
      const window = new Set<string>();
      for (let i = 0n; i < this.#lookahead; i++) window.add(tagOf(noteTag(secret, i)));
      const known = this.incoming.some((i) => crypto.timingSafeEqual(i.secret, secret));
      if (!known && notesOf(body).some((note) => window.has(tagOf(note)))) this.#add(secret, "kem");
    } else if (![0, NOTE_BYTES, 2 * NOTE_BYTES].includes(body.length)) {
      throw new NotesError(`an event published ${body.length} note bytes`);
    }
    const found: NoteRecord[] = [];
    for (const note of notesOf(body)) {
      const match = this.#tags.get(tagOf(note));
      const record = match && this.#take(match, note, event.leaves);
      if (record) found.push(record);
    }
    if (inOrder) this.scannedBlock = maxBigint(this.scannedBlock, event.block);
    return found;
  }

  #take([incoming, noteIndex]: [Incoming, bigint], note: Uint8Array, leaves: Leaf[]) {
    const value = openNote(incoming.secret, noteIndex, note);
    if (value === null) return null;
    const rho = noteRho(incoming.secret, noteIndex);
    const cm = protocol.commitment(this.keys.spendKey, rho, value);
    const leaf = leaves.find((l) => l.cm === cm);
    // A note naming no output of its own event pays nobody, and none is counted twice.
    if (leaf === undefined || this.notes.has(placeOf(leaf))) return null;
    const { epoch, index } = leaf;
    const domain = protocol.domainScalar(this.chainId, this.pool, epoch);
    const nullifier = protocol.nullifier(domain, this.keys.spendKey, cm, index);
    const { kind } = incoming;
    const record = this.#record({ cm, epoch, index, value, rho, nullifier, spent: false, kind });
    if (noteIndex + 1n > incoming.nextIndex) {
      incoming.nextIndex = noteIndex + 1n;
      this.#watch(incoming);
    }
    if (kind === "direct" && incoming.number > this.directHighest) {
      for (let n = this.directHighest + this.#gap + 1n; n <= incoming.number + this.#gap; n++) {
        this.#add(this.keys.directSecret(n), "direct", 0n, n);
      }
      this.directHighest = incoming.number;
    }
    return record;
  }

  #record(record: NoteRecord): NoteRecord {
    this.notes.set(placeOf(record), record);
    this.#nullifiers.set(record.nullifier, placeOf(record));
    return record;
  }

  /**
   * The next direct secret's number, recorded so that it goes to one sender. A scan from the
   * seed watches numbers up to GAP past the highest one paid, so none is issued beyond that.
   */
  issueDirect(): bigint {
    const number = maxBigint(this.directIssued, this.directHighest) + 1n;
    if (number > this.directHighest + this.#gap) {
      throw new NotesError(
        `${this.#gap} direct secrets are waiting for a first payment, and a scan from the seed ` +
          "would not look further: wait until one of them is paid",
      );
    }
    this.directIssued = number;
    return number;
  }

  unspent(): NoteRecord[] {
    return [...this.notes.values()].filter((note) => !note.spent);
  }

  /** The state file's contents, format version 2. */
  toJson() {
    const tree = [...this.#tree].sort(([a], [b]) => compareBigint(a, b));
    const notes = [...this.notes.values()].sort((a, b) =>
      compareKeys([a.epoch, a.index], [b.epoch, b.index]),
    );
    return {
      version: STATE_VERSION,
      chain_id: this.chainId,
      pool: hexPadded(this.pool, 40),
      account: this.keys.account,
      owner_pk: hex32(this.keys.ownerPk),
      scanned_block: this.scannedBlock,
      leaf_block: this.leafBlock,
      direct_highest: this.directHighest,
      direct_issued: this.directIssued,
      tree: Object.fromEntries(tree.map(([epoch, next]) => [String(epoch), next])),
      incoming: this.incoming.map(({ secret, kind, nextIndex, number }) => {
        return { secret: toHex(secret), kind, next_index: nextIndex, number };
      }),
      notes: notes.map((n) => ({
        cm: hex32(n.cm),
        epoch: n.epoch,
        index: n.index,
        value: n.value,
        rho: hex32(n.rho),
        nullifier: hex32(n.nullifier),
        spent: n.spent,
        secret: n.kind,
      })),
    };
  }

  /** A scanner restored from its state file, refused unless it is this wallet's and account's. */
  static fromJson(keys: WalletKeys, data: unknown, options: ScannerOptions = {}): Scanner {
    const state = isObject(data) ? data : {};
    const { account } = state;
    if (
      state.version !== STATE_VERSION ||
      (Number.isSafeInteger(account) ? BigInt(account as number) : account) !== keys.account ||
      state.owner_pk !== hex32(keys.ownerPk)
    ) {
      throw new NotesError("the state file belongs to another wallet, account or format");
    }
    const chainId = parseDec(state.chain_id, "the state's chain_id");
    const pool = parseAddress(state.pool, "the state's pool");
    const scanner = new Scanner(keys, chainId, pool, options);
    // The file lists every watched secret, the self and direct ones included.
    scanner.incoming.length = 0;
    scanner.#tags.clear();
    for (const item of asList(state.incoming, "incoming")) {
      const i = asObject(item, "an incoming secret");
      // 32 bytes, as scan() compares secrets with timingSafeEqual, which throws on other lengths.
      const secret = fromHex(i.secret, "an incoming secret", SECRET_BYTES);
      const nextIndex = parseDec(i.next_index, "an incoming next_index");
      scanner.#add(secret, kindOf(i.kind), nextIndex, integer(i.number, "number"));
    }
    scanner.directHighest = integer(state.direct_highest, "direct_highest");
    scanner.directIssued = integer(state.direct_issued, "direct_issued");
    scanner.leafBlock = integer(state.leaf_block, "leaf_block");
    for (const [epoch, next] of Object.entries(asObject(state.tree, "tree"))) {
      scanner.#tree.set(parseDec(epoch, "a tree epoch"), parseDec(next, "a tree size"));
    }
    for (const item of asList(state.notes, "notes")) {
      const r = asObject(item, "a note");
      const field = (key: string) => toBigint(fromHex(r[key], `a note's ${key}`, 32));
      const uint = (key: string) => parseDec(r[key], `a note's ${key}`);
      const spent = bool(r.spent, "a note's spent");
      const [cm, rho, nullifier] = ["cm", "rho", "nullifier"].map(field);
      const [epoch, index, value] = ["epoch", "index", "value"].map(uint);
      scanner.#record({ cm, epoch, index, value, rho, nullifier, spent, kind: kindOf(r.secret) });
    }
    scanner.scannedBlock = integer(state.scanned_block, "scanned_block");
    return scanner;
  }
}

function kindOf(value: unknown): Kind {
  if (value === "self" || value === "direct" || value === "kem") return value;
  throw new NotesError(`the state file names a ${String(value)} secret`);
}

/** A state file's signed integer, where -1 means "none yet". */
function integer(value: unknown, what: string): bigint {
  if (typeof value === "bigint" || Number.isSafeInteger(value)) return BigInt(value as bigint);
  throw new NotesError(`the state file's ${what} is not an integer`);
}

function bool(value: unknown, what: string): boolean {
  if (typeof value === "boolean") return value;
  throw new NotesError(`${what} is not true or false`);
}

/** Orders sort keys made of bigints, such as (epoch, index) or (block, tx, call). */
function compareKeys(a: readonly bigint[], b: readonly bigint[]): number {
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return compareBigint(a[i], b[i]);
  return 0;
}

// ---- chain ----

/** The bytes of a Notes(bytes) log's ABI-encoded data. */
export function decodeNotesData(data: unknown): Uint8Array {
  const raw = fromHex(data, "Notes log data");
  const offset = toBigint(raw.subarray(0, 32));
  const length = Number(toBigint(raw.subarray(32, 64)));
  const sizes = [...SPEND_NOTES_BYTES, ...SHIELD_NOTE_BYTES];
  if (offset !== 32n || !sizes.includes(length) || raw.length < 64 + length) {
    throw new NotesError("malformed Notes log");
  }
  return raw.slice(64, 64 + length);
}

/**
 * Groups the pool's logs into one PoolEvent per shield or settlement, in chain order. A
 * transaction may shield or settle several times, and each call emits Notes as its last pool log
 * and makes no external call before it, so the transaction's logs split at its Notes logs. Pass
 * only the pool's logs: other contracts can emit its topics.
 */
export function eventsFromLogs(logs: readonly unknown[]): PoolEvent[] {
  const sorted = logs
    .map((value) => {
      const log = asObject(value, "a log");
      const fields = ["blockNumber", "transactionIndex", "logIndex"];
      return { log, at: fields.map((field) => parseHex(log[field], `a log's ${field}`)) };
    })
    .sort((a, b) => compareKeys(a.at, b.at));
  const events: PoolEvent[] = [];
  const open = new Map<string, PoolEvent>();
  const calls = new Map<string, number>();
  for (const { log, at } of sorted) {
    const [block, tx] = at;
    const key = `${block},${tx}`;
    const call = calls.get(key) ?? 0;
    const event = open.get(key) ?? { block, tx, call, notes: EMPTY, leaves: [], spent: [] };
    open.set(key, event);
    const topics = asList(log.topics, "a log's topics");
    if (typeof topics[0] !== "string") throw new NotesError("a pool log has no topic");
    const topic = topics[0].toLowerCase();
    if (topic === LEAF_APPENDED) {
      const leaf = protocol.parseLeafAppended(log);
      if (leaf === null) throw new NotesError("malformed LeafAppended log");
      event.leaves.push({ cm: leaf.cm, epoch: leaf.epoch, index: leaf.index });
    } else if (topic === NOTE_SPENT) {
      event.spent.push(parseHex(topics[1], "a NoteSpent nullifier"));
    } else if (topic === NOTES) {
      event.notes = decodeNotesData(log.data);
      // A shield emits one leaf, then its note; a settlement two nullifiers, at most two
      // leaves, then its notes. Any other shape means the node left logs out.
      const complete = SHIELD_NOTE_BYTES.includes(event.notes.length)
        ? event.leaves.length === 1 && event.spent.length === 0
        : event.spent.length === 2 && event.leaves.length <= 2;
      if (!complete) {
        throw new NotesError(
          `a pool call in block ${block} shows ${event.leaves.length} leaves and ` +
            `${event.spent.length} nullifiers for ${event.notes.length} note bytes; this node is ` +
            "missing pool logs",
        );
      }
      events.push(event);
      open.delete(key);
      calls.set(key, call + 1);
    }
  }
  // Calls open in chain order, so the first one left open is the earliest.
  const [unfinished] = open.values();
  if (unfinished !== undefined) {
    throw new NotesError(
      `a pool call in block ${unfinished.block} has no Notes log; this node is missing pool logs`,
    );
  }
  return events;
}

type Rpc = Pick<RpcChain, "call">;

/** The pool's LeafAppended, NoteSpent and Notes logs in [from, to]. */
export async function fetchLogs(chain: Rpc, pool: bigint, from: bigint, to: bigint, chunk = 2000) {
  if (!(Number.isSafeInteger(chunk) && chunk >= 1)) {
    throw new NotesError("a chunk is at least one block");
  }
  const logs: unknown[] = [];
  for (let start = from, step = BigInt(chunk); start <= to; start += step) {
    const end = start + step - 1n < to ? start + step - 1n : to;
    const range = { fromBlock: hexPadded(start, 1), toBlock: hexPadded(end, 1) };
    const filter = { address: hexPadded(pool, 40), topics: [POOL_TOPICS], ...range };
    logs.push(...asList(await chain.call("eth_getLogs", [filter]), "eth_getLogs's result"));
  }
  return logs;
}

/**
 * The same logs, read from block receipts. ethrex 247e2dd2 leaves out of eth_getLogs every log
 * of a frame transaction in which any frame failed, although the frames that succeeded,
 * settlement included, keep their effects.
 */
export async function receiptLogs(chain: Rpc, pool: bigint, from: bigint, to: bigint) {
  const logs: unknown[] = [];
  for (let block = from; block <= to; block++) {
    const receipts = await chain.call("eth_getBlockReceipts", [hexPadded(block, 1)]);
    for (const value of asList(receipts ?? [], "eth_getBlockReceipts's result")) {
      const receipt = asObject(value, "a receipt");
      // With frame receipts, each frame that succeeded counts, whatever the transaction's status.
      const frames = receipt.frameReceipts ?? null;
      const mine = (frames === null ? [receipt] : asList(frames, "frameReceipts"))
        .map((part) => asObject(part, "a receipt or frame"))
        .filter((part) => parseHex(part.status, "a receipt's status") === 1n)
        .flatMap((part) => asList(part.logs, "a receipt's logs"))
        .map((log) => asObject(log, "a log"))
        // Only the pool's logs are kept, before any is parsed: another contract can emit a log
        // with a pool topic, and its malformed fields must not stop the scan.
        .filter(
          ({ address, topics }) =>
            parseAddress(address, "a log's address") === pool &&
            Array.isArray(topics) &&
            typeof topics[0] === "string" &&
            POOL_TOPICS.includes(topics[0].toLowerCase()),
        );
      mine.forEach(({ topics, data }, position) =>
        logs.push({
          blockNumber: hexPadded(block, 1),
          transactionIndex: receipt.transactionIndex,
          logIndex: hexPadded(BigInt(position), 1),
          topics,
          data,
        }),
      );
    }
  }
  return logs;
}

// ---- commands (src/cli/notes.ts parses the arguments and prints what these return) ----

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
 * `notes scan`: scans the pool's finalized events from where the state stopped, saves the state,
 * and returns the unspent notes. An event whose leaves skip some never seen first brings in the
 * calls the node's eth_getLogs left out, rebuilt from block receipts. It never asks about single
 * nullifiers, which would link notes to their spends.
 */
export async function scanCommand(options: CommandOptions): Promise<string> {
  return withState("scan", options, async (config, scanner, save) => {
    const { deploymentBlock = 0 } = config;
    const deployment = parseDec(deploymentBlock, "the config's deploymentBlock");
    const url = options.rpc || config.rpc;
    if (typeof url !== "string") throw new NotesError("the config names no rpc URL; pass --rpc");
    const chain = new RpcChain(url);
    if ((await chain.chainId()) !== scanner.chainId) {
      throw new NotesError(`the RPC is not on chain ${scanner.chainId}`);
    }
    const start = maxBigint(scanner.scannedBlock + 1n, deployment);
    const head = await chain.finalizedBlock();
    const logs = await fetchLogs(chain, scanner.pool, start, head, options.chunk);
    const at = (e: PoolEvent) => [e.block, e.tx, BigInt(e.call)];
    for (const event of eventsFromLogs(logs)) {
      if (scanner.skipsLeaves(event)) {
        // The missing calls came after the last leaf seen (possibly in its block) and before
        // this event. Apply each one not applied yet, whether or not this node's eth_getLogs
        // shows it, since an earlier scan may have used a node that left it out. A call without
        // leaves changes nothing when applied twice.
        const from = maxBigint(scanner.leafBlock, deployment);
        const missed = eventsFromLogs(await receiptLogs(chain, scanner.pool, from, event.block));
        for (const call of missed) {
          if (compareKeys(at(call), at(event)) < 0 && !scanner.applied(call)) {
            scanner.scan(call, false);
          }
        }
      }
      scanner.scan(event);
    }
    scanner.scannedBlock = maxBigint(scanner.scannedBlock, head);
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
