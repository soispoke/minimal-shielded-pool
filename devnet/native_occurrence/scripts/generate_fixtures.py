"""Disposable real-proof vectors for the occurrence-nullifier deployment.

The native harness executes every deployment, deposit, publication and spend.
Only the explicitly labelled large-tree boundary cases seed reachable storage.
"""
from pathlib import Path
import copy
from functools import lru_cache
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent.parent
REPO = HERE.parent.parent
sys.path[:0] = [str(REPO / "wallet"), str(REPO / "devnet")]
from eth_hash.auto import keccak
from eth_keys import keys
import gen_smoke as smoke
import wallet as w
import pool_frametx as builder
from dispatcher import initcode
from frametx import Frame, FrameSig, FrameTx, rlp_bytes, rlp_int, rlp_list
from gas_profile import (RECENT_ROOT_FRAME_GAS, VERIFY_FRAME_GAS,
    VERIFY_FRAME_STATE_GAS, SETTLE_FRAME_GAS, SETTLE_FRAME_STATE_GAS,
    CLAIM_FRAME_GAS, CLAIM_FRAME_STATE_GAS)

OUT = HERE / "fixtures"
OUT.mkdir(exist_ok=True)
smoke.WORK = HERE / "proof-work"
smoke.WORK.mkdir(exist_ok=True)
CHAIN, SLOT, ETH = 8141, 100, 10**18
FEE = ETH // 20
KEY = keys.PrivateKey((0xD3E10).to_bytes(32, "big"))
DEPLOYER = int.from_bytes(KEY.public_key.to_canonical_address(), "big")
EOA, REJECTOR = 0xCAFEBABE, 0xDEAD

def word(x): return int(x).to_bytes(32, "big")
def addr(x): return f"0x{int(x):040x}"
def create_address(n):
    return int.from_bytes(keccak(rlp_list([rlp_bytes(DEPLOYER.to_bytes(20, "big")), rlp_int(n)]))[-20:], "big")
NAMES = ["poseidon3", "poseidon4", "verifier", "logic", "pool"]
A = {name: create_address(i) for i, name in enumerate(NAMES)}
POOL = A["pool"]

def calldata(signature, *args):
    return bytes.fromhex(subprocess.check_output(["cast", "calldata", signature, *map(str, args)], text=True).strip().removeprefix("0x"))

def ordinary(nonce, to, data, value=0):
    fields = [rlp_int(CHAIN), rlp_int(nonce), rlp_int(1), rlp_int(2), rlp_int(60_000_000),
        rlp_bytes(b"" if to is None else int(to).to_bytes(20, "big")), rlp_int(value), rlp_bytes(data), rlp_list([])]
    sig = KEY.sign_msg_hash(keccak(b"\x02" + rlp_list(fields)))
    return b"\x02" + rlp_list(fields + [rlp_int(sig.v), rlp_int(sig.r), rlp_int(sig.s)])

def save(name, raw, **expect):
    (OUT / f"{name}.hex").write_text("0x" + raw.hex() + "\n")
    return {"raw": f"{name}.hex", **expect}

def artifact(name, small=False):
    path = REPO / "contracts" / ("out-libsmall" if small else "out") / f"{name}.sol" / f"{name}.json"
    return bytes.fromhex(json.loads(path.read_text())["bytecode"]["object"].removeprefix("0x"))

constructors = [artifact("PoseidonT3", True), artifact("PoseidonT4", True), artifact("Groth16Verifier"),
    artifact("ShieldedPoolLogic") + word(A["poseidon3"]) + word(A["poseidon4"]), initcode(A["logic"], A["verifier"])]
setup = [save(f"deploy-{name}", ordinary(i, None, code)) for i, (name, code) in enumerate(zip(NAMES, constructors))]
w.set_seed(20260921)

def note(value):
    sk, rho = w.new_note()
    return {"sk": sk, "rho": rho, "value": value, "inner": w.inner(sk, rho), "cm": w.commitment(sk, rho, value)}

NA, NB, NC, ND = note(ETH), note(95 * ETH // 100), note(70 * ETH // 100), note(60 * ETH // 100)

def tree_of(*notes):
    tree = w.Tree()
    for n in notes: tree.append(n["cm"])
    return tree

BASE = tree_of(NA, NB)
def deposit(name, n, nonce, tree, slot=SLOT):
    return save(name, ordinary(nonce, POOL, calldata("shield(bytes32)", "0x" + word(n["inner"]).hex()), n["value"]),
        slot_number=slot, storage={addr(POOL): {"21": str(len(tree.leaves)), "22": str(tree.root())}},
        balance_delta_before_gas={addr(POOL): str(n["value"])})
def publish(name, nonce, epoch=0, slot=SLOT):
    return save(name, ordinary(nonce, POOL, calldata("publishEpochRoot(uint64)", epoch)), slot_number=slot)

setup += [deposit("deposit-a", NA, 5, tree_of(NA)), deposit("deposit-b", NB, 6, BASE), publish("publish-initial", 7)]
NEXT = 8
entries = {}
KEY_HASH = hashlib.sha256((REPO / "build/spend_final.zkey").read_bytes()).hexdigest()
WASM_HASH = hashlib.sha256((REPO / "build/spend_js/spend.wasm").read_bytes()).hexdigest()

def prove(name, tree, n, index, outputs=None, recipient=EOA, epoch=0, root_slot=SLOT, alias=None):
    outputs = w.sink_outputs() if outputs is None else outputs
    public = n["value"] - FEE - sum(v for _, v in outputs)
    assert public >= 0
    if not public: recipient = 0
    inputs = [{key: n[key] for key in ("sk", "rho", "value")} | {"idx": index}, w.dummy_input()]
    private_key, authorizer = w.new_authorizer()
    domain = w.domain_scalar(CHAIN, addr(POOL), epoch)
    witness = w.build_witness(tree, inputs, outputs, domain, authorizer=authorizer, public_amount=public, fee=FEE, recipient=addr(recipient))
    if alias is not None:
        # An honest witness proved against alpha over an aliased word: the
        # statement value plus p. gamma reduces the word modulo p, so only the
        # pool's range checks can tell the two encodings apart.
        words = w.statement(*w.input_nullifiers(domain, inputs), *w.output_commitments(outputs),
                            tree.root(), domain, public, FEE, recipient, authorizer)
        words[alias] += w.P
        witness["alpha"] = str(int.from_bytes(keccak(b"".join(x.to_bytes(32, "big") for x in words)), "big") % w.P)
    cache = OUT / f"{name}-proof.json"
    digest = keccak(json.dumps(witness, sort_keys=True).encode() + KEY_HASH.encode() + WASM_HASH.encode()).hex()
    if cache.exists() and json.loads(cache.read_text()).get("witness_hash") == digest:
        record = json.loads(cache.read_text())
        publics, proof = record["publics"], record["proof"]
    else:
        print("proving", name, flush=True)
        publics, proof = smoke.prove(witness, name)
        cache.write_text(json.dumps({"witness_hash": digest, "publics": publics, "proof": proof}, indent=2) + "\n")
    if alias is not None:
        honest = smoke.spend_entry(tree, domain, inputs, outputs, epoch, public, FEE, recipient, authorizer,
                                   private_key, prove_publics_honest(inputs, outputs, tree, domain, public, recipient,
                                                                     authorizer, publics), proof, root_slot=str(root_slot))
        entries[name] = honest
        return honest
    entry = smoke.spend_entry(tree, domain, inputs, outputs, epoch, public, FEE, recipient, authorizer, private_key, publics, proof, root_slot=str(root_slot))
    entries[name] = entry
    return entry

def prove_publics_honest(inputs, outputs, tree, domain, public, recipient, authorizer, publics):
    """The (beta, gamma, alpha) an honest statement would have, so spend_entry's
    wallet checks pass for an entry whose proof actually binds an aliased alpha."""
    stmt = w.statement(*w.input_nullifiers(domain, inputs), *w.output_commitments(outputs),
                       tree.root(), domain, public, FEE, recipient, authorizer)
    beta = publics[0]
    alpha = w.compression_alpha(stmt)
    return [beta, w.fingerprint((alpha + beta) % w.P, stmt), alpha]

def frame_tx(entry, settle_gas=SETTLE_FRAME_GAS, mutate=None, max_fee=2):
    source = keccak(POOL.to_bytes(20, "big") + word(int(entry["epoch"])))
    recent = source + int(entry["root_slot"]).to_bytes(8, "big") + word(int(entry["root"], 16))
    settle = builder.cast_calldata(f"settle({builder.SPEND_TUPLE})", builder.spend_args(entry))
    frames = [Frame(1, 0, 0x8272, RECENT_ROOT_FRAME_GAS, 0, recent),
        Frame(1, 3, POOL, VERIFY_FRAME_GAS, 0, builder.proof_bytes(entry), VERIFY_FRAME_STATE_GAS),
        Frame(2, 0, POOL, settle_gas, 0, settle, SETTLE_FRAME_STATE_GAS)]
    if int(entry["public_amount"]):
        frames.append(Frame(0, 0, POOL, CLAIM_FRAME_GAS, 0, keccak(b"claimWithdrawal(address)")[:4] + word(int(entry["recipient"], 16)), CLAIM_FRAME_STATE_GAS))
    if mutate is not None: mutate(frames)
    tx = FrameTx(CHAIN, sorted([int(entry["nf1"], 16), int(entry["nf2"], 16)]), 0, POOL, frames,
        [FrameSig(1, int(entry["authorizer"], 16), b"", b"")], 1, max_fee)
    sig = keys.PrivateKey(bytes.fromhex(entry["authorizer_private_key"].removeprefix("0x"))).sign_msg_hash(tx.sig_hash())
    tx.signatures[0].signature = bytes([sig.v]) + word(sig.r) + word(sig.s)
    return tx

def signed(entry, settle_gas=SETTLE_FRAME_GAS, mutate=None, max_fee=2):
    return frame_tx(entry, settle_gas, mutate, max_fee).raw()

def mapping(key, slot): return "0x" + keccak(word(key) + word(slot)).hex()
def key_slots(entry, value):
    return {"0x" + keccak(word(POOL) + word(int(entry[k], 16))).hex(): str(value) for k in ("nf1", "nf2")}
def spend(name, entry, slot=101, rejected=False, failed_claim=False, paid=None, expected_tree=None,
          mutate=None, statuses=None, error=None, max_fee=2):
    storage = {addr(0x8250): key_slots(entry, 0 if rejected else 1)}
    credit = int(entry["public_amount"]) if failed_claim else 0
    storage[addr(POOL)] = {mapping(int(entry["recipient"], 16), 23): str(credit)}
    if expected_tree is not None:
        storage[addr(POOL)].update({"21": str(len(expected_tree.leaves)), "22": str(expected_tree.root())})
    expect = {"slot_number": slot, "storage": storage}
    if rejected:
        expect["accepted"] = False
    else:
        expect.update(statuses=([1, 1, 1, 0] if failed_claim else [1] * (4 if int(entry["public_amount"]) else 3)), payer=addr(POOL),
            balance_delta_before_gas={addr(POOL): "0" if failed_claim else str(-int(entry["public_amount"]))})
        if paid is not None: expect["balances"] = {addr(EOA): str(paid)}
        if statuses is not None: expect["statuses"] = statuses
    if error is not None: expect["error_contains"] = error
    return save(name, signed(entry, mutate=mutate, max_fee=max_fee), **expect)

cases = []
def case(name, *steps): cases.append({"name": name, "transactions": list(steps)})

# Two identical deposits are independently funded and independently withdrawn.
dup_tree = tree_of(NA, NB, NA)
dup0 = prove("deposit-copy-first", dup_tree, NA, 0, root_slot=101)
dup2 = prove("deposit-copy-second", dup_tree, NA, 2, root_slot=101)
assert dup0["nf1"] != dup2["nf1"]
case("identical-funded-deposits-both-withdrawn",
    deposit("deposit-a-again", NA, NEXT, dup_tree, 101), publish("publish-duplicates", NEXT+1, slot=101),
    spend("withdraw-first-deposit", dup0, 102, paid=ETH-FEE),
    spend("withdraw-second-deposit", dup2, 103, paid=2*(ETH-FEE)))

# Private settlement may create a commitment that already exists; both survive.
duplicate = prove("private-duplicate", BASE, NA, 0, outputs=[(NB["inner"], NB["value"]), w.sink_outputs()[1]])
private_tree = tree_of(NA, NB, NB)
b1 = prove("private-copy-original", private_tree, NB, 1, root_slot=102)
b2 = prove("private-copy-new", private_tree, NB, 2, root_slot=102)
assert b1["nf1"] != b2["nf1"]
case("private-duplicate-output-both-withdrawn", spend("create-private-copy", duplicate, expected_tree=private_tree),
    publish("publish-private-copy", NEXT, slot=102), spend("withdraw-original-private", b1, 103, paid=NB["value"]-FEE),
    spend("withdraw-created-private", b2, 104, paid=2*(NB["value"]-FEE)))

# Different roots/slots do not turn the same occurrence into a new spend.
initial = prove("initial-a-withdrawal", BASE, NA, 0)
later_tree = tree_of(NA, NB, NC)
replay = prove("same-occurrence-later-root", later_tree, NA, 0, root_slot=102)
assert initial["nf1"] == replay["nf1"]
replay_step = spend("replay-later-root", replay, 103, rejected=True)
replay_step["storage"][addr(0x8250)][next(iter(key_slots(replay, 0)))] = "1"
case("same-occurrence-replay-later-root-and-slot", spend("first-a-withdrawal", initial, paid=ETH-FEE),
    deposit("append-after-spend", NC, NEXT, later_tree, 102), publish("publish-after-spend", NEXT+1, slot=102), replay_step)

bad_domain = copy.deepcopy(initial)
bad_domain["domain"] = "0x" + word(w.domain_scalar(CHAIN, addr(POOL), 1)).hex()
case("mutated-domain-rejected-before-approval", spend("mutated-domain", bad_domain, rejected=True))
bad_epoch = copy.deepcopy(initial)
bad_epoch["epoch"] = "1"
case("mutated-epoch-rejected-before-approval", spend("mutated-epoch", bad_epoch, rejected=True))

# Reorg: restore the whole EVM database (keys, roots, balances and nonces),
# reorder two real deposits, reject the old root, then rebuild the proof.
branch_a = tree_of(NA, NB, NC, ND)
branch_b = tree_of(NA, NB, ND, NC)
old = prove("reorg-old-branch", branch_a, NC, 2, root_slot=101)
new = prove("reorg-new-branch", branch_b, NC, 3, root_slot=101)
assert old["nf1"] != new["nf1"]
old_rebound = copy.deepcopy(old)
old_rebound["root"] = new["root"]
case("reorg-reordered-deposits-rebuild-proof", {"checkpoint": "before-branches"},
    deposit("branch-a-c", NC, NEXT, tree_of(NA, NB, NC), 101), deposit("branch-a-d", ND, NEXT+1, branch_a, 101),
    publish("publish-branch-a", NEXT+2, slot=101), spend("spend-on-old-branch", old, 102, paid=NC["value"]-FEE),
    {"restore": "before-branches"}, deposit("branch-b-d", ND, NEXT, tree_of(NA, NB, ND), 101),
    deposit("branch-b-c", NC, NEXT+1, branch_b, 101), publish("publish-branch-b", NEXT+2, slot=101),
    spend("old-branch-proof-rejected", old, 102, rejected=True),
    spend("old-branch-proof-current-root-rejected", old_rebound, 102, rejected=True),
    spend("rebuilt-branch-proof", new, 102, paid=NC["value"]-FEE))

reject = prove("rejecting-recipient", BASE, NA, 0, recipient=REJECTOR)
case("failed-recipient-preserves-withdrawal-credit", spend("rejecting-recipient", reject, failed_claim=True))

class RepeatedTree:
    """Compact tree for a reachable prefix of identical funded deposits."""
    depth = w.DEPTH
    def __init__(self, cm, count, extras=()):
        self.cm, self.count = cm, count
        self.extras = extras
        self.uniform, self.zeros = [cm], [0]
        for _ in range(self.depth):
            self.uniform.append(w.p2(self.uniform[-1], self.uniform[-1]))
            self.zeros.append(w.p2(self.zeros[-1], self.zeros[-1]))
    @lru_cache(None)
    def subtree(self, start, level):
        if start >= self.count + len(self.extras): return self.zeros[level]
        if start + (1 << level) <= self.count: return self.uniform[level]
        if level == 0: return self.extras[start - self.count]
        return w.p2(self.subtree(start, level-1), self.subtree(start+(1 << (level-1)), level-1))
    def root(self): return self.subtree(0, self.depth)
    def auth_path(self, index):
        return ([self.subtree(((index >> level) ^ 1) << level, level) for level in range(self.depth)],
            [(index >> level) & 1 for level in range(self.depth)])

OUT1, OUT2 = note(60 * ETH // 100), note(35 * ETH // 100)
outputs = [(OUT1["inner"], OUT1["value"]), (OUT2["inner"], OUT2["value"])]
gas_cases = [("long-carry", (1 << 19)-1, outputs),
    ("long-carry-even", (1 << 19)-2, outputs),
    ("long-carry-new-credit", (1 << 19)-1, [(OUT1["inner"], OUT1["value"]), (OUT2["inner"], 30*ETH//100)]),
    ("long-carry-retained-credit", (1 << 19)-1, [(OUT1["inner"], OUT1["value"]), (OUT2["inner"], 30*ETH//100)]),
    ("long-carry-one-output-new-credit", (1 << 19)-1, [outputs[0], w.sink_outputs()[1]]),
    ("rollover", (1 << 20)-1, outputs),
    ("rollover-new-credit", (1 << 20)-1, [(OUT1["inner"], OUT1["value"]), (OUT2["inner"], 30*ETH//100)]),
    ("rollover-retained-credit", (1 << 20)-1, [(OUT1["inner"], OUT1["value"]), (OUT2["inner"], 30*ETH//100)]),
    ("full-tree-rollover", 1 << 20, outputs)]
for label, count, boundary_outputs in gas_cases:
    large = RepeatedTree(NA["cm"], count)
    retained = "retained-credit" in label
    entry = prove(label, large, NA, 0, outputs=boundary_outputs, root_slot=101, recipient=REJECTOR if retained else EOA)
    seed = {str(level): str(large.uniform[level] if count >= (1 << level) else 0) for level in range(w.DEPTH+1)}
    seed.update({"21": str(count), "22": str(large.root())})
    post = spend("settle-" + label, entry, 102, failed_claim=retained)
    added = [cm for cm, (_, value) in zip(w.output_commitments(boundary_outputs), boundary_outputs) if value]
    if count + len(added) > (1 << 20):
        next_tree = w.Tree()
        for cm in added: next_tree.append(cm)
        post["storage"][addr(POOL)].update({"21": str(len(added)), "22": str(next_tree.root()), "24": "1", mapping(0,25): str(large.root())})
    else:
        post["storage"][addr(POOL)].update({"21": str(count+len(added)), "22": str(RepeatedTree(NA["cm"], count, added).root()), "24": "0"})
    case("synthetic-reachable-"+label, {"synthetic_storage": {addr(POOL): seed}, "synthetic_balances": {addr(POOL): str(count*ETH)}},
        publish("publish-"+label, NEXT, slot=101), post)
    if label == "rollover":
        epoch_output = prove("rolled-epoch-output", next_tree, OUT1, 0, epoch=1, root_slot=103)
        cases[-1]["transactions"] += [publish("publish-rolled-epoch", NEXT+1, epoch=1, slot=103),
            spend("withdraw-rolled-epoch-output", epoch_output, 104, paid=OUT1["value"]-FEE)]

# Reproduce the former cap with the sole dispatcher literal changed back.
# It is an expected failing settlement, not a relaxed assertion for the fix.
current_limit = b"\x62" + SETTLE_FRAME_GAS.to_bytes(3, "big")
old_limit = b"\x62" + (1_400_000).to_bytes(3, "big")
assert constructors[-1].count(current_limit) == 1
old_setup = copy.deepcopy(setup)
old_setup[4] = save("deploy-pool-old-limit", ordinary(4, None, constructors[-1].replace(current_limit, old_limit)))
old_entry = entries["long-carry"]
old_boundary = RepeatedTree(NA["cm"], (1 << 19)-1)
old_seed = {str(level): str(old_boundary.uniform[level] if old_boundary.count >= (1 << level) else 0) for level in range(w.DEPTH+1)}
old_seed.update({"21": str(old_boundary.count), "22": str(old_boundary.root())})
case("old-1_4m-limit-consumes-keys-before-settlement-failure",
    {"synthetic_storage": {addr(POOL): old_seed}, "synthetic_balances": {addr(POOL): str(old_boundary.count*ETH)}},
    publish("publish-old-limit", NEXT, slot=101),
    save("old-limit-settlement-failure", signed(old_entry, 1_400_000), slot_number=102,
        statuses=[1,1,0], payer=addr(POOL), balance_delta_before_gas={addr(POOL): "0"},
        storage={addr(0x8250): key_slots(old_entry, 1), addr(POOL): {"21": str(old_boundary.count), "22": str(old_boundary.root())}}))
cases[-1]["setup"] = old_setup

# An input from a closed epoch can create the first outputs in a fresh epoch.
# This exposes four fresh storage writes when the recipient leaves credit.
fresh_entry = prove("fresh-epoch-old-input", BASE, NA, 0, outputs=[(OUT1["inner"], OUT1["value"]), (OUT2["inner"], 30*ETH//100)], root_slot=101, recipient=REJECTOR)
fresh_seed = {str(level): "0" for level in range(w.DEPTH+1)}
fresh_seed.update({"21": "0", "22": str(w.Tree().root()), "24": "1", mapping(0,25): str(BASE.root())})
fresh_post = spend("fresh-epoch-retained-credit", fresh_entry, 102, failed_claim=True)
fresh_tree = w.Tree()
for cm in (int(fresh_entry["out_cm1"],16), int(fresh_entry["out_cm2"],16)): fresh_tree.append(cm)
fresh_post["storage"][addr(POOL)].update({"21": "2", "22": str(fresh_tree.root()), "24": "1"})
case("synthetic-storage-upper-bound-empty-epoch-and-credit", {"synthetic_storage": {addr(POOL): fresh_seed}},
    publish("publish-closed-epoch", NEXT, slot=101), fresh_post)

# Conservative five-slot state-gas bound: zero frontier hashes are injected.
# This does not claim that such a full-tree frontier was produced by deposits.
zero_frontier = {str(level): "0" for level in range(w.DEPTH+1)}
zero_frontier.update({"21": str(1 << w.DEPTH), "22": str(BASE.root())})
zero_post = copy.deepcopy(fresh_post)
zero_post["storage"][addr(POOL)][mapping(0,25)] = str(BASE.root())
case("synthetic-storage-upper-bound-five-new-slots", {"synthetic_storage": {addr(POOL): zero_frontier}},
    publish("publish-zero-frontier", NEXT, slot=101), zero_post)

# Same tree contents at a different authenticated epoch require a new proof
# and a different nullifier, even when the occurrence index is identical.
epoch1 = prove("epoch-one-a", BASE, NA, 0, epoch=1, root_slot=101)
rebound = copy.deepcopy(initial)
rebound.update(epoch="1", root_slot="101", domain=epoch1["domain"])
case("authenticated-epoch-proof-binding", {"synthetic_storage": {addr(POOL): {"24": "1", mapping(0,25): str(BASE.root())}}, "synthetic_balances": {addr(POOL): str(4*ETH)}},
    publish("publish-epoch-one", NEXT, epoch=1, slot=101), spend("old-proof-rebound-epoch", rebound, 102, rejected=True),
    spend("epoch-one-proof", epoch1, 102, paid=ETH-FEE))

# Fourth-frame rules. Each rejected case breaks one rule of an otherwise
# valid spend and must fail in the pool's VERIFY frame, before approval, so
# nonce keys, credits and balances stay unchanged. The accepted controls
# keep that rule.
POOL_VERIFY = f"VERIFY frame 1 (target {addr(POOL)}"
ACCOUNT_CALL = b"\x12\x34"
def account_tail(): return Frame(0, 0, EOA, CLAIM_FRAME_GAS, 0, ACCOUNT_CALL)
def set_tail(frames): frames[3:] = [account_tail()]
def tail_field(field, value): return lambda frames: setattr(frames[3], field, value)
def settle_field(field, value): return lambda frames: setattr(frames[2], field, value)
def second_settlement(frames):
    # A SENDER tail would run as the pool and could settle the same spend twice.
    frames[3] = Frame(2, 0, POOL, SETTLE_FRAME_GAS, 0, frames[2].data, SETTLE_FRAME_STATE_GAS)

case("tail-omitted-withdrawal-leaves-credit",
    spend("withdrawal-without-tail", initial, failed_claim=True, paid=0, statuses=[1, 1, 1],
          mutate=lambda frames: frames.pop()))
case("tail-generic-account-call-on-withdrawal-accepted",
    spend("withdrawal-account-tail", initial, failed_claim=True, paid=0, statuses=[1, 1, 1, 1], mutate=set_tail))
case("tail-generic-account-call-on-transfer-accepted",
    spend("transfer-account-tail", duplicate, expected_tree=private_tree, statuses=[1, 1, 1, 1],
          mutate=lambda frames: frames.append(account_tail())))
for label, mutate in [
        ("sender-mode-second-settlement", second_settlement),
        ("zero-target", tail_field("target", 0)),
        ("approval-flag", tail_field("flags", 1)),
        ("settlement-atomic-batch-with-tail", settle_field("flags", 4)),
        ("fifth-frame", lambda frames: frames.append(account_tail()))]:
    case("tail-rejected-" + label, spend("tail-" + label, initial, rejected=True, error=POOL_VERIFY, mutate=mutate))
# Any spend's tail may call the pool, but it reaches only what any caller can.
# A transfer's tail that repeats the settlement call (which requires the pool
# as sender) or the proof call (which works only as frame 1) reverts on its
# own, and the settlement stands with its keys consumed once. Each tail has
# enough gas to finish the call it repeats, so only the pool's checks stop it.
for label, index, execution, state in [
        ("settlement", 2, SETTLE_FRAME_GAS, SETTLE_FRAME_STATE_GAS),
        ("verify-entry", 1, 500_000, VERIFY_FRAME_STATE_GAS)]:
    case(f"tail-pool-call-repeating-{label}-on-transfer-reverts",
        spend(f"transfer-pool-tail-{label}", duplicate, expected_tree=private_tree, statuses=[1, 1, 1, 0],
              mutate=lambda frames, i=index, e=execution, st=state:
                  frames.append(Frame(0, 0, POOL, e, 0, frames[i].data, st))))
# EIP-8141 statically forbids value outside SENDER frames, so the client
# rejects this before the dispatcher's own value check can run.
case("tail-rejected-nonzero-value", spend("tail-nonzero-value", initial, rejected=True,
    error="non-zero value only allowed in SENDER mode", mutate=tail_field("value", 1)))

# Validation-frame limits are wallet defaults, not dispatcher pins. Raising them
# is accepted; a limit below what a frame needs makes the transaction invalid
# before approval, so nonce keys and balances stay unchanged.
def limits(frame, execution=None, state=None):
    def change(frames):
        if execution is not None: frames[frame].gas_limit = execution
        if state is not None: frames[frame].state_limit = state
    return change
def both(*changes): return lambda frames: [change(frames) for change in changes]
case("validation-limits-raised-accepted",
    spend("validation-limits-raised", initial, paid=ETH-FEE,
          mutate=both(limits(0, execution=50_000), limits(1, execution=400_000, state=300_000))))
for label, frame, change in [
        ("recent-root-execution", 0, limits(0, execution=5_000)),
        ("proof-execution", 1, limits(1, execution=200_000)),
        ("proof-state", 1, limits(1, state=VERIFY_FRAME_STATE_GAS - 1))]:
    case("validation-limit-too-low-" + label, spend("too-low-" + label, initial, rejected=True,
         error=f"VERIFY frame {frame}", mutate=change))

# The pool approves payment only if the proof's fee covers the maximum cost of
# every declared limit. At a price where the default limits just fit the fee, the
# same spend is accepted, and raising either validation frame's limit pushes the
# maximum cost past the fee, so the pool refuses it before approval.
fee_price = FEE // frame_tx(initial).total_gas_limit() - 1_000_000
case("validation-fee-covers-defaults", spend("fee-covers-defaults", initial, paid=ETH-FEE, max_fee=fee_price))
for label, change in [("recent-root-execution", limits(0, execution=100_000)),
                      ("proof-state", limits(1, state=300_000))]:
    case("validation-limit-raised-beyond-fee-" + label, spend("beyond-fee-" + label, initial,
         rejected=True, error=POOL_VERIFY, mutate=change, max_fee=fee_price))

# Hybrid compression: the proof binds the ten statement values through alpha
# and gamma, which the pool recomputes from the settlement calldata, and
# through beta, which follows the proof in frame 1. Changing any one statement
# value, or beta, makes the withdrawal invalid in the pool's VERIFY frame.
# nf1 and nf2 change in the entry so the EIP-8250 keys follow, and the
# authorizer case re-signs someone else's proof with an attacker's key, so all
# three reach the proof check. root and domain are refused earlier by the
# exact tuple and domain checks; old-branch-proof-current-root-rejected and
# old-proof-rebound-epoch take a changed root and domain to the verifier. A
# beta outside the field is refused by the dispatcher and by the verifier.
ATTACKER = keys.PrivateKey((0xA77AC4E5).to_bytes(32, "big"))
def changed_entry(field):
    e = copy.deepcopy(initial)
    if field in ("nf1", "nf2"):
        e[field] = "0x" + word(int(e[field], 16) + 1).hex()
    else:
        e["authorizer"] = "0x" + ATTACKER.public_key.to_canonical_address().hex()
        e["authorizer_private_key"] = "0x" + ATTACKER.to_bytes().hex()
    return e
def bump_word(frame, offset, delta=1):
    def change(frames):
        data = bytearray(frames[frame].data)
        value = int.from_bytes(data[offset:offset + 32], "big") + delta
        data[offset:offset + 32] = value.to_bytes(32, "big")
        frames[frame].data = bytes(data)
    return change
SETTLE_WORDS = {"nf1": 132, "nf2": 164, "out-cm1": 196, "out-cm2": 228, "root": 4, "domain": 100,
                "public-amount": 260, "fee": 292, "recipient": 324, "authorizer": 356}
for field, offset in SETTLE_WORDS.items():
    if field in ("nf1", "nf2", "authorizer"):
        step = spend(f"changed-{field}", changed_entry(field), rejected=True, error=POOL_VERIFY)
    else:
        step = spend(f"changed-{field}", initial, rejected=True, error=POOL_VERIFY, mutate=bump_word(2, offset))
    case(f"compression-statement-{field}-changed-rejected", step)
case("compression-beta-changed-rejected", spend("changed-beta", initial, rejected=True,
     error=POOL_VERIFY, mutate=bump_word(1, 256)))
case("compression-beta-outside-field-rejected", spend("beta-outside-field", initial, rejected=True,
     error=POOL_VERIFY, mutate=bump_word(1, 256, w.P)))

# Two independently signed private transfers are reusable policy fixtures.
policy_a = duplicate
policy_b = prove("policy-second", BASE, NB, 1, outputs=[(NC["inner"], 50*ETH//100), (ND["inner"], 40*ETH//100)])
save("policy-first", signed(policy_a))
save("policy-second", signed(policy_b))

# What a pool tail is for: a transfer that publishes its own root, so the note it
# creates can be spent from the next slot without a separate publication. Proved
# last so the earlier proofs keep their witnesses.
publish_call = keccak(b"publishEpochRoot(uint64)")[:4] + word(0)
created_copy = prove("tail-published-copy", private_tree, NB, 2, root_slot=101)
case("tail-transfer-publishes-root-then-created-note-withdrawn",
    spend("transfer-publishes-root", duplicate, expected_tree=private_tree, statuses=[1, 1, 1, 1],
          mutate=lambda frames: frames.append(Frame(0, 0, POOL, CLAIM_FRAME_GAS, 0, publish_call, CLAIM_FRAME_STATE_GAS))),
    spend("withdraw-note-from-tail-root", created_copy, 102, paid=NB["value"]-FEE))

# If the tail's publication fails, only the publication is retried: settlement
# stands and has already consumed the inputs. Here the tail has no state gas for
# the new root slot.
retry_copy = copy.deepcopy(created_copy)
retry_copy["root_slot"] = "102"
case("tail-publication-fails-then-publication-retried",
    spend("transfer-publication-fails", duplicate, expected_tree=private_tree, statuses=[1, 1, 1, 0],
          mutate=lambda frames: frames.append(Frame(0, 0, POOL, CLAIM_FRAME_GAS, 0, publish_call, 0))),
    publish("publish-retried", NEXT, slot=102),
    spend("withdraw-after-retried-publication", retry_copy, 103, paid=NB["value"]-FEE))

# The tail must publish the epoch the outputs land in. This transfer's two
# outputs do not fit in the tree's one free leaf, so settlement starts epoch 1
# and inserts them there. Publishing epoch 1 makes them spendable from the next
# slot. Publishing epoch 0 still succeeds, with epoch 0's final root, which
# lacks them; only a later publication of epoch 1 helps.
rolled = RepeatedTree(NA["cm"], (1 << 20) - 1)
rolled_seed = {str(level): str(rolled.uniform[level] if rolled.count >= (1 << level) else 0)
               for level in range(w.DEPTH+1)}
rolled_seed.update({"21": str(rolled.count), "22": str(rolled.root())})
rolled_state = {"synthetic_storage": {addr(POOL): rolled_seed},
                "synthetic_balances": {addr(POOL): str(rolled.count*ETH)}}
def rolled_transfer(name, epoch):
    step = spend(name, entries["rollover"], 102, statuses=[1, 1, 1, 1],
        mutate=lambda frames: frames.append(Frame(0, 0, POOL, CLAIM_FRAME_GAS, 0,
            keccak(b"publishEpochRoot(uint64)")[:4] + word(epoch), CLAIM_FRAME_STATE_GAS)))
    step["storage"][addr(POOL)].update({"21": str(len(next_tree.leaves)), "22": str(next_tree.root()),
        "24": "1", mapping(0, 25): str(rolled.root())})
    return step
output_next_slot = copy.deepcopy(epoch_output)
output_next_slot["root_slot"] = "102"
case("tail-publishes-output-epoch-after-rollover", rolled_state,
    publish("publish-before-rollover-tail", NEXT, slot=101),
    rolled_transfer("rollover-tail-publishes-epoch-one", 1),
    spend("withdraw-output-from-tail-root", output_next_slot, 103, paid=OUT1["value"]-FEE))
case("tail-publishing-input-epoch-after-rollover-misses-outputs", rolled_state,
    publish("publish-before-wrong-epoch-tail", NEXT, slot=101),
    rolled_transfer("rollover-tail-publishes-epoch-zero", 0),
    spend("output-root-not-published", output_next_slot, 103, rejected=True, error="VERIFY frame 0"),
    publish("publish-epoch-one-later", NEXT+1, epoch=1, slot=103),
    spend("withdraw-output-after-later-publication", epoch_output, 104, paid=OUT1["value"]-FEE))

# The pool's range checks are load-bearing: the verifier no longer sees the ten
# values. Each case proves an honest withdrawal against alpha over one value
# plus p, with the nonce keys following, so the proof and gamma pass and only
# the range check can refuse it before approval. root, domain and authorizer
# are pinned by exact equality checks and are not aliased here.
ALIASES = {"nf1": 0, "nf2": 1, "out-cm1": 2, "out-cm2": 3, "public-amount": 6, "fee": 7, "recipient": 8}
ENTRY_FIELD = {"nf1": "nf1", "nf2": "nf2", "out-cm1": "out_cm1", "out-cm2": "out_cm2"}
for field, index in ALIASES.items():
    aliased = prove(f"alias-{field}", BASE, NA, 0, alias=index)
    mutate = None
    if field in ENTRY_FIELD:
        key = ENTRY_FIELD[field]
        aliased[key] = "0x" + word(int(aliased[key], 16) + w.P).hex()
    elif field in ("public-amount", "fee"):
        key = field.replace("-", "_")
        aliased[key] = str(int(aliased[key]) + w.P)
    else:
        mutate = bump_word(2, SETTLE_WORDS["recipient"], w.P)
    case(f"compression-{field}-aliased-by-p-rejected", spend(f"aliased-{field}", aliased,
         rejected=True, error=POOL_VERIFY, mutate=mutate))

(OUT / "rejector-runtime.hex").write_text("0x60006000fd\n")
(OUT / "entries.json").write_text(json.dumps(entries, indent=2) + "\n")
manifest = {"chain_id": CHAIN, "slot_number": SLOT, "base_fee": 1, "block_gas_limit": 60_000_000,
    "accounts": [{"address": addr(DEPLOYER), "balance": str(100*ETH)},
        {"address": addr(REJECTOR), "balance": "0", "code": "rejector-runtime.hex"}],
    "setup": setup, "cases": cases}
(OUT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(f"generated {len(cases)} native cases, {len(entries)} real proofs", flush=True)
