"""Generate a fixture for the shared-sender nonce-race test.

Two notes A and C are shielded into ONE tree, so after both inserts the pool
publishes a single root R. Two independent transfers then prove membership
against that same R:

  transfer_a: spend A -> (Bob 0.6, change 0.35), fee 0.05
  transfer_c: spend C -> (Dave 0.6, change 0.35), fee 0.05

The two transfers consume DISJOINT nullifier sets (different notes), so under
EIP-8250 keyed nonces they share the shared sender's address without any
sequential-nonce ordering between them: both are admissible in the same block,
in any order. That is the property under test.

The fixture is shaped so pool_frametx.py can drive both spends: it exposes the
two transfers under the keys `transfer` (A) and a second entry the harness
reads directly. Both carry the same recent-root reference (R at R's slot).

Run from sdk/: python3 gen_nonce_race.py --chain-id=N --pool-address=0x...
                   --root-slot=N [--epoch=N] [--random]
                   [--output=PATH]

The fixed seed is public, so it is refused outside the local test chain and
whenever --rpc reads a live tree: pass --random there. The fixture holds the
only openings of its notes, inputs and outputs alike, so it is written under
the ignored sdk/artifacts/ and never over a fixture for another chain.

Notes come from sdk/notes.py. Alice and Carol shield from their own
secrets; Alice pays Bob through his public address (her transfer carries the
ML-KEM ciphertext), and Carol pays Dave with a secret Dave handed her out of
band. The fixture records the wallets' seeds.
"""
import json
import secrets
import sys
import urllib.request
from pathlib import Path

import notes as n
import wallet as w
from poseidon_bn254 import hex32
from gen_smoke import prove, refuse_overwrite, spend_entry, write_private, ETH, WORK

DEFAULT_OUTPUT = WORK / "nonce_race_fixture.json"

HERE = Path(__file__).parent

# LeafAppended(bytes32 indexed cm, uint64 indexed epoch, uint32 index, bytes32 newRoot)
LEAF_APPENDED_TOPIC = "0x1c9386c619e61f45f16a19541b370266f8eb6fd22d241ff010e03cc31ea82368"


def _rpc(url, method, params):
    req = urllib.request.Request(
        url, headers={"content-type": "application/json"},
        data=json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode())
    r = json.loads(urllib.request.urlopen(req, timeout=30).read())
    if "error" in r:
        raise SystemExit(f"{method} -> {r['error']}")
    return r["result"]


def seeded_tree(url, pool, expected_epoch):
    """Rebuild the pool's current Merkle tree from its LeafAppended events, in
    index order, and assert the reconstructed root equals the pool's on-chain
    currentRoot. A real wallet does this; without it the fixture's membership
    proofs would bind an empty-tree root that no live pool with prior leaves
    ever holds. The two new deposits then append at the next free leaves, so
    the root the pool computes after both shields is exactly the fixture's."""
    logs = _rpc(url, "eth_getLogs", [{"address": pool, "topics": [LEAF_APPENDED_TOPIC],
                                      "fromBlock": "0x0", "toBlock": "latest"}])
    epoch_word = _rpc(url, "eth_call", [{"to": pool, "data": "0x76671808"}, "latest"])
    epoch = int(epoch_word, 16)
    if epoch != expected_epoch:
        raise SystemExit(f"--epoch={expected_epoch} does not match the live tree epoch {epoch}")
    leaves = {}
    for l in logs:
        if int(l["topics"][2], 16) != epoch:
            continue
        idx = int(l["data"][2:][0:64], 16)
        leaves[idx] = int(l["topics"][1], 16)
    tree = w.Tree()
    for i in range(len(leaves)):
        tree.append(leaves[i])
    recon = hex32(tree.root())
    onchain = _rpc(url, "eth_call", [{"to": pool, "data": "0xfdab463d"}, "latest"])  # currentRoot()
    onchain = "0x" + onchain.removeprefix("0x").rjust(64, "0")
    if recon.lower() != onchain.lower():
        raise SystemExit(f"tree reconstruction mismatch: rebuilt {recon} != on-chain {onchain}; "
                         "the pool's leaf set changed or DEPTH/hash params differ")
    print(f"  seeded tree from {len(leaves)} on-chain leaves, root {recon[:18]}... verified")
    return tree


def main():
    chain_id = 31337
    pool_address = None
    root_slot = None
    epoch = 0
    note_wei = ETH
    rpc_url = None
    pool = None
    output_path = DEFAULT_OUTPUT
    for arg in sys.argv[1:]:
        if arg.startswith("--chain-id="):
            chain_id = int(arg.split("=", 1)[1], 0)
        elif arg.startswith("--pool-address="):
            pool_address = arg.split("=", 1)[1]
        elif arg.startswith("--root-slot="):
            root_slot = int(arg.split("=", 1)[1], 0)
        elif arg.startswith("--epoch="):
            epoch = int(arg.split("=", 1)[1], 0)
        elif arg.startswith("--note-wei="):
            note_wei = int(arg.split("=", 1)[1], 0)
        elif arg.startswith("--rpc="):
            rpc_url = arg.split("=", 1)[1]
        elif arg.startswith("--pool="):
            pool = arg.split("=", 1)[1]
        elif arg.startswith("--output="):
            output_path = Path(arg.split("=", 1)[1]).expanduser().resolve()
    if pool_address is None or root_slot is None:
        raise SystemExit("--pool-address=0x... and --root-slot=N are required")
    if (rpc_url is None) != (pool is None):
        raise SystemExit("--rpc= and --pool= must be given together (seed the live tree)")
    if "--random" not in sys.argv:
        # Anyone could rebuild notes made from the public seed and spend them.
        if chain_id != 31337 or rpc_url is not None:
            raise SystemExit("the fixed seed is public, so anyone could spend these notes; "
                             "pass --random for another chain or a live tree")
        w.set_seed(20260712)
    previous = refuse_overwrite(output_path)
    if rpc_url is not None and int(_rpc(rpc_url, "eth_chainId", []), 16) != chain_id:
        raise SystemExit("--chain-id does not match the chain --rpc reads")
    WORK.mkdir(exist_ok=True)
    domain = w.domain_scalar(chain_id, pool_address, epoch)

    # The wallets: fixed public seeds on the test chain, refused anywhere else.
    names = ("alice", "bob", "carol", "dave")
    if "--random" in sys.argv:
        seeds = {name: secrets.token_bytes(32) for name in names}
    else:
        seeds = {name: w.keccak(f"minimal-shielded-pool:nonce-race:{name}:v1".encode()) for name in names}
    keys = {name: n.WalletKeys(seed) for name, seed in seeds.items()}
    alice_self = n.direct_channel(keys["alice"].owner_pk, keys["alice"].self_secret)
    carol_self = n.direct_channel(keys["carol"].owner_pk, keys["carol"].self_secret)

    # Two deposits, into one tree. Root R is fixed after both inserts. Against a
    # live pool, seed the tree from its existing leaves first so the fixture's
    # root and proofs match the pool state after the two shields land.
    v = note_wei
    note_a, rho_a, _, _ = n.reserve(alice_self, v)
    note_c, rho_c, _, _ = n.reserve(carol_self, v)
    sk_a, sk_c = keys["alice"].spend_key, keys["carol"].spend_key
    inner_a = w.inner(sk_a, rho_a)
    inner_c = w.inner(sk_c, rho_c)
    cm_a = w.commitment(sk_a, rho_a, v)
    cm_c = w.commitment(sk_c, rho_c, v)

    tree = seeded_tree(rpc_url, pool, epoch) if rpc_url else w.Tree()
    # The root before each note lands, which shield checks against the pool.
    prior_a = tree.root()
    idx_a = tree.append(cm_a)
    prior_c = tree.root()
    idx_c = tree.append(cm_c)
    root_R = tree.root()

    v_bob, v_fee = v * 60 // 100, v * 5 // 100
    v_change = v - v_bob - v_fee

    # transfer A: spend note A (idx 0) against R, paying Bob's public address
    to_bob = n.open_channel(keys["bob"].address())
    note_bob, rho_bob, _, ciphertext_bob = n.reserve(to_bob, v_bob)
    note_achg, rho_achg, _, _ = n.reserve(alice_self, v_change)
    sk_bob, sk_achg = keys["bob"].spend_key, keys["alice"].spend_key
    ins_a = [{"sk": sk_a, "rho": rho_a, "value": v, "idx": idx_a}, w.dummy_input()]
    outs_a = [(w.inner(sk_bob, rho_bob), v_bob), (w.inner(sk_achg, rho_achg), v_change)]
    auth_a_key, auth_a = w.new_authorizer()
    wa = w.build_witness(
        tree, ins_a, outs_a, domain, authorizer=auth_a,
        public_amount=0, fee=v_fee,
    )
    pub_a, proof_a = prove(wa, "race_a")

    # transfer C: spend note C (idx 1) against the SAME R, paying Dave with the
    # secret he handed Carol out of band
    to_dave = n.direct_channel(keys["dave"].owner_pk, keys["dave"].direct_secret(0))
    note_dave, rho_dave, _, _ = n.reserve(to_dave, v_bob)
    note_cchg, rho_cchg, _, _ = n.reserve(carol_self, v_change)
    sk_dave, sk_cchg = keys["dave"].spend_key, keys["carol"].spend_key
    ins_c = [{"sk": sk_c, "rho": rho_c, "value": v, "idx": idx_c}, w.dummy_input()]
    outs_c = [(w.inner(sk_dave, rho_dave), v_bob), (w.inner(sk_cchg, rho_cchg), v_change)]
    auth_c_key, auth_c = w.new_authorizer()
    wc = w.build_witness(
        tree, ins_c, outs_c, domain, authorizer=auth_c,
        public_amount=0, fee=v_fee,
    )
    pub_c, proof_c = prove(wc, "race_c")

    # No later spend here records the outputs, so their openings go with the
    # transfer that creates them.
    def openings(*notes):
        return [{"spend_key": hex32(sk), "rho": hex32(rho), "value": str(v)} for sk, rho, v in notes]
    ea = spend_entry(
        tree, domain, ins_a, outs_a, epoch, 0, v_fee, 0,
        auth_a, auth_a_key, pub_a, proof_a,
        output_openings=openings((sk_bob, rho_bob, v_bob), (sk_achg, rho_achg, v_change)),
        notes="0x" + n.spend_notes(note_bob, note_achg, ciphertext_bob).hex(),
    )
    ec = spend_entry(
        tree, domain, ins_c, outs_c, epoch, 0, v_fee, 0,
        auth_c, auth_c_key, pub_c, proof_c,
        output_openings=openings((sk_dave, rho_dave, v_bob), (sk_cchg, rho_cchg, v_change)),
        notes="0x" + n.spend_notes(note_dave, note_cchg).hex(),
    )

    nfa = {ea["nf1"], ea["nf2"]}
    nfc = {ec["nf1"], ec["nf2"]}
    assert nfa.isdisjoint(nfc), "transfers must consume disjoint nullifiers"
    assert ea["root"] == ec["root"] == hex32(root_R), "both transfers bind the same root"

    fixture = {
        "chain_id": chain_id,
        "pool_address": pool_address,
        "root_slot": root_slot,
        "epoch": epoch,
        "domain": hex32(domain),
        "root": hex32(root_R),
        "shields": [
            {"inner": hex32(inner_a), "cm": hex32(cm_a), "value": str(v), "leaf": idx_a,
             "prior_root": hex32(prior_a), "note": "0x" + n.shield_notes(note_a).hex()},
            {"inner": hex32(inner_c), "cm": hex32(cm_c), "value": str(v), "leaf": idx_c,
             "prior_root": hex32(prior_c), "note": "0x" + n.shield_notes(note_c).hex()},
        ],
        "wallets": {name: {"seed": "0x" + seeds[name].hex(), "address": keys[name].address().hex()}
                    for name in names},
        # pool_frametx.py reads spend entries under an op key; both are transfers
        "transfer": ea,
        "transfer_c": ec,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    write_private(output_path, json.dumps(fixture, indent=1), previous)
    print("two independent transfers proven against one root, disjoint nullifiers")
    print(f"  root R      {hex32(root_R)[:18]}...")
    print(f"  transfer A  nf {ea['nf1'][:14]}.. {ea['nf2'][:14]}..")
    print(f"  transfer C  nf {ec['nf1'][:14]}.. {ec['nf2'][:14]}..")
    print(f"  disjoint: {nfa.isdisjoint(nfc)}   same root: {ea['root'] == ec['root']}")
    print(f"wrote {output_path}")


if __name__ == "__main__":
    main()
