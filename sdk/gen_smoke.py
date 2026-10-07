"""Generate the native-ETH join-split smoke fixture with REAL Groth16 proofs.

All values and fees are wei-denominated; no ERC-20 path is modeled. The story:

  1. Alice shields 1.0 ether into note A.
  2. Alice's join-split transfer: inputs (A, dummy), outputs (Bob 0.6,
     Alice's change 0.35), fee 0.05 retained by the self-paying pool. Two nullifiers,
     consumed on-chain as ONE EIP-8250 key set.
  3. Bob's withdraw: inputs (B, dummy), outputs (two canonical zero sinks),
     publicAmount 0.55 to the recipient, fee 0.05 to the sender.

The v2 circuit rejects the same note in both inputs directly (`nf1 != nf2`),
while the EIP-8250 duplicate-key rule remains defense in depth.

Each honest proof is verified off-chain against the committed verification
key before it lands in the fixture. Groth16 proving is randomised, so the
fixture pairs with the committed Groth16Verifier.sol from the same setup.

Run from the sdk/ directory:
  python3 gen_smoke.py [--random] [--chain-id=N] [--pool-address=0x...]
                       [--shield-wei=N] [--payment-wei=N] [--fee-wei=N]
                       [--output=PATH] [--recipient=0x...] [--epoch=N]

The value overrides preserve the same flow at a smaller scale. They are useful
for disposable devnet deployments and envelope boundary tests; defaults remain
1.0 ETH shielded, 0.6 ETH paid privately, and a 0.05 ETH fee.

Every note comes from sdk/notes.py: Alice's deposit and change from her own
secret, Bob's payment through his public address (the transfer carries the
ML-KEM ciphertext), and random notes in the withdrawals' unused places. The
fixture records each wallet's seed, so a scan rebuilds the notes from it.
"""
import argparse
import json
import os
import secrets
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import notes as n
import wallet as w
from poseidon_bn254 import hex32

HERE = Path(__file__).parent
TOOLING = HERE.parent / "tools"
BUILD = HERE.parent / "core" / "artifacts"
WORK = HERE / "artifacts"
RECIPIENT = "0x00000000000000000000000000000000cafebabe"
ETH = 10**18
TEST_CHAIN_ID = 31337
# keccak256(pool20 || SALT) for the deterministic Forge-test pool address
# 0xf62849f9a0b5bf2913b396098f7c7019b51a820a and SALT = 0, matching EIP-8272.
TEST_POOL = "0xf62849f9a0b5bf2913b396098f7c7019b51a820a"


ANY = object()


def file_identity(path):
    """Which file sits at path, or None if nothing does."""
    try:
        st = os.stat(path)
    except FileNotFoundError:
        return None
    return st.st_ino, st.st_mtime_ns, st.st_size


def write_private(path, text, previous=ANY):
    """Witnesses and fixtures hold note secrets and authorizer keys, so only the
    owner may read them. The text goes to a new owner-only file that then
    replaces the old one, so a reader holding an earlier, world-readable copy
    open never sees it. previous is what refuse_overwrite saw: None means the
    file must still be absent, otherwise it must still be that same file, so a
    concurrent run cannot write over a fixture another run just created."""
    path = Path(path)
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.")
    try:
        with os.fdopen(fd, "w") as f:
            f.write(text)
        if previous is None:
            try:
                os.link(tmp, path)
            except FileExistsError:
                raise SystemExit(f"{path} appeared while generating; move it and run again") from None
            os.unlink(tmp)
        else:
            if previous is not ANY and file_identity(path) != previous:
                raise SystemExit(f"{path} changed while generating; move it and run again")
            os.replace(tmp, path)
    except BaseException:
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise


def refuse_overwrite(path):
    """A fixture for any chain but the local test chain may hold the only
    openings of unspent notes, whatever mode the new run uses. Returns the
    identity of what is there, for write_private to check again."""
    previous = file_identity(path)
    if previous is None:
        return None
    try:
        chain = int(json.loads(path.read_text()).get("chain_id", -1))
    except (OSError, ValueError, AttributeError):
        chain = -1
    if chain != TEST_CHAIN_ID:
        raise SystemExit(f"{path} holds a fixture for chain {chain} and may hold the only secrets "
                         "of unspent notes; move it or pass another --output")
    return previous


def default_output(chain_id, pool_address):
    """The committed fixture for the test chain and pool; anything else goes
    under the ignored sdk/artifacts/, never into a tracked file."""
    if (chain_id, int(pool_address, 16)) == (TEST_CHAIN_ID, int(TEST_POOL, 16)):
        return HERE.parent / "test" / "fixtures" / "smoke_fixture.json"
    return WORK / f"smoke_fixture.{chain_id}.json"


def refuse_recipient(recipient, pool_address):
    """A credit to the pool, a precompile or a system contract can never be
    claimed; refuse it before proving rather than at withdrawal."""
    sys.path.insert(0, str(HERE))
    from pool_frametx import PRECOMPILES, UNCLAIMABLE_RECIPIENTS
    value = w.address_scalar(recipient)
    if value == w.address_scalar(pool_address) or value in PRECOMPILES or value in UNCLAIMABLE_RECIPIENTS:
        raise SystemExit(f"--recipient {recipient} would strand the withdrawal credit")


def run(cmd, cwd=TOOLING):
    r = subprocess.run([str(c) for c in cmd], capture_output=True, text=True, cwd=cwd)
    if r.returncode != 0:
        print(r.stdout, r.stderr, file=sys.stderr)
        raise SystemExit(f"command failed: {' '.join(str(c) for c in cmd)}")
    return r


def private_workdir(tag):
    """A fresh owner-only directory per proof, so concurrent runs never read
    each other's witness or proof, and the witness, which holds note secrets,
    goes away afterwards; the fixture keeps the openings."""
    return Path(tempfile.mkdtemp(dir=WORK, prefix=f"{tag}-"))


def prove(witness, tag):
    work = private_workdir(tag)
    try:
        wpath, proofpath, pubpath = work / "witness.json", work / "proof.json", work / "public.json"
        write_private(wpath, json.dumps(witness))
        run(["npx", "snarkjs", "groth16", "fullprove", wpath,
             BUILD / "spend_js" / "spend.wasm", BUILD / "spend_final.zkey",
             proofpath, pubpath])
        # the real proof check, against the committed verification key
        run(["npx", "snarkjs", "groth16", "verify",
             HERE.parent / "core" / "artifacts" / "spend_vkey.json", pubpath, proofpath])
        call = run(["npx", "snarkjs", "zkey", "export", "soliditycalldata", pubpath, proofpath])
        pa, pb, pc, _pub = json.loads("[" + call.stdout.strip() + "]")
        publics = [int(x) for x in json.loads(pubpath.read_text())]
        return publics, {"pA": pa, "pB": pb, "pC": pc}
    finally:
        shutil.rmtree(work)


def assert_unprovable(witness, tag):
    """Assert witness generation rejects a circuit-level attack."""
    work = private_workdir(f"review-{tag}")
    try:
        wpath = work / "witness.json"
        write_private(wpath, json.dumps(witness))
        result = subprocess.run(
            ["npx", "snarkjs", "wtns", "calculate", BUILD / "spend_js" / "spend.wasm", wpath,
             work / "witness.wtns"],
            capture_output=True, text=True, cwd=TOOLING,
        )
    finally:
        shutil.rmtree(work)
    if result.returncode == 0:
        raise SystemExit(f"UNSOUND: circuit accepted {tag}")


def spend_entry(
    tree, domain, inputs, outputs, epoch, public_amount, fee, recipient,
    authorizer, authorizer_private_key, publics, proof, **extra,
):
    root = tree.root()
    nf1, nf2 = w.input_nullifiers(domain, inputs)
    out_cm1, out_cm2 = w.output_commitments(outputs)
    # the crux: the proof's public signals (beta, gamma, alpha), in the
    # circuit's order, compress exactly the wallet's own ten statement values,
    # recomputed here as the pool recomputes them
    stmt = w.statement(nf1, nf2, out_cm1, out_cm2, root, domain,
                       public_amount, fee, recipient, authorizer)
    beta, gamma, alpha = publics
    assert alpha == w.compression_alpha(stmt), "proof alpha does not hash the wallet's statement"
    assert beta == w.compression_beta(stmt), "proof beta is not Poseidon of the wallet's statement"
    assert gamma == w.fingerprint((alpha + beta) % w.P, stmt), \
        "proof gamma does not fingerprint the wallet's statement"
    e = {"root": hex32(root), "epoch": str(epoch),
         "domain": hex32(domain),
         "nf1": hex32(nf1), "nf2": hex32(nf2),
         "out_cm1": hex32(out_cm1), "out_cm2": hex32(out_cm2),
         "public_amount": str(public_amount), "fee": str(fee),
         "recipient": f"0x{recipient:040x}",
         "authorizer": f"0x{authorizer:040x}",
         "authorizer_private_key": authorizer_private_key,
         "beta": hex32(beta),
         "proof": proof,
         # The openings of both inputs, dummy included. If another deposit
         # changes the tree first, the notes must be proved again against a
         # newer root, at the leaves they occupy, and nothing else keeps these
         # secrets.
         "inputs": [{"spend_key": hex32(i["sk"]), "rho": hex32(i["rho"]),
                     "value": str(i["value"]), "leaf": i["idx"]} for i in inputs]}
    e.update(extra)
    return e


def int_arg(value):
    """An integer in any form int(value, 0) reads."""
    try:
        return int(value, 0)
    except ValueError:
        raise argparse.ArgumentTypeError(f"not an integer: {value}") from None


def path_arg(value):
    return Path(value).expanduser().resolve()


def parse_args(argv):
    """The command line. Every flag must be one this script knows, so a mistyped
    --chain-id stops the run instead of falling back to the test chain."""
    ap = argparse.ArgumentParser(prog="gen_smoke.py", allow_abbrev=False,
                                 description="Generate the smoke fixture with real Groth16 proofs.")
    ap.add_argument("--random", action="store_true",
                    help="fresh seeds and witnesses (required off the test chain and pool)")
    ap.add_argument("--chain-id", type=int_arg, default=TEST_CHAIN_ID)
    ap.add_argument("--pool-address", default=TEST_POOL)
    ap.add_argument("--epoch", type=int_arg, default=0)
    ap.add_argument("--shield-wei", type=int_arg, default=ETH)
    ap.add_argument("--payment-wei", type=int_arg, default=ETH * 60 // 100)
    ap.add_argument("--fee-wei", type=int_arg, default=ETH * 5 // 100)
    ap.add_argument("--recipient")
    ap.add_argument("--output", type=path_arg)
    return ap.parse_args(argv)


def main():
    args = parse_args(sys.argv[1:])
    zkey = BUILD / "spend_final.zkey"
    if not zkey.exists():
        raise SystemExit("run the setup first: (cd ../tools && ./setup.sh)")
    WORK.mkdir(exist_ok=True)
    if not args.random:
        w.set_seed(20260702)
    chain_id, pool_address, epoch = args.chain_id, args.pool_address, args.epoch
    shield_wei, payment_wei, fee_wei = args.shield_wei, args.payment_wei, args.fee_wei
    output_path = args.output
    recipient = RECIPIENT
    if args.recipient is not None:
        recipient = args.recipient
        if not recipient.startswith("0x"):
            recipient = "0x" + recipient
        if w.address_scalar(recipient) == 0 or w.address_scalar(recipient) >= 1 << 160:
            raise SystemExit(f"invalid --recipient: {recipient}")
        recipient = f"0x{w.address_scalar(recipient):040x}"
    # The fixed seed is public, so anyone could rebuild these notes and spend
    # them. Keep it, and the placeholder recipient, for the committed fixture's
    # test chain and pool.
    if (chain_id, int(pool_address, 16)) != (TEST_CHAIN_ID, int(TEST_POOL, 16)):
        if not args.random:
            raise SystemExit("the fixed seed is public, so anyone could spend these notes; "
                             "pass --random for another chain or pool")
        if recipient == RECIPIENT:
            raise SystemExit("pass --recipient for another chain or pool; the default "
                             f"{RECIPIENT} is a test placeholder")
    refuse_recipient(recipient, pool_address)
    output_path = output_path or default_output(chain_id, pool_address)
    previous = refuse_overwrite(output_path)
    domain = w.domain_scalar(chain_id, pool_address, epoch)

    v_shield, v_bob, v_fee = shield_wei, payment_wei, fee_wei
    if not 0 < v_fee < v_bob < v_shield:
        raise SystemExit("value overrides require 0 < fee < payment < shield")
    v_change = v_shield - v_bob - v_fee
    if v_change <= v_fee:
        raise SystemExit("value overrides require change > fee so withdraw_seed can leave prior credit")

    # The wallets. The fixed seeds are as public as the fixed proving seed, and
    # refused off the test chain above.
    if args.random:
        alice_seed, bob_seed = secrets.token_bytes(32), secrets.token_bytes(32)
    else:
        alice_seed = w.keccak(b"minimal-shielded-pool:smoke:alice:v1")
        bob_seed = w.keccak(b"minimal-shielded-pool:smoke:bob:v1")
    alice, bob = n.WalletKeys(alice_seed), n.WalletKeys(bob_seed)
    alice_self = n.direct_channel(alice.owner_pk, alice.self_secret)

    # notes: Alice's deposit, Bob's payment, Alice's change
    note_a, rho_a, _, _ = n.reserve(alice_self, v_shield)
    to_bob = n.open_channel(bob.address())
    note_b, rho_b, _, ciphertext_b = n.reserve(to_bob, v_bob)
    note_a2, rho_a2, _, _ = n.reserve(alice_self, v_change)
    sk_a, sk_b, sk_a2 = alice.spend_key, bob.spend_key, alice.spend_key
    inner_a = w.inner(sk_a, rho_a)
    cm_a = w.commitment(sk_a, rho_a, v_shield)

    # 1+2. Alice's join-split transfer: (A, dummy) -> (Bob 0.6, change 0.35), fee 0.05
    t1 = w.Tree()
    t1.append(cm_a)
    ins_t = [{"sk": sk_a, "rho": rho_a, "value": v_shield, "idx": 0}, w.dummy_input()]
    outs_t = [(w.inner(sk_b, rho_b), v_bob), (w.inner(sk_a2, rho_a2), v_change)]
    auth_t_key, auth_t = w.new_authorizer()
    wt = w.build_witness(
        t1, ins_t, outs_t, domain, authorizer=auth_t, public_amount=0, fee=v_fee,
    )
    pub_t, proof_t = prove(wt, "transfer")

    # 3. Bob's withdraw: (B, dummy) -> (0, 0), publicAmount 0.55, fee 0.05
    t2 = w.Tree()
    for cm in [cm_a, *w.output_commitments(outs_t)]:
        t2.append(cm)
    cm_b = w.commitment(sk_b, rho_b, v_bob)
    assert t2.leaves[1] == cm_b, "Bob's note is leaf 1"
    ins_w = [{"sk": sk_b, "rho": rho_b, "value": v_bob, "idx": 1}, w.dummy_input()]
    outs_w = w.sink_outputs()
    v_pub = v_bob - v_fee
    auth_w_key, auth_w = w.new_authorizer()
    ww = w.build_witness(
        t2, ins_w, outs_w, domain, authorizer=auth_w,
        public_amount=v_pub, fee=v_fee, recipient=recipient,
    )
    pub_w, proof_w = prove(ww, "withdraw")

    # Alice's change at leaf 2, same post-transfer root: a seed exit that can
    # leave withdrawalCredit on the recipient without invalidating Bob's proof.
    cm_change = w.commitment(sk_a2, rho_a2, v_change)
    assert t2.leaves[2] == cm_change, "Alice's change is leaf 2"
    ins_seed = [{"sk": sk_a2, "rho": rho_a2, "value": v_change, "idx": 2}, w.dummy_input()]
    v_seed_pub = v_change - v_fee
    auth_s_key, auth_s = w.new_authorizer()
    ws = w.build_witness(
        t2, ins_seed, w.sink_outputs(), domain, authorizer=auth_s,
        public_amount=v_seed_pub, fee=v_fee, recipient=recipient,
    )
    pub_s, proof_s = prove(ws, "withdraw_seed")

    # The old circuit accepted one real note in both inputs and relied only on
    # the envelope's duplicate-key rule. V2 rejects the witness itself.
    ins_same = [dict(ins_t[0]), dict(ins_t[0])]
    outs_same = [(w.inner(*w.new_note()), v_shield), (w.inner(*w.new_note()), v_shield)]
    _, auth_same = w.new_authorizer()
    same = w.build_witness(
        t1, ins_same, outs_same, domain, authorizer=auth_same,
        public_amount=0, fee=0,
    )
    assert_unprovable(same, "same_note")

    # A positive duplicate output was previously counted twice in conservation
    # but inserted once. The new relation rejects it before approval.
    duplicate_value = (v_shield - v_fee) // 2
    if duplicate_value * 2 + v_fee == v_shield:
        dup_inner = w.inner(*w.new_note())
        _, auth_dup = w.new_authorizer()
        duplicate = dict(wt)
        duplicate["out_inner"] = [str(dup_inner), str(dup_inner)]
        duplicate["out_value"] = [str(duplicate_value), str(duplicate_value)]
        duplicate["authorizer"] = str(auth_dup)
        assert_unprovable(duplicate, "duplicate_positive_output")

    no_real = dict(wt)
    no_real["in_value"] = ["0", "0"]
    no_real["out_inner"] = ["1", "2"]
    no_real["out_value"] = ["0", "0"]
    no_real["public_amount"] = "0"
    no_real["fee"] = "0"
    assert_unprovable(no_real, "zero_real_inputs")

    wrong_sinks = dict(ww)
    wrong_sinks["out_inner"] = ["2", "1"]
    assert_unprovable(wrong_sinks, "wrong_sink_positions")

    zero_authorizer = dict(wt)
    zero_authorizer["authorizer"] = "0"
    assert_unprovable(zero_authorizer, "zero_authorizer")

    positive_sink = dict(wt)
    positive_sink["out_inner"] = ["1", wt["out_inner"][1]]
    assert_unprovable(positive_sink, "positive_output_uses_sink")

    missing_recipient = dict(ww)
    missing_recipient["recipient"] = "0"
    assert_unprovable(missing_recipient, "withdrawal_without_recipient")

    unused = n.spend_notes(n.dummy_note(), n.dummy_note())
    fixture = {
        "chain_id": chain_id,
        "pool_address": pool_address,
        "epoch": epoch,
        "domain": hex32(domain),
        "inner_a": hex32(inner_a),
        "cm_a": hex32(cm_a),
        "shield_value": str(v_shield),
        "shield_note": "0x" + n.shield_notes(note_a).hex(),
        "recipient": recipient,
        "wallets": {name: {"seed": "0x" + seed.hex(), "address": keys.address().hex()}
                    for name, seed, keys in (("alice", alice_seed, alice), ("bob", bob_seed, bob))},
        "transfer": spend_entry(t1, domain, ins_t, outs_t, epoch,
                                0, v_fee, 0, auth_t, auth_t_key, pub_t, proof_t,
                                notes="0x" + n.spend_notes(note_b, note_a2, ciphertext_b).hex(),
                                # Bob's opening is retained for the withdrawal vector.
                                out_inner1=hex32(outs_t[0][0]),
                                out_value1=str(outs_t[0][1])),
        "withdraw_seed": spend_entry(t2, domain, ins_seed, w.sink_outputs(), epoch,
                                     v_seed_pub, v_fee, w.address_scalar(recipient),
                                     auth_s, auth_s_key, pub_s, proof_s, notes="0x" + unused.hex()),
        "withdraw": spend_entry(t2, domain, ins_w, outs_w, epoch,
                                v_pub, v_fee, w.address_scalar(recipient),
                                auth_w, auth_w_key, pub_w, proof_w,
                                notes="0x" + n.spend_notes(n.dummy_note(), n.dummy_note()).hex()),
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    write_private(output_path, json.dumps(fixture, indent=1), previous)
    print("real join-split proofs generated and verified off-chain; compressed public signals bind the wallet statement")
    print(f"wrote {output_path}")
    print(f"  transfer  nf1 {fixture['transfer']['nf1'][:18]}... nf2 {fixture['transfer']['nf2'][:18]}... fee {v_fee}")
    print(f"  withdraw_seed publicAmount {v_seed_pub} fee {v_fee}")
    print(f"  withdraw  publicAmount {v_pub} fee {v_fee}")
    print(f"  domain   {fixture['domain']} (chain {chain_id}, pool {pool_address})")
    print("  same-note witness rejected in-circuit (nf1 != nf2)")


if __name__ == "__main__":
    main()
