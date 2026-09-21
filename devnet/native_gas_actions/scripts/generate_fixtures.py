"""Generate signed native-VM vectors for the gas-only account-action profile.

All keys, assets and accounts are disposable local fixtures. Proofs, verifier,
pool logic and dispatcher bytecode come from this checkout.
"""
from pathlib import Path
import copy
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
from gas_profile import (
    ACTION_FRAME_MAX_CALLDATA,
    ACTION_FRAME_MAX_GAS,
    ACTION_FRAME_MAX_STATE_GAS,
    CLAIM_FRAME_GAS,
    CLAIM_FRAME_STATE_GAS,
    RECENT_ROOT_FRAME_GAS,
    SETTLE_FRAME_GAS,
    SETTLE_FRAME_STATE_GAS,
    VERIFY_FRAME_GAS,
    VERIFY_FRAME_STATE_GAS,
)

OUT = HERE / "fixtures"
OUT.mkdir(exist_ok=True)
CHAIN = 8141
ETH = 10**18
ROOT_SLOT = 100
FEE = ETH // 20
SINK_CM_0, SINK_CM_1 = w.output_commitments(w.sink_outputs())
DEPLOYER_KEY = keys.PrivateKey((0xD3E10).to_bytes(32, "big"))
OWNER_KEY = keys.PrivateKey((0xA11CE).to_bytes(32, "big"))
OTHER_KEY = keys.PrivateKey((0xBAD).to_bytes(32, "big"))
DEPLOYER = int.from_bytes(DEPLOYER_KEY.public_key.to_canonical_address(), "big")
OWNER = int.from_bytes(OWNER_KEY.public_key.to_canonical_address(), "big")
BENEFICIARY = 0xBEEF
EOA = 0xCAFEBABE


def word(value):
    return int(value).to_bytes(32, "big")


def addr(value):
    return f"0x{int(value):040x}"


def create_address(nonce):
    encoded = rlp_list([rlp_bytes(DEPLOYER.to_bytes(20, "big")), rlp_int(nonce)])
    return int.from_bytes(keccak(encoded)[-20:], "big")


NAMES = ["poseidon3", "poseidon4", "verifier", "logic", "pool", "context", "account", "asset", "failure"]
A = {name: create_address(index) for index, name in enumerate(NAMES)}
POOL, ACCOUNT, ASSET, FAILURE = A["pool"], A["account"], A["asset"], A["failure"]


def calldata(signature, *args):
    result = subprocess.run(
        ["cast", "calldata", signature, *map(str, args)],
        check=True,
        capture_output=True,
        text=True,
    )
    return bytes.fromhex(result.stdout.strip().removeprefix("0x"))


def ordinary(nonce, to, data, value=0, key=DEPLOYER_KEY, gas=60_000_000):
    fields = [
        rlp_int(CHAIN), rlp_int(nonce), rlp_int(1), rlp_int(2), rlp_int(gas),
        rlp_bytes(b"" if to is None else int(to).to_bytes(20, "big")),
        rlp_int(value), rlp_bytes(data), rlp_list([]),
    ]
    signature = key.sign_msg_hash(keccak(b"\x02" + rlp_list(fields)))
    return b"\x02" + rlp_list(
        fields + [rlp_int(signature.v), rlp_int(signature.r), rlp_int(signature.s)]
    )


def save(name, raw, **expect):
    (OUT / f"{name}.hex").write_text("0x" + raw.hex() + "\n")
    return {"raw": f"{name}.hex", **expect}


def pool_artifact(contract, small=False):
    directory = "out-libsmall" if small else "out"
    artifact = REPO / "contracts" / directory / f"{contract}.sol" / f"{contract}.json"
    return bytes.fromhex(json.loads(artifact.read_text())["bytecode"]["object"].removeprefix("0x"))


def fixture_artifact(contract):
    artifact = json.loads((HERE / "fixture-contracts" / "GasActionFixtures.sol.json").read_text())
    contracts = artifact["contracts"]
    return bytes.fromhex(next(value["bin"] for key, value in contracts.items() if key.endswith(":" + contract)))


constructors = [
    pool_artifact("PoseidonT3", True),
    pool_artifact("PoseidonT4", True),
    pool_artifact("Groth16Verifier"),
    pool_artifact("ShieldedPoolLogic") + word(A["poseidon3"]) + word(A["poseidon4"]),
    initcode(A["logic"], A["verifier"]),
    bytes.fromhex((HERE / "fixture-contracts" / "NativeFrameContext.init.hex").read_text().strip()),
    fixture_artifact("GasActionNativeAccount") + word(OWNER) + word(A["context"]),
    fixture_artifact("TestAsset"),
    fixture_artifact("FailureTarget"),
]

setup = [
    save(f"deploy-{name}", ordinary(index, None, code), nonces={addr(A[name]): 1})
    for index, (name, code) in enumerate(zip(NAMES, constructors))
]
setup_nonce = len(setup)


def setup_call(name, target, data, value=0, **expect):
    global setup_nonce
    setup.append(save(name, ordinary(setup_nonce, target, data, value), **expect))
    setup_nonce += 1


def mapping_slot(key, slot):
    return "0x" + keccak(word(key) + word(slot)).hex()


TOKEN_START = 1_000
TOKEN_SPEND = 100
setup_call(
    "mint-account-asset",
    ASSET,
    calldata("mint(address,uint256)", addr(ACCOUNT), TOKEN_START),
    storage={addr(ASSET): {mapping_slot(ACCOUNT, 0): str(TOKEN_START)}},
    balances={addr(ACCOUNT): "0"},
)

w.set_seed(20260921)
domain = w.domain_scalar(CHAIN, addr(POOL))
tree = w.Tree()
notes = []
for index, value in enumerate((ETH, 95 * ETH // 100)):
    sk, rho = w.new_note()
    inner = w.inner(sk, rho)
    commitment = w.commitment(sk, rho, value)
    notes.append({"sk": sk, "rho": rho, "value": value, "idx": index, "inner": inner, "cm": commitment})
    tree.append(commitment)
    setup_call(
        f"shield-note-{index}",
        POOL,
        calldata("shield(bytes32)", "0x" + word(inner).hex()),
        value,
        storage={addr(POOL): {"21": str(index + 1), "22": str(tree.root())}},
    )
setup_call("publish-root", POOL, calldata("publishEpochRoot(uint64)", 0))

smoke.WORK = HERE / "proof-work"
smoke.WORK.mkdir(exist_ok=True)
entries = {}


def prove(name, note_index, outputs, public_amount=0, recipient=0):
    inputs = [{key: notes[note_index][key] for key in ("sk", "rho", "value", "idx")}, w.dummy_input()]
    private_key, authorizer = w.new_authorizer()
    witness = w.build_witness(
        tree,
        inputs,
        outputs,
        domain,
        authorizer=authorizer,
        public_amount=public_amount,
        fee=FEE,
        recipient=addr(recipient),
    )
    cache = OUT / f"{name}-proof.json"
    witness_hash = keccak(json.dumps(witness, sort_keys=True).encode()).hex()
    if cache.exists() and json.loads(cache.read_text()).get("witness_hash") == witness_hash:
        record = json.loads(cache.read_text())
        publics, proof = record["publics"], record["proof"]
    else:
        publics, proof = smoke.prove(witness, name)
        cache.write_text(json.dumps({"witness_hash": witness_hash, "publics": publics, "proof": proof}, indent=2) + "\n")
    entry = smoke.spend_entry(
        tree,
        domain,
        inputs,
        outputs,
        0,
        public_amount,
        FEE,
        recipient,
        authorizer,
        private_key,
        publics,
        proof,
        root_slot=str(ROOT_SLOT),
    )
    entries[name] = entry
    return entry


transfer_outputs = [(w.inner(*w.new_note()), 60 * ETH // 100), (w.inner(*w.new_note()), 35 * ETH // 100)]
transfer = prove("transfer", 0, transfer_outputs)
second_outputs = [(w.inner(*w.new_note()), 50 * ETH // 100), (w.inner(*w.new_note()), 40 * ETH // 100)]
second = prove("second", 1, second_outputs)
conflict = prove("conflict", 0, [(notes[1]["inner"], notes[1]["value"]), w.sink_outputs()[1]])
withdrawal = prove("withdrawal", 1, w.sink_outputs(), notes[1]["value"] - FEE, EOA)


def settle(entry):
    return builder.cast_calldata(f"settle({builder.SPEND_TUPLE})", builder.spend_args(entry))


def proof_bytes(entry):
    return builder.proof_bytes(entry)


def recent_tuple(entry):
    source = keccak(POOL.to_bytes(20, "big") + word(0))
    return source + ROOT_SLOT.to_bytes(8, "big") + word(int(entry["root"], 16))


def frame_tx(entry, tail=None, max_fee=2):
    frames = [
        Frame(1, 0, 0x8272, RECENT_ROOT_FRAME_GAS, 0, recent_tuple(entry)),
        Frame(1, 3, POOL, VERIFY_FRAME_GAS, 0, proof_bytes(entry), VERIFY_FRAME_STATE_GAS),
        Frame(2, 0, POOL, SETTLE_FRAME_GAS, 0, settle(entry), SETTLE_FRAME_STATE_GAS),
    ]
    if tail is not None:
        frames.append(tail)
    return FrameTx(
        CHAIN,
        sorted([int(entry["nf1"], 16), int(entry["nf2"], 16)]),
        0,
        POOL,
        frames,
        [FrameSig(1, int(entry["authorizer"], 16), b"", b"")],
        1,
        max_fee,
    )


def sign(tx, entry):
    private_key = keys.PrivateKey(bytes.fromhex(entry["authorizer_private_key"].removeprefix("0x")))
    signature = private_key.sign_msg_hash(tx.sig_hash())
    tx.signatures[0].signature = bytes([signature.v]) + word(signature.r) + word(signature.s)
    return tx.raw()


def eip712_action(entry, target, data, call_gas, nonce=0, value=0, key=OWNER_KEY, signed=None):
    settlement_hash = keccak(settle(entry)[4:])
    action = (POOL, target, value, data, call_gas, nonce, settlement_hash)
    signed_action = signed or action
    signed_pool, signed_target, signed_value, signed_data, signed_gas, signed_nonce, signed_hash = signed_action
    domain_hash = keccak(
        keccak(b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")
        + keccak(b"GasActionNativeAccount")
        + keccak(b"1")
        + word(CHAIN)
        + word(ACCOUNT)
    )
    type_hash = keccak(
        b"GasAction(address pool,address target,uint256 value,bytes data,uint256 callGas,uint256 nonce,bytes32 settlementHash)"
    )
    action_hash = keccak(
        type_hash
        + word(signed_pool)
        + word(signed_target)
        + word(signed_value)
        + keccak(signed_data)
        + word(signed_gas)
        + word(signed_nonce)
        + signed_hash
    )
    signature = key.sign_msg_hash(keccak(b"\x19\x01" + domain_hash + action_hash))
    literal = (
        f"({addr(action[0])},{addr(action[1])},{action[2]},0x{action[3].hex()},"
        f"{action[4]},{action[5]},0x{action[6].hex()})"
    )
    return calldata(
        "execute((address,address,uint256,bytes,uint256,uint256,bytes32),uint8,bytes32,bytes32)",
        literal,
        signature.v + 27,
        "0x" + word(signature.r).hex(),
        "0x" + word(signature.s).hex(),
    ), action


transfer_data = calldata("transfer(address,uint256)", addr(BENEFICIARY), TOKEN_SPEND)
good_call, good_action = eip712_action(transfer, ASSET, transfer_data, 100_000)


def action_tail(data=good_call, execution=ACTION_FRAME_MAX_GAS, state=ACTION_FRAME_MAX_STATE_GAS, target=ACCOUNT):
    return Frame(0, 0, target, execution, 0, data, state)


def withdrawal_tail(entry):
    recipient = int(entry["recipient"], 16)
    data = keccak(b"claimWithdrawal(address)")[:4] + word(recipient)
    return Frame(0, 0, POOL, CLAIM_FRAME_GAS, 0, data, CLAIM_FRAME_STATE_GAS)


def pool_slots(entry, next_index, root, account_nonce=0, account_tokens=TOKEN_START, beneficiary_tokens=0):
    values = {
        addr(POOL): {
            "21": str(next_index),
            "22": str(root),
            mapping_slot(ACCOUNT, 24): "0",
        },
        addr(ACCOUNT): {"0": str(account_nonce), "1": "0"},
        addr(ASSET): {
            mapping_slot(ACCOUNT, 0): str(account_tokens),
            mapping_slot(BENEFICIARY, 0): str(beneficiary_tokens),
        },
        addr(0x8250): {
            "0x" + keccak(word(POOL) + word(int(entry[key], 16))).hex(): "1"
            for key in ("nf1", "nf2")
        },
    }
    return values


def settled_root(*spends):
    replay = w.Tree()
    for note in notes:
        replay.append(note["cm"])
    for entry in spends:
        for key, sink in (("out_cm1", SINK_CM_0), ("out_cm2", SINK_CM_1)):
            commitment = int(entry[key], 16)
            if commitment != sink:
                replay.append(commitment)
    return replay.root()


def add_output_slots(storage, *spends):
    pool = storage.setdefault(addr(POOL), {})
    for entry in spends:
        for key, sink in (("out_cm1", SINK_CM_0), ("out_cm2", SINK_CM_1)):
            commitment = int(entry[key], 16)
            if commitment != sink:
                pool[mapping_slot(commitment, 23)] = "1"
    return storage


def unchanged(entry=transfer):
    storage = pool_slots(entry, 2, tree.root())
    storage[addr(0x8250)] = {key: "0" for key in storage[addr(0x8250)]}
    return storage


cases = []


def add_case(name, tx, entry=transfer, statuses=None, **expect):
    step = save(
        name,
        sign(tx, entry),
        slot_number=ROOT_SLOT + 1,
        statuses=statuses or [1] * len(tx.frames),
        **expect,
    )
    case = {"name": name, "transactions": [step]}
    cases.append(case)
    return case


plain_storage = add_output_slots(pool_slots(transfer, 4, settled_root(transfer)), transfer)
add_case(
    "plain-private-transfer-three-frames",
    frame_tx(transfer),
    storage=plain_storage,
    balances={addr(ACCOUNT): "0"},
    payer=addr(POOL),
)

withdraw_amount = int(withdrawal["public_amount"])
add_case(
    "ordinary-withdrawal-exact-claim",
    frame_tx(withdrawal, withdrawal_tail(withdrawal)),
    withdrawal,
    storage=pool_slots(withdrawal, 2, tree.root()),
    balances={addr(EOA): str(withdraw_amount), addr(ACCOUNT): "0"},
    payer=addr(POOL),
)

success_storage = add_output_slots(
    pool_slots(transfer, 4, settled_root(transfer), 1, TOKEN_START - TOKEN_SPEND, TOKEN_SPEND),
    transfer,
)
success = add_case(
    "gas-only-token-action-from-zero-eth-account",
    frame_tx(transfer, action_tail()),
    storage=success_storage,
    balances={addr(ACCOUNT): "0"},
    payer=addr(POOL),
)
success["transactions"].append(
    save(
        "spent-note-replay",
        sign(frame_tx(transfer, action_tail()), transfer),
        slot_number=ROOT_SLOT + 2,
        accepted=False,
        error_contains="NonceMismatch",
        storage=success_storage,
        balances={addr(ACCOUNT): "0"},
    )
)

# A fresh signature binds the second spend's settlement but reuses the account
# nonce consumed by the first action. Frame 2 settles, while the account rejects
# only the stale nonce. This is distinct from keyed-nullifier replay above.
stale_nonce_call, _ = eip712_action(second, ASSET, transfer_data, 100_000, nonce=0)
second_tx = frame_tx(second, action_tail(stale_nonce_call))
second_storage = add_output_slots(
    pool_slots(second, 6, settled_root(transfer, second), 1, TOKEN_START - TOKEN_SPEND, TOKEN_SPEND),
    transfer,
    second,
)
success["transactions"].append(
    save(
        "stale-account-nonce-in-new-spend",
        sign(second_tx, second),
        slot_number=ROOT_SLOT + 2,
        statuses=[1, 1, 1, 0],
        storage=second_storage,
        balances={addr(ACCOUNT): "0"},
        payer=addr(POOL),
    )
)

failed_tail_storage = add_output_slots(pool_slots(transfer, 4, settled_root(transfer)), transfer)

wrong_owner, _ = eip712_action(transfer, ASSET, transfer_data, 100_000, key=OTHER_KEY)
add_case(
    "wrong-account-owner-signature",
    frame_tx(transfer, action_tail(wrong_owner)),
    statuses=[1, 1, 1, 0],
    storage=failed_tail_storage,
    balances={addr(ACCOUNT): "0"},
    payer=addr(POOL),
)

wrong_context_call, _ = eip712_action(second, ASSET, transfer_data, 100_000)
add_case(
    "copied-signature-wrong-settlement-context",
    frame_tx(transfer, action_tail(wrong_context_call)),
    statuses=[1, 1, 1, 0],
    storage=failed_tail_storage,
    balances={addr(ACCOUNT): "0"},
    payer=addr(POOL),
)

# A normal transaction carrying the exact public account signature cannot
# pre-execute it because the account requires native frame context.
cases.append({
    "name": "direct-copied-account-signature-rejected",
    "transactions": [
        save(
            "direct-copied-account-signature-rejected",
            ordinary(setup_nonce, ACCOUNT, good_call, key=DEPLOYER_KEY, gas=500_000),
            slot_number=ROOT_SLOT + 1,
            success=False,
            storage=unchanged(),
            balances={addr(ACCOUNT): "0"},
        )
    ],
})

# Mutate one account-authorized field but retain the old signature. The outer
# transaction is freshly signed so rejection is attributable to account auth.
mutated_actions = {
    "old-signature-mutated-call-target": (EOA, transfer_data, 100_000),
    "old-signature-mutated-call-data": (
        ASSET,
        calldata("transfer(address,uint256)", addr(BENEFICIARY), TOKEN_SPEND + 1),
        100_000,
    ),
    "old-signature-mutated-call-gas": (ASSET, transfer_data, 100_001),
}
for name, (target, data, call_gas) in mutated_actions.items():
    mutated_call, _ = eip712_action(
        transfer,
        target,
        data,
        call_gas,
        signed=good_action,
    )
    add_case(
        name,
        frame_tx(transfer, action_tail(mutated_call)),
        statuses=[1, 1, 1, 0],
        storage=failed_tail_storage,
        balances={addr(ACCOUNT): "0"},
        payer=addr(POOL),
    )

failure_call, _ = eip712_action(transfer, FAILURE, calldata("fail()"), 80_000)
add_case(
    "downstream-revert-preserves-private-change",
    frame_tx(transfer, action_tail(failure_call)),
    statuses=[1, 1, 1, 0],
    storage=failed_tail_storage,
    balances={addr(ACCOUNT): "0"},
    payer=addr(POOL),
)

exhaust_call, _ = eip712_action(transfer, FAILURE, calldata("exhaustExecution()"), 80_000)
add_case(
    "downstream-execution-oog-preserves-private-change",
    frame_tx(transfer, action_tail(exhaust_call)),
    statuses=[1, 1, 1, 0],
    storage=failed_tail_storage,
    balances={addr(ACCOUNT): "0"},
    payer=addr(POOL),
)

add_case(
    "action-state-oog-preserves-private-change",
    frame_tx(transfer, action_tail(state=1)),
    statuses=[1, 1, 1, 0],
    storage=failed_tail_storage,
    balances={addr(ACCOUNT): "0"},
    payer=addr(POOL),
)

conflict_call, _ = eip712_action(conflict, ASSET, transfer_data, 100_000)
conflict_storage = pool_slots(conflict, 2, tree.root())
add_case(
    "failed-settlement-does-not-trigger-account-action",
    frame_tx(conflict, action_tail(conflict_call)),
    conflict,
    statuses=[1, 1, 0, 0],
    storage=conflict_storage,
    balances={addr(ACCOUNT): "0"},
    payer=addr(POOL),
)


def invalid_case(name, mutate):
    tx = frame_tx(transfer, action_tail())
    mutate(tx)
    cases.append({
        "name": name,
        "transactions": [
            save(
                name,
                sign(tx, transfer),
                slot_number=ROOT_SLOT + 1,
                accepted=False,
                storage=unchanged(),
                balances={addr(ACCOUNT): "0"},
            )
        ],
    })


invalid_case("resigned-five-frame-shape", lambda tx: tx.frames.append(copy.deepcopy(tx.frames[3])))
invalid_case("resigned-action-sender-mode", lambda tx: setattr(tx.frames[3], "mode", 2))
invalid_case("resigned-action-flags", lambda tx: setattr(tx.frames[3], "flags", 4))
invalid_case("resigned-action-value", lambda tx: setattr(tx.frames[3], "value", 1))
invalid_case("resigned-action-pool-target", lambda tx: setattr(tx.frames[3], "target", POOL))
invalid_case("resigned-action-zero-target", lambda tx: setattr(tx.frames[3], "target", 0))
invalid_case(
    "resigned-action-execution-over-cap",
    lambda tx: setattr(tx.frames[3], "gas_limit", ACTION_FRAME_MAX_GAS + 1),
)
invalid_case(
    "resigned-action-state-over-cap",
    lambda tx: setattr(tx.frames[3], "state_limit", ACTION_FRAME_MAX_STATE_GAS + 1),
)
invalid_case(
    "resigned-action-data-over-cap",
    lambda tx: setattr(tx.frames[3], "data", b"\x00" * (ACTION_FRAME_MAX_CALLDATA + 1)),
)


def underfund(tx):
    tx.max_fee = FEE // tx.total_gas_limit() + 1
    assert tx.max_cost() > FEE


invalid_case("fee-does-not-cover-declared-action-caps", underfund)

# Setup runs through ROOT_SLOT and publication records the exact slot used by
# every proof's recent-root tuple.
for index, step in enumerate(setup):
    step["slot_number"] = ROOT_SLOT - len(setup) + index + 1

for case in cases:
    for step in case["transactions"]:
        if step.get("accepted") is False or step.get("success") is False:
            continue
        business = {addr(POOL): "0", addr(ACCOUNT): "0"}
        if case["name"] == "ordinary-withdrawal-exact-claim":
            business[addr(POOL)] = str(-withdraw_amount)
        step["balance_delta_before_gas"] = business

manifest = {
    "chain_id": CHAIN,
    "slot_number": ROOT_SLOT,
    "block_gas_limit": 60_000_000,
    "accounts": [
        {"address": addr(DEPLOYER), "balance": str(10**24)},
        {"address": addr(OWNER), "balance": "0"},
    ],
    "setup": setup,
    "cases": cases,
}
(OUT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
(OUT / "details.json").write_text(
    json.dumps(
        {
            "addresses": {name: addr(value) for name, value in A.items()},
            "deployer": addr(DEPLOYER),
            "owner": addr(OWNER),
            "beneficiary": addr(BENEFICIARY),
            "eoa": addr(EOA),
            "entries": entries,
            "token_start": TOKEN_START,
            "token_spend": TOKEN_SPEND,
            "setup_next_nonce": setup_nonce,
        },
        indent=2,
    ) + "\n"
)
print(f"{len(setup)} deployment/setup transactions; {len(cases)} native scenarios")
print("generated and verified four real Groth16 proofs")
