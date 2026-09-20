"""Build real signed deployment and spend transactions for native client tests.

Keys, funding, DAI and liquidity are disposable local test fixtures.
All pool bytecode and Groth16 proving artifacts come from the prepared PR.
"""
from pathlib import Path
import copy
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent.parent
POOL_REPO = HERE.parent.parent
sys.path[:0] = [str(POOL_REPO / 'wallet'), str(POOL_REPO / 'devnet')]
from eth_keys import keys
from eth_hash.auto import keccak
import wallet as w
import gen_smoke as smoke
import pool_frametx as builder
from dispatcher import initcode
from frametx import Frame, FrameSig, FrameTx, rlp_bytes, rlp_int, rlp_list
from gas_profile import *

OUT = HERE / 'fixtures'
OUT.mkdir(exist_ok=True)
CHAIN = 8141
ETH = 10**18
ROOT_SLOT = 100
DEPLOYER_KEY = keys.PrivateKey((0xD3E10).to_bytes(32, 'big'))
OWNER_KEY = keys.PrivateKey((0xA11CE).to_bytes(32, 'big'))
DEPLOYER = int.from_bytes(DEPLOYER_KEY.public_key.to_canonical_address(), 'big')
OWNER = int.from_bytes(OWNER_KEY.public_key.to_canonical_address(), 'big')
EOA = 0xCAFEBABE


def word(x):
    return x.to_bytes(32, 'big')


def addr(x):
    return f'0x{x:040x}'


def create_address(nonce):
    return int.from_bytes(keccak(rlp_list([rlp_bytes(DEPLOYER.to_bytes(20, 'big')), rlp_int(nonce)]))[-20:], 'big')


NAMES = ['poseidon3', 'poseidon4', 'verifier', 'logic', 'pool', 'context', 'account',
         'dai', 'weth', 'factory', 'router', 'failure']
A = {name: create_address(i) for i, name in enumerate(NAMES)}
POOL, ACCOUNT, DAI = A['pool'], A['account'], A['dai']


def calldata(signature, *args):
    result = subprocess.run(['cast', 'calldata', signature, *map(str, args)], check=True, capture_output=True, text=True)
    return bytes.fromhex(result.stdout.strip().removeprefix('0x'))


def ordinary(nonce, to, data, value=0, key=DEPLOYER_KEY, gas=60_000_000):
    fields = [rlp_int(CHAIN), rlp_int(nonce), rlp_int(1), rlp_int(2), rlp_int(gas),
              rlp_bytes(b'' if to is None else to.to_bytes(20, 'big')),
              rlp_int(value), rlp_bytes(data), rlp_list([])]
    signature = key.sign_msg_hash(keccak(b'\x02' + rlp_list(fields)))
    return b'\x02' + rlp_list(fields + [rlp_int(signature.v), rlp_int(signature.r), rlp_int(signature.s)])


def save(name, raw, **expect):
    (OUT / f'{name}.hex').write_text('0x' + raw.hex() + '\n')
    return {'raw': f'{name}.hex', **expect}


def sol_artifact(filename, contract):
    artifacts = json.loads((HERE / 'fixtures-contracts' / (filename + '.json')).read_text())['contracts']
    return bytes.fromhex(next(v['bin'] for k, v in artifacts.items() if k.endswith(':' + contract)))


def pool_artifact(contract, small=False):
    directory = 'out-libsmall' if small else 'out'
    return bytes.fromhex(json.loads((POOL_REPO / 'contracts' / directory / f'{contract}.sol' / f'{contract}.json').read_text())['bytecode']['object'].removeprefix('0x'))


def dex_artifact(package, contract):
    return bytes.fromhex(json.loads((HERE / 'dex/node_modules/@uniswap' / package / 'build' / f'{contract}.json').read_text())['bytecode'].removeprefix('0x'))


constructors = [pool_artifact('PoseidonT3', True), pool_artifact('PoseidonT4', True),
                pool_artifact('Groth16Verifier'),
                pool_artifact('ShieldedPoolLogic') + word(A['poseidon3']) + word(A['poseidon4']),
                initcode(A['logic'], A['verifier']),
                bytes.fromhex((HERE / 'fixtures-contracts/NativeFrameContext.init.hex').read_text()),
                sol_artifact('RecipientPullNativeAccount.sol', 'RecipientPullNativeAccount') + word(OWNER) + word(A['context']),
                sol_artifact('TestDai.sol', 'TestDai'), dex_artifact('v2-periphery', 'WETH9'),
                dex_artifact('v2-core', 'UniswapV2Factory') + word(DEPLOYER),
                dex_artifact('v2-periphery', 'UniswapV2Router02') + word(A['factory']) + word(A['weth']),
                sol_artifact('TestDai.sol', 'NativeFailureTarget')]
setup = [save('deploy-' + name, ordinary(i, None, code), nonces={addr(A[name]): 1})
         for i, (name, code) in enumerate(zip(NAMES, constructors))]
nonce = len(setup)


def setup_call(name, target, data, value=0, **expect):
    global nonce
    setup.append(save(name, ordinary(nonce, target, data, value), **expect))
    nonce += 1


setup_call('mint-dai', DAI, calldata('mint(address,uint256)', addr(DEPLOYER), 1_000_000 * ETH))
setup_call('approve-router', DAI, calldata('approve(address,uint256)', addr(A['router']), 2**256 - 1))
setup_call('add-liquidity', A['router'], calldata('addLiquidityETH(address,uint256,uint256,uint256,address,uint256)',
           addr(DAI), 200_000 * ETH, 0, 0, addr(DEPLOYER), 2**256 - 1), 100 * ETH)

w.set_seed(20260919)
domain = w.domain_scalar(CHAIN, addr(POOL))
tree = w.Tree()
notes = []
for i, value in enumerate((ETH, 4 * ETH // 10, ETH)):
    sk, rho = w.new_note()
    inner = w.inner(sk, rho)
    cm = w.commitment(sk, rho, value)
    notes.append({'sk': sk, 'rho': rho, 'value': value, 'idx': i, 'inner': inner, 'cm': cm})
    tree.append(cm)
    setup_call(f'shield-note-{i}', POOL, calldata('shield(bytes32)', '0x' + word(inner).hex()), value,
               storage={addr(POOL): {'21': str(i + 1), '22': str(tree.root())}})
setup_call('publish-root', POOL, calldata('publishEpochRoot(uint64)', 0))
smoke.WORK = OUT / 'proof-work'
smoke.WORK.mkdir(exist_ok=True)
entries = {}
fee = ETH // 20
amount = ETH - fee


def prove(name, input_index, outputs, public_amount, recipient):
    inputs = [{k: notes[input_index][k] for k in ('sk', 'rho', 'value', 'idx')}, w.dummy_input()]
    pk_hex, authorizer = w.new_authorizer()
    witness = w.build_witness(tree, inputs, outputs, domain, authorizer=authorizer,
                              public_amount=public_amount, fee=fee, recipient=addr(recipient))
    cached = OUT / (name + '-proof.json')
    witness_hash = keccak(json.dumps(witness, sort_keys=True).encode()).hex()
    if cached.exists() and json.loads(cached.read_text())['witness_hash'] == witness_hash:
        existing = json.loads(cached.read_text())
        publics, proof = existing['publics'], existing['proof']
    else:
        publics, proof = smoke.prove(witness, name)
        cached.write_text(json.dumps({'witness_hash': witness_hash, 'publics': publics, 'proof': proof}, indent=2))
    entry = smoke.spend_entry(tree, domain, inputs, outputs, 0, public_amount, fee, recipient,
                              authorizer, pk_hex, publics, proof, root_slot=str(ROOT_SLOT))
    entries[name] = entry
    return entry


account_spend = prove('account', 0, w.sink_outputs(), amount, ACCOUNT)
eoa_spend = prove('eoa', 0, w.sink_outputs(), amount, EOA)
transfer_spend = prove('transfer', 0, [(w.inner(*w.new_note()), 6 * ETH // 10),
                                      (w.inner(*w.new_note()), 35 * ETH // 100)], 0, 0)
conflict_spend = prove('conflict', 2, [(notes[1]['inner'], notes[1]['value']), w.sink_outputs()[1]],
                       55 * ETH // 100, ACCOUNT)


def settle(entry):
    return builder.cast_calldata(f'settle({builder.SPEND_TUPLE})', builder.spend_args(entry))


def frame_tx(entry, call=None, execution=None, state=None):
    recent = keccak(POOL.to_bytes(20, 'big') + word(0)) + ROOT_SLOT.to_bytes(8, 'big') + word(int(entry['root'], 16))
    frames = [Frame(1, 0, 0x8272, RECENT_ROOT_FRAME_GAS, 0, recent),
              Frame(1, 3, POOL, VERIFY_FRAME_GAS, 0, builder.proof_bytes(entry), VERIFY_FRAME_STATE_GAS),
              Frame(2, 0, POOL, SETTLE_FRAME_GAS, 0, settle(entry), SETTLE_FRAME_STATE_GAS)]
    tail = builder.withdrawal_frame(POOL, settle(entry), call, execution, state)
    if tail:
        frames.append(tail)
    return FrameTx(CHAIN, sorted([int(entry['nf1'], 16), int(entry['nf2'], 16)]), 0, POOL, frames,
                   [FrameSig(1, int(entry['authorizer'], 16), b'', b'')], 1, 2)


def sign(tx, entry):
    pk = keys.PrivateKey(bytes.fromhex(entry['authorizer_private_key'].removeprefix('0x')))
    sig = pk.sign_msg_hash(tx.sig_hash())
    tx.signatures[0].signature = bytes([sig.v]) + word(sig.r) + word(sig.s)
    return tx.raw()


def account_call(entry, target, data, value=amount, call_gas=250_000, nonce=0, key=OWNER_KEY):
    settlement_hash = keccak(settle(entry)[4:])
    domain_hash = keccak(keccak(b'EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)')
                         + keccak(b'RecipientPullNativeTestAccount') + keccak(b'1') + word(CHAIN) + word(ACCOUNT))
    type_hash = keccak(b'PullAction(address pool,address target,uint256 value,bytes data,uint256 callGas,uint256 nonce,bytes32 settlementHash)')
    action_hash = keccak(type_hash + word(POOL) + word(target) + word(value) + keccak(data)
                         + word(call_gas) + word(nonce) + settlement_hash)
    sig = key.sign_msg_hash(keccak(b'\x19\x01' + domain_hash + action_hash))
    action = f'({addr(POOL)},{addr(target)},{value},0x{data.hex()},{call_gas},{nonce},0x{settlement_hash.hex()})'
    return calldata('execute((address,address,uint256,bytes,uint256,uint256,bytes32),uint8,bytes32,bytes32)',
                    action, sig.v + 27, '0x' + word(sig.r).hex(), '0x' + word(sig.s).hex())


def mapping_slot(key, slot):
    return '0x' + keccak(word(key) + word(slot)).hex()


def expected(entry, credit=0, account_nonce=0, dai_balance=0, next_index=3):
    recipient = int(entry['recipient'], 16)
    return {addr(POOL): {'21': str(next_index), mapping_slot(recipient, 24): str(credit)},
            addr(ACCOUNT): {'0': str(account_nonce), '1': '0'},
            addr(DAI): {mapping_slot(ACCOUNT, 0): str(dai_balance)},
            addr(0x8250): {'0x' + keccak(word(POOL) + word(int(entry[nf], 16))).hex(): '1' for nf in ('nf1', 'nf2')}}


cases = []


def add(name, tx, entry=account_spend, statuses=None, **expect):
    step = save(name, sign(tx, entry), slot_number=ROOT_SLOT + 1,
                statuses=statuses or [1] * len(tx.frames), **expect)
    case = {'name': name, 'transactions': [step]}
    cases.append(case)
    return case


add('private-transfer', frame_tx(transfer_spend), transfer_spend, storage=expected(transfer_spend, next_index=5))
add('ordinary-eth-delivery', frame_tx(eoa_spend), eoa_spend, storage=expected(eoa_spend), balances={addr(EOA): str(amount)})
amount_out = amount * 997 * (200_000 * ETH) // (100 * ETH * 1000 + amount * 997)
path = f'[{addr(A["weth"])},{addr(DAI)}]'
swap = calldata('swapExactETHForTokens(uint256,address[],address,uint256)', amount_out, path, addr(ACCOUNT), 2**256 - 1)
swap_call = account_call(account_spend, A['router'], swap)
add('eth-to-dai-swap', frame_tx(account_spend, swap_call), storage=expected(account_spend, account_nonce=1, dai_balance=amount_out),
    balances={addr(ACCOUNT): '0'})
cases[-1]['transactions'].append(save('spent-note-replay', sign(frame_tx(account_spend, swap_call), account_spend),
    slot_number=ROOT_SLOT + 2, accepted=False, error_contains='NonceMismatch',
    storage=expected(account_spend, account_nonce=1, dai_balance=amount_out)))

recover = ordinary(0, ACCOUNT, calldata('recover(address)', addr(POOL)), key=OWNER_KEY, gas=1_000_000)


def with_recovery(case):
    case['transactions'].append(save(case['name'] + '-recovery', recover, slot_number=ROOT_SLOT + 2,
                                     storage=expected(account_spend), balances={addr(ACCOUNT): '0'}))


bad_swap = calldata('swapExactETHForTokens(uint256,address[],address,uint256)', amount_out + 1, path, addr(ACCOUNT), 2**256 - 1)
with_recovery(add('swap-slippage-revert', frame_tx(account_spend, account_call(account_spend, A['router'], bad_swap)),
                  statuses=[1, 1, 1, 0], storage=expected(account_spend, credit=amount), balances={addr(ACCOUNT): '0'}))
with_recovery(add('wrong-account-signature', frame_tx(account_spend, account_call(account_spend, A['router'], swap, key=DEPLOYER_KEY)),
                  statuses=[1, 1, 1, 0], storage=expected(account_spend, credit=amount)))
with_recovery(add('tail-execution-exhaustion', frame_tx(account_spend, swap_call, execution=20_000),
                  statuses=[1, 1, 1, 0], storage=expected(account_spend, credit=amount)))
with_recovery(add('tail-state-exhaustion', frame_tx(account_spend, swap_call, state=1),
                  statuses=[1, 1, 1, 0], storage=expected(account_spend, credit=amount)))
for name, data in [('downstream-execution-exhaustion', calldata('exhaustExecution()')),
                   ('downstream-state-exhaustion', calldata('growState(uint256)', 10))]:
    call = account_call(account_spend, A['failure'], data)
    with_recovery(add(name, frame_tx(account_spend, call), statuses=[1, 1, 1, 0], storage=expected(account_spend, credit=amount)))

add('swap-at-489600-state-limit', frame_tx(account_spend, swap_call, state=489_600),
    storage=expected(account_spend, account_nonce=1, dai_balance=amount_out), balances={addr(ACCOUNT): '0'})
with_recovery(add('swap-below-489600-state-limit', frame_tx(account_spend, swap_call, state=489_599),
                  statuses=[1, 1, 1, 0], storage=expected(account_spend, credit=amount)))
with_recovery(add('account-request-for-another-settlement',
                  frame_tx(account_spend, account_call(conflict_spend, A['router'], swap)),
                  statuses=[1, 1, 1, 0], storage=expected(account_spend, credit=amount)))
add('unsupported-eoa-call-leaves-credit', frame_tx(eoa_spend, b'\x01'), eoa_spend,
    storage=expected(eoa_spend, credit=amount), balances={addr(EOA): '0'})

first = add('failed-settlement-cannot-spend-old-credit', frame_tx(account_spend, swap_call, execution=1),
            statuses=[1, 1, 1, 0], storage=expected(account_spend, credit=amount))
conflict_call = account_call(conflict_spend, A['router'], swap)
first['transactions'].append(save('conflicting-output-settlement', sign(frame_tx(conflict_spend, conflict_call), conflict_spend),
                                 slot_number=ROOT_SLOT + 1, statuses=[1, 1, 0, 0],
                                 storage=expected(conflict_spend, credit=amount)))
with_recovery(first)

# Real transaction rejection, before payment or note-key consumption.
for name, mutate in [('outer-signature-mutation', lambda t: setattr(t.frames[3], 'gas_limit', t.frames[3].gas_limit - 1)),
                     ('invalid-proof', lambda t: setattr(t.frames[1], 'data', b'\x00' * 256)),
                     ('unknown-recent-root', lambda t: setattr(t.frames[0], 'data', t.frames[0].data[:-32] + word(1))),
                     ('sender-tail', lambda t: setattr(t.frames[3], 'mode', 2)),
                     ('fifth-frame', lambda t: t.frames.append(copy.deepcopy(t.frames[3]))),
                     ('wrong-recipient-target', lambda t: setattr(t.frames[3], 'target', EOA)),
                     ('tail-flags', lambda t: setattr(t.frames[3], 'flags', 4)),
                     ('tail-value', lambda t: setattr(t.frames[3], 'value', 1)),
                     ('recipient-execution-over-cap', lambda t: setattr(t.frames[3], 'gas_limit', RECIPIENT_FRAME_MAX_GAS + 1)),
                     ('recipient-state-over-cap', lambda t: setattr(t.frames[3], 'state_limit', RECIPIENT_FRAME_MAX_STATE_GAS + 1))]:
    tx = frame_tx(account_spend, swap_call)
    sign(tx, account_spend)
    mutate(tx)
    raw = tx.raw() if name == 'outer-signature-mutation' else sign(tx, account_spend)
    state = expected(account_spend)
    state[addr(0x8250)] = {slot: '0' for slot in state[addr(0x8250)]}
    rejection = ('atomic batch flag on last frame' if name == 'tail-flags' else
                 'non-zero value only allowed in SENDER mode' if name == 'tail-value' else
                 'InvalidFrameSignature' if name == 'outer-signature-mutation' else
                 'VERIFY frame 0' if name == 'unknown-recent-root' else 'VERIFY frame 1')
    cases.append({'name': name, 'transactions': [save(name, raw, slot_number=ROOT_SLOT + 1,
                                                    accepted=False, error_contains=rejection, storage=state)]})

# Setup uses successive slots and the published root is at ROOT_SLOT.
for i, step in enumerate(setup):
    step['slot_number'] = ROOT_SLOT - len(setup) + i + 1

# Check the business amounts independently of gas. The native report supplies
# gas_spent and the real payer; the harness subtracts exactly that fee.
for case in cases:
    for step in case['transactions']:
        if step.get('accepted') is False:
            continue
        if step['raw'].endswith('-recovery.hex'):
            step['balance_delta_before_gas'] = {addr(POOL): str(-amount), addr(OWNER): str(amount), addr(ACCOUNT): '0'}
            continue
        statuses = step['statuses']
        if len(statuses) == 3:
            step['frame_state_gas'] = [0, 195_840, 293_760]
            step['balance_delta_before_gas'] = {addr(POOL): '0'}
        elif statuses[2] == 0:
            step['frame_state_gas'] = [0, 195_840, 0, 0]
            step['balance_delta_before_gas'] = {addr(POOL): '0'}
            step['allowed_changed_accounts'] = [addr(POOL), addr(0x8250), addr(0)]
        elif statuses[3] == 0:
            step['frame_state_gas'] = [0, 195_840, 97_920, 0]
            step['balance_delta_before_gas'] = {addr(POOL): '0'}
            step['allowed_changed_accounts'] = [addr(POOL), addr(0x8250), addr(0)]
        elif case['name'] == 'unsupported-eoa-call-leaves-credit':
            step['frame_state_gas'] = [0, 195_840, 97_920, 0]
            step['balance_delta_before_gas'] = {addr(POOL): '0'}
        elif case['name'] == 'ordinary-eth-delivery':
            step['frame_state_gas'] = [0, 195_840, 0, 183_600]
            step['balance_delta_before_gas'] = {addr(POOL): str(-amount), addr(EOA): str(amount)}
        else:
            step['frame_state_gas'] = [0, 195_840, 0, 391_680]
            step['balance_delta_before_gas'] = {addr(POOL): str(-amount), addr(ACCOUNT): '0'}

manifest = {'chain_id': CHAIN, 'slot_number': ROOT_SLOT, 'block_gas_limit': 120_000_000,
            'accounts': [{'address': addr(DEPLOYER), 'balance': str(10**24)},
                         {'address': addr(OWNER), 'balance': str(ETH)}], 'setup': setup, 'cases': cases}
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
(OUT / 'details.json').write_text(json.dumps({'addresses': {k: addr(v) for k, v in A.items()},
   'deployer': addr(DEPLOYER), 'owner': addr(OWNER), 'eoa': addr(EOA), 'entries': entries,
   'swap_in_wei': amount, 'expected_dai_out_wei': amount_out, 'setup_next_nonce': nonce}, indent=2) + '\n')
print(f'{len(setup)} real deployment/setup transactions; {len(cases)} native scenarios')
print(f'ETH->DAI: {amount / ETH} ETH -> {amount_out / ETH} local DAI')
