#!/usr/bin/env python3
"""Generate exact Keccak witnesses; Lean checks each permutation round.

The independent Python permutation uses the triangular-number rotation walk
and an LFSR for round constants, rather than Lean's inverse index/table method.
The resulting digest is compared with PyCryptodome's native Keccak and the
lockfile-pinned js-sha3 implementation. No generated data is trusted by Lean.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess

HERE = Path(__file__).resolve().parent
MASK = (1 << 64) - 1
RATE = 136

def rot(x, n):
    n %= 64
    return ((x << n) | (x >> ((64-n) % 64))) & MASK

def round_constants():
    r, result = 1, []
    for _ in range(24):
        rc = 0
        for j in range(7):
            r = ((r << 1) ^ ((r >> 7) * 0x71)) % 256
            if r & 2:
                rc ^= 1 << ((1 << j)-1)
        result.append(rc)
    return result

RC = round_constants()

def step(state, rc):
    a = list(state)
    c = [a[x] ^ a[x+5] ^ a[x+10] ^ a[x+15] ^ a[x+20] for x in range(5)]
    for y in range(5):
        for x in range(5):
            a[x+5*y] ^= c[(x+4)%5] ^ rot(c[(x+1)%5], 1)
    x, y, current = 1, 0, a[1]
    for t in range(24):
        x, y = y, (2*x+3*y)%5
        current, a[x+5*y] = a[x+5*y], rot(current, (t+1)*(t+2)//2)
    for y in range(5):
        row = a[5*y:5*y+5]
        for x in range(5):
            a[x+5*y] = row[x] ^ ((~row[(x+1)%5]) & row[(x+2)%5])
    a[0] ^= rc
    return a

def pad(message):
    out = bytearray(message)
    out.append(1)
    out.extend(b'\0' * ((-len(out)) % RATE))
    out[-1] |= 0x80
    return bytes(out)

def trace(message):
    padded = pad(message)
    state, blocks = [0]*25, []
    for off in range(0, len(padded), RATE):
        block = padded[off:off+RATE]
        for i in range(17):
            state[i] ^= int.from_bytes(block[8*i:8*i+8], 'little')
        states = [state.copy()]
        for rc in RC:
            state = step(state, rc)
            states.append(state.copy())
        blocks.append(states)
    digest = b''.join(l.to_bytes(8,'little') for l in state)[:32]
    return blocks, digest

VECTORS = [
    ('empty', b'', '[]'),
    ('abc', b'abc', '[97, 98, 99]'),
    ('source_one_zero', (1).to_bytes(20,'big')+bytes(32), 'MSP.addr20 1 ++ MSP.u256 0'),
    ('rate_minus_one', bytes(range(135)), '(List.range 135).map UInt8.ofNat'),
    ('rate_exact', bytes(range(136)), '(List.range 136).map UInt8.ofNat'),
    ('rate_plus_one', bytes(range(137)), '(List.range 137).map UInt8.ofNat'),
]

for _name, _message in [
    ('domain_tag', b'minimal-shielded-pool:occurrence-domain:v1'),
    ('rr_entry_tag', b'RECENT_ROOT_ENTRY'),
    ('rr_storage_tag', b'RECENT_ROOT_STORAGE'),
]:
    VECTORS.append((_name, _message, '['+', '.join(map(str,_message))+']'))
_domain_tag = int.from_bytes(trace(b'minimal-shielded-pool:occurrence-domain:v1')[1], 'big')
_domain_message = _domain_tag.to_bytes(32,'big') + (1).to_bytes(32,'big')*2 + bytes(32)
VECTORS.append(('domain_one_one_zero', _domain_message,
                f'MSP.u256 {_domain_tag} ++ MSP.u256 1 ++ MSP.u256 1 ++ MSP.u256 0'))

def state_lean(state):
    return '⟨#[' + ', '.join(f'0x{n:016x}' for n in state) + '], rfl⟩'

def emit(name, message, expression):
    blocks, digest = trace(message)
    lines = ['import Keccak.Hash', '', f'namespace MSP.Keccak.Vectors.{name}',
             'set_option maxRecDepth 65536', 'set_option maxHeartbeats 2000000', '',
             f'def input : List UInt8 := {expression}', '']
    for b, states in enumerate(blocks):
        for r, st in enumerate(states):
            lines.append(f'def b{b}s{r} : State := {state_lean(st)}')
        lines.append('')
        for r in range(24):
            lines.append(f'theorem b{b}step{r} : round b{b}s{r} '
                         f'(roundConstants.get ⟨{r}, by decide⟩) = b{b}s{r+1} := by decide')
        lines.extend(['',f'theorem b{b}permute : permute b{b}s0 = b{b}s24 := by',
                      '  unfold permute',
                      '  simp only [rounds]',
                      '  rw [' + ', '.join(f'b{b}step{r}' for r in range(24)) + ']', ''])
    lines += [f'theorem final_state : finalState input = b{len(blocks)-1}s24 := by',
              '  dsimp only [finalState]',
              f'  have hlength : (pad input).length / 136 = {len(blocks)} := by decide',
              '  rw [hlength]',
              '  simp only [absorbBlocks]']
    # Rewrite the first absorb and each following absorb through explicit states.
    for b in range(len(blocks)):
        expr = '(pad input)' + '.drop 136' * b
        previous = 'zeroState' if b == 0 else f'b{b-1}s24'
        lines.append(f'  have h{b} : absorbBlock {previous} (({expr}).take 136) = b{b}s0 := by decide')
        lines.append(f'  rw [h{b}, b{b}permute]')
    lines += ['',f'theorem hash_eq : hash input = 0x{digest.hex()} := by',
              '  unfold hash digest', '  rw [final_state]', '  decide', '',
              f'end MSP.Keccak.Vectors.{name}', '']
    return '\n'.join(lines)

def external_checks(node_modules):
    from Crypto.Hash import keccak
    for name, message, _ in VECTORS:
        actual = trace(message)[1].hex()
        expected = keccak.new(digest_bits=256, data=message).hexdigest()
        assert actual == expected, name
    if node_modules:
        module = (Path(node_modules)/'js-sha3').resolve()
        assert json.loads((module/'package.json').read_text())['version'] == '0.8.0'
        assert hashlib.sha256((module/'src/sha3.js').read_bytes()).hexdigest() == '13590a201b2199f00b74ee711edc1bdf744705dca12f43cc6ef64c32b5767fa9'
        script = 'const k=require(process.argv[1]);const v=JSON.parse(process.argv[2]);console.log(JSON.stringify(v.map(x=>k.keccak256(Buffer.from(x,"hex")))));'
        result = subprocess.check_output(['node', '-e', script, str(module),
                                        json.dumps([m.hex() for _,m,_ in VECTORS])], text=True)
        assert json.loads(result) == [trace(m)[1].hex() for _,m,_ in VECTORS]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--node-modules', type=Path)
    args=ap.parse_args()
    external_checks(args.node_modules)
    for name, message, expression in VECTORS:
        path=HERE/('Vector_'+name+'.lean')
        output=emit(name,message,expression)
        if args.write: path.write_text(output)
        else: assert path.read_text()==output, f'stale {path.name}'
    print(f'{len(VECTORS)} Keccak vectors checked; exact Lean traces ' + ('written' if args.write else 'unchanged'))

if __name__=='__main__': main()
