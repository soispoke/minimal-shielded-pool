#!/usr/bin/env python3
"""Compile the candidate with explicit TEST-ONLY FrameTx host substitutions.
The real Yul checks/proof encoding/fee check execute. This does not test custom
opcodes, protocol signature verification, APPROVE, or two-dimensional gas.
"""
from pathlib import Path
import subprocess
import tempfile
from dispatcher import solc_binary

root = Path(__file__).resolve().parent
source = (root / 'ShieldedPoolDispatcher.yul').read_text()
replacements = {
    'value := verbatim_1i_1o(hex"B0", param)': 'value := sload(add(0x1000, param))',
    'value := verbatim_2i_1o(hex"B3", frameIndex, param)': 'value := sload(add(add(0x2000, mul(frameIndex, 0x100)), param))',
    'value := verbatim_2i_1o(hex"B1", offset, frameIndex)': 'value := sload(add(add(0x3000, mul(frameIndex, 0x1000)), offset))',
    'value := verbatim_2i_1o(hex"B4", signatureIndex, param)': 'value := sload(add(add(0x8000, mul(signatureIndex, 0x100)), param))',
    'verbatim_3i_0o(hex"AA", 0, 0, 3)': 'sstore(0x9000, 1)',
}
for old, new in replacements.items():
    assert source.count(old) == 1, old
    source = source.replace(old, new)
assert 'verbatim_' not in source
with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp) / 'Probe.yul'
    path.write_text(source)
    result = subprocess.run([solc_binary(), '--strict-assembly', '--optimize', '--optimize-runs', '200', '--bin', str(path)], check=True, capture_output=True, text=True)
    bytecode = result.stdout.split('Binary representation:\n')[1].splitlines()[0]
(root / 'build' / 'recipient_pull_probe.hex').write_text('0x' + bytecode)
print('wrote TEST-ONLY introspection-substituted dispatcher artifact')
