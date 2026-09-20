"""Compile the native integration account, context helper and local test token."""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE.parent))
from dispatcher import solc_binary

for name in ('RecipientPullNativeAccount.sol', 'TestDai.sol'):
    source = HERE / 'fixtures-contracts' / name
    result = subprocess.run(
        [solc_binary(), '--optimize', '--optimize-runs', '200',
         '--combined-json', 'abi,bin,bin-runtime', str(source)],
        check=True, capture_output=True, text=True,
    )
    json.loads(result.stdout)
    source.with_suffix(source.suffix + '.json').write_text(result.stdout)

result = subprocess.run(
    [solc_binary(), '--strict-assembly', '--optimize', '--bin',
     str(HERE / 'fixtures-contracts/NativeFrameContext.yul')],
    check=True, capture_output=True, text=True,
)
bytecode = result.stdout.split('Binary representation:\n')[1].splitlines()[0]
(HERE / 'fixtures-contracts/NativeFrameContext.init.hex').write_text(bytecode)
print('Compiled native integration fixtures with solc 0.8.30')
