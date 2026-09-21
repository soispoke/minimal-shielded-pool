"""Compile the native gas-action account, context helper, token and targets."""
from pathlib import Path
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE.parent))
from dispatcher import solc_binary

source = HERE / "fixture-contracts" / "GasActionFixtures.sol"
result = subprocess.run(
    [solc_binary(), "--optimize", "--optimize-runs", "200",
     "--combined-json", "abi,bin,bin-runtime", str(source)],
    check=True, capture_output=True, text=True,
)
json.loads(result.stdout)
source.with_suffix(source.suffix + ".json").write_text(result.stdout)

context = HERE / "fixture-contracts" / "NativeFrameContext.yul"
result = subprocess.run(
    [solc_binary(), "--strict-assembly", "--optimize", "--bin", str(context)],
    check=True, capture_output=True, text=True,
)
bytecode = result.stdout.split("Binary representation:\n", 1)[1].splitlines()[0]
(HERE / "fixture-contracts" / "NativeFrameContext.init.hex").write_text(bytecode + "\n")
print("compiled native gas-action fixtures with solc 0.8.30")
