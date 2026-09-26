# Tree.lean's ZEROS[l] = Z_l for l < 20 and EMPTY_ROOT_CONST = Z_20,
# with reference/poseidon_bn254.py's p2.
import sys, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'reference'))
from poseidon_bn254 import p2
src = (ROOT / 'formal/Spec/Tree.lean').read_text()
zs = [int(x, 0) for x in re.findall(r'(0x[0-9a-f]+|(?<=\[)0)', src.split('def ZEROS')[1].split('/--')[0])]
er = int(re.search(r'EMPTY_ROOT_CONST : ℕ := (0x[0-9a-f]+)', src).group(1), 16)
Z = [0]
for l in range(20): Z.append(p2(Z[-1], Z[-1]))
ok = len(zs) == 20 and all(zs[l] == Z[l] for l in range(20)) and er == Z[20]
print('C6 constants match' if ok else 'C6 constants MISMATCH')
sys.exit(0 if ok else 1)
