#!/usr/bin/env python3
"""Step 1 checks for the formal project, run by CI next to `lake build`.

  statements  SPEC.md and every project module `Spec` imports, transitively,
              match formal/STATEMENTS.lock
  pins        every artifact in SPEC.md's §1 table has its pinned SHA-256
  sources     no Lean file admits a proof (sorry, admit, native_decide), skips
              the kernel (debug.skipKernelTC) or uses axiom, unsafe or
              implemented_by, outside comments; this is a
              textual check, and Proofs/AxiomAudit.lean is the binding one

`statements --update` rewrites the lock after a reviewed change to the spec.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[1]
ROOT = FORMAL.parent
LOCK = FORMAL / 'STATEMENTS.lock'
BANNED = re.compile(r'\b(sorry|admit|native_decide|implemented_by|axiom|unsafe|skipKernelTC)\b')


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(name):
    return FORMAL / (name.replace('.', '/') + '.lean')


def statement_files():
    """SPEC.md and the import closure of `Spec` within this project: every
    module that fixes what a claim means, including the concrete hashes and
    circuit."""
    seen, stack = set(), ['Spec']
    while stack:
        name = stack.pop()
        if name in seen or not module_path(name).exists():
            continue
        seen.add(name)
        stack += re.findall(r'^import\s+(\S+)', module_path(name).read_text(), re.M)
    return [FORMAL / 'SPEC.md'] + sorted(module_path(n) for n in seen)


def statements(update):
    current = {str(p.relative_to(ROOT)): sha256(p) for p in statement_files()}
    if update:
        LOCK.write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
        print(f'wrote {LOCK.relative_to(ROOT)} for {len(current)} files')
        return True
    locked = json.loads(LOCK.read_text())
    ok = True
    for name in sorted(set(current) | set(locked)):
        if current.get(name) != locked.get(name):
            print(f'statement changed without a lock update: {name}')
            ok = False
    if ok:
        print(f'statements: {len(current)} files match the lock')
    return ok


def pins():
    section = FORMAL.joinpath('SPEC.md').read_text().split('## 2.')[0]
    ok, count = True, 0
    for line in section.splitlines():
        if not line.startswith('| `'):
            continue
        cells = [c.strip() for c in line.strip('|').split('|')]
        paths = re.findall(r'`([^`]+)`', cells[0])
        hashes = re.findall(r'`([0-9a-f]{16})`', cells[1])
        # a row may pin several files of one directory: `a/B.sol`, `C.sol`
        base = paths[0].rsplit('/', 1)[0] + '/' if '/' in paths[0] else ''
        for i, (name, want) in enumerate(zip(paths, hashes)):
            path = ROOT / (name if i == 0 or '/' in name else base + name)
            count += 1
            if not path.exists():
                print(f'pinned artifact missing: {path.relative_to(ROOT)}')
                ok = False
            elif sha256(path)[:16] != want:
                print(f'pinned artifact changed: {path.relative_to(ROOT)}')
                ok = False
    if count == 0:
        print('no artifact pins found in SPEC.md §1')
        return False
    if ok:
        print(f'pins: {count} artifacts match SPEC.md §1')
    return ok


def strip_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return ''.join(out)


def sources():
    ok, count = True, 0
    for path in sorted(FORMAL.rglob('*.lean')):
        if '.lake' in path.relative_to(FORMAL).parts:
            continue
        count += 1
        code = strip_comments(path.read_text())
        for m in BANNED.finditer(code):
            line = code.count('\n', 0, m.start()) + 1
            print(f'{path.relative_to(ROOT)}: `{m.group(0)}` near code line {line}')
            ok = False
    if ok:
        print(f'sources: {count} Lean files admit nothing and add no axiom')
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('check', choices=['statements', 'pins', 'sources', 'all'])
    ap.add_argument('--update', action='store_true', help='rewrite STATEMENTS.lock')
    args = ap.parse_args()
    if args.update and args.check != 'statements':
        ap.error('--update applies to `statements` only')
    checks = {'statements': lambda: statements(args.update), 'pins': pins, 'sources': sources}
    names = list(checks) if args.check == 'all' else [args.check]
    results = [checks[n]() for n in names]
    sys.exit(0 if all(results) else 1)


if __name__ == '__main__':
    main()
