#!/usr/bin/env python3
"""Report which formally verified files differ from their pinned hashes.

The Lean proofs in soispoke/verified-shielded-pool cover one pool commit, whose
artifacts SPEC.md section 1 pins by SHA-256. This script hashes the pinned
files here and lists any that changed, so a pull request shows when it moves
the pool away from the verified commit. It only reports: it exits 0 whether or
not pins differ, and whether or not SPEC.md can be read.

It reads formal/SPEC.md when the formal repository is checked out as formal/,
and otherwise fetches SPEC.md from the formal repository's main branch.
"""
import hashlib
import os
import re
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC_URL = 'https://raw.githubusercontent.com/soispoke/verified-shielded-pool/main/SPEC.md'


def read_spec():
    local = ROOT / 'formal' / 'SPEC.md'
    if local.exists():
        return local.read_text(), str(local.relative_to(ROOT))
    with urllib.request.urlopen(SPEC_URL, timeout=30) as response:
        return response.read().decode(), SPEC_URL


def pinned(spec):
    """(path, sha256) for every row of SPEC.md's section 1 table, parsed as
    formal/tools/check_formal.py parses it."""
    rows = [line for line in spec.split('## 2.')[0].splitlines() if line.startswith('|')]
    for line in rows[2:]:
        cells = [c.strip() for c in line.strip('|').split('|')]
        paths = [p for p in re.findall(r'`([^`]+)`', cells[0]) if '/' in p or '.' in p]
        hashes = [t for t in re.findall(r'`([^`]+)`', cells[1]) if re.fullmatch(r'[0-9a-f]{64}', t)]
        base = paths[0].rsplit('/', 1)[0] + '/' if paths and '/' in paths[0] else ''
        for i, (name, want) in enumerate(zip(paths, hashes)):
            yield (name if i == 0 or '/' in name else base + name), want


def main():
    try:
        spec, source = read_spec()
    except OSError as err:
        print(f'::warning::could not read the formal pins ({err}); nothing checked')
        return 0
    pins = list(pinned(spec))
    if not pins:
        print(f'::warning::no full SHA-256 pins found in {source}; nothing checked')
        return 0
    changed = []
    for name, want in pins:
        path = ROOT / name
        if not path.exists() or hashlib.sha256(path.read_bytes()).hexdigest() != want:
            changed.append(name)
    verified = re.search(r'at `([0-9a-f]{7,40})`', spec)
    commit = verified.group(1) if verified else 'the pinned commit'
    if changed:
        for name in changed:
            print(f'::warning file={name}::{name} differs from the formally verified '
                  f'version; the proofs cover pool commit {commit}')
        summary = (f'{len(changed)} of {len(pins)} formally verified files differ from '
                   f'{commit}: ' + ', '.join(f'`{n}`' for n in changed) +
                   '. The proofs in soispoke/verified-shielded-pool do not cover this change '
                   'until its pins are updated.')
    else:
        summary = f'All {len(pins)} formally verified files match {commit} ({source}).'
    print(summary)
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as out:
            out.write(summary + '\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())
