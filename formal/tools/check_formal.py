#!/usr/bin/env python3
"""Step 1 checks for the formal project, run by CI next to `lake build`.

  statements  SPEC.md, every project module `Spec` imports, transitively,
              the import closure of Mutations/Soundness.lean and the four
              Mutations/*Certificate.lean modules, which define the mutants
              the audit pins, Proofs/PinClaims.lean and its imports, which
              state the other pinned results, Proofs/AxiomAudit.lean, which pins the principal
              theorems' types,
              and Proofs/AuditCommand.lean, the audit command it uses, match
              formal/STATEMENTS.lock
  pins        every artifact in SPEC.md's §1 table has its full pinned SHA-256
  sources     no Lean file admits a proof (sorry, admit, native evaluation),
              skips the kernel (debug.skipKernelTC) or uses axiom, unsafe or
              implemented_by; no Lean file outside the lock, except the
              step-4 driver tools/DifferentialModel.lean, runs or defines
              metaprograms (#eval, run_cmd, macros, syntax, elaborators, the
              `Lean` namespace), which could rewrite files or the audit during
              the build; no lakefile.lean overrides lakefile.toml; and no
              build output under formal/.lake is committed, since Lake would
              replay it instead of checking the source. These
              are textual checks outside comments and string literals;
              Proofs/AxiomAudit.lean is the binding one

`statements --update` rewrites the lock after a reviewed change to the spec.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[1]
ROOT = FORMAL.parent
LOCK = FORMAL / 'STATEMENTS.lock'
BANNED = re.compile(r'\b(sorry|sorryAx|admit|native_decide|implemented_by|axiom|unsafe|skipKernelTC|bv_decide)\b'
                    r'|\+native\b|\bnative\s*:=\s*true')
# Metaprogramming entry points, allowed only in locked (owner-reviewed) files.
META = re.compile(r'#eval\b|#guard_msgs\b|\beval%|\b(by_elab|run_cmd|run_elab|run_meta|run_tac|initialize|'
                  r'builtin_initialize|macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|'
                  r'prefix|postfix|declare_syntax_cat|simproc|dsimproc|Lean|__raw_string__|__brace_string__)\b'
                  r'|(?:@\[|\battribute\s*\[)[^\]]*\b(?:builtin_)?init\b')
# The step-4 driver evaluates the model with #eval; `lake build` never runs it.
META_EXEMPT = {'tools/DifferentialModel.lean'}
# A plain string containing `{`, which Lean may interpolate; rejected in the driver too.
BRACE_STRING = re.compile(r'\b__brace_string__\b')
IMPORT = re.compile(r'^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)', re.M)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(name):
    return FORMAL / (name.replace('.', '/') + '.lean')


def statement_files():
    """SPEC.md, the import closure of `Spec` within this project (every module
    that fixes what a claim means, including the concrete hashes and circuit),
    the import closure of the four circuit mutants and `Mutations.C1For`,
    which fix what the pinned mutation results mean, Proofs.PinClaims, which
    states the other results the audit pins by name, and the audit that pins
    each principal theorem to its claim, with its audit command."""
    seen, stack = set(), ['Spec', 'Mutations.Soundness', 'Proofs.PinClaims'] + [
        f'Mutations.{case}Certificate' for case in ('Membership', 'Range', 'Duplicate', 'Sink')]
    while stack:
        name = stack.pop()
        if name in seen or not module_path(name).exists():
            continue
        seen.add(name)
        stack += IMPORT.findall(module_path(name).read_text())
    return [FORMAL / 'SPEC.md'] + sorted(module_path(n) for n in seen | {'Proofs.AxiomAudit', 'Proofs.AuditCommand'})


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
    rows = [line for line in section.splitlines() if line.startswith('|')]
    for line in rows[2:]:  # every row after the header and the |---| separator
        cells = [c.strip() for c in line.strip('|').split('|')]
        # file names contain '/' or '.', which drops prose such as `compiler`
        paths = [p for p in re.findall(r'`([^`]+)`', cells[0]) if '/' in p or '.' in p]
        tokens = re.findall(r'`([^`]+)`', cells[1])
        hashes = [t for t in tokens if re.fullmatch(r'[0-9a-f]{64}', t)]
        if not paths or hashes != tokens or len(hashes) != len(paths):
            print(f'malformed pin row: {line}')
            ok = False
            continue
        # a row may pin several files of one directory: `a/B.sol`, `C.sol`
        base = paths[0].rsplit('/', 1)[0] + '/' if '/' in paths[0] else ''
        for i, (name, want) in enumerate(zip(paths, hashes)):
            path = ROOT / (name if i == 0 or '/' in name else base + name)
            count += 1
            if not path.exists():
                print(f'pinned artifact missing: {path.relative_to(ROOT)}')
                ok = False
            elif sha256(path) != want:
                print(f'pinned artifact changed: {path.relative_to(ROOT)}')
                ok = False
    if count == 0:
        print('no artifact pins found in SPEC.md §1')
        return False
    if ok:
        print(f'pins: {count} artifacts match SPEC.md §1')
    return ok


IDENT_TAIL = set("_'.!?")


def _ident_before(text, i):
    return i > 0 and (text[i - 1].isalnum() or text[i - 1] in IDENT_TAIL)


CHAR_LIT = re.compile(r"'(\\.[^']*|[^\\'])'")


def strip_comments(text):
    """The code outside comments, with every string and character literal
    emptied, so a literal can neither hide code nor open a fake comment.
    Plain strings honour escapes; raw strings (`r"..."`, `r#"..."#`) have
    none and become the token `__raw_string__`, which `META` rejects outside
    the lock; interpolated strings (`s!"...{code}..."`, and `m!` and `f!`)
    keep their code, which is lexed again, nested literals included. Every
    other string is lexed as plain; Lean agrees except after `println!`,
    `dbg_trace`, `throwError` and similar, which interpolate a string without
    a prefix. So a plain string containing `{` becomes `__brace_string__`,
    rejected outside the lock, the step-4 driver included; inside the lock,
    such a string's code is not scanned. A `«...»` identifier is emitted as its bare name, so an escaped
    name such as `debug.«skipKernelTC»` is still seen."""
    out, i, n = [], 0, len(text)
    stack = []  # for each open interpolated string, the enclosing brace depth
    mode, depth = 'code', 0
    while i < n:
        c = text[i]
        if mode == 'istr':
            if c == '\\':
                i += 2
            elif c == '"':
                out.append('"')
                mode, depth = 'code', stack.pop()
                i += 1
            elif c == '{':
                out.append('{')
                stack.append('istr')
                mode, depth = 'code', 0
                i += 1
            else:
                i += 1
            continue
        if text.startswith('/-', i):
            level, i = 1, i + 2
            while i < n and level:
                if text.startswith('/-', i):
                    level, i = level + 1, i + 2
                elif text.startswith('-/', i):
                    level, i = level - 1, i + 2
                else:
                    i += 1
            continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
            continue
        raw = re.match(r'r(#*)"', text[i:]) if c == 'r' and not _ident_before(text, i) else None
        char = CHAR_LIT.match(text, i) if c == "'" and not _ident_before(text, i) else None
        if raw:
            close = '"' + raw.group(1)
            j = text.find(close, i + raw.end())
            out.append(' __raw_string__ ')
            i = n if j < 0 else j + len(close)
        elif c == '"' and i > 1 and text[i - 1] == '!' and text[i - 2] in 'smf' \
                and not _ident_before(text, i - 2):
            out.append('"')
            stack.append(depth)
            mode = 'istr'
            i += 1
        elif c == '"':
            start = i = i + 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            out.append(' __brace_string__ ' if '{' in text[start:i] else '""')
            i += 1
        elif c == '\u00ab':
            j = text.find('\u00bb', i + 1)
            j = n if j < 0 else j
            out.append(' ' + text[i + 1:j] + ' ')
            i = j + 1
        elif char:
            out.append("' '")
            i = char.end()
        elif c == '}' and depth == 0 and stack and stack[-1] == 'istr':
            stack.pop()
            mode = 'istr'
            i += 1
        else:
            depth += (c == '{') - (c == '}')
            out.append(c)
            i += 1
    return ''.join(out)


def sources():
    ok, count = True, 0
    if (FORMAL / 'lakefile.lean').exists():
        print('formal/lakefile.lean exists; Lake would use it instead of the owned lakefile.toml')
        ok = False
    tracked = subprocess.run(['git', 'ls-files', '--', '.lake'], cwd=FORMAL, check=True,
                             capture_output=True, text=True).stdout.split()
    for name in tracked:
        print(f'formal/{name} is committed; Lake would replay it instead of building the source')
        ok = False
    locked = {p.resolve() for p in statement_files()}
    lean_files = []
    # Walk without following links, so every file Lake could compile is read:
    # a symlink or a nested `.lake` directory could hide a module from the scan.
    for top, dirs, files in os.walk(FORMAL, followlinks=False):
        here = Path(top)
        if here == FORMAL and '.lake' in dirs:
            dirs.remove('.lake')
        for name in dirs + files:
            entry = here / name
            if entry.is_symlink():
                print(f'{entry.relative_to(ROOT)} is a symlink; the scan does not follow links')
                ok = False
            elif name == '.lake':
                print(f'{entry.relative_to(ROOT)} is a nested .lake directory')
                ok = False
        dirs[:] = [d for d in dirs if not (here / d).is_symlink() and d != '.lake']
        lean_files += [here / f for f in files if f.endswith('.lean') and not (here / f).is_symlink()]
    for path in sorted(lean_files):
        rel = path.relative_to(FORMAL)
        count += 1
        code = strip_comments(path.read_text())
        found = list(BANNED.finditer(code))
        if path.resolve() not in locked:
            found += (BRACE_STRING if rel.as_posix() in META_EXEMPT else META).finditer(code)
        for m in found:
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
