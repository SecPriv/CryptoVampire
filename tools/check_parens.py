#!/usr/bin/env python3
"""Check parenthesis balance of Scheme (.scm) source files (steel dialect).

Strings ("...") and line comments (; ...) are ignored, so it does not get
fooled by parentheses inside docstrings or comments.  Useful to validate the
`@doc`-wrapped definitions used in the `crates/*/scheme/libs/*.scm` libraries.

Usage:
    python3 tools/check_parens.py crates/indistinguishability/scheme/libs/*.scm

With --blocks it additionally reports the balance of each top-level `(@doc ...)`
form separately, naming the function it wraps -- handy when an `@doc` wrapper is
missing its closing parenthesis.
"""

import re
import sys


def strip(s):
    """Drop string literals and `;` line comments, keeping parens intact."""
    out = []
    i, n = 0, len(s)
    in_str = False
    while i < n:
        c = s[i]
        if c == ';' and not in_str:
            while i < n and s[i] != '\n':
                i += 1
            continue
        if c == '"':
            in_str = not in_str
            i += 1
            continue
        if in_str:
            i += 1
            continue
        out.append(c)
        i += 1
    return ''.join(out)


def net_balance(seg):
    """Count `(` minus `)` outside of strings/comments."""
    return seg.count('(') - seg.count(')')


def check(path):
    s = strip(open(path, encoding='utf-8').read())
    depth = 0
    line = 1
    bad = False
    for ch in s:
        if ch == '\n':
            line += 1
        elif ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth < 0:
                print(f"{path}: unbalanced `)` at line {line}")
                bad = True
                return False
    if depth != 0:
        print(f"{path}: UNBALANCED (missing {depth} `)`)")
        return False
    if not bad:
        print(f"{path}: OK")
    return True


def check_blocks(path):
    raw = open(path, encoding='utf-8').read()
    docs = [m.start() for m in re.finditer(r'\(@doc', raw)]
    if not docs:
        check(path)
        return
    ok = True
    for k, start in enumerate(docs):
        end = docs[k + 1] if k + 1 < len(docs) else len(raw)
        block = raw[start:end]
        m = re.search(r'\(define\s*\(?([^\s)]+)', block)
        name = m.group(1) if m else '?'
        net = net_balance(strip(block))
        # a full (@doc .. (define ..)) form must be balanced on its own
        flag = '' if net == 0 else f'   <-- missing {net} `)`' if net > 0 else f'   <-- {net} extra `)`'
        if net != 0:
            ok = False
        print(f"  @doc[{k:2d}] {name:26s} net={net:+d}{flag}")
    print("TOTAL:", net_balance(strip(raw)))


def main(argv):
    if not argv:
        print(__doc__)
        return 1
    if argv[0] == '--blocks':
        argv = argv[1:]
        for p in argv:
            check_blocks(p)
        return 0
    ok = all(check(p) for p in argv)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
