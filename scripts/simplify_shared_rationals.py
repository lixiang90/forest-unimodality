"""Share repeated literal rationals in generated Stage80 Cell definitions.

Dry run by default. Private transparent definitions preserve exact fractions;
Lean compilation and definitional equality checks are required after rewriting.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

RATIONAL = re.compile(rb'\(-?\d+/\d+\)')
CELL = re.compile(rb'(?m)^def cell(\d+) : Cell :=\r?\n(?P<body>.*?)(?=^theorem checked\1 :)', re.S | re.M)
MARKER = b'-- Shared literal rationals (simplify_shared_rationals.py).'


def simplify(source: bytes):
    if MARKER in source:
        return source, 0, 0
    if b'sharedRat' in source:
        raise ValueError('sharedRat name already present')
    matches = list(CELL.finditer(source))
    if not matches:
        raise ValueError('no generated Cell definitions found')
    for match in matches:
        if any(token in match['body'] for token in (b'--', b'/-', b'"')):
            raise ValueError('comments or strings in generated cell body')
    counts = Counter(value for match in matches for value in RATIONAL.findall(match['body']))
    newline = b'\r\n' if b'\r\n' in source else b'\n'
    names = {}
    declarations = []
    for value, count in counts.items():
        name = ('sharedRat%04d' % len(names)).encode()
        declaration = b'private def ' + name + b' : Rat := ' + value + newline
        if count >= 3 and count * (len(value) - len(name)) > len(declaration):
            names[value] = name
            declarations.append(declaration)
    if not names:
        return source, 0, 0
    occurrences = sum(counts[value] for value in names)
    pieces = [source[:matches[0].start()], MARKER + newline, *declarations, newline]
    cursor = matches[0].start()
    for match in matches:
        pieces.append(source[cursor:match.start('body')])
        pieces.append(RATIONAL.sub(lambda m: names.get(m[0], m[0]), match['body']))
        cursor = match.end('body')
    pieces.append(source[cursor:])
    updated = b''.join(pieces)
    # Lossless inversion checks every unchanged byte, not only numeric values.
    restored = updated.replace(MARKER + newline + b''.join(declarations) + newline, b'', 1)
    inverse = {name: value for value, name in names.items()}
    restored = re.sub(rb'\bsharedRat\d+\b', lambda m: inverse[m[0]], restored)
    assert restored == source
    return updated, len(names), occurrences


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', type=Path, nargs='+')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    for path in args.files:
        original = path.read_bytes()
        updated, definitions, occurrences = simplify(original)
        if args.write and definitions:
            path.write_bytes(updated)
        print(json.dumps(dict(path=str(path), definitions=definitions, occurrences=occurrences,
            before_bytes=len(original), after_bytes=len(updated),
            before_sha256=hashlib.sha256(original).hexdigest(),
            after_sha256=hashlib.sha256(updated).hexdigest(), written=args.write)))

if __name__ == '__main__':
    main()
