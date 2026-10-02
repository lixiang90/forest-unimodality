"""Collapse generated rational-valued lambdas whose every branch is identical.

Dry-run by default. The transformation matches only the exact generated syntax,
compares the rational literals byte-for-byte and preserves all other bytes.
Re-run Lean on changed modules and rebuild their downstream closure before
claiming a complete verification of the simplified branch.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

CONSTANT_LAMBDA = re.compile(
    rb'\(fun i=>if i\.val=\d+ then (?P<v>\(-?\d+(?:/\d+)?\))'
    rb'(?: else if i\.val=\d+ then (?P=v))* else (?P=v)\)')

def simplify(source: bytes):
    return CONSTANT_LAMBDA.subn(rb'(fun _ => \g<v>)', source)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', type=Path, nargs='+')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    for path in args.files:
        original = path.read_bytes()
        updated, count = simplify(original)
        if args.write and count:
            path.write_bytes(updated)
        print(json.dumps(dict(path=str(path), replacements=count,
            before_bytes=len(original), after_bytes=len(updated),
            before_sha256=hashlib.sha256(original).hexdigest(),
            after_sha256=hashlib.sha256(updated).hexdigest(), written=args.write)))

if __name__ == '__main__':
    main()
