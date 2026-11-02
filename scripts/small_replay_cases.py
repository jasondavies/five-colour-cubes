#!/usr/bin/env python3
"""Reproduce the fixed input selection of all certificates with <=500 instructions.

This manifest specifies mathematical inputs, not a runtime verification log.
Lean replay is a separate check; no acceptance claim follows from this script.
"""
import argparse
import hashlib
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def selection():
    archive = ROOT / 'data/q5-certificates.tar.gz'
    selected = []
    with tarfile.open(archive) as tar:
        for i in range(357):
            raw = tar.extractfile(f'case-{i}.q5p').read()
            assert raw[:4] == b'Q5P2'
            position, pending, commands = 160, 1, 0
            while pending:
                op = raw[position]
                assert op in (0, 1, 2)
                position += 3 if op == 1 else 2
                pending += 1 if op == 1 else (-1 if op == 0 else 0)
                commands += 1
            assert position == len(raw)
            if commands <= 500:
                selected.append(dict(case=i, commands=commands))
    assert len(selected) == 105
    return dict(archive='q5-certificates.tar.gz',
                archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                maximum_instructions=500, cases=selected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'data/lean-small-replay-cases.json'
    text = json.dumps(selection(), indent=2) + '\n'
    if args.check:
        assert path.read_text() == text, 'Small-case selection differs from archive'
    else:
        path.write_text(text)
    print('Checked selection of all 105 certificates with at most 500 instructions.')


if __name__ == '__main__':
    main()
