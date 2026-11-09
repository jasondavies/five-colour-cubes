#!/usr/bin/env python3
"""Compare publication proof inputs with a passed record, without rerunning proofs.

Scope: Lean sources, mathematical data (including text root ledgers), toolchain
and dependency pins, Lake configuration and comparator configuration. Editorial
files and verification scripts are outside this identity check.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path


def is_proof_input(name):
    return (name.endswith('.lean') or
            (name.startswith('data/') and name not in {
                'data/README.md', 'data/classification-certificates.txt'}) or
            name in {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                     'comparator.json'})


def source_names(root):
    checkout = subprocess.run(['git', 'rev-parse', '--show-toplevel'], cwd=root,
                              capture_output=True, text=True)
    if checkout.returncode == 0 and Path(checkout.stdout.strip()).resolve() == root.resolve():
        return set(subprocess.check_output(
            ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'],
            cwd=root).decode().strip('\0').split('\0'))
    # Also works in extracted archives; omit build products and dependency caches.
    return {p.relative_to(root).as_posix() for p in root.rglob('*')
            if p.is_file() and not {'.git', '.lake', 'build', '__pycache__'} &
            set(p.relative_to(root).parts)}


def check_sources(root, record, names):
    if record.get('status') != 'passed':
        raise ValueError('publication record is not passed')
    manifest = record['source_sha256']
    expected = {name for name in manifest if is_proof_input(name)}
    if not expected:
        raise ValueError('publication record has no proof inputs')
    actual = {name for name in names if is_proof_input(name)}
    errors = [f'unrecorded: {name}' for name in sorted(actual - expected)]
    for name in sorted(expected):
        path = Path(name)
        if path.is_absolute() or '..' in path.parts:
            raise ValueError('record contains a non-relative source path')
        path = root / path
        if name not in actual or not path.is_file():
            errors.append(f'missing: {name}')
        elif path.is_symlink():
            errors.append(f'symlink: {name}')
        elif hashlib.sha256(path.read_bytes()).hexdigest() != manifest[name]:
            errors.append(f'changed: {name}')
    return len(expected), errors


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path,
                        default=root / 'verification/optimized-comparator.json')
    args = parser.parse_args()
    count, errors = check_sources(root, json.loads(args.record.read_text()), source_names(root))
    if errors:
        print('\n'.join(errors))
        return 1
    print(f'Publication identity passed: {count} proof inputs match the record.')
    print('Scope: Lean, mathematical data, toolchain/dependency pins and build/comparator configuration.')
    print('This checks source identity; it does not execute verification.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
