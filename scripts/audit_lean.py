#!/usr/bin/env python3
"""Audit the default package's named theorems; fail on missing reports or unexpected axioms."""
from pathlib import Path
import argparse
import re
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--file', default='Audit.lean', help='Lean file listing the audited declarations')
args = parser.parse_args()
expected = re.findall(r'^#print axioms (\S+)$', (root / args.file).read_text(), re.M)
result = subprocess.run(['lake', 'env', 'lean', args.file], cwd=root, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end='')
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if (result.returncode or not expected or [name for name, _ in reports] != expected
        or any({s.strip() for s in axioms.split(',') if s.strip()} - allowed
               for _, axioms in reports)):
    raise SystemExit('Axiom audit failed')
print(f'Audited {len(reports)} theorems; only standard axioms occur.')
