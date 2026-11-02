#!/usr/bin/env python3
"""Audit the default package's ten named theorems; fail on unexpected axioms."""
from pathlib import Path
import re
import subprocess
root=Path(__file__).resolve().parents[1]
result=subprocess.run(['lake','env','lean','Audit.lean'],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print(result.stdout,end='')
reports=re.findall(r'depends on axioms:\s*\[([^]]*)\]',result.stdout)
allowed={'propext','Classical.choice','Quot.sound'}
if result.returncode or len(reports)!=10 or any({s.strip() for s in r.split(',') if s.strip()}-allowed for r in reports):
 raise SystemExit('Axiom audit failed')
