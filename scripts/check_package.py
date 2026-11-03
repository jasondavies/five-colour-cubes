#!/usr/bin/env python3
"""Check source hygiene, fixed dependency revisions and packaged input counts."""
import hashlib,json,re,tarfile,tomllib
from pathlib import Path
root=Path(__file__).resolve().parents[1]
config=tomllib.loads((root/'lakefile.toml').read_text())
manifest=json.loads((root/'lake-manifest.json').read_text())
packages={p['name']:p for p in manifest['packages']}
assert {d['name'] for d in config['require']} == {'mathlib', 'colour_cubes_core'}
assert not {'macmahon_min_universal_sets', 'macmahon_four_to_three'} & packages.keys()
assert re.fullmatch('[0-9a-f]{40}', packages['colour_cubes_core']['rev'])
for dep in config['require']:
 assert packages[dep['name']]['inputRev']==dep['rev']
 assert packages[dep['name']]['url']==dep['git']
assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
for path in [*(root/'FiveColour').rglob('*.lean'), root/'Solution.lean']:
 if 'ReplayChunks' in path.parts:continue
 assert not re.search(r'\bsorry\b|\bnative_decide\b|^\s*axiom\s',path.read_text(),re.M),path
# Statement holes are confined to the standalone challenge, never imported by proofs.
challenge=(root/'Challenge.lean').read_text()
assert re.findall(r'^(?:public )?import (.+)$',challenge,re.M)==['Mathlib']
comparison=json.loads((root/'comparator.json').read_text())
assert len(re.findall(r':= by sorry',challenge))==len(comparison['theorem_names'])==5
for path in [*(root/'FiveColour').rglob('*.lean'),root/'FiveColour.lean',root/'Solution.lean']:
 assert not re.search(r'^(?:public )?import Challenge\b',path.read_text(),re.M),path
rows=(root/'data/q5-threshold-cases-size15.txt').read_text().splitlines()
assert int(rows[0])==len(rows)-1==357
with tarfile.open(root/'data/q5-certificates.tar.gz') as archive:
 members=archive.getmembers()
 assert len(members)==357 and {m.name for m in members}=={f'case-{i}.q5p' for i in range(357)}
 for m in members:
  assert m.isfile()
  i=int(m.name[5:-4]);raw=archive.extractfile(m).read()
  assert raw[:160]==b'Q5P2'+bytes(map(int,rows[i+1].split()))
assert hashlib.sha256((root/'data/q5-certificates.tar.gz').read_bytes()).hexdigest()=='2792f86f9b87bc231aafe94679b9abd90b28163748ba7821e00371cd7699d1a3'
print('Package sources, pins, 357 headers and archived certificate hash checked.')
