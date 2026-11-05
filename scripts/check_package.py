#!/usr/bin/env python3
"""Check source hygiene, fixed dependency revisions and packaged input counts."""
import hashlib,json,re,subprocess,tarfile,tomllib
from pathlib import Path
root=Path(__file__).resolve().parents[1]
# Check exactly the distributable source set, including unused audit modules.
checkout = subprocess.run(['git','rev-parse','--show-toplevel'], cwd=root,
                          capture_output=True,text=True)
if checkout.returncode == 0 and Path(checkout.stdout.strip()).resolve() == root:
 source_names = set(subprocess.check_output(
   ['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=root
 ).decode().rstrip('\0').split('\0'))
elif (root/'REVIEW.json').exists():
 source_names = set(json.loads((root/'REVIEW.json').read_text())['source_files'])
else:
 source_names = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()
                 and not {'.git','.lake','build','__pycache__'} & set(p.relative_to(root).parts)}
for name in sorted(source_names):
 path=root/name
 if not path.is_file(): continue
 assert path.suffix not in {'.olean','.ilean','.a','.bc','.dll','.dylib','.o','.obj','.so','.trace'},name
 if path.suffix != '.lean': continue
 text=path.read_text()
 assert not path.is_symlink() and text.startswith('module\n'),name
 assert len(text.splitlines())<=10000,name
 for module in re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',text,re.M):
  if module == 'Solution' or module == 'FiveColour' or module.startswith('FiveColour.'):
   imported = module.replace('.','/')+'.lean'
   assert imported in source_names and (root/imported).is_file() and not (root/imported).is_symlink(),(name,module,'missing submitted source')
assert (root/'Challenge.lean').stat().st_size<=100*1024
assert len((root/'Challenge.lean').read_text().splitlines())<=1000
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
 assert not re.search(r'\bsorry\b|\bnative_decide\b|^\s*axiom\s',path.read_text(),re.M),path
# Statement holes are confined to the standalone challenge, never imported by proofs.
challenge=(root/'Challenge.lean').read_text()
assert re.findall(r'^(?:public )?import (.+)$',challenge,re.M)==['Mathlib']
comparison=json.loads((root/'comparator.json').read_text())
assert len(re.findall(r':= by sorry',challenge))==len(comparison['theorem_names'])==13
for path in [*(root/'FiveColour').rglob('*.lean'),root/'FiveColour.lean',root/'Solution.lean']:
 assert not re.search(r'^(?:public )?import Challenge\b',path.read_text(),re.M),path
rows=(root/'data/q5-projected-root-cases.txt').read_text().splitlines()
assert int(rows[0])==len(rows)-1==279
projection=json.loads((root/'data/q5-projected-root-manifest.json').read_text())
with tarfile.open(root/'data/q5-projected-certificates.tar.gz') as archive:
 members=archive.getmembers()
 assert len(members)==279 and {m.name for m in members}=={f'case-{i}.q5p' for i in range(279)}
 for m in members:
  assert m.isfile()
  i=int(m.name[5:-4]);raw=archive.extractfile(m).read()
  assert raw[:160]==b'Q5P2'+bytes(map(int,rows[i+1].split()))
  assert hashlib.sha256(raw).hexdigest()==projection['cases'][i]['certificate_sha256']
assert hashlib.sha256((root/'data/q5-projected-certificates.tar.gz').read_bytes()).hexdigest()==projection['projected_archive_sha256']
print('Package sources, pins, 279 headers and certificate hashes checked.')
