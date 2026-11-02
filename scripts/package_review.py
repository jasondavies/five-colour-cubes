#!/usr/bin/env python3
"""Freeze the current source snapshot and exact project dependencies for review.

The archive is identified by checksums, not a claim that a dirty tree equals HEAD.
Only tracked and nonignored source files enter; build products/logs are excluded.
Pinned project dependencies are Git bundles, so their exact revisions remain
verifiable and no access to their GitHub repositories is needed.
"""
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def main():
    names = sorted(set(git('ls-files', '-z', '--cached', '--others', '--exclude-standard').decode().rstrip('\0').split('\0')))
    payload, modes = {}, {}
    for name in names:
        path = ROOT / name
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f'Expected a regular source file: {name}')
        payload[name] = path.read_bytes()
        modes[name] = 0o755 if path.stat().st_mode & 0o111 else 0o644
    hashes = {name: hashlib.sha256(data).hexdigest() for name, data in payload.items()}
    source_id = hashlib.sha256(json.dumps({name: [hashes[name], modes[name]] for name in names},
                                        sort_keys=True).encode()).hexdigest()
    base = git('rev-parse', 'HEAD').decode().strip()
    manifest = json.loads(payload['lake-manifest.json'])
    dependencies = {}
    with tempfile.TemporaryDirectory(prefix='q5-review-') as temp:
        for entry in manifest['packages']:
            if entry['name'] not in ('macmahon_four_to_three', 'macmahon_min_universal_sets'):
                continue
            source = ROOT / '.lake/packages' / entry['name']
            actual = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
            if actual != entry['rev']:
                raise SystemExit(f'Wrong dependency revision: {entry["name"]}')
            subprocess.run(['git', '-C', str(source), 'diff', '--quiet', 'HEAD'], check=True)
            bundle = Path(temp) / f'{entry["name"]}.bundle'
            subprocess.run(['git', '-C', str(source), 'bundle', 'create', str(bundle), 'HEAD'], check=True)
            name = f'dependencies/{bundle.name}'
            payload[name] = bundle.read_bytes()
            dependencies[entry['name']] = entry['rev']
    payload['REVIEW.json'] = (json.dumps(dict(base_git_revision=base, source_snapshot_sha256=source_id,
        identification='Exact source snapshot is identified by checksums; it may differ from the base Git revision.',
        source_files=hashes, project_dependencies=dependencies,
        formal_status='Full Lean archive replay and unconditional threshold comparator pending.'), indent=2)+'\n').encode()
    payload['REVIEW.txt'] = b"""Five-colour cube threshold: fixed review snapshot

REVIEW.json identifies the base Git revision, exact source snapshot and pinned
project dependencies. SHA256SUMS authenticates file integrity, not mathematical
correctness. This snapshot may include changes after the base revision.

From the extracted directory:
  sha256sum -c SHA256SUMS
  python3 -S scripts/bootstrap_review.py
  lake exe cache get
  make check WORKERS=2
  make small-replay WORKERS=2

Lean 4.35.0, Git, Python 3.12+, Make and a C++20/OpenMP compiler are required.
Only the toolchain and public mathlib dependencies need network access. The two
MacMahon project dependencies are bundled at their exact pinned Git revisions.

Checked conditional upper-bound theorem:
  FiveColour.Physical.threshold_of_integer_root_exclusions
  lake build FiveColour.CaseProblem
Preferred projected conditional sharp-threshold theorem:
  FiveColour.Packed.Projected.sharp_threshold_of_exclusions
  lake build FiveColour.ProjectedBridge
Physical lower-bound theorem:
  FiveColour.Physical.lower_bound
  lake build FiveColour.LowerBound
Complete list of audited declarations: Audit.lean
  python3 -S scripts/audit_lean.py

The 105-case input selection is data/lean-small-replay-cases.json. The small
replay also checks its aggregate's agreement with the integer root models.
Full replay is separate and remains pending:
  make projected-replay-data WORKERS=2
  make projected-replay WORKERS=2
  make comparator

No publication or Palomar submission is asserted. See README.md and the paper
for the distinction between the C++ certificate proof and partial formalisation.
"""
    payload['SHA256SUMS'] = ''.join(f'{hashlib.sha256(data).hexdigest()}  {name}\n'
        for name, data in sorted(payload.items())).encode()
    destination = ROOT / 'build/review'
    destination.mkdir(parents=True, exist_ok=True)
    prefix = f'macmahon-five-colour-threshold-review-{source_id[:12]}'
    output = destination / f'{prefix}.tar.gz'
    with output.open('wb') as raw:
        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as zipped:
            with tarfile.open(fileobj=zipped, mode='w') as archive:
                for name, data in sorted(payload.items()):
                    info = tarfile.TarInfo(f'{prefix}/{name}')
                    info.size, info.mode, info.mtime = len(data), modes.get(name, 0o644), 0
                    archive.addfile(info, io.BytesIO(data))
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    output.with_name(output.name+'.sha256').write_text(f'{digest}  {output.name}\n')
    print(output)
    print(f'SHA256 {digest}')


if __name__ == '__main__':
    main()
