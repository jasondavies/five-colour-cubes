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
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def main():
    listed = set(git('ls-files', '-z', '--cached', '--others', '--exclude-standard').decode().rstrip('\0').split('\0'))
    deleted = set(git('ls-files', '-z', '--deleted').decode().rstrip('\0').split('\0')) - {''}
    names = sorted(listed - deleted - {''})
    base = git('rev-parse', 'HEAD').decode().strip()
    base_files = set(git('ls-tree', '-rz', '--name-only', base).decode().rstrip('\0').split('\0')) - {''}
    omitted = sorted((base_files - set(names)) | deleted)
    if omitted:
        print('Omitting tracked source files from the review snapshot:', file=sys.stderr)
        for name in omitted:
            print(f'  {name!r}', file=sys.stderr)
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
    manifest = json.loads(payload['lake-manifest.json'])
    dependencies = {}
    with tempfile.TemporaryDirectory(prefix='q5-review-') as temp:
        for entry in manifest['packages']:
            if entry['name'] not in ('colour_cubes_core',):
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
        source_files=hashes, omitted_tracked_files=omitted, project_dependencies=dependencies,
        formal_status='Complete physical Lean proof; full external comparator pass unconfirmed.'), indent=2)+'\n').encode()
    payload['REVIEW.txt'] = b"""Five-colour cube threshold: fixed review snapshot

REVIEW.json identifies the base Git revision, exact source snapshot and pinned
project dependencies. SHA256SUMS authenticates file integrity, not mathematical
correctness. This snapshot may include changes after the base revision.
REVIEW.json records omitted tracked files, including staged and unstaged deletions;
the packager also reports their paths on standard error.

From the extracted directory:
  sha256sum -c SHA256SUMS
  python3 -S scripts/bootstrap_review.py
  lake exe cache get
  make check WORKERS=2
  make small-replay WORKERS=2

Lean 4.35.0, Git, Python 3.12+, Make and a C++20/OpenMP compiler are required.
Only the toolchain and public mathlib dependencies need network access. The shared
colour-cubes-core dependency is bundled at its exact pinned Git revision.

Checked conditional upper-bound theorem:
  FiveColour.Physical.threshold_of_integer_root_exclusions
  lake build FiveColour.CaseProblem
Unconditional physical threshold and sharpness (after generating replay):
  FiveColour.Packed.ProjectedChunks.threshold15
  FiveColour.Packed.ProjectedChunks.sharpThreshold15
  lake build FiveColour.ProjectedChunks.Threshold
Physical lower-bound theorem:
  FiveColour.Physical.lower_bound
  lake build FiveColour.LowerBound
Cuboid classification (conditional on the corner threshold):
  FiveColour.Physical.box_frame_threshold_iff
  FiveColour.Physical.box_threshold_iff
  lake build FiveColour.BoxThresholds
Unconditional cuboid, larger-cube and support conclusions (after replay):
  FiveColour.Puzzle.box_frame_threshold
  FiveColour.Puzzle.complete_box_threshold
  FiveColour.Puzzle.frame_bound
  FiveColour.Puzzle.frame_threshold
  FiveColour.Puzzle.full_cube
  FiveColour.Puzzle.full_cube27
  FiveColour.Puzzle.complete_cube_threshold
  FiveColour.Puzzle.support_threshold
  make check-extensions
Complete lists of audited declarations: Audit.lean and ExtensionsAudit.lean
  python3 -S scripts/audit_lean.py

The 105-case input selection is data/lean-small-replay-cases.json. The small
replay also checks its aggregate's agreement with the integer root models.
The complete physical proof has passed. Reproduce its full replay with:
  make projected-replay-data WORKERS=2
  make projected-replay WORKERS=2
  make check-extensions
  make comparator

No publication or Palomar submission is asserted. See README.md and the paper
for the physical theorem statements and the scope of comparator checking.
"""
    payload['SHA256SUMS'] = ''.join(f'{hashlib.sha256(data).hexdigest()}  {name}\n'
        for name, data in sorted(payload.items())).encode()
    destination = ROOT / 'build/review'
    destination.mkdir(parents=True, exist_ok=True)
    prefix = f'five-colour-cubes-review-{source_id[:12]}'
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
