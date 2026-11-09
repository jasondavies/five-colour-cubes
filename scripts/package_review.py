#!/usr/bin/env python3
"""Freeze the current source snapshot and exact project dependencies for review.

The archive is identified by checksums, not a claim that a dirty tree equals HEAD.
Only tracked and nonignored source files enter; build products/logs are excluded.
Pinned project dependencies are shallow Git bundles containing the exact commit
and its source tree. Bootstrap restores their boundary without fetching history.
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
            # Bundle only the pinned tree. A partial clone may deliberately lack
            # historical blobs; none are needed to reproduce this dependency.
            snapshot = Path(temp) / f'{entry["name"]}.git'
            subprocess.run(['git', 'init', '--bare', '--quiet', '--template=', str(snapshot)], check=True)
            objects = subprocess.check_output(
                ['git', '-C', str(source), 'rev-parse', '--path-format=absolute', '--git-path', 'objects'],
                text=True).strip()
            (snapshot / 'objects/info/alternates').write_text(objects + '\n')
            (snapshot / 'shallow').write_text(actual + '\n')
            subprocess.run(['git', '-C', str(snapshot), 'update-ref', 'refs/heads/snapshot', actual], check=True)
            subprocess.run(['git', '-C', str(snapshot), 'bundle', 'create', str(bundle),
                            'refs/heads/snapshot'], check=True)
            name = f'dependencies/{bundle.name}'
            payload[name] = bundle.read_bytes()
            dependencies[entry['name']] = entry['rev']
    payload['REVIEW.json'] = (json.dumps(dict(base_git_revision=base, source_snapshot_sha256=source_id,
        identification='Exact source snapshot is identified by checksums; it may differ from the base Git revision.',
        source_files=hashes, omitted_tracked_files=omitted, project_dependencies=dependencies,
        dependency_history='shallow bundles: pinned commit and complete source tree',
        formal_status='Complete physical Lean proof; see formalization.yaml for external comparison status.'), indent=2)+'\n').encode()
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
  make verify-full WORKERS=2

Lean 4.35.0, Git, Python 3.12+, Make and a C++20/OpenMP compiler are required.
Only the toolchain and public mathlib dependencies need network access. The shared
colour-cubes-core dependency is bundled at its exact pinned Git revision.

The archived README.md is the entry point for theorem statements, commands and
verification scope. formalization.yaml records the formalisation and external
comparison status. Audit.lean, ExtensionsAudit.lean, FiveColour/ProjectedChunks/Audit.lean and
ClassificationAudit.lean list their separately audited declarations.

make verify-full checks the threshold route and its extensions, and builds
Solution including the complete classification. Run the dedicated classification
checks as well:
  make check-classification-data WORKERS=2
  make classification-replay WORKERS=2
See README.md and data/classification-certificates.txt for their exact scope.
The external comparison is also a separate command:
  make comparator

The paper and FiveColour/README.md explain the mathematical and formal models.
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
