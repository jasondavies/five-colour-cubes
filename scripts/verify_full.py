#!/usr/bin/env python3
"""Run the complete Lean proof route and retain a source-bound local record.

Lake validates cached artifacts. This is not a clean-build timing benchmark or
an external-kernel comparison. Records are ignored build outputs, suitable for
inclusion in a release alongside the exact source archive.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def source_hashes():
    # Include new source files as well as tracked files; missing tracked inputs
    # are errors, never silently omitted from a successful record.
    paths = git('ls-files', '--cached', '--others', '--exclude-standard', '-z')
    return {name: digest(ROOT / name) for name in sorted(set(
        os.fsdecode(p) for p in paths.split(b'\0') if p))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=2)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('--workers must be positive')
    started = datetime.now(timezone.utc)
    output = ROOT / 'build/verification' / started.strftime('%Y%m%dT%H%M%S.%fZ')
    output.mkdir(parents=True)
    inputs = source_hashes()
    record = {'status': 'running', 'started_utc': started.isoformat(),
              'git_commit': git('rev-parse', 'HEAD').decode().strip(),
              'git_status': git('status', '--porcelain').decode().splitlines(),
              'workers': args.workers, 'cache_policy': 'Lake dependency-trace validation',
              'external_comparator': 'not run', 'source_sha256': inputs, 'steps': []}

    def save():
        (output / 'record.json').write_text(json.dumps(record, indent=2) + '\n')

    save()
    env = dict(os.environ)
    env.setdefault('LEAN_NUM_THREADS', '1')
    record['build_threads'] = env['LEAN_NUM_THREADS']
    targets = ['check-code', 'check-lean', 'projected-replay-data',
               'projected-replay', 'check-extensions']
    try:
        for target in targets:
            command = ['make', target, f'WORKERS={args.workers}']
            print(f'Full verification: {target}', flush=True)
            with (output / f'{target}.log').open('w') as log:
                phase_env = dict(env, LEAN_NUM_THREADS='1') if target == 'projected-replay' else env
                child = subprocess.Popen(command, cwd=ROOT, env=phase_env, text=True,
                                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                for line in child.stdout:
                    log.write(line)
                    log.flush()
                    print(line, end='', flush=True)
                code = child.wait()
            record['steps'].append({'target': target, 'exit_code': code})
            save()
            if code:
                raise RuntimeError(f'{target} failed with exit code {code}')
        if source_hashes() != inputs:
            raise RuntimeError('source files changed during verification; rerun on frozen sources')
        generated = ROOT / 'FiveColour/ProjectedChunks'
        record['generated_sha256'] = {
            str(p.relative_to(ROOT)): digest(p)
            for p in sorted([*generated.rglob('*.lean'), generated / 'manifest.json'])}
        # The replay driver validates the exact endpoint axiom reports.
        for name in ['audit.log', 'progress.json']:
            src = ROOT / 'build/five-colour-chunks/ProjectedChunks' / name
            (output / f'projected-{name}').write_bytes(src.read_bytes())
        record['status'] = 'passed'
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        record['status'] = 'failed'
        record['error'] = str(error)
    finally:
        record['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print(f"Full verification {record['status']}: {output.relative_to(ROOT)}/record.json")
    return 0 if record['status'] == 'passed' else 1


if __name__ == '__main__':
    sys.exit(main())
