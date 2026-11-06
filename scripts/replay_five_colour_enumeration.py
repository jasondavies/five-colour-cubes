#!/usr/bin/env python3
"""Bounded-concurrency Lean replay of the 349 classification roots.

Lake validates cached dependencies. --roots-only checks selected root proofs,
not the physical classification or its axiom audit. Every started run records
its terminal status, including failures during initial setup or metadata checks.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time
from verification_state import dependency_state, environment_state
from verify_full import source_state

ROOT = Path(__file__).resolve().parents[1]


def write_json(path, value):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def terminate(child):
    if child.poll() is not None:
        return
    try:
        os.killpg(child.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        child.wait(timeout=10)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        child.wait()


def replay_case(root, logs, row, cancelled):
    i = row['case']
    start = time.monotonic()
    if cancelled.is_set() or (logs/'STOP').exists():
        return {'case': i, 'exit_code': 125, 'seconds': 0, 'commands': row['commands']}
    with (logs/f'case-{i}.log').open('w') as out:
        child = subprocess.Popen(['lake', 'build', f'FiveColour.EnumerationChunks.Case{i}'],
                                 cwd=root, stdout=out, stderr=subprocess.STDOUT,
                                 start_new_session=True)
        try:
            while child.poll() is None:
                if cancelled.is_set() or (logs/'STOP').exists():
                    terminate(child)
                    break
                try:
                    child.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    pass
        finally:
            terminate(child)
    return {'case': i, 'exit_code': child.returncode,
            'seconds': round(time.monotonic()-start, 2), 'commands': row['commands']}


def run_verification(root, logs, rows, selected, workers, full):
    started = time.monotonic()
    done = {}
    record = {'status': 'running', 'stage': 'collecting verification metadata',
              'started_utc': datetime.now(timezone.utc).isoformat(),
              'workers': workers, 'total': len(selected), 'requested': selected,
              'scope': 'complete physical classification and axiom audit' if full else 'selected root proofs only',
              'external_comparator': 'not run'}

    def save():
        record.update(elapsed_seconds=round(time.monotonic()-started, 2),
                      passed=sum(r['exit_code'] == 0 for r in done.values()),
                      failed=sum(r['exit_code'] != 0 for r in done.values()))
        write_json(logs/'record.json', record)
        write_json(logs/'progress.json', {
            k: v for k, v in record.items()
            if k not in {'source_sha256', 'dependencies', 'environment'}
        } | {'results': sorted(done.values(), key=lambda r: r['case'])})

    def stage(name):
        record['stage'] = name
        save()

    save()
    try:
        if full:
            inputs, deleted = source_state()
            dependencies = dependency_state(root)
            environment = environment_state(root, dict(os.environ), workers)
            record.update(source_sha256=inputs, deleted_tracked_files=deleted,
                          dependencies=dependencies, environment=environment)
        stage('building enumeration infrastructure')
        with (logs/'initial.log').open('w') as out:
            subprocess.run(['lake', 'build', 'FiveColour.EnumerationRoot'], cwd=root,
                           stdout=out, stderr=subprocess.STDOUT, check=True)
        stage('running roots')
        cancelled = threading.Event()
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures = [pool.submit(replay_case, root, logs, rows[i], cancelled)
                       for i in sorted(selected, key=lambda i: -rows[i]['commands'])]
            try:
                for future in as_completed(futures):
                    result = future.result()
                    done[result['case']] = result
                    save()
                    print(f'{len(done)}/{len(selected)} root {result["case"]}: '
                          f'{"PASS" if result["exit_code"] == 0 else "FAIL"} '
                          f'({result["seconds"]}s)', flush=True)
            except BaseException:
                cancelled.set()
                for future in futures:
                    future.cancel()
                raise
        if any(r['exit_code'] for r in done.values()):
            raise RuntimeError('one or more root proofs failed')
        if full:
            stage('building physical classification')
            with (logs/'aggregate.log').open('w') as out:
                subprocess.run(['lake', 'build', 'FiveColour.ClassificationSubmission'], cwd=root,
                               stdout=out, stderr=subprocess.STDOUT, check=True)
            stage('auditing classification axioms')
            with (logs/'audit.log').open('w') as out:
                subprocess.run(['python3', '-S', 'scripts/audit_lean.py', '--file', 'ClassificationAudit.lean'],
                               cwd=root, stdout=out, stderr=subprocess.STDOUT, check=True)
            stage('checking final source and dependency identity')
            if (source_state() != (inputs, deleted) or dependency_state(root) != dependencies
                    or environment_state(root, dict(os.environ), workers) != environment):
                raise RuntimeError('sources, dependencies or tools changed during verification')
            record.update(status='passed', stage='physical classification and axiom audit passed')
        else:
            record.update(status='partial_passed', stage='selected root proofs passed; physical aggregate not requested')
    except KeyboardInterrupt:
        record.update(status='interrupted', error='verification interrupted')
    except Exception as error:
        record.update(status='failed', error=f'{type(error).__name__}: {error}')
    finally:
        record['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    return 0 if record['status'] in {'passed', 'partial_passed'} else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=2)
    parser.add_argument('--roots-only', action='store_true')
    parser.add_argument('--cases', nargs='+', type=int)
    parser.add_argument('--wait', action='store_true', help='wait for an active replay before validating the cached result')
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('workers must be positive')
    os.environ['LEAN_NUM_THREADS'] = '1'
    rows = json.loads((ROOT/'FiveColour/EnumerationChunks/manifest.json').read_text())['cases']
    if [r['case'] for r in rows] != list(range(349)):
        parser.error('incomplete root manifest')
    selected = list(range(349)) if args.cases is None else args.cases
    if len(set(selected)) != len(selected) or any(i not in range(349) for i in selected):
        parser.error('invalid cases')
    logs = ROOT/'build/classification-replay'
    logs.mkdir(exist_ok=True, parents=True)
    with (logs/'run.lock').open('w') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | (0 if args.wait else fcntl.LOCK_NB))
        except BlockingIOError:
            parser.error('another enumeration replay owns this log directory')
        if (logs/'STOP').exists():
            parser.error('remove build/classification-replay/STOP to resume')
        return run_verification(ROOT, logs, rows, selected, args.workers,
                                not args.roots_only and args.cases is None)


if __name__ == '__main__':
    raise SystemExit(main())
