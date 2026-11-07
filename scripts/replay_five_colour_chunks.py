#!/usr/bin/env python3
"""Replay generated Lean cases with bounded concurrency and Lake's cache.

Logs and progress go under ignored build/, not into committed validation data.
A full run builds the physical sharp-threshold theorem and audits its axioms.
Interrupted runs can be resumed with the same command: Lake verifies its own
source/dependency traces before reusing a completed module.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import fcntl
import os
import signal
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=2)
    parser.add_argument('--cases', nargs='+', type=int, help='only these cases; omit to build and audit the aggregate')
    args = parser.parse_args()
    args.group = 'ProjectedChunks'
    # Bound each Lean process even when the driver is invoked directly.
    os.environ['LEAN_NUM_THREADS'] = '1'
    if args.workers < 1:
        parser.error('--workers must be positive')
    manifest = json.loads((LEAN / f'FiveColour/{args.group}/manifest.json').read_text())
    available = {row['case']: row for row in manifest['cases']}
    selected = list(available) if args.cases is None else args.cases
    if len(set(selected)) != len(selected) or any(c not in available for c in selected):
        parser.error('case selection is absent from the generated manifest or contains duplicates')
    count = 279
    if args.cases is None and sorted(available) != list(range(count)):
        parser.error(f'full threshold replay requires exactly cases 0 through {count-1}')
    endpoint = 'Threshold'
    if args.cases is None and not (LEAN / f'FiveColour/{args.group}/{endpoint}.lean').is_file():
        parser.error('aggregate link is missing; run make replay-data')
    logs = ROOT / 'build/five-colour-chunks' / args.group
    logs.mkdir(parents=True, exist_ok=True)
    lock = (logs / 'run.lock').open('w')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        parser.error('another replay runner owns this log directory')
    stop = logs / 'STOP'
    if stop.exists():
        parser.error(f'remove {stop} to resume; it requests that workers stop')
    started = time.monotonic()
    records = {}

    def progress(status):
        value = {'status': status, 'module_group': args.group, 'requested': selected,
                 'workers': args.workers, 'cached_aggregate': cached, 'elapsed_seconds': round(time.monotonic()-started, 2),
                 'passed': sum(row['exit_code'] == 0 for row in records.values()),
                 'failed': sum(row['exit_code'] != 0 for row in records.values()),
                 'results': sorted(records.values(), key=lambda row: row['case'])}
        tmp = logs / 'progress.tmp'
        tmp.write_text(json.dumps(value, indent=2) + '\n')
        tmp.replace(logs / 'progress.json')

    def replay(case):
        begin = time.monotonic()
        if stop.exists():
            return {'case': case, 'exit_code': 125, 'seconds': 0, 'commands': available[case]['commands']}
        with (logs / f'case-{case}.log').open('w') as stream:
            child = subprocess.Popen(['lake', 'build', f'FiveColour.{args.group}.Case{case}'],
                                     cwd=LEAN, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            while child.poll() is None:
                if stop.exists():
                    try:
                        os.killpg(child.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        child.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL)
                        child.wait()
                    break
                try:
                    child.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    pass
        return {'case': case, 'exit_code': child.returncode,
                'seconds': round(time.monotonic()-begin, 2), 'commands': available[case]['commands']}

    cached = False
    if args.cases is None:
        # Lake validates source/dependency traces. Mere artifact existence is
        # never acceptance, and --no-build cannot silently rebuild serially.
        with (logs / 'cache-check.log').open('w') as stream:
            cached = subprocess.run(
                ['lake', '--no-build', 'build', 'FiveColour.ProjectedChunks.Threshold'],
                cwd=LEAN, stdout=stream, stderr=subprocess.STDOUT).returncode == 0
    if cached:
        records.update({case: {'case': case, 'exit_code': 0, 'seconds': 0,
                               'commands': available[case]['commands'],
                               'validation': 'Lake aggregate dependency traces'} for case in selected})
        print('Lake validated the cached complete threshold and all 279 cases.', flush=True)
    else:
        shared = ['FiveColour.PackedCalibration', 'FiveColour.PackedPruning', 'FiveColour.PackedFast']
        if args.cases is None:
            shared.append('FiveColour.ProjectedBridge')
        subprocess.run(['lake', 'build', *shared], cwd=LEAN, check=True)
        progress('running')
        # Check cached artifacts first, then schedule large fresh cases to reduce
        # the tail. Lake still verifies dependency traces for every apparent hit.
        def priority(case):
            artifact = LEAN / f'.lake/build/lib/lean/FiveColour/{args.group}/Case{case}.olean'
            return (not artifact.exists(), -available[case]['commands'])
        ordered = sorted(selected, key=priority)
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            jobs = {pool.submit(replay, case): case for case in ordered}
            for future in as_completed(jobs):
                row = future.result()
                records[row['case']] = row
                progress('running')
                print(f"{len(records)}/{len(selected)} case {row['case']}: "
                      f"{'PASS' if row['exit_code'] == 0 else 'FAIL'} ({row['seconds']}s)", flush=True)
    if any(row['exit_code'] for row in records.values()):
        progress('stopped' if stop.exists() else 'failed')
        raise SystemExit(1)
    if args.cases is not None:
        progress('selected cases passed; aggregate not requested')
        return
    if not cached:
        progress('building physical threshold')
        with (logs / 'aggregate.log').open('w') as stream:
            result = subprocess.run(['lake', 'build', 'FiveColour.ProjectedChunks.Threshold'],
                                    cwd=LEAN, stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            progress('threshold assembly failed')
            raise SystemExit(1)
    audit = subprocess.run(['lake', 'env', 'lean', f'FiveColour/{args.group}/Audit.lean'],
                           cwd=LEAN, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / 'audit.log').write_text(audit.stdout)
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit.stdout)
    namespace = f'FiveColour.Packed.{args.group}'
    expected = ['FiveColour.Packed.Chunks.check_sound', 'FiveColour.Packed.Fast.check_sound',
                f'{namespace}.all_excluded']
    expected += [f'{namespace}.threshold15', f'{namespace}.sharpThreshold15']
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if audit.returncode or [name for name, _ in reports] != expected or any(
            {name.strip() for name in report.split(',') if name.strip()} - allowed for _, report in reports):
        progress('axiom audit failed')
        raise SystemExit(1)
    progress('physical sharp threshold proved and axiom audit passed')
    print(audit.stdout, end='')


if __name__ == '__main__':
    main()
