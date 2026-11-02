#!/usr/bin/env python3
"""Replay generated Lean cases with bounded concurrency and Lake's cache.

Logs and progress go under ignored build/, not into committed validation data.
A successful run builds the aggregate exclusion theorem and audits its axioms.
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
    parser.add_argument('--group', choices=['Chunked', 'ReplayChunks'], default='ReplayChunks')
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--cases', nargs='+', type=int, help='only these cases; omit to build and audit the aggregate')
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('--workers must be positive')
    manifest = json.loads((LEAN / f'FiveColour/{args.group}/manifest.json').read_text())
    available = {row['case']: row for row in manifest['cases']}
    selected = list(available) if args.cases is None else args.cases
    if len(set(selected)) != len(selected) or any(c not in available for c in selected):
        parser.error('case selection is absent from the generated manifest or contains duplicates')
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
    # Build shared dependencies once before starting concurrent Lake processes.
    subprocess.run(['lake', 'build', 'FiveColour.PackedCalibration', 'FiveColour.PackedChunks'], cwd=LEAN, check=True)
    started = time.monotonic()
    records = {}

    def progress(status):
        value = {'status': status, 'module_group': args.group, 'requested': selected,
                 'workers': args.workers, 'elapsed_seconds': round(time.monotonic()-started, 2),
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
    progress('building aggregate')
    with (logs / 'aggregate.log').open('w') as stream:
        result = subprocess.run(['lake', 'build', f'FiveColour.{args.group}.All'],
                                cwd=LEAN, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        progress('aggregate failed')
        raise SystemExit(1)
    audit = subprocess.run(['lake', 'env', 'lean', f'FiveColour/{args.group}/Audit.lean'],
                           cwd=LEAN, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / 'audit.log').write_text(audit.stdout)
    reports = re.findall(r'depends on axioms:\s*\[([^]]*)\]', audit.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if audit.returncode or len(reports) != 2 or any(
            {name.strip() for name in report.split(',') if name.strip()} - allowed for report in reports):
        progress('axiom audit failed')
        raise SystemExit(1)
    progress('aggregate proved and axiom audit passed')
    print(audit.stdout, end='')


if __name__ == '__main__':
    main()
