#!/usr/bin/env python3
"""Benchmark chunk sizes using fresh, kernel-checked replays of one certificate.

Generated sources and measurements stay in ignored build/. This never edits
production replay sources or imports their cached case proofs. Only shared
checker dependencies are reused. Runs are sequential, with one Lean thread;
the order alternates to reduce bias from changing background CPU load.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import time

from generate_five_colour_chunks import generate

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', type=int, default=120)
    parser.add_argument('--limits', nargs='+', type=int, default=[128, 256, 512])
    parser.add_argument('--cut-modes', nargs='+', choices=['auto', 'original', 'reduced'], default=['auto'])
    parser.add_argument('--repeats', type=int, default=3)
    args = parser.parse_args()
    if not 0 <= args.case < 279 or args.repeats < 1:
        parser.error('case must be 0..278 and repeats must be positive')
    if len(set(args.limits)) != len(args.limits) or any(not 1 <= x <= 1024 for x in args.limits):
        parser.error('limits must be distinct integers in 1..1024')
    destination = ROOT / 'build/replay-benchmark' / f'case-{args.case}'
    destination.mkdir(parents=True, exist_ok=True)
    subprocess.run(['make', 'build/five_colour_chunks'], cwd=ROOT, check=True)
    # This is a dependency build only; never schedule a production case replay.
    subprocess.run(['lake', 'build', 'FiveColour.PackedCalibration', 'FiveColour.PackedFast', 'FiveColour.PackedPruning'],
                   cwd=ROOT, check=True)
    rows = [list(map(int, line.split())) for line in
            (ROOT / 'data/q5-projected-root-cases.txt').read_text().splitlines()[1:]]
    with tarfile.open(ROOT / 'data/q5-projected-certificates.tar.gz') as archive:
        raw = archive.extractfile(f'case-{args.case}.q5p').read()
    certificate = destination / 'input.q5p'
    certificate.write_bytes(raw)
    variants = {}
    for limit, mode in [(limit, mode) for limit in args.limits for mode in args.cut_modes]:
        folder = destination / f'limit-{limit}-{mode}'
        folder.mkdir(exist_ok=True)
        chunks = folder / 'chunks.tsv'
        subprocess.run([str(ROOT / 'build/five_colour_chunks'),
                        str(ROOT / 'data/five-colour-geometry.txt'),
                        str(ROOT / 'data/q5-projected-root-cases.txt'),
                        str(certificate), str(args.case), str(limit), str(chunks)],
                       check=True, capture_output=True)
        group = f'Benchmark{limit}{mode}'
        stats = generate(args.case, rows[args.case], chunks, limit, folder, group, cut_mode=mode)
        source = folder / f'Case{args.case}.lean'
        text = source.read_text().replace('@[expose] public section',
            '@[expose] public section\nset_option Elab.async false\n'
            'set_option profiler true\nset_option profiler.threshold 1')
        text += f'\n#print axioms FiveColour.Packed.{group}.Case{args.case}.excludes\n'
        source.write_text(text)
        variants[limit, mode] = (source, stats, group)
    records = []
    environment = dict(os.environ, LEAN_NUM_THREADS='1')
    for repeat in range(args.repeats):
        order = list(variants) if repeat % 2 == 0 else list(variants)[::-1]
        for variant in order:
            source, stats, group = variants[variant]
            log = source.parent / f'run-{repeat}.log'
            timing = source.parent / f'run-{repeat}.time'
            started = time.monotonic()
            with log.open('w') as stream:
                result = subprocess.run(['/usr/bin/time', '-f', '%U %S %e %M', '-o', str(timing),
                                         'lake', 'env', 'lean', str(source)], cwd=ROOT,
                                        env=environment, stdout=stream, stderr=subprocess.STDOUT)
            elapsed = time.monotonic() - started
            output = log.read_text()
            reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
            expected = f'FiveColour.Packed.{group}.Case{args.case}.excludes'
            passed = result.returncode == 0 and len(reports) == 1 and reports[0][0] == expected
            if passed:
                passed = not ({a.strip() for a in reports[0][1].split(',') if a.strip()}
                              - {'propext', 'Classical.choice', 'Quot.sound'})
            record = dict(stats, requested_cut_mode=variant[1], repeat=repeat, wall_seconds=round(elapsed, 3), passed=passed)
            if result.returncode == 0:
                user, system, wall, rss = map(float, timing.read_text().split())
                record.update(cpu_seconds=round(user+system, 3), max_rss_kib=int(rss))
            records.append(record)
            (destination / 'measurements.json').write_text(json.dumps(records, indent=2)+'\n')
            print(json.dumps(record), flush=True)
            if not passed:
                raise SystemExit(f'Kernel replay or axiom audit failed; see {log}')
    print(f'Measurements: {destination / "measurements.json"}')


if __name__ == '__main__':
    main()
