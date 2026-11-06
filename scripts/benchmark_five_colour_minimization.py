#!/usr/bin/env python3
"""Minimize copies of retained certificates and optionally benchmark them in Lean.

Everything generated stays under ignored build/certificate-minimization. The
production archive and replay modules are never rewritten. C++ acceptance is
only a search check: --measure kernel proves each selected root using the
unchanged Lean checker and audits its axioms. --measure export additionally
replays all concrete chunk-acceptance proofs in the standalone Lean kernel.
That export measurement isolates certificate execution; it is NOT the full
thirteen-claim Comparator or its complete soundness/geometry dependency closure.

Examples:
  python3 -S scripts/benchmark_five_colour_minimization.py --cases all
  python3 -S scripts/benchmark_five_colour_minimization.py --cases 16 19 --measure export
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import time

from generate_five_colour_chunks import generate

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'build/certificate-minimization'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases', nargs='+', default=['16', '19'])
    parser.add_argument('--passes', type=int, default=2)
    parser.add_argument('--trial-limit', type=int, default=4096)
    parser.add_argument('--measure', choices=['none', 'kernel', 'export'], default='none')
    parser.add_argument('--repeats', type=int, default=2)
    parser.add_argument('--label', default='pilot', help='output subdirectory under build/certificate-minimization')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', args.label):
        parser.error('label must contain only letters, digits, underscores and hyphens')
    destination = DEST / args.label
    if min(args.passes, args.trial_limit, args.repeats) < 1:
        parser.error('passes, trial limit and repeats must be positive')
    try:
        cases = list(range(279)) if args.cases == ['all'] else [int(c) for c in args.cases]
    except ValueError:
        parser.error('cases must be integers or the single word all')
    if len(set(cases)) != len(cases) or any(c not in range(279) for c in cases):
        parser.error('cases must be distinct integers from 0 through 278')
    targets = ['build/minimize_five_colour_certificate']
    if args.measure != 'none':
        targets.append('build/five_colour_chunks')
    subprocess.run(['make', *targets], cwd=ROOT, check=True)
    env = dict(os.environ, LEAN_NUM_THREADS='1',
               LEAN_PATH=str(destination) + (os.pathsep + os.environ['LEAN_PATH'] if os.environ.get('LEAN_PATH') else ''))
    if args.measure != 'none':
        subprocess.run(['lake', 'build', 'FiveColour.PackedCalibration',
                        'FiveColour.PackedChunks', 'FiveColour.PackedPruning'],
                       cwd=ROOT, env=env, check=True)
    destination.mkdir(parents=True, exist_ok=True)
    archive = ROOT / 'data/q5-projected-certificates.tar.gz'
    geometry = ROOT / 'data/five-colour-geometry.txt'
    case_file = ROOT / 'data/q5-projected-root-cases.txt'
    rows = [list(map(int, line.split())) for line in case_file.read_text().splitlines()[1:]]
    record = {
        'scope': 'Experimental certificate candidates; production proof unchanged. '
                 'Standalone timings cover chunk-acceptance proofs, not the full Comparator.',
        'settings': vars(args), 'cases': [], 'measurements': [],
        'inputs_sha256': {str(p.relative_to(ROOT)): digest(p) for p in [
            archive, geometry, case_file, Path(__file__),
            ROOT / 'src/minimize_five_colour_certificate.cpp',
            ROOT / 'src/check_five_colour_certificate.cpp',
            ROOT / 'src/five_colour_chunks.cpp',
            ROOT / 'scripts/generate_five_colour_chunks.py',
            ROOT / 'scripts/generate_five_colour_reduced.py',
            ROOT / 'scripts/generate_five_colour_packed.py',
            ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']},
    }

    def save():
        (destination / 'measurements.json').write_text(json.dumps(record, indent=2) + '\n')

    with tarfile.open(archive) as tar:
        for case in cases:
            folder = destination / f'case-{case}'
            folder.mkdir(exist_ok=True)
            original = folder / 'original.q5p'
            original.write_bytes(tar.extractfile(f'case-{case}.q5p').read())
            current = original
            passes = []
            for iteration in range(args.passes):
                candidate = folder / f'pass-{iteration}.q5p'
                result = subprocess.check_output([
                    str(ROOT / 'build/minimize_five_colour_certificate'),
                    str(geometry), str(case_file), str(current), str(case),
                    str(candidate), str(args.trial_limit)], cwd=ROOT, text=True)
                stats = json.loads(result)
                if candidate.read_bytes()[:160] != original.read_bytes()[:160]:
                    raise RuntimeError('candidate header changed')
                if stats['after'] > stats['before']:
                    raise RuntimeError('candidate grew')
                passes.append(stats)
                current = candidate
                if stats['before'] == stats['after']:
                    break
            summary = dict(case=case, before=passes[0]['before'], after=passes[-1]['after'],
                           passes=passes, candidate_sha256=digest(current))
            record['cases'].append(summary)
            save()
            print(json.dumps(summary), flush=True)
            if args.measure == 'none':
                continue
            variants = {}
            for mode, certificate in [('baseline', original), ('minimized', current)]:
                generated = folder / mode
                generated.mkdir(exist_ok=True)
                chunks = generated / 'chunks.tsv'
                subprocess.run([str(ROOT / 'build/five_colour_chunks'), str(geometry),
                                str(case_file), str(certificate), str(case), '128', str(chunks)],
                               check=True, capture_output=True)
                group = f'Minimization{case}{mode}'
                stats = generate(case, rows[case], chunks, 128, generated, group)
                source = (generated / f'Case{case}.lean').read_text().replace(
                    '@[expose] public section', '@[expose] public section\nset_option Elab.async false')
                endpoint = f'FiveColour.Packed.{group}.Case{case}.excludes'
                source += f'\n#print axioms {endpoint}\n'
                module = f'Benchmark{case}{mode}'
                path = destination / f'{module}.lean'
                path.write_text(source)
                variants[mode] = (path, module, endpoint, stats, generated)
            for repeat in range(args.repeats):
                for mode in (['baseline', 'minimized'] if repeat % 2 == 0 else ['minimized', 'baseline']):
                    path, module, endpoint, stats, generated = variants[mode]
                    log = generated / f'compile-{repeat}.log'
                    started = time.monotonic()
                    with log.open('w') as stream:
                        result = subprocess.run(['lake', 'env', 'lean', '-o',
                                                 str(destination / f'{module}.olean'), str(path)],
                                                cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
                    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log.read_text())
                    passed = (result.returncode == 0 and len(reports) == 1 and reports[0][0] == endpoint
                              and not ({a.strip() for a in reports[0][1].split(',') if a.strip()}
                                       - {'propext', 'Classical.choice', 'Quot.sound'}))
                    measurement = dict(stats, mode=mode, repeat=repeat, phase='complete certificate kernel compilation',
                                       seconds=time.monotonic()-started, passed=passed)
                    record['measurements'].append(measurement); save()
                    print(json.dumps(measurement), flush=True)
                    if not passed:
                        raise SystemExit(f'Kernel check or axiom audit failed: {log}')
                    if args.measure != 'export':
                        continue
                    names = [endpoint.removesuffix('excludes') + f'Part{i}.accepted'
                             for i in range(stats['chunks'])]
                    export = generated / 'acceptance.export.jsonl'
                    with export.open('w') as stream:
                        subprocess.run(['lake', 'env', 'leanexport', module, '--', *names],
                                       cwd=ROOT, env=env, stdout=stream, check=True)
                    started = time.monotonic()
                    log = generated / f'export-{repeat}.log'
                    with log.open('w') as stream:
                        result = subprocess.run(['lake', 'env', 'leanchecker', '--from-export', str(export)],
                                                cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
                    passed = result.returncode == 0 and 'Lean default kernel accepts the solution' in log.read_text()
                    measurement = dict(case=case, mode=mode, repeat=repeat,
                                       phase='standalone replay of all concrete chunk acceptances',
                                       seconds=time.monotonic()-started, passed=passed,
                                       export_bytes=export.stat().st_size, export_sha256=digest(export))
                    record['measurements'].append(measurement); save()
                    print(json.dumps(measurement), flush=True)
                    if not passed:
                        raise SystemExit(f'Standalone kernel replay failed: {log}')
    for name, value in record['inputs_sha256'].items():
        if digest(ROOT / name) != value:
            raise RuntimeError(f'Benchmark input changed during the run: {name}')
    record['input_stability'] = 'passed'
    save()


if __name__ == '__main__':
    main()
