#!/usr/bin/env python3
"""Export bounded Q5P2 chunks with C++ and generate their Lean composition.

Python only serializes declarations; C++ computes checkpoint boxes. Both are
untrusted: Lean checks each chunk, each boundary, and the final composition.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
from generate_five_colour_packed import ROOT, RESULTS, cut

DEST = ROOT / 'FiveColour/Chunked'


def packed(counts):
    return sum(int(v) << (10 * i) for i, v in enumerate(counts))


def problem(row):
    _, m, _, goal, anchor, budget, *rest = row
    lo, hi = [0] * 75, rest[:75]
    lo[anchor] = hi[anchor] = m
    text = f'''def root : Box := ⟨{packed(lo)}, {packed(hi)}⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [{cut([], 0)}]
  else if r.val = 1 then [{cut(list(range(75)), goal)}]
  else if r.val = 2 then [{cut([i for i, b in enumerate(rest[75:]) if b], budget)}]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc
'''
    return text


def generate(case, row, path, limit, dest=DEST, group="Chunked"):
    dest.mkdir(parents=True, exist_ok=True)
    prefix = f'FiveColour.Packed.{group}.Case{case}'
    text = f'''module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace {prefix}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

'''
    text += problem(row)
    sizes = []
    for line in path.read_text().splitlines():
        ident, lo, hi, size, refs, proof = line.split('\t')
        ident, size = int(ident), int(size)
        refs = list(map(int, refs.split(','))) if refs else []
        if ident != len(sizes) or not 1 <= size <= limit or any(r >= ident or r < 0 for r in refs):
            raise ValueError('invalid chunk ordering or size')
        if len(lo) != 75 or len(hi) != 75 or any(v not in '01234567' for v in lo + hi):
            raise ValueError('invalid checkpoint bound')
        sizes.append(size)
        reference_value = '![' + ', '.join(f'Part{r}.root' for r in refs) + ']' if refs else 'Fin.elim0'
        text += f'''
namespace Part{ident}
def root : Box := ⟨{packed(lo)}, {packed(hi)}⟩
def references : Fin {len(refs)} → Box := {reference_value}
def proof : Chunks.Proof {len(refs)} := {proof}
theorem accepted : Chunks.check {row[3]} families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes {row[3]} families (references i) := by
'''
        if refs:
            text += '  intro i\n  fin_cases i\n'
            text += ''.join(f'  · exact Part{r}.excludes\n' for r in refs)
        else:
            text += '  intro i\n  exact Fin.elim0 i\n'
        text += f'''
theorem excludes : Chunks.Excludes {row[3]} families root :=
  Chunks.check_sound {row[3]} families families_valid references references_excluded proof root root_valid accepted
end Part{ident}
'''
    if not sizes:
        raise ValueError('empty chunk export')
    text += f'''
/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes {row[3]} families root := Part{len(sizes)-1}.excludes
end {prefix}
'''
    (dest / f'Case{case}.lean').write_text(text)
    return {'case': case, 'chunks': len(sizes), 'commands': sum(sizes),
            'largest_chunk': max(sizes), 'smallest_chunk': min(sizes), 'limit': limit}


def aggregate(dest, group, cases):
    namespace = f'FiveColour.Packed.{group}'
    text = 'module\n' + ''.join(f'public import FiveColour.{group}.Case{c}\n' for c in cases)
    text += f"@[expose] public section\nnamespace {namespace}\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n"
    text += f"def roots : Fin {len(cases)} → Box := ![" + ', '.join(f'Case{c}.root' for c in cases) + ']\n'
    text += f"def families : Fin {len(cases)} → Fin 78 → List Cut := ![" + ', '.join(f'Case{c}.families' for c in cases) + ']\n'
    text += 'theorem all_excluded : ∀ i, Chunks.Excludes 15 (families i) (roots i) := by\n  intro i\n  fin_cases i\n'
    text += ''.join(f'  · exact Case{c}.excludes\n' for c in cases)
    text += f'end {namespace}\n'
    (dest / 'All.lean').write_text(text)
    (dest / 'Audit.lean').write_text(f'module\nimport FiveColour.{group}.All\n#print axioms FiveColour.Packed.Chunks.check_sound\n#print axioms {namespace}.all_excluded\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument('--cases', nargs='+', type=int)
    scope.add_argument('--all', action='store_true', help='generate all cases into ignored ReplayChunks/')
    parser.add_argument('--limit', type=int, default=128)
    parser.add_argument('--workers', type=int, default=8, help='concurrent C++ exporters')
    args = parser.parse_args()
    if not 1 <= args.limit <= 1024 or args.workers < 1:
        parser.error('--limit must be 1..1024 and --workers must be positive')
    rows = [list(map(int, line.split())) for line in
            (RESULTS / 'q5-threshold-cases-size15.txt').read_text().splitlines()[1:]]
    cases = list(range(len(rows))) if args.all else (args.cases or [78, 326, 7])
    if len(set(cases)) != len(cases) or any(c < 0 or c >= len(rows) for c in cases):
        parser.error('case indices must be distinct and in range')
    group = 'ReplayChunks' if args.all else 'Chunked'
    dest = ROOT / 'FiveColour' / group
    subprocess.run(['make', 'build/five_colour_chunks'], cwd=ROOT, check=True)
    dest.mkdir(exist_ok=True)
    with tarfile.open(RESULTS / 'q5-certificates.tar.gz', 'r:gz') as archive:
        members = {Path(m.name).name: m for m in archive.getmembers() if m.isfile()}
        payloads = {case: archive.extractfile(members[f'case-{case}.q5p']).read() for case in cases}
    with tempfile.TemporaryDirectory(prefix='q5-chunks-') as temp:
        def export(case):
            raw = Path(temp) / f'case-{case}.q5p'
            raw.write_bytes(payloads[case])
            tsv = Path(temp) / f'chunks-{case}.tsv'
            subprocess.run([str(ROOT / 'build/five_colour_chunks'),
                            str(RESULTS / 'five-colour-geometry.txt'),
                            str(RESULTS / 'q5-threshold-cases-size15.txt'),
                            str(raw), str(case), str(args.limit), str(tsv)], check=True, capture_output=True)
            result = generate(case, rows[case], tsv, args.limit, dest, group)
            print(f"case {case}: {result['commands']} instructions, {result['chunks']} chunks", flush=True)
            return result
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            stats = list(pool.map(export, cases))
    aggregate(dest, group, cases)
    # This manifest describes generation only, never successful Lean replay.
    manifest = {'status': 'generated, not a verification record', 'module_group': group, 'cases': stats}
    (dest / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f"Generated {len(cases)} cases, {sum(s['chunks'] for s in stats)} chunks, {sum(s['commands'] for s in stats):,} instructions.")


if __name__ == '__main__':
    main()
