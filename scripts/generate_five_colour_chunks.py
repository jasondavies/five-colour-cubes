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
from generate_five_colour_reduced import reduction

DEST = ROOT / 'FiveColour/ProjectedChunks'


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
    apply FastWeight.cut_valid_of_fast_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply FastWeight.cut_valid_of_fast_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply FastWeight.cut_valid_of_fast_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc
'''
    return text


def generate(case, row, path, limit, dest=DEST, group="ProjectedChunks", cut_mode="auto"):
    if cut_mode not in ("auto", "original", "reduced"):
        raise ValueError('invalid cut mode')
    checkpoints = path.read_text()
    commands = sum(int(line.split('\t')[3]) for line in checkpoints.splitlines())
    # The root-coverage and calibration proofs have a fixed upfront cost.
    # Retain original families for small cases; complete-root benchmarks near
    # 3,500 instructions include the extra coverage and calibration proofs.
    reduced = cut_mode == "reduced" or (cut_mode == "auto" and commands >= 3500)
    families = 'checkedFamilies' if reduced else 'families'
    pruning_import = 'public import FiveColour.PackedPruning\n' if reduced else ''
    dest.mkdir(parents=True, exist_ok=True)
    prefix = f'FiveColour.Packed.{group}.Case{case}'
    text = f'''module
public import FiveColour.PackedCalibration
public import FiveColour.PackedFast
public import FiveColour.PackedComputations
{pruning_import}@[expose] public section
namespace {prefix}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

'''
    text += problem(row)
    pruning_stats = {}
    if reduced:
        geometry = [list(map(int, line.split())) for line in
                    (RESULTS / 'five-colour-geometry.txt').read_text().splitlines()[76:]]
        declarations, pruning_stats = reduction(row, checkpoints, geometry)
        text += declarations
    sizes = []
    for line in checkpoints.splitlines():
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
theorem accepted : Fast.check {row[3]} {families} references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by
  apply FastValidity.box_valid_of_masks <;> decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes {row[3]} {families} (references i) := by
'''
        if refs:
            text += '  intro i\n  fin_cases i\n'
            text += ''.join(f'  · exact Part{r}.excludes\n' for r in refs)
        else:
            text += '  intro i\n  exact Fin.elim0 i\n'
        text += f'''
theorem excludes : Chunks.Excludes {row[3]} {families} root :=
  Fast.check_sound {row[3]} {families} {families}_valid references references_excluded proof root root_valid accepted
end Part{ident}
'''
    if not sizes:
        raise ValueError('empty chunk export')
    endpoint = f'Part{len(sizes)-1}.excludes'
    if reduced:
        endpoint = (f'excludes_of_covered root (by apply FastValidity.box_valid_of_masks <;> decide +kernel) {row[3]} families '
                    f'checkedFamilies families_valid checkedFamilies_valid checkedFamilies_cover {endpoint}')
    text += f'''
/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes {row[3]} families root := {endpoint}
end {prefix}
'''
    (dest / f'Case{case}.lean').write_text(text)
    return {'case': case, 'chunks': len(sizes), 'commands': sum(sizes),
            'largest_chunk': max(sizes), 'smallest_chunk': min(sizes), 'limit': limit,
            'cut_mode': 'reduced' if reduced else 'original', **pruning_stats}


def projected_aggregate(dest, cases, rows):
    namespace = 'FiveColour.Packed.ProjectedChunks'
    text = 'module\n' + ''.join(f'public import FiveColour.ProjectedChunks.Case{c}\n' for c in cases)
    text += f'@[expose] public section\nnamespace {namespace}\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
    text += 'def roots : Fin 279 → Box := ![' + ', '.join(f'Case{c}.root' for c in cases) + ']\n'
    text += 'def families : Fin 279 → Fin 78 → List Cut := ![' + ', '.join(f'Case{c}.families' for c in cases) + ']\n'
    text += 'def goals : Fin 279 → Nat := ![' + ', '.join(str(rows[c][3]) for c in cases) + ']\n'
    text += 'theorem all_excluded : ∀ i, Chunks.Excludes (goals i) (families i) (roots i) := by\n  intro i\n  fin_cases i\n'
    text += ''.join(f'  · exact Case{c}.excludes\n' for c in cases)
    text += f'end {namespace}\n'
    (dest/'All.lean').write_text(text)
    (dest/'Link.lean').write_text(f'''module
public import FiveColour.ProjectedChunks.All
public import FiveColour.ProjectedBridge
@[expose] public section
namespace {namespace}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem roots_match (i : Fin 279) : roots i = Projected.root i := by
  fin_cases i <;> rfl
theorem families_match (i : Fin 279) : families i = Projected.families i := by
  fin_cases i <;> funext t <;> rfl
theorem goals_match (i : Fin 279) : goals i = Projected.goals i := by
  fin_cases i <;> rfl

theorem archive_exclusions (i : Fin 279) :
    Chunks.Excludes (Projected.goals i) (Projected.families i) (Projected.root i) := by
  rw [← roots_match, ← families_match, ← goals_match]
  exact all_excluded i
end {namespace}
''')
    (dest/'Threshold.lean').write_text(f'''module
public import FiveColour.ProjectedChunks.Link
@[expose] public section
namespace {namespace}

/-- All projected certificates, their header identities, and physical coverage. -/
theorem threshold15 : Physical.Threshold15 :=
  Projected.threshold_of_exclusions archive_exclusions

theorem sharpThreshold15 : Physical.SharpThreshold15 :=
  Projected.sharp_threshold_of_exclusions archive_exclusions
end {namespace}
''')
    (dest/'Audit.lean').write_text('module\nimport FiveColour.ProjectedChunks.Threshold\n' +
        '#print axioms FiveColour.Packed.Chunks.check_sound\n' +
        '#print axioms FiveColour.Packed.Fast.check_sound\n' +
        ''.join(f'#print axioms {namespace}.{name}\n' for name in ['all_excluded', 'threshold15', 'sharpThreshold15']))


def check_sources(generated, retained):
    expected = {p.relative_to(generated): p.read_bytes() for p in generated.rglob('*') if p.is_file()}
    actual = {p.relative_to(retained): p.read_bytes() for p in retained.rglob('*') if p.is_file()}
    missing = sorted(expected.keys() - actual.keys())
    extra = sorted(actual.keys() - expected.keys())
    changed = sorted(p for p in expected.keys() & actual.keys() if expected[p] != actual[p])
    if missing or extra or changed:
        details = '; '.join(f'{label}: {", ".join(map(str, paths))}'
                            for label, paths in [('missing', missing), ('extra', extra), ('changed', changed)] if paths)
        advice = []
        if extra:
            advice.append('remove the files listed as extra')
        if missing or changed:
            advice.append('run make replay-data to regenerate missing or changed files')
        raise ValueError(f'Retained replay sources differ ({details}); {"; then ".join(advice)}.')


def generate_sources(dest, workers, cut_mode):
    case_file = RESULTS / 'q5-projected-root-cases.txt'
    archive_file = RESULTS / 'q5-projected-certificates.tar.gz'
    rows = [list(map(int, line.split())) for line in case_file.read_text().splitlines()[1:]]
    if len(rows) != 279:
        raise ValueError('Expected exactly 279 projected cases')
    cases = list(range(279))
    subprocess.run(['make', 'build/five_colour_chunks'], cwd=ROOT, check=True)
    dest.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive_file, 'r:gz') as archive:
        payloads = {case: archive.extractfile(f'case-{case}.q5p').read() for case in cases}
    with tempfile.TemporaryDirectory(prefix='q5-chunks-') as temp:
        def export(case):
            raw = Path(temp) / f'case-{case}.q5p'
            raw.write_bytes(payloads[case])
            tsv = Path(temp) / f'chunks-{case}.tsv'
            subprocess.run([str(ROOT / 'build/five_colour_chunks'),
                            str(RESULTS / 'five-colour-geometry.txt'), str(case_file),
                            str(raw), str(case), '128', str(tsv)], check=True, capture_output=True)
            return generate(case, rows[case], tsv, 128, dest=dest, cut_mode=cut_mode)
        with ThreadPoolExecutor(max_workers=workers) as pool:
            stats = list(pool.map(export, cases))
    projected_aggregate(dest, cases, rows)
    manifest = {'status': 'generated, not a verification record',
                'module_group': 'ProjectedChunks', 'cases': stats}
    (dest / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return manifest


def report(manifest, action):
    stats = manifest['cases']
    print(f"{action} {len(stats)} cases, {sum(s['chunks'] for s in stats)} chunks, "
          f"{sum(s['commands'] for s in stats):,} instructions.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cut-mode', choices=['auto', 'original', 'reduced'], default='auto',
                        help='auto reduces only cases with at least 4096 instructions')
    parser.add_argument('--workers', type=int, default=2, help='concurrent C++ exporters')
    parser.add_argument('--check', action='store_true', help='compare all retained files without writing them')
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('--workers must be positive')
    if args.check:
        with tempfile.TemporaryDirectory(prefix='q5-replay-check-') as temp:
            generated = Path(temp) / 'ProjectedChunks'
            manifest = generate_sources(generated, args.workers, args.cut_mode)
            check_sources(generated, DEST)
        report(manifest, 'Checked')
    else:
        report(generate_sources(DEST, args.workers, args.cut_mode), 'Generated')


if __name__ == '__main__':
    main()
