"""Checked inputs and Lean adapters for projected fourteen-copy exclusions.

Projection preserves the original anchor and bounds. These certificates prove
empty roots; no terminal census or fifteen-copy threshold justifies exclusion.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
from generate_five_colour_chunks import generate as generate_chunks
from generate_five_colour_packed import cut

ROOT = Path(__file__).resolve().parents[1]


def projected_row(source, retained):
    """Reconstruct the header from the original root, not supplied bounds."""
    if len(source) != 156:
        raise ValueError('invalid original root width')
    anchor, multiplicity, budget = source[4], source[1], source[5]
    if not (0 <= anchor < 75 and 1 <= multiplicity <= 5
            and 0 <= retained <= budget
            and source[6+anchor] == source[81+anchor] == 0
            and all(v in (0, 1) for v in source[81:])):
        raise ValueError('invalid projection conditions')
    row = source[:]
    row[3], row[5] = 14-budget+retained, retained
    if row[3] < multiplicity:
        raise ValueError('projection cannot preserve anchor')
    for i in range(75):
        if source[81+i]:
            row[6+i] = min(source[6+i], retained)
    return row


def load_projections(originals, work):
    metadata = json.loads((ROOT/'data/five-colour-classification-projections.json').read_text())
    archive_path = ROOT/'data/five-colour-classification-projections.tar.gz'
    if (metadata['format'] != 1 or metadata['original_total'] != 14
            or hashlib.sha256(archive_path.read_bytes()).hexdigest() != metadata['archive_sha256']):
        raise ValueError('invalid projection archive identity')
    entries = metadata['cases']
    if ([c['index'] for c in entries] != list(range(137))
            or len({c['original_root'] for c in entries}) != len(entries)):
        raise ValueError('invalid projection case mapping')
    result, rows = {}, []
    with tarfile.open(archive_path) as archive:
        members = archive.getmembers()
        expected = {f'case-{i}.q5p' for i in range(len(entries))}
        if len(members) != len(expected) or {m.name for m in members} != expected or any(not m.isfile() for m in members):
            raise ValueError('invalid projection archive members')
        for entry in entries:
            r, i = entry['original_root'], entry['index']
            if not 0 <= r < len(originals):
                raise ValueError('invalid original root index')
            row = projected_row(originals[r], entry['retained_budget'])
            payload = archive.extractfile(f'case-{i}.q5p').read()
            if (payload[:160] != b'Q5P2'+bytes(row) or row[3] != entry['goal']
                    or len(payload) != entry['certificate_bytes']
                    or hashlib.sha256(payload).hexdigest() != entry['certificate_sha256']):
                raise ValueError(f'projection certificate/header mismatch: {r}')
            path = work/f'projection-{i}.q5p'
            path.write_bytes(payload)
            result[r] = (entry, row, path)
            rows.append(row)
    cases = work/'projection-cases.txt'
    cases.write_text(str(len(rows))+'\n'+'\n'.join(' '.join(map(str,r)) for r in rows)+'\n')
    return result, cases


def generate_projected_case(case, entry, row, certificate, cases, work, dest):
    r, s, goal = entry['original_root'], entry['retained_budget'], row[3]
    tsv = work/f'projection-{case}.tsv'
    subprocess.run([str(ROOT/'build/five_colour_chunks'), str(ROOT/'data/five-colour-geometry.txt'),
                    str(cases), str(certificate), str(entry['index']), '128', str(tsv)],
                   check=True, stdout=subprocess.DEVNULL)
    stats = generate_chunks(case, row, tsv, 128, dest, 'EnumerationChunks.Projected', 'auto')
    if stats['commands'] != entry['new_instructions']:
        raise ValueError(f'projection instruction count mismatch: {r}')
    path = dest/f'Case{case}.lean'
    source = path.read_text().replace('@[expose] public section',
        'public import FiveColour.ClassificationProjection\n@[expose] public section', 1)
    budget = cut([i for i,v in enumerate(row[81:]) if v], s)
    prefix = f'FiveColour.Packed.EnumerationChunks.Projected.Case{case}'
    source += f'''
namespace {prefix}
open Physical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma projected_header : ProjectionValidAt 14 {r} {s} {goal} := by decide +kernel
lemma lower_model : ∀ i, root.model.lower i = (projectedBox {r} {s}).lower i := by decide +kernel
lemma upper_model : ∀ i, root.model.upper i = (projectedBox {r} {s}).upper i := by decide +kernel
lemma budget_model : ({budget} : Cut).model =
    (⟨rootBad (rootCapacity {r}), {s}⟩ : Certificate.Cut 75) := by
  have h : (Finset.univ.filter fun i : Fin 75 => ({budget} : Cut).member i = true) = rootBad (rootCapacity {r}) := by decide +kernel
  unfold Cut.model
  rw [h]
  rfl
lemma families_models (t : Fin 78) :
    (families t).map Cut.model = (caseProblem {r} {s} {goal}).alternatives t := by
  dsimp only [families, caseProblem]
  split_ifs
  · simp only [List.map_cons, List.map_nil, Archive.emptyCut_model]
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) (Archive.totalCut_model {goal})
  · exact congrArg (fun c : Certificate.Cut 75 => [c]) budget_model
  · exact hallCuts_models ⟨t.val-3, by omega⟩
lemma problem_model : Verified.problem {goal} families = caseProblem {r} {s} {goal} := by
  have h := funext families_models
  unfold Verified.problem
  rw [h]
  rfl
/-- Exclusion of the projected inventory excludes its original fourteen-copy root. -/
theorem original_covered (points : List Nat) :
    Enumeration.Covers points 14 (Enumeration.families {r}) (Archive.root {r}) := by
  intro x hx hp
  rw [Archive.root_model] at hx
  rw [Enumeration.problem_model] at hp
  obtain ⟨y,hy,hyp⟩ := root_projection_at 14 {r} {s} {goal} projected_header hx hp
  have hroot : root.model.Contains y := by
    intro i
    simpa only [lower_model, upper_model] using hy i
  change (caseProblem {r} {s} {goal}).Admissible y at hyp
  rw [← problem_model] at hyp
  exact False.elim (excludes y hroot hyp)
end {prefix}

namespace FiveColour.Packed.EnumerationChunks.Case{case}
def root : Box := Archive.root {r}
def families : Fin 78 → List Cut := Enumeration.families {r}
def points : List Nat := []
theorem covered : Enumeration.Covers points 14 families root :=
  Projected.Case{case}.original_covered points
end FiveColour.Packed.EnumerationChunks.Case{case}
'''
    if len(source.splitlines()) > 10000:
        raise ValueError(f'projected root {case} exceeds module line limit')
    path.write_text(source)
    return {'case':case, 'original_root':r, 'commands':stats['commands'],
            'chunks':stats['chunks'], 'points':0, 'route':'projection',
            'projected_total':goal, 'retained_budget':s, 'cut_mode':stats.get('cut_mode')}
