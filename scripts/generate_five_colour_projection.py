#!/usr/bin/env python3
"""Serialize projected headers; Lean checks every transformation and root coverage."""
import argparse
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def encoded_header(row):
    """Packed bounds and budget cut, shared by both projection routes."""
    _,m,_,_,a,b,*rest=row
    lo,hi=[0]*75,rest[:75]
    lo[a]=hi[a]=m
    encode=lambda xs:sum(v << (10*i) for i,v in enumerate(xs))
    bad=rest[75:]
    return (encode(lo),encode(hi),sum(v<<i for i,v in enumerate(bad)),
            sum(v<<(10*(74-i)) for i,v in enumerate(bad)),b)


def generate(root, check=False):
    data = root / 'data'
    lines = (data/'q5-projected-root-cases.txt').read_text().splitlines()
    rows = [list(map(int, line.split())) for line in lines[1:]]
    meta = json.loads((data/'q5-projected-root-manifest.json').read_text())['cases']
    assert int(lines[0]) == len(rows) == len(meta) == 279
    originals = [m['original_case'] for m in meta]
    assert originals == json.loads((data/'q5-root-reduction.json').read_text())['replay_case_ids']
    with tarfile.open(data/'q5-projected-certificates.tar.gz') as archive:
        members = {m.name:m for m in archive.getmembers()}
        assert set(members) == {f'case-{i}.q5p' for i in range(279)}
        for i,row in enumerate(rows):
            assert archive.extractfile(members[f'case-{i}.q5p']).read(160) == b'Q5P2'+bytes(row)
    def emit(name, text):
        p = root/'FiveColour'/name
        if check:
            if not p.is_file() or p.read_text() != text:
                raise SystemExit(f'Generated file differs: {p.name}')
        else:
            p.write_text(text)
    def vector(values):
        return '!['+', '.join(map(str, values))+']'
    headers=[encoded_header(row) for row in rows]
    text='''module
public import FiveColour.ProjectionBridge
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed.Projected
open Physical

/-- Local projected IDs map explicitly to the original 357-root numbering. -/
def caseNumbers : Fin 279 → Fin 357 := '''+vector(originals)+'''
def goals : Fin 279 → Nat := '''+vector([r[3] for r in rows])+'''
def budgets : Fin 279 → Nat := '''+vector([r[5] for r in rows])+'''
def headers : Array Archive.Header := #[
  '''+',\n  '.join('⟨'+','.join(map(str,h))+'⟩' for h in headers)+''']

def root (i : Fin 279) : Box := ⟨headers[i.val]!.lower, headers[i.val]!.upper⟩
def budgetCut (i : Fin 279) : Cut :=
  ⟨headers[i.val]!.badMask, headers[i.val]!.badWeight, headers[i.val]!.budget⟩
def families (i : Fin 279) (t : Fin 78) : List Cut :=
  if t.val = 0 then [⟨0, 0, 0⟩]
  else if t.val = 1 then [⟨2^75-1, allWeight, goals i⟩]
  else if t.val = 2 then [budgetCut i]
  else (cuts[t.val-3]!).toList

/-- Check the entire changed header, including the projection hypotheses. -/
def HeaderValid (i : Fin 279) : Prop :=
  Projection.HeaderValid 15 (caseNumbers i) (budgets i) (goals i) headers[i.val]!

instance (i : Fin 279) : Decidable (HeaderValid i) := by
  unfold HeaderValid
  infer_instance

/-- Every root still requiring replay is represented by a projected header. -/
theorem covers : ∀ r ∈ replayRoots, ∃ i, caseNumbers i = r := by decide +kernel

end FiveColour.Packed.Projected
'''
    emit('ProjectedData.lean',text)
    groups=6
    for g in range(groups):
        emit(f'ProjectedChecks{g}.lean','''module
public import FiveColour.ProjectedData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed.Projected
'''+''.join(f'lemma header_valid_{i} : HeaderValid {i} := by decide +kernel\n' for i in range(g*50,min(g*50+50,279)))+'end FiveColour.Packed.Projected\n')
    emit('ProjectedChecks.lean','module\n'+''.join(f'public import FiveColour.ProjectedChecks{g}\n' for g in range(groups))+'''@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Packed.Projected
theorem header_valid (i : Fin 279) : HeaderValid i := by
  fin_cases i
'''+''.join(f'  · exact header_valid_{i}\n' for i in range(279))+'end FiveColour.Packed.Projected\n')
    print('Projected archive: 279 headers, full projection conditions and root coverage.')

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check',action='store_true')
    args=p.parse_args()
    generate(ROOT,args.check)
