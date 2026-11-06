#!/usr/bin/env python3
"""Generate small physical-geometry witnesses for the universal collection.

Lean checks every witness. The independent auditor uses its own rotations and
matching implementation, not these production helpers.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path

from cube_geometry import canonical, corners
from cube_witnesses import match_copies

ROOT = Path(__file__).resolve().parents[1]
SEEDS = [(0,2,0,3,1,4), (0,2,0,4,3,1), (0,3,0,4,1,2)]


def vector(values):
    return '![' + ','.join(map(str, values)) + ']'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    rows = [list(map(int, line.split())) for line in
            (ROOT/'data/five-colour-geometry.txt').read_text().splitlines()]
    cubes = [tuple(c) for c in rows[1:76]]
    masks = rows[76:]
    sources = [cubes.index(canonical(tuple((c+r)%5 for c in seed)))
               for r in range(5) for seed in SEEDS]
    assert len(set(sources)) == 15
    labels = []
    for c in cubes:
        r = next(r for r in range(5) if c.count(r) == 2)
        labels.append(5 if any(c[2*j] == c[2*j+1] for j in range(3)) else r)
    pairs = list(combinations(range(4), 2))
    targets, positions = [], []
    for r in range(5):
        colours = [p for p in range(5) if p != r]
        ts, ps = [], []
        for p, q in pairs:
            wanted = [(r,r,colours[p]), (r,r,colours[q])]
            wanted = [min(x,x[1:]+x[:1],x[2:]+x[:2]) for x in wanted]
            t = next(i for i,c in enumerate(cubes) if all(x in corners(c) for x in wanted))
            ts.append(t); ps.append([corners(cubes[t]).index(x) for x in wanted])
        targets.append(ts); positions.append(ps)
    placements = [match_copies(row,sources) for row in masks]
    assert all(p is not None and len(set(p))==8 for p in placements)
    text = '''module
public import FiveColour.Multiplicity
public import FiveColour.SubmissionModel
@[expose] public section
namespace FiveColour.Physical

/-- Adjacent repeated colour, with 5 marking the opposite-repeat varieties. -/
def universalSourceClass : Fin 75 → Fin 6 :=
  ''' + vector(labels) + '''

def universalPairFirst : Fin 6 → Fin 4 := ''' + vector([p for p,q in pairs]) + '''
def universalPairSecond : Fin 6 → Fin 4 := ''' + vector([q for p,q in pairs]) + '''

/-- One physical target for each repeated colour and each pair of other colours. -/
def universalPairTarget : Fin 5 → Fin 6 → Fin 75 :=
  ''' + vector([vector(ts) for ts in targets]) + '''
def universalPairPosition : Fin 5 → Fin 6 → Fin 2 → Fin 8 :=
  ''' + vector([vector([vector(ps) for ps in group]) for group in positions]) + '''

/-- The fifteen cyclic seed copies, in repeat/seed order. -/
def universalSource : Fin 15 → Fin 75 :=
  ''' + vector(sources) + '''
/-- Distinct physical-copy indices for every prescribed catalogue target. -/
def universalPlacement : Fin 75 → Fin 8 → Fin 15 :=
  ''' + vector([vector(p) for p in placements]) + '''

end FiveColour.Physical
'''
    dictionary = dict(seeds=SEEDS, face_order=['+x','-x','+y','-y','+z','-z'],
        construction='Five cyclic colour shifts of each seed; sources ordered by shift then seed.',
        source_indices=sources, placements=placements)
    outputs = {'FiveColour/UniversalData.lean':text,
               'data/five-colour-universal.json':json.dumps(dictionary,indent=2)+'\n'}
    for name, content in outputs.items():
        path=ROOT/name
        if args.check:
            if not path.exists() or path.read_text()!=content:
                raise SystemExit(f'Generated file differs: {name}')
        else: path.write_text(content)
    print(('Checked' if args.check else 'Generated')+' universal geometry and 75 explicit matchings.')

if __name__=='__main__': main()
