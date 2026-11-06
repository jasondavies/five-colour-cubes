#!/usr/bin/env python3
"""Generate small, kernel-checked witnesses for the support refinements."""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def render():
    rows = (ROOT/'data/five-colour-geometry.txt').read_text().splitlines()
    assert int(rows[0]) == 75
    faces = [tuple(map(int,row.split())) for row in rows[1:76]]
    fits = [list(map(int,row.split())) for row in rows[76:]]
    targets = []
    for i in range(75):
        row = []
        for j in range(75):
            if fits[i][j]:
                row.append(i)
            else:
                row.append(next(t for t in range(75)
                    if (fits[t][i] | fits[t][j]) == 255
                    and fits[t][i].bit_count() >= 4 and fits[t][j].bit_count() >= 4))
        targets.append(row)
    P,Q = [faces.index(c) for c in [(0,1,2,3,2,4),(0,3,1,2,4,1)]]
    def missing(mask):
        return next(1 << k for k in range(8) if not mask & (1 << k))
    pairCuts=[]
    for t in range(75):
        union=fits[t][P] | fits[t][Q]
        pairCuts.append(255 ^ fits[t][Q] if t==P else 255 ^ fits[t][P] if t==Q else missing(union))
    vec=lambda xs:'!['+','.join(map(str,xs))+']'
    return f'''module
public import FiveColour.PairCapacityDefs
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

/-- A target for seven copies of i and six of j. -/
def supportPairTarget : Fin 75 → Fin 75 → Fin 75 :=
  ![{','.join(vec(row) for row in targets)}]

def supportPairAmount (i j : Fin 75) : ℕ := if Replay.fits i j = 0 then 4 else 7

def pairP : Fin 75 := {P}
def pairQ : Fin 75 := {Q}
def pairLowerCutMask : Fin 75 → ℕ := {vec(pairCuts)}
def pairLowerCut (t : Fin 75) : Finset (Fin 8) := cornerSet (pairLowerCutMask t)

end FiveColour.Physical
'''

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    path=ROOT/'FiveColour/SupportData.lean'
    expected=render()
    if args.check:
        if path.read_text()!=expected:raise SystemExit('SupportData.lean differs from regenerated witnesses')
        print('Support pair and obstruction witnesses match regeneration.')
    else:path.write_text(expected)

if __name__=='__main__':main()
