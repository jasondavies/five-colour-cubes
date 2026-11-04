#!/usr/bin/env python3
"""Independent physical audit of the publication geometry and root coverage.

Rotations are generated from quarter turns. The search and its geometry helpers
are not imported. This verifies the lower-bound witness and coverage without importing the search
model or treating historical solver status reports as evidence.
"""
import hashlib
import itertools
import json
from pathlib import Path
from physical_geometry import canonical, corner_types, fits, match, require

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'data'
REPORT=ROOT/'build/checks'
REPORT.mkdir(parents=True,exist_ok=True)


def main():
    cubes=sorted({canonical(c) for c in itertools.product(range(5),repeat=6)
                  if len(set(c))==5})
    require(len(cubes)==75,'Wrong catalogue size')
    index={c:i for i,c in enumerate(cubes)}
    slots=fits(cubes,cubes)
    masks=[[sum(1<<k for k,neighbours in enumerate(row) if i in neighbours)
            for i in range(75)] for row in slots]
    rows=(OUT/'five-colour-geometry.txt').read_text().splitlines()
    require([tuple(map(int,s.split())) for s in rows[1:76]]==cubes,'Catalogue ordering')
    require([list(map(int,s.split())) for s in rows[76:]]==masks,'Physical incidence mismatch')
    corner_keys = [corner_types(cube) for cube in cubes]
    corner_sets = list(map(set, corner_keys))
    for t,target in enumerate(cubes):
        for i,cube in enumerate(cubes):
            require(masks[t][i]==sum(1<<k for k,c in enumerate(corner_keys[t]) if c in corner_sets[i]),
                    'Cyclic and physical corners disagree')
    witness=json.loads((OUT/'q5-three-variety-obstruction.json').read_text())
    counts=[0]*75
    for e in witness['collection']:
        counts[index[canonical(tuple(e['faces']))]]+=e['count']
    require(sum(counts)==witness['size']==14,'Wrong lower-bound size')
    require(not any(match(s,counts) for s in slots),'Solvable lower-bound witness')
    # Check exported case bounds against independently generated physical data,
    # and verify that the symmetry representatives cover EVERY anchored Hall cut.
    case_rows=[list(map(int,row.split())) for row in
               (OUT/'q5-cases-size15.txt').read_text().splitlines()[1:]]
    opposite=[any(c[2*j]==c[2*j+1] for j in range(3)) for c in cubes]
    anchors=[opposite.index(False),opposite.index(True)]
    for kind,anchor in enumerate(anchors):
        group=[]
        for p in itertools.permutations(range(5)):
            for mirror in (False,True):
                def image(c):
                    c=tuple(p[a] for a in c)
                    if mirror:c=(c[1],c[0],*c[2:])
                    return index[canonical(c)]
                if image(cubes[anchor])==anchor:group.append([image(c) for c in cubes])
        winning={i:[a for a in range(1,8)
                    if any(row[anchor]|row[i]==255 and
                           a<=row[anchor].bit_count() and 8-a<=row[i].bit_count()
                           for row in masks)] for i in range(75) if i!=anchor}
        for m in range(1,8):
            represented=set()
            for row in case_rows:
                if row[:2]!=[kind,m]:continue
                _,_,k,size,a,budget,*rest=row
                require(a==anchor and size==15,'Wrong anchored case')
                bad=[int(i!=anchor and bool(mask & ~k)) for i,mask in enumerate(masks[anchor])]
                require(budget==7-m-k.bit_count() and rest[75:]==bad,'Wrong Hall cover')
                upper=[m if kind==0 or f else m-1 for f in opposite]
                for i in range(75):
                    if bad[i]:upper[i]=min(upper[i],budget)
                    if i!=anchor:
                        for n in winning[i]:
                            if n<=m:upper[i]=min(upper[i],7-n)
                upper[anchor]=0
                require(upper==rest[:75],'Unsound exported multiplicity bound')
                represented.add((sum(b<<i for i,b in enumerate(bad)),budget))
            for k in range(256):
                if k.bit_count()>7-m:continue
                bad=[i for i,mask in enumerate(masks[anchor]) if i!=anchor and mask & ~k]
                budget=7-m-k.bit_count()
                require(any((sum(1<<p[i] for i in bad),budget) in represented for p in group),
                        'Missing Hall-cover orbit')
    result=dict(source_varieties=75,targets=75,physical_incidence_check=True,
                lower_bound_witness_checked=True,
                anchored_cover_cases_checked=len(case_rows),cover_orbits_complete=True,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (REPORT/'q5-independent-check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    return cubes, slots, masks


if __name__=='__main__':main()
