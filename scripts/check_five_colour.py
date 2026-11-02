#!/usr/bin/env python3
"""Independent physical audit of the five-colour research results.

Rotations are generated from quarter turns. The search and its geometry helpers
are not imported. This verifies witnesses and the finite bridge lemma for the
three-variety upper bound; it does not certify any CP-SAT UNSAT report.
"""
from collections import Counter
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
    for t,target in enumerate(cubes):
        for i,cube in enumerate(cubes):
            cs=set(corner_types(cube))
            require(masks[t][i]==sum(1<<k for k,c in enumerate(corner_types(target)) if c in cs),
                    'Cyclic and physical corners disagree')
    verified=[]
    for name in ['q5-initial.json','q5-local-initial.json','q5-local-diverse.json',
                 'q5-local-distinct.json','q5-local-cap2.json','q5-three-variety-obstruction.json',
                 'q5-one-repeat-colour.json']:
        data=json.loads((OUT/name).read_text());counts=[0]*75
        for e in data['collection']: counts[index[canonical(tuple(e['faces']))]]+=e['count']
        require(sum(counts)==data['size'],f'Wrong size in {name}')
        require(not any(match(s,counts) for s in slots),f'Solvable witness {name}')
        verified.append(dict(file=name,size=sum(counts)))
    # Every cube in this witness repeats the same colour; this establishes
    # sharpness of the separately enumerated twelve-cube family threshold.
    family=json.loads((OUT/'q5-one-repeat-colour.json').read_text())
    require(all(e['faces'].count(0)==2 for e in family['collection']),'Wrong repeat family')
    family_check=json.loads((OUT/'q5-one-repeat-colour-size12-exhaustive.json').read_text())
    require(family_check['status']=='EXHAUSTIVE_UNSAT' and family_check['size']==12,
            'Family enumeration did not complete')
    # For three types, N>=15 and each multiplicity<=7 imply that every pair
    # of types together has >=8 copies. Hall therefore reduces to the number
    # of target corners private to each individual source type.
    cases=Counter()
    for ids in itertools.combinations(range(75),3):
        private=[8-(masks[ids[i]][ids[(i+1)%3]]|masks[ids[i]][ids[(i+2)%3]]).bit_count()
                 for i in range(3)]
        if sum(private)<=17:
            cases['private_sum_bound']+=1
            continue
        lower=[max(1,17-private[(i+1)%3]-private[(i+2)%3]) for i in range(3)]
        for row in masks:
            a,b,c=[row[i] for i in ids]
            if a|b|c !=255:continue
            required=[8-(b|c).bit_count(),8-(a|c).bit_count(),8-(a|b).bit_count()]
            if all(r<=l for r,l in zip(required,lower)):
                cases['bridge_target']+=1
                break
        else:raise ValueError(f'Missing bridge for {ids}')
    data=json.loads((OUT/'q5-three-variety-exhaustive.json').read_text())
    require(data['maximum']==14,'Unexpected maximum')
    vectors=set()
    for w in data['maximisers']:
        require(tuple(sorted(w[3:]))==(4,5,5),'Unexpected multiplicities')
        counts=[0]*75
        for i,n in zip(w[:3],w[3:]):counts[i]=n
        require(not any(match(s,counts) for s in slots),'Solvable extremal triple')
        vectors.add(tuple(counts))
    require(len(vectors)==len(data['maximisers'])==840,'Duplicate or missing records')
    # Reproduce the completeness of the 14-cube triple list using the dual
    # Hall criterion, separately from the C++ enumerator.
    # Only triples with >=17 private corners can fail all their own targets
    # at (4,5,5): every pair of multiplicities is >=8, so the same lemma applies.
    expected=set()
    for ids in itertools.combinations(range(75),3):
        private=[8-(masks[ids[i]][ids[(i+1)%3]]|masks[ids[i]][ids[(i+2)%3]]).bit_count()
                 for i in range(3)]
        for counts3 in [(4,5,5),(5,4,5),(5,5,4)]:
            if any(n>=p for n,p in zip(counts3,private)):continue
            counts=[0]*75
            for i,n in zip(ids,counts3):counts[i]=n
            if not any(match(s,counts) for s in slots):expected.add(tuple(counts))
    require(expected==vectors,'Incomplete (4,5,5) list')
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
    for case in json.loads((OUT/'q5-control-cpp-size14.json').read_text()):
        if case['status']=='SAT':
            counts=[0]*75
            for i in case['copies']:counts[i]+=1
            require(sum(counts)==14 and not any(match(s,counts) for s in slots),
                    'False positive in exact-search control')
    result=dict(source_varieties=75,targets=75,physical_incidence_check=True,
                verified_witnesses=verified,three_variety_upper_bound_cases=cases,
                verified_extremal_triples=len(vectors),
                anchored_cover_cases_checked=len(case_rows),cover_orbits_complete=True,
                limitation='Exclusion of other size-14 multiplicity patterns uses the C++ enumeration.',
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (REPORT/'q5-independent-check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
