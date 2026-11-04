#!/usr/bin/env python3
"""Independent local audit of the three-witness reduction; no research-model import.

A minimal obstruction to choosing three witnesses consists of four sources:
two for each own completion. Check all four-source multisets. The handwritten
proof does not depend on this enumeration.
"""
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json

V=frozenset(range(5))
sources=[]
for poles in combinations(range(5),2):
    for side in (frozenset(poles), V-frozenset(poles)):
        tri=frozenset((a,b) for a in side for b in V-side)
        for repeat in sorted(V-frozenset(poles)):
            sources.append(tri)
for repeated in range(5):
    other=sorted(V-{repeated})
    for partner in other[1:]:
        left={other[0],partner}; right=V-left-{repeated}
        sources.append(frozenset((a,b) for l,r in ((left,right),(right,left)) for a in l for b in r))
assert len(sources)==75
F={(0,2),(0,3),(1,2),(1,3)}
alpha={(0,4),(1,4)}
gamma={(4,2),(4,3)}

def pair_witness(s,t,private):
    requirements=F|private
    return any(a!=b and (a in private or b in private)
               for a in sources[s]&requirements for b in sources[t]&requirements)

wa={(s,t):pair_witness(s,t,alpha) for s,t in combinations_with_replacement(range(75),2)}
wb={(s,t):pair_witness(s,t,gamma) for s,t in combinations_with_replacement(range(75),2)}
positions=list(combinations(range(4),2))
checked=0
exceptions=[]
for pool in combinations_with_replacement(range(75),4):
    checked+=1
    a_endpoints=b_endpoints=0
    for i,j in positions:
        pair=(pool[i],pool[j]); bits=(1<<i)|(1<<j)
        if wa[pair]: a_endpoints |= bits
        if wb[pair]: b_endpoints |= bits
    if not a_endpoints or not b_endpoints or a_endpoints&b_endpoints:
        continue
    # No witness edge for A shares a physical source with one for B.
    # All four forced classes must occur, regardless of their repeats.
    assert sorted(s//3 for s in pool)==[7,13,16,18],pool
    assignment={7:(2,0),13:(3,1),16:(2,1),18:(3,0)}
    assert all(assignment[s//3] in sources[s] for s in pool)
    assert set(assignment.values())=={(b,a) for a,b in F}
    exceptions.append(pool)
assert len(exceptions)==81
record={'four_source_multisets_checked':checked,
        'two_completions_without_three_witnesses':len(exceptions),
        'forced_classes':['C(123)','C(023)','C(24)','C(34)'],
        'explanation':'One of each class; all 3^4 repeat refinements. Each explicitly fills the reverse half of 01|23; four core sources fill the forward half.',
        'scope':'Local incidence audit. The general arbitrary-pool reduction is the handwritten proof; no Lean formalisation.'}
out=Path(__file__).with_name('three-witness-audit.json')
out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
