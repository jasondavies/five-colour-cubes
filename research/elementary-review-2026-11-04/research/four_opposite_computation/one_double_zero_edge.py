"""Discovery of repeated-class eligibility in a globally zero adjacent edge."""
from itertools import combinations,permutations
from collections import Counter
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
import cut_model as m
E={i:frozenset(tuple(sorted((a,b)))for _,a,b in m.CORNERS[i])for i in range(60,75)}
def match(src,pos):
    pos=list(pos);owners=[-1]*len(src)
    def aug(k,seen):
        for i,s in enumerate(src):
            if i not in seen and pos[k] in s:
                seen.add(i)
                if owners[i]<0 or aug(owners[i],seen):owners[i]=k;return True
        return False
    return all(aug(k,set())for k in range(len(pos)))
rs=[]
D=60
for P,Q in combinations(range(61,75),2):
    src=[E[D],E[D],E[P],E[Q]]
    good=[t for t in E if match(src,E[t])]
    repeated=[j for j,A in enumerate(m.CUTS)if not any(len(A&m.CORNERS[t])==4 for t in good)]
    for f in combinations(range(5),2):
        if f in E[D] or not(f in E[P] or f in E[Q]):continue
        arcs={('t',*f),('t',*f[::-1])}
        allowed=[j for j,A in enumerate(m.CUTS)if not A&arcs]
        rep=[j for j in repeated if j in allowed]
        one=[]
        for j in rep:
            p,s=m.CLASSES[j];S=set(p)if s>0 else set(range(5))-set(p)
            if set(f)<=S:one.append(j)
        assert len(rep)==2*len(one)
        rs.append({'D':D,'P':P,'Q':Q,'f':f,'good_targets':good,'repeatable_avoid_f':rep,'same_side_group':one})
hist=Counter(len(r['same_side_group'])for r in rs)
print('cases',len(rs),'repeatable classes per orientation group',hist)
for r in rs:
    if len(r['same_side_group'])>=2:print(r)
Path(__file__).with_name('one-double-zero-edge.json').write_text(json.dumps(rs,indent=2)+'\n')
