"""Discovery of maximal pairwise-intersecting cut families.

The intended hand classification uses the fact that an intersecting
edge family of K5 is contained in a star or a triangle.
"""
import sys,json
from pathlib import Path
from itertools import permutations
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import CUTS,CLASSES,V

neighbors={i:{j for j in range(20) if j!=i and CUTS[i]&CUTS[j]} for i in range(20)}
maximal=[]
def bk(r,p,x):
    if not p and not x:
        maximal.append(frozenset(r));return
    pivot=max(p|x,key=lambda u:len(p&neighbors[u]))
    for v in sorted(p-neighbors[pivot]):
        bk(r|{v},p&neighbors[v],x&neighbors[v])
        p.remove(v);x.add(v)
bk(set(),set(range(20)),set())

acts=[]
for p in permutations(V):
    for rev in (False,True):
        acts.append(tuple(CUTS.index(frozenset(('t',p[b],p[a]) if rev else ('t',p[a],p[b]) for _,a,b in c)) for c in CUTS))
reps={}
for s in maximal:
    key=min(tuple(sorted(a[j] for j in s)) for a in acts)
    reps.setdefault(key,[]).append(sorted(s))
def name(j):
    p,s=CLASSES[j]
    return 'C'+''.join(map(str,sorted(p if s==1 else set(V)-set(p))))
out=[]
for k,orbit in sorted(reps.items(),key=lambda kv:(len(kv[0]),kv[0])):
    row={'classes':list(k),'names':[name(j) for j in k],'labelled_count':len(orbit)}
    out.append(row)
    print(row)
Path(__file__).with_name('intersecting-cut-families.json').write_text(json.dumps(out,indent=2)+'\n')
print('maximal labelled',len(maximal),'orbits',len(reps))
