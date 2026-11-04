"""Discover simple Hall inequalities for the root's paired-cover normal forms."""
from itertools import combinations, product
import sys, json
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'root'))
import cut_model as m

rows=json.loads(Path('research/four_opposite_root/paired-cover-orbits.json').read_text())
oc=[m.CORNERS[71]]*2+[m.CORNERS[73]]*2

def conditions(js,t,total=10):
    target=tuple(sorted(m.CORNERS[t]))
    req={}
    for mask in range(1,1<<8):
        S={target[k] for k in range(8) if mask>>k&1}
        d=len(S)-sum(bool(S&o) for o in oc)
        if d<=0:continue
        inds=tuple(j for j in js if m.CUTS[j]&S)
        lower=max(0,total-3*(len(js)-len(inds)))
        if lower>=d:continue
        req[inds]=max(d,req.get(inds,0))
    if () in req:return None
    # Constraints on supersets at weaker thresholds are implied.
    for inds,d in list(req.items()):
        if any(set(k)<set(inds) and v>=d for k,v in req.items()):
            del req[inds]
    return req

def matched(src,pos):
    pos=list(pos);owners=[-1]*len(src)
    def aug(k,seen):
        for i,s in enumerate(src):
            if i not in seen and pos[k] in s:
                seen.add(i)
                if owners[i]<0 or aug(owners[i],seen):owners[i]=k;return True
        return False
    return all(aug(k,set()) for k in range(len(pos)))

for r,row in enumerate(rows):
    js=row['common']
    print('\nROW',r,'classes',js,'cover sizes',len(row['Hx']),len(row['Hy']))
    if row['Xbudget'] or row['Ybudget']:
        src=oc+[m.CUTS[j] for j in js for _ in range(3)]
        targets=[t for t in range(60,75)if matched(src,m.CORNERS[t])]
        loops=[]
        for j in js:
            ss=oc+[m.CUTS[k]for k in js for _ in range(3-2*(k==j))]
            if matched(ss,m.CUTS[j]):loops.append(j)
        pairloops=[(a,b)for a,b in combinations(loops,2)if set(m.CLASSES[a][0])&set(m.CLASSES[b][0])]
        print('nine-adjcore opposite targets',targets,'ownloops',loops,'intersectingloop pairs',pairloops)
        helpers=sorted(set(row['Yclasses'])-set(row['Xclasses']))
        print('helper classes',helpers)
        for h in helpers:
            ss=src+[m.CUTS[h]]
            ts=[t for t in range(60,75)if matched(ss,m.CORNERS[t])]
            print('helper',h,'targets',ts)
        continue
    options=[]
    for t in range(60,75):
        req=conditions(js,t)
        if req is not None:options.append((len(req),t,req))
    for _,t,req in sorted(options):print('target',t,'requires',req)
