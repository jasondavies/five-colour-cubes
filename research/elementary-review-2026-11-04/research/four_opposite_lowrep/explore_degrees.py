from itertools import combinations
from pathlib import Path
import random, sys, json
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import CUTS, CORNERS
random.seed(49043)
arcs=[('t',a,b) for a in range(5) for b in range(5) if a!=b]
am=[[int(c in s) for c in arcs] for s in CUTS]
om=[[int(c in s) for c in arcs] for s in CORNERS[60:]]
ti=[[i for i,c in enumerate(arcs) if c in t] for t in CORNERS[60:]]
out=[]
for case in range(30000):
    if case%2:
        d,*other=random.sample(range(15),3); os=[d,d]+other
    else: os=random.sample(range(15),4)
    g=[0]*20
    for _ in range(10):
        j=random.choice([j for j in range(20) if g[j]<3]);g[j]+=1
    deg=[sum(om[o][i] for o in os)+sum(g[j]*am[j][i] for j in range(20)) for i in range(20)]
    good=[t for t in range(15) if min(deg[i] for i in ti[t])>=3]
    if not good:
        out.append({'opposite':[o+60 for o in os],'adjacent':g,'degree':deg})
        if len(out)>=10:break
print(json.dumps({'cases':case+1,'examples':out},indent=2))
