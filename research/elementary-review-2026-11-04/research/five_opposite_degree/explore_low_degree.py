"""Discovery only: can all opposite targets have a corner of degree <=2?"""
from itertools import combinations, permutations, product
from pathlib import Path
import sys, json
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import V, PAIRS, CUTS, CORNERS, CLASSES, OPP

edge_index={e:i for i,e in enumerate(PAIRS)}
cycles=[]
for c in CORNERS[60:]:
 cycles.append(sum(1<<edge_index[(a,b)] for _,a,b in c if a<b))
perms=list(permutations(V))
def perm_edge(mask,p):
 return sum(1<<edge_index[tuple(sorted((p[a],p[b])))] for i,(a,b) in enumerate(PAIRS) if mask>>i&1)
def hits(mask): return all(mask&c for c in cycles)
minimal=[m for m in range(1<<10) if hits(m) and all(not hits(m^(1<<i)) for i in range(10) if m>>i&1)]
forms=sorted({min(perm_edge(m,p) for p in perms) for m in minimal})
print('Minimal undirected hitting sets:',len(minimal),'orbits:',len(forms),flush=True)
def canonical(arcs):
 return min(tuple(sorted((p[a],p[b]) if s==1 else (p[b],p[a]) for a,b in arcs)) for p in perms for s in [1,-1])
oriented=sorted({canonical(tuple(e if bit==0 else e[::-1] for e,bit in zip([PAIRS[i] for i in range(10) if m>>i&1],bs))) for m in forms for bs in product([0,1],repeat=m.bit_count())})
print('Oriented hitting set orbits:',len(oriented),flush=True)
sources=list(CUTS)+list(CORNERS[60:])
results=[]
for k,arcs in enumerate(oriented):
 rows=[[int(('t',a,b) in s) for s in sources] for a,b in arcs]
 rows += [[int(i<20) for i in range(35)],[int(i>=20) for i in range(35)]]
 low=[-np.inf]*len(arcs)+[9,5]
 high=[2]*len(arcs)+[9,5]
 res=milp(np.zeros(35),integrality=np.ones(35),bounds=Bounds(np.zeros(35),np.full(35,2)),constraints=LinearConstraint(np.array(rows),low,high),options={'time_limit':20})
 rec={'arcs':arcs,'status':int(res.status)}
 if res.x is not None:
  vals=np.rint(res.x).astype(int).tolist();rec['adj']={str(i):v for i,v in enumerate(vals[:20]) if v};rec['opp']={str(i+60):v for i,v in enumerate(vals[20:]) if v}
  print('FEASIBLE',k,rec,flush=True)
 results.append(rec)
print('Feasible',sum('adj' in r for r in results),'of',len(results),flush=True)
Path(__file__).with_name('low-degree-results.json').write_text(json.dumps({'undirected_forms':forms,'oriented_results':results},indent=2))
