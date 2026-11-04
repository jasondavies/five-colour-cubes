import sys,json
from itertools import combinations
from pathlib import Path
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
from scipy.sparse import lil_matrix
sys.path.insert(0,'/workspace/scratch/66c0ebb8d303/research/root')
import cut_model as m
normal=int(sys.argv[1]) if len(sys.argv)>1 else 0
families=json.loads(Path('minimal-support-posets.json').read_text())
r=families[normal]['relation']
classes=[]
for j,(pair,sign)in enumerate(m.CLASSES):
 S=set(pair)if sign==1 else set(m.V)-set(pair)
 if all(a not in S or b in S for a,b in r):classes.append(j)
indices=[3*j+k for j in classes for k in range(3)]
Cs=[m.CORNERS[i]for i in indices]
assert not any(C<=set().union(*Cs)for C in m.CORNERS[60:])
obs=[]
for target in Cs:
 t=list(target);neigh=[sum(1<<i for i,C in enumerate(Cs)if k in C)for k in t]
 best={}
 for mask in range(1,256):
  n=0
  for k in range(8):
   if mask>>k&1:n|=neigh[k]
  best[n]=max(best.get(n,-1),mask.bit_count()-1)
 obs.append([(n,s)for n,s in best.items()if not any(q!=n and q&n==q and v>=s for q,v in best.items())])
print('normal',normal,'relation',r,'classes',classes,'cuts',[len(c)for c in obs],flush=True)
num=18+sum(map(len,obs));rows=[];lb=[];ub=[]
def row(co,l=-np.inf,u=np.inf):rows.append(co);lb.append(l);ub.append(u)
at=18
for cuts in obs:
 row({at+k:1 for k in range(len(cuts))},1,1)
 for n,s in cuts:
  co={i:1 for i in range(18)if n>>i&1};co[at]=126
  row(co,u=s+126);at+=1
mat=lil_matrix((len(rows),num))
for k,co in enumerate(rows):
 for j,v in co.items():mat[k,j]=v
c=np.array([-1.]*18+[0.]*(num-18))
res=milp(c,integrality=np.ones(num),bounds=Bounds(np.zeros(num),np.array([7]*18+[1]*(num-18))),constraints=LinearConstraint(mat.tocsr(),lb,ub),options={'time_limit':120,'mip_rel_gap':0,'threads':1})
print(res,flush=True)
record={'normal':normal,'classes':classes,'indices':indices,'relation':r,'cuts':obs,'message':res.message}
if res.x is not None:
 x=np.rint(res.x[:18]).astype(int).tolist();full=[0]*75
 for i,v in zip(indices,x):full[i]=v
 assert all(not m.match_target(full,t)for t in range(75))
 print('total',sum(x),'witness',[(m.KINDS[i],v)for i,v in zip(indices,x)if v],flush=True)
 print('coarse',[(m.CLASSES[j],sum(full[3*j:3*j+3]))for j in classes],flush=True)
 record.update({'x':x,'full_x':full,'total':sum(x),'dual_bound':res.mip_dual_bound,'nodes':res.mip_node_count})
Path(f'family-{normal}-milp.json').write_text(json.dumps(record,indent=2))
