from itertools import combinations
from collections import Counter
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
from scipy.sparse import lil_matrix
import json,time
V=range(5);E=list(combinations(V,2));arcs=[(a,b)for a in V for b in V if a!=b]
arcid={e:i for i,e in enumerate(arcs)}
classes=[];labels=[];missing=[]
for e in E:
 for sg in [1,-1]:
  a=set(e);b=set(V)-a
  classes.append(set((x,y)if sg==1 else(y,x)for x in a for y in b));labels.append(('A',e,sg));missing.append({e})
for r in V:
 v=[a for a in V if a!=r]
 for b in v[1:]:
  a={v[0],b};q=set(v)-a
  classes.append(set((x,y)for x in a for y in q)|set((y,x)for x in a for y in q));labels.append(('O',r,tuple(sorted(a)),tuple(sorted(q))));missing.append({tuple(sorted(a)),tuple(sorted(q))})
obs=[]
for target in classes[20:]:
 t=list(target);neigh=[sum(1<<i for i,c in enumerate(classes)if corner in c)for corner in t]
 best={}
 for mask in range(1,256):
  n=0
  for k in range(8):
   if mask>>k&1:n|=neigh[k]
  best[n]=max(best.get(n,-1),mask.bit_count()-1)
 obs.append([(n,r)for n,r in best.items()if not any(q!=n and q&n==q and s>=r for q,s in best.items())])
print('cut counts',list(map(len,obs)),flush=True)
num=35+sum(map(len,obs));rows=[];lb=[];ub=[]
def row(co,l=-np.inf,u=np.inf):rows.append(co);lb.append(l);ub.append(u)
row({i:1 for i in range(35)},14,14)
row({i:1 for i in range(20,35)},5,np.inf)
for i,j in combinations(range(20),2):
 if len(classes[i]&classes[j])==4:row({i:1,j:1},u=7)
for e in E:row({i:1 for i,m in enumerate(missing)if e in m},u=7)
at=35
for cuts in obs:
 row({at+k:1 for k in range(len(cuts))},1,1)
 for n,r in cuts:
  co={i:1 for i in range(35)if n>>i&1};co[at]=14
  row(co,u=r+14);at+=1
mat=lil_matrix((len(rows),num))
for k,co in enumerate(rows):
 for j,v in co.items():mat[k,j]=v
c=np.zeros(num)
res=milp(c,integrality=np.ones(num),bounds=Bounds(np.zeros(num),np.array([5]*20+[4]*15+[1]*(num-35))),constraints=LinearConstraint(mat.tocsr(),lb,ub),options={'time_limit':120,'mip_rel_gap':0})
print(res,flush=True)
if res.x is not None:
 x=np.rint(res.x[:35]).astype(int).tolist()
 print('inventory',[(labels[i],n)for i,n in enumerate(x)if n],flush=True)
 print('W',3*sum(n*(n-1)//2 for n in x[:20])-4*sum(x[20:])*(sum(x[20:])-1)//2,flush=True)
 open('coarse_milp_result.json','w').write(json.dumps({'labels':labels,'x':x,'status':res.message},indent=2))
