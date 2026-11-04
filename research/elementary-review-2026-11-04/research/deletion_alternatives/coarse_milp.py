from itertools import combinations
from collections import Counter
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix
import argparse,json

V=frozenset(range(5))
cuts=[frozenset(s) for k in [2,3] for s in combinations(range(5),k)]
arcs=[frozenset((a,b) for a in s for b in V-s) for s in cuts]
miss=[{tuple(sorted(s if len(s)==2 else V-s))} for s in cuts]
opps=[]
for r in range(5):
    rest=sorted(V-{r}); a=rest[0]
    for b in rest[1:]:
        p=frozenset([a,b]);q=V-{r}-p
        opps.append((r,tuple(sorted(p)),tuple(sorted(q))))
        arcs.append(frozenset((u,v) for u in p for v in q)|frozenset((v,u) for u in p for v in q))
        miss.append({tuple(sorted(p)),tuple(sorted(q))})

def matching(cap,target,reserve=0):
    cap=list(cap)
    if reserve:cap[target]-=reserve
    copies=[j for j,c in enumerate(cap) for _ in range(c)]
    owners=[None]*len(copies)
    def aug(e,seen):
        for i,j in enumerate(copies):
            if i in seen or e not in arcs[j]:continue
            seen.add(i)
            if owners[i] is None or aug(owners[i],seen):owners[i]=e;return True
        return False
    return all(aug(e,set()) for e in sorted(arcs[target]))

def solve(n,limit=60,quiet=False,maxg=None,fixo=None):
    lb=[0]*35; ub=[5]*20+[4]*15
    if maxg is not None:
        ub[:20]=[maxg]*20
        lb[0]=maxg
    if fixo is not None:
        lb[20]=fixo
        ub[20:]=[fixo]*15
    rows=[];lower=[];upper=[]
    def add(entries,l=-np.inf,u=np.inf):
        rows.append(entries);lower.append(l);upper.append(u)
    add({j:1 for j in range(35)},n,n)
    paircaps=[]
    for i,j in combinations(range(20),2):
        if len(arcs[i]&arcs[j])==4:
            add({i:1,j:1},u=7);paircaps.append((i,j))
    for pair in combinations(range(5),2):
        add({j:1 for j in range(35) if pair in miss[j]},u=7)
    branches=[]
    for t in range(35):
        target=sorted(arcs[t]);choices=[]
        if t<20:
            inactive=len(lb);lb.append(0);ub.append(1);choices.append(inactive)
            add({t:1,inactive:2},u=5)
        # Collect strongest Hall failure bound for each source-neighbour set.
        cuts_by_support={}
        for mask in range(1,1<<len(target)):
            ds={e for k,e in enumerate(target) if mask>>k&1}
            ns=frozenset(j for j in range(35) if arcs[j]&ds)
            budget=len(ds)-1+(2 if t<20 else 0)
            if len(ns)==35 and budget<n:continue
            if t<20 and budget<4:continue # active class contributes >=4
            cuts_by_support[ns]=max(cuts_by_support.get(ns,-1),budget)
        # If one constraint permits all assignments permitted by another,
        # retain the weaker failure condition only (OR of failures).
        candidates=list(cuts_by_support.items())
        retained=[]
        for ns,budget in candidates:
            if any(ns2<=ns and b2>=budget and (ns2!=ns or b2!=budget) for ns2,b2 in candidates):continue
            retained.append((ns,budget))
        for ns,budget in retained:
            z=len(lb);lb.append(0);ub.append(1);choices.append(z)
            add({**{j:1 for j in ns},z:n-budget},u=n)
        add({z:1 for z in choices},l=1)
        branches.append(len(choices))
    if not quiet:print('n',n,'variables',len(lb),'constraints',len(rows),'branches',branches,'sharedfour',len(paircaps),flush=True)
    rs=[];cs=[];vs=[]
    for r,row in enumerate(rows):
        for j,v in row.items():rs.append(r);cs.append(j);vs.append(v)
    mat=coo_matrix((vs,(rs,cs)),shape=(len(rows),len(lb))).tocsc()
    # Nonzero symmetric objective asks for concentrated solutions first.
    obj=np.zeros(len(lb))
    result=milp(obj,integrality=np.ones(len(lb)),bounds=Bounds(lb,ub),constraints=LinearConstraint(mat,lower,upper),options={'time_limit':limit,'disp':not quiet})
    print(result.message,flush=True)
    if result.x is not None:
        x=np.rint(result.x[:35]).astype(int).tolist()
        assert sum(x)==n
        solved=[t for t in range(35) if (t>=20 or x[t]>=4) and matching(x,t,2 if t<20 else 0)]
        assert not solved,solved
        W=3*sum(v*(v-1)//2 for v in x[:20])-4*sum(x[20:])*(sum(x[20:])-1)//2
        out={'n':n,'x':x,'W':W,'g':{str(sorted(cuts[i])):v for i,v in enumerate(x[:20]) if v},'o':{str(opps[i]):v for i,v in enumerate(x[20:]) if v},'result':result.message}
        print(json.dumps(out,indent=2),flush=True)
        return out
    return {'n':n,'result':result.message}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=15);p.add_argument('--seconds',type=float,default=60);p.add_argument('--quiet',action='store_true');p.add_argument('--maxg',type=int);p.add_argument('--fixo',type=int);a=p.parse_args()
    solve(a.n,a.seconds,a.quiet,a.maxg,a.fixo)
